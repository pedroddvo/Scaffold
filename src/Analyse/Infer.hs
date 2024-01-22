{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant <$>" #-}

module Analyse.Infer where

import Analyse.Subtype (instantiateForalls, subtype)
import Analyse.TcContext (TcCtxM, TcError (TcError), TcState (..), apply, fresh, getEnv, instantiate, instantiateType, solve)
import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad (forM, zipWithM)
import Control.Monad.Error (MonadError (throwError))
import Control.Monad.State (gets)
import Data.Bifunctor (second)
import Data.Foldable (foldr')
import Data.List (find)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Debug.Trace (traceShowM)
import Error (Error (Error))
import Span (Span)
import Syntax.Ast (node)
import Syntax.Ast qualified as Ast
import Syntax.Name (Name)
import Syntax.Name qualified as Name

class Typed a where
  nodeType :: Ast.Node n a -> Type

class Spanned a where
  nodeSpan :: Ast.Node n a -> Span

instance Typed (a, Type) where
  nodeType (Ast.Node _ (_, t)) = t

instance Spanned (Span, a) where
  nodeSpan (Ast.Node _ (t, _)) = t

type TypeVars = Ast.Vars Unique

wfType :: TypeVars -> Ast.Type Unique Span -> Ast.Type Unique (Span, Type)
wfType vars (Ast.Node ty sp) = case ty of
  Ast.TSymbol alpha ->
    if alpha `elem` vars
      then Ast.Node (Ast.TSymbol alpha) (sp, Type.Var $ Type.Named alpha)
      else Ast.Node (Ast.TSymbol alpha) (sp, Type.Base alpha)
  Ast.TBorrow a ->
    let a' = wfType vars a
     in Ast.Node (Ast.TBorrow a') (sp, Type.Borrow $ nodeType a')
  Ast.TArrow a b ->
    let a' = wfType vars a
        b' = wfType vars b
     in Ast.Node (Ast.TArrow a' b') (sp, Type.Arrow (nodeType a') (nodeType b'))
  Ast.TApp a b ->
    let a' = wfType vars a
        b' = map (wfType vars) b
     in Ast.Node (Ast.TApp a' b') (sp, Type.App (nodeType a') (map nodeType b'))

instantiatePattern ::
  TypeVars ->
  Ast.Pattern Unique Span ->
  Type ->
  TcCtxM (Ast.Pattern Unique (Span, Type))
instantiatePattern vars (Ast.Node pat sp) scrutinee = case pat of
  Ast.PSymbol alpha -> do
    instantiate alpha scrutinee
    return $ Ast.Node (Ast.PSymbol alpha) (sp, scrutinee)
  Ast.PAnno p t -> do
    let t'@(Ast.Node _ (_, t't)) = wfType vars t
    subtype sp scrutinee t't
    p' <- instantiatePattern vars p t't
    return $ Ast.Node (Ast.PAnno p' t') (sp, t't)
  Ast.PCtor alpha args -> do
    ctorF <-
      synthSymbol alpha >>= \case
        Just t -> return t
        Nothing -> undefined -- should be unreachable (caught in resolver)
    let (vars', argsT, returnT) = Type.arrowUnzip ctorF
    varsE <- mapM (const fresh) vars'
    let varsSubst = zip vars' varsE
    let argsT' =
          foldr'
            (\(v, e) -> map (Type.substitute (Type.Named v) (Type.Exist' e)))
            argsT
            varsSubst
    let returnT' =
          foldr'
            (\(v, e) -> Type.substitute (Type.Named v) (Type.Exist' e))
            returnT
            varsSubst
    subtype sp returnT' scrutinee
    args' <- zipWithM (instantiatePattern $ vars ++ vars') args argsT'
    return $ Ast.Node (Ast.PCtor alpha args') (sp, returnT')
  Ast.PWildcard -> return $ Ast.Node Ast.PWildcard (sp, scrutinee)
  Ast.PNumeric num -> do
    subtype sp scrutinee Type.int
    return $ Ast.Node (Ast.PNumeric num) (sp, Type.int)

check ::
  Ast.Expr Unique Span ->
  Type ->
  TcCtxM (Ast.Expr Unique (Span, Type))
check e_@(Ast.Node expr sp) t = case (expr, t) of
  (Ast.Lam p e, Type.Arrow a b) -> do
    p' <- instantiatePattern [] p a
    e' <- check e b
    return $ Ast.Node (Ast.Lam p' e') (sp, t)
  (_, b) -> do
    e' <- synth e_
    env <- getEnv
    subtype sp (apply env $ nodeType e') (apply env b)
    return e'

synthApp ::
  Span ->
  Type ->
  [Ast.Expr Unique Span] ->
  TcCtxM (Type, [Ast.Expr Unique (Span, Type)])
synthApp sp t args = case (t, args) of
  (Type.Arrow a c, [arg]) -> do
    arg' <- check arg a
    env <- getEnv
    return (apply env c, [arg'])
  (Type.Arrow (Type.Tuple as) _, _)
    | length args /= length as ->
        throwError $ TcError (Error sp "function called with wrong number of arguments")
  (Type.Arrow (Type.Tuple as) c, _) -> do
    args' <- zipWithM check args as
    return (c, args')
  (Type.Forall alpha a, _) -> do
    alphaE <- fresh
    let instA = Type.substitute (Type.Named alpha) (Type.Exist' alphaE) a
    (c, args') <- synthApp sp instA args
    env <- getEnv
    return (apply env c, fmap (applyExpr env) args')
  (Type.Exist' alpha, _) -> do
    alphas <- mapM (const $ Type.Exist' <$> fresh) args
    alphaRet <- Type.Exist' <$> fresh
    args' <- zipWithM check args alphas
    solve alpha (Type.arrow alphas alphaRet)
    return (alphaRet, args')
  (Type.Arrow a c, xs) -> throwError $ TcError (Error sp "function called with too many arguments")
  _ -> throwError $ TcError (Error sp $ Text.pack ("cannot call a " ++ show t))

synthSymbol ::
  Unique ->
  TcCtxM (Maybe Type)
synthSymbol alpha =
  getEnv >>= \env -> case Map.lookup alpha (tc_vars env) of
    Just t -> return $ Just t
    Nothing -> return Nothing

synthDot ::
  Ast.Expr Unique Span ->
  TcCtxM (Either Unique (Ast.Expr Unique (Span, Type)))
synthDot e@(Ast.Node expr sp) = case expr of
  Ast.Symbol alpha ->
    synthSymbol alpha >>= \case
      Just t -> return $ Right (Ast.Node (Ast.Symbol alpha) (sp, t))
      Nothing -> return $ Left alpha
  _ -> Right <$> synth e

textFromUnique :: Unique -> TcCtxM (Maybe (Name Text, Unique))
textFromUnique uniq = find (\(_, v) -> v == uniq) <$> gets tc_resolved_vars_kv

lookupName :: Span -> Unique -> Name Text -> TcCtxM (Unique, Type)
lookupName sp namespaceUniq rest =
  textFromUnique namespaceUniq >>= \case
    Just (namespace, _) -> do
      let fullName = namespace <> rest
      Map.lookup fullName <$> gets tc_resolved_vars >>= \case
        Nothing -> throwError $ undefinedSymbol sp (Name.moduleName fullName)
        Just symbol ->
          synthSymbol symbol >>= \case
            Just t -> return (symbol, t)
            Nothing -> throwError $ undefinedSymbol sp (Text.pack $ show symbol)
    Nothing -> undefined

undefinedSymbol :: Show a => Span -> a -> TcError
undefinedSymbol sp n = TcError (Error sp $ Text.concat ["undefined symbol ", Text.pack $ show n])

synth ::
  Ast.Expr Unique Span ->
  TcCtxM (Ast.Expr Unique (Span, Type))
synth (Ast.Node expr sp) = case expr of
  Ast.Symbol alpha ->
    synthSymbol alpha >>= \case
      Just t -> return $ Ast.Node (Ast.Symbol alpha) (sp, t)
      Nothing -> throwError $ undefinedSymbol sp alpha
  Ast.Numeric num -> return $ Ast.Node (Ast.Numeric num) (sp, Type.int)
  Ast.String str -> return $ Ast.Node (Ast.String str) (sp, Type.string)
  Ast.Let p e1 e2 -> do
    e1' <- synth e1
    p' <- instantiatePattern [] p (nodeType e1')
    e2' <- synth e2
    return $ Ast.Node (Ast.Let p' e1' e2') (sp, nodeType e2')
  Ast.Lam p e -> do
    alpha <- Type.Exist' <$> fresh
    beta <- Type.Exist' <$> fresh
    p' <- instantiatePattern [] p alpha
    e' <- check e beta
    return $ Ast.Node (Ast.Lam p' e') (sp, Type.Arrow alpha beta)
  Ast.App a as -> do
    a' <- synth a
    env <- getEnv
    let a'' = applyExpr env a'
    (c, as') <- synthApp sp (nodeType a'') as
    return $ Ast.Node (Ast.App a'' as') (sp, c)
  Ast.Dot _ (Ast.DotResolved _) -> undefined
  Ast.Dot a (Ast.DotUnresolved rest) -> do
    synthDot a >>= \case
      Left namespaceUniq -> do
        (symbol, t) <- lookupName sp namespaceUniq rest
        return $ Ast.Node (Ast.Symbol symbol) (sp, t)
      Right a' -> do
        env <- getEnv
        a't <- instantiateForalls . apply env $ nodeType a'
        case Type.name a't of
          Just namespaceUniq -> do
            (symbol, f) <- lookupName sp namespaceUniq rest
            let symbolNode = Ast.Node (Ast.Symbol symbol) (sp, f)
            f' <- applyDotType sp f a't
            return $ Ast.Node (Ast.Dot a' $ Ast.DotResolved symbolNode) (sp, f')
          Nothing -> throwError $ TcError (Error sp $ Text.pack ("cannot use dot notation on type " ++ show a't))
  Ast.Unit -> return $ Ast.Node Ast.Unit (sp, Type.unit)
  Ast.Def name vars args ret e rest -> do
    args' <- mapM (\pat -> fresh >>= instantiatePattern vars pat . Type.Exist') args
    let ret' = fmap (wfType vars) ret
    let argsTy = fmap nodeType args'
    retTy <- case ret' of
      Just n -> return $ nodeType n
      Nothing -> Type.Exist' <$> fresh
    let funcTy = foldr' Type.Forall (Type.arrow argsTy retTy) vars
    instantiate name funcTy
    e' <- check e retTy
    env <- getEnv
    instantiate name (apply env funcTy)
    rest' <- synth rest
    return $ Ast.Node (Ast.Def name vars args' ret' e' rest') (sp, funcTy)
  Ast.ExternDef name args ret cident rest -> do
    args' <- mapM (\pat -> fresh >>= instantiatePattern [] pat . Type.Exist') args
    let ret' = wfType [] ret
    let argsTy = fmap nodeType args'
    let retTy = nodeType ret'
    let funcTy = Type.arrow argsTy retTy
    env <- getEnv
    instantiate name (apply env funcTy)
    rest' <- synth rest
    return $ Ast.Node (Ast.ExternDef name args' ret' cident rest') (sp, funcTy)
  Ast.ExternType name cident rest -> do
    let t = case name of
          Unique.Builtin name' -> Type.Intrinsic name'
          _ -> Type.Base name
    instantiateType name t
    rest' <- synth rest
    return $ Ast.Node (Ast.ExternType name cident rest') (sp, t)
  Ast.InductiveType name vars ctors rest -> do
    let t = Type.Base name
    instantiateType name t
    ctors' <- mapM (synthInductiveCtor vars t) ctors
    rest' <- synth rest
    return $ Ast.Node (Ast.InductiveType name vars ctors' rest') (sp, Type.unit)
  Ast.Match scrutinee branches -> do
    scrutinee' <- synth scrutinee
    let t = nodeType scrutinee'
    instT <- instantiateForalls t
    alpha <- Type.Exist' <$> fresh
    branches' <- forM branches $ \(pat, guards, e) -> do
      pat' <- instantiatePattern [] pat instT
      guards' <- mapM (`check` Type.bool) guards
      e' <- check e alpha
      return (pat', guards', e')
    env <- getEnv
    let scrutinee'' = case scrutinee' of
          Ast.Node kind (scrutSp, _) -> Ast.Node kind (scrutSp, apply env instT)
    return $
      Ast.Node (Ast.Match scrutinee'' $ map (applyBranch env) branches') (sp, apply env alpha)

applyBranch :: TcState -> Ast.MatchBranch Unique (Span, Type) -> Ast.MatchBranch Unique (Span, Type)
applyBranch env (p, g, e) = (applyExpr env p, map (applyExpr env) g, applyExpr env e)

applyExpr :: (Functor a) => TcState -> Ast.Node a (Span, Type) -> Ast.Node a (Span, Type)
applyExpr env = fmap (second $ apply env)

synthInductiveCtor ::
  TypeVars ->
  Type ->
  Ast.Ctor Unique Span ->
  TcCtxM (Ast.Ctor Unique (Span, Type))
synthInductiveCtor vars ctorT (Ast.Ctor name args) = do
  let args' = map (second $ wfType vars) args
  let argsTys = map (nodeType . snd) args'
  let innerFn = Type.ctor argsTys $ Type.App ctorT (map Type.Named' vars)
  let ctorFn = foldr Type.Forall innerFn vars
  instantiate name ctorFn
  return $ Ast.Ctor name args'

applyDotType :: Span -> Type -> Type -> TcCtxM Type
applyDotType sp f b = case f of
  Type.Arrow a@(Type.Tuple []) c -> do
    subtype sp a b
    return c
  Type.Arrow (Type.Tuple (a : as)) c -> do
    subtype sp a b
    return $ Type.arrow as c
  Type.Arrow a c -> do
    subtype sp a b
    return (Type.Arrow (Type.Tuple []) c)
  Type.Forall{} -> do
    f' <- instantiateForalls f
    applyDotType sp f' b
  _ -> throwError $ TcError (Error sp $ Text.pack ("cannot call type " ++ show f))
