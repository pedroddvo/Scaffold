{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant <$>" #-}

module Analyse.Infer where

import Analyse.Subtype (subtype)
import Analyse.TcContext (TcCtxM, TcError (TcError), TcState (..), apply, fresh, getEnv, instantiate, solve, instantiateType)
import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad (zipWithM, forM)
import Control.Monad.Error (MonadError (throwError))
import Control.Monad.State (gets)
import Data.List (find)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
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

wfType :: Ast.Type Unique Span -> Ast.Type Unique (Span, Type)
wfType (Ast.Node ty sp) = case ty of
  Ast.TSymbol alpha -> Ast.Node (Ast.TSymbol alpha) (sp, Type.Base alpha)
  Ast.TBorrow a -> 
    let a' = wfType a
    in Ast.Node (Ast.TBorrow a') (sp, Type.Borrow $ nodeType a')
  Ast.TArrow a b ->
    let a' = wfType a
        b' = wfType b
     in Ast.Node (Ast.TArrow a' b') (sp, Type.Arrow (nodeType a') (nodeType b'))

instantiatePattern ::
  Ast.Pattern Unique Span ->
  Type ->
  TcCtxM (Ast.Pattern Unique (Span, Type))
instantiatePattern (Ast.Node pat sp) scrutinee = case pat of
  Ast.PSymbol alpha -> do
    instantiate alpha scrutinee
    return $ Ast.Node (Ast.PSymbol alpha) (sp, scrutinee)
  Ast.PAnno p t -> do
    let t'@(Ast.Node _ (_, t't)) = wfType t
    subtype sp scrutinee t't
    p' <- instantiatePattern p t't
    return $ Ast.Node (Ast.PAnno p' t') (sp, t't)
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
    p' <- instantiatePattern p a
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
    return (c, [arg'])
  (Type.Arrow (Type.Tuple as) _, _) | length args /= length as ->
    throwError $ TcError (Error sp "function called with wrong number of arguments")
  (Type.Arrow (Type.Tuple as) c, _) -> do
    args' <- zipWithM check args as
    return (c, args')
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
    p' <- instantiatePattern p (nodeType e1')
    e2' <- synth e2
    return $ Ast.Node (Ast.Let p' e1' e2') (sp, nodeType e2')
  Ast.Lam p e -> do
    alpha <- Type.Exist' <$> fresh
    beta <- Type.Exist' <$> fresh
    p' <- instantiatePattern p alpha
    e' <- check e beta
    return $ Ast.Node (Ast.Lam p' e') (sp, Type.Arrow alpha beta)
  Ast.App a as -> do
    a' <- synth a
    (c, as') <- synthApp sp (nodeType a') as
    return $ Ast.Node (Ast.App a' as') (sp, c)
  Ast.Dot _ (Ast.DotResolved _) -> undefined
  Ast.Dot a (Ast.DotUnresolved rest) -> do
    synthDot a >>= \case
      Left namespaceUniq -> do
        (symbol, t) <- lookupName sp namespaceUniq rest
        return $ Ast.Node (Ast.Symbol symbol) (sp, t)
      Right a' -> do
        let a't = nodeType a'
        case Type.name a't of
          Just namespaceUniq -> do
            (symbol, f) <- lookupName sp namespaceUniq rest
            let symbolNode = Ast.Node (Ast.Symbol symbol) (sp, f)
            f' <- applyDotType sp f a't
            return $ Ast.Node (Ast.Dot a' $ Ast.DotResolved symbolNode) (sp, f')
          Nothing -> throwError $ TcError (Error sp $ Text.pack ("cannot use dot notation on type " ++ show a't))
  Ast.Unit -> return $ Ast.Node Ast.Unit (sp, Type.unit)
  Ast.Def name args ret e rest -> do
    args' <- mapM (\pat -> fresh >>= instantiatePattern pat . Type.Exist') args
    let ret' = fmap wfType ret
    let argsTy = fmap nodeType args'
    retTy <- case ret' of
      Just n -> return $ nodeType n
      Nothing -> Type.Exist' <$> fresh
    let funcTy = Type.arrow argsTy retTy
    instantiate name funcTy
    e' <- check e retTy
    env <- getEnv
    instantiate name (apply env funcTy)
    rest' <- synth rest
    return $ Ast.Node (Ast.Def name args' ret' e' rest') (sp, funcTy)
  Ast.ExternDef name args ret cident rest -> do
    args' <- mapM (\pat -> fresh >>= instantiatePattern pat . Type.Exist') args
    let ret' = wfType ret
    let argsTy = fmap nodeType args'
    let retTy = nodeType ret'
    let funcTy = Type.arrow argsTy retTy
    env <- getEnv
    instantiate name (apply env funcTy)
    rest' <- synth rest
    return $ Ast.Node (Ast.ExternDef name args' ret' cident rest') (sp, funcTy)
  Ast.Type extern name cident rest -> do
    let t = case (extern, name) of
          (Ast.Extern, Unique.Builtin name') -> Type.Intrinsic name'
          _ -> Type.Base name
    instantiateType name t
    rest' <- synth rest
    return $ Ast.Node (Ast.Type extern name cident rest') (sp, t)
  Ast.Match scrutinee branches -> do
    scrutinee' <- synth scrutinee
    let t = nodeType scrutinee'
    alpha <- Type.Exist' <$> fresh
    branches' <- forM branches $ \(pat, guards, e) -> do
      pat' <- instantiatePattern pat t
      guards' <- mapM (`check` Type.bool) guards
      e' <- check e alpha
      return (pat', guards', e')
    env <- getEnv
    return $ Ast.Node (Ast.Match scrutinee' branches') (sp, apply env alpha)

applyDotType :: Span -> Type -> Type -> TcCtxM Type
applyDotType sp f b = case f of
  Type.Arrow a@(Type.Tuple []) c -> do
    subtype sp a b
    return c
  Type.Arrow (Type.Tuple (a:as)) c -> do
    subtype sp a b
    return $ Type.arrow as c
  Type.Arrow a c -> do
    subtype sp a b
    return (Type.Arrow (Type.Tuple []) c)
  _ -> throwError $ TcError (Error sp $ Text.pack ("cannot call type " ++ show f))
