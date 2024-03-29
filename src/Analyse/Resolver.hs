module Analyse.Resolver where

import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad (foldM, forM)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.State (MonadState (get), State, evalState, gets, modify, runState)
import Data.Bifunctor (second)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Debug.Trace (traceShowM)
import Error (Error (..))
import Span (Span)
import Syntax.Ast (node, node2, node3)
import Syntax.Ast qualified as Ast
import Syntax.Name (Name (..))
import Syntax.Name qualified as Name

type ResolvedMap = Map (Name Text) Unique

data ResolverState = ResolverState
  { rs_id_counter :: Unique.Id,
    rs_module_names :: ResolvedMap,
    rs_inductive_ctors :: Set Unique
  }

type ResolverM = ExceptT Error (State ResolverState)

fresh :: ResolverM Unique.Id
fresh = modify (\s -> s {rs_id_counter = rs_id_counter s + 1}) >> gets rs_id_counter

getInductiveCtor :: ResolvedMap -> Name Text -> ResolverM (Maybe Unique)
getInductiveCtor env name = case Map.lookup name env of
  Just n -> gets (f n . Set.member n . rs_inductive_ctors)
  Nothing -> return Nothing
  where
    f n True = Just n
    f _ False = Nothing

instantiateName :: ResolvedMap -> Name Text -> ResolverM (ResolvedMap, Unique)
instantiateName m v = do
  uniq <- (`Unique.Id` Just v) <$> fresh
  modify (\s -> s {rs_module_names = Map.insert v uniq (rs_module_names s)})
  return (Map.insert v uniq m, uniq)

instantiateParts :: ResolvedMap -> [Text] -> Name Text -> ResolverM (ResolvedMap, Unique)
instantiateParts m path (Namespace v vs) = do
  let path' = path ++ [v]
  let partialName = Name.fromList path'
  gets (Map.lookup partialName . rs_module_names) >>= \case
    Just _ -> instantiateParts m path' vs
    Nothing -> do
      (m', _) <- instantiateName m partialName
      instantiateParts m' path' vs
instantiateParts m path (Name v) = do
  let fullName = Name.fromList (path ++ [v])
  instantiateName m fullName

instantiate :: ResolvedMap -> Name Text -> ResolverM (ResolvedMap, Unique)
instantiate m = instantiateParts m []

check :: ResolvedMap -> Span -> Name Text -> ResolverM Unique
check m sp v = case Map.lookup v m of
  Just uniq -> return uniq
  Nothing -> throwError (Error sp "undefined symbol")

resolveType :: ResolvedMap -> Ast.Type (Name Text) Span -> ResolverM (Ast.Type Unique Span)
resolveType env ty =
  let sp = Ast.node_data ty
   in case Ast.node_kind ty of
        Ast.TSymbol alpha -> node Ast.TSymbol ty <$> check env sp alpha
        Ast.TArrow a b -> node2 Ast.TArrow ty <$> resolveType env a <*> resolveType env b
        Ast.TBorrow e -> node Ast.TBorrow ty <$> resolveType env e
        Ast.TApp a as -> node2 Ast.TApp ty <$> resolveType env a <*> mapM (resolveType env) as

instantiatePattern :: ResolvedMap -> Ast.Pattern (Name Text) Span -> ResolverM (ResolvedMap, Ast.Pattern Unique Span)
instantiatePattern env pat =
  case Ast.node_kind pat of
    Ast.PSymbol alpha ->
      getInductiveCtor env alpha >>= \case
        Just ctor -> return (env, Ast.Node (Ast.PCtor ctor []) (Ast.node_data pat))
        Nothing -> fmap (node Ast.PSymbol pat) <$> instantiate env alpha
    Ast.PCtor alpha args -> do
      let sp = Ast.node_data pat
      getInductiveCtor env alpha >>= \case
        Just ctor -> do
          (env', args') <- instantiateMany instantiatePattern env args
          return (env', Ast.Node (Ast.PCtor ctor args') sp)
        Nothing -> throwError (Error sp "constructor not in scope")
    Ast.PAnno p t -> do
      t' <- resolveType env t
      (env', p') <- instantiatePattern env p
      return (env', node2 Ast.PAnno pat p' t')
    Ast.PNumeric num -> return (env, node Ast.PNumeric pat num)
    Ast.PWildcard -> return (env, Ast.Node Ast.PWildcard (Ast.node_data pat))

instantiateMany ::
  (ResolvedMap -> a -> ResolverM (ResolvedMap, b)) ->
  ResolvedMap ->
  [a] ->
  ResolverM (ResolvedMap, [b])
instantiateMany f env as = second reverse <$> foldM (\(env', ys) x -> fmap (: ys) <$> f env' x) (env, []) as

resolveExpr :: ResolvedMap -> Ast.Expr (Name Text) Span -> ResolverM (Ast.Expr Unique Span)
resolveExpr env expr =
  let sp = Ast.node_data expr
   in case Ast.node_kind expr of
        Ast.Symbol alpha -> node Ast.Symbol expr <$> check env sp alpha
        Ast.Numeric num -> return $ node Ast.Numeric expr num
        Ast.String str -> return $ node Ast.String expr str
        Ast.Lam p e -> do
          (env', p') <- instantiatePattern env p
          e' <- resolveExpr env' e
          return $ node2 Ast.Lam expr p' e'
        Ast.Let p e1 e2 -> do
          e1' <- resolveExpr env e1
          (env', p') <- instantiatePattern env p
          e2' <- resolveExpr env' e2
          return $ node3 Ast.Let expr p' e1' e2'
        Ast.App a as -> do
          a' <- resolveExpr env a
          as' <- mapM (resolveExpr env) as
          return $ node2 Ast.App expr a' as'
        -- We cannot fully resolve dot until typechecking
        Ast.Dot _ (Ast.DotResolved _) -> undefined
        Ast.Dot a (Ast.DotUnresolved b) -> do
          a' <- resolveExpr env a
          return $ node2 Ast.Dot expr a' (Ast.DotUnresolved b)
        Ast.Unit -> return $ Ast.Node Ast.Unit sp
        Ast.Def name vars args ret e rest -> do
          (env', name') <-
            if Name.moduleName name `elem` intrinsicDefNames
              then return (env, Unique.Builtin name)
              else instantiate env name
          (envVars, vars') <- instantiateMany instantiate env' vars
          ret' <- mapM (resolveType envVars) ret
          (env'', args') <- instantiateMany instantiatePattern envVars args
          e' <- resolveExpr env'' e
          rest' <- resolveExpr env' rest
          return $ Ast.Node (Ast.Def name' vars' args' ret' e' rest') sp
        Ast.ExternDef name args ret cident rest -> do
          ret' <- resolveType env ret
          (env', name') <- instantiate env name
          (_, args') <- instantiateMany instantiatePattern env' args
          rest' <- resolveExpr env' rest
          return $ Ast.Node (Ast.ExternDef name' args' ret' cident rest') sp
        Ast.ExternType name cident rest -> do
          (env', name') <- if Name.moduleName name `elem` intrinsicTypes then return (Map.insert name (Unique.Builtin name) env, Unique.Builtin name) else instantiate env name
          rest' <- resolveExpr env' rest
          return $ Ast.Node (Ast.ExternType name' cident rest') sp
        Ast.InductiveType name vars ctors rest -> do
          (env', name') <- instantiate env name
          (envVars, vars') <- instantiateMany instantiate env' vars
          (env'', ctors') <- instantiateMany (instantiateCtor name) envVars ctors
          rest' <- resolveExpr env'' rest
          return $ Ast.Node (Ast.InductiveType name' vars' ctors' rest') sp
        Ast.Match scrutinee branches -> do
          scrutinee' <- resolveExpr env scrutinee
          branches' <- mapM (resolveMatchBranch env) branches
          return $ Ast.Node (Ast.Match scrutinee' branches') sp

instantiateCtor ::
  Name Text ->
  ResolvedMap ->
  Ast.Ctor (Name Text) Span ->
  ResolverM (ResolvedMap, Ast.Ctor Unique Span)
instantiateCtor namespace env (Ast.Ctor name args) = do
  args' <- forM args $ \(arg, t) -> do
    (_, arg') <- instantiate env arg
    t' <- resolveType env t
    return (arg', t')
  (env', name') <- instantiate env (namespace <> name)
  modify (\s -> s {rs_inductive_ctors = Set.insert name' (rs_inductive_ctors s)})
  return (env', Ast.Ctor name' args')

resolveMatchBranch ::
  ResolvedMap ->
  Ast.MatchBranch (Name Text) Span ->
  ResolverM (Ast.MatchBranch Unique Span)
resolveMatchBranch env (pat, guards, e) = do
  (env', pat') <- instantiatePattern env pat
  guards' <- mapM (resolveExpr env') guards
  e' <- resolveExpr env' e
  return (pat', guards', e')

intrinsicDefNames :: [Text]
intrinsicDefNames = ["main"]

intrinsicTypes :: [Text]
intrinsicTypes = ["Int", "String", "Bool"]

runResolver :: ResolverM a -> (Either Error a, ResolverState)
runResolver =
  flip
    runState
    ( ResolverState
        { rs_id_counter = 0,
          rs_module_names = Map.fromList intrinsicModules,
          rs_inductive_ctors = Set.empty
        }
    )
    . runExceptT
  where
    intrinsicModules = map (\t -> let n = Name t in (n, Unique.Builtin n)) intrinsicTypes
