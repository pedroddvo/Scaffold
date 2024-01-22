module Analyse.Desugar where

import Analyse.Infer (Typed (nodeType), wfType)
import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad (forM)
import Control.Monad.State (State, evalState, execState, gets, modify, zipWithM)
import Core (Core (..))
import Core qualified
import Data.Bifunctor (second)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Debug.Trace
import Syntax.Ast qualified as Ast
import Syntax.Name (Name (..))

data DesugarState = DesugarState
  { ds_core :: Core,
    ds_unique_gen :: Unique.Id,
    ds_inductive_ctor_args :: Map Unique Int
  }

type DesugarM = State DesugarState

fresh :: DesugarM Unique
fresh =
  (`Unique.Id` Nothing)
    <$> (modify (\s -> s {ds_unique_gen = ds_unique_gen s + 1}) >> gets ds_unique_gen)

modifyCore :: (Core -> Core) -> DesugarM ()
modifyCore f = modify (\s -> s {ds_core = f (ds_core s)})

newDef :: Unique -> Core.Def -> DesugarM ()
newDef k v = modifyCore (\s -> s {core_defs = (k, v) : core_defs s})

newExternDef :: Unique -> Core.ExternDef -> DesugarM ()
newExternDef k v = modifyCore (\s -> s {core_extern_defs = (k, v) : core_extern_defs s})

newTypeDef :: Unique -> Core.TypeDef -> DesugarM ()
newTypeDef k v = modifyCore (\s -> s {core_type_defs = (k, v) : core_type_defs s})

newInductiveType :: Unique -> Core.InductiveType -> DesugarM ()
newInductiveType k v = modifyCore (\s -> s {core_inductive_types = (k, v) : core_inductive_types s})

desugar :: Typed a => Unique.Id -> Ast.Expr Unique a -> DesugarState
desugar gen program = execState (desugarProgram program) initState
  where
    initState =
      DesugarState
        { ds_core =
            Core
              { core_defs = [],
                core_type_defs = [],
                core_extern_defs = [],
                core_inductive_types = []
              },
          ds_unique_gen = gen,
          ds_inductive_ctor_args = Map.empty
        }

desugarPattern :: Typed a => Ast.Pattern Unique a -> DesugarM (Core.AltCon, Type)
desugarPattern node@(Ast.Node kind _) = case kind of
  Ast.PAnno p _ -> desugarPattern p
  Ast.PCtor alpha args -> do
    args' <- mapM desugarPattern args
    return (Core.AltCtor alpha args', nodeType node)
  Ast.PSymbol uniq -> return (Core.AltBind uniq, nodeType node)
  Ast.PWildcard -> return (Core.AltWildcard, nodeType node)
  Ast.PNumeric num -> return (Core.AltLiteral (Core.LitNumeric num), nodeType node)

desugarExpr :: Typed a => Ast.Expr Unique a -> DesugarM Core.Expr
desugarExpr thisNode@(Ast.Node kind d) = case kind of
  Ast.Symbol uniq ->
    gets (Map.lookup uniq . ds_inductive_ctor_args) >>= \case
      Just 0 -> return $ Core.App (nodeType thisNode) (Core.Var uniq) []
      _ -> return $ Core.Var uniq
  Ast.Numeric num -> return $ Core.Lit (Core.LitNumeric num)
  Ast.String str -> return $ Core.Lit (Core.LitString str)
  Ast.Let p e1 e2 -> do
    e1' <- desugarExpr e1
    (name, _) <- desugarPattern p
    e2' <- desugarExpr e2
    case name of
      Core.AltWildcard -> (\x -> Core.Let x (nodeType e1) e1' e2') <$> fresh
      Core.AltBind x -> return $ Core.Let x (nodeType e1) e1' e2'
      _ -> undefined
  Ast.App (Ast.Node (Ast.Dot a (Ast.DotResolved f)) _) as -> do
    desugarExpr (Ast.Node (Ast.App f (a : as)) d)
  Ast.App a as -> do
    a' <- desugarExpr a
    let (_, f) = Type.unarrow $ nodeType a
    as' <- zipWithM desugarArg as f
    let e = Core.App (nodeType thisNode) a' as'
    return e
  Ast.Lam p e -> do
    (name, _) <- desugarPattern p
    e' <- desugarExpr e
    case name of
      Core.AltWildcard -> (`Core.Lam` e') <$> fresh
      Core.AltBind x -> return $ Core.Lam x e'
      _ -> undefined
  Ast.Match e branches -> do
    e' <- desugarExpr e
    branches' <- mapM desugarBranch branches
    return $ Core.Case e' (nodeType e) branches' (nodeType thisNode)
  _ -> undefined

desugarArg :: Typed a => Ast.Expr Unique a -> Type -> DesugarM Core.Arg
desugarArg e t = do
  let eT = nodeType e
  e' <- desugarExpr e
  let pass = case t of
        Type.Borrow _ -> Core.PassBorrow
        _ -> Core.PassOwned
  let eBox = case t of
        Type.Named' _
          | not (Type.isBoxed eT) ->
              Core.App
                Type.boxed
                (Core.Var $ Unique.Builtin $ Name "sfd_box")
                [Core.Arg eT e' Core.PassOwned]
        _ -> e'
  return $ Core.Arg t eBox pass

desugarBranch :: Typed a => Ast.MatchBranch Unique a -> DesugarM Core.Alt
desugarBranch (pat, guards, e) = do
  (pat', t) <- desugarPattern pat
  guards' <- mapM desugarExpr guards
  e' <- desugarExpr e
  return $ Core.Alt pat' guards' t e'

desugarProgram :: Typed a => Ast.Expr Unique a -> DesugarM ()
desugarProgram node@(Ast.Node kind _) = case kind of
  Ast.Def name _ args _ e rest -> do
    e' <- desugarExpr e
    args' <- mapM desugarPattern args
    newDef
      name
      ( Core.Def
          { Core.def_expr_type = nodeType e,
            Core.def_expr = e',
            Core.def_args = args'
          }
      )
    desugarProgram rest
  Ast.ExternDef name args ret cident rest -> do
    args' <- mapM desugarPattern args
    newExternDef
      name
      ( Core.ExternDef
          { Core.extern_def_args = args',
            Core.extern_def_return_type = nodeType ret,
            Core.extern_def_name = cident
          }
      )
    desugarProgram rest
  Ast.ExternType name cident rest -> do
    newTypeDef name (Core.TypeDefExtern cident (nodeType node))
    desugarProgram rest
  Ast.InductiveType name _ ctors rest -> do
    ctors' <- zipWithM desugarCtor [0 ..] ctors
    newInductiveType
      name
      ( Core.InductiveType
          { Core.inductive_type_ctors = ctors'
          }
      )
    desugarProgram rest
  Ast.Unit -> return ()
  _ -> undefined

desugarCtor :: (Typed a) => Int -> Ast.Ctor Unique a -> DesugarM (Unique, Core.InductiveTypeCtor)
desugarCtor i (Ast.Ctor ctorName ctorArgs) = do
  modify (\s -> s {ds_inductive_ctor_args = Map.insert ctorName (length ctorArgs) (ds_inductive_ctor_args s)})
  return (ctorName, Core.InductiveTypeCtor (map (second nodeType) ctorArgs) i)
