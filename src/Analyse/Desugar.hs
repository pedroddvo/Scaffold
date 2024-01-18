module Analyse.Desugar where

import Analyse.Infer (Typed (nodeType), wfType)
import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad.State (State, evalState, execState, gets, modify, zipWithM)
import Core (Core (..))
import Core qualified
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Debug.Trace
import Syntax.Ast qualified as Ast

data DesugarState = DesugarState
  { ds_core :: Core,
    ds_unique_gen :: Unique.Id
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

desugar :: Typed a => Unique.Id -> Ast.Expr Unique a -> DesugarState
desugar gen program = execState (desugarProgram program) initState
  where
    initState =
      DesugarState
        { ds_core =
            Core
              { core_defs = [],
                core_type_defs = [],
                core_extern_defs = []
              },
          ds_unique_gen = gen
        }

desugarPattern :: Typed a => Ast.Pattern Unique a -> DesugarM (Core.AltCon, Type)
desugarPattern node@(Ast.Node kind _) = case kind of
  Ast.PAnno p _ -> desugarPattern p
  Ast.PSymbol uniq -> return (Core.AltBind uniq, nodeType node)
  Ast.PWildcard -> return (Core.AltWildcard, nodeType node)
  Ast.PNumeric num -> return (Core.AltLiteral (Core.LitNumeric num), nodeType node)

desugarExpr :: Typed a => Ast.Expr Unique a -> DesugarM Core.Expr
desugarExpr thisNode@(Ast.Node kind d) = case kind of
  Ast.Symbol uniq -> return $ Core.Var uniq
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
    let f = Type.unarrow $ nodeType a
    as' <- zipWithM desugarArg as f
    let e = Core.App (nodeType thisNode) a' (map snd as')
    let e' = foldr ($) e (concatMap fst as')
    return e'
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

desugarArg :: Typed a => Ast.Expr Unique a -> Type -> DesugarM ([Core.Expr -> Core.Expr], Core.Arg)
desugarArg e@(Ast.Node kind _) t = do
  e' <- desugarExpr e
  case (kind, t) of
    (_, Type.Borrow t') -> return ([], Core.Arg t' e' Core.PassBorrow)
    (_, t') -> return ([], Core.Arg t' e' Core.PassOwned)

desugarBranch :: Typed a => Ast.MatchBranch Unique a -> DesugarM Core.Alt
desugarBranch (pat, guards, e) = do
  (pat', t) <- desugarPattern pat
  guards' <- mapM desugarExpr guards
  e' <- desugarExpr e
  return $ Core.Alt pat' guards' t e'

desugarProgram :: Typed a => Ast.Expr Unique a -> DesugarM ()
desugarProgram node@(Ast.Node kind _) = case kind of
  Ast.Def name args _ e rest -> do
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
  Ast.Type Ast.Extern name cident rest -> do
    newTypeDef name (Core.TypeDefExtern cident (nodeType node))
    desugarProgram rest
  Ast.Unit -> return ()
  _ -> undefined
