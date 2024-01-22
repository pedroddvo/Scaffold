module Analyse.TcContext where

import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State (MonadState (get), State, evalState, gets, modify, runState)
import Data.Functor ((<&>))
import Data.Map (Map)
import Data.Map qualified as Map
import Error (Error)
import Data.Text (Text)
import Analyse.Resolver (ResolvedMap)
import Syntax.Name (Name)

data TcState = TcState
  { tc_vars :: Map Unique Type,
    tc_types :: Map Unique Type,
    tc_solved :: Map Unique Type,
    tc_resolved_vars :: ResolvedMap,
    tc_resolved_vars_kv :: [(Name Text, Unique)],
    tc_exist_counter :: Unique.Id
  }

data TcError = SubtypeFailure | TcError Error

type TcCtxM = ExceptT TcError (State TcState)

-- Generate a new existential variable
fresh :: TcCtxM Unique
fresh =
  (`Unique.Id` Nothing)
    <$> (modify (\s -> s {tc_exist_counter = tc_exist_counter s + 1}) >> gets tc_exist_counter)

apply :: TcState -> Type -> Type
apply env t' = case t' of
  Type.Base {} -> t'
  Type.Var Type.Named {} -> t'
  Type.Var (Type.Exist alpha) -> case Map.lookup alpha (tc_solved env) of
    Just t -> apply env t
    Nothing -> t'
  Type.Arrow a b -> Type.Arrow (apply env a) (apply env b)
  Type.App a b -> Type.App (apply env a) (map (apply env) b)
  Type.Tuple as -> Type.Tuple (map (apply env) as)
  Type.Borrow t -> Type.Borrow (apply env t)
  Type.Forall alpha a -> Type.Forall alpha (apply env a)

instantiate :: Unique -> Type -> TcCtxM ()
instantiate name t = modify (\s -> s {tc_vars = Map.insert name t (tc_vars s)})

instantiateType :: Unique -> Type -> TcCtxM ()
instantiateType name t = modify (\s -> s {tc_types = Map.insert name t (tc_types s)})

solve :: Unique -> Type -> TcCtxM ()
solve exist t = modify (\s -> s {tc_solved = Map.insert exist t (tc_solved s)})

getEnv :: TcCtxM TcState
getEnv = get

runTc :: ResolvedMap -> Unique.Id -> TcCtxM a -> Either TcError a
runTc m uuid =
  flip evalState tcState
    . runExceptT
  where
    tcState =
      TcState
        { tc_vars = Map.empty,
          tc_solved = Map.empty,
          tc_types = Map.empty,
          tc_exist_counter = uuid,
          tc_resolved_vars = m,
          tc_resolved_vars_kv = Map.toList m
        }
