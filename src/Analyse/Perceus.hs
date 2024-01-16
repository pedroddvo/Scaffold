module Analyse.Perceus where

import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad.State (State, gets, modify)
import Control.Monad.State.Lazy
import Core (Arg (..), Expr (..), PassKind (..))
import Data.Bifunctor (second)
import Data.Maybe (catMaybes)
import Data.MultiSet (MultiSet, (\\))
import Data.MultiSet qualified as S
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace (traceShowM)

type Env = MultiSet Unique

data PerceusState = PerceusState
  { ps_owned :: Env,
    ps_borrowed :: Env,
    ps_globals :: Set Unique,
    ps_uuid :: Unique.Id
  }
  deriving (Show)

type PerceusM = State PerceusState

translate :: Expr -> PerceusM Expr
translate = \case
  Var x -> do
    owned <- getOwned
    if S.member x owned
      then do
        consume x
        return $ Var x
      else
        gets (Set.member x . ps_globals) >>= \case
          True -> return (Var x)
          False -> return $ Dup x (Var x)
  Lit lit -> return $ Lit lit
  Let x t e1 e2 -> do
    instantiate x
    ownedA <- getOwned
    e2' <- translate e2
    ownedB <- getOwned
    let consumedA = S.difference ownedA ownedB
    borrow consumedA
    consume x
    e1' <- translate e1
    return $
      if S.member x consumedA
        then Let x t e1' e2'
        else Let x t e1' (Drop x e2')
  App t e1 e2 -> do
    ownedA <- getOwned
    (drops, e2') <- unzip . reverse <$> foldM (\l arg -> (: l) <$> translateArg arg) [] e2
    ownedB <- getOwned
    let consumed = S.difference ownedA ownedB
    borrow consumed
    e1' <- translate e1
    let app = App t e1' e2'
    case catMaybes drops of
      [] -> return app
      drops' -> do
        p <- fresh
        return . Let p t app $ foldr Drop (Var p) drops'

translateArg :: Arg -> PerceusM (Maybe Unique, Arg)
translateArg (Arg e PassOwned) = do
  e' <- translate e
  return (Nothing, Arg e' PassOwned)
translateArg (Arg (Var x) PassBorrow) = do
  let e = Var x
  borrowed <- getBorrowed
  drops <-
    if S.notMember x borrowed
      then do
        consume x
        return $ Just x
      else return Nothing
  return (drops, Arg e PassBorrow)

borrow :: Env -> PerceusM ()
borrow env = modify (\s -> s {ps_borrowed = S.union (ps_borrowed s) env})

consume :: Unique -> PerceusM ()
consume uniq = modify (\s -> s {ps_owned = S.delete uniq (ps_owned s)})

borrowAll :: PerceusM ()
borrowAll = modify (\s -> s {ps_borrowed = S.union (ps_borrowed s) (ps_owned s), ps_owned = S.empty})

instantiate :: Unique -> PerceusM ()
instantiate uniq = modify (\s -> s {ps_owned = S.insert uniq (ps_owned s)})

instantiateAll :: Env -> PerceusM ()
instantiateAll env = modify (\s -> s {ps_owned = env})

scoped :: PerceusM a -> PerceusM a
scoped f = do
  ownedA <- getOwned
  borrowedA <- getBorrowed
  borrowAll
  a <- f
  modify (\s -> s {ps_owned = ownedA, ps_borrowed = borrowedA})
  return a

getOwned :: PerceusM Env
getOwned = gets ps_owned

getBorrowed :: PerceusM Env
getBorrowed = gets ps_borrowed

fresh :: PerceusM Unique
fresh =
  (`Unique.Id` Nothing)
    <$> (modify (\s -> s {ps_uuid = ps_uuid s + 1}) >> gets ps_uuid)

runPerceus :: Set Unique -> Unique.Id -> Expr -> (Expr, Unique.Id)
runPerceus globals uuid = second ps_uuid . flip runState initState . translate
  where
    initState =
      PerceusState
        { ps_owned = S.empty,
          ps_borrowed = S.empty,
          ps_globals = globals,
          ps_uuid = uuid
        }
