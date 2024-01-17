{-# LANGUAGE TupleSections #-}

module Analyse.Perceus where

import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad.Reader
import Control.Monad.State
import Core
import Data.Bifunctor (second)
import Data.Foldable (foldr')
import Data.List (unzip4)
import Data.Maybe (catMaybes, fromMaybe, maybeToList)
import Data.MultiSet (MultiSet, (\\))
import Data.MultiSet qualified as MS
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace
import Syntax.Name (Name (..))

translate :: Expr -> PerceusM Expr
translate = \case
  Var x ->
    isRefCounted x >>= \case
      True -> fromMaybe (Var x) <$> useUnique x
      False -> return $ Var x
  Lit lit -> return $ Lit lit
  Let x t e1 e2 -> do
    isRc <- typeIsRefCounted t
    unless isRc $ setNotRC x
    e2' <- ownedInScope (MS.singleton x) $ translate e2
    e1' <- translate e1
    return $ Let x t e1' e2'
  App t e@(Var _) args -> do
    translateApp args t e

translateApp :: [Arg] -> Type -> Expr -> PerceusM Expr
translateApp args t expr = do
  (lets, drops, args') <- unzip3 <$> reverseMapM translateAppArg args
  expr' <- case concat drops of
    [] -> return $ App t expr args'
    drops' -> do
      name <- fresh
      expr' <- foldM (flip genDrop) (Var name) drops'
      return $ Let name t (App t expr args') expr'
  return $ foldr' ($) expr' (concat lets)

translateAppArg :: Arg -> PerceusM ([Expr -> Expr], [Unique], Arg)
translateAppArg (Arg t e@(Var name) PassBorrow) =
  isRefCounted name >>= \case
    True ->
      ([],,Arg t e PassBorrow)
        . maybeToList
        . fmap (const name)
        <$> useUniqueBorrowed name
    False -> return ([], [], Arg t e PassBorrow)
translateAppArg (Arg t e PassBorrow) = do
  e' <- translate e
  name <- fresh
  return ([Let name t e'], [name], Arg t (Var name) PassBorrow)
translateAppArg (Arg t e PassOwned) = do
  e' <- translate e
  name <- fresh
  return ([Let name t e'], [], Arg t (Var name) PassOwned)

type Owned = MultiSet Unique

type Borrowed = MultiSet Unique

data Env = Env
  { owned :: Owned,
    borrowed :: Borrowed,
    globals :: Set Unique
  }

type Live = MultiSet Unique

data PerceusState = PerceusState
  { ps_uuid :: Unique.Id,
    ps_not_refcounted :: Set Unique,
    ps_live :: Live
  }

type PerceusM = ReaderT Env (State PerceusState)

runPerceus :: Set Unique -> Set Unique -> Unique.Id -> Expr -> (Expr, Unique.Id)
runPerceus nonRc globs uuid =
  second ps_uuid
    . flip runState initState
    . flip runReaderT initEnv
    . translate
  where
    initEnv =
      Env
        { owned = MS.empty,
          borrowed = MS.empty,
          globals = globs
        }

    initState =
      PerceusState
        { ps_uuid = uuid,
          ps_live = MS.empty,
          ps_not_refcounted = nonRc
        }

fresh :: PerceusM Unique
fresh =
  (`Unique.Id` Nothing)
    <$> (modify (\s -> s {ps_uuid = ps_uuid s + 1}) >> gets ps_uuid)

genDrop :: Unique -> Expr -> PerceusM Expr
genDrop x y =
  isRefCounted x >>= \case
    True -> return (Drop x y)
    False -> return y

useUnique :: Unique -> PerceusM (Maybe Expr)
useUnique name = do
  live <- isLive name
  borrowed <- isBorrowed name
  markLive name
  if live || borrowed
    then return $ Just (Dup name (Var name))
    else return Nothing

useUniqueBorrowed :: Unique -> PerceusM (Maybe Expr)
useUniqueBorrowed name = do
  live <- isLive name
  borrowed <- isBorrowed name
  markLive name
  if not (live || borrowed)
    then return $ Just (Drop name (Var name))
    else return Nothing

forget :: Live -> PerceusM ()
forget names = modify (\s -> s {ps_live = ps_live s \\ names})

reverseMapM :: Monad m => (a -> m b) -> [a] -> m [b]
reverseMapM action args = do
  args' <- mapM action (reverse args)
  return $ reverse args'

isLive :: Unique -> PerceusM Bool
isLive x = gets (MS.member x . ps_live)

updateOwned :: (Owned -> Owned) -> PerceusM a -> PerceusM a
updateOwned f = local (\e -> e {owned = f (owned e)})

extendOwned :: Owned -> PerceusM a -> PerceusM a
extendOwned = updateOwned . MS.union

scoped :: Live -> PerceusM a -> PerceusM a
scoped vars f = do
  expr <- f
  forget vars
  return expr

ownedInScope :: Live -> PerceusM Expr -> PerceusM Expr
ownedInScope vars f = scoped vars $ extendOwned vars $ do
  expr <- f
  live <- getLive
  foldM (flip genDrop) expr (vars \\ live)

markLive :: Unique -> PerceusM ()
markLive x = modify (\s -> s {ps_live = MS.insert x (ps_live s)})

getLive :: PerceusM Live
getLive = gets ps_live

isOwned :: Unique -> PerceusM Bool
isOwned x = MS.member x <$> getOwned

getOwned :: PerceusM Owned
getOwned = asks owned

isBorrowed :: Unique -> PerceusM Bool
isBorrowed x = not <$> isOwned x

isRefCounted :: Unique -> PerceusM Bool
isRefCounted x = gets (Set.notMember x . ps_not_refcounted)

setNotRC :: Unique -> PerceusM ()
setNotRC x = modify (\s -> s {ps_not_refcounted = Set.insert x (ps_not_refcounted s)})

typeIsRefCounted :: Type -> PerceusM Bool
typeIsRefCounted = \case
  Type.Intrinsic (Name "Int") -> return False
  Type.Intrinsic (Name "String") -> return True
  -- external types
  Type.Base uniq -> isRefCounted uniq 
  _ -> return True
