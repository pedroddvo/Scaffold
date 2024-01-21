{-# LANGUAGE TupleSections #-}

module Analyse.Perceus where

import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad.Reader
import Control.Monad.State
import Core
import Data.Bifunctor (Bifunctor (first), second)
import Data.Foldable (foldr')
import Data.List (unzip4)
import Data.Maybe (catMaybes, fromMaybe, maybeToList)
import Data.MultiSet (MultiSet, (\\))
import Data.MultiSet qualified as MS
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace
import GHC.List (foldl')
import Syntax.Name (Name (..))

translate :: Expr -> PerceusM Expr
translate = \case
  Var x -> do
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
  Case e@(Var scrutinee) eT branches t -> do
    branches' <- translateAlts scrutinee branches eT
    return $ Case e eT branches' t
  Case e eT branches t -> do
    name <- fresh (Just eT)
    let expr = Var name
    translate (Let name eT e (Case expr eT branches t))

translateAlts :: Unique -> [Alt] -> Type -> PerceusM [Alt]
translateAlts scrutinee alts t = do
  scrutOwned <- isOwned scrutinee
  live <- getLive
  owned <- getOwned
  when scrutOwned $ markLive scrutinee
  reverseMapM (translateAlt live owned scrutOwned t) alts

translateAlt :: Live -> Owned -> Bool -> Type -> Alt -> PerceusM Alt
translateAlt live outsideOwned scrutOwned scrutT (Alt con guards t e) = do
  bvs <- instantiateBoundVars scrutT con
  let ownedBvs = if scrutOwned then bvs else MS.empty
  scoped bvs $ extendOwned ownedBvs $ do
    (e', liveAlt) <- isolateWith live $ translate e
    markLives liveAlt
    let drops = outsideOwned \\ liveAlt
    let dups = MS.intersection ownedBvs liveAlt
    guards' <- mapM (withOwned MS.empty . translate) guards
    eWithDrops <- foldM (flip genDrop) e' drops
    eWithDups <- foldM (flip genDup) eWithDrops dups
    return $ Alt con guards' t eWithDups

-- translateAlts :: Unique -> [Alt] -> Type -> PerceusM [Alt]
-- translateAlts scrutinee alts t = do
--   live <- getLive
--   owned <- isOwned scrutinee
--   altsF <- reverseMapM (translateAlt owned live t) alts
--   isRc <- typeIsRefCounted t
--   unless isRc $ setNotRC scrutinee
--   when owned $ markLive scrutinee
--   live' <- getLive
--   mapM ($ live') altsF
--
-- type IsOwned = Bool
--
-- translateAlt :: IsOwned -> Live -> Type -> Alt -> PerceusM (Live -> PerceusM Alt)
-- translateAlt owned live t (Alt con tests altT e) = do
--   testF <- translateGuard owned live con t e tests
--   return $ \c -> do
--     (e', tests') <- testF c
--     return $ Alt con tests' altT e'

-- type Guard = Expr

-- translateGuard :: IsOwned -> Live -> AltCon -> Type -> Expr -> [Guard] -> PerceusM (Live -> PerceusM (Expr, [Guard]))
-- translateGuard owned live con t e tests = do
--   bvs <- instantiateBoundVars t con
--   let ownedBvs = if owned then bvs else MS.empty
--   scoped bvs $ extendOwned ownedBvs $ do
--     (e', liveAlt) <- isolateWith live $ translate e
--     markLives liveAlt
--     test' <- mapM (withOwned MS.empty . translate) tests
--     return $ \liveSomeAlt -> scoped bvs $ extendOwned ownedBvs $ do
--       let dups = MS.intersection ownedBvs liveAlt
--       drops <- filterM isOwned (MS.toList $ liveSomeAlt \\ liveAlt)
--       -- Alt con altT <$> altRc dups (MS.fromList drops) e' t
--       e'' <- altRc dups (MS.fromList drops) e'
--       return (e'', test')
--
-- type Dups = MultiSet Unique
-- type Drops = MultiSet Unique
--
-- altRc :: Dups -> Drops -> Expr -> PerceusM Expr
-- altRc dups drops e = do
--   drops' <- foldM (flip genDrop) e drops
--   dups' <- foldM (flip genDup) drops' dups
--   return dups'

instantiateBoundVars :: Type -> AltCon -> PerceusM (MultiSet Unique)
instantiateBoundVars scrutT con = case (scrutT, con) of
  (_, AltLiteral _) -> return MS.empty
  (t, AltBind n) -> do
    isRc <- typeIsRefCounted t
    unless isRc $ setNotRC n
    return $ MS.singleton n
  (_, AltCtor _ args) -> do
    args' <- mapM (\(n, t) -> instantiateBoundVars t n) args
    return $ MS.unions args'
  (_, AltWildcard) -> return MS.empty

translateApp :: [Arg] -> Type -> Expr -> PerceusM Expr
translateApp args t expr = do
  (lets, drops, args') <- unzip3 <$> reverseMapM translateAppArg args
  expr' <- case concat drops of
    [] -> return $ App t expr args'
    drops' -> do
      name <- fresh (Just t)
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
  name <- fresh (Just t)
  return ([Let name t e'], [name], Arg t (Var name) PassBorrow)
translateAppArg (Arg t e PassOwned) = do
  e' <- translate e
  name <- fresh (Just t)
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

runPerceus :: Set Unique -> Set Unique -> Unique.Id -> Core -> (Core, Unique.Id)
runPerceus nonRc globs uuid core =
  let (defNames, defs) = unzip (Core.core_defs core)
      (defs', uuid') = runDefs uuid defs
   in (core {core_defs = zip (reverse defNames) defs'}, uuid')
  where
    runDefs uid = foldl' (\(defs', uuid') def -> first (: defs') $ runDef def uuid') ([], uid)

    runDef def uid =
      let (expr, uuid') = runExpr (Core.def_args def) uid (Core.def_expr def)
       in (def {def_expr = expr}, uuid')

    runExpr' args e = do
      args' <- mapM (uncurry $ flip instantiateBoundVars) args

      ownedInScope (MS.unions args') (translate e)

    runExpr args uid e =
      second ps_uuid
        . flip runState (initState uid)
        . flip runReaderT initEnv
        $ runExpr' args e

    initEnv =
      Env
        { owned = MS.empty,
          borrowed = MS.empty,
          globals = globs
        }

    initState uid =
      PerceusState
        { ps_uuid = uid,
          ps_live = MS.empty,
          ps_not_refcounted = nonRc
        }

fresh :: Maybe Type -> PerceusM Unique
fresh (Just t) = do
  isRc <- typeIsRefCounted t
  x <- fresh Nothing
  unless isRc $ setNotRC x
  return x
fresh Nothing =
  (`Unique.Id` Nothing)
    <$> (modify (\s -> s {ps_uuid = ps_uuid s + 1}) >> gets ps_uuid)

genDrop :: Unique -> Expr -> PerceusM Expr
genDrop x y =
  isRefCounted x >>= \case
    True -> return (Drop x y)
    False -> return y

genDup :: Unique -> Expr -> PerceusM Expr
genDup x y =
  isRefCounted x >>= \case
    True -> return (Dup x y)
    False -> return y

useUnique :: Unique -> PerceusM (Maybe Expr)
useUnique name = do
  live <- isLive name
  borrowed <- isBorrowed name
  markLive name
  if live || borrowed
    then Just <$> genDup name (Var name)
    else return Nothing

useUniqueBorrowed :: Unique -> PerceusM (Maybe Expr)
useUniqueBorrowed name = do
  live <- isLive name
  borrowed <- isBorrowed name
  markLive name
  if not (live || borrowed)
    then Just <$> genDrop name (Var name)
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

withOwned :: Owned -> PerceusM a -> PerceusM a
withOwned = updateOwned . const

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

isolated :: PerceusM a -> PerceusM (a, Live)
isolated action = do
  live <- getLive
  x <- action
  live' <- getLive
  setLive live
  return (x, live')

isolateWith :: Live -> PerceusM a -> PerceusM (a, Live)
isolateWith live action = isolated $ do
  setLive live
  action

markLive :: Unique -> PerceusM ()
markLive x = modify (\s -> s {ps_live = MS.insert x (ps_live s)})

markLives :: Foldable t => t Unique -> PerceusM ()
markLives = mapM_ markLive

getLive :: PerceusM Live
getLive = gets ps_live

setLive :: Live -> PerceusM ()
setLive live = modify (\s -> s {ps_live = live})

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
  Type.Intrinsic (Name "Bool") -> return False
  Type.Intrinsic (Name "String") -> return True
  -- external types
  Type.Base uniq -> isRefCounted uniq
  _ -> return True
