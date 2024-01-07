module Analyse.Subtype where

import Analyse.TcContext (TcCtxM, TcError (SubtypeFailure, TcError), apply, fresh, getEnv, solve)
import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Control.Monad.Except (MonadError (catchError, throwError))
import Data.Set qualified as Set
import Data.Text qualified as Text
import Debug.Trace (traceShowId, traceShowM)
import Error (Error (..))
import Span (Span)
import Control.Monad (foldM_)

subtype :: Span -> Type -> Type -> TcCtxM ()
subtype sp a b =
  catchError
    (subtype' a b)
    ( \case
        SubtypeFailure -> throwError $ TcError (Error sp $ Text.pack ("type mismatch between " ++ show a ++ " and " ++ show b))
        TcError err -> throwError $ TcError err
    )

subtype' :: Type -> Type -> TcCtxM ()
subtype' a b = case (a, b) of
  (Type.Var (Type.Named alpha), Type.Var (Type.Named beta)) | alpha == beta -> return ()
  (Type.Base alpha, Type.Base beta) | alpha == beta -> return ()
  (Type.Tuple as, Type.Tuple bs) -> foldM_ (\() (a', b') -> subtype' a' b') () (zip as bs)
  (Type.Arrow a1 a2, Type.Arrow b1 b2) -> do
    subtype' b1 a1
    env <- getEnv
    subtype' (apply env a2) (apply env b2)
  (Type.Var alpha@(Type.Exist alphaE), _)
    | not $ Set.member alpha (Type.freeVars b) ->
        instantiateL alphaE b
  (_, Type.Var alpha@(Type.Exist alphaE))
    | not $ Set.member alpha (Type.freeVars a) ->
        instantiateR a alphaE
  (_, _) -> throwError SubtypeFailure

instantiateL :: Unique -> Type -> TcCtxM ()
instantiateL alphaE a =
  if Type.isMonotype a
    then solve alphaE a
    else case a of
      Type.Exist' betaE ->
        if betaE > alphaE
          then solve betaE (Type.Exist' alphaE)
          else solve alphaE (Type.Exist' betaE)
      Type.Arrow a1 a2 -> do
        alpha2 <- fresh
        alpha1 <- fresh
        solve alphaE (Type.Arrow (Type.Exist' alpha1) (Type.Exist' alpha2))
        instantiateR a1 alpha1
        env <- getEnv
        instantiateL alpha2 (apply env a2)
      Type.Tuple as -> do
        alphas <- mapM (const fresh) as
        solve alphaE (Type.Tuple $ map Type.Exist' alphas)
        mapM_ (uncurry instantiateL) (zip alphas as)
      _ -> undefined

instantiateR :: Type -> Unique -> TcCtxM ()
instantiateR a alphaE =
  if Type.isMonotype a
    then solve alphaE a
    else case a of
      Type.Exist' betaE ->
        if betaE > alphaE
          then solve betaE (Type.Exist' alphaE)
          else solve alphaE (Type.Exist' betaE)
      Type.Arrow a1 a2 -> do
        alpha2 <- fresh
        alpha1 <- fresh
        solve alphaE (Type.Arrow (Type.Exist' alpha1) (Type.Exist' alpha2))
        instantiateL alpha1 a1
        env <- getEnv
        instantiateR (apply env a2) alpha2
      Type.Tuple as -> do
        alphas <- mapM (const fresh) as
        solve alphaE (Type.Tuple $ map Type.Exist' alphas)
        mapM_ (uncurry instantiateR) (zip as alphas)
      _ -> undefined

applyType :: Span -> Type -> Type -> TcCtxM Type
applyType sp f b = case f of
  Type.Arrow a@(Type.Tuple []) c -> do
    subtype sp a b
    return c
  Type.Arrow (Type.Tuple (a:as)) c -> do
    subtype sp a b
    return $ Type.arrow as c
  Type.Arrow a c -> do
    subtype sp a b
    return c
  _ -> throwError $ TcError (Error sp $ Text.pack ("cannot call type " ++ show f))
