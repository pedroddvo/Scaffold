module Main (main, inferTest) where

import Analyse.Desugar qualified as Desugar
import Analyse.Infer qualified as Infer
import Analyse.Perceus qualified as Perceus
import Analyse.Resolver (resolveExpr)
import Analyse.Resolver qualified as Resolver
import Analyse.TcContext qualified as TcContext
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Core qualified
import Data.Map qualified as Map
import Data.MultiSet qualified as MS
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text.IO qualified as Text
import Debug.Trace (traceShow, traceShowId, traceShowM)
import Emit.C qualified as Emit
import Error (Error (..))
import Span (Span)
import Syntax.Ast qualified as Ast
import Syntax.Parser qualified as Parser
import Text.Megaparsec qualified as M
import Data.Bifunctor (second)
import Control.Monad (forM)

main :: IO ()
main = inferTest "example.sfd"

inferTest :: FilePath -> IO ()
inferTest file =
  Text.readFile file
    >>= \src -> case chain src of
      Left err -> putStrLn err
      Right e -> Text.putStrLn e
  where
    chain src = do
      ast <- parse src
      (resolved, env) <- resolve ast
      (typed, env') <- infer resolved env
      return $ emit (TcContext.tc_vars env') (TcContext.tc_exist_counter env') typed

    parse src = case M.parse Parser.program "" src of
      Left err -> Left $ M.errorBundlePretty err
      Right e -> Right e

    resolve e =
      let (res, env) = Resolver.runResolver (Resolver.resolveExpr Map.empty e)
       in case res of
            Left err -> Left $ show err
            Right e' -> Right (e', env)

    infer e env = case TcContext.runTc (Resolver.rs_module_names env) (Resolver.rs_id_counter env) (synth e) of
      Left TcContext.SubtypeFailure -> undefined
      Left (TcContext.TcError err) -> Left $ show err
      Right t -> Right t

    synth e = do
      e' <- Infer.synth e
      env <- TcContext.getEnv
      return (e', env)

    emit env uid e =
      let ds = Desugar.desugar uid e
          uid' = Desugar.ds_unique_gen ds
          core = Desugar.ds_core ds
          globalDefs =
            S.unions
              [ S.fromList . map fst $ Core.core_defs core,
                S.fromList . map fst $ Core.core_extern_defs core
              ]
          nonRcTypes =
            S.fromList
              . map fst
              . filter (not . Type.isIntrinsic . Core.type_def_extern_type . snd)
              $ Core.core_type_defs core
          (core', uid'') = Perceus.runPerceus nonRcTypes globalDefs uid' core
       in Emit.emit
            core'
            uid''
            env
