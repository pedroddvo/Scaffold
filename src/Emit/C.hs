{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Emit.C where

import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Control.Monad.State (State, evalState, gets, modify)
import Core (Alt (Alt), AltCon (..), Arg (..), Core (..), Def (..), Expr (..), ExternDef (extern_def_args, extern_def_name, extern_def_return_type), Guards, Literal (..), TypeDef (..))
import Data.Bifunctor qualified
import Data.Foldable (Foldable (foldl', foldr'))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.MultiSet qualified as MS
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Debug.Trace (traceShowId, traceShowM, traceShow)
import GHC.List qualified as List
import Syntax.Name (Name)
import Syntax.Name qualified as Name
import Text.Builder
import Text.Builder qualified as Builder

data EmitState = EmitState
  { es_vars :: Map Unique Type,
    es_extern_vars :: Map Unique Text,
    es_placeholder_id :: Unique.Id,
    es_rc :: Map Unique Int
  }

type EmitM = State EmitState

typeOfName :: Unique -> EmitM Type
typeOfName name =
  gets (Map.lookup name . es_vars) >>= \case
    Just t -> return t
    Nothing -> undefined

placeholder :: EmitM Builder
placeholder = do
  modify (\s -> s {es_placeholder_id = es_placeholder_id s + 1})
  i <- gets es_placeholder_id
  return ("_" <> decimal i)

emit :: Core -> Unique.Id -> Map Unique Type -> Text
emit core uid vars = Builder.run (evalState builder emitState)
  where
    builder = do
      let typeDefs = emitTypeDefs
      externDefs <- emitExternDefs
      defs <- emitDefs
      return $
        header
          <> "\n\n"
          <> typeDefs
          <> "\n\n"
          <> externDefs
          <> "\n\n"
          <> defs

    emitState =
      EmitState
        { es_vars = vars,
          es_extern_vars = Map.fromList externVars,
          es_placeholder_id = uid,
          es_rc = Map.fromList $ map (,1) (Map.keys vars)
        }

    header = text "#include <scaffold.h>"

    externVars = map (Data.Bifunctor.second extern_def_name) $ Core.core_extern_defs core

    emitDefs = intercalate "\n\n" <$> mapM emitDef (Core.core_defs core)
    emitExternDefs = intercalate "\n\n" <$> mapM emitExternDef (reverse $ Core.core_extern_defs core)
    emitTypeDefs = intercalate "\n" $ map emitTypeDef (reverse $ Core.core_type_defs core)

emitTypeDef :: (Unique, Core.TypeDef) -> Builder
emitTypeDef (name, def) =
  let def' = text (type_def_extern_name def)
   in "typedef " <> def' <> " " <> emitName name <> ";"

emitExternDef :: (Unique, Core.ExternDef) -> EmitM Builder
emitExternDef (_, def) = do
  defArgs <- mapM emitDefArg (Core.extern_def_args def)
  return $
    "extern "
      <> emitType (Core.extern_def_return_type def)
      <> " "
      <> text (Core.extern_def_name def)
      <> ( "("
             <> intercalate ", " (map snd defArgs)
             <> ");"
         )

emitDef :: (Unique, Core.Def) -> EmitM Builder
emitDef (name, def) = do
  expr <- emitExpr 1 (\e -> "return " <> e <> ";") (Core.def_expr def)
  defArgs <- mapM emitDefArg (Core.def_args def)
  let (stmts, args) = unzip defArgs
  return $
    emitType (Core.def_expr_type def)
      <> " "
      <> emitName name
      <> "("
      <> intercalate ", " args
      <> ") {\n"
      <> intercalate ";\n" (map (indent 1 <>) $ concat stmts)
      <> expr
      <> "\n}"

emitAssertion :: Builder -> Builder
emitAssertion b = "assert(" <> b <> ")"

emitDefArg :: (AltCon, Type) -> EmitM ([Builder], Builder)
emitDefArg (Core.AltBind name', ty) = return ([], emitType ty <> " " <> emitName name')
emitDefArg (Core.AltWildcard, ty) = return ([], emitType ty <> " _")
emitDefArg (Core.AltLiteral lit, ty) = do
  p <- placeholder
  return ([emitAssertion $ p <> "==" <> emitLiteral lit], emitType ty <> " " <> p)

type Indent = Int

indent :: Indent -> Builder
indent i = text $ Text.replicate (i * 4) " "

emitStmts :: Indent -> [Builder] -> Builder
emitStmts i stmts = do
  let endStmts = case stmts of
        [] -> text ""
        _ -> text ";\n"
   in intercalate ";\n" (map (indent i <>) stmts) <> endStmts <> indent i

emitExpr :: Indent -> (Builder -> Builder) -> Core.Expr -> EmitM Builder
emitExpr i' mapEnd expr = do
  (stmts, expr') <- emitExpr' i' expr
  return $ emitStmts i' stmts <> mapEnd expr'
  where
    emitExpr' :: Indent -> Core.Expr -> EmitM ([Builder], Builder)
    emitExpr' i = \case
      Core.Var name -> emitVar name
      Core.Lit lit -> return ([], emitLiteral lit)
      Core.App _ e args -> emitApp i e args
      Core.Let name t e e' -> emitLet i name t e e'
      Core.Case scrutinee scrutineeT alts resultT -> emitCase i scrutinee scrutineeT alts resultT
      Core.Dup x e -> do
        let stmt = "sfd_inc_ref(" <> emitName x <> ")"
        (stmts, e') <- emitExpr' i e
        return (stmt : stmts, e')
      Core.Drop x e -> do
        let stmt = "sfd_dec_ref(" <> emitName x <> ")"
        (stmts, e') <- emitExpr' i e
        return (stmt : stmts, e')
      Core.Lam {} -> undefined

    emitCase :: Indent -> Core.Expr -> Type -> [Core.Alt] -> Type -> EmitM ([Builder], Builder)
    emitCase i scrut scrutT alts resultT = do
      (stmts, scrut') <- emitExpr' i scrut
      resultP <- placeholder
      scrutP <- placeholder
      alts' <- emitCaseAlts i resultP scrutP alts
      let setScrutinee = emitType scrutT <> " " <> scrutP <> " = " <> scrut'
      let setResult = emitType resultT <> " " <> resultP
      return (stmts ++ [setScrutinee, setResult, alts'], resultP)

    emitCaseAlts :: Indent -> Builder -> Builder -> [Core.Alt] -> EmitM Builder
    emitCaseAlts i res scrut [] = return ""
    emitCaseAlts i res scrut ((Core.Alt con guards t e) : rest) = do
      let offs = if List.null guards then 1 else 2
      e' <-
        emitExpr (i + offs) (\e' -> res <> " = " <> e' <> ";\n") e
          >>= emitGuards (i + 1) guards
      case (con, guards) of
        (Core.AltLiteral lit, _) -> do
          rest' <- emitCaseAlts i res scrut rest
          return $
            "if ("
              <> scrut
              <> " == "
              <> emitLiteral lit
              <> ") {\n"
              <> e'
              <> indent i
              <> "}"
              <> (if List.null rest then "" else " else ")
              <> rest'
        (Core.AltBind x, []) -> do
          return $
            "{\n"
              <> indent (i + 1)
              <> emitType t
              <> " "
              <> emitName x
              <> " = "
              <> scrut
              <> ";\n"
              <> e'
              <> indent i
              <> "}"
        (Core.AltBind x, _xs) -> do
          rest' <- emitCaseAlts (i + 1) res scrut rest
          return $
            "{\n"
              <> indent (i + 1)
              <> emitType t
              <> " "
              <> emitName x
              <> " = "
              <> scrut
              <> ";\n"
              <> e'
              <> (if List.null rest then "" else " else ")
              <> rest'
              <> "\n"
              <> indent i
              <> "}"
        (Core.AltWildcard, _) -> return $ "{\n" <> e' <> indent i <> "}"

    emitGuards :: Indent -> Core.Guards -> Builder -> EmitM Builder
    emitGuards _ [] e = return e
    emitGuards i [guard] e = do
      (stmts, guard') <- emitExpr' i guard
      let stmts' = emitStmts i stmts
      return $ stmts' <> "if (" <> guard' <> ") {\n" <> e <> indent i <> "}"
    emitGuards _ _ _ = undefined

    emitVar :: Unique -> EmitM ([Builder], Builder)
    emitVar name =
      gets (Map.lookup name . es_extern_vars) >>= \case
        Nothing -> return ([], emitName name)
        Just cident -> return ([], text cident)

    emitApp :: Indent -> Core.Expr -> [Core.Arg] -> EmitM ([Builder], Builder)
    emitApp i f args = do
      (stmts, f') <- emitExpr' i f
      emittedArgs <- mapM (\(Core.Arg _ e _) -> emitExpr' 0 e) args
      let (stmts', args') = foldl' (\(ss, sa) (s, a) -> (ss ++ s, sa ++ [a])) (stmts, []) emittedArgs
      return (stmts', f' <> "(" <> intercalate ", " args' <> ")")

    emitLet :: Indent -> Unique -> Type -> Expr -> Expr -> EmitM ([Builder], Builder)
    emitLet i bind t e1 e2 = do
      (stmts, e1') <- emitExpr' i e1
      (stmts', e2') <- emitExpr' i e2
      let decl = emitType t <> " " <> emitName bind <> " = " <> e1'
      return (stmts ++ [decl] ++ stmts', e2')

emitLiteral :: Core.Literal -> Builder
emitLiteral = \case
  LitNumeric num -> text num
  LitString str -> "sfd_string_mk(\"" <> text str <> "\")"

emitType :: Type -> Builder
emitType = \case
  Type.Base name -> emitName name
  Type.Borrow e -> emitType e
  t -> traceShow t undefined

emitName :: Unique -> Builder
emitName = \case
  Unique.Builtin name -> emitName' text name
  Unique.Id i Nothing -> "_" <> decimal i
  Unique.Id i (Just name) -> "_" <> emitName' text name <> "_" <> decimal i

emitName' :: (a -> Builder) -> Name a -> Builder
emitName' f n = intercalate "_" (map f $ Name.toList n)

--
-- emitExternName :: Unique -> Builder
-- emitExternName = \case
--   Unique.Builtin name -> text name
--   Unique.Id i Nothing -> "_" <> decimal i
--   Unique.Id _ (Just name) -> emitName''
