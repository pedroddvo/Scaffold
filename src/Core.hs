module Core where

import Analyse.Type (Type)
import Analyse.Type qualified as Type
import Analyse.Unique (Unique)
import Data.Bifunctor qualified
import Data.List (foldl', intercalate)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.MultiSet (MultiSet)
import Data.MultiSet qualified as S
import Data.Text (Text)
import Data.Text qualified as Text
import Syntax.Name

data Expr
  = Var Unique
  | Lit Literal
  | App Type Expr [Arg]
  | Lam Unique Expr
  | Let Unique Type Expr Expr
  | Dup Unique Expr
  | Drop Unique Expr
  | Case Expr Type [Alt] Type

data Arg = Arg Type Expr PassKind

data PassKind = PassOwned | PassBorrow

type Guards = [Expr]

data Alt = Alt AltCon Guards Type Expr

data AltCon
  = AltLiteral Literal
  | AltBind Unique
  | AltWildcard

data Literal = LitNumeric Text | LitString Text

data Core = Core
  { core_defs :: [(Unique, Def)],
    core_extern_defs :: [(Unique, ExternDef)],
    core_type_defs :: [(Unique, TypeDef)],
    core_inductive_types :: [(Unique, InductiveType)]
  }

newtype InductiveType = InductiveType
  { inductive_type_ctors :: [(Unique, InductiveTypeCtor)]
  }

newtype InductiveTypeCtor = InductiveTypeCtor
  { inductive_type_ctor_args :: [(Unique, Type)]
  }

data ExternDef = ExternDef
  { extern_def_args :: [(AltCon, Type)],
    extern_def_return_type :: Type,
    extern_def_name :: Text
  }

data Def = Def
  { def_expr_type :: Type,
    def_expr :: Expr,
    def_args :: [(AltCon, Type)]
  }

data TypeDef = TypeDefExtern
  { type_def_extern_name :: Text,
    type_def_extern_type :: Type
  }

instance Show Literal where
  show (LitNumeric n) = Text.unpack n
  show (LitString n) = Text.unpack n

instance Show AltCon where
  show (AltLiteral lit) = show lit
  show (AltBind uniq) = show uniq
  show AltWildcard = "_"

instance Show Alt where
  show (Alt con guards _ e) =
    show con ++ intercalate ", " (map (("if " ++) . show) guards) ++ " => " ++ show e

instance Show Arg where
  show (Arg _ e PassOwned) = show e
  show (Arg _ e PassBorrow) = "&" ++ show e

instance Show Expr where
  show = \case
    Var uniq -> show uniq
    Lit lit -> show lit
    App _ e es -> show e ++ "(" ++ intercalate ", " (map show es) ++ ")"
    Lam uniq e -> "λ" ++ show uniq ++ " -> " ++ show e
    Let bind _ e e' -> "let " ++ show bind ++ " = " ++ show e ++ " in " ++ show e'
    Dup x e -> "dup " ++ show x ++ "; " ++ show e
    Drop x e -> "drop " ++ show x ++ "; " ++ show e
    Case e _ alts _ -> "match " ++ show e ++ " { " ++ intercalate ", " (map show alts) ++ " } "

foldCore :: (a -> Expr -> (Expr, a)) -> a -> Core -> (Core, a)
foldCore f a core = (core', a1)
  where
    (a1, foldDefs) = foldl' (\(_, es) (u, e) -> let (e', a') = f a (def_expr e) in (a', (u, e {def_expr = e'}) : es)) (a, []) (core_defs core)
    core' = core {core_defs = foldDefs}

--
-- freeVars :: Expr -> MultiSet Unique
-- freeVars = \case
--   Var x -> S.singleton x
--   Lit _ -> S.empty
--   App _ e1 e2 -> foldl' S.maxUnion (freeVars e1) (map fvArg e2)
--   Lam x e -> S.delete x (freeVars e)
--   Let x _ e1 e2 -> S.delete x $ S.maxUnion (freeVars e1) (freeVars e2)
--   Dup _ e -> freeVars e
--   Drop _ e -> freeVars e
--   Case e _ alts _ -> foldl' fvAlt (freeVars e) alts
--   where
--     fvArg (Arg e PassOwned) = freeVars e
--     fvArg (Arg (Var x) PassBorrow) = S.empty
--     fvAlt e' (Alt con _ e) = S.maxUnion e' (fvAltCon (freeVars e) con)
--
--     fvAltCon e (AltLiteral _) = e
--     fvAltCon e (AltBind x) = S.delete x e
--     fvAltCon e AltWildcard = e
