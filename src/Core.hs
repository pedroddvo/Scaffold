module Core where

import Analyse.Type (Type)
import Analyse.Unique (Unique)
import Data.List (intercalate)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text

data Expr
  = Var Unique
  | Lit Literal
  | App Expr [Expr]
  | Lam Unique Expr
  | Let Unique Type Expr Expr
  | Dup Unique Expr
  | Drop Unique Expr
  | Case Expr Type [Alt] Type

data Alt = Alt AltCon Expr

data AltCon
  = AltLiteral Literal
  | AltBind Unique
  | AltWildcard

data Literal = LitNumeric Text | LitString Text

data Core = Core
  { core_defs :: [(Unique, Def)],
    core_extern_defs :: [(Unique, ExternDef)],
    core_type_defs :: [(Unique, TypeDef)]
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

newtype TypeDef = TypeDefExtern Text

instance Show Literal where
  show (LitNumeric n) = Text.unpack n
  show (LitString n) = Text.unpack n

instance Show AltCon where
  show (AltLiteral lit) = show lit
  show (AltBind uniq) = show uniq
  show AltWildcard = "_"

instance Show Alt where
  show (Alt con e) = show con ++ " => " ++ show e

instance Show Expr where
  show = \case
    Var uniq -> show uniq
    Lit lit -> show lit
    App e es -> show e ++ "(" ++ intercalate ", " (map show es) ++ ")"
    Lam uniq e -> "λ" ++ show uniq ++ " -> " ++ show e
    Let bind _ e e' -> "let " ++ show bind ++ " = " ++ show e ++ " in " ++ show e'
    Dup x e -> "dup " ++ show x ++ "; " ++ show e
    Drop x e -> "drop " ++ show x ++ "; " ++ show e
    Case e _ alts _ -> "match " ++ show e ++ " { " ++ intercalate ", " (map show alts) ++ " } "
