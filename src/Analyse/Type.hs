{-# LANGUAGE PatternSynonyms #-}
module Analyse.Type where
import Analyse.Unique (Unique)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Analyse.Unique as Unique
import Data.List (intercalate)
import Syntax.Name (Name(..))

data Var
  = Exist Unique
  | Named Unique
  deriving (Eq, Ord)

data Type
  = Base Unique
  | Var Var
  | Arrow Type Type
  | Tuple [Type]
  | Borrow Type

instance Show Var where
  show (Exist alpha) = "^" ++ show alpha
  show (Named alpha) = show alpha

instance Show Type where
  show = \case
    Base a -> show a
    Var alpha -> show alpha
    Arrow a@Arrow{} b -> "(" ++ show a ++ ") -> " ++ show b
    Arrow a b -> show a ++ " -> " ++ show b
    Tuple as -> "(" ++ intercalate ", " (map show as) ++ ")"
    Borrow t -> "&" ++ show t

pattern Exist' :: Unique -> Type
pattern Exist' uniq = Var (Exist uniq)

pattern Intrinsic :: Name Text -> Type
pattern Intrinsic v = Base (Unique.Builtin v)

freeVars :: Type -> Set Var
freeVars = \case
  Base {} -> Set.empty
  Var alpha -> Set.singleton alpha
  Arrow a b -> Set.union (freeVars a) (freeVars b)
  Tuple as -> Set.unions (map freeVars as)
  Borrow t -> freeVars t

isMonotype :: Type -> Bool
isMonotype = \case
  Base {} -> True
  Var {} -> True
  Arrow a b -> isMonotype a && isMonotype b
  Tuple as -> all isMonotype as
  Borrow t -> isMonotype t

int :: Type
int = Intrinsic (Name "Int")

string :: Type
string = Intrinsic (Name "String")

unit :: Type
unit = Tuple []

tuple :: [Type] -> Type
tuple [x] = x
tuple xs = Tuple xs

arrow :: [Type] -> Type -> Type
arrow args = Arrow (tuple args)

unarrow :: Type -> [Type]
unarrow (Arrow (Tuple xs) c) = xs ++ [c]
unarrow (Arrow a c) = [a, c]
unarrow _ = undefined

name :: Type -> Maybe Unique
name = \case
  Base uniq -> Just uniq
  _ -> Nothing
