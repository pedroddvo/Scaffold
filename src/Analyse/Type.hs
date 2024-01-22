{-# LANGUAGE PatternSynonyms #-}

module Analyse.Type where

import Analyse.Unique (Unique)
import Analyse.Unique qualified as Unique
import Data.List (intercalate)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Syntax.Name (Name (..))

data Var
  = Exist Unique
  | Named Unique
  deriving (Eq, Ord)

data Type
  = Base Unique
  | Var Var
  | Arrow Type Type
  | App Type [Type]
  | Tuple [Type]
  | Forall Unique Type
  | Borrow Type

instance Show Var where
  show (Exist alpha) = "^" ++ show alpha
  show (Named alpha) = show alpha

instance Show Type where
  show = \case
    Base a -> show a
    Var alpha -> show alpha
    Forall alpha a -> "V" ++ show alpha ++ " . " ++ show a
    App a b -> show a ++ "[" ++ intercalate ", " (map show b) ++ "]"
    Arrow a@Arrow {} b -> "(" ++ show a ++ ") -> " ++ show b
    Arrow a b -> show a ++ " -> " ++ show b
    Tuple as -> "(" ++ intercalate ", " (map show as) ++ ")"
    Borrow t -> "&" ++ show t

pattern Exist' :: Unique -> Type
pattern Exist' uniq = Var (Exist uniq)

pattern Named' :: Unique -> Type
pattern Named' uniq = Var (Named uniq)

pattern Intrinsic :: Name Text -> Type
pattern Intrinsic v = Base (Unique.Builtin v)

freeVars :: Type -> Set Var
freeVars = \case
  Base {} -> Set.empty
  Var alpha -> Set.singleton alpha
  Arrow a b -> Set.union (freeVars a) (freeVars b)
  App a as -> Set.union (freeVars a) $ Set.unions (map freeVars as)
  Tuple as -> Set.unions (map freeVars as)
  Borrow t -> freeVars t
  Forall alpha a -> Set.delete (Named alpha) $ freeVars a

isMonotype :: Type -> Bool
isMonotype = \case
  Forall {} -> False
  Base {} -> True
  Var {} -> True
  Arrow a b -> isMonotype a && isMonotype b
  App a b -> isMonotype a && all isMonotype b
  Tuple as -> all isMonotype as
  Borrow t -> isMonotype t

substitute :: Var -> Type -> Type -> Type
substitute alpha b = \case
  Forall beta a | alpha == Named beta -> Forall beta a
  Forall beta a -> Forall beta (substitute alpha b a)
  Tuple as -> Tuple (map (substitute alpha b) as)
  App a as -> App (substitute alpha b a) (map (substitute alpha b) as)
  Arrow t u -> Arrow (substitute alpha b t) (substitute alpha b u)
  Var beta | alpha == beta -> b
  Borrow a -> Borrow $ substitute alpha b a
  a@Var {} -> a
  a@Base {} -> a

isWellFormed :: Type -> Bool
isWellFormed = \case
  Var (Exist _) -> False
  Var (Named _) -> True
  Base{} -> True
  Borrow a -> isWellFormed a
  Forall _ a -> isWellFormed a
  Tuple as -> all isWellFormed as
  Arrow a b -> isWellFormed a && isWellFormed b
  App a as -> isWellFormed a && all isWellFormed as

int :: Type
int = Intrinsic (Name "Int")

bool :: Type
bool = Intrinsic (Name "Bool")

string :: Type
string = Intrinsic (Name "String")

boxed :: Type
boxed = Intrinsic (Name "sfd_boxed")

unit :: Type
unit = Tuple []

tuple :: [Type] -> Type
tuple [x] = x
tuple xs = Tuple xs

arrow :: [Type] -> Type -> Type
arrow args = Arrow (tuple args)

ctor :: [Type] -> Type -> Type
ctor [] x = x
ctor args x = Arrow (tuple args) x

arrowUnzip :: Type -> ([Unique], [Type], Type)
arrowUnzip (Arrow (Tuple xs) c) = ([], xs, c)
arrowUnzip (Arrow a c) = ([], [a], c)
arrowUnzip (Forall alpha a) = 
  let (u, ts, t) = arrowUnzip a in (alpha : u, ts, t)
arrowUnzip a = ([], [], a)

unarrow :: Type -> ([Unique], [Type])
unarrow (Arrow (Tuple xs) c) = ([], xs ++ [c])
unarrow (Arrow a c) = ([], [a, c])
unarrow (Forall alpha a) = let (u, t) = unarrow a in (alpha : u, t)
unarrow _ = undefined

name :: Type -> Maybe Unique
name = \case
  Base uniq -> Just uniq
  Forall _ a -> name a
  App a _ -> name a
  Borrow a -> name a
  _ -> Nothing

isIntrinsic :: Type -> Bool
isIntrinsic = \case
  Intrinsic _ -> True
  _ -> False

isBoxed :: Type -> Bool
isBoxed = \case
  Intrinsic (Name "Int") -> False
  Intrinsic (Name "Bool") -> False
  Var (Named _) -> True
  _ -> True
