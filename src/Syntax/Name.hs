module Syntax.Name where

import Data.Text (Text)
import Data.Text qualified as Text

data Name a = Namespace a (Name a) | Name a
  deriving (Eq, Ord)

fromList :: [a] -> Name a
fromList [] = undefined
fromList [n] = Name n
fromList (n : ns) = Namespace n (fromList ns)

toList :: Name a -> [a]
toList (Name a) = [a]
toList (Namespace a as) = a : toList as

toParts :: Name a -> [Name a]
toParts (Name a) = [Name a]
toParts (Namespace a as) = Name a : map (Namespace a) (toParts as)

instance Show a => Show (Name a) where
  show (Name a) = show a
  show (Namespace a as) = show a ++ "." ++ show as

instance Semigroup (Name a) where
  a <> b = case (a, b) of
    (Name x, Name y) -> Namespace x (Name y)
    (Name x, Namespace y ys) -> Namespace x (Namespace y ys)
    (Namespace x xs, y) -> Namespace x (xs <> y)

moduleName :: Name Text -> Text
moduleName = Text.intercalate "." . toList
