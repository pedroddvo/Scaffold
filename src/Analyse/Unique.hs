module Analyse.Unique where

import Data.Text (Text)
import Data.Text qualified as Text
import Syntax.Name (Name)
import Syntax.Name qualified as Name

type Id = Int

data Unique
  = Id Id (Maybe (Name Text))
  | Builtin (Name Text)

instance Eq Unique where
  (Id a _) == (Id b _) = a == b
  (Builtin a) == (Builtin b) = a == b
  _ == _ = False

instance Ord Unique where
  compare (Id a _) (Id b _) = compare a b
  compare (Builtin a) (Builtin b) = compare a b
  compare _ _ = LT

instance Show Unique where
  show (Id alpha Nothing) = show alpha
  show (Id _ (Just v)) = Text.unpack (Name.moduleName v)
  show (Builtin v) = Text.unpack (Name.moduleName v)
