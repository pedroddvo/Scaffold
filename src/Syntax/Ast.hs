{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

module Syntax.Ast where

import Analyse.Unique (Unique)
import Data.Text (Text)
import Syntax.Name (Name)

data Node n a = Node
  { node_kind :: n a,
    node_data :: a
  }
  deriving (Show, Functor, Foldable, Traversable)

data TypeNode v a
  = TSymbol v
  | TArrow (Type v a) (Type v a)
  | TBorrow (Type v a)
  deriving (Show, Functor, Foldable, Traversable)

type Type v = Node (TypeNode v)

data PatternNode v a
  = PSymbol v
  | PCtor v [Pattern v a]
  | PAnno (Pattern v a) (Type v a)
  | PNumeric Text
  | PWildcard
  deriving (Show, Functor, Foldable, Traversable)

type Pattern v = Node (PatternNode v)

data ExprNode v a
  = Symbol v
  | Numeric Text
  | String Text
  | Let (Pattern v a) (Expr v a) (Expr v a)
  | Lam (Pattern v a) (Expr v a)
  | App (Expr v a) [Expr v a]
  | Def v [Pattern v a] (Maybe (Type v a)) (Expr v a) (Expr v a)
  | ExternDef v [Pattern v a] (Type v a) Text (Expr v a)
  | InductiveType v [Ctor v a] (Expr v a)
  | ExternType v Text (Expr v a)
  | Dot (Expr v a) (DotResolved v a)
  | Match (Expr v a) [MatchBranch v a]
  | Unit
  deriving (Show, Functor, Foldable, Traversable)

data Ctor v a = Ctor v [(v, Type v a)]
  deriving (Show, Functor, Foldable, Traversable)

type MatchBranch v a = (Pattern v a, [Expr v a], Expr v a)

type Expr v = Node (ExprNode v)

data DotResolved v a = DotUnresolved (Name Text) | DotResolved (Expr v a)
  deriving (Show, Functor, Foldable, Traversable)

node :: (a -> m z) -> Node n z -> a -> Node m z
node f n a = Node (f a) (node_data n)

node2 :: (a -> b -> m z) -> Node n z -> a -> b -> Node m z
node2 f n a b = Node (f a b) (node_data n)

node3 :: (a -> b -> c -> m z) -> Node n z -> a -> b -> c -> Node m z
node3 f n a b c = Node (f a b c) (node_data n)
