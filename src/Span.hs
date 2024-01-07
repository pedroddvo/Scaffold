module Span (Span (..)) where

data Span
  = Span
      {-# UNPACK #-} !Int
      {-# UNPACK #-} !Int

instance Show Span where
  show (Span start end) = show start ++ ".." ++ show end

instance Semigroup Span where
  (Span a1 a2) <> (Span b1 b2) = Span (min a1 b1) (max a2 b2)