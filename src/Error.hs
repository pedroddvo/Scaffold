module Error where

import Data.Text (Text)
import Span (Span)

data Error = Error Span Text
  deriving (Show)