module Once.Type
  ( Type (..)
  , Name
  ) where

import Data.Text (Text)

-- | Type variable or constructor name
type Name = Text

-- | Once type representation
data Type
  = TVar Name              -- ^ Type variable: A, B, etc.
  | TUnit                  -- ^ Unit type (terminal object)
  | TVoid                  -- ^ Void type (initial object)
  | TInt                   -- ^ Integer type
  | TProduct Type Type     -- ^ Product type: A * B
  | TSum Type Type         -- ^ Sum type: A + B
  | TArrow Type Type       -- ^ Function type: A -> B
  deriving (Eq, Show)
