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
  | TFloat                 -- ^ Floating-point type (double precision)
  | TProduct Type Type     -- ^ Product type: A * B
  | TSum Type Type         -- ^ Sum type: A + B
  | TArrow Type Type       -- ^ Function type: A -> B (pure)
  | TEff Type Type         -- ^ Effectful morphism: Eff A B (see D032)
  | TApp Name [Type]       -- ^ Type constructor application: Maybe A, List Int
  | TFix Type              -- ^ Fixed point type: Fix F (for recursive types)
  deriving (Eq, Show)
