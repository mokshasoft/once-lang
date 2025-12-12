module Once.Type
  ( Type (..)
  , Encoding (..)
  , Name
  ) where

import Data.Text (Text)

-- | Type variable or constructor name
type Name = Text

-- | String encoding (erased at runtime)
data Encoding
  = Utf8    -- ^ UTF-8 (variable width, 1-4 bytes per character)
  | Utf16   -- ^ UTF-16 (variable width, 2 or 4 bytes per character)
  | Ascii   -- ^ ASCII (fixed width, 1 byte per character, 0-127)
  deriving (Eq, Show)

-- | Once type representation
data Type
  = TVar Name              -- ^ Type variable: A, B, etc.
  | TUnit                  -- ^ Unit type (terminal object)
  | TVoid                  -- ^ Void type (initial object)
  | TInt                   -- ^ Integer type
  | TBuffer                -- ^ Buffer type (contiguous bytes)
  | TString Encoding       -- ^ String type with encoding (encoding erased at runtime)
  | TProduct Type Type     -- ^ Product type: A * B
  | TSum Type Type         -- ^ Sum type: A + B
  | TArrow Type Type       -- ^ Function type: A -> B (pure)
  | TEff Type Type         -- ^ Effectful morphism: Eff A B (see D032)
  | TApp Name [Type]       -- ^ Type constructor application: Maybe A, List Int
  | TFix Type              -- ^ Fixed point type: Fix F (for recursive types)
  deriving (Eq, Show)
