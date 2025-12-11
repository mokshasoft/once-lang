module Once.IR
  ( IR (..)
  ) where

import Data.Text (Text)

import Once.Type (Type, Name)

-- | Intermediate representation: the 12 categorical generators
--
-- Every Once program reduces to compositions of these primitives.
-- They correspond to the structure of a bicartesian closed category:
--
-- - Category: id, compose
-- - Products: fst, snd, pair (terminal object via Terminal)
-- - Coproducts: inl, inr, case (initial object via Initial)
-- - Exponentials: curry, apply
data IR
  -- Category
  = Id Type                    -- ^ id : A -> A
  | Compose IR IR              -- ^ compose g f : A -> C (where f : A -> B, g : B -> C)

  -- Products (corresponds to categorical product)
  | Fst Type Type              -- ^ fst : A * B -> A
  | Snd Type Type              -- ^ snd : A * B -> B
  | Pair IR IR                 -- ^ pair f g : C -> A * B (where f : C -> A, g : C -> B)

  -- Terminal object
  | Terminal Type              -- ^ terminal : A -> Unit

  -- Coproducts (corresponds to categorical coproduct)
  | Inl Type Type              -- ^ inl : A -> A + B
  | Inr Type Type              -- ^ inr : B -> A + B
  | Case IR IR                 -- ^ case f g : A + B -> C (where f : A -> C, g : B -> C)

  -- Initial object
  | Initial Type               -- ^ initial : Void -> A (ex falso quodlibet)

  -- Exponentials (corresponds to categorical exponential/closed structure)
  | Curry IR                   -- ^ curry f : A -> (B -> C) (where f : A * B -> C)
  | Apply Type Type            -- ^ apply : (A -> B) * A -> B

  -- Variables and primitives (for surface syntax elaboration)
  | Var Name                   -- ^ Variable reference
  | Prim Name Type Type        -- ^ Primitive operation: name, input type, output type

  -- Literals
  | StringLit Text             -- ^ String literal (Utf8 encoded)

  -- Recursive types (Fixed points)
  -- These are the isomorphism witnesses for Fix F ≅ F (Fix F)
  | Fold Type                  -- ^ fold : F (Fix F) -> Fix F (constructor)
  | Unfold Type                -- ^ unfold : Fix F -> F (Fix F) (destructor)

  deriving (Eq, Show)
