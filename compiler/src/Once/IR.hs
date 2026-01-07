module Once.IR
  ( IR (..)
  , AllocMode (..)
  ) where

import Data.Text (Text)

import Once.Type (Type, Name)
import qualified MAlonzo.Code.Once.Arith.IR as MA
import qualified MAlonzo.Code.Once.Arith.Type as MT

-- | Allocation mode for compound data structures
data AllocMode
  = Stack  -- ^ Stack allocation (doesn't escape)
  | Heap   -- ^ Heap allocation (may escape)
  deriving (Eq, Show)

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
  | Pair IR IR AllocMode       -- ^ pair f g mode : C -> A * B (where f : C -> A, g : C -> B)

  -- Terminal object
  | Terminal Type              -- ^ terminal : A -> Unit

  -- Coproducts (corresponds to categorical coproduct)
  | Inl Type Type AllocMode    -- ^ inl mode : A -> A + B
  | Inr Type Type AllocMode    -- ^ inr mode : B -> A + B
  | Case IR IR                 -- ^ case f g : A + B -> C (where f : A -> C, g : B -> C)

  -- Initial object
  | Initial Type               -- ^ initial : Void -> A (ex falso quodlibet)

  -- Exponentials (corresponds to categorical exponential/closed structure)
  | Curry Name IR AllocMode    -- ^ curry f mode : A -> (B -> C) (with lambda var name for codegen)
  | Apply Type Type            -- ^ apply : (A -> B) * A -> B

  -- Variables and primitives (for surface syntax elaboration)
  | Var Name                   -- ^ Variable reference (function call)
  | LocalVar Name              -- ^ Local variable reference (from let binding)
  | FunRef Name                -- ^ Function reference (pointer to function, not a call)
  | Prim Name Type Type        -- ^ Primitive operation: name, input type, output type

  -- Literals
  | StringLit Text             -- ^ String literal (Utf8 encoded)

  -- Recursive types (Fixed points)
  -- These are the isomorphism witnesses for Fix F ≅ F (Fix F)
  | Fold Type                  -- ^ fold : F (Fix F) -> Fix F (constructor)
  | Unfold Type                -- ^ unfold : Fix F -> F (Fix F) (destructor)

  -- Let binding (for sequencing operations)
  -- Categorically: let x = e1 in e2 ≡ (λx. e2) e1
  -- But at runtime we generate explicit local variables for efficiency
  | Let Name IR IR             -- ^ let x = e1 in e2

  -- Arithmetic expressions (OCP-0001)
  -- Pure arithmetic recognized at elaboration time for efficient register-based codegen
  -- Uses MAlonzo-extracted types from verified Agda proofs
  | Arith MT.T_NumType_6 MA.T_ArithIR_72  -- ^ Arithmetic: result type + expression tree
  -- Note: No Eq/Show due to MAlonzo types containing AgdaAny

  -- Reference counting operations (semantically transparent)
  | Retain Type                -- ^ retain : A -> A (increment refcount if heap-allocated)
  | Release Type               -- ^ release : A -> A (decrement refcount, free if zero)
  | Move Type                  -- ^ move : A -> A (transfer ownership, no refcount change)
