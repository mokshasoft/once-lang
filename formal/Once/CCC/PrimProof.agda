------------------------------------------------------------------------
-- Once.CCC.PrimProof
--
-- Abstract proof obligation for primitives.
--
-- Design: Primitives prove they "preserve CCC state" without knowing
-- what that means internally. The backend provides the interpretation.
------------------------------------------------------------------------

module Once.CCC.PrimProof where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
open import Once.CCC.IR using (AllocMode)
open import Once.CCC.Prim.Contract using (PrimContract; output-mode)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Sem using (⟦_⟧)

------------------------------------------------------------------------
-- Abstract CCC State Preservation
--
-- Backend provides:
--   State : Set                    -- runtime state type
--   PreservesCCC : State → State → Set  -- "didn't mess with CCC"
--
-- Primitives prove PreservesCCC holds without knowing its definition.
------------------------------------------------------------------------

module PrimProofInterface
  {FS : FrameSemantics}
  (State : Set)
  (ValueLoc : Set)
  -- Abstract predicate: "primitive preserved CCC state"
  (PreservesCCC : State → State → Set)
  -- Abstract predicate: "result is valid at location with mode"
  (ResultValid : ∀ {B : Type} → AllocMode → ⟦ B ⟧ → ValueLoc → State → Set)
  -- How to read the result location from state
  (getResultLoc : State → ValueLoc)
  where

  ------------------------------------------------------------------------
  -- PrimProof: What a primitive must prove
  --
  -- Clean interface:
  --   1. CCC state preserved (abstract - primitive doesn't know details)
  --   2. Result is valid at the right location
  ------------------------------------------------------------------------

  record PrimResult {A B : Type} (c : PrimContract A B)
                    (sem : ⟦ A ⟧ → ⟦ B ⟧)
                    (x : ⟦ A ⟧)
                    (s-before : State) : Set where
    field
      s-after : State
      result-loc : ValueLoc

      -- Abstract: "I preserved CCC state"
      preserves : PreservesCCC s-before s-after

      -- Result is valid at the promised location
      result-valid : ResultValid (output-mode c) (sem x) result-loc s-after

      -- Result location is in output register
      result-in-output : getResultLoc s-after ≡ result-loc

  -- A primitive proof provider gives PrimResult for any input
  PrimProofProvider : ∀ {A B : Type} → PrimContract A B → (⟦ A ⟧ → ⟦ B ⟧) → Set
  PrimProofProvider {A} c sem = ∀ (x : ⟦ A ⟧) (s : State) → PrimResult c sem x s
