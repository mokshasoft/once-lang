------------------------------------------------------------------------
-- Once.Backend.X86v3.SlotBoundedLemma
--
-- Common slot-bounded proof patterns for IR cases.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.Backend.X86v3.SlotBoundedLemma where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

------------------------------------------------------------------------
-- Slot-bounded lemmas for non-recursive IR cases
--
-- For id, fst, snd, terminal: ir-stack-requirement = 0
-- So slot-bounded needs: next-slot alloc ≤ next-slot alloc + 0
-- Which is: next-slot alloc ≤ next-slot alloc (after +-identityʳ)
------------------------------------------------------------------------

-- Proof that n ≤ n + 0 (used for ir-stack-requirement = 0 cases)
slot-bounded-zero : ∀ (n : ℕ) → n ≤ n + 0
slot-bounded-zero n = subst (n ≤_) (sym (+-identityʳ n)) ≤-refl
