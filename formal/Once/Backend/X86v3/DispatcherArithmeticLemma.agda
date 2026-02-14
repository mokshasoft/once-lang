------------------------------------------------------------------------
-- Once.Backend.X86v3.DispatcherArithmeticLemma
--
-- Arithmetic lemmas for the dispatcher.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.Backend.X86v3.DispatcherArithmeticLemma where

open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-assoc; +-monoˡ-≤; ≤-reflexive; +-suc; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Once.Backend.X86v3.IR using (pair-slots)

------------------------------------------------------------------------
-- Slot-bounded lemmas for compose and pair
------------------------------------------------------------------------

-- Helper for compose: slot-bound chains through two sub-IRs
-- Proves: final ≤ (alloc + req-f) + req-g and (alloc + req-f) + req-g = alloc + (req-f + req-g)
compose-slot-bounded-lemma : ∀ (slot slot₁ slot₂ req-f req-g : ℕ) →
  slot₂ ≤ slot₁ + req-g →
  slot₁ ≤ slot + req-f →
  slot₂ ≤ slot + (req-f + req-g)
compose-slot-bounded-lemma slot slot₁ slot₂ req-f req-g bound-g bound-f =
  ≤-trans (≤-trans bound-g (+-monoˡ-≤ req-g bound-f))
          (≤-reflexive (+-assoc slot req-f req-g))

-- Helper for pair: slot-bound chains through two sub-IRs plus pair allocation
-- Proves: (slot₂ + pair-slots) ≤ slot + ((req-f + req-g) + pair-slots)
pair-slot-bounded-lemma : ∀ (slot slot₁ slot₂ req-f req-g ps : ℕ) →
  slot₂ ≤ slot₁ + req-g →
  slot₁ ≤ slot + req-f →
  slot₂ + ps ≤ slot + ((req-f + req-g) + ps)
pair-slot-bounded-lemma slot slot₁ slot₂ req-f req-g ps bound-g bound-f =
  ≤-trans (+-monoˡ-≤ ps alloc₂-bound) (≤-reflexive step2)
  where
    alloc₂-bound : slot₂ ≤ (slot + req-f) + req-g
    alloc₂-bound = ≤-trans bound-g (+-monoˡ-≤ req-g bound-f)
    step2 : ((slot + req-f) + req-g) + ps ≡ slot + ((req-f + req-g) + ps)
    step2 = trans (cong (_+ ps) (+-assoc slot req-f req-g))
                  (+-assoc slot (req-f + req-g) ps)

------------------------------------------------------------------------
-- Slot size lemmas for BeforeFrontier proofs
--
-- We use pair-slots and closure-slots from IR.agda (both = 2).
--
-- suc n < n + 2  (used for proving sucLoc is before frontier after 2-slot allocation)
-- n + 2 = n + suc (suc 0) = suc (n + suc 0) = suc (suc (n + 0)) = suc (suc n)
-- So suc n < n + 2 is equivalent to suc (suc n) ≤ suc (suc n)
------------------------------------------------------------------------

suc<+2 : ∀ n → suc n < n + pair-slots
suc<+2 n = subst (suc (suc n) ≤_) (sym eq) (s≤s (s≤s ≤-refl))
  where
    -- n + 2 = n + suc (suc zero) = suc (n + suc zero) = suc (suc (n + zero)) = suc (suc n)
    eq : n + pair-slots ≡ suc (suc n)
    eq = trans (+-suc n 1) (cong suc (trans (+-suc n 0) (cong suc (+-identityʳ n))))
