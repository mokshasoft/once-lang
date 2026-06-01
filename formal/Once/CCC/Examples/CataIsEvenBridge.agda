-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Examples.CataIsEvenBridge
--
-- Plan 0.27 (C3): ties the compiled-loop result back to the OFFICIAL IR
-- semantics of the catamorphism.  `CataIsEvenInduction` proves the x86-64
-- code computes `booltag (evenB n)` for every heap Nat; `NatCata` exercises
-- the denotational `eval (Cata wf-NatF alg-isEven) = sem-cata`.  Here we
-- close the loop: for every n, the model semantics `eval isEven (natⁿ n)`
-- equals the spec `evenB n` (as an Once Bool).  Combined, the heap tag the
-- CPU produces faithfully encodes the Cata semantics — a refinement of the
-- structural spec, exactly the Option-2 story (loop refines fold).
------------------------------------------------------------------------

module Once.CCC.Examples.CataIsEvenBridge where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; not)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Once.CCC.Eval using (eval; ⟦_⟧)
open import Once.Semantics.Core ℕ using (sem-cata-compute)
open import Once.Functor.Translate using (wf-NatF)
open import Once.CCC.Examples.NatCata
  using (Nat; zero#; suc#; isEven; evalAlg)
  renaming (Bool to BoolC; not to notC; true to trueC; false to falseC)
open import Once.CCC.Examples.CataIsEvenInduction using (evenB)

-- the μ-value of the natural number n
natⁿ : ℕ → Nat
natⁿ zero    = zero#
natⁿ (suc n) = suc# (natⁿ n)

-- the Once-level Bool denoted by an Agda Bool
cccBool : Bool → ⟦ BoolC ⟧
cccBool true  = trueC
cccBool false = falseC

-- the categorical `not` (swap injections) flips the cccBool encoding
not-cccBool : ∀ b → eval notC (cccBool b) ≡ cccBool (not b)
not-cccBool true  = refl
not-cccBool false = refl

------------------------------------------------------------------------
-- The IR Cata semantics agrees with the `evenB` spec for every n.
-- (The ∀-n generalisation of NatCata's isEven-0..3.)
------------------------------------------------------------------------
eval-isEven : ∀ n → eval isEven (natⁿ n) ≡ cccBool (evenB n)
eval-isEven zero    = sem-cata-compute wf-NatF evalAlg (inj₁ tt)
eval-isEven (suc n) =
  trans (sem-cata-compute wf-NatF evalAlg (inj₂ (natⁿ n)))
        (trans (cong (eval notC) (eval-isEven n)) (not-cccBool (evenB n)))
