-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.BudgetApex — a machine whose fuelled runs show, at every
-- round budget, what the meaning's budgeted run shows has the meaning's trace
-- (plan 0.119 D5).
--
-- The meaning is a run that need not stop (`T∞`); the backend relates the
-- binary to it one budget at a time (`Once.Denotation.Approx`), and where the
-- budget cuts the run, the machine has taken (all but one of) a step per
-- silent step. `Once.Adequacy.FuelTrace` turns that into weak bisimilarity;
-- this module only lines the two machines up — the binary's, and the trace
-- machine of the meaning (`TraceTr.δ∞`), whose fuelled run IS the budgeted run
-- (`TraceTr.approx-run`). The budget is read one higher to absorb the step.
------------------------------------------------------------------------

module Once.Adequacy.BudgetApex where

open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym; cong)

open import Once.Lang.Trace using (Interp; run)
open import Once.Lang.Iterative using (T∞)
open T∞ using (force)
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
open import Once.Denotation.Approx using (approx)
open import Once.Denotation.TraceTr using (δ∞; trT∞; obsAp; approx-run)
open import Once.Adequacy.MachineTrace using (Step; module Machine)
open import Once.Adequacy.FuelTrace using (module Fuel; module Agree)

budget-apex : ∀ {S : Set} (δ : S → Step S) (c₀ : S) (ι : Interp) {X : Set} (m : T∞ X)
            → (∀ k → Σ[ M ∈ ℕ ] (Fuel.runN δ M c₀ ≡ obsAp (run ι [] (approx k m)))
                               × (proj₂ (obsAp (run ι [] (approx k m))) ≡ nothing → k ≤ suc M))
            → Machine.trace δ c₀ ≈ᵗ⟨ _≡_ ⟩ trT∞ ι [] m
budget-apex δ c₀ ι {X} m fact = Agree.agree-≈ δ (δ∞ ι {X}) ag
  where
    ag : Agree.BudgetAgree δ (δ∞ ι {X}) c₀ ([] , force m)
    ag k with fact (suc k) | approx-run ι (suc k) [] m
    ... | M , eM , cM | n , eN , cN =
      M , n , trans eM (sym eN) , λ c → ≤-pred (cM (trans (sym (cong proj₂ eM)) c))
                                      , ≤-pred′ (cN (trans (sym (cong proj₂ eM)) c))
      where
        ≤-pred′ : ∀ {a b} → suc a ≤ b → a ≤ b
        ≤-pred′ {b = suc b} (s≤s p) = Data.Nat.Properties.m≤n⇒m≤1+n p
