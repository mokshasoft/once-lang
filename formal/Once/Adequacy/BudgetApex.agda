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
-- silent step. `Once.Adequacy.FuelTrace` turns that into `⊑ᵗ` (D347: the
-- binary may end `exhausted` where the meaning goes on); this module only
-- lines the two machines up — the binary's, and the trace
-- machine of the meaning (`TraceTr.δ∞`), whose fuelled run IS the budgeted run
-- (`TraceTr.approx-run`). The budget is read one higher to absorb the step.
------------------------------------------------------------------------

module Once.Adequacy.BudgetApex where

open import Data.List using ([]; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-pred; ≤-trans)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym; cong)

open import Once.IR.Semantics.Trace using (Interp; run)
open import Once.IR.Semantics.Iterative using (T∞)
open T∞ using (force)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_; exhausted)
open import Once.Denotation.Approx using (approx)
open import Once.Denotation.TraceTr using (δ∞; trT∞; obsAp; approx-run)
open import Once.Adequacy.MachineTrace using (Step; module Machine)
open import Once.Adequacy.FuelTrace using (Obs; module Fuel; module Agree)
open import Once.IR.Semantics.Event using (toEvent)
open import Once.IR.Semantics.Out using (Out)
import Once.IR.Semantics.Out as Out

------------------------------------------------------------------------
-- Up to running out (D347; plan 0.123 A.4): at every round budget the
-- machine's run shows what the meaning's budgeted run shows, or it ENDED
-- `exhausted` after calls the meaning's run makes first. The machine follows
-- the meaning's trace up to running out.
------------------------------------------------------------------------

-- The machine's run ran out after a prefix of the meaning's calls.
RanOutOf : Obs → Obs → Set
RanOutOf o₁ o₂ = proj₂ o₁ ≡ just exhausted × ∃[ rest ] (proj₁ o₁ ++ rest ≡ proj₁ o₂)

BudgetFact⊑ : ∀ {S : Set} (δ : S → Step S) (c₀ : S) (ι : Interp) {X : Set} (m : T∞ X) → Set
BudgetFact⊑ δ c₀ ι m =
  ∀ k → Σ[ M ∈ ℕ ] ((Fuel.runN δ M c₀ ≡ obsAp (run ι [] (approx k m)))
                     ⊎ RanOutOf (Fuel.runN δ M c₀) (obsAp (run ι [] (approx k m))))
                  × (proj₂ (Fuel.runN δ M c₀) ≡ nothing → k ≤ suc M)

budget-apex-⊑ : ∀ {S : Set} (δ : S → Step S) (c₀ : S) (ι : Interp) {X : Set} (m : T∞ X)
              → BudgetFact⊑ δ c₀ ι m
              → Machine.trace δ c₀ ⊑ᵗ⟨ _≡_ ⟩ trT∞ ι [] m
budget-apex-⊑ δ c₀ ι {X} m fact = Agree.agree-⊑ δ (δ∞ ι {X}) ag
  where
    ag : Agree.BudgetSub δ (δ∞ ι {X}) c₀ ([] , force m)
    ag k with fact (suc k) | approx-run ι (suc k) [] m
    ... | M , rel , cM | n , eN , cN =
      M , n , rel′ rel , (λ c → ≤-pred (cM c)) , (λ c → ≤-pred′ (cN (trans (sym (cong proj₂ eN)) c)))
      where
        ≤-pred′ : ∀ {a b} → suc a ≤ b → a ≤ b
        ≤-pred′ {b = suc b} (s≤s p) = Data.Nat.Properties.m≤n⇒m≤1+n p
        rel′ : (Fuel.runN δ M c₀ ≡ obsAp (run ι [] (approx (suc k) m)))
               ⊎ RanOutOf (Fuel.runN δ M c₀) (obsAp (run ι [] (approx (suc k) m)))
             → (Fuel.runN δ M c₀ ≡ Fuel.runN (δ∞ ι {X}) n ([] , force m))
               ⊎ Agree.RanOutAt δ (δ∞ ι {X}) (Fuel.runN δ M c₀) (Fuel.runN (δ∞ ι {X}) n ([] , force m))
        rel′ (inj₁ eM)                = inj₁ (trans eM (sym eN))
        rel′ (inj₂ (ex , rest , req)) = inj₂ (ex , rest , trans req (sym (cong proj₁ eN)))

-- THE FACT AT A BUDGET, from a run that agrees with the flat run or ran out
-- after a prefix of its calls (the engine's `AgreeAt`, spelled out): the
-- machine's fuelled run is the concrete run read as the Spec's calls, and the
-- flat run so read is the meaning's budgeted run. One proof for every arch.
budget-fact-of : ∀ {S : Set} (δ : S → Step S) (c₀ : S) (ι : Interp) {X : Set} (m : T∞ X) (k M c : ℕ)
               → (conc flatO : Out)
               → Fuel.runN δ M c₀ ≡ (map toEvent (proj₁ conc) , proj₂ conc)
               → (map toEvent (proj₁ flatO) , proj₂ flatO) ≡ obsAp (run ι [] (approx k m))
               → (proj₂ (obsAp (run ι [] (approx k m))) ≡ nothing → k ≤ c)
               → ((conc ≡ flatO × c ≤ suc M) ⊎ Out.RanOutOf conc flatO)
               → Σ[ M′ ∈ ℕ ] ((Fuel.runN δ M′ c₀ ≡ obsAp (run ι [] (approx k m)))
                              ⊎ RanOutOf (Fuel.runN δ M′ c₀) (obsAp (run ι [] (approx k m))))
                           × (proj₂ (Fuel.runN δ M′ c₀) ≡ nothing → k ≤ suc M′)
budget-fact-of δ c₀ ι m k M c conc flatO eR eF cut (inj₁ (eq , b)) =
  M , inj₁ E , λ nc → ≤-trans (cut (trans (sym (cong proj₂ E)) nc)) b
  where E = trans eR (trans (cong (λ o → map toEvent (proj₁ o) , proj₂ o) eq) eF)
budget-fact-of δ c₀ ι m k M c conc flatO eR eF cut (inj₂ (ex , rest , req)) =
  M , inj₂ ( trans (cong proj₂ eR) ex
           , map toEvent rest
           , trans (cong (λ o → proj₁ o ++ map toEvent rest) eR)
               (trans (sym (map-++ toEvent (proj₁ conc) rest))
                 (trans (cong (map toEvent) req) (cong proj₁ eF))) )
    , λ nc → absurd (trans (sym nc) (trans (cong proj₂ eR) ex))
  where absurd : ∀ {A : Set} → nothing ≡ just exhausted → A
        absurd ()
