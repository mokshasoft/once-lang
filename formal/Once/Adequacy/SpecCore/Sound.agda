{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Sound — a compiler core program, as the Spec's,
-- does what the Spec says (plan 0.121 §3.5).
--
-- Over a well-formed Spec signature Σ, a compiler core program over Σ
-- (`Core.Telescope`) IS a Spec program (`programS`, plan 0.122). In a Spec
-- Interpretation `J`, the compiler's run of it (each definition meaning its
-- instance) and the Spec's have the same trace (`core-sound`): the
-- definitions are related (`Program.teleR`), the entry's conversion keeps
-- them related (`conv-entry`), and related runs are bisimilar, so observed
-- alike (`Metatheory.Observe.trace-≈`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature; WellFormed)
import Once.Spec.Observation as Obs

module Once.Adequacy.SpecCore.Sound (Σ : Signature) (wf : WellFormed Σ) (fmt : TargetNum) where

open import Data.List using ([])
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Core.Telescope Σ as TL
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
open import Once.Spec.Sub using (_<:_; sub-void; sub-unit; sub-arr)
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
open import Once.Metatheory.Observe Σ using (trace-≈)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Monad Σ
import Once.Adequacy.SpecCore.Program as PG

open SE using (_≈_; _≈ν_; done≈; node≈)
open _≈ν_
open T∞R

------------------------------------------------------------------------
-- The program
------------------------------------------------------------------------

programS : TL.Program → SP.Program
programS = PG.programS Σ fmt wf

------------------------------------------------------------------------
-- The entry: related definitions, converted, run alike
------------------------------------------------------------------------

-- `main`'s conversion to `Eff Unit Unit`, on related values.
conv-entry : ∀ {A : ST.Type} (p : A <: SP.EffUU) {x y} → ValR (gr (A ST.⟨ SP.noVars ⟩)) x y
           → T∞R (ValR g-unit) (SD.conv SP.noVars p x tt) (SD.conv SP.noVars p y tt)
conv-entry sub-void {()} r
conv-entry (sub-arr {π = π} sub-unit sub-unit g) r = sub-R g g (pr π) pr-eff (fmap-R (pr π) (r tt) (λ _ → tt))
conv-entry (sub-arr {π = π} sub-unit sub-void g) r = sub-R g g (pr π) pr-eff (fmap-R (pr π) (r tt) (λ _ → tt))

entry-R : ∀ {sc : SC.Schema} (e : SP.Entry sc) (v v′ : (τ : ST.TySub (SC.Schema.arity sc) 0) → ST.Respects (SC.Schema.kinds sc) ST.∅ₖ τ
                                                     → SD.⟦ SC.Schema.type sc ST.⟨ τ ⟩ ⟧ᵛ)
        → (∀ τ r → ValR (gr (SC.Schema.type sc ST.⟨ τ ⟩)) (v τ r) (v′ τ r))
        → T∞R (ValR g-unit) (SP.runEntry e v) (SP.runEntry e v′)
entry-R (SP.entry p) v v′ rel = conv-entry p (rel SP.noVars _)

------------------------------------------------------------------------
-- Related runs are bisimilar
------------------------------------------------------------------------

private
  bisim  : ∀ {m m′ : SE.T∞ ⊤} → T∞R (ValR g-unit) m m′ → m ≈ m′
  bisimB : ∀ {t t′} → TR (SumR (ValR g-unit) (T∞R (ValR g-unit))) t t′ → SE.BlockEq _ t t′
  force≈ (bisim r) = bisimB (force∞ r)
  bisimB (ret (left _))  = done≈ refl
  bisimB (ret (right r)) = done≈ (bisim r)
  bisimB (call k)        = node≈ (λ b → bisimB (k b))

------------------------------------------------------------------------
-- The program: the same trace
------------------------------------------------------------------------

core-sound : ∀ (J : Obs.Interp Σ) (P : TL.Program)
           → Obs.trace Σ (Obs.Interp.world J) [] (TL.runCore fmt P (Obs.Interp.model J)) ≈ᵗ⟨ _≡_ ⟩ SP.behaviour fmt (programS P) J
core-sound J (TL.program {sig = S} defs d e) =
  trace-≈ (Obs.Interp.world J) []
    (bisim (entry-R e _ _ (λ τ r → PG.teleR Σ fmt (Obs.Interp.model J) defs d τ r)))
