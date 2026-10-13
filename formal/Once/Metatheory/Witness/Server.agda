-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Witness.Server — an effectful stream is typed, and its
-- first layer performs an event (`Spec.Metatheory.Totality`, D311).
--
-- The stream is `Spec.Totality.ticker`, `unfold tick 0`; its coalgebra is the
-- interpretation's effectful `tick`, so forcing a layer CALLS it. Built at
-- `pure` (a stream is a lazy value) and forced at `eff`.
------------------------------------------------------------------------

module Once.Metatheory.Witness.Server where

open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (∃-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Type.Grade using (pure; eff)
open import Once.Spec.Type using (ν-type; Id)
open import Once.Spec.Type.WellFormed using (con-fun; base-Int; wf-Id; rf-Int; rf-⇒)
open import Once.Spec.Type.Sub using (⊑-pe)
open import Once.Spec.Context using (∅; [])
open import Once.Spec.Totality using (tickDefs; tick; ticker)
open import Once.Spec.Core.Typing tickDefs
open import Once.Spec.Core.Meaning tickDefs
open import Once.Spec.Trace using (call)
open import Once.Denotation.GradedDomain using (_>>=ᵖ_)

stream-typed : ∅ ⊢[ [] ] ticker ∷ ν-type Id eff ! pure
stream-typed = ⊢unfold wf-Id (⊢sigop tick (con-fun base-Int base-Int) tt (rf-⇒ rf-Int rf-Int) (here refl)) ⊢lit-int

-- The pure bind is opaque (it keeps checking fast elsewhere); the witness
-- computes through it.
opaque
  unfolding _>>=ᵖ_
  stream-emits : ∀ fmt (ds : DefSem)
               → ∃[ o ] ∃[ a ] ∃[ k ] ⟦ ⊢out wf-Id (⊢sub-eff ⊑-pe stream-typed) ⟧ fmt ds tt ≡ call o a k
  stream-emits fmt ds = _ , _ , _ , refl
