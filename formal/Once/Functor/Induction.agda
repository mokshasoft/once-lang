-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Functor.Induction — a structural induction principle for the
-- strictly-positive initial algebra `μS F`.
--
-- `μS F` is a plain inductive type (`⟨_⟩ : ⟦ F ⟧SF (μS F) → μS F`), but
-- to reason about it we need to lift a predicate over the polynomial
-- functor's *recursive positions* and recurse there. `All-SF F P z`
-- says `P` holds at every `SId` (recursive) position of one functor
-- layer `z`; `μS-ind` is the resulting induction principle.
--
-- This is the missing tool (Plan 0.36, Phase 3): no `All`/`□` lifting
-- nor general `sem-cata` fusion is exposed by `Once.Semantics.Functor`
-- (only natural-transformation fusion `fuseNatS`). With `μS-ind`,
-- properties of `sem-cata`/`cataS` folds (e.g. "a SigOp-free cata emits
-- no events", and the cata trace-correspondence) become provable by
-- induction on the folded value.
------------------------------------------------------------------------

module Once.Functor.Induction where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)

open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩)

------------------------------------------------------------------------
-- Predicate lifting over one polynomial-functor layer.
--
-- `All-SF F P z` : `P` holds at every recursive (`SId`) position of `z`.
-- Constants (`SK`) carry no recursive positions, so the obligation is
-- trivial there.
------------------------------------------------------------------------

All-SF : ∀ F {X} → (X → Set) → ⟦ F ⟧SF X → Set
All-SF (SK A)   P x        = ⊤
All-SF SId      P x        = P x
All-SF (F S⊕ G) P (inj₁ x) = All-SF F P x
All-SF (F S⊕ G) P (inj₂ y) = All-SF G P y
All-SF (F S⊗ G) P (x , y)  = All-SF F P x × All-SF G P y

------------------------------------------------------------------------
-- Structural induction on `μS F`.
--
-- To prove `P` for every `x : μS F`, it suffices to prove `P ⟨ y ⟩`
-- from the inductive hypotheses `All-SF F P y` (i.e. `P` at each
-- recursive child of the layer `y`).
------------------------------------------------------------------------

μS-ind : ∀ {F} (P : μS F → Set)
       → (∀ (y : ⟦ F ⟧SF (μS F)) → All-SF F P y → P ⟨ y ⟩)
       → ∀ x → P x
μS-ind {F} P step ⟨ y ⟩ = step y (gather F y)
  where
    -- Walk the functor structure, discharging each recursive position
    -- by the (structurally smaller) recursive call to `μS-ind`.
    gather : ∀ G (z : ⟦ G ⟧SF (μS F)) → All-SF G P z
    gather (SK A)   z        = tt
    gather SId      z        = μS-ind P step z
    gather (G S⊕ H) (inj₁ z) = gather G z
    gather (G S⊕ H) (inj₂ z) = gather H z
    gather (G S⊗ H) (z , w)  = gather G z , gather H w
