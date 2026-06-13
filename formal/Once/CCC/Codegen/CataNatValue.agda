-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatValue — the VALUE side of `cata-correct` for
-- the strat-nat catamorphism (Plan 0.36 task #8, the `value-realized`
-- field / the recursion-scheme value semantics).
--
-- Where the trace side (CataNatAscend) shows the machine EMITS the fold's
-- events, this module is the VALUE analogue: the machine's final
-- accumulator REALIZES `eval (Cata wf alg) x` (the denotational fold).
--
-- Two pieces, mirroring the trace side:
--   * `nat-fold-cons` — the denotational fold LAW at a cons layer: the
--     fold of `In (inr child)` is `alg` applied to `inr (fold child)`.
--     This is `sem-cata-compute` specialised to `F = G ⊕ Id` (the `inr`
--     summand is the `Id` recursive position). It is the value each ascend
--     iteration must produce (the analogue of one layer's `E k`).
--   * `cata-value-loop` — the value-side fold μ-induction (the analogue of
--     `ascend-loop-runs`): given the base's realization + a per-layer
--     value-step (`vstep` — the machine builds the `inr` node and runs
--     `alg`, realizing the next fold value), the machine realizes the fold
--     over the whole depth-`n` spine. `vstep` abstracts build-layer's
--     node-value + the algebra's `value-realized` IH (the deep per-layer
--     machine value correctness), exactly as the trace side abstracts the
--     algebra run as a hypothesis chain.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Functor; _⊕_; Id; μ-type; ⟦_⟧T)
open import Once.Semantics.Machine
  using (⟦_⟧; sem-In; sem-cata; sem-cata-compute; coerce-functor⁻¹)
open import Once.CCC.IR using (IR; Cata)
open import Once.CCC.Eval using (eval)
open import Once.Functor.Translate using (WellFormedF)

module CataNatValue (G : Functor) where
  F : Functor
  F = G ⊕ Id

  -- The denotational fold law at a cons (`inr`/recursive) layer: folding
  -- `In (inr child)` runs `alg` on `inr (fold child)`. Pure `sem-cata-
  -- compute` + the definitional `sem-fmap (G ⊕ Id) f (inj₂ c) = inj₂ (f c)`
  -- (the `Id` position applies the fold).
  nat-fold-cons : ∀ (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                    (child : ⟦ μ-type F ⟧)
    → eval (Cata wf alg) (sem-In F (inj₂ child))
        ≡ eval alg (coerce-functor⁻¹ F A (inj₂ (eval (Cata wf alg) child)))
  nat-fold-cons wf alg child =
    sem-cata-compute wf (λ fa → eval alg (coerce-functor⁻¹ F _ fa)) (inj₂ child)

  -- A depth-`n` Nat spine over a base value: `n` cons (`inr`) layers.
  nat-spine : ℕ → ⟦ μ-type F ⟧ → ⟦ μ-type F ⟧
  nat-spine zero    base = base
  nat-spine (suc k) base = sem-In F (inj₂ (nat-spine k base))

  -- The value-side fold μ-induction. `Realizes x` = "the machine has a
  -- state representing `eval (Cata wf alg) x`" (the `value-realized` shape,
  -- with the witnessing state existentially packed into `Realizes`). Given
  -- the base's realization and a per-layer value-step, the machine realizes
  -- the fold over the whole depth-`n` spine. The induction simply iterates
  -- `vstep` `n` times — the substance is in `vstep` (build-layer node-value
  -- + the algebra's `value-realized` IH), abstracted here as the trace side
  -- abstracts the per-iteration run.
  cata-value-loop : ∀ (Realizes : ⟦ μ-type F ⟧ → Set)
                      (base : ⟦ μ-type F ⟧)
    → Realizes base
    → (∀ (child : ⟦ μ-type F ⟧) → Realizes child → Realizes (sem-In F (inj₂ child)))
    → ∀ (n : ℕ) → Realizes (nat-spine n base)
  cata-value-loop Realizes base base-real vstep zero    = base-real
  cata-value-loop Realizes base base-real vstep (suc k) =
    vstep (nat-spine k base) (cata-value-loop Realizes base base-real vstep k)
