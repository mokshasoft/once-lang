-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatSeam — the Nat-shape SEAM: a Nat value's
-- `valid-μ-wf` yields the cata descend's per-cell tag fact (Plan 0.36
-- task #8).
--
-- This is the functor-SHAPE-specific step the general proof builds on.
-- For the concrete Nat functor `NatF = K Unit ⊕ Id`, the μ-layer type
-- `⟦ NatF ⟧T (μ-type NatF)` REDUCES to `Unit + μ-type NatF` — a sum —
-- so peeling `valid-μ-wf` (`peel-μ`) lands a `ValidAtWF` on a sum layer,
-- which `inr-tag`/`inl-tag` (CataNatHeapExtract) then read.
--
-- The seam is the SAME for general strat-nat `F` (the loop machinery and
-- the projections above are functor-agnostic); only this peel — where
-- `⟦F⟧T` is stuck for variable `F` — generalizes (induct on the functor /
-- `WellFormedF`). So Nat here is the first instance, not a rewrite.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatSeam where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Type using (Unit; μ-type; ⟦_⟧T; NatF; _+_)
open import Once.Semantics.Machine using (⟦_⟧; sem-inl; sem-inr)
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR using (out-μ; Heap)
open import Once.Functor.Translate using (WellFormedF; WellFormedF-irrelevant)
open import Once.CCC.Machine.Allocation using (AllocState)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Tag; module MemOps)
open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)
open import Once.CCC.Codegen.CataNatHeapExtract using (module CataNatHeapExtract)

module CataNatSeam {FS : FrameSemantics} (program-bound : ℕ) where
  open MemOps {FS} using (readLoc)
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF; valid-μ-wf)
  open CataNatHeapExtract {FS} program-bound using (inr-tag; inl-tag)

  -- Peel `valid-μ-wf`: the μ-value's validity at `loc` IS its F-layer's
  -- validity at the same `loc`. (= `μ-layer-iso`, specialised to NatF.)
  peel-μ : ∀ {alloc} {x : ⟦ μ-type NatF ⟧} {loc : ValueLocation FS} {s : LocState FS}
             (wf : WellFormedF NatF)
         → ValidAtWF Heap alloc {μ-type NatF} x loc s
         → ValidAtWF Heap alloc {⟦ NatF ⟧T (μ-type NatF)} (eval (out-μ wf) x) loc s
  peel-μ wf (valid-μ-wf wf′ x lv) rewrite WellFormedF-irrelevant wf wf′ = lv

  -- SEAM (cons): a Nat cons value's validity gives the cons tag. `⟦ NatF
  -- ⟧T (μ-type NatF) = Unit + μ-type NatF` (reduces), so the peeled layer
  -- is a sum; `subst` to the cons shape, then `inr-tag`.
  nat-cons-tag : ∀ {alloc} {x : ⟦ μ-type NatF ⟧} {child : ⟦ μ-type NatF ⟧}
                   {loc : ValueLocation FS} {s : LocState FS}
                   (wf : WellFormedF NatF)
               → eval (out-μ wf) x ≡ sem-inr {Unit} {μ-type NatF} child
               → ValidAtWF Heap alloc {μ-type NatF} x loc s
               → readLoc s loc ≡ just (SV-Tag 1)
  nat-cons-tag {alloc} {x = x} {child} {loc} {s} wf cons-shape v =
    inr-tag (subst (λ w → ValidAtWF Heap alloc {Unit + μ-type NatF} w loc s) cons-shape (peel-μ wf v))

  -- SEAM (base): a Nat base value's validity gives the base tag.
  nat-base-tag : ∀ {alloc} {x : ⟦ μ-type NatF ⟧} {u : ⟦ Unit ⟧}
                   {loc : ValueLocation FS} {s : LocState FS}
                   (wf : WellFormedF NatF)
               → eval (out-μ wf) x ≡ sem-inl {Unit} {μ-type NatF} u
               → ValidAtWF Heap alloc {μ-type NatF} x loc s
               → readLoc s loc ≡ just (SV-Tag 0)
  nat-base-tag {alloc} {x = x} {u} {loc} {s} wf base-shape v =
    inl-tag (subst (λ w → ValidAtWF Heap alloc {Unit + μ-type NatF} w loc s) base-shape (peel-μ wf v))
