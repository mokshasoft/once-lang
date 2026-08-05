-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatSeam — the Nat-shape SEAM: a Nat value's
-- `valid-μ-wf` yields the cata descend's per-cell tag fact (Plan 0.36
-- task #8).
--
-- This is the functor-SHAPE-specific step the general proof builds on.
-- For the concrete Nat functor `F = K Unit ⊕ Id`, the μ-layer type
-- `⟦ F ⟧T (μ-type F)` REDUCES to `Unit + μ-type F` — a sum —
-- so peeling `valid-μ-wf` (`peel-μ`) lands a `ValidAtWF` on a sum layer,
-- which `inr-tag`/`inl-tag` (CataNatHeapExtract) then read.
--
-- The seam is the SAME for general strat-nat `F` (the loop machinery and
-- the projections above are functor-agnostic); only this peel — where
-- `⟦F⟧T` is stuck for variable `F` — generalizes (induct on the functor /
-- `WellFormedF`). So Nat here is the first instance, not a rewrite.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.CataNatSeam (o : CanonicalName) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Type using (Type; Functor; _⊕_; Id; μ-type; ⟦_⟧T; _+_)
open import Once.Semantics.Machine using (⟦_⟧; sem-inl; sem-inr)
open import Once.CCC.Eval using (eval)
open import Once.IR using (out-μ; Heap)
open import Once.Functor.Translate using (WellFormedF; WellFormedF-irrelevant)
open import Once.CCC.Machine.Allocation using (AllocState)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Tag; SV-Ptr; sucLoc; module MemOps)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
open import Once.CCC.Codegen.CataNatHeapExtract o using (module CataNatHeapExtract)

-- Generalised to any strat-nat functor `F = G ⊕ Id` (binary sum, base
-- branch `G` with no Id, bare Id cons). Nat is the instance `G = K Unit`.
-- `⟦ G ⊕ Id ⟧T (μ F) = ⟦G⟧T(μ F) + μ F` still reduces (top-level ⊕), so
-- the whole seam transfers with the inl-branch type `Unit` replaced by the
-- base layer `⟦G⟧T(μ F)`. This is the functor generalisation of `peel-μ`.
module CataNatSeam {FS : FrameSemantics} (program-bound : ℕ) (G : Functor) where
  open MemOps {FS} using (readLoc)

  -- the strat-nat functor and its base layer.
  F : Functor
  F = G ⊕ Id

  B₀ : Type
  B₀ = ⟦ G ⟧T (μ-type F)
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF; valid-μ-wf; valid-inr-wf)
  open CataNatHeapExtract {FS} program-bound using (inr-tag; inl-tag)

  -- Peel `valid-μ-wf`: the μ-value's validity at `loc` IS its F-layer's
  -- validity at the same `loc`. (= `μ-layer-iso`, specialised to F.)
  peel-μ : ∀ {alloc} {x : ⟦ μ-type F ⟧} {loc : ValueLocation FS} {s : LocState FS}
             (wf : WellFormedF F)
         → ValidAtWF Heap alloc {μ-type F} x loc s
         → ValidAtWF Heap alloc {⟦ F ⟧T (μ-type F)} (eval (out-μ wf) x) loc s
  peel-μ wf (valid-μ-wf wf′ x lv) rewrite WellFormedF-irrelevant wf wf′ = lv

  -- SEAM (cons): a Nat cons value's validity gives the cons tag. `⟦ F
  -- ⟧T (μ-type F) = Unit + μ-type F` (reduces), so the peeled layer
  -- is a sum; `subst` to the cons shape, then `inr-tag`.
  nat-cons-tag : ∀ {alloc} {x : ⟦ μ-type F ⟧} {child : ⟦ μ-type F ⟧}
                   {loc : ValueLocation FS} {s : LocState FS}
                   (wf : WellFormedF F)
               → eval (out-μ wf) x ≡ sem-inr {B₀} {μ-type F} child
               → ValidAtWF Heap alloc {μ-type F} x loc s
               → readLoc s loc ≡ just (SV-Tag 1)
  nat-cons-tag {alloc} {x = x} {child} {loc} {s} wf cons-shape v =
    inr-tag (subst (λ w → ValidAtWF Heap alloc {B₀ + μ-type F} w loc s) cons-shape (peel-μ wf v))

  -- SEAM (base): a Nat base value's validity gives the base tag.
  nat-base-tag : ∀ {alloc} {x : ⟦ μ-type F ⟧} {u : ⟦ B₀ ⟧}
                   {loc : ValueLocation FS} {s : LocState FS}
                   (wf : WellFormedF F)
               → eval (out-μ wf) x ≡ sem-inl {B₀} {μ-type F} u
               → ValidAtWF Heap alloc {μ-type F} x loc s
               → readLoc s loc ≡ just (SV-Tag 0)
  nat-base-tag {alloc} {x = x} {u} {loc} {s} wf base-shape v =
    inl-tag (subst (λ w → ValidAtWF Heap alloc {B₀ + μ-type F} w loc s) base-shape (peel-μ wf v))

  -- SEAM (child pointer): a Nat cons value's validity gives the child
  -- pointer at `sucLoc loc` (the descend's `child` step fact). Same peel,
  -- then match `valid-inr-wf` and project its payload-pointer field.
  nat-cons-child : ∀ {alloc} {x : ⟦ μ-type F ⟧} {child : ⟦ μ-type F ⟧}
                     {loc : ValueLocation FS} {s : LocState FS}
                     (wf : WellFormedF F)
                 → eval (out-μ wf) x ≡ sem-inr {B₀} {μ-type F} child
                 → ValidAtWF Heap alloc {μ-type F} x loc s
                 → ∃[ child-loc ] (readLoc s (sucLoc loc) ≡ just (SV-Ptr child-loc))
  nat-cons-child {alloc} {x = x} {child} {loc} {s} wf cons-shape v
    with subst (λ w → ValidAtWF Heap alloc {B₀ + μ-type F} w loc s) cons-shape (peel-μ wf v)
  ... | valid-inr-wf {payload-loc = cl} lmm tag cp pb slb cv = cl , cp
