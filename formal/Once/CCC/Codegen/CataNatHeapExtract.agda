-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatHeapExtract — project a Heap sum layer's
-- `ValidAtWF` into the cata descend's per-cell tag fact (Plan 0.36 task
-- #8, the per-cell extraction).
--
-- `valid-inr-wf`/`valid-inl-wf` now carry the `SumTag` field (the
-- `ValidAtWF` cascade); in Heap mode it IS `readLoc s loc ≡ just (SV-Tag
-- t)`. These projections pull that out by matching the layer's validity
-- constructor — the only one producing `ValidAtWF Heap {A + B} (sem-in*
-- _)`. Composed with `CataNatHeap.cons-tcond`/`base-tcond`, this turns the
-- input value's heap validity into the descend's tag condition.
--
-- The child pointer + child validity are already projected by
-- `ClosureWellFormed.decompose{Inr,Inl}WF`; this supplies the tag those
-- drop. The remaining step (connecting a Nat value's `valid-μ-wf` layer
-- to one of these `valid-in*-wf`s) is functor-shape-specific.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.CataNatHeapExtract (o : CanonicalName) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Type using (Type; _+_)
open import Once.Semantics.Machine using (⟦_⟧; sem-inl; sem-inr)
open import Once.IR using (AllocMode; Heap)
open import Once.CCC.Machine.Allocation using (AllocState)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Tag; module MemOps)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)

module CataNatHeapExtract {FS : FrameSemantics} (program-bound : ℕ) where
  open MemOps {FS} using (readLoc)
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF; valid-inl-wf; valid-inr-wf)

  -- The inr (cons) tag: `*loc ≡ SV-Tag 1`. Pulled from the `SumTag Heap 1`
  -- field, which in Heap mode unfolds to exactly this read.
  inr-tag : ∀ {A B alloc} {b : ⟦ B ⟧} {loc : ValueLocation FS} {s : LocState FS}
          → ValidAtWF Heap alloc {A + B} (sem-inr b) loc s
          → readLoc s loc ≡ just (SV-Tag 1)
  inr-tag (valid-inr-wf lmm tag pp pb slb pv) = tag

  -- The inl (base) tag: `*loc ≡ SV-Tag 0`.
  inl-tag : ∀ {A B alloc} {a : ⟦ A ⟧} {loc : ValueLocation FS} {s : LocState FS}
          → ValidAtWF Heap alloc {A + B} (sem-inl a) loc s
          → readLoc s loc ≡ just (SV-Tag 0)
  inl-tag (valid-inl-wf lmm tag pp pb slb pv) = tag
