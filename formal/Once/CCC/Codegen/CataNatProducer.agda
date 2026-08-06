-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatProducer — A: produce the descend-ready
-- HeapNatChain from a Nat value's ValidAtWF (Plan 0.36 task #8).
--
-- The investigation showed μ-values are NOT universally Heap (`In-valid
-- -bf` is mode-polymorphic — a μ-value's mode = its layer's mode). So the
-- producer needs a Heap-UNIFORMITY precondition on the cata input,
-- justified by the heap-only pivot (the value is built via `In … Heap`
-- throughout). `AllHeap` is that precondition: a mode-polymorphic
-- recursive predicate over the validity derivation asserting `mB ≡ Heap`
-- at each cons (the inr payload mode). `valid→chain` consumes it — the
-- `mB ≡ Heap` `rewrite` is exactly what lets the cons recursion proceed
-- (the child's validity becomes Heap, so its tag is readable).
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.CataNatProducer (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
-- Plan 0.52 M2: machine values are IRTy values (⟦_⟧ᴵ), renamed to ⟦_⟧ locally —
-- the convention `ClosureWellFormed` uses, since `ValidAtWF` is indexed by IRTy.
open import Once.IR using (IRTy; IRFunctor; _⊕_; Id; μ-type; ⟦_⟧TI; _+_; AllocMode; Heap)
open import Once.Semantics.Machine using (sem-inl; sem-inr) renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.CCC.Machine.Allocation using (AllocState)
open import Once.CCC.Machine.SMCore using (LocState; ValueLocation; SV-Tag; SV-Ptr; module MemOps)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
open import Once.CCC.Codegen.CataNatChain using (module CataNatChain)

module CataNatProducer {FS : FrameSemantics} (program-bound : ℕ) (G : IRFunctor) where
  open MemOps {FS} using (readLoc)
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF; valid-μ-wf; valid-inl-wf; valid-inr-wf)
  open CataNatChain {FS}

  F : IRFunctor
  F = G ⊕ Id

  B₀ : IRTy
  B₀ = ⟦ G ⟧TI (μ-type F)

  -- Heap-uniformity of the value's cons-spine: mode-polymorphic so the
  -- recursion needs no `subst` (the cons child's validity is recursed on
  -- directly at its own mode `mB`, with `mB ≡ Heap` recorded alongside).
  AllHeap      : ∀ {m alloc} {x : ⟦ μ-type F ⟧} {loc s} → ValidAtWF m alloc {μ-type F} x loc s → Set
  AllHeapLayer : ∀ {m alloc} {y : ⟦ B₀ + μ-type F ⟧} {loc s} → ValidAtWF m alloc {B₀ + μ-type F} y loc s → Set
  AllHeap (valid-μ-wf wf x lv) = AllHeapLayer lv
  AllHeapLayer (valid-inl-wf lmm tag pp pb slb pv)            = ⊤
  AllHeapLayer (valid-inr-wf {mB = mB} lmm tag pp pb slb pv) = (mB ≡ Heap) × AllHeap pv

  -- A Heap Nat value's validity + Heap-uniformity produces the
  -- descend-ready chain (depth existential). Recurse on the validity;
  -- base = the inl tag, cons = inr tag + child ptr + recurse on the child
  -- (made Heap by the recorded `mB ≡ Heap`).
  valid→chain      : ∀ {alloc} {x : ⟦ μ-type F ⟧} {loc s} (v : ValidAtWF Heap alloc {μ-type F} x loc s)
                   → AllHeap v → ∃[ n ] HeapNatChain n loc s
  valid→chain-layer : ∀ {alloc} {y : ⟦ B₀ + μ-type F ⟧} {loc s} (lv : ValidAtWF Heap alloc {B₀ + μ-type F} y loc s)
                   → AllHeapLayer lv → ∃[ n ] HeapNatChain n loc s
  valid→chain (valid-μ-wf wf x lv) ah = valid→chain-layer lv ah
  valid→chain-layer (valid-inl-wf lmm tag pp pb slb pv) _ = zero , tag
  valid→chain-layer (valid-inr-wf {payload-loc = cl} lmm tag pp pb slb pv) (eq , ah)
    rewrite eq =
      let (m , child-chain) = valid→chain pv ah
      in suc m , tag , cl , pp , child-chain
