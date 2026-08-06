-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatDescendComplete — the descend phase, complete
-- on the input VALUE (Plan 0.36 task #8): compose A (the producer
-- valid→chain) with B (the loop discharge descend-chain-runs).
--
-- From a Heap Nat value's `ValidAtWF` (+ the `AllHeap` Heap-uniformity
-- precondition + the entry register invariant + the `DescendCode` loop-
-- code facts), the strat-nat descend loop provably RUNS TO COMPLETION:
-- `valid→chain` reads the cons-spine off the validity into a
-- `HeapNatChain`, which `descend-chain-runs` then descends.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.CataNatDescendComplete (o : CanonicalName) where

open import Once.CCC.Label using (LabelId)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
-- Plan 0.52 M2: machine values are IRTy values (⟦_⟧ᴵ), renamed to ⟦_⟧ locally.
open import Once.IR using (IRFunctor; μ-type)
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.IR using (Heap)
open import Once.CCC.Machine.SMCore
  using (LocState; AllocState; halted; regs; readReg; Input1; Scratch;
         sv-as-loc; SV-Tag; ValueLocation; AbstractTrace)
open import Once.CCC.Machine.Allocation using (next-slot)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
open import Once.CCC.Codegen.CataNatDescendRun using (module CataNatDescendRun)
open import Once.CCC.Codegen.CataNatProducer o using (module CataNatProducer)

module CataNatDescendComplete {FS : FrameSemantics} (program-bound : ℕ) (G : IRFunctor) where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)
  open CataNatDescendRun {FS}
  open CataNatProducer {FS} program-bound G

  -- The descend phase runs to completion on the input value: A ∘ B.
  descend-runs-on-value :
      ∀ (prog : AbstractTrace) (ld-top ld-end ld-inl ld-de : LabelId) (q-top q-de q-inl q-end : ℕ)
        (code : DescendCode prog ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end)
        {alloc : AllocState {FS}} {x : ⟦ μ-type F ⟧}
        {loc : ValueLocation FS} {s : LocState FS}
      → sv-as-loc (readReg (regs s) Input1) ≡ just loc
      → readReg (regs s) Scratch ≡ SV-Tag 1
      → halted s ≡ false
      → (v : ValidAtWF Heap alloc {μ-type F} x loc s) → AllHeap v
      → ∃[ n ] Σ[ final ∈ FlatState ]
          (FlatSteps prog (n * 9 + 9) (mkFlat s alloc q-top) final
           × next-slot (falloc final) ≡ next-slot alloc)
  descend-runs-on-value prog ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end code
                        {alloc = alloc} {loc = loc} {s = s} ptr sc hlt v ah =
    let (n , chain)        = valid→chain v ah
        (final , steps , ns) = descend-chain-runs prog ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end
                                 code n s alloc loc ptr sc hlt chain
    in n , final , steps , ns
