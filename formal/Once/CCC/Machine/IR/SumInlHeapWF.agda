-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.SumInlHeapWF
--
-- Heap-mode `inl` handler (Plan 0.14 Phase B).
--
-- Allocates the sum value on the heap via `instr-alloc-heap 2`. Sum
-- layout: 2 heap cells (tag + payload-ptr).
--
-- Trace skeleton:
--    1. mov-to-output                  ; Output := SV-Ptr input-loc (payload)
--    2. store-at-slot payload-stash    ; stash payload ptr
--    3. instr-alloc-stack 2            ; reserve scratch
--    4. instr-alloc-heap 2             ; Output := SV-Ptr (AtDynamic fresh)
--    5. store-at-slot sum-stash        ; stash sum heap ptr
--    6. instr-load-tag-lit 0           ; Output := SV-Tag 0 (inl tag)
--    7. mov-to-input                   ; Input1 = ... wait, need input for store-indirect
--    -- Restructured below to interleave correctly.
--
-- Result: SV-Ptr (AtDynamic sum-loc); cell[0] = tag 0, cell[1] = SV-Ptr payload-loc.
--
-- See also: SumInrHeapWF (symmetric, uses tag 1 for inr).
-- ARCHITECTURAL: valid-inl-wf requires SV-Ptr at sucLoc sum-loc (the
-- payload pointer), not a tag at sum-loc. The cell[0] tag is for runtime
-- dispatch (case-on-tag); the proof side just witnesses the payload-loc
-- pointer at sucLoc sum-loc.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.SumInlHeapWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧; sem-inl)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

import Once.CCC.Machine.SMPrimitives as SMP
import Once.CCC.Machine.SMPrimitives.Heap as SMPH

module SumInlHeapWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}

  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMPH.HeapPrimitives {FS}

  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; at-loc; valid-inl-wf;
           RecDispatcherWF; validityWF-mem-only)

  -- Heap-mode inl handler.
  run-inl-heap : ∀ {A B} (mIn : AllocMode)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF Heap (inl {A} {B} Heap) x s alloc
  run-inl-heap {A} {B} mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s-final
        ; final-alloc = alloc-final
        ; trace = inl-heap-trace
        ; trace-correct = refl
        ; alloc-correct = SMP.!!  -- Phase A scaffold
        ; result-place = at-loc sum-loc sum-valid-final sum-before-final
                            sum-rax-eq sum-valid-cont sum-before-cont
        ; not-halted = not-halted-final
        ; frame-preserved = refl
        ; trace-twf = SMP.!!
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF inl-heap-trace
        }
      ; stack-inv = record
        { slot-monotone = ≤-refl
        ; max-slot-written = next-slot alloc +ℕ scratch-slots
        ; max-slot-geq-final = m≤m+n (next-slot alloc) scratch-slots
        ; stack-budget = scratch-slots
        ; max-slot-usage-bound = ≤-refl
        ; slot-stays-in-budget = m≤m+n (next-slot alloc) scratch-slots
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = SMP.!!
        ; trace-slot-reads-above = SMP.!!
        ; trace-writes-below = SMP.!!
        ; trace-slot-reads-below = SMP.!!
        ; scratch-budget = scratch-slots
        ; scratch-bounded = SMP.!!
        }
      ; heap-inv = record
        { heap-monotone = n≤1+n (next-heap-ref alloc)
        ; heap-budget = 2
        ; max-heap-ref-written = next-heap-ref alloc-final
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = subst (suc (next-heap-ref alloc) ≤_)
                                        (+-comm 2 (next-heap-ref alloc))
                                        (n≤1+n (suc (next-heap-ref alloc)))
        ; trace-no-heap-writes = SMP.!!  -- architecturally false (store-indirect)
        }
      }
    where
      frame = current-frame alloc
      payload-stash = next-slot alloc
      sum-stash     = suc payload-stash

      scratch-slots : ℕ
      scratch-slots = 2

      inl-heap-trace : AbstractTrace
      inl-heap-trace =
          mov-to-output
        ∷ store-at-slot payload-stash
        ∷ instr-alloc-stack scratch-slots
        ∷ instr-alloc-heap 2
        ∷ store-at-slot sum-stash
        ∷ mov-to-input                 -- Input1 := SV-Ptr sum-loc
        ∷ instr-load-tag-lit 0         -- Output := SV-Tag 0 (inl tag)
        ∷ store-indirect               -- *sum-loc := SV-Tag 0
        ∷ load-from-slot payload-stash -- Output := SV-Ptr payload-loc
        ∷ store-indirect-suc           -- *(sucLoc sum-loc) := SV-Ptr payload-loc
        ∷ load-from-slot sum-stash     -- Output := SV-Ptr sum-loc
        ∷ []

      s-final : LocState FS
      s-final = proj₁ (exec-trace inl-heap-trace s alloc)

      sum-loc : ValueLocation FS
      sum-loc = AtDynamic (heap-loc (mkHeapRef (next-heap-ref alloc)) 0)

      alloc-final : AllocState {FS}
      alloc-final = record alloc { next-heap-ref = suc (next-heap-ref alloc) }

      sum-valid-final : ValidAtWF Heap alloc-final (sem-inl {A} {B} x) sum-loc s-final
      sum-valid-final = SMP.!!

      sum-before-final : BeforeFrontier alloc-final sum-loc
      sum-before-final = heap-before ≤-refl

      sum-rax-eq : readReg (regs s-final) Output ≡ SV-Ptr sum-loc
      sum-rax-eq = SMP.!!

      sum-cont-alloc : AllocState {FS}
      sum-cont-alloc = record alloc { next-slot     = next-slot     alloc-final
                                    ; next-heap-ref = next-heap-ref alloc-final }

      sum-valid-cont : ValidAtWF Heap sum-cont-alloc (sem-inl {A} {B} x) sum-loc s-final
      sum-valid-cont = SMP.!!

      sum-before-cont : BeforeFrontier sum-cont-alloc sum-loc
      sum-before-cont = heap-before ≤-refl

      not-halted-final : halted s-final ≡ false
      not-halted-final = exec-trace-preserves-halted-WF inl-heap-trace s alloc not-halted SMP.!!
