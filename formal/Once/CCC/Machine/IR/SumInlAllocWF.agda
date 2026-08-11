-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.SumInlAllocWF
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
-- See also: SumInrAllocWF (symmetric, uses tag 1 for inr).
-- ARCHITECTURAL: valid-inl-wf requires SV-Ptr at sucLoc sum-loc (the
-- payload pointer), not a tag at sum-loc. The cell[0] tag is for runtime
-- dispatch (case-on-tag); the proof side just witnesses the payload-loc
-- pointer at sucLoc sum-loc.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.SumInlAllocWF (o : CanonicalName) where

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
open import Once.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed o
open import Once.CCC.Machine.TraceEvaluator

import Once.CCC.Machine.SMPrimitives as SMP
import Once.CCC.Machine.SMPrimitives.Heap as SMPH

module SumInlAllocWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}

  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMPH.HeapPrimitives {FS}

  open TraceEvaluatorDef {FS}

  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; at-loc; valid-inl-wf;
           RecDispatcherWF; validityWF-mem-only; mk-IRResultAWF-via-bump)

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
    mk-IRResultAWF-via-bump
      s-final alloc-final inl-heap-trace (mkBump 0 1) refl
      refl refl
      (TraceEvaluator.exec-alloc-eq trace-eval)
      (at-loc sum-loc sum-valid-final sum-before-final
              sum-rax-eq sum-valid-cont sum-before-cont)
      (TraceEvaluator.halted-preserved trace-eval not-halted)
      (TraceEvaluator.mem-preserved-before trace-eval)
      (TraceEvaluator.trace-wf trace-eval)
      (exec-trace-preserves-halted-WF inl-heap-trace)
      _
      (record
        { max-slot-written = next-slot alloc +ℕ scratch-slots
        ; stack-budget = scratch-slots
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = m≤m+n (next-slot alloc) scratch-slots
        ; max-slot-usage-bound = ≤-refl
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = inl-twa
        ; trace-slot-reads-above = inl-tsra
        ; trace-writes-below = inl-twb
        ; trace-slot-reads-below = inl-tsrb
        ; scratch-budget = scratch-slots
        ; scratch-bounded = ≤-refl
        })
      (record
        { heap-budget = 2
        ; max-heap-ref-written = next-heap-ref alloc-final
        ; bump-fits-heap-budget = s≤s z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = subst (suc (next-heap-ref alloc) ≤_)
                                        (+-comm 2 (next-heap-ref alloc))
                                        (n≤1+n (suc (next-heap-ref alloc)))
        })
    where
      frame = current-frame alloc
      payload-stash = next-slot alloc
      sum-stash     = suc payload-stash

      scratch-slots : ℕ
      scratch-slots = 2

      -- Plan 0.14 SV-Code refactor (2026-05-17): dropped instr-alloc-stack
      -- to match IRToTrace runtime. Slot allocation is implicit in the
      -- function prologue (subq $budget*8, %rsp); the abstract trace
      -- doesn't bump next-slot. alloc-final tracks only next-heap-ref.
      inl-heap-trace : AbstractTrace
      inl-heap-trace =
          mov-to-output
        ∷ store-at-slot payload-stash
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

      ------------------------------------------------------------------
      -- Plan 0.16 TraceEvaluator (2026-05-19): consolidates the
      -- per-step state trajectory used by alloc-correct, trace-twf,
      -- mem-preserved-before, and not-halted. Each of these obligations
      -- becomes a projection. The three remaining holes
      -- (trace-wf / exec-alloc-eq / mem-preserved-before) are the
      -- semantic Phase C work; `mk-trace-evaluator` derives
      -- halted-preserved automatically from `trace-wf` via
      -- `exec-trace-preserves-halted-WF`.
      ------------------------------------------------------------------
      trace-eval : TraceEvaluator inl-heap-trace s alloc
      trace-eval = mk-trace-evaluator
        s-final
        alloc-final
        SMP.!!    -- trace-wf : TraceWF s alloc inl-heap-trace
        refl      -- exec-state-eq : proj₁ (exec-trace …) ≡ s-final  (by definition)
        SMP.!!    -- exec-alloc-eq : proj₂ (exec-trace …) ≡ alloc-final
        (λ _ _ → SMP.!!)  -- mem-preserved-before

      ------------------------------------------------------------------
      -- Structural slot-bound discharges (Phase C, 2026-05-17).
      -- inl-heap-trace writes only to payload-stash = next-slot alloc
      -- and sum-stash = suc (next-slot alloc). Reads same two slots.
      -- All other instructions are nothing-writes / nothing-reads at
      -- the slot level. The four trace-{writes,slot-reads}-{above,below}
      -- obligations reduce to per-instruction tuples Agda evaluates
      -- via the with-clauses on instr-{writes,reads}-slot.
      ------------------------------------------------------------------
      open import Relation.Binary.PropositionalEquality using (sym)

      max-sw : ℕ
      max-sw = next-slot alloc +ℕ scratch-slots  -- = next-slot alloc + 2

      -- Bridge `next-slot alloc + 2 ≡ suc (suc (next-slot alloc))` via
      -- +-comm (2 + n reduces because + is left-recursive).
      max-sw-eq : max-sw ≡ suc (suc (next-slot alloc))
      max-sw-eq = +-comm (next-slot alloc) 2

      sum-stash<max : sum-stash < max-sw
      sum-stash<max = subst (suc sum-stash ≤_) (sym max-sw-eq) ≤-refl

      payload-stash<max : payload-stash < max-sw
      payload-stash<max = ≤-trans (n≤1+n sum-stash) sum-stash<max

      inl-twa : TraceWritesAbove (next-slot alloc) inl-heap-trace
      inl-twa = ≤-refl , n≤1+n (next-slot alloc) , tt

      inl-twb : TraceWritesBelow max-sw inl-heap-trace
      inl-twb = payload-stash<max , sum-stash<max , tt

      inl-tsra : TraceSlotReadsAbove (next-slot alloc) inl-heap-trace
      inl-tsra = ≤-refl , n≤1+n (next-slot alloc) , tt

      inl-tsrb : TraceSlotReadsBelow max-sw inl-heap-trace
      inl-tsrb = payload-stash<max , sum-stash<max , tt
