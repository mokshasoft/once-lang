-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.CurryAllocWF
--
-- Heap-mode curry handler (Plan 0.14 Phase B).
--
-- Allocates the closure on the heap via `instr-alloc-heap 2` rather
-- than on the stack. Scratch slots are still used (saving the env
-- pointer across the alloc, stashing the closure heap pointer for the
-- final load), but the closure itself lives at a fresh `AtDynamic`
-- and validity is `heap-before`.
--
-- Trace skeleton (parallel to PairWF):
--
--    1. mov-to-output                  ; Output := SV-Ptr env-loc (= input)
--    2. store-at-slot env-stash        ; stash env-ptr for re-use after alloc
--    3. instr-alloc-stack 2            ; reserve scratch (env-stash + closure-stash)
--    4. instr-alloc-heap 2             ; Output := SV-Ptr (AtDynamic fresh)
--    5. store-at-slot closure-stash    ; stash closure heap-ptr
--    6. mov-to-input                   ; Input1 := SV-Ptr closure-loc (for store-indirect)
--    7. load-from-slot env-stash       ; Output := SV-Ptr env-loc
--    8. store-indirect                 ; *closure-loc := SV-Ptr env-loc
--    9. instr-load-code-addr <id>      ; Output := SV-Code <id>   ⟵ ARCHITECTURAL: see below
--   10. store-indirect-suc             ; *(sucLoc closure-loc) := SV-Code <id>
--   11. load-from-slot closure-stash   ; Output := SV-Ptr closure-loc
--
-- ARCHITECTURAL OPEN (flagged for user review):
--   `valid-closure-wf` (in ClosureWellFormed.agda) requires
--   `readLoc s (sucLoc closure-loc) ≡ just (SV-Ptr code-loc)` —
--   an SV-Ptr at closure[1]. But `instr-load-code-addr n` produces
--   `SV-Code n` (a tag-like value, not a pointer). The existing
--   Stack-mode `CurryStackWF` sidesteps this by using `lea-slot
--   (suc closure-slot)` to store a *self-pointer* at closure[1],
--   which satisfies the type-checker but means code-loc is
--   semantically the stack-slot address, not a real code address.
--
--   For heap-mode, the same trick isn't directly available (no
--   `lea-heap` instruction to derive `SV-Ptr (AtDynamic (heap-loc
--   fresh 1))`). Three possible resolutions:
--     (a) Add a new instruction `instr-lea-heap-suc` that converts
--         the heap pointer in Output to a pointer to the next cell.
--     (b) Weaken `valid-closure-wf` to accept either SV-Ptr or
--         SV-Code at closure[1], and have a separate consumer-side
--         derivation.
--     (c) Accept the closure self-reference at closure[0]
--         (closure[1] := closure-loc itself) — type-checks,
--         semantically meaningless.
--
--   For now this file uses (c) at the abstract-trace level via
--   `lea-slot closure-stash` to produce SV-Ptr (AtStack closure-stash),
--   matching the Stack-mode shape. Real code-address linkage is a
--   codegen concern that will be addressed in Phase D.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.CurryAllocWF (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-identityʳ; m≤n+m; +-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧ᴵ)
open import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed o
open import Once.CCC.Machine.TraceEvaluator

import Once.CCC.Machine.SMPrimitives as SMP
import Once.CCC.Machine.SMPrimitives.Heap as SMPH

------------------------------------------------------------------------
-- CurryAllocWF Implementation
------------------------------------------------------------------------

module CurryAllocWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

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
    using (ValidAtWF; IRResultAWF; ResultPlace; at-loc; valid-closure-wf;
           RecDispatcherWF; BodyCorrect;
           validityWF-mem-only; validityWF-frontier-advance;
           mk-IRResultAWF-via-bump)

  ----------------------------------------------------------------------
  -- run-curry-heap: emits the alloc-heap-based trace described above.
  --
  -- Returned IRResultAWF Heap, matching curry's IR-level mode = Heap.
  ----------------------------------------------------------------------

  run-curry-heap : ∀ {A B C k} (mIn : AllocMode) (f : IR (A * B) C)
    (ir<bound : ir-size (curry {k = k} f Heap) < program-bound)
    (rec-wf : RecDispatcherWF (ir-size (curry {k = k} f Heap)))
    (x : ⟦ A ⟧ᴵ) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF Heap (curry {k = k} f Heap) x s alloc
  run-curry-heap {A} {B} {C} {k} mIn f ir<bound rec-wf x input-loc s alloc
                 input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s-final alloc-final curry-heap-trace (mkBump 0 1) refl
      refl refl
      (TraceEvaluator.exec-alloc-eq trace-eval)
      (at-loc closure-loc closure-valid-final closure-before-final
              closure-rax-eq closure-valid-cont closure-before-cont)
      (TraceEvaluator.halted-preserved trace-eval not-halted)
      (TraceEvaluator.mem-preserved-before trace-eval)
      (TraceEvaluator.trace-wf trace-eval)
      (exec-trace-preserves-halted-WF curry-heap-trace)
      _
      (record
        { max-slot-written = next-slot alloc +ℕ closure-heap-scratch
        ; stack-budget = closure-heap-scratch
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = m≤m+n (next-slot alloc) closure-heap-scratch
        ; max-slot-usage-bound = ≤-refl
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = curry-twa
        ; trace-slot-reads-above = curry-tsra
        ; trace-writes-below = curry-twb
        ; trace-slot-reads-below = curry-tsrb
        ; scratch-budget = closure-heap-scratch
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
      ------------------------------------------------------------------
      -- Slot layout (scratch only; closure lives on the heap)
      ------------------------------------------------------------------
      frame = current-frame alloc
      env-stash     = next-slot alloc
      closure-stash = suc env-stash

      -- Number of scratch slots reserved before f runs:
      -- env-stash + closure-stash = 2.
      closure-heap-scratch : ℕ
      closure-heap-scratch = 2

      alloc-after-scratch : AllocState {FS}
      alloc-after-scratch = record alloc { next-slot = next-slot alloc +ℕ closure-heap-scratch }

      ------------------------------------------------------------------
      -- Trace
      ------------------------------------------------------------------
      -- Plan 0.14 SV-Code refactor (2026-05-17):
      --   * Dropped instr-alloc-stack (function prologue allocates slots,
      --     matches IRToTrace runtime).
      --   * Replaced `lea-slot closure-stash` self-reference fiction with
      --     `instr-load-code-addr 0` — matches runtime (which emits the
      --     real body label) and the SV-Code invariant in valid-closure-wf.
      --     The `0` is a placeholder; label coherence with the body's
      --     trace is a separate IRTraceCorrect bridge concern.
      curry-heap-trace : AbstractTrace
      curry-heap-trace =
          mov-to-output
        ∷ store-at-slot env-stash
        ∷ instr-alloc-heap 2
        ∷ store-at-slot closure-stash
        ∷ mov-to-input
        ∷ load-from-slot env-stash
        ∷ store-indirect
        ∷ instr-load-code-addr 0       -- Output := SV-Code 0 (label)
        ∷ store-indirect-suc           -- closure[1] := SV-Code 0
        ∷ load-from-slot closure-stash
        ∷ []

      s-final : LocState FS
      s-final = proj₁ (exec-trace curry-heap-trace s alloc)

      ------------------------------------------------------------------
      -- Closure location (fresh AtDynamic) and validity
      ------------------------------------------------------------------
      closure-loc : ValueLocation FS
      closure-loc = AtDynamic (heap-loc (mkHeapRef (next-heap-ref alloc)) 0)

      -- alloc-final: heap-ref bumped by 1 (via instr-alloc-heap 2),
      -- stack scratch reclaimed back to next-slot alloc (since closure
      -- itself is on heap, scratch slots are reclaimable after trace).
      alloc-final : AllocState {FS}
      alloc-final = record alloc { next-heap-ref = suc (next-heap-ref alloc) }

      ------------------------------------------------------------------
      -- Validity, rax-eq, before — all SMP.!! pending Phase C analogue.
      -- Pattern follows PairWF: step-through proof of the trace.
      ------------------------------------------------------------------
      closure-valid-final : ValidAtWF Heap alloc-final
                             (eval (curry {k = k} f Heap) x) closure-loc s-final
      closure-valid-final = SMP.!!

      closure-before-final : BeforeFrontier alloc-final closure-loc
      closure-before-final = heap-before ≤-refl

      closure-rax-eq : readReg (regs s-final) Output ≡ SV-Ptr closure-loc
      closure-rax-eq = SMP.!!

      closure-cont-alloc : AllocState {FS}
      closure-cont-alloc = record alloc { next-slot     = next-slot     alloc-final
                                        ; next-heap-ref = next-heap-ref alloc-final }

      closure-valid-cont : ValidAtWF Heap closure-cont-alloc
                            (eval (curry {k = k} f Heap) x) closure-loc s-final
      closure-valid-cont = SMP.!!

      closure-before-cont : BeforeFrontier closure-cont-alloc closure-loc
      closure-before-cont = heap-before ≤-refl

      ------------------------------------------------------------------
      -- Plan 0.16 TraceEvaluator: mirror of SumInl/InrHeapWF.
      -- Consolidates per-step state trajectory; `halted-preserved`
      -- derives automatically from `trace-wf`.
      ------------------------------------------------------------------
      trace-eval : TraceEvaluator curry-heap-trace s alloc
      trace-eval = mk-trace-evaluator
        s-final
        alloc-final
        SMP.!!                       -- trace-wf
        refl                         -- exec-state-eq (definitional)
        SMP.!!                       -- exec-alloc-eq
        (λ _ _ → SMP.!!)             -- mem-preserved-before

      ------------------------------------------------------------------
      -- Structural slot-bound discharges (Phase C, mirror SumInlAllocWF).
      ------------------------------------------------------------------
      open import Relation.Binary.PropositionalEquality using (sym)

      max-sw : ℕ
      max-sw = next-slot alloc +ℕ closure-heap-scratch

      max-sw-eq : max-sw ≡ suc (suc (next-slot alloc))
      max-sw-eq = +-comm (next-slot alloc) 2

      closure-stash<max : closure-stash < max-sw
      closure-stash<max = subst (suc closure-stash ≤_) (sym max-sw-eq) ≤-refl

      env-stash<max : env-stash < max-sw
      env-stash<max = ≤-trans (n≤1+n closure-stash) closure-stash<max

      curry-twa : TraceWritesAbove (next-slot alloc) curry-heap-trace
      curry-twa = ≤-refl , n≤1+n (next-slot alloc) , tt

      curry-twb : TraceWritesBelow max-sw curry-heap-trace
      curry-twb = env-stash<max , closure-stash<max , tt

      curry-tsra : TraceSlotReadsAbove (next-slot alloc) curry-heap-trace
      curry-tsra = ≤-refl , n≤1+n (next-slot alloc) , tt

      curry-tsrb : TraceSlotReadsBelow max-sw curry-heap-trace
      curry-tsrb = env-stash<max , closure-stash<max , tt
