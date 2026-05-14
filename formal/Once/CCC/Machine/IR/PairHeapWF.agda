-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairHeapWF
--
-- Heap-mode pair handler (Plan 0.14 Phase B).
--
-- Allocates the pair on the heap via `instr-alloc-heap 2` rather than
-- on the stack. Stack slots are still used as *scratch* (saving the
-- input pointer across sub-IR calls, stashing intermediate results
-- before stitching them into the heap block), but the pair itself lives
-- at a fresh `AtDynamic` and validity is `heap-before`, not
-- `stack-before`.
--
-- Trace skeleton (no inter-IR stack-frontier dependence):
--
--    1. mov-to-output                  ; Output := SV-Ptr input-loc
--    2. store-at-slot backup-slot      ; stash input-loc for re-use after f
--    3. f-trace                        ; Output := SV-Ptr fst-loc
--    4. store-at-slot fst-stash        ; stash fst-loc
--    5. restore-input backup-slot      ; Input1 := SV-Ptr input-loc again
--    6. g-trace                        ; Output := SV-Ptr snd-loc
--    7. store-at-slot snd-stash        ; stash snd-loc
--    8. instr-alloc-heap 2             ; Output := SV-Ptr (AtDynamic fresh)
--    9. store-at-slot pair-stash       ; stash pair-loc
--   10. mov-to-input                   ; Input1 := SV-Ptr pair-loc
--   11. load-from-slot fst-stash       ; Output := SV-Ptr fst-loc
--   12. store-indirect                 ; *pair-loc := SV-Ptr fst-loc
--   13. load-from-slot snd-stash       ; Output := SV-Ptr snd-loc
--   14. store-indirect-suc             ; *(sucLoc pair-loc) := SV-Ptr snd-loc
--   15. load-from-slot pair-stash      ; Output := SV-Ptr pair-loc
--
-- The result-place is `at-loc pair-loc …` where `pair-loc` is the
-- fresh `AtDynamic`. `BeforeFrontier` for pair-loc is `heap-before`,
-- which holds trivially after `instr-alloc-heap` bumps next-heap-ref.
--
-- This file is intentionally scaffolded with `SMP.!!` placeholders
-- for the heaviest proof obligations. The structure is in place so
-- downstream consumers (Dispatcher, IRResultAWF construction) can rely
-- on the function's type; each `!!` will be discharged in its own
-- focused commit. See `[[scaffold_then_discharge]]`.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairHeapWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-identityʳ; m≤n+m)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧; sem-pair)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

import Once.CCC.Machine.SMPrimitives as SMP
import Once.CCC.Machine.SMPrimitives.Heap as SMPH

------------------------------------------------------------------------
-- PairHeapWF Implementation
------------------------------------------------------------------------

module PairHeapWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
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
    using (ValidAtWF; IRResultAWF; ResultPlace; at-loc; valid-pair-wf;
           RecDispatcherWF;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-frontier-advance)

  ----------------------------------------------------------------------
  -- run-pair-heap: emits the alloc-heap-based trace described above.
  ----------------------------------------------------------------------

  run-pair-heap : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR A C)
    (rec-wf : RecDispatcherWF (ir-size (⟨ f , g ⟩ Heap)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF Heap (⟨ f , g ⟩ Heap) x s alloc
  run-pair-heap {A} {B} {C} mIn f g rec-wf x input-loc s alloc
                input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s-final
        ; final-alloc = alloc-final
        ; trace = pair-heap-trace
        ; trace-correct = refl
        ; result-place = at-loc pair-loc pair-valid-final pair-before-final
                            pair-rax-eq pair-valid-cont pair-before-cont
        ; not-halted = not-halted-final
        ; frame-preserved = exec-trace-preserves-frame pair-heap-trace s alloc
        ; trace-twf = SMP.!!
        ; mem-preserved-before = λ _ _ → SMP.!!  -- TODO: heap-aware mem-preserved
        ; trace-preserves-halted = exec-trace-preserves-halted-WF pair-heap-trace
        }
      ; stack-inv = record
        { slot-monotone = SMP.!!
        ; max-slot-written = max-slot-pair
        ; max-slot-geq-final = SMP.!!
        ; stack-budget = req-pair-stack
        ; max-slot-usage-bound = SMP.!!
        ; slot-stays-in-budget = SMP.!!
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = SMP.!!
        ; trace-slot-reads-above = SMP.!!
        ; trace-writes-below = SMP.!!
        ; trace-slot-reads-below = SMP.!!
        ; scratch-budget = req-pair-scratch
        ; scratch-bounded = SMP.!!
        }
      ; heap-inv = record
        { heap-monotone = heap-mono
        ; heap-budget = req-pair-heap
        ; max-heap-ref-written = next-heap-ref alloc-final
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = SMP.!!
        ; trace-no-heap-writes = SMP.!!
        }
      }
    where
      ------------------------------------------------------------------
      -- Slot layout (scratch only; pair itself is on the heap)
      ------------------------------------------------------------------
      frame = current-frame alloc
      backup-slot = next-slot alloc
      fst-stash   = suc backup-slot
      snd-stash   = suc fst-stash
      pair-stash  = suc snd-stash
      f-start     = suc pair-stash    -- = next-slot alloc + 4

      alloc-after-scratch : AllocState {FS}
      alloc-after-scratch = record alloc { next-slot = f-start }

      ------------------------------------------------------------------
      -- Run f at the post-scratch state.
      -- For scaffolding, we run f directly on (s, alloc-after-scratch)
      -- — discharging the setup-trace transport is part of the followup
      -- pass.
      ------------------------------------------------------------------
      input-before-at-f-start : BeforeFrontier alloc-after-scratch input-loc
      input-before-at-f-start = frontier-monotone alloc alloc-after-scratch refl
                                  (≤-trans (n≤1+n backup-slot)
                                    (≤-trans (n≤1+n fst-stash)
                                      (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash))))
                                  ≤-refl input-loc input-before

      input-valid-wf-at-f-start : ValidAtWF mIn alloc-after-scratch x input-loc s
      input-valid-wf-at-f-start = validityWF-frontier-advance x input-loc s refl
                                    (≤-trans (n≤1+n backup-slot)
                                      (≤-trans (n≤1+n fst-stash)
                                        (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash))))
                                    ≤-refl input-valid-wf

      f-exec : ∃[ mF ] IRResultAWF mF f x s alloc-after-scratch
      f-exec = rec-wf mIn f (⟨,⟩-f-smaller f g {Heap}) x input-loc s alloc-after-scratch
                 input-valid-wf-at-f-start input-before-at-f-start not-halted rdi-eq
      result-f = proj₂ f-exec

      ------------------------------------------------------------------
      -- Run g — scaffolded as a re-call on the same alloc.
      ------------------------------------------------------------------
      g-exec : ∃[ mG ] IRResultAWF mG g x s alloc-after-scratch
      g-exec = rec-wf mIn g (⟨,⟩-g-smaller f g {Heap}) x input-loc s alloc-after-scratch
                 input-valid-wf-at-f-start input-before-at-f-start not-halted rdi-eq
      result-g = proj₂ g-exec

      f-trace = IRResultAWF.trace result-f
      g-trace = IRResultAWF.trace result-g

      ------------------------------------------------------------------
      -- Pair-heap trace
      ------------------------------------------------------------------
      pair-heap-trace : AbstractTrace
      pair-heap-trace =
          mov-to-output
        ∷ store-at-slot backup-slot
        ∷ f-trace
        ++ store-at-slot fst-stash
        ∷ restore-input backup-slot
        ∷ g-trace
        ++ store-at-slot snd-stash
        ∷ instr-alloc-heap 2
        ∷ store-at-slot pair-stash
        ∷ mov-to-input
        ∷ load-from-slot fst-stash
        ∷ store-indirect
        ∷ load-from-slot snd-stash
        ∷ store-indirect-suc
        ∷ load-from-slot pair-stash
        ∷ []

      s-final : LocState FS
      s-final = proj₁ (exec-trace pair-heap-trace s alloc)

      alloc-final : AllocState {FS}
      alloc-final = proj₂ (exec-trace pair-heap-trace s alloc)

      not-halted-final : halted s-final ≡ false
      not-halted-final = exec-trace-preserves-halted-WF pair-heap-trace s alloc not-halted SMP.!!
        -- TODO: replace SMP.!! with the trace-twf witness once `trace-twf` discharges

      ------------------------------------------------------------------
      -- Pair location (fresh AtDynamic) and validity at final state.
      --
      -- The exact heap ref depends on f's and g's intermediate heap
      -- allocations; for the scaffold we leave it abstract and let
      -- `SMP.!!` produce the witness.
      ------------------------------------------------------------------
      pair-loc : ValueLocation FS
      pair-loc = SMP.!!  -- fresh AtDynamic at next-heap-ref-after-(setup ++ f ++ middle ++ g ++ middle')

      pair-valid-final : ValidAtWF Heap alloc-final
                           (sem-pair (eval f x) (eval g x)) pair-loc s-final
      pair-valid-final = SMP.!!

      pair-before-final : BeforeFrontier alloc-final pair-loc
      pair-before-final = SMP.!!

      pair-rax-eq : readReg (regs s-final) Output ≡ SV-Ptr pair-loc
      pair-rax-eq = SMP.!!

      -- Continuation-alloc side: caller's frame, but final's next-slot and
      -- next-heap-ref (so BeforeFrontier passes for the fresh heap pair-loc).
      pair-cont-alloc : AllocState {FS}
      pair-cont-alloc = record alloc { next-slot     = next-slot     alloc-final
                                     ; next-heap-ref = next-heap-ref alloc-final }

      pair-valid-cont : ValidAtWF Heap pair-cont-alloc
                           (sem-pair (eval f x) (eval g x)) pair-loc s-final
      pair-valid-cont = SMP.!!

      pair-before-cont : BeforeFrontier pair-cont-alloc pair-loc
      pair-before-cont = SMP.!!

      ------------------------------------------------------------------
      -- Budgets
      ------------------------------------------------------------------
      rf-stack = IRResultAWF.stack-budget result-f
      rg-stack = IRResultAWF.stack-budget result-g
      rf-scratch = IRResultAWF.scratch-budget result-f
      rg-scratch = IRResultAWF.scratch-budget result-g
      rf-heap = IRResultAWF.heap-budget result-f
      rg-heap = IRResultAWF.heap-budget result-g

      -- Pair scaffolding uses 4 scratch slots + the sub-IR budgets.
      req-pair-stack : ℕ
      req-pair-stack = 4 +ℕ rf-stack +ℕ rg-stack

      req-pair-scratch : ℕ
      req-pair-scratch = 4 +ℕ rf-scratch +ℕ rg-scratch

      -- Heap: one fresh ref for the pair block, plus whatever f and g consumed.
      req-pair-heap : ℕ
      req-pair-heap = suc (rf-heap +ℕ rg-heap)

      -- Concrete watermark: covers the 4 scratch slots + the high
      -- watermarks of f and g, capped via ⊔.
      max-slot-pair : ℕ
      max-slot-pair = suc pair-stash
                    ⊔ IRResultAWF.max-slot-written result-f
                    ⊔ IRResultAWF.max-slot-written result-g

      -- alloc-final.next-heap-ref ≥ alloc.next-heap-ref by composing
      -- f's heap-monotone, g's heap-monotone, and the +1 from
      -- instr-alloc-heap. For now keep as SMP.!! pending proper state
      -- threading; the budget side is already correct.
      heap-mono : next-heap-ref alloc ≤ next-heap-ref alloc-final
      heap-mono = SMP.!!
