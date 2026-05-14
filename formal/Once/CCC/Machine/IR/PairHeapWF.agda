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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-identityʳ; m≤n+m; m≤n⊔m; m≤m⊔n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

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
        ; frame-preserved = refl  -- alloc-final = record alloc { ... } definitionally
        ; trace-twf = SMP.!!
        ; mem-preserved-before = λ _ _ → SMP.!!  -- TODO: heap-aware mem-preserved
        ; trace-preserves-halted = exec-trace-preserves-halted-WF pair-heap-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-monotone-pair
        ; max-slot-written = max-slot-pair
        ; max-slot-geq-final = max-slot-geq-final-pair
        ; stack-budget = req-pair-stack
        ; max-slot-usage-bound = max-slot-usage-bound-pair
        ; slot-stays-in-budget = slot-stays-in-budget-pair
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
        ; max-heap-usage-bound = max-heap-usage-bound-pair
        -- ARCHITECTURAL: trace-no-heap-writes is structurally false for
        -- pair-heap-trace (contains store-indirect / store-indirect-suc).
        -- mem-preserved-before is the load-bearing consequence-form
        -- invariant; this field stays SMP.!! by design for heap-mode IRs.
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

      -- Plan 0.14: phrased as `next-slot alloc + 4` (not `f-start`) so
      -- alloc-after-scratch is definitionally equal to the output of
      -- `instr-alloc-stack 4` at the end of setup-trace.
      alloc-after-scratch : AllocState {FS}
      alloc-after-scratch = record alloc { next-slot = next-slot alloc +ℕ 4 }

      ------------------------------------------------------------------
      -- Trace phases — named so each phase's proofs can target the
      -- correct intermediate state without re-deriving exec-trace
      -- decompositions.
      ------------------------------------------------------------------
      -- Plan 0.14: setup ends with `instr-alloc-stack 4` so the
      -- runtime next-slot bumps to match `alloc-after-scratch` (= the
      -- construction-time alloc passed to f's rec-wf). Eliminates the
      -- runtime/construction-time alignment story that PairWF2 had to
      -- thread by hand. See [[alloc-construction-vs-runtime]].
      setup-trace : AbstractTrace
      setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ instr-alloc-stack 4 ∷ []

      mid-trace : AbstractTrace
      mid-trace = store-at-slot fst-stash ∷ restore-input backup-slot ∷ []

      post-trace : AbstractTrace
      post-trace =
          store-at-slot snd-stash
        ∷ instr-alloc-heap 2
        ∷ store-at-slot pair-stash
        ∷ mov-to-input
        ∷ load-from-slot fst-stash
        ∷ store-indirect
        ∷ load-from-slot snd-stash
        ∷ store-indirect-suc
        ∷ load-from-slot pair-stash
        ∷ []

      ------------------------------------------------------------------
      -- Setup phase: stash input pointer to backup-slot.
      -- Neither instruction bumps next-slot or next-heap-ref, so the
      -- runtime alloc matches input alloc on those axes.
      ------------------------------------------------------------------
      s-after-setup : LocState FS
      s-after-setup = proj₁ (exec-trace setup-trace s alloc)

      -- All three setup instructions are unconditional preservers (InstrWF = ⊤).
      setup-twf : TraceWF s alloc setup-trace
      setup-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))

      not-halted-after-setup : halted s-after-setup ≡ false
      not-halted-after-setup = exec-trace-preserves-halted-WF setup-trace s alloc not-halted setup-twf

      -- All three setup instructions preserve Input1:
      --   mov-to-output writes Output, store-at-slot writes stack mem,
      --   instr-alloc-stack bumps stackSlot (in regs) but not Input1.
      rdi-eq-after-setup : readReg (regs s-after-setup) Input1 ≡ SV-Ptr input-loc
      rdi-eq-after-setup =
        let s₁      = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁  = proj₂ (exec-abstract mov-to-output s alloc)
            mov-preserves : readReg (regs s₁) Input1 ≡ readReg (regs s) Input1
            mov-preserves = writeReg-preserves (regs s) Output Input1 (readReg (regs s) Input1) (λ ())
            not-halted₁ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            s₂      = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            alloc₂  = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            store-preserves : readReg (regs s₂) Input1 ≡ readReg (regs s₁) Input1
            store-preserves = exec-abstract-store-at-slot-preserves-input backup-slot s₁ alloc₁
            not-halted₂ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ alloc₁ not-halted₁ iph-store-at-slot
            s₃      = proj₁ (exec-abstract (instr-alloc-stack 4) s₂ alloc₂)
            -- instr-alloc-stack only changes regs.stackSlot, leaving
            -- input1 / input2 / output untouched (definitional).
            alloc-stack-preserves : readReg (regs s₃) Input1 ≡ readReg (regs s₂) Input1
            alloc-stack-preserves = refl
            d1 : exec-trace setup-trace s alloc ≡
                 exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack 4 ∷ []) s₁ alloc₁
            d1 = exec-trace-cons mov-to-output _ s alloc not-halted
            d2 : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack 4 ∷ []) s₁ alloc₁ ≡
                 exec-trace (instr-alloc-stack 4 ∷ []) s₂ alloc₂
            d2 = exec-trace-cons (store-at-slot backup-slot) _ s₁ alloc₁ not-halted₁
            d3 : exec-trace (instr-alloc-stack 4 ∷ []) s₂ alloc₂ ≡
                 exec-abstract (instr-alloc-stack 4) s₂ alloc₂
            d3 = exec-trace-single (instr-alloc-stack 4) s₂ alloc₂ not-halted₂
            s-eq : s-after-setup ≡ s₃
            s-eq = cong proj₁ (trans d1 (trans d2 d3))
        in trans (cong (λ st → readReg (regs st) Input1) s-eq)
                 (trans alloc-stack-preserves
                   (trans store-preserves
                     (trans mov-preserves rdi-eq)))

      -- f-start ≡ next-slot alloc + 4 propositionally. `4 + n` reduces
      -- definitionally to suc(suc(suc(suc n))) = f-start (when
      -- n = next-slot alloc); add `+-comm` to swap.
      f-start≡+4 : f-start ≡ next-slot alloc +ℕ 4
      f-start≡+4 = sym (+-comm (next-slot alloc) 4)
        where open import Data.Nat.Properties using (+-comm)

      input-before-at-f-start : BeforeFrontier alloc-after-scratch input-loc
      input-before-at-f-start = frontier-monotone alloc alloc-after-scratch refl
                                  (subst (next-slot alloc ≤_) f-start≡+4
                                    (≤-trans (n≤1+n backup-slot)
                                      (≤-trans (n≤1+n fst-stash)
                                        (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash)))))
                                  ≤-refl input-loc input-before

      -- setup-trace stack writes: backup-slot = next-slot alloc.
      -- BeforeFrontier locations are below backup-slot, so the store
      -- doesn't touch them. instr-alloc-stack bumps regs.stackSlot
      -- and alloc.next-slot but doesn't touch stack memory.
      mem-preserved-through-setup :
        ∀ loc → BeforeFrontier alloc loc → readLoc s-after-setup loc ≡ readLoc s loc
      mem-preserved-through-setup loc bf =
        let s₁      = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁  = proj₂ (exec-abstract mov-to-output s alloc)
            not-halted₁ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            mov-mem : readLoc s₁ loc ≡ readLoc s loc
            mov-mem = SMP.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-mem s alloc loc
            frame-eq₁ : current-frame alloc₁ ≡ current-frame alloc
            frame-eq₁ = exec-abstract-preserves-frame mov-to-output s alloc
            loc≢slot : loc ≢ AtStack (current-frame alloc₁) backup-slot
            loc≢slot eq = fresh-stack-after alloc loc bf
                            (trans eq (cong (λ fr → AtStack fr backup-slot) frame-eq₁))
            s₂      = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            alloc₂  = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            store-mem : readLoc s₂ loc ≡ readLoc s₁ loc
            store-mem = exec-abstract-store-at-slot-preserves-loc backup-slot s₁ alloc₁ loc loc≢slot
            not-halted₂ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ alloc₁ not-halted₁ iph-store-at-slot
            -- instr-alloc-stack only changes regs.stackSlot, so stack/heap
            -- memory is preserved; readLoc reads memory, not stackSlot.
            s₃      = proj₁ (exec-abstract (instr-alloc-stack 4) s₂ alloc₂)
            alloc-stack-mem : readLoc s₃ loc ≡ readLoc s₂ loc
            alloc-stack-mem = ExecLemmas.readLoc-stackMem-eq s₃ s₂ loc refl refl
            d1 : exec-trace setup-trace s alloc ≡
                 exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack 4 ∷ []) s₁ alloc₁
            d1 = exec-trace-cons mov-to-output _ s alloc not-halted
            d2 : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack 4 ∷ []) s₁ alloc₁ ≡
                 exec-trace (instr-alloc-stack 4 ∷ []) s₂ alloc₂
            d2 = exec-trace-cons (store-at-slot backup-slot) _ s₁ alloc₁ not-halted₁
            d3 : exec-trace (instr-alloc-stack 4 ∷ []) s₂ alloc₂ ≡
                 exec-abstract (instr-alloc-stack 4) s₂ alloc₂
            d3 = exec-trace-single (instr-alloc-stack 4) s₂ alloc₂ not-halted₂
            s-eq : s-after-setup ≡ s₃
            s-eq = cong proj₁ (trans d1 (trans d2 d3))
        in trans (cong (λ st → readLoc st loc) s-eq)
                 (trans alloc-stack-mem (trans store-mem mov-mem))

      input-valid-wf-at-f-start : ValidAtWF mIn alloc-after-scratch x input-loc s-after-setup
      input-valid-wf-at-f-start =
        validityWF-frontier-advance x input-loc s-after-setup refl
          (subst (next-slot alloc ≤_) f-start≡+4
            (≤-trans (n≤1+n backup-slot)
              (≤-trans (n≤1+n fst-stash)
                (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash)))))
          ≤-refl
          (validityWF-mem-preserved x input-loc s s-after-setup input-before
            mem-preserved-through-setup input-valid-wf)

      ------------------------------------------------------------------
      -- f phase: run f on (s-after-setup, alloc-after-scratch).
      ------------------------------------------------------------------
      f-exec : ∃[ mF ] IRResultAWF mF f x s-after-setup alloc-after-scratch
      f-exec = rec-wf mIn f (⟨,⟩-f-smaller f g {Heap}) x input-loc s-after-setup alloc-after-scratch
                 input-valid-wf-at-f-start input-before-at-f-start
                 not-halted-after-setup rdi-eq-after-setup
      result-f = proj₂ f-exec
      f-trace = IRResultAWF.trace result-f

      -- Plan 0.14: s-after-f / alloc-after-f are the RUNTIME values
      -- after exec-trace f-trace from (s-after-setup, alloc-after-scratch).
      -- result-f.final-state ≡ s-after-f via trace-correct; result-f.final-alloc
      -- is a construction-time bookkeeping alloc that may differ from the
      -- runtime alloc on slot/heap-ref dimensions. Bridge via monotone
      -- lemmas where needed. See [[alloc-construction-vs-runtime]] and the
      -- PairWF2 stage-A/B pattern.
      s-after-f : LocState FS
      s-after-f = proj₁ (exec-trace f-trace s-after-setup alloc-after-scratch)
      alloc-after-f : AllocState {FS}
      alloc-after-f = proj₂ (exec-trace f-trace s-after-setup alloc-after-scratch)

      -- s-after-f ≡ result-f.final-state by trace-correct (free bridge).
      s-after-f-eq : s-after-f ≡ IRResultAWF.final-state result-f
      s-after-f-eq = IRResultAWF.trace-correct result-f

      not-halted-after-f : halted s-after-f ≡ false
      not-halted-after-f = exec-trace-preserves-halted-WF f-trace s-after-setup alloc-after-scratch
                             not-halted-after-setup (IRResultAWF.trace-twf result-f)

      ------------------------------------------------------------------
      -- Middle phase: stash f's result to fst-stash, restore input.
      --
      -- The restore-input backup-slot precondition needs that backup-slot
      -- still holds SV-Ptr input-loc at this point. That value was put
      -- there by setup; f preserves it (BeforeFrontier alloc-after-scratch
      -- holds for backup-slot since backup-slot < f-start = next-slot
      -- alloc-after-scratch); store-at-slot fst-stash also preserves it
      -- (different slot).
      ------------------------------------------------------------------

      -- backup-slot < f-start = next-slot alloc-after-scratch, so
      -- BeforeFrontier alloc-after-scratch holds for it.
      backup<f-start : backup-slot < next-slot alloc-after-scratch
      backup<f-start =
        subst (suc backup-slot ≤_) f-start≡+4
          (≤-trans (n≤1+n fst-stash)
            (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash)))

      backup-loc-before-scratch : BeforeFrontier alloc-after-scratch (AtStack frame backup-slot)
      backup-loc-before-scratch = stack-before refl backup<f-start

      -- After setup, backup-slot holds SV-Ptr input-loc. Step through
      -- setup-trace's three instructions.
      backup-after-setup : readLoc s-after-setup (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc)
      backup-after-setup =
        let s₁ = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁ = proj₂ (exec-abstract mov-to-output s alloc)
            not-halted₁ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            s₂ = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            alloc₂ = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            not-halted₂ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ alloc₁ not-halted₁ iph-store-at-slot
            s₃ = proj₁ (exec-abstract (instr-alloc-stack 4) s₂ alloc₂)
            -- step1: after mov-to-output, Output := readReg Input1 = SV-Ptr input-loc.
            mov-output : readReg (regs s₁) Output ≡ SV-Ptr input-loc
            mov-output = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) rdi-eq
            -- step2: after store-at-slot backup-slot, stack[frame, backup-slot] = Output = SV-Ptr input-loc.
            store-stores : readLoc s₂ (AtStack (current-frame alloc₁) backup-slot) ≡ just (readReg (regs s₁) Output)
            store-stores = writeLoc-read-same-stack s₁ (current-frame alloc₁) backup-slot (readReg (regs s₁) Output)
            backup-at-s₂ : readLoc s₂ (AtStack (current-frame alloc₁) backup-slot) ≡ just (SV-Ptr input-loc)
            backup-at-s₂ = trans store-stores (cong just mov-output)
            -- step3: instr-alloc-stack preserves stack memory.
            backup-at-s₃ : readLoc s₃ (AtStack (current-frame alloc₁) backup-slot) ≡
                           readLoc s₂ (AtStack (current-frame alloc₁) backup-slot)
            backup-at-s₃ = ExecLemmas.readLoc-stackMem-eq s₃ s₂ (AtStack (current-frame alloc₁) backup-slot) refl refl
            -- exec-trace decomposition
            d1 : exec-trace setup-trace s alloc ≡
                 exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack 4 ∷ []) s₁ alloc₁
            d1 = exec-trace-cons mov-to-output _ s alloc not-halted
            d2 : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack 4 ∷ []) s₁ alloc₁ ≡
                 exec-trace (instr-alloc-stack 4 ∷ []) s₂ alloc₂
            d2 = exec-trace-cons (store-at-slot backup-slot) _ s₁ alloc₁ not-halted₁
            d3 : exec-trace (instr-alloc-stack 4 ∷ []) s₂ alloc₂ ≡
                 exec-abstract (instr-alloc-stack 4) s₂ alloc₂
            d3 = exec-trace-single (instr-alloc-stack 4) s₂ alloc₂ not-halted₂
            s-eq : s-after-setup ≡ s₃
            s-eq = cong proj₁ (trans d1 (trans d2 d3))
        in trans (cong (λ st → readLoc st (AtStack frame backup-slot)) s-eq)
                 (trans backup-at-s₃ backup-at-s₂)

      -- f preserves backup-slot. Discharged via mem-preserved-before
      -- from result-f (consequence-form invariant: any BeforeFrontier
      -- alloc-after-scratch loc is unchanged after f). For heap-mode f
      -- the field is currently SMP.!! pending heap-aware derivation;
      -- consuming it transitively trusts the place-stage discipline
      -- that store-indirect's Input1 is AtDynamic.
      backup-after-f : readLoc s-after-f (AtStack frame backup-slot) ≡
                       readLoc s-after-setup (AtStack frame backup-slot)
      backup-after-f =
        subst (λ st → readLoc st (AtStack frame backup-slot) ≡
                      readLoc s-after-setup (AtStack frame backup-slot))
              (sym s-after-f-eq)
              (irresult-mem-preserved result-f (AtStack frame backup-slot) backup-loc-before-scratch)
        where
          open ClosureWellFormedDef {FS} program-bound using (irresult-mem-preserved)

      s-after-middle : LocState FS
      s-after-middle = proj₁ (exec-trace mid-trace s-after-f alloc-after-f)
      alloc-after-middle : AllocState {FS}
      alloc-after-middle = proj₂ (exec-trace mid-trace s-after-f alloc-after-f)

      -- s-after-fst-store : state after the first instruction of mid-trace
      s-after-fst-store : LocState FS
      s-after-fst-store = proj₁ (exec-abstract (store-at-slot fst-stash) s-after-f alloc-after-f)
      alloc-after-fst-store : AllocState {FS}
      alloc-after-fst-store = proj₂ (exec-abstract (store-at-slot fst-stash) s-after-f alloc-after-f)

      -- backup-slot is preserved through store-at-slot fst-stash
      -- (different slot: fst-stash = suc backup-slot ≠ backup-slot).
      -- frame ≡ current-frame alloc-after-f via chained frame-preserved
      -- through setup-trace and f-trace.
      -- current-frame alloc-after-scratch ≡ frame definitionally
      -- (record-update doesn't touch current-frame); exec-trace-preserves-frame
      -- on f-trace gives the rest.
      frame-after-f-eq : current-frame alloc-after-f ≡ frame
      frame-after-f-eq = exec-trace-preserves-frame f-trace s-after-setup alloc-after-scratch

      ¬suc-≡-self : ∀ n → suc n ≢ n
      ¬suc-≡-self (suc n) eq = ¬suc-≡-self n (suc-injective eq)
        where open import Data.Nat.Properties using (suc-injective)
      ¬suc-≡-self zero ()

      AtStack-snd-injective : ∀ {f₁ f₂ : Frame} {k₁ k₂ : Slot} →
                              AtStack {FS} f₁ k₁ ≡ AtStack {FS} f₂ k₂ → k₁ ≡ k₂
      AtStack-snd-injective refl = refl

      backup-after-fst-store : readLoc s-after-fst-store (AtStack frame backup-slot) ≡
                               readLoc s-after-f (AtStack frame backup-slot)
      backup-after-fst-store =
        writeLoc-preserves-other s-after-f
          (AtStack (current-frame alloc-after-f) fst-stash)
          (AtStack frame backup-slot)
          (readReg (regs s-after-f) Output)
          (λ eq → ¬suc-≡-self backup-slot (AtStack-snd-injective eq))

      -- Chain everything: backup-slot in s-after-fst-store = SV-Ptr input-loc.
      backup-at-fst-store : readLoc s-after-fst-store (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc)
      backup-at-fst-store = trans backup-after-fst-store (trans backup-after-f backup-after-setup)

      -- store-at-slot preserves frame, so current-frame alloc-after-fst-store
      -- = current-frame alloc-after-f. Use exec-abstract-preserves-frame.
      frame-after-fst-store-eq : current-frame alloc-after-fst-store ≡ current-frame alloc-after-f
      frame-after-fst-store-eq = exec-abstract-preserves-frame (store-at-slot fst-stash) s-after-f alloc-after-f

      -- Bridge backup-at-fst-store from `frame` to `current-frame alloc-after-fst-store`.
      backup-at-fst-store-current-frame :
        readLoc s-after-fst-store (AtStack (current-frame alloc-after-fst-store) backup-slot) ≡
        just (SV-Ptr input-loc)
      backup-at-fst-store-current-frame =
        subst (λ f → readLoc s-after-fst-store (AtStack f backup-slot) ≡ just (SV-Ptr input-loc))
              (sym (trans frame-after-fst-store-eq frame-after-f-eq))
              backup-at-fst-store

      mid-twf : TraceWF s-after-f alloc-after-f mid-trace
      mid-twf = twf-∷ tt (twf-∷ (SV-Ptr input-loc , backup-at-fst-store-current-frame) twf-[])

      not-halted-after-middle : halted s-after-middle ≡ false
      not-halted-after-middle = exec-trace-preserves-halted-WF mid-trace s-after-f alloc-after-f
                                  not-halted-after-f mid-twf

      not-halted-after-fst-store : halted s-after-fst-store ≡ false
      not-halted-after-fst-store = exec-abstract-preserves-halted (store-at-slot fst-stash)
        s-after-f alloc-after-f not-halted-after-f iph-store-at-slot

      s-after-restore : LocState FS
      s-after-restore = proj₁ (exec-abstract (restore-input backup-slot)
                                 s-after-fst-store alloc-after-fst-store)

      -- The `just` branch of exec-restore-input-with-value writes
      -- the looked-up value to Input1. backup-at-fst-store-current-frame
      -- says the lookup returns just (SV-Ptr input-loc).
      restore-input-input1 : readReg (regs s-after-restore) Input1 ≡ SV-Ptr input-loc
      restore-input-input1
        rewrite backup-at-fst-store-current-frame =
          writeReg-same (regs s-after-fst-store) Input1 (SV-Ptr input-loc)

      -- mid-trace's last instruction is restore-input backup-slot, which
      -- overwrites Input1 with stack[backup-slot] = SV-Ptr input-loc.
      rdi-eq-after-middle : readReg (regs s-after-middle) Input1 ≡ SV-Ptr input-loc
      rdi-eq-after-middle =
        let d1 : exec-trace mid-trace s-after-f alloc-after-f ≡
                 exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store
            d1 = exec-trace-cons (store-at-slot fst-stash) _ s-after-f alloc-after-f not-halted-after-f
            d2 : exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store ≡
                 exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store
            d2 = exec-trace-single (restore-input backup-slot) s-after-fst-store alloc-after-fst-store
                   not-halted-after-fst-store
            s-eq : s-after-middle ≡ s-after-restore
            s-eq = cong proj₁ (trans d1 d2)
        in trans (cong (λ st → readReg (regs st) Input1) s-eq) restore-input-input1

      ------------------------------------------------------------------
      -- Construction-time alloc passed to g-exec. PairWF2's pattern:
      -- runtime state + construction-time alloc (with bookkeeping that
      -- reflects result-f's claimed final alloc).
      ------------------------------------------------------------------
      alloc-for-g : AllocState {FS}
      alloc-for-g = record alloc { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
                                 ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) }

      input-before-at-g-start : BeforeFrontier alloc-for-g input-loc
      input-before-at-g-start = frontier-monotone alloc alloc-for-g refl
                                  (≤-trans
                                    (subst (next-slot alloc ≤_) f-start≡+4
                                      (≤-trans (n≤1+n backup-slot)
                                        (≤-trans (n≤1+n fst-stash)
                                          (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash)))))
                                    (IRResultAWF.slot-monotone result-f))
                                  (IRResultAWF.heap-monotone result-f)
                                  input-loc input-before

      -- BeforeFrontier alloc loc lifts to BeforeFrontier alloc-after-scratch loc
      -- (alloc-after-scratch.next-slot ≥ next-slot alloc; same frame; same heap-ref).
      bf-lift-to-scratch :
        ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-after-scratch loc
      bf-lift-to-scratch loc bf =
        frontier-monotone alloc alloc-after-scratch refl
          (subst (next-slot alloc ≤_) f-start≡+4
            (≤-trans (n≤1+n backup-slot)
              (≤-trans (n≤1+n fst-stash)
                (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash)))))
          ≤-refl loc bf

      -- s → s-after-middle preserves BeforeFrontier-alloc locations.
      -- Chain through setup, f, and mid using:
      --   - mem-preserved-through-setup: setup-trace preserves
      --   - irresult-mem-preserved result-f: f-trace preserves (via
      --     mem-preserved-before, transitively place-stage-trusted
      --     for heap-mode f)
      --   - mid-trace preservation: store-at-slot fst-stash writes
      --     above frontier (fst-stash > next-slot alloc); restore-input
      --     writes regs, not memory
      -- mid-trace step 1 (store-at-slot fst-stash): writes at fst-stash =
      -- suc backup-slot, which is > next-slot alloc. BeforeFrontier alloc
      -- locs are either AtDynamic, AtStack ancestor, or AtStack with
      -- slot < next-slot alloc ≤ fst-stash — all disjoint from the write.
      -- Top-level helpers (let-bindings can't have where clauses).
      AtStack-fst-injective : ∀ {f₁ f₂ : Frame} {k₁ k₂ : Slot} →
                              AtStack {FS} f₁ k₁ ≡ AtStack {FS} f₂ k₂ → f₁ ≡ f₂
      AtStack-fst-injective refl = refl

      k<fst-stash : ∀ {k} → k < next-slot alloc → k < fst-stash
      k<fst-stash k<n = ≤-trans k<n (n≤1+n (next-slot alloc))

      store-fst-preserves : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-after-fst-store loc ≡ readLoc s-after-f loc
      store-fst-preserves (AtStack f k) (stack-before f≡cf k<next) =
        writeLoc-preserves-other s-after-f
          (AtStack (current-frame alloc-after-f) fst-stash) (AtStack f k)
          (readReg (regs s-after-f) Output)
          (λ eq → <⇒≢ (k<fst-stash k<next) (sym (AtStack-snd-injective eq)))
        where open import Data.Nat.Properties using (<⇒≢)
      store-fst-preserves (AtStack f k) (stack-ancestor cf≺f _) =
        writeLoc-preserves-other s-after-f
          (AtStack (current-frame alloc-after-f) fst-stash) (AtStack f k)
          (readReg (regs s-after-f) Output)
          (λ eq → ≺⇒≢ cf≺f (trans (sym frame-after-f-eq) (AtStack-fst-injective eq)))
      store-fst-preserves (AtDynamic hl) (heap-before _) =
        writeLoc-preserves-other s-after-f
          (AtStack (current-frame alloc-after-f) fst-stash) (AtDynamic hl)
          (readReg (regs s-after-f) Output)
          (λ ())

      -- Top-level helpers (restore-input case split on the Maybe).
      restore-input-stackMem-aux : ∀ (m : Maybe (StoredValue FS)) →
        stackMem (proj₁ (exec-restore-input-with-value m s-after-fst-store
                          alloc-after-fst-store)) ≡ stackMem s-after-fst-store
      restore-input-stackMem-aux (just _) = refl
      restore-input-stackMem-aux nothing = refl

      restore-input-heapMem-aux : ∀ (m : Maybe (StoredValue FS)) →
        heapMem (proj₁ (exec-restore-input-with-value m s-after-fst-store
                         alloc-after-fst-store)) ≡ heapMem s-after-fst-store
      restore-input-heapMem-aux (just _) = refl
      restore-input-heapMem-aux nothing = refl

      mid-state-eq : s-after-middle ≡ s-after-restore
      mid-state-eq =
        let d1 : exec-trace mid-trace s-after-f alloc-after-f ≡
                 exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store
            d1 = exec-trace-cons (store-at-slot fst-stash) _ s-after-f alloc-after-f not-halted-after-f
            d2 : exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store ≡
                 exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store
            d2 = exec-trace-single (restore-input backup-slot) s-after-fst-store alloc-after-fst-store
                   not-halted-after-fst-store
        in cong proj₁ (trans d1 d2)

      restore-input-preserves-stackMem :
        stackMem s-after-middle ≡ stackMem s-after-fst-store
      restore-input-preserves-stackMem =
        trans (cong stackMem mid-state-eq)
              (restore-input-stackMem-aux
                (readLoc s-after-fst-store
                  (AtStack (current-frame alloc-after-fst-store) backup-slot)))

      restore-input-preserves-heapMem :
        heapMem s-after-middle ≡ heapMem s-after-fst-store
      restore-input-preserves-heapMem =
        trans (cong heapMem mid-state-eq)
              (restore-input-heapMem-aux
                (readLoc s-after-fst-store
                  (AtStack (current-frame alloc-after-fst-store) backup-slot)))

      restore-input-preserves-mem : ∀ loc →
        readLoc s-after-middle loc ≡ readLoc s-after-fst-store loc
      restore-input-preserves-mem loc =
        ExecLemmas.readLoc-stackMem-eq s-after-middle s-after-fst-store loc
          restore-input-preserves-stackMem restore-input-preserves-heapMem

      mem-preserved-f-to-mid :
        ∀ loc → BeforeFrontier alloc loc → readLoc s-after-middle loc ≡ readLoc s-after-f loc
      mem-preserved-f-to-mid loc bf =
        trans (restore-input-preserves-mem loc) (store-fst-preserves loc bf)

      mem-preserved-s-to-after-middle :
        ∀ loc → BeforeFrontier alloc loc → readLoc s-after-middle loc ≡ readLoc s loc
      mem-preserved-s-to-after-middle loc bf =
        trans (mem-preserved-f-to-mid loc bf)
              (trans (subst (λ st → readLoc st loc ≡ readLoc s-after-setup loc)
                            (sym s-after-f-eq)
                            (irresult-mem-preserved result-f loc (bf-lift-to-scratch loc bf)))
                     (mem-preserved-through-setup loc bf))
        where
          open ClosureWellFormedDef {FS} program-bound using (irresult-mem-preserved)

      input-valid-wf-at-g-start : ValidAtWF mIn alloc-for-g x input-loc s-after-middle
      input-valid-wf-at-g-start =
        validityWF-frontier-advance x input-loc s-after-middle refl
          (≤-trans
            (subst (next-slot alloc ≤_) f-start≡+4
              (≤-trans (n≤1+n backup-slot)
                (≤-trans (n≤1+n fst-stash)
                  (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash)))))
            (IRResultAWF.slot-monotone result-f))
          (IRResultAWF.heap-monotone result-f)
          (validityWF-mem-preserved x input-loc s s-after-middle input-before
            mem-preserved-s-to-after-middle input-valid-wf)

      ------------------------------------------------------------------
      -- g phase: run g on (s-after-middle, alloc-for-g).
      ------------------------------------------------------------------
      g-exec : ∃[ mG ] IRResultAWF mG g x s-after-middle alloc-for-g
      g-exec = rec-wf mIn g (⟨,⟩-g-smaller f g {Heap}) x input-loc
                 s-after-middle alloc-for-g
                 input-valid-wf-at-g-start input-before-at-g-start
                 not-halted-after-middle rdi-eq-after-middle
      result-g = proj₂ g-exec
      g-trace = IRResultAWF.trace result-g

      s-after-g : LocState FS
      s-after-g = IRResultAWF.final-state result-g
      alloc-after-g : AllocState {FS}
      alloc-after-g = IRResultAWF.final-alloc result-g

      ------------------------------------------------------------------
      -- Pair-heap trace: composition of all phases.
      ------------------------------------------------------------------
      pair-heap-trace : AbstractTrace
      pair-heap-trace = setup-trace ++ f-trace ++ mid-trace ++ g-trace ++ post-trace

      s-final : LocState FS
      s-final = proj₁ (exec-trace pair-heap-trace s alloc)

      -- Plan 0.14: construction-time alloc-final. final-alloc has no
      -- trace-correct constraint, so we're free to pick a value that
      -- makes the budget bookkeeping work out. After g, alloc-after-g
      -- summarises sub-IR allocations; post-trace's only frontier-bumping
      -- instruction is instr-alloc-heap (+1 next-heap-ref). next-slot is
      -- unchanged by post-trace.
      alloc-final : AllocState {FS}
      alloc-final = record alloc
        { next-slot     = next-slot     alloc-after-g
        ; next-heap-ref = suc (next-heap-ref alloc-after-g)
        }

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
      -- Concrete: after g finishes, alloc-after-g.next-heap-ref is the
      -- ref the next instr-alloc-heap will hand out. store-at-slot
      -- snd-stash doesn't touch next-heap-ref, so the fresh ref at the
      -- instr-alloc-heap point is exactly next-heap-ref alloc-after-g.
      pair-loc : ValueLocation FS
      pair-loc = AtDynamic (heap-loc (mkHeapRef (next-heap-ref alloc-after-g)) 0)

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

      -- next-slot alloc-final = next-slot alloc-after-g ≤ max-slot-written result-g ≤ max-slot-pair.
      max-slot-geq-final-pair : next-slot alloc-final ≤ max-slot-pair
      max-slot-geq-final-pair =
        ≤-trans (IRResultAWF.max-slot-geq-final result-g)
                (m≤n⊔m (suc pair-stash ⊔ IRResultAWF.max-slot-written result-f)
                       (IRResultAWF.max-slot-written result-g))

      -- Bounds for the three components of max-slot-pair, all in terms of
      -- next-slot alloc + req-pair-stack = next-slot alloc + 4 + rf-stack + rg-stack.
      open import Data.Nat.Properties using (+-monoʳ-≤; +-monoˡ-≤; +-assoc; +-suc; +-comm; ⊔-lub)

      pair-stash≡+3 : suc pair-stash ≡ next-slot alloc +ℕ 4
      pair-stash≡+3 = f-start≡+4

      suc-pair-stash≤budget : suc pair-stash ≤ next-slot alloc +ℕ req-pair-stack
      suc-pair-stash≤budget =
        subst (suc pair-stash ≤_)
          (cong (next-slot alloc +ℕ_) refl)
          (≤-trans (≤-reflexive pair-stash≡+3)
                   (+-monoʳ-≤ (next-slot alloc) (m≤m+n 4 (rf-stack +ℕ rg-stack))))
        where open import Data.Nat.Properties using (≤-reflexive)

      -- max-slot-written result-f ≤ next-slot alloc-after-scratch + rf-stack
      --                          = (next-slot alloc + 4) + rf-stack
      --                          ≤ next-slot alloc + (4 + rf-stack + rg-stack).
      max-f-bound : IRResultAWF.max-slot-written result-f ≤ next-slot alloc +ℕ req-pair-stack
      max-f-bound =
        let bound-f : IRResultAWF.max-slot-written result-f ≤ next-slot alloc-after-scratch +ℕ rf-stack
            bound-f = IRResultAWF.max-slot-usage-bound result-f
            -- next-slot alloc-after-scratch = next-slot alloc + 4
            -- (next-slot alloc + 4) + rf-stack = next-slot alloc + (4 + rf-stack)
            step1 : next-slot alloc-after-scratch +ℕ rf-stack ≡ next-slot alloc +ℕ (4 +ℕ rf-stack)
            step1 = +-assoc (next-slot alloc) 4 rf-stack
            -- 4 + rf-stack ≤ 4 + rf-stack + rg-stack = req-pair-stack
            step2 : 4 +ℕ rf-stack ≤ req-pair-stack
            step2 = m≤m+n (4 +ℕ rf-stack) rg-stack
        in ≤-trans bound-f
             (≤-trans (≤-reflexive step1)
                      (+-monoʳ-≤ (next-slot alloc) step2))
        where open import Data.Nat.Properties using (≤-reflexive)

      -- max-slot-written result-g ≤ next-slot alloc-for-g + rg-stack
      -- alloc-for-g.next-slot = next-slot result-f.final-alloc.
      -- result-f.slot-stays-in-budget: next-slot result-f.final-alloc ≤
      --   next-slot alloc-after-scratch + rf-stack = (next-slot alloc + 4) + rf-stack.
      -- So max-g ≤ ((next-slot alloc + 4) + rf-stack) + rg-stack
      --        = next-slot alloc + (4 + rf-stack + rg-stack) = next-slot alloc + req-pair-stack.
      max-g-bound : IRResultAWF.max-slot-written result-g ≤ next-slot alloc +ℕ req-pair-stack
      max-g-bound =
        let bound-g : IRResultAWF.max-slot-written result-g ≤
                      next-slot (IRResultAWF.final-alloc result-f) +ℕ rg-stack
            bound-g = IRResultAWF.max-slot-usage-bound result-g
            -- result-f.slot-stays-in-budget at alloc-after-scratch gives
            -- `... ≤ next-slot alloc-after-scratch + rf-stack`. Agda eagerly
            -- reduces next-slot alloc-after-scratch to next-slot alloc + 4
            -- (record projection), so the actual type uses (next-slot alloc + 4).
            f-final-bound : next-slot (IRResultAWF.final-alloc result-f) ≤
                            (next-slot alloc +ℕ 4) +ℕ rf-stack
            f-final-bound = IRResultAWF.slot-stays-in-budget result-f
            step : next-slot (IRResultAWF.final-alloc result-f) +ℕ rg-stack ≤
                   ((next-slot alloc +ℕ 4) +ℕ rf-stack) +ℕ rg-stack
            step = +-monoˡ-≤ rg-stack f-final-bound
            -- ((next-slot alloc + 4) + rf-stack) + rg-stack
            --   = next-slot alloc + (4 + rf-stack + rg-stack)
            --   = next-slot alloc + req-pair-stack.
            req-pair-stack-eq : ((next-slot alloc +ℕ 4) +ℕ rf-stack) +ℕ rg-stack ≡
                                next-slot alloc +ℕ req-pair-stack
            req-pair-stack-eq =
              trans (+-assoc (next-slot alloc +ℕ 4) rf-stack rg-stack)
                    (+-assoc (next-slot alloc) 4 (rf-stack +ℕ rg-stack))
        in ≤-trans bound-g (≤-trans step (≤-reflexive req-pair-stack-eq))
        where open import Data.Nat.Properties using (≤-reflexive)

      max-slot-usage-bound-pair : max-slot-pair ≤ next-slot alloc +ℕ req-pair-stack
      max-slot-usage-bound-pair =
        ⊔-lub (⊔-lub suc-pair-stash≤budget max-f-bound) max-g-bound

      -- next-slot alloc-final = next-slot result-g.final-alloc
      --                     ≤ next-slot result-f.final-alloc + rg-stack
      --                     ≤ (next-slot alloc + 4 + rf-stack) + rg-stack
      --                     ≤ next-slot alloc + req-pair-stack.
      slot-stays-in-budget-pair : next-slot alloc-final ≤ next-slot alloc +ℕ req-pair-stack
      slot-stays-in-budget-pair = ≤-trans max-slot-geq-final-pair max-slot-usage-bound-pair

      -- max-heap-usage-bound: next-heap-ref alloc-final = suc (next-heap-ref alloc-after-g)
      -- ≤ next-heap-ref alloc + req-pair-heap.
      -- Chain: alloc-after-g.next-heap-ref ≤ result-f.final.next-heap-ref + rg-heap
      --       (g's max-heap-usage-bound + max-heap-ref-geq-final)
      --     ≤ (next-heap-ref alloc + rf-heap) + rg-heap (similar for f)
      --     = next-heap-ref alloc + (rf-heap + rg-heap).
      -- suc that = next-heap-ref alloc + suc (rf-heap + rg-heap) = + req-pair-heap.
      max-heap-usage-bound-pair :
        next-heap-ref alloc-final ≤ next-heap-ref alloc +ℕ req-pair-heap
      max-heap-usage-bound-pair =
        let g-step : next-heap-ref alloc-after-g ≤
                     next-heap-ref (IRResultAWF.final-alloc result-f) +ℕ rg-heap
            g-step = ≤-trans (IRResultAWF.max-heap-ref-geq-final result-g)
                             (IRResultAWF.max-heap-usage-bound result-g)
            f-step : next-heap-ref (IRResultAWF.final-alloc result-f) ≤
                     next-heap-ref alloc +ℕ rf-heap
            f-step = ≤-trans (IRResultAWF.max-heap-ref-geq-final result-f)
                             (IRResultAWF.max-heap-usage-bound result-f)
            chain : next-heap-ref alloc-after-g ≤
                    (next-heap-ref alloc +ℕ rf-heap) +ℕ rg-heap
            chain = ≤-trans g-step (+-monoˡ-≤ rg-heap f-step)
            assoc-eq : (next-heap-ref alloc +ℕ rf-heap) +ℕ rg-heap ≡
                       next-heap-ref alloc +ℕ (rf-heap +ℕ rg-heap)
            assoc-eq = +-assoc (next-heap-ref alloc) rf-heap rg-heap
            suc-+-eq : suc (next-heap-ref alloc +ℕ (rf-heap +ℕ rg-heap)) ≡
                       next-heap-ref alloc +ℕ req-pair-heap
            suc-+-eq = sym (+-suc (next-heap-ref alloc) (rf-heap +ℕ rg-heap))
        in ≤-trans (s≤s (≤-trans chain (≤-reflexive assoc-eq)))
                   (≤-reflexive suc-+-eq)
        where open import Data.Nat.Properties using (≤-reflexive)

      -- slot-monotone-pair: alloc.next-slot ≤ alloc-final.next-slot
      -- = alloc-after-g.next-slot. Chain: alloc → alloc-after-scratch
      -- (definitional +4) → result-f.final-alloc (via f's slot-monotone)
      -- = alloc-for-g → result-g.final-alloc (via g's slot-monotone) =
      -- alloc-after-g.
      slot-monotone-pair : next-slot alloc ≤ next-slot alloc-final
      slot-monotone-pair =
        ≤-trans (subst (next-slot alloc ≤_) f-start≡+4
                  (≤-trans (n≤1+n backup-slot)
                    (≤-trans (n≤1+n fst-stash)
                      (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash)))))
                (≤-trans (IRResultAWF.slot-monotone result-f)
                         (IRResultAWF.slot-monotone result-g))

      -- alloc-final.next-heap-ref ≥ alloc.next-heap-ref:
      -- alloc.next-heap-ref ≤ next-heap-ref result-f.final-alloc (f.heap-monotone)
      -- ≤ next-heap-ref result-g.final-alloc (g.heap-monotone, since
      --   alloc-for-g.next-heap-ref = next-heap-ref result-f.final-alloc)
      -- ≤ suc (next-heap-ref alloc-after-g) = next-heap-ref alloc-final
      heap-mono : next-heap-ref alloc ≤ next-heap-ref alloc-final
      heap-mono =
        ≤-trans (IRResultAWF.heap-monotone result-f)
          (≤-trans (IRResultAWF.heap-monotone result-g)
                   (n≤1+n (next-heap-ref alloc-after-g)))
