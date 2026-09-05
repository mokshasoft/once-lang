-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairAllocWF
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

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.PairAllocWF (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-identityʳ; m≤n+m; m≤n⊔m; m≤m⊔n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧ᴵ; sem-pair)
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
-- PairAllocWF Implementation
------------------------------------------------------------------------

module PairAllocWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
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
    using (ValidAtWF; IRResultAWF; ResultPlace; at-loc; valid-pair-wf;
           RecDispatcherWF; InputPlace; in-at-loc; Place; AtStorage; mk-IRResultAWF-via-bump;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-frontier-advance)

  ----------------------------------------------------------------------
  -- run-pair-heap: emits the alloc-heap-based trace described above.
  ----------------------------------------------------------------------

  run-pair-heap : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR A C)
    (rec-wf : RecDispatcherWF (ir-size (⟨ f , g ⟩ Heap)))
    (x : ⟦ A ⟧ᴵ) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF Heap (⟨ f , g ⟩ Heap) x s alloc
  run-pair-heap {A} {B} {C} mIn f g rec-wf x input-loc s alloc
                input-valid-wf input-before not-halted rdi-eq =
    -- Plan 0.17: use mk-IRResultAWF-via-bump smart constructor.
    -- Producer-side fields stay at `alloc-final` (local shape);
    -- the helper transports proofs to `apply-bump pair-bump alloc`
    -- via the `pair-bump-eq` bridge (SMP.!! for now — the bridge
    -- shape itself doesn't add proof obligations beyond what
    -- alloc-correct-pair-heap already discharges).
    mk-IRResultAWF-via-bump
      s-final
      alloc-final
      pair-heap-trace
      pair-bump
      pair-bump-eq
      SMP.!!  -- trace-is-ir-to-trace (Pattern 1)
      refl    -- trace-correct (s-final defined by exec-trace)
      (TraceEvaluator.exec-alloc-eq trace-eval)  -- alloc-correct-local
      (at-loc pair-loc pair-valid-final pair-before-final
              pair-rax-eq pair-valid-cont pair-before-cont)
      (TraceEvaluator.halted-preserved trace-eval not-halted)
      (TraceEvaluator.mem-preserved-before trace-eval)
      (TraceEvaluator.trace-wf trace-eval)
      (exec-trace-preserves-halted-WF pair-heap-trace)
      (SMP.trace-no-frame-ops-append setup-trace _ _
        (SMP.trace-no-frame-ops-append f-trace _ (IRResultAWF.trace-no-frame-ops result-f)
          (SMP.trace-no-frame-ops-append mid-trace _ _
            (SMP.trace-no-frame-ops-append g-trace _ (IRResultAWF.trace-no-frame-ops result-g)
              _))))
      (record
        { max-slot-written = max-slot-pair
        ; stack-budget = req-pair-stack
        ; bump-fits-stack-budget = pair-bump-fits-stack-budget
        ; max-slot-geq-final = pair-max-slot-geq-final
        ; max-slot-usage-bound = max-slot-usage-bound-pair
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = pair-trace-writes-above
        ; trace-slot-reads-above = pair-trace-slot-reads-above
        ; trace-writes-below = pair-trace-writes-below
        ; trace-slot-reads-below = pair-trace-slot-reads-below
        ; scratch-budget = req-pair-scratch
        ; scratch-bounded = pair-scratch-bounded
        })
      (record
        { heap-budget = req-pair-heap
        ; max-heap-ref-written = next-heap-ref alloc-final
        ; bump-fits-heap-budget = pair-bump-fits-heap-budget
        ; max-heap-ref-geq-final = pair-max-heap-ref-geq-final
        ; max-heap-usage-bound = max-heap-usage-bound-pair
        })
    where
      ------------------------------------------------------------------
      -- Slot layout (scratch only; pair itself is on the heap)
      ------------------------------------------------------------------
      frame = current-frame alloc
      backup-slot = next-slot alloc
      fst-stash   = suc backup-slot
      snd-stash   = suc fst-stash
      pair-stash  = suc snd-stash
      f-start     = suc pair-stash    -- = next-slot alloc + pair-heap-overhead

      -- Number of scratch slots reserved before f runs (heap-mode):
      -- backup + fst-stash + snd-stash + pair-stash. The pair value
      -- itself lives on the heap, so unlike PairStackWF's pair-overhead
      -- (which includes the pair's stack-resident pointers) this
      -- counts only scratch.
      pair-heap-overhead : ℕ
      pair-heap-overhead = 4

      -- Plan 0.14: phrased as `next-slot alloc + pair-heap-overhead`
      -- so alloc-after-scratch is definitionally equal to the output
      -- of `instr-alloc-stack pair-heap-overhead` at the end of
      -- setup-trace.
      alloc-after-scratch : AllocState {FS}
      alloc-after-scratch = record alloc { next-slot = next-slot alloc +ℕ pair-heap-overhead }

      ------------------------------------------------------------------
      -- Trace phases — named so each phase's proofs can target the
      -- correct intermediate state without re-deriving exec-trace
      -- decompositions.
      ------------------------------------------------------------------
      -- Plan 0.14: setup ends with `instr-alloc-stack pair-heap-overhead` so the
      -- runtime next-slot bumps to match `alloc-after-scratch` (= the
      -- construction-time alloc passed to f's rec-wf). Eliminates the
      -- runtime/construction-time alignment story that PairStackWF had to
      -- thread by hand. See [[alloc-construction-vs-runtime]].
      setup-trace : AbstractTrace
      setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ instr-alloc-stack pair-heap-overhead ∷ []

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
      --   instr-alloc-stack touches nothing in the LocState (0.63).
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
            s₃      = proj₁ (exec-abstract (instr-alloc-stack pair-heap-overhead) s₂ alloc₂)
            -- instr-alloc-stack changes nothing in the LocState, leaving
            -- input1 / input2 / output untouched (definitional).
            alloc-stack-preserves : readReg (regs s₃) Input1 ≡ readReg (regs s₂) Input1
            alloc-stack-preserves = refl
            d1 : exec-trace setup-trace s alloc ≡
                 exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-heap-overhead ∷ []) s₁ alloc₁
            d1 = exec-trace-cons mov-to-output _ s alloc not-halted
            d2 : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-heap-overhead ∷ []) s₁ alloc₁ ≡
                 exec-trace (instr-alloc-stack pair-heap-overhead ∷ []) s₂ alloc₂
            d2 = exec-trace-cons (store-at-slot backup-slot) _ s₁ alloc₁ not-halted₁
            d3 : exec-trace (instr-alloc-stack pair-heap-overhead ∷ []) s₂ alloc₂ ≡
                 exec-abstract (instr-alloc-stack pair-heap-overhead) s₂ alloc₂
            d3 = exec-trace-single (instr-alloc-stack pair-heap-overhead) s₂ alloc₂ not-halted₂
            s-eq : s-after-setup ≡ s₃
            s-eq = cong proj₁ (trans d1 (trans d2 d3))
        in trans (cong (λ st → readReg (regs st) Input1) s-eq)
                 (trans alloc-stack-preserves
                   (trans store-preserves
                     (trans mov-preserves rdi-eq)))

      -- f-start ≡ next-slot alloc + 4 propositionally. `4 + n` reduces
      -- definitionally to suc(suc(suc(suc n))) = f-start (when
      -- n = next-slot alloc); add `+-comm` to swap.
      f-start≡+4 : f-start ≡ next-slot alloc +ℕ pair-heap-overhead
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
      -- doesn't touch them. instr-alloc-stack touches no LocState field
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
            -- instr-alloc-stack changes no LocState field, so stack/heap
            -- memory is preserved.
            s₃      = proj₁ (exec-abstract (instr-alloc-stack pair-heap-overhead) s₂ alloc₂)
            alloc-stack-mem : readLoc s₃ loc ≡ readLoc s₂ loc
            alloc-stack-mem = ExecLemmas.readLoc-stackMem-eq s₃ s₂ loc refl refl
            d1 : exec-trace setup-trace s alloc ≡
                 exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-heap-overhead ∷ []) s₁ alloc₁
            d1 = exec-trace-cons mov-to-output _ s alloc not-halted
            d2 : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-heap-overhead ∷ []) s₁ alloc₁ ≡
                 exec-trace (instr-alloc-stack pair-heap-overhead ∷ []) s₂ alloc₂
            d2 = exec-trace-cons (store-at-slot backup-slot) _ s₁ alloc₁ not-halted₁
            d3 : exec-trace (instr-alloc-stack pair-heap-overhead ∷ []) s₂ alloc₂ ≡
                 exec-abstract (instr-alloc-stack pair-heap-overhead) s₂ alloc₂
            d3 = exec-trace-single (instr-alloc-stack pair-heap-overhead) s₂ alloc₂ not-halted₂
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
      -- Stage F: the four memory facts are now bundled as an `InputPlace`.
      -- Stage F destinations: each sub-IR's result crosses an IR boundary, so
      -- it goes to a caller-owned STACK slot — the frontier each sub-IR starts
      -- from. The pair RECORD's own layout (which cells hold what) is a stage-G
      -- decision, so these are the component destinations, not record offsets.
      -- Not yet binding — see `RecDispatcherWF`.
      f-dest : Place
      f-dest = AtStorage (AtStack (current-frame alloc) (next-slot alloc-after-scratch))

      f-exec = rec-wf mIn f (⟨,⟩-f-smaller f g {Heap}) x s-after-setup alloc-after-scratch
                 (in-at-loc input-loc input-valid-wf-at-f-start input-before-at-f-start
                            rdi-eq-after-setup)
                 f-dest not-halted-after-setup
      result-f = proj₂ f-exec
      f-trace = IRResultAWF.trace result-f

      -- Plan 0.14: s-after-f / alloc-after-f are the RUNTIME values
      -- after exec-trace f-trace from (s-after-setup, alloc-after-scratch).
      -- result-f.final-state ≡ s-after-f via trace-correct; result-f.final-alloc
      -- is a construction-time bookkeeping alloc that may differ from the
      -- runtime alloc on slot/heap-ref dimensions. Bridge via monotone
      -- lemmas where needed. See [[alloc-construction-vs-runtime]] and the
      -- PairStackWF stage-A/B pattern.
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
            s₃ = proj₁ (exec-abstract (instr-alloc-stack pair-heap-overhead) s₂ alloc₂)
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
                 exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-heap-overhead ∷ []) s₁ alloc₁
            d1 = exec-trace-cons mov-to-output _ s alloc not-halted
            d2 : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-heap-overhead ∷ []) s₁ alloc₁ ≡
                 exec-trace (instr-alloc-stack pair-heap-overhead ∷ []) s₂ alloc₂
            d2 = exec-trace-cons (store-at-slot backup-slot) _ s₁ alloc₁ not-halted₁
            d3 : exec-trace (instr-alloc-stack pair-heap-overhead ∷ []) s₂ alloc₂ ≡
                 exec-abstract (instr-alloc-stack pair-heap-overhead) s₂ alloc₂
            d3 = exec-trace-single (instr-alloc-stack pair-heap-overhead) s₂ alloc₂ not-halted₂
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
      -- Construction-time alloc passed to g-exec. PairStackWF's pattern:
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
      g-dest : Place
      g-dest = AtStorage (AtStack (current-frame alloc) (next-slot alloc-for-g))

      g-exec = rec-wf mIn g (⟨,⟩-g-smaller f g {Heap}) x
                 s-after-middle alloc-for-g
                 (in-at-loc input-loc input-valid-wf-at-g-start input-before-at-g-start
                            rdi-eq-after-middle)
                 g-dest not-halted-after-middle
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

      -- Plan 0.17 bump declaration: pair-heap's effect on alloc is
      --   scratch (mkBump 4 0)
      --   ∘ f-result.bump
      --   ∘ g-result.bump
      --   ∘ heap-alloc post (mkBump 0 1)
      -- Composed via bump-+. Concrete arithmetic discharged via
      -- pair-bump-eq below.
      pair-bump : AllocBump
      pair-bump = mkBump (4 +ℕ next-slot-delta (IRResultAWF.bump result-f)
                           +ℕ next-slot-delta (IRResultAWF.bump result-g))
                         (next-heap-ref-delta (IRResultAWF.bump result-f)
                           +ℕ next-heap-ref-delta (IRResultAWF.bump result-g)
                           +ℕ 1)

      pair-bump-eq : alloc-final ≡ apply-bump pair-bump alloc
      pair-bump-eq = SMP.!!  -- TODO Plan 0.17 Phase 5: concrete arithmetic bridge

      ------------------------------------------------------------------
      -- alloc-correct discharge for pair-heap-trace.
      --
      -- Strategy: walk through the 5 trace segments via exec-trace-append,
      -- bridging construction-time and runtime alloc states as needed.
      ------------------------------------------------------------------

      rest-after-setup : AbstractTrace
      rest-after-setup = f-trace ++ mid-trace ++ g-trace ++ post-trace

      pair-trace-decomp-1 : exec-trace pair-heap-trace s alloc ≡
                            exec-trace rest-after-setup (proj₁ (exec-trace setup-trace s alloc))
                                                        (proj₂ (exec-trace setup-trace s alloc))
      pair-trace-decomp-1 = SMP.TraceComposition.exec-trace-append {FS} setup-trace rest-after-setup s alloc

      -- Setup-trace produces alloc-after-scratch (the synthetic), propositionally.
      alloc-setup-eq-scratch : proj₂ (exec-trace setup-trace s alloc) ≡ alloc-after-scratch
      alloc-setup-eq-scratch =
        let s₁ʳ = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁ʳ = proj₂ (exec-abstract mov-to-output s alloc)
            not-halted₁ʳ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            s₂ʳ = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            alloc₂ʳ = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            not-halted₂ʳ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ʳ alloc₁ʳ not-halted₁ʳ iph-store-at-slot
            d₀ = exec-trace-cons mov-to-output _ s alloc not-halted
            d₁ = exec-trace-cons (store-at-slot backup-slot) _ s₁ʳ alloc₁ʳ not-halted₁ʳ
            d₂ = exec-trace-single (instr-alloc-stack pair-heap-overhead) s₂ʳ alloc₂ʳ not-halted₂ʳ
        in cong proj₂ (trans d₀ (trans d₁ d₂))

      pair-trace-after-setup-alloc-eq :
        proj₂ (exec-trace pair-heap-trace s alloc) ≡
        proj₂ (exec-trace rest-after-setup s-after-setup alloc-after-scratch)
      pair-trace-after-setup-alloc-eq =
        trans (cong proj₂ pair-trace-decomp-1)
              (cong (λ a → proj₂ (exec-trace rest-after-setup s-after-setup a))
                    alloc-setup-eq-scratch)

      rest-after-f : AbstractTrace
      rest-after-f = mid-trace ++ g-trace ++ post-trace

      f-decomp : exec-trace rest-after-setup s-after-setup alloc-after-scratch ≡
                 exec-trace rest-after-f
                   (proj₁ (exec-trace f-trace s-after-setup alloc-after-scratch))
                   (proj₂ (exec-trace f-trace s-after-setup alloc-after-scratch))
      f-decomp = SMP.TraceComposition.exec-trace-append {FS} f-trace rest-after-f s-after-setup alloc-after-scratch

      pair-trace-after-f-alloc-eq :
        proj₂ (exec-trace pair-heap-trace s alloc) ≡
        proj₂ (exec-trace rest-after-f s-after-f alloc-after-f)
      pair-trace-after-f-alloc-eq =
        trans pair-trace-after-setup-alloc-eq (cong proj₂ f-decomp)

      rest-after-middle : AbstractTrace
      rest-after-middle = g-trace ++ post-trace

      mid-decomp : exec-trace rest-after-f s-after-f alloc-after-f ≡
                   exec-trace rest-after-middle s-after-middle alloc-after-middle
      mid-decomp = SMP.TraceComposition.exec-trace-append {FS} mid-trace rest-after-middle s-after-f alloc-after-f

      pair-trace-after-middle-alloc-eq :
        proj₂ (exec-trace pair-heap-trace s alloc) ≡
        proj₂ (exec-trace rest-after-middle s-after-middle alloc-after-middle)
      pair-trace-after-middle-alloc-eq =
        trans pair-trace-after-f-alloc-eq (cong proj₂ mid-decomp)

      -- Bridge alloc-after-middle ≡ alloc-for-g (so we can apply result-g.alloc-correct).
      alloc-after-middle-eq-after-f : alloc-after-middle ≡ alloc-after-f
      alloc-after-middle-eq-after-f =
        let nh-store = exec-abstract-preserves-halted (store-at-slot fst-stash)
              s-after-f alloc-after-f not-halted-after-f iph-store-at-slot
            d₀ = exec-trace-cons (store-at-slot fst-stash) _ s-after-f alloc-after-f not-halted-after-f
            d₁ = exec-trace-single (restore-input backup-slot)
                   (proj₁ (exec-abstract (store-at-slot fst-stash) s-after-f alloc-after-f))
                   (proj₂ (exec-abstract (store-at-slot fst-stash) s-after-f alloc-after-f))
                   nh-store
            rest-preserves =
              SMP.RecSchemeSemantics.exec-abstract-restore-input-preserves-alloc {FS}
                backup-slot
                (proj₁ (exec-abstract (store-at-slot fst-stash) s-after-f alloc-after-f))
                (proj₂ (exec-abstract (store-at-slot fst-stash) s-after-f alloc-after-f))
        in trans (cong proj₂ (trans d₀ d₁)) rest-preserves

      alloc-for-g-eq-final-f : alloc-for-g ≡ IRResultAWF.final-alloc result-f
      alloc-for-g-eq-final-f =
        cong (λ fr → record (IRResultAWF.final-alloc result-f) { current-frame = fr })
             (sym (IRResultAWF.frame-preserved result-f))

      alloc-after-middle-eq-for-g : alloc-after-middle ≡ alloc-for-g
      alloc-after-middle-eq-for-g =
        trans alloc-after-middle-eq-after-f
              (trans (IRResultAWF.alloc-correct result-f) (sym alloc-for-g-eq-final-f))

      g-decomp : exec-trace rest-after-middle s-after-middle alloc-after-middle ≡
                 exec-trace post-trace
                   (proj₁ (exec-trace g-trace s-after-middle alloc-after-middle))
                   (proj₂ (exec-trace g-trace s-after-middle alloc-after-middle))
      g-decomp = SMP.TraceComposition.exec-trace-append {FS} g-trace post-trace s-after-middle alloc-after-middle

      runtime-state-after-g-eq :
        proj₁ (exec-trace g-trace s-after-middle alloc-after-middle) ≡ s-after-g
      runtime-state-after-g-eq =
        trans (cong (λ a → proj₁ (exec-trace g-trace s-after-middle a)) alloc-after-middle-eq-for-g)
              (IRResultAWF.trace-correct result-g)

      runtime-alloc-after-g-eq-final-g :
        proj₂ (exec-trace g-trace s-after-middle alloc-after-middle) ≡ IRResultAWF.final-alloc result-g
      runtime-alloc-after-g-eq-final-g =
        trans (cong (λ a → proj₂ (exec-trace g-trace s-after-middle a)) alloc-after-middle-eq-for-g)
              (IRResultAWF.alloc-correct result-g)

      pair-trace-after-g-alloc-eq :
        proj₂ (exec-trace pair-heap-trace s alloc) ≡
        proj₂ (exec-trace post-trace s-after-g alloc-after-g)
      pair-trace-after-g-alloc-eq =
        trans (trans pair-trace-after-middle-alloc-eq (cong proj₂ g-decomp))
              (cong₂ (λ st a → proj₂ (exec-trace post-trace st a))
                runtime-state-after-g-eq runtime-alloc-after-g-eq-final-g)

      -- post-trace bumps next-heap-ref by 1 (via instr-alloc-heap 2).
      -- 9 steps; postulated pending dedicated proof analogous to
      -- curry-trace-alloc-correct.
      post-trace-alloc-correct :
        proj₂ (exec-trace post-trace s-after-g alloc-after-g) ≡
          record alloc-after-g { next-heap-ref = suc (next-heap-ref alloc-after-g) }
      post-trace-alloc-correct = SMP.!!

      -- Final: bridge the bumped alloc-after-g to alloc-final (current-frame
      -- match via result-g.frame-preserved; other fields match by def).
      final-bridge-eq :
        record alloc-after-g { next-heap-ref = suc (next-heap-ref alloc-after-g) } ≡ alloc-final
      final-bridge-eq =
        cong (λ fr → record alloc-after-g
                       { current-frame = fr
                       ; next-heap-ref = suc (next-heap-ref alloc-after-g) })
             (IRResultAWF.frame-preserved result-g)

      alloc-correct-pair-heap : proj₂ (exec-trace pair-heap-trace s alloc) ≡ alloc-final
      alloc-correct-pair-heap =
        trans pair-trace-after-g-alloc-eq (trans post-trace-alloc-correct final-bridge-eq)

      ------------------------------------------------------------------
      -- Plan 0.16 TraceEvaluator: bundles the per-step state trajectory.
      -- `exec-alloc-eq` reuses the existing `alloc-correct-pair-heap`
      -- derivation; `trace-wf` and `mem-preserved-before` remain the
      -- two scaffolded semantic obligations. `halted-preserved`
      -- (i.e. the old `not-halted-final`) now derives automatically
      -- from `trace-wf` via `exec-trace-preserves-halted-WF`.
      ------------------------------------------------------------------
      trace-eval : TraceEvaluator pair-heap-trace s alloc
      trace-eval = mk-trace-evaluator
        s-final
        alloc-final
        SMP.!!                       -- trace-wf
        refl                         -- exec-state-eq (definitional)
        alloc-correct-pair-heap      -- exec-alloc-eq (already derived)
        (λ _ _ → SMP.!!)             -- mem-preserved-before

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

      -- pair-loc's ref-id = next-heap-ref alloc-after-g
      -- alloc-final.next-heap-ref = suc (next-heap-ref alloc-after-g)
      -- So the freshness check is `next-heap-ref alloc-after-g < suc(...)`
      -- = ≤-refl. The disjointness lives in the allocator interface
      -- (AbstractInstance); here we just instantiate `heap-before`.
      pair-before-final : BeforeFrontier alloc-final pair-loc
      pair-before-final = heap-before ≤-refl

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

      -- pair-cont-alloc.next-heap-ref = next-heap-ref alloc-final
      -- = suc (next-heap-ref alloc-after-g). Same fact as pair-before-final.
      pair-before-cont : BeforeFrontier pair-cont-alloc pair-loc
      pair-before-cont = heap-before ≤-refl

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

      pair-stash≡+3 : suc pair-stash ≡ next-slot alloc +ℕ pair-heap-overhead
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
                            (next-slot alloc +ℕ pair-heap-overhead) +ℕ rf-stack
            f-final-bound = IRResultAWF.slot-stays-in-budget result-f
            step : next-slot (IRResultAWF.final-alloc result-f) +ℕ rg-stack ≤
                   ((next-slot alloc +ℕ pair-heap-overhead) +ℕ rf-stack) +ℕ rg-stack
            step = +-monoˡ-≤ rg-stack f-final-bound
            -- ((next-slot alloc + 4) + rf-stack) + rg-stack
            --   = next-slot alloc + (4 + rf-stack + rg-stack)
            --   = next-slot alloc + req-pair-stack.
            req-pair-stack-eq : ((next-slot alloc +ℕ pair-heap-overhead) +ℕ rf-stack) +ℕ rg-stack ≡
                                next-slot alloc +ℕ req-pair-stack
            req-pair-stack-eq =
              trans (+-assoc (next-slot alloc +ℕ pair-heap-overhead) rf-stack rg-stack)
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
      ------------------------------------------------------------------
      -- Trace-write/read region bookkeeping.
      ------------------------------------------------------------------
      next-slot≤alloc-after-scratch : next-slot alloc ≤ next-slot alloc-after-scratch
      next-slot≤alloc-after-scratch =
        subst (next-slot alloc ≤_) f-start≡+4 (≤-trans (n≤1+n backup-slot)
          (≤-trans (n≤1+n fst-stash)
            (≤-trans (n≤1+n snd-stash) (n≤1+n pair-stash))))

      next-slot≤alloc-for-g : next-slot alloc ≤ next-slot alloc-for-g
      next-slot≤alloc-for-g = ≤-trans next-slot≤alloc-after-scratch
                                       (IRResultAWF.slot-monotone result-f)

      setup-twa : SMP.TraceWritesAbove (next-slot alloc) setup-trace
      setup-twa = ≤-refl , tt

      mid-twa : SMP.TraceWritesAbove (next-slot alloc) mid-trace
      mid-twa = n≤1+n (next-slot alloc) , tt

      post-twa : SMP.TraceWritesAbove (next-slot alloc) post-trace
      post-twa =
        ≤-trans (n≤1+n backup-slot) (n≤1+n fst-stash) ,  -- next-slot alloc ≤ snd-stash
        ≤-trans (n≤1+n backup-slot)
          (≤-trans (n≤1+n fst-stash) (n≤1+n snd-stash)) ,  -- next-slot alloc ≤ pair-stash
        tt

      -- Named tails for explicit append-chains.
      rest-from-f : AbstractTrace
      rest-from-f = mid-trace ++ g-trace ++ post-trace
      rest-from-mid : AbstractTrace
      rest-from-mid = g-trace ++ post-trace

      pair-trace-writes-above : SMP.TraceWritesAbove (next-slot alloc) pair-heap-trace
      pair-trace-writes-above =
        SMP.trace-writes-above-append (next-slot alloc) setup-trace
          (f-trace ++ rest-from-f) setup-twa
          (SMP.trace-writes-above-append (next-slot alloc) f-trace rest-from-f
            (SMP.trace-writes-above-mono (next-slot alloc) (next-slot alloc-after-scratch) f-trace
              next-slot≤alloc-after-scratch (IRResultAWF.trace-writes-above result-f))
            (SMP.trace-writes-above-append (next-slot alloc) mid-trace rest-from-mid mid-twa
              (SMP.trace-writes-above-append (next-slot alloc) g-trace post-trace
                (SMP.trace-writes-above-mono (next-slot alloc) (next-slot alloc-for-g) g-trace
                  next-slot≤alloc-for-g (IRResultAWF.trace-writes-above result-g))
                post-twa)))

      -- trace-slot-reads-above: pair-heap-trace's slot reads come from
      -- load-from-slot (fst-stash, snd-stash, pair-stash), restore-input
      -- (backup-slot), and whatever f/g read. All ≥ next-slot alloc.
      setup-tsra : SMP.TraceSlotReadsAbove (next-slot alloc) setup-trace
      setup-tsra = tt  -- setup has no slot reads (mov, store, alloc-stack)

      mid-tsra : SMP.TraceSlotReadsAbove (next-slot alloc) mid-trace
      mid-tsra = ≤-refl , tt  -- restore-input backup-slot reads backup-slot = next-slot alloc

      post-tsra : SMP.TraceSlotReadsAbove (next-slot alloc) post-trace
      post-tsra =
        ≤-trans (n≤1+n backup-slot) ≤-refl ,       -- load-from-slot fst-stash
        ≤-trans (n≤1+n backup-slot)
          (≤-trans (n≤1+n fst-stash) ≤-refl) ,     -- load-from-slot snd-stash
        ≤-trans (n≤1+n backup-slot)
          (≤-trans (n≤1+n fst-stash)
            (≤-trans (n≤1+n snd-stash) ≤-refl)) ,  -- load-from-slot pair-stash
        tt

      pair-trace-slot-reads-above : SMP.TraceSlotReadsAbove (next-slot alloc) pair-heap-trace
      pair-trace-slot-reads-above =
        SMP.trace-slot-reads-above-append (next-slot alloc) setup-trace
          (f-trace ++ rest-from-f) setup-tsra
          (SMP.trace-slot-reads-above-append (next-slot alloc) f-trace rest-from-f
            (SMP.trace-slot-reads-above-mono (next-slot alloc) (next-slot alloc-after-scratch) f-trace
              next-slot≤alloc-after-scratch (IRResultAWF.trace-slot-reads-above result-f))
            (SMP.trace-slot-reads-above-append (next-slot alloc) mid-trace rest-from-mid mid-tsra
              (SMP.trace-slot-reads-above-append (next-slot alloc) g-trace post-trace
                (SMP.trace-slot-reads-above-mono (next-slot alloc) (next-slot alloc-for-g) g-trace
                  next-slot≤alloc-for-g (IRResultAWF.trace-slot-reads-above result-g))
                post-tsra)))

      -- trace-writes-below max-slot-pair: every slot write in pair-heap-trace
      -- is at a slot < max-slot-pair.
      max-slot-pair-bound-on-stashes :
        ∀ {k} → k ≤ pair-stash → k < max-slot-pair
      max-slot-pair-bound-on-stashes k≤pair =
        ≤-trans (s≤s k≤pair)
          (≤-trans (m≤m⊔n (suc pair-stash) (IRResultAWF.max-slot-written result-f))
                   (m≤m⊔n (suc pair-stash ⊔ IRResultAWF.max-slot-written result-f)
                          (IRResultAWF.max-slot-written result-g)))

      setup-twb : SMP.TraceWritesBelow max-slot-pair setup-trace
      setup-twb =
        -- store-at-slot backup-slot: backup-slot < max-slot-pair
        max-slot-pair-bound-on-stashes
          (≤-trans (n≤1+n backup-slot)
            (≤-trans (n≤1+n fst-stash) (n≤1+n snd-stash))) ,
        tt

      mid-twb : SMP.TraceWritesBelow max-slot-pair mid-trace
      mid-twb =
        -- store-at-slot fst-stash: fst-stash < max-slot-pair
        max-slot-pair-bound-on-stashes
          (≤-trans (n≤1+n fst-stash) (n≤1+n snd-stash)) ,
        tt

      post-twb : SMP.TraceWritesBelow max-slot-pair post-trace
      post-twb =
        -- store-at-slot snd-stash: snd-stash < max-slot-pair
        max-slot-pair-bound-on-stashes (n≤1+n snd-stash) ,
        -- store-at-slot pair-stash: pair-stash < max-slot-pair
        max-slot-pair-bound-on-stashes ≤-refl ,
        tt

      pair-trace-writes-below : SMP.TraceWritesBelow max-slot-pair pair-heap-trace
      pair-trace-writes-below =
        SMP.trace-writes-below-append max-slot-pair setup-trace
          (f-trace ++ rest-from-f) setup-twb
          (SMP.trace-writes-below-append max-slot-pair f-trace rest-from-f
            (SMP.trace-writes-below-mono (IRResultAWF.max-slot-written result-f) max-slot-pair f-trace
              (≤-trans (m≤n⊔m (suc pair-stash) (IRResultAWF.max-slot-written result-f))
                       (m≤m⊔n (suc pair-stash ⊔ IRResultAWF.max-slot-written result-f)
                              (IRResultAWF.max-slot-written result-g)))
              (IRResultAWF.trace-writes-below result-f))
            (SMP.trace-writes-below-append max-slot-pair mid-trace rest-from-mid mid-twb
              (SMP.trace-writes-below-append max-slot-pair g-trace post-trace
                (SMP.trace-writes-below-mono (IRResultAWF.max-slot-written result-g) max-slot-pair g-trace
                  (m≤n⊔m (suc pair-stash ⊔ IRResultAWF.max-slot-written result-f)
                         (IRResultAWF.max-slot-written result-g))
                  (IRResultAWF.trace-writes-below result-g))
                post-twb)))

      setup-tsrb : SMP.TraceSlotReadsBelow max-slot-pair setup-trace
      setup-tsrb = tt

      mid-tsrb : SMP.TraceSlotReadsBelow max-slot-pair mid-trace
      mid-tsrb =
        max-slot-pair-bound-on-stashes
          (≤-trans (n≤1+n backup-slot)
            (≤-trans (n≤1+n fst-stash) (n≤1+n snd-stash))) ,  -- backup-slot ≤ pair-stash
        tt

      post-tsrb : SMP.TraceSlotReadsBelow max-slot-pair post-trace
      post-tsrb =
        max-slot-pair-bound-on-stashes
          (≤-trans (n≤1+n fst-stash) (n≤1+n snd-stash)) ,  -- fst-stash ≤ pair-stash
        max-slot-pair-bound-on-stashes (n≤1+n snd-stash) ,  -- snd-stash ≤ pair-stash
        max-slot-pair-bound-on-stashes ≤-refl ,             -- pair-stash ≤ pair-stash
        tt

      pair-trace-slot-reads-below : SMP.TraceSlotReadsBelow max-slot-pair pair-heap-trace
      pair-trace-slot-reads-below =
        SMP.trace-slot-reads-below-append max-slot-pair setup-trace
          (f-trace ++ rest-from-f) setup-tsrb
          (SMP.trace-slot-reads-below-append max-slot-pair f-trace rest-from-f
            (SMP.trace-slot-reads-below-mono (IRResultAWF.max-slot-written result-f) max-slot-pair f-trace
              (≤-trans (m≤n⊔m (suc pair-stash) (IRResultAWF.max-slot-written result-f))
                       (m≤m⊔n (suc pair-stash ⊔ IRResultAWF.max-slot-written result-f)
                              (IRResultAWF.max-slot-written result-g)))
              (IRResultAWF.trace-slot-reads-below result-f))
            (SMP.trace-slot-reads-below-append max-slot-pair mid-trace rest-from-mid mid-tsrb
              (SMP.trace-slot-reads-below-append max-slot-pair g-trace post-trace
                (SMP.trace-slot-reads-below-mono (IRResultAWF.max-slot-written result-g) max-slot-pair g-trace
                  (m≤n⊔m (suc pair-stash ⊔ IRResultAWF.max-slot-written result-f)
                         (IRResultAWF.max-slot-written result-g))
                  (IRResultAWF.trace-slot-reads-below result-g))
                post-tsrb)))

      -- scratch-bounded: max-slot-pair ≤ next-slot alloc-after-g + req-pair-scratch.
      -- Each ⊔-component:
      --   suc pair-stash = next-slot alloc + 4 ≤ next-slot alloc-after-g + 4
      --                   (slot-monotone-pair via slot-monotone of f then g)
      --                   ≤ next-slot alloc-after-g + req-pair-scratch (4 ≤ 4 + rf + rg)
      --   max-slot-written result-f ≤ next-slot alloc-for-g + rf-scratch
      --                             ≤ next-slot alloc-after-g + rf-scratch
      --                             (result-g.slot-monotone)
      --                             ≤ next-slot alloc-after-g + req-pair-scratch
      --   max-slot-written result-g ≤ next-slot alloc-after-g + rg-scratch
      --                             ≤ next-slot alloc-after-g + req-pair-scratch
      scratch-bounded-pair : max-slot-pair ≤ next-slot alloc-after-g +ℕ req-pair-scratch
      scratch-bounded-pair = ⊔-lub (⊔-lub bound-pair-stash bound-f) bound-g
        where
          open import Data.Nat.Properties using (≤-reflexive)
          -- next-slot alloc ≤ next-slot alloc-after-g
          slot-mono-to-g : next-slot alloc-after-scratch ≤ next-slot alloc-after-g
          slot-mono-to-g = ≤-trans (IRResultAWF.slot-monotone result-f)
                                   (IRResultAWF.slot-monotone result-g)
          bound-pair-stash : suc pair-stash ≤ next-slot alloc-after-g +ℕ req-pair-scratch
          bound-pair-stash =
            -- suc pair-stash = next-slot alloc + 4 (propositionally via f-start≡+4).
            -- next-slot alloc + 4 = next-slot alloc-after-scratch (definitionally).
            -- ≤ next-slot alloc-after-g (slot-mono-to-g).
            -- ≤ next-slot alloc-after-g + req-pair-scratch (m≤m+n).
            ≤-trans (≤-reflexive f-start≡+4)
              (≤-trans slot-mono-to-g (m≤m+n (next-slot alloc-after-g) req-pair-scratch))
          rf-≤-req : rf-scratch ≤ req-pair-scratch
          rf-≤-req = ≤-trans (m≤n+m rf-scratch 4) (m≤m+n (4 +ℕ rf-scratch) rg-scratch)
          rg-≤-req : rg-scratch ≤ req-pair-scratch
          rg-≤-req = ≤-trans (m≤n+m rg-scratch (4 +ℕ rf-scratch)) (≤-reflexive refl)
          bound-f : IRResultAWF.max-slot-written result-f ≤ next-slot alloc-after-g +ℕ req-pair-scratch
          bound-f =
            ≤-trans (IRResultAWF.scratch-bounded result-f)
              (≤-trans (+-monoˡ-≤ rf-scratch (IRResultAWF.slot-monotone result-g))
                       (+-monoʳ-≤ (next-slot alloc-after-g) rf-≤-req))
          bound-g : IRResultAWF.max-slot-written result-g ≤ next-slot alloc-after-g +ℕ req-pair-scratch
          bound-g =
            ≤-trans (IRResultAWF.scratch-bounded result-g)
              (+-monoʳ-≤ (next-slot alloc-after-g) rg-≤-req)

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

      ------------------------------------------------------------------
      -- Plan 0.17.1: discharge the new IRStackBudget / IRHeapBudget
      -- fields. Each rests on `pair-bump-eq` (the alloc-final ≡
      -- apply-bump pair-bump alloc bridge); arithmetic chains into the
      -- existing pair-* lemmas above.
      ------------------------------------------------------------------

      pair-bump-fits-stack-budget : next-slot-delta pair-bump ≤ req-pair-stack
      pair-bump-fits-stack-budget =
        +-mono-≤ (+-mono-≤ (≤-refl {x = 4})
                            (IRResultAWF.bump-fits-stack-budget result-f))
                  (IRResultAWF.bump-fits-stack-budget result-g)
        where open import Data.Nat.Properties using (+-mono-≤)

      pair-max-slot-geq-final :
        next-slot-delta pair-bump +ℕ next-slot alloc ≤ max-slot-pair
      pair-max-slot-geq-final =
        subst (λ a → next-slot a ≤ max-slot-pair)
              pair-bump-eq
              max-slot-geq-final-pair

      pair-scratch-bounded :
        max-slot-pair ≤ next-slot (apply-bump pair-bump alloc) +ℕ req-pair-scratch
      pair-scratch-bounded =
        subst (λ a → max-slot-pair ≤ next-slot a +ℕ req-pair-scratch)
              pair-bump-eq
              scratch-bounded-pair

      pair-bump-fits-heap-budget : next-heap-ref-delta pair-bump ≤ req-pair-heap
      pair-bump-fits-heap-budget =
        ≤-trans
          (+-monoˡ-≤ 1 (+-mono-≤ (IRResultAWF.bump-fits-heap-budget result-f)
                                  (IRResultAWF.bump-fits-heap-budget result-g)))
          (≤-reflexive (+-comm (rf-heap +ℕ rg-heap) 1))
        where open import Data.Nat.Properties using (+-mono-≤; ≤-reflexive)

      pair-max-heap-ref-geq-final :
        next-heap-ref-delta pair-bump +ℕ next-heap-ref alloc ≤ next-heap-ref alloc-final
      pair-max-heap-ref-geq-final =
        subst (λ a → next-heap-ref-delta pair-bump +ℕ next-heap-ref alloc ≤ next-heap-ref a)
              (sym pair-bump-eq)
              ≤-refl
