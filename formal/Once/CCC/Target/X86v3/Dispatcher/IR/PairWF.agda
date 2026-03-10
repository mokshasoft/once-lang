------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.PairWF
--
-- Pair IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
--
-- Uses LINEAR capacity formula: pair-slots * ir-size
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.PairWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n; _<?_; _≤?_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; ≤-antisym; m≤m+n; m≤n+m; m<m+n; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; *-monoʳ-≤; m≤m*n; *-distribˡ-+; *-suc; n≤1+n; <⇒≢; ≮⇒≥; <⇒≤; <⇒≱; ≤∧≢⇒<; <-≤-trans; ≰⇒>)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; _∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; subst; module ≡-Reasoning)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Pair implementation
------------------------------------------------------------------------

module PairWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-pair-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-frontier-advance; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-with-bf-transfer;
           at-frontier-neq-before-wf; suc-frontier-neq-before-wf;
           validityWF-mem-preserved-excluding)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import lemmas
  open import Once.CCC.Target.X86v3.Dispatcher.DispatcherArithmeticLemma
    using (suc<+2; compose-f-cap; compose-g-cap; pair-slot-bounded-lemma; pair-alloc-fits)
  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap; at-frontier-before-pair)
  open ExecLemmas {FS}

  -- Import write operations
  open import Once.CCC.Target.X86v3.Dispatcher.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import bf-same-frame-slot from BFTransfer module
  open import Once.CCC.Target.X86v3.Dispatcher.IR.ApplyWF
  open BFTransfer {FS}
    using (bf-same-frame-slot)

  ------------------------------------------------------------------------
  -- run-pair: Pair IR with Trace-Defined Final State
  --
  -- KEY INSIGHT: Define s-final BY the trace execution, not semantically.
  -- This makes trace-correct trivial (refl), then we prove properties about
  -- this trace-defined state.
  --
  -- For pair, we define:
  --   s-final = proj₁ (exec-trace pair-trace s alloc)
  -- Then prove fst-ptr, snd-ptr, validity, etc. about this state.
  ------------------------------------------------------------------------

  run-pair : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR A C) (m : AllocMode)
    (rec-wf : RecDispatcherWF (ir-size (⟨ f , g ⟩ Heap)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (⟨ f , g ⟩ m) ≤ frame-capacity alloc →
    IRResultAWF m (⟨ f , g ⟩ m) x s alloc

  run-pair {A} {B} {C} mIn f g m rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc₃
      ; trace = pair-trace
      ; trace-correct = refl  -- TRIVIAL: s-final is DEFINED by the trace
      ; result-valid-wf = pair-valid-wf-final
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-pair
      ; heap-monotone = heap-monotone-pair
      ; heap-preserved = heap-preserved-pair
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-pair
      ; reclaimable-slot = pair-reclaim
      ; reclaim-monotone = pair-reclaim-monotone
      ; reclaim-bounded = pair-reclaim-bounded
      ; reclaim-preserves-result = pair-reclaim-preserves
      ; reclaim-preserves-validity = pair-reclaim-preserves-validity
      ; reclaim-size-bound = pair-reclaim-size-bound
      ; frontier-slot-stable = pair-frontier-stable
      ; trace-writes-above = pair-trace-writes-above
      ; trace-slot-reads-above = pair-trace-slot-reads-above
      ; trace-writes-below = pair-trace-writes-below
      ; trace-slot-reads-below = pair-trace-slot-reads-below
      ; trace-preserves-capacity = pair-trace-preserves-capacity
      }
    where
      -- Stack requirement abbreviations
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-pair = ir-stack-requirement (⟨ f , g ⟩ m)
      ps : ℕ
      ps = 2

      ps≥2 : 2 ≤ ps
      ps≥2 = ≤-refl

      ps≥1 : 1 ≤ ps
      ps≥1 = s≤s z≤n

      ------------------------------------------------------------------------
      -- Capacity derivations (same as run-pair)
      ------------------------------------------------------------------------

      backup-slot : ℕ
      backup-slot = next-slot alloc

      alloc-after-backup : AllocState {FS}
      alloc-after-backup = record alloc { next-slot = suc (next-slot alloc) }

      combined-cap-expanded : (next-slot alloc +ℕ 1) +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc
      combined-cap-expanded = ⟨,⟩-capacity-for-pair f g m (next-slot alloc) (frame-capacity alloc) combined-cap

      slot+1≡suc-slot : next-slot alloc +ℕ 1 ≡ suc (next-slot alloc)
      slot+1≡suc-slot = +-comm (next-slot alloc) 1

      combined-cap-suc : suc (next-slot alloc) +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc
      combined-cap-suc = subst (λ x → x +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc) slot+1≡suc-slot combined-cap-expanded

      combined-cap-reassoc : (suc (next-slot alloc) +ℕ rf) +ℕ (rg +ℕ ps) ≤ frame-capacity alloc
      combined-cap-reassoc = subst (_≤ frame-capacity alloc) (+-assoc (suc (next-slot alloc) +ℕ rf) rg ps) combined-cap-suc

      combined-cap-f : suc (next-slot alloc) +ℕ rf ≤ frame-capacity alloc
      combined-cap-f = ≤-trans (m≤m+n (suc (next-slot alloc) +ℕ rf) (rg +ℕ ps)) combined-cap-reassoc

      input-before-after-backup : BeforeFrontier alloc-after-backup input-loc
      input-before-after-backup = frontier-monotone alloc alloc-after-backup refl (n≤1+n (next-slot alloc)) ≤-refl input-loc input-before

      bf-to-after-backup : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-after-backup loc
      bf-to-after-backup loc bf = frontier-monotone alloc alloc-after-backup refl (n≤1+n (next-slot alloc)) ≤-refl loc bf

      input-valid-wf-after-backup : ValidAtWF mIn alloc-after-backup x input-loc s
      input-valid-wf-after-backup = validityWF-frontier-advance x input-loc s refl (n≤1+n (next-slot alloc)) ≤-refl input-valid-wf

      ------------------------------------------------------------------------
      -- Run f via recursive dispatch
      ------------------------------------------------------------------------

      f-exec-result : ∃[ mOut ] IRResultAWF mOut f x s alloc-after-backup
      f-exec-result = rec-wf mIn f (⟨,⟩-f-smaller f g {m}) x input-loc s alloc-after-backup input-valid-wf-after-backup input-before-after-backup not-halted rdi-eq combined-cap-f
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      fst-loc = IRResultAWF.result-loc result-f

      ------------------------------------------------------------------------
      -- Reclaim after f
      ------------------------------------------------------------------------
      reclaim-f = IRResultAWF.reclaimable-slot result-f

      reclaim-f-bound : reclaim-f ≤ suc (next-slot alloc) +ℕ rf
      reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

      reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
      reclaim-f-fits = ≤-trans reclaim-f-bound combined-cap-f

      reclaim-f-above-backup : suc backup-slot ≤ reclaim-f
      reclaim-f-above-backup = IRResultAWF.reclaim-monotone result-f

      alloc₁-reclaimed : AllocState {FS}
      alloc₁-reclaimed = record alloc { next-slot = reclaim-f }

      ------------------------------------------------------------------------
      -- Capacity for g
      ------------------------------------------------------------------------

      combined-cap-g : reclaim-f +ℕ rg ≤ frame-capacity alloc
      combined-cap-g = ≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                         (≤-trans (m≤m+n (suc (next-slot alloc) +ℕ rf +ℕ rg) ps) combined-cap-suc)

      input-before₁-reclaimed : BeforeFrontier alloc₁-reclaimed input-loc
      input-before₁-reclaimed = frontier-monotone alloc alloc₁-reclaimed
                                  refl
                                  (≤-trans (n≤1+n (next-slot alloc)) reclaim-f-above-backup)
                                  ≤-refl
                                  input-loc input-before

      input-valid-wf-s1 : ValidAtWF mIn alloc x input-loc s₁
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s s₁
                            input-before
                            (λ loc bf → IRResultAWF.mem-preserved-before result-f loc (bf-to-after-backup loc bf))
                            input-valid-wf

      input-valid-wf₁-reclaimed : ValidAtWF mIn alloc₁-reclaimed x input-loc s₁
      input-valid-wf₁-reclaimed = validityWF-frontier-advance x input-loc s₁
                                    refl
                                    (≤-trans (n≤1+n (next-slot alloc)) (IRResultAWF.reclaim-monotone result-f))
                                    ≤-refl
                                    input-valid-wf-s1

      s₁' = record s₁ { regs = writeReg (regs s₁) Input input-loc }
      rdi-eq₁ : readReg (regs s₁') Input ≡ input-loc
      rdi-eq₁ = writeReg-same (regs s₁) Input input-loc

      input-valid-wf₁' : ValidAtWF mIn alloc₁-reclaimed x input-loc s₁'
      input-valid-wf₁' = validityWF-mem-only x input-loc s₁ s₁' refl refl input-valid-wf₁-reclaimed

      ------------------------------------------------------------------------
      -- Run g via recursive dispatch
      ------------------------------------------------------------------------

      g-exec-result : ∃[ mOut ] IRResultAWF mOut g x s₁' alloc₁-reclaimed
      g-exec-result = rec-wf mIn g (⟨,⟩-g-smaller f g {m}) x input-loc s₁' alloc₁-reclaimed
                        input-valid-wf₁' input-before₁-reclaimed (IRResultAWF.not-halted result-f) rdi-eq₁ combined-cap-g
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result

      s₂ = IRResultAWF.final-state result-g
      snd-loc = IRResultAWF.result-loc result-g

      ------------------------------------------------------------------------
      -- Pair allocation
      ------------------------------------------------------------------------
      reclaim-g = IRResultAWF.reclaimable-slot result-g

      reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
      reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

      reclaim-g-plus-ps-fits : reclaim-g +ℕ ps ≤ frame-capacity alloc
      reclaim-g-plus-ps-fits = ≤-trans (+-monoˡ-≤ ps reclaim-g-bound)
                                  (≤-trans (+-monoˡ-≤ ps (+-monoˡ-≤ rg reclaim-f-bound))
                                     combined-cap-suc)

      reclaim-g-fits : reclaim-g ≤ frame-capacity alloc
      reclaim-g-fits = ≤-trans reclaim-g-bound (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                         (≤-trans (m≤m+n (suc (next-slot alloc) +ℕ rf +ℕ rg) ps) combined-cap-suc))

      pair-loc = OnStack (current-frame alloc) reclaim-g

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc { next-slot = reclaim-g +ℕ ps }

      ------------------------------------------------------------------------
      -- Trace construction
      ------------------------------------------------------------------------
      f-trace = IRResultAWF.trace result-f
      g-trace = IRResultAWF.trace result-g

      fst-slot = reclaim-g
      snd-slot = suc reclaim-g

      pair-trace : AbstractTrace
      pair-trace = mov-to-output ∷ store-at-slot backup-slot ∷
                   f-trace ++
                   store-at-slot fst-slot ∷ restore-input backup-slot ∷
                   g-trace ++
                   store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      ------------------------------------------------------------------------
      -- KEY: s-final is DEFINED by the trace execution
      -- This makes trace-correct = refl trivially
      ------------------------------------------------------------------------
      s-final : LocState FS
      s-final = proj₁ (exec-trace pair-trace s alloc)

      ------------------------------------------------------------------------
      -- Location definitions
      ------------------------------------------------------------------------
      frame = current-frame alloc
      backup-loc : ValueLocation FS
      backup-loc = OnStack frame backup-slot
      fst-loc-stack : ValueLocation FS
      fst-loc-stack = OnStack frame fst-slot
      snd-loc-stack : ValueLocation FS
      snd-loc-stack = OnStack frame snd-slot

      ------------------------------------------------------------------------
      -- Slot independence bounds from sub-IRs
      ------------------------------------------------------------------------
      f-slot-reads : TraceSlotReadsAbove (suc backup-slot) f-trace
      f-slot-reads = IRResultAWF.trace-slot-reads-above result-f

      f-slot-writes : TraceWritesAbove (suc backup-slot) f-trace
      f-slot-writes = IRResultAWF.trace-writes-above result-f

      f-slot-reads-below : TraceSlotReadsBelow reclaim-f f-trace
      f-slot-reads-below = IRResultAWF.trace-slot-reads-below result-f

      f-writes-below : TraceWritesBelow reclaim-f f-trace
      f-writes-below = IRResultAWF.trace-writes-below result-f

      g-slot-reads : TraceSlotReadsAbove reclaim-f g-trace
      g-slot-reads = IRResultAWF.trace-slot-reads-above result-g

      g-slot-writes : TraceWritesAbove reclaim-f g-trace
      g-slot-writes = IRResultAWF.trace-writes-above result-g

      backup-below-reclaim : suc backup-slot ≤ reclaim-f
      backup-below-reclaim = IRResultAWF.reclaim-monotone result-f

      g-writes-below : TraceWritesBelow reclaim-g g-trace
      g-writes-below = IRResultAWF.trace-writes-below result-g

      g-slot-reads-below : TraceSlotReadsBelow reclaim-g g-trace
      g-slot-reads-below = IRResultAWF.trace-slot-reads-below result-g

      ------------------------------------------------------------------------
      -- Trace capacity preservation from sub-IRs
      ------------------------------------------------------------------------
      f-tpc : TracePreservesCapacity f-trace
      f-tpc = IRResultAWF.trace-preserves-capacity result-f

      g-tpc : TracePreservesCapacity g-trace
      g-tpc = IRResultAWF.trace-preserves-capacity result-g

      -- pair-trace preserves capacity: all instructions preserve capacity
      -- pair-trace = mov-to-output ∷ store-at-slot backup-slot ∷
      --              f-trace ++
      --              store-at-slot fst-slot ∷ restore-input backup-slot ∷
      --              g-trace ++
      --              store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      pair-trace-preserves-capacity : TracePreservesCapacity pair-trace
      pair-trace-preserves-capacity =
        tpc-∷ ipc-mov-to-output
        (tpc-∷ ipc-store-at-slot
        (tpc-++ f-tpc
        (tpc-∷ ipc-store-at-slot
        (tpc-∷ ipc-restore-input
        (tpc-++ g-tpc
        (tpc-∷ ipc-store-at-slot
        (tpc-∷ ipc-lea-slot tpc-[])))))))

      ------------------------------------------------------------------------
      -- Trace correctness from sub-IRs
      ------------------------------------------------------------------------
      f-correct : proj₁ (exec-trace f-trace s alloc-after-backup) ≡ s₁
      f-correct = IRResultAWF.trace-correct result-f

      g-correct : proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed) ≡ s₂
      g-correct = IRResultAWF.trace-correct result-g

      rax-f : readReg (regs s₁) Output ≡ fst-loc
      rax-f = IRResultAWF.rax-is-result result-f

      rax-g : readReg (regs s₂) Output ≡ snd-loc
      rax-g = IRResultAWF.rax-is-result result-g

      ------------------------------------------------------------------------
      -- Slot independence lemmas
      ------------------------------------------------------------------------
      f-slot-indep : ∀ (s' : LocState FS) (v : ValueLocation FS) →
        proj₁ (exec-trace f-trace (writeLoc s' backup-loc v) alloc-after-backup) ≡
        writeLoc (proj₁ (exec-trace f-trace s' alloc-after-backup)) backup-loc v
      f-slot-indep s' v = exec-trace-slot-independent f-trace s' alloc-after-backup
        frame backup-slot v (suc backup-slot) refl ≤-refl f-slot-reads f-slot-writes

      g-backup-indep : ∀ (s' : LocState FS) (v : ValueLocation FS) →
        proj₁ (exec-trace g-trace (writeLoc s' backup-loc v) alloc₁-reclaimed) ≡
        writeLoc (proj₁ (exec-trace g-trace s' alloc₁-reclaimed)) backup-loc v
      g-backup-indep s' v = exec-trace-slot-independent g-trace s' alloc₁-reclaimed
        frame backup-slot v reclaim-f refl backup-below-reclaim
        g-slot-reads g-slot-writes

      g-preserves-fst : ∀ (sg : LocState FS) →
        readLoc (proj₁ (exec-trace g-trace sg alloc₁-reclaimed)) fst-loc-stack ≡ readLoc sg fst-loc-stack
      g-preserves-fst sg = exec-trace-preserves-slot-above g-trace sg alloc₁-reclaimed
        frame fst-slot reclaim-g refl ≤-refl g-writes-below

      g-fst-indep : ∀ (s' : LocState FS) (val : ValueLocation FS) →
        proj₁ (exec-trace g-trace (writeLoc s' fst-loc-stack val) alloc₁-reclaimed) ≡
        writeLoc (proj₁ (exec-trace g-trace s' alloc₁-reclaimed)) fst-loc-stack val
      g-fst-indep s' val = exec-trace-slot-independent-above g-trace s' alloc₁-reclaimed
        frame fst-slot val reclaim-g refl ≤-refl g-slot-reads-below g-writes-below

      ------------------------------------------------------------------------
      -- Trace properties we need to prove about s-final
      --
      -- The trace does:
      -- 1. mov-to-output: Output := Input (= input-loc)
      -- 2. store-at-slot backup-slot: stackMem[backup-slot] := Output
      -- 3. f-trace: produces s₁ with Output = fst-loc
      -- 4. store-at-slot fst-slot: stackMem[fst-slot] := Output (= fst-loc)
      -- 5. restore-input backup-slot: Input := stackMem[backup-slot]
      -- 6. g-trace: produces s₂ with Output = snd-loc
      -- 7. store-at-slot snd-slot: stackMem[snd-slot] := Output (= snd-loc)
      -- 8. lea-slot fst-slot: Output := OnStack frame fst-slot (= pair-loc)
      --
      -- The key properties:
      -- - readReg Output s-final = pair-loc  (from lea-slot)
      -- - readLoc s-final fst-loc-stack = just fst-loc  (from store-at-slot fst-slot)
      -- - readLoc s-final snd-loc-stack = just snd-loc  (from store-at-slot snd-slot)
      ------------------------------------------------------------------------

      ------------------------------------------------------------------------
      -- Trace decomposition and result proofs
      --
      -- Strategy: decompose pair-trace into segments, track state changes
      -- pair-trace = setup ++ f-trace ++ middle ++ g-trace ++ final
      -- where:
      --   setup  = mov-to-output ∷ store-at-slot backup-slot ∷ []
      --   middle = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      --   final  = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      ------------------------------------------------------------------------

      -- Trace segments
      setup-trace : AbstractTrace
      setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []

      middle-trace : AbstractTrace
      middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []

      final-trace : AbstractTrace
      final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      -- TPC for trace segments
      setup-tpc : TracePreservesCapacity setup-trace
      setup-tpc = tpc-∷ ipc-mov-to-output (tpc-∷ ipc-store-at-slot tpc-[])

      middle-tpc : TracePreservesCapacity middle-trace
      middle-tpc = tpc-∷ ipc-store-at-slot (tpc-∷ ipc-restore-input tpc-[])

      final-tpc : TracePreservesCapacity final-trace
      final-tpc = tpc-∷ ipc-store-at-slot (tpc-∷ ipc-lea-slot tpc-[])

      -- Rewrite pair-trace in terms of segments
      pair-trace-eq : pair-trace ≡ setup-trace ++ f-trace ++ middle-trace ++ g-trace ++ final-trace
      pair-trace-eq = refl

      -- State after each segment
      s-after-setup : LocState FS
      s-after-setup = proj₁ (exec-trace setup-trace s alloc)

      alloc-after-setup : AllocState {FS}
      alloc-after-setup = proj₂ (exec-trace setup-trace s alloc)

      -- Note: setup doesn't change alloc (both mov-to-output and store-at-slot preserve alloc)

      -- Decomposition helper using exec-trace-append-state
      -- s-final = proj₁ (exec-trace pair-trace s alloc)
      --         = proj₁ (exec-trace final-trace s-before-final alloc-before-final)
      -- where s-before-final is after setup ++ f ++ middle ++ g

      -- For output-is-pair, we need to show the final lea-slot sets Output to pair-loc
      -- The final instruction is lea-slot fst-slot

      -- State right before final-trace (after g-trace)
      rest-after-setup : AbstractTrace
      rest-after-setup = f-trace ++ middle-trace ++ g-trace ++ final-trace

      rest-after-f : AbstractTrace
      rest-after-f = middle-trace ++ g-trace ++ final-trace

      rest-after-middle : AbstractTrace
      rest-after-middle = g-trace ++ final-trace

      -- halted preserved through setup-trace
      -- setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
      -- Both instructions preserve halted (halted-preserved-mov-to-output, halted-preserved-store-at-slot)
      not-halted-after-setup : halted s-after-setup ≡ false
      not-halted-after-setup =
        let
          -- After mov-to-output
          s-after-mov : LocState FS
          s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)

          halted-after-mov : halted s-after-mov ≡ halted s
          halted-after-mov = trans
            (cong halted (mov-to-output-state-eq s alloc not-halted))
            refl  -- record update preserves halted

          not-halted-after-mov : halted s-after-mov ≡ false
          not-halted-after-mov = trans halted-after-mov not-halted

          -- After store-at-slot backup-slot
          alloc-after-mov : AllocState {FS}
          alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)

          s-after-store-on-mov : LocState FS
          s-after-store-on-mov = proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)

          halted-after-store : halted s-after-store-on-mov ≡ halted s-after-mov
          halted-after-store = trans
            (cong halted (store-at-slot-state-eq backup-slot s-after-mov alloc-after-mov not-halted-after-mov))
            (writeLoc-halted s-after-mov (OnStack (current-frame alloc-after-mov) backup-slot)
                             (readReg (regs s-after-mov) Output))

          not-halted-after-store : halted s-after-store-on-mov ≡ false
          not-halted-after-store = trans halted-after-store not-halted-after-mov

          -- Relate s-after-setup to s-after-store-on-mov
          setup-decomp : s-after-setup ≡ s-after-store-on-mov
          setup-decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
        in
        trans (cong halted setup-decomp) not-halted-after-store

      -- State after f-trace on s-after-setup
      s-after-f-on-setup : LocState FS
      s-after-f-on-setup = proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)

      -- The f-trace was proven correct for state s (not s-after-setup)
      -- But using exec-trace-same-frame, we can reason about it

      -- Key insight: We need to track through the full trace decomposition
      -- Let's work backwards from the final state

      -- final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      -- After store-at-slot snd-slot: writes Output to snd-slot
      -- After lea-slot fst-slot: sets Output to OnStack frame fst-slot = pair-loc

      -- Define prefix-trace as everything before final-trace
      -- pair-trace structure (by definition):
      --   mov-to-output ∷ store-at-slot backup-slot ∷ f-trace ++
      --   store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++
      --   store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      prefix-trace : AbstractTrace
      prefix-trace = mov-to-output ∷ store-at-slot backup-slot ∷ f-trace ++
                     store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace

      -- Helper for the inner segment after f-trace
      middle-g-segment : AbstractTrace
      middle-g-segment = store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace

      -- pair-trace = prefix-trace ++ final-trace (via ++-assoc)
      -- pair-trace has structure: a ∷ b ∷ (f-trace ++ (middle ++ final-trace))
      -- prefix-trace ++ final-trace reduces to: a ∷ b ∷ ((f-trace ++ middle) ++ final-trace)
      -- These are equal by ++-assoc
      pair-trace-split : pair-trace ≡ prefix-trace ++ final-trace
      pair-trace-split = cong (mov-to-output ∷_) (cong (store-at-slot backup-slot ∷_)
                           (sym (++-assoc f-trace middle-g-segment final-trace)))

      -- State right before final-trace
      s-before-final : LocState FS
      s-before-final = proj₁ (exec-trace prefix-trace s alloc)

      alloc-before-final : AllocState {FS}
      alloc-before-final = proj₂ (exec-trace prefix-trace s alloc)

      -- s-final decomposition (uses pair-trace-split)
      -- First use pair-trace-split to rewrite pair-trace as prefix ++ final
      -- Then use exec-trace-append-state to decompose the execution
      s-final-decomp : s-final ≡ proj₁ (exec-trace final-trace s-before-final alloc-before-final)
      s-final-decomp = trans
        (cong (λ t → proj₁ (exec-trace t s alloc)) pair-trace-split)
        (exec-trace-append-state prefix-trace final-trace s alloc)

      -- Current frame is preserved through the whole trace
      -- Each instruction in pair-trace preserves the frame (no alloc-stack/dealloc-stack)
      -- The f-trace and g-trace preserve frame via IRResultAWF.frame-preserved
      -- PROVEN using exec-trace-preserves-frame from SlotMachine
      frame-preserved-trace : current-frame alloc-before-final ≡ frame
      frame-preserved-trace = exec-trace-preserves-frame prefix-trace s alloc

      ------------------------------------------------------------------------
      -- State decomposition for g-trace (moved here for not-halted-before-final)
      ------------------------------------------------------------------------
      middle-before-g : AbstractTrace
      middle-before-g = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []

      middle-before-g-tpc : TracePreservesCapacity middle-before-g
      middle-before-g-tpc = tpc-∷ ipc-store-at-slot (tpc-∷ ipc-restore-input tpc-[])

      prefix-before-g : AbstractTrace
      prefix-before-g = mov-to-output ∷ store-at-slot backup-slot ∷ f-trace ++ middle-before-g

      prefix-before-g-tpc : TracePreservesCapacity prefix-before-g
      prefix-before-g-tpc =
        tpc-∷ ipc-mov-to-output
        (tpc-∷ ipc-store-at-slot
        (tpc-++ f-tpc middle-before-g-tpc))

      -- prefix-trace = prefix-before-g ++ g-trace
      prefix-trace-split : prefix-trace ≡ prefix-before-g ++ g-trace
      prefix-trace-split = cong (mov-to-output ∷_) (cong (store-at-slot backup-slot ∷_)
        (trans (cong (f-trace ++_) refl)
          (sym (++-assoc f-trace middle-before-g g-trace))))

      -- State before g-trace
      s-before-g : LocState FS
      s-before-g = proj₁ (exec-trace prefix-before-g s alloc)

      alloc-before-g : AllocState {FS}
      alloc-before-g = proj₂ (exec-trace prefix-before-g s alloc)

      -- s-before-final decomposition via g-trace
      s-before-final-via-g : s-before-final ≡ proj₁ (exec-trace g-trace s-before-g alloc-before-g)
      s-before-final-via-g = trans
        (cong (λ t → proj₁ (exec-trace t s alloc)) prefix-trace-split)
        (exec-trace-append-state prefix-before-g g-trace s alloc)

      -- Frame is preserved through prefix-before-g
      frame-preserved-prefix-before-g : current-frame alloc-before-g ≡ frame
      frame-preserved-prefix-before-g = exec-trace-preserves-frame prefix-before-g s alloc

      -- Alloc frame equality: alloc-before-g has same frame as alloc₁-reclaimed
      alloc-frame-eq : current-frame alloc-before-g ≡ current-frame alloc₁-reclaimed
      alloc-frame-eq = trans frame-preserved-prefix-before-g refl

      -- Alloc capacity equality (both derived from alloc)
      alloc-cap-eq : frame-capacity alloc-before-g ≡ frame-capacity alloc₁-reclaimed
      alloc-cap-eq = trans (exec-trace-preserves-capacity' prefix-before-g s alloc prefix-before-g-tpc) refl

      ------------------------------------------------------------------------
      -- Intermediate state decomposition (for not-halted-before-final and s2-agrees-before-final)
      ------------------------------------------------------------------------
      setup-seg : AbstractTrace
      setup-seg = mov-to-output ∷ store-at-slot backup-slot ∷ []

      setup-seg-tpc : TracePreservesCapacity setup-seg
      setup-seg-tpc = tpc-∷ ipc-mov-to-output (tpc-∷ ipc-store-at-slot tpc-[])

      s-after-setup' : LocState FS
      s-after-setup' = proj₁ (exec-trace setup-seg s alloc)

      alloc-after-setup' : AllocState {FS}
      alloc-after-setup' = proj₂ (exec-trace setup-seg s alloc)

      -- After f-trace
      s-after-f' : LocState FS
      s-after-f' = proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup')

      alloc-after-f' : AllocState {FS}
      alloc-after-f' = proj₂ (exec-trace f-trace s-after-setup' alloc-after-setup')

      -- After store-at-slot fst-slot
      s-after-store-fst : LocState FS
      s-after-store-fst = proj₁ (exec-trace (store-at-slot fst-slot ∷ []) s-after-f' alloc-after-f')

      alloc-after-store-fst : AllocState {FS}
      alloc-after-store-fst = proj₂ (exec-trace (store-at-slot fst-slot ∷ []) s-after-f' alloc-after-f')

      -- Halted after setup
      not-halted-setup' : halted s-after-setup' ≡ false
      not-halted-setup' = not-halted-after-setup

      -- Frame and capacity equalities for f-trace state equivalence
      setup-frame-eq : current-frame alloc-after-setup' ≡ current-frame alloc
      setup-frame-eq = exec-trace-preserves-frame setup-seg s alloc

      setup-cap-eq : frame-capacity alloc-after-setup' ≡ frame-capacity alloc
      setup-cap-eq = exec-trace-preserves-capacity' setup-seg s alloc setup-seg-tpc

      -- State after restore-input
      s-after-restore : LocState FS
      s-after-restore = proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-store-fst alloc-after-store-fst)

      alloc-after-restore : AllocState {FS}
      alloc-after-restore = proj₂ (exec-trace (restore-input backup-slot ∷ []) s-after-store-fst alloc-after-store-fst)

      -- s-before-g = s-after-restore (by trace decomposition)
      s-before-g-eq : s-before-g ≡ s-after-restore
      s-before-g-eq =
        let
          step1 : proj₁ (exec-trace prefix-before-g s alloc) ≡
                  proj₁ (exec-trace (f-trace ++ middle-before-g) s-after-setup' alloc-after-setup')
          step1 = exec-trace-append-state setup-seg (f-trace ++ middle-before-g) s alloc
          step2 : proj₁ (exec-trace (f-trace ++ middle-before-g) s-after-setup' alloc-after-setup') ≡
                  proj₁ (exec-trace middle-before-g s-after-f' alloc-after-f')
          step2 = exec-trace-append-state f-trace middle-before-g s-after-setup' alloc-after-setup'
          step3 : proj₁ (exec-trace middle-before-g s-after-f' alloc-after-f') ≡
                  proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-store-fst alloc-after-store-fst)
          step3 = exec-trace-append-state (store-at-slot fst-slot ∷ []) (restore-input backup-slot ∷ []) s-after-f' alloc-after-f'
        in trans step1 (trans step2 step3)

      -- Frame after f-trace
      frame-after-f' : current-frame alloc-after-f' ≡ current-frame alloc
      frame-after-f' = trans (exec-trace-preserves-frame f-trace s-after-setup' alloc-after-setup') setup-frame-eq

      -- Frame after store-fst
      frame-after-store-fst : current-frame alloc-after-store-fst ≡ current-frame alloc
      frame-after-store-fst = trans (exec-trace-preserves-frame (store-at-slot fst-slot ∷ []) s-after-f' alloc-after-f') frame-after-f'

      -- Helper to extract slot from a stack location
      slot-of : ValueLocation FS → ℕ
      slot-of (OnStack _ k) = k
      slot-of (OnHeap _) = 0

      -- Helper to extract frame from stack location
      frame-of-loc : ValueLocation FS → Frame
      frame-of-loc (OnStack f _) = f
      frame-of-loc (OnHeap _) = frame  -- default, won't be used

      -- Helper: traces that write only to current frame preserve ancestor frame locations
      -- If trace writes above bound on current frame, and loc is in ancestor frame f' ≺ frame,
      -- then the trace preserves loc (because f' ≠ frame)
      exec-trace-preserves-ancestor : ∀ trace st a (loc : ValueLocation FS) →
        current-frame a ≡ frame →
        frame-of-loc loc ≺ frame →
        TraceWritesAbove (suc backup-slot) trace →
        readLoc (proj₁ (exec-trace trace st a)) loc ≡ readLoc st loc
      exec-trace-preserves-ancestor trace st a loc frame-eq f'≺frame writes-above =
        exec-trace-preserves-disjoint trace st a loc (suc backup-slot) writes-above
          (λ slot' bound eq → ≺⇒≢ f'≺frame (trans (sym (cong frame-of-loc eq)) frame-eq))

      -- Halted after f-trace (proven via exec-trace-preserves-halted-subir)
      not-halted-after-f' : halted s-after-f' ≡ false
      not-halted-after-f' =
        let
          -- Input after setup = input-loc
          input-after-setup'' : readReg (regs s-after-setup') Input ≡ input-loc
          input-after-setup'' =
            let
              s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              input-unchanged : readReg (regs s-after-mov) Input ≡ readReg (regs s) Input
              input-unchanged = trans (cong (λ st → readReg (regs st) Input) (mov-to-output-state-eq s alloc not-halted)) refl
              decomp : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov
                                                          (proj₂ (exec-trace (mov-to-output ∷ []) s alloc)))
              decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              not-halted-mov : halted s-after-mov ≡ false
              not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              store-input-unchanged : readReg (regs (proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov
                                                                        (proj₂ (exec-trace (mov-to-output ∷ []) s alloc))))) Input ≡
                                      readReg (regs s-after-mov) Input
              store-input-unchanged = trans (cong (λ st → readReg (regs st) Input)
                                                  (store-at-slot-state-eq backup-slot s-after-mov
                                                    (proj₂ (exec-trace (mov-to-output ∷ []) s alloc)) not-halted-mov))
                                            refl
            in trans (cong (λ st → readReg (regs st) Input) decomp)
                     (trans store-input-unchanged (trans input-unchanged rdi-eq))
          -- Slots equivalence for f-trace: slots in [suc backup-slot, reclaim-f) are same in s-after-setup' and s
          slots-eq-f' : ∀ slot → suc backup-slot ≤ slot → slot < reclaim-f →
            readLoc s-after-setup' (OnStack (current-frame alloc-after-backup) slot) ≡
            readLoc s (OnStack (current-frame alloc-after-backup) slot)
          slots-eq-f' slot lo hi =
            let
              loc = OnStack (current-frame alloc) slot
              s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              mov-preserves : readLoc s-after-mov loc ≡ readLoc s loc
              mov-preserves = mov-to-output-preserves-readLoc s alloc loc not-halted
              not-halted-mov : halted s-after-mov ≡ false
              not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              backup-neq-slot : backup-slot ≢ slot
              backup-neq-slot eq = <⇒≢ lo eq
              frame-after-mov : current-frame alloc-after-mov ≡ current-frame alloc
              frame-after-mov = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
              loc-neq : OnStack (current-frame alloc-after-mov) backup-slot ≢ loc
              loc-neq eq = backup-neq-slot (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-mov))))
              store-preserves : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov alloc-after-mov)) loc ≡
                                readLoc s-after-mov loc
              store-preserves = store-at-slot-preserves-disjoint backup-slot s-after-mov alloc-after-mov loc loc-neq
              decomp : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)
              decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              store-via-abstract : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov) ≡
                                   proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov alloc-after-mov)
              store-via-abstract = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov alloc-after-mov not-halted-mov)
            in trans (cong (λ st → readLoc st loc) decomp)
                     (trans (cong (λ st → readLoc st loc) store-via-abstract)
                            (trans store-preserves mov-preserves))
          -- Use exec-trace-preserves-halted-subir with f-trace
          halted-f-equiv : halted (proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)) ≡ false
          halted-f-equiv = exec-trace-preserves-halted-subir f-trace s-after-setup' s alloc-after-backup
                             (suc backup-slot) reclaim-f
                             (trans input-after-setup'' (sym rdi-eq))
                             slots-eq-f'
                             f-slot-reads
                             (IRResultAWF.trace-slot-reads-below result-f)
                             not-halted-setup'
                             not-halted
                             (subst (λ st → halted st ≡ false) (sym f-correct) (IRResultAWF.not-halted result-f))
          f-same-frame : proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup') ≡
                         proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)
          f-same-frame = exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup
                           setup-frame-eq setup-cap-eq
        in trans (cong halted f-same-frame) halted-f-equiv

      -- Halted after store-at-slot fst-slot (safe instruction)
      not-halted-after-store-fst : halted s-after-store-fst ≡ false
      not-halted-after-store-fst =
        subst (λ st → halted st ≡ false)
              (sym (store-at-slot-state-eq fst-slot s-after-f' alloc-after-f' not-halted-after-f'))
              not-halted-after-f'

      -- backup-slot contains input-loc at s-after-store-fst (needed for restore-input)
      backup-has-input' : readLoc s-after-store-fst (OnStack (current-frame alloc-after-store-fst) backup-slot) ≡ just input-loc
      backup-has-input' =
        let
          backup-after-setup : readLoc s-after-setup' (OnStack (current-frame alloc) backup-slot) ≡ just input-loc
          backup-after-setup =
            let
              s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              not-halted-mov : halted s-after-mov ≡ false
              not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              output-after-mov : readReg (regs s-after-mov) Output ≡ input-loc
              output-after-mov = trans (mov-to-output-sets-output s alloc not-halted) rdi-eq
              backup-written : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov))
                                       (OnStack (current-frame alloc-after-mov) backup-slot) ≡
                               just (readReg (regs s-after-mov) Output)
              backup-written = store-at-slot-reads-back backup-slot s-after-mov alloc-after-mov not-halted-mov
              decomp : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)
              decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              frame-after-mov : current-frame alloc-after-mov ≡ current-frame alloc
              frame-after-mov = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
            in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) decomp)
                     (trans (subst (λ f → readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov))
                                                  (OnStack f backup-slot) ≡ just (readReg (regs s-after-mov) Output))
                                   frame-after-mov backup-written)
                            (cong just output-after-mov))
          -- f-trace preserves backup-slot (writes above suc backup-slot)
          f-preserves-backup : readLoc s-after-f' (OnStack (current-frame alloc) backup-slot) ≡
                               readLoc s-after-setup' (OnStack (current-frame alloc) backup-slot)
          f-preserves-backup =
            let
              backup-disjoint : ∀ slot' → suc backup-slot ≤ slot' →
                                OnStack (current-frame alloc-after-backup) slot' ≢ OnStack (current-frame alloc) backup-slot
              backup-disjoint slot' bound eq =
                let slot-eq : slot' ≡ backup-slot
                    slot-eq = cong slot-of eq
                in <⇒≢ bound (sym slot-eq)
              f-same : proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup') ≡
                       proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)
              f-same = exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup
                         setup-frame-eq setup-cap-eq
            in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) f-same)
                     (exec-trace-preserves-disjoint f-trace s-after-setup' alloc-after-backup
                        (OnStack (current-frame alloc) backup-slot) (suc backup-slot)
                        (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                        backup-disjoint)
          -- store-at-slot fst-slot preserves backup-slot (fst-slot ≠ backup-slot)
          fst-neq-backup : fst-slot ≢ backup-slot
          fst-neq-backup eq = <⇒≢ (≤-trans (IRResultAWF.reclaim-monotone result-f)
                                          (IRResultAWF.reclaim-monotone result-g)) (sym eq)
          loc-neq : OnStack (current-frame alloc-after-f') fst-slot ≢ OnStack (current-frame alloc) backup-slot
          loc-neq eq = fst-neq-backup (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f backup-slot) (sym frame-after-f'))))
          store-fst-via-abstract : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
          store-fst-via-abstract = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')
          store-fst-preserves : readLoc (proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f'))
                                        (OnStack (current-frame alloc) backup-slot) ≡
                                readLoc s-after-f' (OnStack (current-frame alloc) backup-slot)
          store-fst-preserves = store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f'
                                  (OnStack (current-frame alloc) backup-slot) loc-neq
        in trans (cong (λ f → readLoc s-after-store-fst (OnStack f backup-slot)) frame-after-store-fst)
                 (trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) store-fst-via-abstract)
                        (trans store-fst-preserves (trans f-preserves-backup backup-after-setup)))

      -- Halted after restore-input
      not-halted-after-restore : halted s-after-restore ≡ false
      not-halted-after-restore =
        let
          restore-via-abstract : s-after-restore ≡ proj₁ (exec-abstract (restore-input backup-slot) s-after-store-fst alloc-after-store-fst)
          restore-via-abstract = cong proj₁ (exec-trace-single (restore-input backup-slot) s-after-store-fst alloc-after-store-fst not-halted-after-store-fst)
          halted-eq : halted (proj₁ (exec-abstract (restore-input backup-slot) s-after-store-fst alloc-after-store-fst)) ≡ halted s-after-store-fst
          halted-eq = halted-preserved-restore-input backup-slot s-after-store-fst alloc-after-store-fst input-loc backup-has-input'
        in trans (cong halted restore-via-abstract) (trans halted-eq not-halted-after-store-fst)

      -- halted is preserved through the trace (needed for final instructions)
      -- Proof structure: trace through setup → f → store-fst → restore → g
      not-halted-before-final : halted s-before-final ≡ false
      not-halted-before-final =
        let

          -- Input after setup = input-loc
          input-after-setup' : readReg (regs s-after-setup') Input ≡ input-loc
          input-after-setup' =
            let
              s-after-mov' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              input-unchanged : readReg (regs s-after-mov') Input ≡ readReg (regs s) Input
              input-unchanged = trans (cong (λ st → readReg (regs st) Input) (mov-to-output-state-eq s alloc not-halted))
                                      refl
              decomp : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'
                                                          (proj₂ (exec-trace (mov-to-output ∷ []) s alloc)))
              decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              not-halted-mov : halted s-after-mov' ≡ false
              not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              store-input-unchanged : readReg (regs (proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'
                                                                        (proj₂ (exec-trace (mov-to-output ∷ []) s alloc))))) Input ≡
                                      readReg (regs s-after-mov') Input
              store-input-unchanged = trans (cong (λ st → readReg (regs st) Input)
                                                  (store-at-slot-state-eq backup-slot s-after-mov'
                                                    (proj₂ (exec-trace (mov-to-output ∷ []) s alloc)) not-halted-mov))
                                            refl
            in trans (cong (λ st → readReg (regs st) Input) decomp)
                     (trans store-input-unchanged (trans input-unchanged rdi-eq))

          -- Slots equivalence for f-trace: slots in [suc backup-slot, reclaim-f) are same in s-after-setup' and s
          slots-eq-f : ∀ slot → suc backup-slot ≤ slot → slot < reclaim-f →
            readLoc s-after-setup' (OnStack (current-frame alloc-after-backup) slot) ≡
            readLoc s (OnStack (current-frame alloc-after-backup) slot)
          slots-eq-f slot lo hi =
            let
              loc = OnStack (current-frame alloc) slot
              -- setup writes only to backup-slot, which is < suc backup-slot ≤ slot
              -- So slot is preserved through setup
              s-after-mov' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              mov-preserves : readLoc s-after-mov' loc ≡ readLoc s loc
              mov-preserves = mov-to-output-preserves-readLoc s alloc loc not-halted
              not-halted-mov : halted s-after-mov' ≡ false
              not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              -- store backup-slot preserves slot (backup-slot ≠ slot since backup-slot < suc backup-slot ≤ slot)
              backup-neq-slot : backup-slot ≢ slot
              backup-neq-slot eq = <⇒≢ lo eq
              frame-after-mov : current-frame alloc-after-mov' ≡ current-frame alloc
              frame-after-mov = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
              loc-neq : OnStack (current-frame alloc-after-mov') backup-slot ≢ loc
              loc-neq eq = backup-neq-slot (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-mov))))
              store-preserves : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov' alloc-after-mov')) loc ≡
                                readLoc s-after-mov' loc
              store-preserves = store-at-slot-preserves-disjoint backup-slot s-after-mov' alloc-after-mov' loc loc-neq
              decomp : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov' alloc-after-mov')
              decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              store-via-abstract : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov' alloc-after-mov') ≡
                                   proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov' alloc-after-mov')
              store-via-abstract = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov' alloc-after-mov' not-halted-mov)
            in trans (cong (λ st → readLoc st loc) decomp)
                     (trans (cong (λ st → readLoc st loc) store-via-abstract)
                            (trans store-preserves mov-preserves))

          -- Halted after f-trace using exec-trace-preserves-halted-subir
          not-halted-after-f' : halted s-after-f' ≡ false
          not-halted-after-f' =
            let
              -- Use exec-trace-preserves-halted-subir with f-trace
              -- comparing s-after-setup' with s (the canonical state for result-f)
              halted-f-equiv : halted (proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)) ≡ false
              halted-f-equiv = exec-trace-preserves-halted-subir f-trace s-after-setup' s alloc-after-backup
                                 (suc backup-slot) reclaim-f
                                 (trans input-after-setup' (sym rdi-eq))
                                 slots-eq-f
                                 f-slot-reads
                                 (IRResultAWF.trace-slot-reads-below result-f)
                                 not-halted-setup'
                                 not-halted
                                 (subst (λ st → halted st ≡ false) (sym f-correct) (IRResultAWF.not-halted result-f))
              -- Relate alloc-after-setup' to alloc-after-backup via same-frame
              f-same-frame : proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup') ≡
                             proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)
              f-same-frame = exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup
                               setup-frame-eq setup-cap-eq
            in trans (cong halted f-same-frame) halted-f-equiv

          -- Halted after store-at-slot fst-slot (safe instruction)
          not-halted-after-store-fst : halted s-after-store-fst ≡ false
          not-halted-after-store-fst =
            subst (λ st → halted st ≡ false)
                  (sym (store-at-slot-state-eq fst-slot s-after-f' alloc-after-f' not-halted-after-f'))
                  not-halted-after-f'

          -- backup-slot contains input-loc at s-after-store-fst (needed for restore-input)
          frame-after-f' : current-frame alloc-after-f' ≡ current-frame alloc
          frame-after-f' = trans (exec-trace-preserves-frame f-trace s-after-setup' alloc-after-setup') setup-frame-eq

          frame-after-store-fst : current-frame alloc-after-store-fst ≡ current-frame alloc
          frame-after-store-fst = trans (exec-trace-preserves-frame (store-at-slot fst-slot ∷ []) s-after-f' alloc-after-f') frame-after-f'

          backup-has-input' : readLoc s-after-store-fst (OnStack (current-frame alloc-after-store-fst) backup-slot) ≡ just input-loc
          backup-has-input' =
            let
              -- backup-slot was written at setup and preserved through f-trace and store-fst
              -- Similar to backup-has-input in the existing code
              backup-after-setup' : readLoc s-after-setup' (OnStack (current-frame alloc) backup-slot) ≡ just input-loc
              backup-after-setup' =
                let
                  s-after-mov' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
                  alloc-after-mov' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
                  not-halted-mov : halted s-after-mov' ≡ false
                  not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
                  output-after-mov : readReg (regs s-after-mov') Output ≡ input-loc
                  output-after-mov = trans (mov-to-output-sets-output s alloc not-halted) rdi-eq
                  backup-written : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov' alloc-after-mov'))
                                           (OnStack (current-frame alloc-after-mov') backup-slot) ≡
                                   just (readReg (regs s-after-mov') Output)
                  backup-written = store-at-slot-reads-back backup-slot s-after-mov' alloc-after-mov' not-halted-mov
                  decomp : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov' alloc-after-mov')
                  decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
                  frame-after-mov' : current-frame alloc-after-mov' ≡ current-frame alloc
                  frame-after-mov' = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
                in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) decomp)
                         (trans (subst (λ f → readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov' alloc-after-mov'))
                                                      (OnStack f backup-slot) ≡ just (readReg (regs s-after-mov') Output))
                                       frame-after-mov' backup-written)
                                (cong just output-after-mov))

              -- f-trace preserves backup-slot (writes above suc backup-slot)
              f-preserves-backup' : readLoc s-after-f' (OnStack (current-frame alloc) backup-slot) ≡
                                    readLoc s-after-setup' (OnStack (current-frame alloc) backup-slot)
              f-preserves-backup' =
                let
                  -- alloc-after-backup only changes next-slot, so frame is same as alloc
                  backup-frame-eq : current-frame alloc-after-backup ≡ current-frame alloc
                  backup-frame-eq = refl
                  backup-disjoint : ∀ slot' → suc backup-slot ≤ slot' →
                                    OnStack (current-frame alloc-after-backup) slot' ≢ OnStack (current-frame alloc) backup-slot
                  backup-disjoint slot' bound eq =
                    let slot-eq : slot' ≡ backup-slot
                        slot-eq = cong slot-of (trans (cong (λ f → OnStack f slot') (sym backup-frame-eq)) eq)
                    in <⇒≢ bound (sym slot-eq)
                  f-same : proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup') ≡
                           proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)
                  f-same = exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup
                             setup-frame-eq setup-cap-eq
                in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) f-same)
                         (exec-trace-preserves-disjoint f-trace s-after-setup' alloc-after-backup
                            (OnStack (current-frame alloc) backup-slot) (suc backup-slot)
                            (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                            backup-disjoint)

              -- store-at-slot fst-slot preserves backup-slot (fst-slot ≠ backup-slot)
              fst-neq-backup'' : fst-slot ≢ backup-slot
              fst-neq-backup'' eq = <⇒≢ (≤-trans (IRResultAWF.reclaim-monotone result-f)
                                                (IRResultAWF.reclaim-monotone result-g)) (sym eq)
              loc-neq'' : OnStack (current-frame alloc-after-f') fst-slot ≢ OnStack (current-frame alloc) backup-slot
              loc-neq'' eq = fst-neq-backup'' (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f backup-slot) (sym frame-after-f'))))
              store-fst-via-abstract' : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
              store-fst-via-abstract' = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')
              store-fst-preserves : readLoc (proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f'))
                                            (OnStack (current-frame alloc) backup-slot) ≡
                                    readLoc s-after-f' (OnStack (current-frame alloc) backup-slot)
              store-fst-preserves = store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f'
                                      (OnStack (current-frame alloc) backup-slot) loc-neq''
            in trans (cong (λ f → readLoc s-after-store-fst (OnStack f backup-slot)) frame-after-store-fst)
                     (trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) store-fst-via-abstract')
                            (trans store-fst-preserves (trans f-preserves-backup' backup-after-setup')))

          -- Shared helper: store-fst-via-abstract (needed by both backup-has-input' and slots-eq-g)
          store-fst-via-abstract : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
          store-fst-via-abstract = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')

          -- State after restore-input
          s-after-restore : LocState FS
          s-after-restore = proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-store-fst alloc-after-store-fst)

          alloc-after-restore : AllocState {FS}
          alloc-after-restore = proj₂ (exec-trace (restore-input backup-slot ∷ []) s-after-store-fst alloc-after-store-fst)

          -- Halted after restore-input (using halted-preserved-restore-input)
          not-halted-after-restore : halted s-after-restore ≡ false
          not-halted-after-restore =
            let
              restore-via-abstract : s-after-restore ≡ proj₁ (exec-abstract (restore-input backup-slot) s-after-store-fst alloc-after-store-fst)
              restore-via-abstract = cong proj₁ (exec-trace-single (restore-input backup-slot) s-after-store-fst alloc-after-store-fst not-halted-after-store-fst)
              halted-eq : halted (proj₁ (exec-abstract (restore-input backup-slot) s-after-store-fst alloc-after-store-fst)) ≡ halted s-after-store-fst
              halted-eq = halted-preserved-restore-input backup-slot s-after-store-fst alloc-after-store-fst input-loc backup-has-input'
            in trans (cong halted restore-via-abstract) (trans halted-eq not-halted-after-store-fst)

          -- s-before-g = s-after-restore (by trace decomposition)
          s-before-g-eq : s-before-g ≡ s-after-restore
          s-before-g-eq =
            let
              step1 : proj₁ (exec-trace prefix-before-g s alloc) ≡
                      proj₁ (exec-trace (f-trace ++ middle-before-g) s-after-setup' alloc-after-setup')
              step1 = exec-trace-append-state setup-seg (f-trace ++ middle-before-g) s alloc
              step2 : proj₁ (exec-trace (f-trace ++ middle-before-g) s-after-setup' alloc-after-setup') ≡
                      proj₁ (exec-trace middle-before-g s-after-f' alloc-after-f')
              step2 = exec-trace-append-state f-trace middle-before-g s-after-setup' alloc-after-setup'
              step3 : proj₁ (exec-trace middle-before-g s-after-f' alloc-after-f') ≡
                      proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-store-fst alloc-after-store-fst)
              step3 = exec-trace-append-state (store-at-slot fst-slot ∷ []) (restore-input backup-slot ∷ []) s-after-f' alloc-after-f'
            in trans step1 (trans step2 step3)

          not-halted-s-before-g' : halted s-before-g ≡ false
          not-halted-s-before-g' = trans (cong halted s-before-g-eq) not-halted-after-restore

          -- Step 3: Prove halted preserved through g-trace
          -- Use exec-trace-preserves-halted-subir comparing s-before-g with s₁'

          -- Input equivalence
          input-after-restore : readReg (regs s-after-restore) Input ≡ input-loc
          input-after-restore = restore-input-sets-input backup-slot s-after-store-fst alloc-after-store-fst input-loc
                                  not-halted-after-store-fst backup-has-input'

          input-eq-g : readReg (regs s-before-g) Input ≡ readReg (regs s₁') Input
          input-eq-g = trans (cong (λ st → readReg (regs st) Input) s-before-g-eq)
                             (trans input-after-restore (sym rdi-eq₁))

          not-halted-s1' : halted s₁' ≡ false
          not-halted-s1' = IRResultAWF.not-halted result-f

          -- Slots equivalence for g-trace: slots in [reclaim-f, reclaim-g) are same
          slots-eq-g : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
            readLoc s-before-g (OnStack (current-frame alloc₁-reclaimed) slot) ≡
            readLoc s₁' (OnStack (current-frame alloc₁-reclaimed) slot)
          slots-eq-g slot rf≤slot slot<rg =
            let
              loc = OnStack (current-frame alloc) slot
              -- s₁' preserves slot from s (f-trace writes below reclaim-f)
              s1'-eq-s : readLoc s₁' loc ≡ readLoc s loc
              s1'-eq-s =
                let
                  s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
                  s1-via-trace = sym (IRResultAWF.trace-correct result-f)
                  s1-eq-s : readLoc s₁ loc ≡ readLoc s loc
                  s1-eq-s = trans (cong (λ st → readLoc st loc) s1-via-trace)
                                  (exec-trace-preserves-slot-above f-trace s alloc-after-backup
                                     (current-frame alloc-after-backup) slot reclaim-f refl rf≤slot f-writes-below)
                in trans refl s1-eq-s  -- s₁' has same memory as s₁

              -- s-before-g preserves slot from s
              -- prefix-before-g writes: backup-slot, slots in [suc backup-slot, reclaim-f), fst-slot = reclaim-g
              -- None of these are in [reclaim-f, reclaim-g) except we need to check fst-slot
              fst-slot-neq : fst-slot ≢ slot
              fst-slot-neq eq = <⇒≢ slot<rg (sym eq)

              s-before-g-eq-s : readLoc s-before-g loc ≡ readLoc s loc
              s-before-g-eq-s =
                let
                  -- setup preserves slot (writes only backup-slot < reclaim-f ≤ slot)
                  backup-below-rf : backup-slot < reclaim-f
                  backup-below-rf = IRResultAWF.reclaim-monotone result-f
                  backup-neq : backup-slot ≢ slot
                  backup-neq eq = <⇒≢ (≤-trans backup-below-rf rf≤slot) eq

                  -- Setup preservation: setup segment only writes backup-slot, which is < reclaim-f ≤ slot
                  s-after-mov'' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
                  alloc-after-mov'' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
                  mov-preserves' : readLoc s-after-mov'' loc ≡ readLoc s loc
                  mov-preserves' = mov-to-output-preserves-readLoc s alloc loc not-halted
                  not-halted-mov'' : halted s-after-mov'' ≡ false
                  not-halted-mov'' = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
                  frame-after-mov'' : current-frame alloc-after-mov'' ≡ current-frame alloc
                  frame-after-mov'' = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
                  loc-neq' : OnStack (current-frame alloc-after-mov'') backup-slot ≢ loc
                  loc-neq' eq' = backup-neq (trans (cong slot-of eq') (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-mov''))))
                  store-preserves' : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')) loc ≡
                                     readLoc s-after-mov'' loc
                  store-preserves' = store-at-slot-preserves-disjoint backup-slot s-after-mov'' alloc-after-mov'' loc loc-neq'
                  decomp' : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'')
                  decomp' = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
                  store-via-abstract' : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'') ≡
                                        proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')
                  store-via-abstract' = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'' not-halted-mov'')
                  setup-preserves' : readLoc s-after-setup' loc ≡ readLoc s loc
                  setup-preserves' = trans (cong (λ st → readLoc st loc) decomp')
                                           (trans (cong (λ st → readLoc st loc) store-via-abstract')
                                                  (trans store-preserves' mov-preserves'))

                  -- f-trace preserves slot (writes below reclaim-f ≤ slot)
                  -- store-at-slot fst-slot preserves slot (fst-slot = reclaim-g ≠ slot < reclaim-g)
                  -- restore-input doesn't write to stack
                in trans (cong (λ st → readLoc st loc) s-before-g-eq)
                         (trans (restore-input-preserves-readLoc backup-slot s-after-store-fst alloc-after-store-fst input-loc loc not-halted-after-store-fst backup-has-input')
                                (trans (cong (λ st → readLoc st loc) store-fst-via-abstract)
                                       (trans (store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f' loc
                                                (λ eq → fst-slot-neq (trans (cong slot-of eq)
                                                                           (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-f'))))))
                                              (trans (cong (λ st → readLoc st loc) (exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup setup-frame-eq setup-cap-eq))
                                                     (trans (exec-trace-preserves-slot-above f-trace s-after-setup' alloc-after-backup
                                                              (current-frame alloc-after-backup) slot reclaim-f refl rf≤slot f-writes-below)
                                                            setup-preserves')))))
            in trans s-before-g-eq-s (sym s1'-eq-s)

          -- Halted after g-trace using exec-trace-preserves-halted-subir
          halted-g-equiv : halted (proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed)) ≡ false
          halted-g-equiv = exec-trace-preserves-halted-subir g-trace s-before-g s₁' alloc₁-reclaimed
                             reclaim-f reclaim-g
                             input-eq-g
                             slots-eq-g
                             g-slot-reads
                             g-slot-reads-below
                             not-halted-s-before-g'
                             not-halted-s1'
                             (subst (λ st → halted st ≡ false) (sym g-correct) (IRResultAWF.not-halted result-g))

          -- Relate alloc-before-g to alloc₁-reclaimed via same-frame
          g-same-frame : proj₁ (exec-trace g-trace s-before-g alloc-before-g) ≡
                         proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed)
          g-same-frame = exec-trace-state-same-frame g-trace s-before-g alloc-before-g alloc₁-reclaimed
                           alloc-frame-eq alloc-cap-eq
        in trans (cong halted s-before-final-via-g) (trans (cong halted g-same-frame) halted-g-equiv)

      -- State after store-at-slot snd-slot
      s-after-snd-store : LocState FS
      s-after-snd-store = proj₁ (exec-trace (store-at-slot snd-slot ∷ []) s-before-final alloc-before-final)

      snd-store-state : s-after-snd-store ≡ writeLoc s-before-final (OnStack (current-frame alloc-before-final) snd-slot) (readReg (regs s-before-final) Output)
      snd-store-state = store-at-slot-state-eq snd-slot s-before-final alloc-before-final not-halted-before-final

      not-halted-after-snd-store : halted s-after-snd-store ≡ false
      not-halted-after-snd-store = subst (λ st → halted st ≡ false) (sym snd-store-state) not-halted-before-final

      -- State after lea-slot fst-slot (this is s-final)
      lea-slot-decomp : proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final) ≡
                        record s-after-snd-store { regs = writeReg (regs s-after-snd-store) Output (OnStack (current-frame alloc-before-final) fst-slot) }
      lea-slot-decomp = lea-slot-state-eq fst-slot s-after-snd-store alloc-before-final not-halted-after-snd-store

      -- store-at-slot doesn't change alloc (needed for decomposition)
      -- From exec-trace-single: exec-trace (i ∷ []) s alloc ≡ exec-abstract i s alloc
      -- From exec-abstract: exec-abstract (store-at-slot slot) s alloc = (writeLoc s ... , alloc)
      alloc-after-snd-store : AllocState {FS}
      alloc-after-snd-store = proj₂ (exec-trace (store-at-slot snd-slot ∷ []) s-before-final alloc-before-final)

      alloc-after-snd-eq : alloc-after-snd-store ≡ alloc-before-final
      alloc-after-snd-eq = cong proj₂ (exec-trace-single (store-at-slot snd-slot) s-before-final alloc-before-final not-halted-before-final)

      -- The final trace decomposition
      -- final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      --             = (store-at-slot snd-slot ∷ []) ++ (lea-slot fst-slot ∷ [])  (definitionally!)
      -- Uses exec-trace-append-state with explicit alloc threading
      final-trace-decomp : proj₁ (exec-trace final-trace s-before-final alloc-before-final) ≡
                           proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final)
      final-trace-decomp =
        let
          -- exec-trace-append-state gives us RHS with alloc-after-snd-store
          step1 : proj₁ (exec-trace final-trace s-before-final alloc-before-final) ≡
                  proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-after-snd-store)
          step1 = exec-trace-append-state (store-at-slot snd-slot ∷ []) (lea-slot fst-slot ∷ []) s-before-final alloc-before-final
          -- Use alloc equality to get the desired form
          step2 : proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-after-snd-store) ≡
                  proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final)
          step2 = cong (λ a → proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store a)) alloc-after-snd-eq
        in trans step1 step2

      -- pair-loc = OnStack frame fst-slot, and frame = current-frame alloc-before-final
      pair-loc-eq-final : OnStack (current-frame alloc-before-final) fst-slot ≡ pair-loc
      pair-loc-eq-final = cong (λ f → OnStack f fst-slot) frame-preserved-trace

      -- PROVEN: output-is-pair
      output-is-pair : readReg (regs s-final) Output ≡ pair-loc
      output-is-pair =
        let
          s-lea = record s-after-snd-store { regs = writeReg (regs s-after-snd-store) Output (OnStack (current-frame alloc-before-final) fst-slot) }
          step1 : s-final ≡ proj₁ (exec-trace final-trace s-before-final alloc-before-final)
          step1 = s-final-decomp
          step2 : proj₁ (exec-trace final-trace s-before-final alloc-before-final) ≡ proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final)
          step2 = final-trace-decomp
          step3 : proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final) ≡ s-lea
          step3 = lea-slot-decomp
          s-final-eq : s-final ≡ s-lea
          s-final-eq = trans step1 (trans step2 step3)
          reg-eq : readReg (regs s-lea) Output ≡ OnStack (current-frame alloc-before-final) fst-slot
          reg-eq = writeReg-same (regs s-after-snd-store) Output (OnStack (current-frame alloc-before-final) fst-slot)
        in
        trans (cong (λ st → readReg (regs st) Output) s-final-eq) (trans reg-eq pair-loc-eq-final)

      ------------------------------------------------------------------------
      -- fst-preserved-final: show fst-slot still contains fst-loc
      --
      -- fst-slot is written by store-at-slot fst-slot in middle-trace.
      -- Need to show subsequent instructions don't overwrite it:
      -- - restore-input: only modifies Input register
      -- - g-trace: writes below reclaim-g = fst-slot (TraceWritesBelow)
      -- - store-at-slot snd-slot: snd-slot = suc fst-slot ≠ fst-slot
      -- - lea-slot: only modifies registers
      ------------------------------------------------------------------------

      -- PROVEN using trace preservation lemmas
      -- Strategy: Show fst-slot preserved through final-trace (store-at-slot snd-slot, lea-slot)
      -- and was written correctly before final-trace

      -- snd-slot ≠ fst-slot (needed for store-at-slot snd-slot preservation)
      -- snd-slot = suc fst-slot, so suc fst-slot ≢ fst-slot
      -- Use <⇒≢: fst-slot < snd-slot implies fst-slot ≢ snd-slot, then flip
      -- fst-slot < snd-slot means suc fst-slot ≤ snd-slot = suc fst-slot, i.e., ≤-refl
      snd≢fst : snd-slot ≢ fst-slot
      snd≢fst eq = <⇒≢ ≤-refl (sym eq)

      -- frame equality through execution (needed for disjointness proofs)
      frame-eq-before-final : current-frame alloc-before-final ≡ frame
      frame-eq-before-final = frame-preserved-trace

      -- OnStack frame snd-slot ≢ OnStack frame fst-slot because snd-slot ≢ fst-slot
      snd-loc-neq-fst : OnStack (current-frame alloc-before-final) snd-slot ≢ fst-loc-stack
      snd-loc-neq-fst eq = snd≢fst (cong slot-of eq'')
        where
          -- First convert to same frame
          eq' : OnStack (current-frame alloc-before-final) snd-slot ≡ OnStack frame fst-slot
          eq' = eq
          -- Use frame equality to get OnStack frame snd-slot ≡ OnStack frame fst-slot
          eq'' : OnStack frame snd-slot ≡ OnStack frame fst-slot
          eq'' = subst (λ f → OnStack f snd-slot ≡ OnStack frame fst-slot) frame-eq-before-final eq'

      -- store-at-slot snd-slot preserves fst-slot (disjoint slots)
      -- Need to relate s-after-snd-store (defined via exec-trace) to exec-abstract
      snd-store-preserves-fst : readLoc s-after-snd-store fst-loc-stack ≡ readLoc s-before-final fst-loc-stack
      snd-store-preserves-fst =
        let
          -- exec-trace (i ∷ []) ≡ exec-abstract i when not halted
          trace-to-abstract : proj₁ (exec-trace (store-at-slot snd-slot ∷ []) s-before-final alloc-before-final) ≡
                              proj₁ (exec-abstract (store-at-slot snd-slot) s-before-final alloc-before-final)
          trace-to-abstract = cong proj₁ (exec-trace-single (store-at-slot snd-slot) s-before-final alloc-before-final not-halted-before-final)
          -- store-at-slot-preserves-disjoint gives us the exec-abstract version
          abstract-preserves : readLoc (proj₁ (exec-abstract (store-at-slot snd-slot) s-before-final alloc-before-final)) fst-loc-stack ≡
                               readLoc s-before-final fst-loc-stack
          abstract-preserves = store-at-slot-preserves-disjoint snd-slot s-before-final alloc-before-final fst-loc-stack snd-loc-neq-fst
        in trans (cong (λ st → readLoc st fst-loc-stack) trace-to-abstract) abstract-preserves

      -- lea-slot preserves fst-slot (only modifies registers)
      lea-preserves-fst : readLoc (proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final)) fst-loc-stack ≡
                          readLoc s-after-snd-store fst-loc-stack
      lea-preserves-fst = lea-slot-preserves-readLoc fst-slot s-after-snd-store alloc-before-final fst-loc-stack not-halted-after-snd-store

      -- final-trace preserves fst-slot
      final-trace-preserves-fst : readLoc (proj₁ (exec-trace final-trace s-before-final alloc-before-final)) fst-loc-stack ≡
                                  readLoc s-before-final fst-loc-stack
      final-trace-preserves-fst = trans (trans
        (cong (λ st → readLoc st fst-loc-stack) final-trace-decomp)
        lea-preserves-fst)
        snd-store-preserves-fst

      ------------------------------------------------------------------------
      -- Show fst-slot contains fst-loc in s-before-final
      -- Need to track through: store-at-slot fst-slot writes fst-loc, then restore-input and g-trace preserve
      ------------------------------------------------------------------------
      fst-in-s-before-final : readLoc s-before-final fst-loc-stack ≡ just fst-loc
      fst-in-s-before-final = g-preserves-fst-composed
        where
          -- g-trace writes below reclaim-g = fst-slot, so preserves fst-slot
          -- Use g-preserves-fst with s-before-g
          g-preserves-fst-in-s-before-g : readLoc (proj₁ (exec-trace g-trace s-before-g alloc-before-g)) fst-loc-stack ≡
                                          readLoc s-before-g fst-loc-stack
          g-preserves-fst-in-s-before-g =
            let
              -- Use same-frame lemma to relate alloc-before-g and alloc₁-reclaimed
              same-state : proj₁ (exec-trace g-trace s-before-g alloc-before-g) ≡
                           proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed)
              same-state = exec-trace-state-same-frame g-trace s-before-g alloc-before-g alloc₁-reclaimed
                             alloc-frame-eq alloc-cap-eq
            in trans (cong (λ st → readLoc st fst-loc-stack) same-state)
                     (g-preserves-fst s-before-g)

          -- Need to show fst-slot contains fst-loc in s-before-g
          -- s-before-g is after store-at-slot fst-slot (which writes Output = fst-loc)
          -- followed by restore-input (which only changes Input register)
          --
          -- Structure: prefix-before-g = setup ++ f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
          -- We decompose and track fst-slot through each segment.
          fst-written-in-s-before-g : readLoc s-before-g fst-loc-stack ≡ just fst-loc
          fst-written-in-s-before-g =
            let
              -- Decompose prefix-before-g into: before-store ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
              before-store : AbstractTrace
              before-store = mov-to-output ∷ store-at-slot backup-slot ∷ f-trace

              -- State after before-store (just before store-at-slot fst-slot)
              s-before-store : LocState FS
              s-before-store = proj₁ (exec-trace before-store s alloc)

              alloc-before-store : AllocState {FS}
              alloc-before-store = proj₂ (exec-trace before-store s alloc)

              -- prefix-before-g = before-store ++ (store-at-slot fst-slot ∷ restore-input backup-slot ∷ [])
              -- This is definitionally true since middle-before-g = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []

              -- Show Output = fst-loc before store-at-slot
              -- PROVEN using state equivalence: f-trace on s-after-setup ≈ f-trace on s (for Output)

              -- before-store = setup-trace ++ f-trace
              -- s-before-store = exec f-trace (exec setup-trace s) alloc-after-setup
              s-before-store-decomp : s-before-store ≡ proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)
              s-before-store-decomp = exec-trace-append-state setup-trace f-trace s alloc

              -- alloc-after-setup has same frame and capacity as alloc (setup preserves both)
              alloc-after-setup-frame-eq : current-frame alloc-after-setup ≡ current-frame alloc
              alloc-after-setup-frame-eq = exec-trace-preserves-frame setup-trace s alloc

              alloc-after-setup-cap-eq : frame-capacity alloc-after-setup ≡ frame-capacity alloc
              alloc-after-setup-cap-eq = exec-trace-preserves-capacity' setup-trace s alloc setup-tpc

              -- s-after-setup has same Input as s (mov-to-output doesn't change Input)
              -- and differs from s only in Output register and backup-slot
              input-after-setup : readReg (regs s-after-setup) Input ≡ input-loc
              input-after-setup =
                let
                  -- mov-to-output doesn't change Input (writeReg r Output v preserves input field)
                  s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
                  input-after-mov : readReg (regs s-after-mov) Input ≡ input-loc
                  input-after-mov = trans
                    (cong (λ st → readReg (regs st) Input) (mov-to-output-state-eq s alloc not-halted))
                    rdi-eq  -- readReg (writeReg r Output v) Input = readReg r Input by definition
                  -- store-at-slot doesn't change registers
                  s-after-store = proj₁ (exec-trace (store-at-slot backup-slot ∷ [])
                                          s-after-mov (proj₂ (exec-trace (mov-to-output ∷ []) s alloc)))
                  -- halted preserved through mov-to-output
                  not-halted-after-mov : halted s-after-mov ≡ false
                  not-halted-after-mov = trans
                    (cong halted (mov-to-output-state-eq s alloc not-halted))
                    not-halted
                in trans (cong (λ st → readReg (regs st) Input)
                           (exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc))
                         (trans (cong (λ st → readReg (regs st) Input)
                                  (store-at-slot-state-eq backup-slot s-after-mov
                                    (proj₂ (exec-trace (mov-to-output ∷ []) s alloc)) not-halted-after-mov))
                                (trans (cong (λ r → readReg r Input)
                                         (writeLoc-regs s-after-mov
                                           (OnStack (current-frame (proj₂ (exec-trace (mov-to-output ∷ []) s alloc))) backup-slot)
                                           (readReg (regs s-after-mov) Output)))
                                       input-after-mov))

              -- s and s-after-setup agree on slots in [suc backup-slot, reclaim-f)
              -- s-after-setup only modified backup-slot = next-slot alloc
              slots-eq-for-f : ∀ slot → suc backup-slot ≤ slot → slot < reclaim-f →
                readLoc s-after-setup (OnStack (current-frame alloc-after-backup) slot) ≡
                readLoc s (OnStack (current-frame alloc-after-backup) slot)
              slots-eq-for-f slot lo hi =
                let
                  -- Store-at-slot backup-slot only writes to backup-slot
                  -- Slots ≥ suc backup-slot are preserved because all writes are < suc backup-slot
                  setup-writes-below : TraceWritesBelow (suc backup-slot) setup-trace
                  setup-writes-below = ≤-refl , tt  -- backup-slot < suc backup-slot, rest is tt
                in exec-trace-preserves-slot-above setup-trace s alloc
                     (current-frame alloc) slot (suc backup-slot)
                     refl lo setup-writes-below

              -- Same-frame chain: alloc-after-setup → alloc → alloc-after-backup
              -- Step 1: alloc-after-setup has same frame/capacity as alloc
              f-same-frame-step1 : proj₁ (exec-trace f-trace s-after-setup alloc-after-setup) ≡
                                   proj₁ (exec-trace f-trace s-after-setup alloc)
              f-same-frame-step1 = exec-trace-state-same-frame f-trace s-after-setup alloc-after-setup alloc
                                     alloc-after-setup-frame-eq alloc-after-setup-cap-eq

              -- Step 2: alloc has same frame/capacity as alloc-after-backup (only next-slot differs)
              f-same-frame-step2 : proj₁ (exec-trace f-trace s-after-setup alloc) ≡
                                   proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)
              f-same-frame-step2 = exec-trace-state-same-frame f-trace s-after-setup alloc alloc-after-backup
                                     refl  -- same frame
                                     refl  -- same capacity

              -- Combined: alloc-after-setup → alloc-after-backup
              f-same-frame : proj₁ (exec-trace f-trace s-after-setup alloc-after-setup) ≡
                             proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)
              f-same-frame = trans f-same-frame-step1 f-same-frame-step2

              -- Use exec-trace-output-equiv to show Output is same as when running on s
              -- Need: Input same, slots in [suc backup-slot, reclaim-f) same
              output-equiv : readReg (regs (proj₁ (exec-trace f-trace s-after-setup alloc-after-backup))) Output ≡
                             readReg (regs (proj₁ (exec-trace f-trace s alloc-after-backup))) Output
              output-equiv = exec-trace-output-equiv f-trace s-after-setup s alloc-after-backup
                               (suc backup-slot) reclaim-f
                               (trans input-after-setup (sym rdi-eq))
                               (trans not-halted-after-setup (sym not-halted))  -- halted s-after-setup ≡ halted s
                               not-halted-after-setup
                               slots-eq-for-f
                               f-slot-reads
                               (IRResultAWF.trace-slot-reads-below result-f)

              -- From f-correct: proj₁ (exec-trace f-trace s alloc-after-backup) ≡ s₁
              -- From rax-f: readReg (regs s₁) Output ≡ fst-loc
              output-before-store-is-fst : readReg (regs s-before-store) Output ≡ fst-loc
              output-before-store-is-fst =
                trans (cong (λ st → readReg (regs st) Output) s-before-store-decomp)
                      (trans (cong (λ st → readReg (regs st) Output) f-same-frame)
                             (trans output-equiv (trans (cong (λ st → readReg (regs st) Output) f-correct) rax-f)))

              -- Halted preservation through before-store
              not-halted-before-store : halted s-before-store ≡ false
              not-halted-before-store =
                let
                  -- Use halted equivalence: f-trace preserves halted on equivalent states
                  halted-equiv : halted (proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)) ≡ false
                  halted-equiv = exec-trace-preserves-halted-subir f-trace s-after-setup s alloc-after-backup
                                   (suc backup-slot) reclaim-f
                                   (trans input-after-setup (sym rdi-eq))
                                   slots-eq-for-f
                                   f-slot-reads
                                   (IRResultAWF.trace-slot-reads-below result-f)
                                   not-halted-after-setup
                                   not-halted
                                   (subst (λ st → halted st ≡ false) (sym f-correct) (IRResultAWF.not-halted result-f))
                in trans (cong halted s-before-store-decomp)
                         (trans (cong halted f-same-frame) halted-equiv)

              -- State after store-at-slot fst-slot
              s-after-fst-store : LocState FS
              s-after-fst-store = proj₁ (exec-trace (store-at-slot fst-slot ∷ []) s-before-store alloc-before-store)

              -- Frame preserved through before-store
              frame-eq-before-store : current-frame alloc-before-store ≡ frame
              frame-eq-before-store = exec-trace-preserves-frame before-store s alloc

              -- store-at-slot writes Output to fst-slot (in alloc-before-store's frame)
              fst-after-store-raw : readLoc s-after-fst-store (OnStack (current-frame alloc-before-store) fst-slot) ≡
                                    just (readReg (regs s-before-store) Output)
              fst-after-store-raw = store-at-slot-reads-back fst-slot s-before-store alloc-before-store not-halted-before-store

              -- Convert to fst-loc-stack frame and fst-loc value
              fst-loc-eq : OnStack (current-frame alloc-before-store) fst-slot ≡ fst-loc-stack
              fst-loc-eq = cong (λ f → OnStack f fst-slot) frame-eq-before-store

              fst-after-store : readLoc s-after-fst-store fst-loc-stack ≡ just fst-loc
              fst-after-store = trans
                (subst (λ loc → readLoc s-after-fst-store loc ≡ just (readReg (regs s-before-store) Output))
                       fst-loc-eq fst-after-store-raw)
                (cong just output-before-store-is-fst)

              -- restore-input preserves fst-slot (only modifies Input register)
              not-halted-after-fst-store : halted s-after-fst-store ≡ false
              not-halted-after-fst-store = subst (λ st → halted st ≡ false)
                (sym (store-at-slot-state-eq fst-slot s-before-store alloc-before-store not-halted-before-store))
                not-halted-before-store

              alloc-after-fst-store : AllocState {FS}
              alloc-after-fst-store = proj₂ (exec-trace (store-at-slot fst-slot ∷ []) s-before-store alloc-before-store)

              -- backup-slot contains input-loc (written at start, preserved through f-trace and store-at-slot fst-slot)
              -- PROVEN: trace through setup → f-trace → store-at-slot fst-slot
              backup-has-input : readLoc s-after-fst-store (OnStack (current-frame alloc-after-fst-store) backup-slot) ≡ just input-loc
              backup-has-input =
                let
                  -- Step 1: After setup, backup-slot contains input-loc
                  -- setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
                  -- After mov-to-output: Output = Input = input-loc
                  -- After store-at-slot backup-slot: backup-slot contains Output = input-loc
                  backup-after-setup : readLoc s-after-setup (OnStack (current-frame alloc) backup-slot) ≡ just input-loc
                  backup-after-setup =
                    let
                      s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
                      alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
                      not-halted-after-mov : halted s-after-mov ≡ false
                      not-halted-after-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
                      -- Output after mov = Input = input-loc
                      output-after-mov : readReg (regs s-after-mov) Output ≡ input-loc
                      output-after-mov = trans (mov-to-output-sets-output s alloc not-halted) rdi-eq
                      -- store-at-slot backup-slot writes Output to backup-slot
                      s-after-store-on-mov = proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)
                      backup-written : readLoc s-after-store-on-mov (OnStack (current-frame alloc-after-mov) backup-slot) ≡
                                       just (readReg (regs s-after-mov) Output)
                      backup-written = store-at-slot-reads-back backup-slot s-after-mov alloc-after-mov not-halted-after-mov
                      -- s-after-setup = s-after-store-on-mov
                      setup-decomp : s-after-setup ≡ s-after-store-on-mov
                      setup-decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
                      -- Frame unchanged through mov
                      frame-after-mov : current-frame alloc-after-mov ≡ current-frame alloc
                      frame-after-mov = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
                    in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) setup-decomp)
                             (trans (subst (λ f → readLoc s-after-store-on-mov (OnStack f backup-slot) ≡
                                                  just (readReg (regs s-after-mov) Output))
                                           frame-after-mov backup-written)
                                    (cong just output-after-mov))

                  -- Step 2: f-trace preserves backup-slot (writes above suc backup-slot)
                  -- Use exec-trace-preserves-slot-above with TraceWritesBelow (suc backup-slot)
                  -- Actually f-trace writes ABOVE suc backup-slot, so backup-slot (< suc backup-slot) is preserved
                  f-preserves-backup : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)) (OnStack (current-frame alloc) backup-slot) ≡
                                       readLoc s-after-setup (OnStack (current-frame alloc) backup-slot)
                  f-preserves-backup =
                    let
                      -- f-trace writes to slots ≥ suc backup-slot (from trace-writes-above)
                      -- backup-slot < suc backup-slot, so backup-slot is preserved
                      f-writes-above : TraceWritesAbove (suc backup-slot) f-trace
                      f-writes-above = IRResultAWF.trace-writes-above result-f
                      -- backup-slot is disjoint from all write locations (using alloc-after-setup frame)
                      backup-disjoint : ∀ slot' → suc backup-slot ≤ slot' →
                                        OnStack (current-frame alloc-after-setup) slot' ≢ OnStack (current-frame alloc) backup-slot
                      backup-disjoint slot' bound eq =
                        let slot-eq : slot' ≡ backup-slot
                            slot-eq = cong slot-of (trans (cong (λ f → OnStack f slot') (sym alloc-after-setup-frame-eq)) eq)
                        in <⇒≢ bound (sym slot-eq)
                    in exec-trace-preserves-disjoint f-trace s-after-setup alloc-after-setup
                         (OnStack (current-frame alloc) backup-slot) (suc backup-slot)
                         (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-writes-above)
                         backup-disjoint

                  -- before-store = setup ++ f-trace, so s-before-store = exec f-trace s-after-setup
                  s-before-store-via-setup : s-before-store ≡ proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)
                  s-before-store-via-setup = s-before-store-decomp

                  -- backup preserved from s-after-setup to s-before-store
                  backup-at-before-store : readLoc s-before-store (OnStack (current-frame alloc) backup-slot) ≡ just input-loc
                  backup-at-before-store = trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) s-before-store-via-setup)
                                                 (trans f-preserves-backup backup-after-setup)

                  -- Step 3: store-at-slot fst-slot preserves backup-slot (fst-slot ≠ backup-slot)
                  fst-neq-backup : fst-slot ≢ backup-slot
                  fst-neq-backup eq = <⇒≢ (≤-trans (IRResultAWF.reclaim-monotone result-f)
                                                   (IRResultAWF.reclaim-monotone result-g)) (sym eq)

                  -- Frame preserved through before-store
                  frame-before-store : current-frame alloc-before-store ≡ current-frame alloc
                  frame-before-store = exec-trace-preserves-frame before-store s alloc

                  -- Frame preserved through store-at-slot fst-slot
                  frame-after-fst : current-frame alloc-after-fst-store ≡ current-frame alloc
                  frame-after-fst = trans (exec-trace-preserves-frame (store-at-slot fst-slot ∷ []) s-before-store alloc-before-store)
                                          frame-before-store

                  -- store-at-slot fst-slot preserves backup-slot
                  fst-store-preserves-backup : readLoc s-after-fst-store (OnStack (current-frame alloc) backup-slot) ≡
                                               readLoc s-before-store (OnStack (current-frame alloc) backup-slot)
                  fst-store-preserves-backup =
                    let
                      loc-neq : OnStack (current-frame alloc-before-store) fst-slot ≢ OnStack (current-frame alloc) backup-slot
                      loc-neq eq = fst-neq-backup (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f backup-slot) (sym frame-before-store))))
                      -- Convert from exec-trace to exec-abstract via exec-trace-single
                      s-after-fst-via-abstract : s-after-fst-store ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-before-store alloc-before-store)
                      s-after-fst-via-abstract = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-before-store alloc-before-store not-halted-before-store)
                      -- Apply the preservation lemma
                      abstract-preserves : readLoc (proj₁ (exec-abstract (store-at-slot fst-slot) s-before-store alloc-before-store)) (OnStack (current-frame alloc) backup-slot) ≡
                                           readLoc s-before-store (OnStack (current-frame alloc) backup-slot)
                      abstract-preserves = store-at-slot-preserves-disjoint fst-slot s-before-store alloc-before-store (OnStack (current-frame alloc) backup-slot) loc-neq
                    in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) s-after-fst-via-abstract) abstract-preserves

                in trans (cong (λ f → readLoc s-after-fst-store (OnStack f backup-slot)) frame-after-fst)
                         (trans fst-store-preserves-backup backup-at-before-store)

              restore-preserves-fst : readLoc (proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store)) fst-loc-stack ≡
                                      readLoc s-after-fst-store fst-loc-stack
              restore-preserves-fst = restore-input-preserves-readLoc backup-slot s-after-fst-store alloc-after-fst-store input-loc fst-loc-stack not-halted-after-fst-store backup-has-input

              -- Compose: s-before-g = exec (restore-input) (exec (store fst) s-before-store)
              s-before-g-decomp : s-before-g ≡ proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store)
              s-before-g-decomp =
                let
                  -- prefix-before-g = before-store ++ (store-at-slot fst-slot ∷ restore-input backup-slot ∷ [])
                  step1 : proj₁ (exec-trace prefix-before-g s alloc) ≡
                          proj₁ (exec-trace (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s-before-store alloc-before-store)
                  step1 = exec-trace-append-state before-store (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s alloc

                  -- (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) =
                  -- (store-at-slot fst-slot ∷ []) ++ (restore-input backup-slot ∷ [])
                  step2 : proj₁ (exec-trace (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s-before-store alloc-before-store) ≡
                          proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store)
                  step2 = exec-trace-append-state (store-at-slot fst-slot ∷ []) (restore-input backup-slot ∷ []) s-before-store alloc-before-store
                in trans step1 step2

            in trans (cong (λ st → readLoc st fst-loc-stack) s-before-g-decomp)
                     (trans restore-preserves-fst fst-after-store)

          g-preserves-fst-composed : readLoc s-before-final fst-loc-stack ≡ just fst-loc
          g-preserves-fst-composed = trans
            (cong (λ st → readLoc st fst-loc-stack) s-before-final-via-g)
            (trans g-preserves-fst-in-s-before-g fst-written-in-s-before-g)

      -- PROVEN: fst-preserved-final
      fst-preserved-final : readLoc s-final fst-loc-stack ≡ just fst-loc
      fst-preserved-final = trans
        (cong (λ st → readLoc st fst-loc-stack) s-final-decomp)
        (trans final-trace-preserves-fst fst-in-s-before-final)

      ------------------------------------------------------------------------
      -- snd-written: show snd-slot contains snd-loc
      --
      -- snd-slot is written by store-at-slot snd-slot right before lea-slot.
      -- Only lea-slot follows, which doesn't modify memory.
      ------------------------------------------------------------------------

      -- snd-slot location in final frame
      snd-loc-stack-eq : snd-loc-stack ≡ OnStack (current-frame alloc-before-final) snd-slot
      snd-loc-stack-eq = cong (λ f → OnStack f snd-slot) (sym frame-preserved-trace)

      -- Output before final-trace contains snd-loc (result of g-trace)
      -- Strategy: Use state equivalence to show g-trace produces same Output
      -- whether starting from s-before-g or s₁'.
      output-before-final-is-snd : readReg (regs s-before-final) Output ≡ snd-loc
      output-before-final-is-snd =
        let
          -- Step 1: s-before-final = exec g-trace s-before-g alloc-before-g
          -- Then use same-frame to relate to alloc₁-reclaimed
          state-via-g : proj₁ (exec-trace g-trace s-before-g alloc-before-g) ≡
                        proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed)
          state-via-g = exec-trace-state-same-frame g-trace s-before-g alloc-before-g alloc₁-reclaimed
                          alloc-frame-eq alloc-cap-eq

          -- Step 2: Show s-before-g and s₁' satisfy state equivalence conditions
          -- Need: same Input, same halted, same slots in [reclaim-f, reclaim-g)

          -- Decompose prefix-before-g to trace Input and halted through
          before-store-here : AbstractTrace
          before-store-here = mov-to-output ∷ store-at-slot backup-slot ∷ f-trace

          s-before-store-here : LocState FS
          s-before-store-here = proj₁ (exec-trace before-store-here s alloc)

          alloc-before-store-here : AllocState {FS}
          alloc-before-store-here = proj₂ (exec-trace before-store-here s alloc)

          s-after-fst-store-here : LocState FS
          s-after-fst-store-here = proj₁ (exec-trace (store-at-slot fst-slot ∷ []) s-before-store-here alloc-before-store-here)

          alloc-after-fst-store-here : AllocState {FS}
          alloc-after-fst-store-here = proj₂ (exec-trace (store-at-slot fst-slot ∷ []) s-before-store-here alloc-before-store-here)

          -- s-before-g = exec (restore-input) s-after-fst-store
          s-before-g-decomp-here : s-before-g ≡ proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-fst-store-here alloc-after-fst-store-here)
          s-before-g-decomp-here =
            let
              step1 : proj₁ (exec-trace prefix-before-g s alloc) ≡
                      proj₁ (exec-trace (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s-before-store-here alloc-before-store-here)
              step1 = exec-trace-append-state before-store-here (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s alloc
              step2 : proj₁ (exec-trace (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s-before-store-here alloc-before-store-here) ≡
                      proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-fst-store-here alloc-after-fst-store-here)
              step2 = exec-trace-append-state (store-at-slot fst-slot ∷ []) (restore-input backup-slot ∷ []) s-before-store-here alloc-before-store-here
            in trans step1 step2

          -- Trace halted=false through setup
          setup-here : AbstractTrace
          setup-here = mov-to-output ∷ store-at-slot backup-slot ∷ []

          s-after-setup-here : LocState FS
          s-after-setup-here = proj₁ (exec-trace setup-here s alloc)

          alloc-after-setup-here : AllocState {FS}
          alloc-after-setup-here = proj₂ (exec-trace setup-here s alloc)

          -- Manual halted preservation through setup
          s-after-mov-setup : LocState FS
          s-after-mov-setup = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)

          alloc-after-mov-setup : AllocState {FS}
          alloc-after-mov-setup = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)

          not-halted-after-mov-setup : halted s-after-mov-setup ≡ false
          not-halted-after-mov-setup = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted

          setup-decomp : s-after-setup-here ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov-setup alloc-after-mov-setup)
          setup-decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc

          not-halted-after-setup-here : halted s-after-setup-here ≡ false
          not-halted-after-setup-here =
            trans (cong halted setup-decomp)
                  (subst (λ st → halted st ≡ false)
                         (sym (store-at-slot-state-eq backup-slot s-after-mov-setup alloc-after-mov-setup not-halted-after-mov-setup))
                         not-halted-after-mov-setup)

          -- s-before-store-here = exec f-trace s-after-setup-here
          s-before-store-here-decomp : s-before-store-here ≡ proj₁ (exec-trace f-trace s-after-setup-here alloc-after-setup-here)
          s-before-store-here-decomp = exec-trace-append-state setup-here f-trace s alloc

          -- Prove via exec-trace-preserves-halted-subir + exec-trace-state-same-frame
          not-halted-before-store-here : halted s-before-store-here ≡ false
          not-halted-before-store-here =
            let
              -- alloc-after-setup-here has same frame/capacity as alloc (and thus alloc-after-backup)
              setup-here-frame-eq : current-frame alloc-after-setup-here ≡ current-frame alloc
              setup-here-frame-eq = exec-trace-preserves-frame setup-here s alloc

              setup-here-cap-eq : frame-capacity alloc-after-setup-here ≡ frame-capacity alloc
              setup-here-cap-eq = exec-trace-preserves-capacity' setup-here s alloc setup-tpc

              -- Input equivalence: s-after-setup-here has same Input as s
              input-after-setup-here' : readReg (regs s-after-setup-here) Input ≡ input-loc
              input-after-setup-here' =
                let
                  input-after-mov' : readReg (regs s-after-mov-setup) Input ≡ input-loc
                  input-after-mov' = trans (cong (λ st → readReg (regs st) Input) (mov-to-output-state-eq s alloc not-halted)) rdi-eq
                in trans (cong (λ st → readReg (regs st) Input) setup-decomp)
                         (trans (cong (λ st → readReg (regs st) Input)
                                  (store-at-slot-state-eq backup-slot s-after-mov-setup alloc-after-mov-setup not-halted-after-mov-setup))
                                (trans (cong (λ r → readReg r Input)
                                         (writeLoc-regs s-after-mov-setup
                                           (OnStack (current-frame alloc-after-mov-setup) backup-slot)
                                           (readReg (regs s-after-mov-setup) Output)))
                                       input-after-mov'))

              -- Slots equivalence: [suc backup-slot, reclaim-f) are same in s-after-setup-here and s
              slots-eq-here : ∀ slot → suc backup-slot ≤ slot → slot < reclaim-f →
                readLoc s-after-setup-here (OnStack (current-frame alloc-after-backup) slot) ≡
                readLoc s (OnStack (current-frame alloc-after-backup) slot)
              slots-eq-here slot lo hi =
                let
                  loc = OnStack (current-frame alloc) slot
                  -- setup-here writes only to backup-slot, which is < suc backup-slot ≤ slot
                  mov-preserves'' : readLoc s-after-mov-setup loc ≡ readLoc s loc
                  mov-preserves'' = mov-to-output-preserves-readLoc s alloc loc not-halted
                  frame-after-mov'' : current-frame alloc-after-mov-setup ≡ current-frame alloc
                  frame-after-mov'' = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
                  backup-neq-slot' : backup-slot ≢ slot
                  backup-neq-slot' eq = <⇒≢ lo eq
                  loc-neq'' : OnStack (current-frame alloc-after-mov-setup) backup-slot ≢ loc
                  loc-neq'' eq' = backup-neq-slot' (trans (cong slot-of eq') (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-mov''))))
                  store-preserves'' : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov-setup alloc-after-mov-setup)) loc ≡
                                      readLoc s-after-mov-setup loc
                  store-preserves'' = store-at-slot-preserves-disjoint backup-slot s-after-mov-setup alloc-after-mov-setup loc loc-neq''
                  store-via-abstract'' : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov-setup alloc-after-mov-setup) ≡
                                         proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov-setup alloc-after-mov-setup)
                  store-via-abstract'' = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov-setup alloc-after-mov-setup not-halted-after-mov-setup)
                in trans (cong (λ st → readLoc st loc) setup-decomp)
                         (trans (cong (λ st → readLoc st loc) store-via-abstract'')
                                (trans store-preserves'' mov-preserves''))

              -- Use exec-trace-state-same-frame for alloc equivalence
              f-here-same-frame : proj₁ (exec-trace f-trace s-after-setup-here alloc-after-setup-here) ≡
                                  proj₁ (exec-trace f-trace s-after-setup-here alloc-after-backup)
              f-here-same-frame = exec-trace-state-same-frame f-trace s-after-setup-here alloc-after-setup-here alloc-after-backup
                                    setup-here-frame-eq setup-here-cap-eq

              -- Use exec-trace-preserves-halted-subir
              halted-f-equiv : halted (proj₁ (exec-trace f-trace s-after-setup-here alloc-after-backup)) ≡ false
              halted-f-equiv = exec-trace-preserves-halted-subir f-trace s-after-setup-here s alloc-after-backup
                                 (suc backup-slot) reclaim-f
                                 (trans input-after-setup-here' (sym rdi-eq))
                                 slots-eq-here
                                 f-slot-reads
                                 (IRResultAWF.trace-slot-reads-below result-f)
                                 not-halted-after-setup-here
                                 not-halted
                                 (subst (λ st → halted st ≡ false) (sym f-correct) (IRResultAWF.not-halted result-f))
            in trans (cong halted s-before-store-here-decomp)
                     (trans (cong halted f-here-same-frame) halted-f-equiv)

          -- store-at-slot preserves halted
          not-halted-after-fst-store-here : halted s-after-fst-store-here ≡ false
          not-halted-after-fst-store-here =
            subst (λ st → halted st ≡ false)
              (sym (store-at-slot-state-eq fst-slot s-before-store-here alloc-before-store-here not-halted-before-store-here))
              not-halted-before-store-here

          -- First prove backup-slot contains input-loc at s-after-fst-store-here
          -- (needed for restore-input halted preservation below)
          frame-before-store-here : current-frame alloc-before-store-here ≡ current-frame alloc
          frame-before-store-here = exec-trace-preserves-frame before-store-here s alloc

          frame-after-fst-here : current-frame alloc-after-fst-store-here ≡ current-frame alloc
          frame-after-fst-here = trans (exec-trace-preserves-frame (store-at-slot fst-slot ∷ []) s-before-store-here alloc-before-store-here)
                                       frame-before-store-here

          backup-has-input-here : readLoc s-after-fst-store-here (OnStack (current-frame alloc-after-fst-store-here) backup-slot) ≡ just input-loc
          backup-has-input-here =
            let
              -- backup-slot written at start by setup, preserved through f-trace and store fst

              -- Step 1: After setup, backup-slot contains input-loc
              s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              not-halted-after-mov : halted s-after-mov ≡ false
              not-halted-after-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              output-after-mov : readReg (regs s-after-mov) Output ≡ input-loc
              output-after-mov = trans (mov-to-output-sets-output s alloc not-halted) rdi-eq
              s-after-store-on-mov = proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)
              backup-written : readLoc s-after-store-on-mov (OnStack (current-frame alloc-after-mov) backup-slot) ≡
                               just (readReg (regs s-after-mov) Output)
              backup-written = store-at-slot-reads-back backup-slot s-after-mov alloc-after-mov not-halted-after-mov
              setup-decomp' : s-after-setup-here ≡ s-after-store-on-mov
              setup-decomp' = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              frame-after-mov : current-frame alloc-after-mov ≡ current-frame alloc
              frame-after-mov = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc

              backup-after-setup : readLoc s-after-setup-here (OnStack (current-frame alloc) backup-slot) ≡ just input-loc
              backup-after-setup = trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) setup-decomp')
                                         (trans (subst (λ f → readLoc s-after-store-on-mov (OnStack f backup-slot) ≡
                                                              just (readReg (regs s-after-mov) Output))
                                                       frame-after-mov backup-written)
                                                (cong just output-after-mov))

              -- Step 2: f-trace preserves backup-slot (writes above suc backup-slot)
              alloc-after-setup-frame-eq : current-frame alloc-after-setup-here ≡ current-frame alloc
              alloc-after-setup-frame-eq = exec-trace-preserves-frame setup-here s alloc

              f-writes-above : TraceWritesAbove (suc backup-slot) f-trace
              f-writes-above = IRResultAWF.trace-writes-above result-f
              backup-disjoint : ∀ slot' → suc backup-slot ≤ slot' →
                                OnStack (current-frame alloc-after-setup-here) slot' ≢ OnStack (current-frame alloc) backup-slot
              backup-disjoint slot' bound eq =
                let slot-eq : slot' ≡ backup-slot
                    slot-eq = cong slot-of (trans (cong (λ f → OnStack f slot') (sym alloc-after-setup-frame-eq)) eq)
                in <⇒≢ bound (sym slot-eq)

              f-preserves-backup : readLoc (proj₁ (exec-trace f-trace s-after-setup-here alloc-after-setup-here)) (OnStack (current-frame alloc) backup-slot) ≡
                                   readLoc s-after-setup-here (OnStack (current-frame alloc) backup-slot)
              f-preserves-backup = exec-trace-preserves-disjoint f-trace s-after-setup-here alloc-after-setup-here
                                     (OnStack (current-frame alloc) backup-slot) (suc backup-slot)
                                     (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-writes-above)
                                     backup-disjoint

              -- Step 3: store-at-slot fst-slot preserves backup-slot
              backup-at-before-store : readLoc s-before-store-here (OnStack (current-frame alloc) backup-slot) ≡ just input-loc
              backup-at-before-store = trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) s-before-store-here-decomp)
                                             (trans f-preserves-backup backup-after-setup)

              fst-neq-backup : fst-slot ≢ backup-slot
              fst-neq-backup eq = <⇒≢ (≤-trans (IRResultAWF.reclaim-monotone result-f)
                                               (IRResultAWF.reclaim-monotone result-g)) (sym eq)

              loc-neq : OnStack (current-frame alloc-before-store-here) fst-slot ≢ OnStack (current-frame alloc) backup-slot
              loc-neq eq = fst-neq-backup (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f backup-slot) (sym frame-before-store-here))))

              s-after-fst-via-abstract : s-after-fst-store-here ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-before-store-here alloc-before-store-here)
              s-after-fst-via-abstract = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-before-store-here alloc-before-store-here not-halted-before-store-here)

              abstract-preserves : readLoc (proj₁ (exec-abstract (store-at-slot fst-slot) s-before-store-here alloc-before-store-here)) (OnStack (current-frame alloc) backup-slot) ≡
                                   readLoc s-before-store-here (OnStack (current-frame alloc) backup-slot)
              abstract-preserves = store-at-slot-preserves-disjoint fst-slot s-before-store-here alloc-before-store-here (OnStack (current-frame alloc) backup-slot) loc-neq

              fst-store-preserves-backup : readLoc s-after-fst-store-here (OnStack (current-frame alloc) backup-slot) ≡
                                           readLoc s-before-store-here (OnStack (current-frame alloc) backup-slot)
              fst-store-preserves-backup = trans (cong (λ st → readLoc st (OnStack (current-frame alloc) backup-slot)) s-after-fst-via-abstract) abstract-preserves

            in trans (cong (λ f → readLoc s-after-fst-store-here (OnStack f backup-slot)) frame-after-fst-here)
                     (trans fst-store-preserves-backup backup-at-before-store)

          -- restore-input preserves halted (when slot contains valid value)
          not-halted-s-before-g : halted s-before-g ≡ false
          not-halted-s-before-g =
            let
              -- Use exec-trace-single to convert to exec-abstract
              restore-via-abstract : proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-fst-store-here alloc-after-fst-store-here) ≡
                                     proj₁ (exec-abstract (restore-input backup-slot) s-after-fst-store-here alloc-after-fst-store-here)
              restore-via-abstract = cong proj₁ (exec-trace-single (restore-input backup-slot) s-after-fst-store-here alloc-after-fst-store-here not-halted-after-fst-store-here)

              -- halted-preserved-restore-input needs the slot to contain a valid value
              halted-eq : halted (proj₁ (exec-abstract (restore-input backup-slot) s-after-fst-store-here alloc-after-fst-store-here)) ≡ halted s-after-fst-store-here
              halted-eq = halted-preserved-restore-input backup-slot s-after-fst-store-here alloc-after-fst-store-here input-loc backup-has-input-here
            in trans (cong halted s-before-g-decomp-here)
                     (trans (cong halted restore-via-abstract)
                            (trans halted-eq not-halted-after-fst-store-here))

          -- Input register after restore-input is input-loc
          input-eq-s-before-g : readReg (regs s-before-g) Input ≡ input-loc
          input-eq-s-before-g =
            trans (cong (λ st → readReg (regs st) Input) s-before-g-decomp-here)
                  (restore-input-sets-input backup-slot s-after-fst-store-here alloc-after-fst-store-here input-loc
                     not-halted-after-fst-store-here backup-has-input-here)

          input-eq : readReg (regs s-before-g) Input ≡ readReg (regs s₁') Input
          input-eq = trans input-eq-s-before-g (sym rdi-eq₁)

          not-halted-s1' : halted s₁' ≡ false
          not-halted-s1' = IRResultAWF.not-halted result-f  -- s₁' has same halted as s₁

          halted-eq : halted s-before-g ≡ halted s₁'
          halted-eq = trans not-halted-s-before-g (sym not-halted-s1')

          -- Slots in [reclaim-f, reclaim-g) are the same in both s-before-g and s₁'
          --
          -- KEY INSIGHT: fst-slot = reclaim-g (defined at line 2434)
          -- So fst-slot is NOT in [reclaim-f, reclaim-g) since slot < reclaim-g.
          --
          -- For slots in [reclaim-f, reclaim-g):
          -- - s₁' comes from exec f-trace on s with alloc-after-backup
          --   f-trace writes to [suc backup-slot, reclaim-f), doesn't write to [reclaim-f, reclaim-g)
          --   So s₁'[slot] = s[slot] for slot in [reclaim-f, reclaim-g)
          --
          -- - s-before-g comes from exec (setup ++ f-trace ++ store-fst ++ restore) on s
          --   setup writes to backup-slot only (< reclaim-f)
          --   f-trace writes to [suc backup-slot, reclaim-f)
          --   store fst-slot writes to fst-slot = reclaim-g (NOT in [reclaim-f, reclaim-g))
          --   restore writes to Input register only (not stack)
          --   So s-before-g[slot] = s[slot] for slot in [reclaim-f, reclaim-g)
          --
          -- Both equal s[slot], so they're equal.
          slots-eq : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
            readLoc s-before-g (OnStack (current-frame alloc₁-reclaimed) slot) ≡
            readLoc s₁' (OnStack (current-frame alloc₁-reclaimed) slot)
          slots-eq slot rf≤slot slot<rg =
            let
              -- Frame equality: alloc₁-reclaimed has same frame as alloc
              frame-eq-1r : current-frame alloc₁-reclaimed ≡ current-frame alloc
              frame-eq-1r = refl

              loc = OnStack (current-frame alloc) slot

              -- s₁' preserves slot from s (f-trace doesn't write to [reclaim-f, reclaim-g))
              f-writes-below : TraceWritesBelow reclaim-f f-trace
              f-writes-below = IRResultAWF.trace-writes-below result-f

              -- s₁' = record s₁ { regs = writeReg (regs s₁) Input input-loc }
              -- where s₁ = IRResultAWF.final-state result-f = exec f-trace s alloc-after-backup
              -- readLoc only looks at memory, not registers, so s₁' has same memory as s₁
              s1'-eq-s : readLoc s₁' loc ≡ readLoc s loc
              s1'-eq-s =
                let
                  -- s₁' and s₁ have same stack memory (only register differs)
                  s1'-same-mem : readLoc s₁' loc ≡ readLoc s₁ loc
                  s1'-same-mem = refl  -- readLoc reads stackMem which is unchanged

                  -- s₁ = final-state result-f = exec f-trace s alloc-after-backup
                  s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
                  s1-via-trace = sym (IRResultAWF.trace-correct result-f)

                  -- f-trace preserves slot (writes below reclaim-f, slot >= reclaim-f)
                  -- Use exec-trace-preserves-slot-above: TraceWritesBelow n → n ≤ slot → slot preserved
                  s1-eq-s : readLoc s₁ loc ≡ readLoc s loc
                  s1-eq-s = trans (cong (λ st → readLoc st loc) s1-via-trace)
                                  (exec-trace-preserves-slot-above f-trace s alloc-after-backup
                                     (current-frame alloc-after-backup) slot reclaim-f
                                     refl rf≤slot f-writes-below)
                in trans s1'-same-mem s1-eq-s

              -- s-before-g preserves slot from s (none of the operations write to [reclaim-f, reclaim-g))
              -- prefix-before-g = setup ++ f-trace ++ store fst-slot ++ restore backup-slot
              -- where setup = mov-to-output ∷ store-at-slot backup-slot ∷ []

              -- Step 1: setup doesn't write to slot (writes only to backup-slot < reclaim-f ≤ slot)
              backup-below-rf : backup-slot < reclaim-f
              backup-below-rf = IRResultAWF.reclaim-monotone result-f

              -- Step 2: f-trace doesn't write to slot (writes below reclaim-f)
              -- Step 3: store fst-slot doesn't write to slot (fst-slot = reclaim-g > slot)
              -- fst-slot = reclaim-g and slot < reclaim-g, so fst-slot ≠ slot
              fst-slot-neq-slot : fst-slot ≢ slot
              fst-slot-neq-slot eq = <⇒≢ slot<rg (sym eq)

              -- Step 4: restore doesn't write to stack

              -- Show s-before-g preserves slot from s
              s-before-g-eq-s : readLoc s-before-g loc ≡ readLoc s loc
              s-before-g-eq-s =
                -- Trace through each operation:
                -- 1. mov-to-output doesn't change stack
                -- 2. store backup-slot changes backup-slot, not slot (backup-slot < reclaim-f ≤ slot)
                -- 3. f-trace changes slots < reclaim-f, not slot
                -- 4. store fst-slot changes fst-slot = reclaim-g, not slot (slot < reclaim-g)
                -- 5. restore backup-slot doesn't change stack

                -- Use exec-trace-preserves-disjoint with TraceWritesAbove (suc slot)
                -- No wait, that doesn't work because writes are both above and below.
                -- Use the fact that writes are to specific slots, all ≠ slot.

                -- Alternative: trace preservation through each segment
                let
                  -- After setup (mov + store backup)
                  setup-segment : AbstractTrace
                  setup-segment = mov-to-output ∷ store-at-slot backup-slot ∷ []

                  s-after-setup' : LocState FS
                  s-after-setup' = proj₁ (exec-trace setup-segment s alloc)

                  alloc-after-setup' : AllocState {FS}
                  alloc-after-setup' = proj₂ (exec-trace setup-segment s alloc)

                  -- mov doesn't change stack
                  s-after-mov' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
                  alloc-after-mov' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)

                  mov-preserves : readLoc s-after-mov' loc ≡ readLoc s loc
                  mov-preserves = mov-to-output-preserves-readLoc s alloc loc not-halted

                  -- store backup-slot doesn't change slot (backup-slot ≠ slot)
                  not-halted-after-mov' : halted s-after-mov' ≡ false
                  not-halted-after-mov' = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted

                  -- backup-slot < reclaim-f ≤ slot, so backup-slot < slot
                  backup-neq-slot : backup-slot ≢ slot
                  backup-neq-slot eq = <⇒≢ (≤-trans backup-below-rf rf≤slot) eq

                  frame-after-mov' : current-frame alloc-after-mov' ≡ current-frame alloc
                  frame-after-mov' = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc

                  backup-loc-neq : OnStack (current-frame alloc-after-mov') backup-slot ≢ loc
                  backup-loc-neq eq = backup-neq-slot (trans (cong slot-of eq)
                                        (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-mov'))))

                  store-backup-via-abstract : s-after-setup' ≡ proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov' alloc-after-mov')
                  store-backup-via-abstract =
                    trans (exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc)
                          (cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov' alloc-after-mov' not-halted-after-mov'))

                  store-backup-preserves : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov' alloc-after-mov')) loc ≡
                                           readLoc s-after-mov' loc
                  store-backup-preserves = store-at-slot-preserves-disjoint backup-slot s-after-mov' alloc-after-mov' loc backup-loc-neq

                  setup-preserves : readLoc s-after-setup' loc ≡ readLoc s loc
                  setup-preserves = trans (cong (λ st → readLoc st loc) store-backup-via-abstract)
                                          (trans store-backup-preserves mov-preserves)

                  -- f-trace preserves slot (writes below reclaim-f, slot >= reclaim-f)
                  s-after-setup-f : LocState FS
                  s-after-setup-f = proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup')

                  alloc-after-setup-f : AllocState {FS}
                  alloc-after-setup-f = proj₂ (exec-trace f-trace s-after-setup' alloc-after-setup')

                  setup-f-frame : current-frame alloc-after-setup' ≡ current-frame alloc
                  setup-f-frame = exec-trace-preserves-frame setup-segment s alloc

                  -- f-trace preserves slot (writes below reclaim-f, slot >= reclaim-f)
                  -- Use exec-trace-preserves-slot-above: TraceWritesBelow n → n ≤ slot → slot preserved
                  -- Note: current-frame alloc = current-frame alloc-after-backup (definitionally)
                  f-preserves : readLoc s-after-setup-f loc ≡ readLoc s-after-setup' loc
                  f-preserves = exec-trace-preserves-slot-above f-trace s-after-setup' alloc-after-setup'
                                  (current-frame alloc-after-backup) slot reclaim-f
                                  setup-f-frame rf≤slot f-writes-below

                  -- store fst-slot preserves slot (fst-slot = reclaim-g ≠ slot < reclaim-g)
                  s-after-setup-f-store : LocState FS
                  s-after-setup-f-store = proj₁ (exec-trace (store-at-slot fst-slot ∷ []) s-after-setup-f alloc-after-setup-f)

                  alloc-after-setup-f-store : AllocState {FS}
                  alloc-after-setup-f-store = proj₂ (exec-trace (store-at-slot fst-slot ∷ []) s-after-setup-f alloc-after-setup-f)

                  -- Prove using exec-trace-preserves-halted-subir with proper state equivalence
                  not-halted-setup-f : halted s-after-setup-f ≡ false
                  not-halted-setup-f =
                    let
                      -- First prove halted after setup
                      not-halted-after-setup' : halted s-after-setup' ≡ false
                      not-halted-after-setup' =
                        trans (cong halted (exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc))
                              (subst (λ st → halted st ≡ false)
                                     (sym (store-at-slot-state-eq backup-slot s-after-mov' alloc-after-mov' not-halted-after-mov'))
                                     not-halted-after-mov')

                      -- Input equivalence
                      input-after-setup' : readReg (regs s-after-setup') Input ≡ input-loc
                      input-after-setup' =
                        let
                          input-after-mov'' : readReg (regs s-after-mov') Input ≡ input-loc
                          input-after-mov'' = trans (cong (λ st → readReg (regs st) Input) (mov-to-output-state-eq s alloc not-halted)) rdi-eq
                        in trans (cong (λ st → readReg (regs st) Input) (exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc))
                                 (trans (cong (λ st → readReg (regs st) Input)
                                          (store-at-slot-state-eq backup-slot s-after-mov' alloc-after-mov' not-halted-after-mov'))
                                        (trans (cong (λ r → readReg r Input)
                                                 (writeLoc-regs s-after-mov'
                                                   (OnStack (current-frame alloc-after-mov') backup-slot)
                                                   (readReg (regs s-after-mov') Output)))
                                               input-after-mov''))

                      -- Slots equivalence for f-trace
                      slots-eq-for-f' : ∀ slot' → suc backup-slot ≤ slot' → slot' < reclaim-f →
                        readLoc s-after-setup' (OnStack (current-frame alloc-after-backup) slot') ≡
                        readLoc s (OnStack (current-frame alloc-after-backup) slot')
                      slots-eq-for-f' slot' lo' hi' =
                        let
                          loc' = OnStack (current-frame alloc) slot'
                          mov-preserves' : readLoc s-after-mov' loc' ≡ readLoc s loc'
                          mov-preserves' = mov-to-output-preserves-readLoc s alloc loc' not-halted
                          backup-neq-slot'' : backup-slot ≢ slot'
                          backup-neq-slot'' eq = <⇒≢ lo' eq
                          backup-loc-neq' : OnStack (current-frame alloc-after-mov') backup-slot ≢ loc'
                          backup-loc-neq' eq = backup-neq-slot'' (trans (cong slot-of eq)
                                                 (cong slot-of (cong (λ f → OnStack f slot') (sym frame-after-mov'))))
                          store-backup-via-abstract' : s-after-setup' ≡ proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov' alloc-after-mov')
                          store-backup-via-abstract' =
                            trans (exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc)
                                  (cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov' alloc-after-mov' not-halted-after-mov'))
                          store-backup-preserves' : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov' alloc-after-mov')) loc' ≡
                                                    readLoc s-after-mov' loc'
                          store-backup-preserves' = store-at-slot-preserves-disjoint backup-slot s-after-mov' alloc-after-mov' loc' backup-loc-neq'
                        in trans (cong (λ st → readLoc st loc') store-backup-via-abstract')
                                 (trans store-backup-preserves' mov-preserves')

                      -- Frame and capacity equivalence
                      setup-f-frame-eq : current-frame alloc-after-setup' ≡ current-frame alloc
                      setup-f-frame-eq = exec-trace-preserves-frame setup-segment s alloc

                      setup-f-cap-eq : frame-capacity alloc-after-setup' ≡ frame-capacity alloc
                      setup-f-cap-eq = exec-trace-preserves-capacity' setup-segment s alloc setup-tpc

                      -- Use exec-trace-state-same-frame
                      f-same-frame' : proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup') ≡
                                      proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)
                      f-same-frame' = exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup
                                        setup-f-frame-eq setup-f-cap-eq

                      -- Use exec-trace-preserves-halted-subir
                      halted-f-equiv' : halted (proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)) ≡ false
                      halted-f-equiv' = exec-trace-preserves-halted-subir f-trace s-after-setup' s alloc-after-backup
                                          (suc backup-slot) reclaim-f
                                          (trans input-after-setup' (sym rdi-eq))
                                          slots-eq-for-f'
                                          f-slot-reads
                                          (IRResultAWF.trace-slot-reads-below result-f)
                                          not-halted-after-setup'
                                          not-halted
                                          (subst (λ st → halted st ≡ false) (sym f-correct) (IRResultAWF.not-halted result-f))
                    in trans (cong halted f-same-frame') halted-f-equiv'

                  setup-f-frame' : current-frame alloc-after-setup-f ≡ current-frame alloc
                  setup-f-frame' = trans (exec-trace-preserves-frame f-trace s-after-setup' alloc-after-setup') setup-f-frame

                  fst-loc-neq : OnStack (current-frame alloc-after-setup-f) fst-slot ≢ loc
                  fst-loc-neq eq = fst-slot-neq-slot (trans (cong slot-of eq)
                                     (cong slot-of (cong (λ f → OnStack f slot) (sym setup-f-frame'))))

                  store-fst-via-abstract : s-after-setup-f-store ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-setup-f alloc-after-setup-f)
                  store-fst-via-abstract = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-setup-f alloc-after-setup-f not-halted-setup-f)

                  store-fst-preserves : readLoc s-after-setup-f-store loc ≡ readLoc s-after-setup-f loc
                  store-fst-preserves = trans (cong (λ st → readLoc st loc) store-fst-via-abstract)
                                              (store-at-slot-preserves-disjoint fst-slot s-after-setup-f alloc-after-setup-f loc fst-loc-neq)

                  -- restore backup-slot doesn't change stack memory
                  not-halted-after-store-fst : halted s-after-setup-f-store ≡ false
                  not-halted-after-store-fst = subst (λ st → halted st ≡ false)
                                                 (sym (store-at-slot-state-eq fst-slot s-after-setup-f alloc-after-setup-f not-halted-setup-f))
                                                 not-halted-setup-f

                  -- After store fst, backup-slot still has input-loc
                  setup-f-store-frame : current-frame alloc-after-setup-f-store ≡ current-frame alloc
                  setup-f-store-frame = trans (exec-trace-preserves-frame (store-at-slot fst-slot ∷ []) s-after-setup-f alloc-after-setup-f) setup-f-frame'

                  -- Need backup-has-input for restore-input
                  -- This was proven in backup-has-input-here above
                  -- Actually we need to show it holds at s-after-setup-f-store with alloc-after-setup-f-store

                  restore-preserves : readLoc (proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-setup-f-store alloc-after-setup-f-store)) loc ≡
                                      readLoc s-after-setup-f-store loc
                  restore-preserves =
                    let
                      -- backup-slot still has input-loc at this point
                      backup-frame-eq : current-frame alloc-after-setup-f-store ≡ current-frame alloc-after-fst-store-here
                      backup-frame-eq = trans setup-f-store-frame (sym frame-after-fst-here)

                      -- The states are the same: s-after-setup-f-store = s-after-fst-store-here
                      -- Proof: both are exec-trace (store-at-slot fst-slot ∷ []) on the same intermediate state
                      -- before-store-here = setup-segment ++ f-trace
                      -- s-before-store-here = exec-trace before-store-here s alloc
                      --                     = exec-trace (setup-segment ++ f-trace) s alloc
                      --                     = exec-trace f-trace s-after-setup' alloc-after-setup'
                      --                     = s-after-setup-f
                      -- exec-trace append gives: before-store-here = setup-segment ++ f-trace
                      -- so exec-trace before-store-here = exec-trace f-trace after setup
                      both-eq : exec-trace before-store-here s alloc ≡ exec-trace f-trace s-after-setup' alloc-after-setup'
                      both-eq = exec-trace-append setup-segment f-trace s alloc

                      -- exec-trace on the tuple gives tuple equality
                      store-tuple-eq : exec-trace (store-at-slot fst-slot ∷ []) s-after-setup-f alloc-after-setup-f ≡
                                       exec-trace (store-at-slot fst-slot ∷ []) s-before-store-here alloc-before-store-here
                      store-tuple-eq = cong (λ p → exec-trace (store-at-slot fst-slot ∷ []) (proj₁ p) (proj₂ p)) (sym both-eq)

                      states-same : s-after-setup-f-store ≡ s-after-fst-store-here
                      states-same = cong proj₁ store-tuple-eq

                      backup-here' : readLoc s-after-setup-f-store (OnStack (current-frame alloc-after-setup-f-store) backup-slot) ≡ just input-loc
                      backup-here' = subst (λ f → readLoc s-after-setup-f-store (OnStack f backup-slot) ≡ just input-loc)
                                           (sym backup-frame-eq)
                                           (subst (λ st → readLoc st (OnStack (current-frame alloc-after-fst-store-here) backup-slot) ≡ just input-loc)
                                                  (sym states-same) backup-has-input-here)
                    in restore-input-preserves-readLoc backup-slot s-after-setup-f-store alloc-after-setup-f-store input-loc loc
                         not-halted-after-store-fst backup-here'

                  -- Compose all the preservation proofs
                  s-before-g-via-steps : s-before-g ≡ proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-setup-f-store alloc-after-setup-f-store)
                  s-before-g-via-steps =
                    let
                      step1 : proj₁ (exec-trace prefix-before-g s alloc) ≡
                              proj₁ (exec-trace (f-trace ++ (store-at-slot fst-slot ∷ restore-input backup-slot ∷ [])) s-after-setup' alloc-after-setup')
                      step1 = exec-trace-append-state setup-segment (f-trace ++ (store-at-slot fst-slot ∷ restore-input backup-slot ∷ [])) s alloc

                      step2 : proj₁ (exec-trace (f-trace ++ (store-at-slot fst-slot ∷ restore-input backup-slot ∷ [])) s-after-setup' alloc-after-setup') ≡
                              proj₁ (exec-trace (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s-after-setup-f alloc-after-setup-f)
                      step2 = exec-trace-append-state f-trace (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s-after-setup' alloc-after-setup'

                      step3 : proj₁ (exec-trace (store-at-slot fst-slot ∷ restore-input backup-slot ∷ []) s-after-setup-f alloc-after-setup-f) ≡
                              proj₁ (exec-trace (restore-input backup-slot ∷ []) s-after-setup-f-store alloc-after-setup-f-store)
                      step3 = exec-trace-append-state (store-at-slot fst-slot ∷ []) (restore-input backup-slot ∷ []) s-after-setup-f alloc-after-setup-f
                    in trans step1 (trans step2 step3)

                in trans (cong (λ st → readLoc st loc) s-before-g-via-steps)
                         (trans restore-preserves
                                (trans store-fst-preserves
                                       (trans f-preserves setup-preserves)))

            in trans s-before-g-eq-s (sym s1'-eq-s)

          -- Step 3: Apply state equivalence
          output-equiv : readReg (regs (proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed))) Output ≡
                         readReg (regs (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed))) Output
          output-equiv = exec-trace-output-equiv g-trace s-before-g s₁' alloc₁-reclaimed reclaim-f reclaim-g
                           input-eq halted-eq not-halted-s-before-g slots-eq g-slot-reads g-slot-reads-below

          -- Step 4: Connect to g-correct and rax-g
          -- g-correct : proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed) ≡ s₂
          output-s2 : readReg (regs (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed))) Output ≡ snd-loc
          output-s2 = trans (cong (λ st → readReg (regs st) Output) g-correct) rax-g

        in trans (cong (λ st → readReg (regs st) Output) s-before-final-via-g)
                 (trans (cong (λ st → readReg (regs st) Output) state-via-g)
                        (trans output-equiv output-s2))

      -- After store-at-slot snd-slot, snd-slot contains snd-loc
      snd-written-after-store : readLoc s-after-snd-store snd-loc-stack ≡ just snd-loc
      snd-written-after-store =
        let
          loc = OnStack (current-frame alloc-before-final) snd-slot
          val = readReg (regs s-before-final) Output
          written-eq : s-after-snd-store ≡ writeLoc s-before-final loc val
          written-eq = snd-store-state
          read-back : readLoc (writeLoc s-before-final loc val) loc ≡ just val
          read-back = write-read-same-stack s-before-final (current-frame alloc-before-final) snd-slot val
          loc-eq : loc ≡ snd-loc-stack
          loc-eq = sym snd-loc-stack-eq
        in
        trans (cong (λ st → readLoc st snd-loc-stack) written-eq)
              (trans (subst (λ l → readLoc (writeLoc s-before-final (OnStack (current-frame alloc-before-final) snd-slot) val) l ≡ just val)
                           loc-eq read-back)
                     (cong just output-before-final-is-snd))

      -- lea-slot preserves all memory locations
      lea-preserves-snd : readLoc (proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final)) snd-loc-stack ≡
                          readLoc s-after-snd-store snd-loc-stack
      lea-preserves-snd = lea-slot-preserves-readLoc fst-slot s-after-snd-store alloc-before-final snd-loc-stack not-halted-after-snd-store

      -- PROVEN: snd-written
      snd-written : readLoc s-final snd-loc-stack ≡ just snd-loc
      snd-written =
        let
          step1 : s-final ≡ proj₁ (exec-trace final-trace s-before-final alloc-before-final)
          step1 = s-final-decomp
          step2 : proj₁ (exec-trace final-trace s-before-final alloc-before-final) ≡
                  proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final)
          step2 = final-trace-decomp
        in
        trans (cong (λ st → readLoc st snd-loc-stack) (trans step1 step2))
              (trans lea-preserves-snd snd-written-after-store)

      ------------------------------------------------------------------------
      -- BeforeFrontier proofs
      ------------------------------------------------------------------------

      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl (m<m+n reclaim-g {ps} ps≥1)

      fst-before₃ : BeforeFrontier alloc₃ fst-loc
      fst-before₃ = frontier-monotone alloc₁-reclaimed alloc₃
                      refl
                      (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
                      ≤-refl
                      fst-loc
                      (IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits)

      snd-before₃ : BeforeFrontier alloc₃ snd-loc
      snd-before₃ = frontier-monotone (record alloc { next-slot = reclaim-g }) alloc₃
                      refl
                      (m≤m+n reclaim-g ps)
                      ≤-refl
                      snd-loc
                      (IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits)

      suc<+ps : suc reclaim-g < reclaim-g +ℕ ps
      suc<+ps = ≤-trans (suc<+2 reclaim-g) (+-monoʳ-≤ reclaim-g ps≥2)

      sucLoc-pair-before₃ : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before₃ = stack-before refl suc<+ps

      fst-ptr : readLoc s-final pair-loc ≡ just fst-loc
      fst-ptr = fst-preserved-final

      snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
      snd-ptr = snd-written

      rax-eq : readReg (regs s-final) Output ≡ pair-loc
      rax-eq = output-is-pair

      -- Since s-final is defined by trace, we need to prove halted is preserved
      -- PROVEN: trace halted through final-trace (store-at-slot snd-slot, lea-slot)
      not-halted-final : halted s-final ≡ false
      not-halted-final =
        let
          -- s-final = proj₁ (exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-before-final)
          -- via s-final-decomp and final-trace-decomp
          s-lea = record s-after-snd-store { regs = writeReg (regs s-after-snd-store) Output (OnStack (current-frame alloc-before-final) fst-slot) }

          s-final-eq-lea : s-final ≡ s-lea
          s-final-eq-lea = trans s-final-decomp (trans final-trace-decomp lea-slot-decomp)

          -- halted of record update is same as original
          halted-lea-eq : halted s-lea ≡ halted s-after-snd-store
          halted-lea-eq = refl
        in trans (cong halted s-final-eq-lea) (trans halted-lea-eq not-halted-after-snd-store)

      -- NOTE: Validity proofs moved after mem-preserved-pair (needed for scoping)

      ------------------------------------------------------------------------
      -- Monotonicity and preservation proofs
      ------------------------------------------------------------------------

      slot-monotone-pair : next-slot alloc ≤ reclaim-g +ℕ ps
      slot-monotone-pair = ≤-trans (n≤1+n (next-slot alloc))
                             (≤-trans reclaim-f-above-backup
                               (≤-trans (IRResultAWF.reclaim-monotone result-g)
                                 (m≤m+n reclaim-g ps)))

      heap-monotone-pair : next-heap-ref alloc ≤ next-heap-ref alloc₃
      heap-monotone-pair = ≤-refl

      heap-preserved-pair : next-heap-ref alloc₃ ≡ next-heap-ref alloc
      heap-preserved-pair = refl

      -- NOTE: mem-preserved-pair is defined after trace bounds (see below)

      ------------------------------------------------------------------------
      -- Reclamation
      ------------------------------------------------------------------------
      pair-reclaim = reclaim-g +ℕ ps

      pair-reclaim-monotone : next-slot alloc ≤ pair-reclaim
      pair-reclaim-monotone = slot-monotone-pair

      pair-reclaim-bounded : pair-reclaim ≤ next-slot alloc₃
      pair-reclaim-bounded = ≤-refl  -- next-slot alloc₃ = reclaim-g +ℕ ps = pair-reclaim

      pair-reclaim-preserves : ∀ fits → BeforeFrontier alloc₃ pair-loc
      pair-reclaim-preserves fits = pair-before

      -- NOTE: pair-reclaim-preserves-validity moved after pair-valid-wf-final for scoping

      pair-reclaim-size-bound : pair-reclaim ≤ next-slot alloc +ℕ req-pair
      pair-reclaim-size-bound = subst (pair-reclaim ≤_) req-eq lemma-result
        where
          -- Lemma gives bound relative to suc (next-slot alloc)
          lemma-result : pair-reclaim ≤ suc (next-slot alloc) +ℕ ((rf +ℕ rg) +ℕ ps)
          lemma-result = pair-slot-bounded-lemma (suc (next-slot alloc)) reclaim-f reclaim-g rf rg ps
                           reclaim-g-bound reclaim-f-bound

          -- suc slot + ((rf + rg) + ps) = slot + req-pair where req-pair = 1 + rf + rg + ps
          req-eq : suc (next-slot alloc) +ℕ ((rf +ℕ rg) +ℕ ps) ≡ next-slot alloc +ℕ req-pair
          req-eq = trans (cong (_+ℕ ((rf +ℕ rg) +ℕ ps)) (sym slot+1≡suc-slot))
                    (trans (+-assoc (next-slot alloc) 1 ((rf +ℕ rg) +ℕ ps))
                      (cong (next-slot alloc +ℕ_)
                        (trans (sym (+-assoc 1 (rf +ℕ rg) ps))
                          (cong (_+ℕ ps) (sym (+-assoc 1 rf rg))))))

      ------------------------------------------------------------------------
      -- Frontier stability (proven by decomposing trace into setup + rest)
      ------------------------------------------------------------------------
      pair-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input ≡ input-loc' →
        readLoc s' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
        readLoc (proj₁ (exec-trace pair-trace s' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
      pair-frontier-stable s' input-loc' s'-not-halted input-eq' slot-eq' =
        -- Strategy: setup writes input-loc' to backup-slot, rest preserves it
        let
          -- Split pair-trace = setup ++ rest
          setup-tr : AbstractTrace
          setup-tr = mov-to-output ∷ store-at-slot backup-slot ∷ []

          rest-tr : AbstractTrace
          rest-tr = f-trace ++ (store-at-slot fst-slot ∷ restore-input backup-slot ∷ (g-trace ++ final-trace))

          -- pair-trace = setup ++ rest (definitional)
          split-eq : pair-trace ≡ setup-tr ++ rest-tr
          split-eq = refl

          -- rest writes above suc backup-slot, so preserves backup-slot
          rest-writes-above : TraceWritesAbove (suc backup-slot) rest-tr
          rest-writes-above =
            let
              f-tw : TraceWritesAbove (suc backup-slot) f-trace
              f-tw = IRResultAWF.trace-writes-above result-f
              fst-gt : suc backup-slot ≤ fst-slot
              fst-gt = ≤-trans (IRResultAWF.reclaim-monotone result-f) (IRResultAWF.reclaim-monotone result-g)
              snd-gt : suc backup-slot ≤ snd-slot
              snd-gt = ≤-trans fst-gt (n≤1+n fst-slot)
              final-tw : TraceWritesAbove (suc backup-slot) final-trace
              final-tw = snd-gt , tt
              g-tw : TraceWritesAbove (suc backup-slot) g-trace
              g-tw = trace-writes-above-mono (suc backup-slot) reclaim-f g-trace
                       (IRResultAWF.reclaim-monotone result-f)
                       (IRResultAWF.trace-writes-above result-g)
              g-plus-final-tw : TraceWritesAbove (suc backup-slot) (g-trace ++ final-trace)
              g-plus-final-tw = trace-writes-above-append (suc backup-slot) g-trace final-trace g-tw final-tw
              restore-plus-tw : TraceWritesAbove (suc backup-slot) (restore-input backup-slot ∷ (g-trace ++ final-trace))
              restore-plus-tw = g-plus-final-tw
              fst-plus-tw : TraceWritesAbove (suc backup-slot) (store-at-slot fst-slot ∷ restore-input backup-slot ∷ (g-trace ++ final-trace))
              fst-plus-tw = fst-gt , restore-plus-tw
            in trace-writes-above-append (suc backup-slot) f-trace _ f-tw fst-plus-tw

          -- Disjointness for backup slot
          backup-disjoint : ∀ slot → suc backup-slot ≤ slot → OnStack (current-frame alloc) slot ≢ backup-loc
          backup-disjoint slot bound eq = <⇒≢ bound (sym (cong slot-of eq))

          -- rest preserves backup-loc
          rest-preserves : ∀ (sr : LocState FS) (allocr : AllocState {FS}) →
            current-frame allocr ≡ current-frame alloc →
            readLoc (proj₁ (exec-trace rest-tr sr allocr)) backup-loc ≡ readLoc sr backup-loc
          rest-preserves sr allocr frame-eq =
            exec-trace-preserves-disjoint rest-tr sr allocr backup-loc (suc backup-slot)
              rest-writes-above
              (λ slot bound eq → backup-disjoint slot bound (trans (cong (λ f → OnStack f slot) (sym frame-eq)) eq))

          -- After mov-to-output
          s-after-mov : LocState FS
          s-after-mov = proj₁ (exec-abstract mov-to-output s' alloc)

          output-after-mov : readReg (regs s-after-mov) Output ≡ input-loc'
          output-after-mov = trans (writeReg-same (regs s') Output (readReg (regs s') Input)) input-eq'

          halted-after-mov : halted s-after-mov ≡ false
          halted-after-mov = s'-not-halted

          -- setup-state after executing setup-tr
          setup-state : LocState FS × AllocState {FS}
          setup-state = exec-trace setup-tr s' alloc

          setup-eq : setup-state ≡ exec-abstract (store-at-slot backup-slot) s-after-mov alloc
          setup-eq = trans (exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ []) s' alloc s'-not-halted)
                           (exec-trace-single (store-at-slot backup-slot) s-after-mov alloc halted-after-mov)

          setup-frame-unchanged : current-frame (proj₂ setup-state) ≡ current-frame alloc
          setup-frame-unchanged = trans (cong (λ p → current-frame (proj₂ p)) setup-eq)
                                        (exec-abstract-preserves-frame (store-at-slot backup-slot) s-after-mov alloc)

          -- After store, backup-loc contains input-loc'
          s-after-store : LocState FS
          s-after-store = proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov alloc)

          backup-after-setup : readLoc s-after-store backup-loc ≡ just input-loc'
          backup-after-setup =
            trans (cong (λ v → readLoc (writeLoc s-after-mov backup-loc v) backup-loc) output-after-mov)
                  (write-read-same-stack s-after-mov (current-frame alloc) backup-slot input-loc')

          proj₁-setup-eq : proj₁ setup-state ≡ s-after-store
          proj₁-setup-eq = cong proj₁ setup-eq

          setup-backup-correct : readLoc (proj₁ setup-state) backup-loc ≡ just input-loc'
          setup-backup-correct = trans (cong (λ st → readLoc st backup-loc) proj₁-setup-eq) backup-after-setup

          -- Main: split and combine
          split-exec : proj₁ (exec-trace pair-trace s' alloc) ≡
                       proj₁ (exec-trace rest-tr (proj₁ setup-state) (proj₂ setup-state))
          split-exec = trans (cong (λ t → proj₁ (exec-trace t s' alloc)) split-eq)
                             (exec-trace-append-state setup-tr rest-tr s' alloc)

          rest-eq : readLoc (proj₁ (exec-trace rest-tr (proj₁ setup-state) (proj₂ setup-state))) backup-loc ≡
                    readLoc (proj₁ setup-state) backup-loc
          rest-eq = rest-preserves (proj₁ setup-state) (proj₂ setup-state) setup-frame-unchanged
        in trans (cong (λ st → readLoc st backup-loc) split-exec)
                 (trans rest-eq setup-backup-correct)

      ------------------------------------------------------------------------
      -- Trace bounds (proven using composition lemmas)
      ------------------------------------------------------------------------

      -- TraceWritesAbove: all stack writes are at slots ≥ next-slot alloc
      pair-trace-writes-above : TraceWritesAbove (next-slot alloc) pair-trace
      pair-trace-writes-above =
        let
          n = next-slot alloc
          -- f-trace writes above suc n (ran with alloc-after-backup), weaken to n
          f-tw-at-suc : TraceWritesAbove (suc n) f-trace
          f-tw-at-suc = IRResultAWF.trace-writes-above result-f
          f-tw : TraceWritesAbove n f-trace
          f-tw = trace-writes-above-mono n (suc n) f-trace (n≤1+n n) f-tw-at-suc
          -- g-trace writes above reclaim-f ≥ suc n ≥ n
          g-tw-at-reclaim : TraceWritesAbove reclaim-f g-trace
          g-tw-at-reclaim = IRResultAWF.trace-writes-above result-g
          g-tw : TraceWritesAbove n g-trace
          g-tw = trace-writes-above-mono n reclaim-f g-trace
                   (≤-trans (n≤1+n n) (IRResultAWF.reclaim-monotone result-f)) g-tw-at-reclaim
          -- Slot bounds
          backup-bound : n ≤ backup-slot
          backup-bound = ≤-refl
          fst-bound : n ≤ fst-slot
          fst-bound = ≤-trans (n≤1+n n) (≤-trans (IRResultAWF.reclaim-monotone result-f) (IRResultAWF.reclaim-monotone result-g))
          snd-bound : n ≤ snd-slot
          snd-bound = ≤-trans fst-bound (n≤1+n reclaim-g)
          -- Define trace segments explicitly
          final-seg : AbstractTrace
          final-seg = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
          final-tw : TraceWritesAbove n final-seg
          final-tw = snd-bound , tt
          g-plus-final : AbstractTrace
          g-plus-final = g-trace ++ final-seg
          g-plus-final-tw : TraceWritesAbove n g-plus-final
          g-plus-final-tw = trace-writes-above-append n g-trace final-seg g-tw final-tw
          restore-plus-rest : AbstractTrace
          restore-plus-rest = restore-input backup-slot ∷ g-plus-final
          restore-plus-rest-tw : TraceWritesAbove n restore-plus-rest
          restore-plus-rest-tw = g-plus-final-tw  -- restore-input has no slot write
          fst-plus-rest : AbstractTrace
          fst-plus-rest = store-at-slot fst-slot ∷ restore-plus-rest
          fst-plus-rest-tw : TraceWritesAbove n fst-plus-rest
          fst-plus-rest-tw = fst-bound , restore-plus-rest-tw
          f-plus-rest : AbstractTrace
          f-plus-rest = f-trace ++ fst-plus-rest
          f-plus-rest-tw : TraceWritesAbove n f-plus-rest
          f-plus-rest-tw = trace-writes-above-append n f-trace fst-plus-rest f-tw fst-plus-rest-tw
          setup : AbstractTrace
          setup = mov-to-output ∷ store-at-slot backup-slot ∷ []
          setup-tw : TraceWritesAbove n setup
          setup-tw = backup-bound , tt
        in
        trace-writes-above-append n setup f-plus-rest setup-tw f-plus-rest-tw

      -- TraceSlotReadsAbove: all slot reads are from slots ≥ next-slot alloc
      pair-trace-slot-reads-above : TraceSlotReadsAbove (next-slot alloc) pair-trace
      pair-trace-slot-reads-above =
        let
          n = next-slot alloc
          -- f-trace reads above suc n, weaken to n
          f-ra-at-suc : TraceSlotReadsAbove (suc n) f-trace
          f-ra-at-suc = IRResultAWF.trace-slot-reads-above result-f
          f-ra : TraceSlotReadsAbove n f-trace
          f-ra = trace-reads-above-mono n (suc n) f-trace (n≤1+n n) f-ra-at-suc
          -- g-trace reads above reclaim-f ≥ suc n ≥ n
          g-ra-at-reclaim : TraceSlotReadsAbove reclaim-f g-trace
          g-ra-at-reclaim = IRResultAWF.trace-slot-reads-above result-g
          g-ra : TraceSlotReadsAbove n g-trace
          g-ra = trace-reads-above-mono n reclaim-f g-trace
                   (≤-trans (n≤1+n n) (IRResultAWF.reclaim-monotone result-f)) g-ra-at-reclaim
          -- backup-slot = n, so restore-input backup-slot reads at n
          backup-bound : n ≤ backup-slot
          backup-bound = ≤-refl
          -- Define trace segments explicitly
          final-seg : AbstractTrace
          final-seg = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
          final-ra : TraceSlotReadsAbove n final-seg
          final-ra = tt
          g-plus-final : AbstractTrace
          g-plus-final = g-trace ++ final-seg
          g-plus-final-ra : TraceSlotReadsAbove n g-plus-final
          g-plus-final-ra = trace-reads-above-append n g-trace final-seg g-ra final-ra
          restore-plus-rest : AbstractTrace
          restore-plus-rest = restore-input backup-slot ∷ g-plus-final
          restore-plus-rest-ra : TraceSlotReadsAbove n restore-plus-rest
          restore-plus-rest-ra = backup-bound , g-plus-final-ra
          fst-plus-rest : AbstractTrace
          fst-plus-rest = store-at-slot fst-slot ∷ restore-plus-rest
          fst-plus-rest-ra : TraceSlotReadsAbove n fst-plus-rest
          fst-plus-rest-ra = restore-plus-rest-ra  -- store-at-slot has no slot read
          f-plus-rest : AbstractTrace
          f-plus-rest = f-trace ++ fst-plus-rest
          f-plus-rest-ra : TraceSlotReadsAbove n f-plus-rest
          f-plus-rest-ra = trace-reads-above-append n f-trace fst-plus-rest f-ra fst-plus-rest-ra
          setup : AbstractTrace
          setup = mov-to-output ∷ store-at-slot backup-slot ∷ []
          setup-ra : TraceSlotReadsAbove n setup
          setup-ra = tt
        in
        trace-reads-above-append n setup f-plus-rest setup-ra f-plus-rest-ra

      -- TraceWritesBelow: all stack writes are at slots < reclaim-g + ps
      pair-trace-writes-below : TraceWritesBelow (reclaim-g +ℕ ps) pair-trace
      pair-trace-writes-below =
        let
          bound = reclaim-g +ℕ ps
          -- f-trace writes below reclaim-f ≤ reclaim-g + ps
          f-wb-at-reclaim : TraceWritesBelow reclaim-f f-trace
          f-wb-at-reclaim = IRResultAWF.trace-writes-below result-f
          reclaim-f≤bound : reclaim-f ≤ bound
          reclaim-f≤bound = ≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps)
          f-wb : TraceWritesBelow bound f-trace
          f-wb = trace-writes-below-mono bound reclaim-f f-trace reclaim-f≤bound f-wb-at-reclaim
          -- g-trace writes below reclaim-g ≤ reclaim-g + ps
          g-wb-at-reclaim : TraceWritesBelow reclaim-g g-trace
          g-wb-at-reclaim = IRResultAWF.trace-writes-below result-g
          g-wb : TraceWritesBelow bound g-trace
          g-wb = trace-writes-below-mono bound reclaim-g g-trace (m≤m+n reclaim-g ps) g-wb-at-reclaim
          -- Slot bounds: suc backup-slot ≤ reclaim-f ≤ reclaim-g ≤ reclaim-g + ps
          -- backup-slot < bound means suc backup-slot ≤ bound
          -- reclaim-monotone result-f gives suc backup-slot ≤ reclaim-f
          backup-bound : backup-slot < bound
          backup-bound = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                           (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
          fst-bound : fst-slot < bound
          fst-bound = m<m+n reclaim-g {ps} ps≥1
          snd-bound : snd-slot < bound
          snd-bound = suc<+ps
          -- Define trace segments explicitly
          final-seg : AbstractTrace
          final-seg = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
          final-wb : TraceWritesBelow bound final-seg
          final-wb = snd-bound , tt
          g-plus-final : AbstractTrace
          g-plus-final = g-trace ++ final-seg
          g-plus-final-wb : TraceWritesBelow bound g-plus-final
          g-plus-final-wb = trace-writes-below-append bound g-trace final-seg g-wb final-wb
          restore-plus-rest : AbstractTrace
          restore-plus-rest = restore-input backup-slot ∷ g-plus-final
          restore-plus-rest-wb : TraceWritesBelow bound restore-plus-rest
          restore-plus-rest-wb = g-plus-final-wb  -- restore-input has no slot write
          fst-plus-rest : AbstractTrace
          fst-plus-rest = store-at-slot fst-slot ∷ restore-plus-rest
          fst-plus-rest-wb : TraceWritesBelow bound fst-plus-rest
          fst-plus-rest-wb = fst-bound , restore-plus-rest-wb
          f-plus-rest : AbstractTrace
          f-plus-rest = f-trace ++ fst-plus-rest
          f-plus-rest-wb : TraceWritesBelow bound f-plus-rest
          f-plus-rest-wb = trace-writes-below-append bound f-trace fst-plus-rest f-wb fst-plus-rest-wb
          setup : AbstractTrace
          setup = mov-to-output ∷ store-at-slot backup-slot ∷ []
          setup-wb : TraceWritesBelow bound setup
          setup-wb = backup-bound , tt
        in
        trace-writes-below-append bound setup f-plus-rest setup-wb f-plus-rest-wb

      -- TraceSlotReadsBelow: all slot reads are from slots < reclaim-g + ps
      pair-trace-slot-reads-below : TraceSlotReadsBelow (reclaim-g +ℕ ps) pair-trace
      pair-trace-slot-reads-below =
        let
          bound = reclaim-g +ℕ ps
          -- f-trace reads below reclaim-f ≤ reclaim-g + ps
          f-rb-at-reclaim : TraceSlotReadsBelow reclaim-f f-trace
          f-rb-at-reclaim = IRResultAWF.trace-slot-reads-below result-f
          reclaim-f≤bound : reclaim-f ≤ bound
          reclaim-f≤bound = ≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps)
          f-rb : TraceSlotReadsBelow bound f-trace
          f-rb = trace-reads-below-mono bound reclaim-f f-trace reclaim-f≤bound f-rb-at-reclaim
          -- g-trace reads below reclaim-g ≤ reclaim-g + ps
          g-rb-at-reclaim : TraceSlotReadsBelow reclaim-g g-trace
          g-rb-at-reclaim = IRResultAWF.trace-slot-reads-below result-g
          g-rb : TraceSlotReadsBelow bound g-trace
          g-rb = trace-reads-below-mono bound reclaim-g g-trace (m≤m+n reclaim-g ps) g-rb-at-reclaim
          -- restore-input backup-slot reads at backup-slot < bound
          -- backup-slot < bound means suc backup-slot ≤ bound
          -- reclaim-monotone result-f gives suc backup-slot ≤ reclaim-f
          backup-bound : backup-slot < bound
          backup-bound = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                           (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
          -- Define trace segments explicitly
          final-seg : AbstractTrace
          final-seg = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
          final-rb : TraceSlotReadsBelow bound final-seg
          final-rb = tt
          g-plus-final : AbstractTrace
          g-plus-final = g-trace ++ final-seg
          g-plus-final-rb : TraceSlotReadsBelow bound g-plus-final
          g-plus-final-rb = trace-reads-below-append bound g-trace final-seg g-rb final-rb
          restore-plus-rest : AbstractTrace
          restore-plus-rest = restore-input backup-slot ∷ g-plus-final
          restore-plus-rest-rb : TraceSlotReadsBelow bound restore-plus-rest
          restore-plus-rest-rb = backup-bound , g-plus-final-rb
          fst-plus-rest : AbstractTrace
          fst-plus-rest = store-at-slot fst-slot ∷ restore-plus-rest
          fst-plus-rest-rb : TraceSlotReadsBelow bound fst-plus-rest
          fst-plus-rest-rb = restore-plus-rest-rb  -- store-at-slot has no slot read
          f-plus-rest : AbstractTrace
          f-plus-rest = f-trace ++ fst-plus-rest
          f-plus-rest-rb : TraceSlotReadsBelow bound f-plus-rest
          f-plus-rest-rb = trace-reads-below-append bound f-trace fst-plus-rest f-rb fst-plus-rest-rb
          setup : AbstractTrace
          setup = mov-to-output ∷ store-at-slot backup-slot ∷ []
          setup-rb : TraceSlotReadsBelow bound setup
          setup-rb = tt
        in
        trace-reads-below-append bound setup f-plus-rest setup-rb f-plus-rest-rb

      ------------------------------------------------------------------------
      -- Memory preservation for locations before frontier
      -- PROVEN using exec-trace-preserves-disjoint and pair-trace-writes-above
      ------------------------------------------------------------------------
      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair loc bf = exec-trace-preserves-disjoint pair-trace s alloc loc (next-slot alloc)
                                    pair-trace-writes-above disjoint-proof
        where
          -- Locations before frontier are disjoint from all slots ≥ next-slot alloc
          disjoint-proof : ∀ slot → next-slot alloc ≤ slot → OnStack (current-frame alloc) slot ≢ loc
          disjoint-proof slot n≤slot eq = bf-disjoint bf slot n≤slot (sym eq)
            where
              -- BeforeFrontier implies the location is not at slots ≥ next-slot
              -- For stack-before: slot<next gives k < next-slot, and n≤slot' gives next-slot ≤ slot'
              -- So k < slot', but eq' gives k ≡ slot', contradiction
              bf-disjoint : BeforeFrontier alloc loc → ∀ slot' → next-slot alloc ≤ slot' →
                            loc ≢ OnStack (current-frame alloc) slot'
              bf-disjoint (stack-before frame-eq slot<next) slot' n≤slot' eq' =
                let k<slot' : _ < slot'
                    k<slot' = ≤-trans slot<next n≤slot'
                    k≡slot' = cong slot-of eq'
                in <⇒≢ k<slot' k≡slot'
              bf-disjoint (stack-ancestor cf≺f _) slot' n≤slot' eq' =
                -- f is an ancestor frame, but eq' says OnStack f k ≡ OnStack (current-frame alloc) slot'
                -- This implies f ≡ current-frame alloc, contradicting cf≺f (irreflexivity)
                let f≡cf = cong frame-of eq'
                in ≺⇒≢ cf≺f (sym f≡cf)
                  where
                    frame-of : ValueLocation FS → Frame
                    frame-of (OnStack f _) = f
                    frame-of (OnHeap _) = current-frame alloc  -- dummy
              bf-disjoint (heap-before _) slot' n≤slot' ()

      ------------------------------------------------------------------------
      -- Validity proofs
      --
      -- Mathematical reasoning:
      --
      -- For fst-valid-s-final:
      -- 1. fst-loc is at slot ≥ suc backup-slot (f ran with alloc-after-backup)
      -- 2. All sub-locations of (eval primSem f x) at fst-loc are also at slots ≥ suc backup-slot
      -- 3. backup-slot = next-slot alloc is NOT a sub-location of fst-loc
      -- 4. The trace after f writes at slots ≥ reclaim-g ≥ reclaim-f > fst-loc's sub-locations
      -- 5. So fst-loc's sub-locations are preserved from s₁ to s-final
      -- 6. Input data sub-locations (at slots < backup-slot) are preserved via
      --    IRResultAWF.mem-preserved-before result-f + mem-preserved-pair
      --
      -- For snd-valid-s-final:
      -- 1. snd-loc is at slot ≥ reclaim-f (g ran with alloc₁-reclaimed)
      -- 2. All sub-locations of (eval primSem g x) at snd-loc are at slots ≥ reclaim-f
      -- 3. The final-trace writes at fst-slot = reclaim-g and snd-slot = suc reclaim-g
      -- 4. Both write slots are ≥ reclaim-g > snd-loc's sub-locations (since snd-loc < reclaim-g)
      -- 5. So snd-loc's sub-locations are preserved from s₂ to s-final
      --
      -- Proof uses validityWF-mem-preserved-excluding with backup-slot as the gap.
      ------------------------------------------------------------------------

      -- fst validity at s₁ with alloc₁-reclaimed
      fst-before₁-reclaimed : BeforeFrontier alloc₁-reclaimed fst-loc
      fst-before₁-reclaimed = IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits

      fst-valid-s1 : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s₁
      fst-valid-s1 = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

      -- snd validity at s₂ with alloc₂-reclaimed
      alloc₂-reclaimed : AllocState {FS}
      alloc₂-reclaimed = record alloc { next-slot = reclaim-g }

      snd-before₂-reclaimed : BeforeFrontier alloc₂-reclaimed snd-loc
      snd-before₂-reclaimed = IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits

      snd-valid-s2 : ValidAtWF mG alloc₂-reclaimed (eval primSem g x) snd-loc s₂
      snd-valid-s2 = IRResultAWF.reclaim-preserves-validity result-g reclaim-g-fits

      -- Memory agreement from s₁ to s-final, excluding backup-slot
      -- Key insight: rest-after-f writes at slots ≥ reclaim-f, so slots < reclaim-f are preserved
      -- (except backup-slot which is explicitly excluded)

      -- rest-after-f writes above reclaim-f
      rest-after-f-writes-above : TraceWritesAbove reclaim-f rest-after-f
      rest-after-f-writes-above =
        let
          -- fst-slot = reclaim-g ≥ reclaim-f
          fst-above : reclaim-f ≤ fst-slot
          fst-above = IRResultAWF.reclaim-monotone result-g

          -- g-trace writes above reclaim-f
          g-above : TraceWritesAbove reclaim-f g-trace
          g-above = IRResultAWF.trace-writes-above result-g

          -- snd-slot = suc reclaim-g > reclaim-g ≥ reclaim-f
          snd-above : reclaim-f ≤ snd-slot
          snd-above = ≤-trans fst-above (n≤1+n fst-slot)

          -- final-trace writes above reclaim-f
          final-above : TraceWritesAbove reclaim-f final-trace
          final-above = snd-above , tt

          -- g ++ final writes above reclaim-f
          g-final-above : TraceWritesAbove reclaim-f (g-trace ++ final-trace)
          g-final-above = trace-writes-above-append reclaim-f g-trace final-trace g-above final-above

          -- restore-input doesn't write to stack, so passes through
          restore-g-final-above : TraceWritesAbove reclaim-f (restore-input backup-slot ∷ (g-trace ++ final-trace))
          restore-g-final-above = g-final-above

          -- store fst-slot ++ rest writes above reclaim-f
          middle-g-final-above : TraceWritesAbove reclaim-f (store-at-slot fst-slot ∷ restore-input backup-slot ∷ (g-trace ++ final-trace))
          middle-g-final-above = fst-above , restore-g-final-above
        in middle-g-final-above

      -- State after setup ++ f in the trace
      s-after-setup-f : LocState FS
      s-after-setup-f = proj₁ (exec-trace (setup-trace ++ f-trace) s alloc)

      alloc-after-setup-f : AllocState {FS}
      alloc-after-setup-f = proj₂ (exec-trace (setup-trace ++ f-trace) s alloc)

      -- s-final = exec rest-after-f s-after-setup-f alloc-after-setup-f
      s-final-via-rest : s-final ≡ proj₁ (exec-trace rest-after-f s-after-setup-f alloc-after-setup-f)
      s-final-via-rest = exec-trace-append-state (setup-trace ++ f-trace) rest-after-f s alloc

      -- Frame preserved through setup ++ f
      frame-after-setup-f : current-frame alloc-after-setup-f ≡ frame
      frame-after-setup-f = exec-trace-preserves-frame (setup-trace ++ f-trace) s alloc

      -- For loc' before alloc₁-reclaimed and loc' ≠ backup-slot:
      -- 1. rest-after-f preserves loc' (writes above reclaim-f, loc' has slot < reclaim-f)
      -- 2. Need to relate s₁ to s-after-setup-f

      -- s₁ and s-after-setup-f agree on locations before alloc₁-reclaimed (except backup-slot)
      -- Both are states after f completes, just with different starting states/allocs
      -- Key insight: f-trace reads only slots ≥ suc backup-slot (f-slot-reads)
      -- and s, s-after-setup agree on all such slots (setup only writes backup-slot)
      -- So f-trace produces same results from both starting states
      s1-agrees-setup-f : ∀ loc' → BeforeFrontier alloc₁-reclaimed loc' →
                          loc' ≢ OnStack frame backup-slot →
                          readLoc s₁ loc' ≡ readLoc s-after-setup-f loc'
      s1-agrees-setup-f loc' bf neq-backup' =
        let
          -- s₁ = exec f-trace s alloc-after-backup
          s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
          s1-via-trace = sym (IRResultAWF.trace-correct result-f)

          -- s-after-setup-f = exec (setup ++ f) s alloc
          --                 = exec f-trace s-after-setup alloc-after-setup
          setup-f-decomp : s-after-setup-f ≡ proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)
          setup-f-decomp = exec-trace-append-state setup-trace f-trace s alloc

          -- alloc-after-setup = alloc (setup preserves alloc)
          -- so we can use same-frame to relate to alloc-after-backup
          setup-frame-eq' : current-frame alloc-after-setup ≡ current-frame alloc-after-backup
          setup-frame-eq' = trans (exec-trace-preserves-frame setup-trace s alloc) refl

          setup-cap-eq' : frame-capacity alloc-after-setup ≡ frame-capacity alloc-after-backup
          setup-cap-eq' = trans (exec-trace-preserves-capacity' setup-trace s alloc setup-tpc) refl

          -- exec f-trace s-after-setup alloc-after-setup = exec f-trace s-after-setup alloc-after-backup
          f-same-frame' : proj₁ (exec-trace f-trace s-after-setup alloc-after-setup) ≡
                          proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)
          f-same-frame' = exec-trace-state-same-frame f-trace s-after-setup
                            alloc-after-setup alloc-after-backup setup-frame-eq' setup-cap-eq'

          -- So s-after-setup-f = exec f-trace s-after-setup alloc-after-backup
          setup-f-via-backup : s-after-setup-f ≡ proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)
          setup-f-via-backup = trans setup-f-decomp f-same-frame'

          -- Setup preserves Input register
          setup-input-eq : readReg (regs s) Input ≡ readReg (regs s-after-setup) Input
          setup-input-eq =
            let
              s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              mov-input : readReg (regs s-after-mov) Input ≡ readReg (regs s) Input
              mov-input = trans (cong (λ st → readReg (regs st) Input)
                                      (mov-to-output-state-eq s alloc not-halted))
                                (writeReg-same (regs s) Output (readReg (regs s) Input))
              alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              not-halted-mov : halted s-after-mov ≡ false
              not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              s-after-store = proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)
              -- store-at-slot produces writeLoc s-after-mov loc output, and writeLoc preserves regs
              store-backup-loc = OnStack (current-frame alloc-after-mov) backup-slot
              store-output = readReg (regs s-after-mov) Output
              store-input : readReg (regs s-after-store) Input ≡ readReg (regs s-after-mov) Input
              store-input = trans (cong (λ st → readReg (regs st) Input)
                                        (store-at-slot-state-eq backup-slot s-after-mov alloc-after-mov not-halted-mov))
                                  (cong (λ r → readReg r Input)
                                        (writeLoc-regs s-after-mov store-backup-loc store-output))
              decomp : s-after-setup ≡ s-after-store
              decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
            in sym (trans (cong (λ st → readReg (regs st) Input) decomp)
                          (trans store-input mov-input))

          -- Setup preserves halted
          setup-halted-eq : halted s ≡ halted s-after-setup
          setup-halted-eq = sym (trans not-halted-after-setup (sym not-halted))

          -- Slots in [suc backup-slot, reclaim-f) agree in s and s-after-setup
          setup-slots-eq : ∀ slot → suc backup-slot ≤ slot → slot < reclaim-f →
            readLoc s (OnStack (current-frame alloc-after-backup) slot) ≡
            readLoc s-after-setup (OnStack (current-frame alloc-after-backup) slot)
          setup-slots-eq slot lo hi =
            let
              setup-writes-below' : TraceWritesBelow (suc backup-slot) setup-trace
              setup-writes-below' = ≤-refl , tt
            in sym (exec-trace-preserves-slot-above setup-trace s alloc
                     (current-frame alloc) slot (suc backup-slot) refl lo setup-writes-below')

          -- loc' agrees in s and s-after-setup (since loc' ≠ backup-slot)
          setup-loc-eq : readLoc s loc' ≡ readLoc s-after-setup loc'
          setup-loc-eq =
            let
              s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              not-halted-mov : halted s-after-mov ≡ false
              not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              -- mov-to-output preserves all memory
              mov-preserves : readLoc s-after-mov loc' ≡ readLoc s loc'
              mov-preserves = mov-to-output-preserves-readLoc s alloc loc' not-halted
              -- store-at-slot backup-slot preserves loc' ≠ backup-slot
              backup-loc' = OnStack (current-frame alloc-after-mov) backup-slot
              frame-after-mov-eq : current-frame alloc-after-mov ≡ current-frame alloc
              frame-after-mov-eq = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
              neq-backup-mov : backup-loc' ≢ loc'
              neq-backup-mov = subst (λ f → OnStack f backup-slot ≢ loc') (sym frame-after-mov-eq) (λ eq → neq-backup' (sym eq))
              -- Use exec-abstract via exec-trace-single
              store-preserves-abstract : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov alloc-after-mov)) loc' ≡
                                         readLoc s-after-mov loc'
              store-preserves-abstract = store-at-slot-preserves-disjoint backup-slot s-after-mov alloc-after-mov loc' neq-backup-mov
              -- Connect exec-trace to exec-abstract
              store-via-abstract : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov) ≡
                                   proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov alloc-after-mov)
              store-via-abstract = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov alloc-after-mov not-halted-mov)
              store-preserves : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)) loc' ≡
                                readLoc s-after-mov loc'
              store-preserves = trans (cong (λ st → readLoc st loc') store-via-abstract) store-preserves-abstract
              decomp : s-after-setup ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)
              decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
            in sym (trans (cong (λ st → readLoc st loc') decomp)
                          (trans store-preserves mov-preserves))

          -- Use exec-trace-mem-equiv: since s and s-after-setup agree on inputs to f-trace and on loc',
          -- the results agree on loc'
          mem-equiv : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) loc' ≡
                      readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)) loc'
          mem-equiv = exec-trace-mem-equiv f-trace s s-after-setup alloc-after-backup
                        (suc backup-slot) reclaim-f loc'
                        setup-input-eq setup-halted-eq not-halted setup-slots-eq
                        f-slot-reads f-slot-reads-below setup-loc-eq

        in trans (cong (λ st → readLoc st loc') s1-via-trace)
                 (trans mem-equiv (cong (λ st → readLoc st loc') (sym setup-f-via-backup)))

      mem-agree-fst : ∀ loc' → BeforeFrontier alloc₁-reclaimed loc' →
                      loc' ≢ OnStack (current-frame alloc) backup-slot →
                      readLoc s₁ loc' ≡ readLoc s-final loc'
      -- Disjointness helper: loc' before alloc₁-reclaimed ⇒ loc' not at slots ≥ reclaim-f
      disjoint-fst : ∀ loc' → BeforeFrontier alloc₁-reclaimed loc' →
                     ∀ slot' → reclaim-f ≤ slot' → OnStack frame slot' ≢ loc'
      disjoint-fst loc' (stack-before frame-eq slot<rf) slot' rf≤slot' eq =
        let slot'-eq : slot' ≡ slot-of loc'
            slot'-eq = cong slot-of eq
            slot-of-loc<rf : slot-of loc' < reclaim-f
            slot-of-loc<rf = subst (_< reclaim-f) (cong slot-of (cong (λ f → OnStack f (slot-of loc')) (sym frame-eq))) slot<rf
        in <⇒≢ (≤-trans slot-of-loc<rf rf≤slot') (sym slot'-eq)
      disjoint-fst loc' (stack-ancestor cf≺f _) slot' rf≤slot' eq =
        ≺⇒≢ cf≺f (cong frame-of-loc eq)
      disjoint-fst _ (heap-before _) _ _ ()

      mem-agree-fst loc' bf neq-backup =
        let
          disjoint : ∀ slot' → reclaim-f ≤ slot' → OnStack frame slot' ≢ loc'
          disjoint = disjoint-fst loc' bf

          -- rest-after-f preserves loc'
          rest-preserves : readLoc (proj₁ (exec-trace rest-after-f s-after-setup-f alloc-after-setup-f)) loc' ≡
                           readLoc s-after-setup-f loc'
          rest-preserves = exec-trace-preserves-disjoint rest-after-f s-after-setup-f alloc-after-setup-f
                             loc' reclaim-f rest-after-f-writes-above
                             (λ slot bound eq → disjoint slot bound (trans (cong (λ f → OnStack f slot) (sym frame-after-setup-f)) eq))

          -- Combine: s-final = exec rest s-after-setup-f, and rest preserves loc'
          s-final-eq : readLoc s-final loc' ≡ readLoc s-after-setup-f loc'
          s-final-eq = trans (cong (λ st → readLoc st loc') s-final-via-rest) rest-preserves
        in trans (s1-agrees-setup-f loc' bf neq-backup) (sym s-final-eq)

      -- Similar for snd: final-trace writes above reclaim-g
      final-trace-writes-above : TraceWritesAbove reclaim-g final-trace
      final-trace-writes-above = n≤1+n reclaim-g , tt  -- snd-slot = suc reclaim-g ≥ reclaim-g

      -- s₂ and s-before-final agree on locations before alloc₂-reclaimed
      -- Both are results of executing g-trace, starting from s₁' and s-before-g respectively.
      -- Uses exec-trace-mem-equiv to show they agree if starting states agree on relevant inputs.
      s2-agrees-before-final : ∀ loc' → BeforeFrontier alloc₂-reclaimed loc' →
                               loc' ≢ OnStack frame backup-slot →
                               readLoc s₂ loc' ≡ readLoc s-before-final loc'
      s2-agrees-before-final loc' bf neq-backup = result-proof
        where
        -- Helper to extract slot from stack location
        slot-of-loc : ValueLocation FS → ℕ
        slot-of-loc (OnStack _ k) = k
        slot-of-loc (OnHeap _) = 0

        -- s₂ = exec g-trace s₁' alloc₁-reclaimed (via g-correct)
        s2-via-trace : s₂ ≡ proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)
        s2-via-trace = sym g-correct

        -- s-before-final = exec g-trace s-before-g alloc₁-reclaimed (via s-before-final-via-g + same-frame)
        g-same-frame' : proj₁ (exec-trace g-trace s-before-g alloc-before-g) ≡
                        proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed)
        g-same-frame' = exec-trace-state-same-frame g-trace s-before-g alloc-before-g alloc₁-reclaimed
                          alloc-frame-eq alloc-cap-eq

        s-before-final-via-g' : s-before-final ≡ proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed)
        s-before-final-via-g' = trans s-before-final-via-g g-same-frame'

        -- Prerequisites for exec-trace-mem-equiv:
        -- 1. Input registers agree
        input-eq' : readReg (regs s₁') Input ≡ readReg (regs s-before-g) Input
        input-eq' = trans rdi-eq₁ (sym (trans (cong (λ st → readReg (regs st) Input) s-before-g-eq)
                                               (restore-input-sets-input backup-slot s-after-store-fst alloc-after-store-fst input-loc
                                                  not-halted-after-store-fst backup-has-input')))

        -- 2. Halted flags agree
        not-halted-s1'' : halted s₁' ≡ false
        not-halted-s1'' = IRResultAWF.not-halted result-f

        not-halted-s-before-g' : halted s-before-g ≡ false
        not-halted-s-before-g' = trans (cong halted s-before-g-eq) not-halted-after-restore

        halted-eq' : halted s₁' ≡ halted s-before-g
        halted-eq' = trans not-halted-s1'' (sym not-halted-s-before-g')

        -- 3. Slots in [reclaim-f, reclaim-g) agree
        -- Both s₁' and s-before-g preserve these slots from s
        -- Symmetric version of slots-eq-g from not-halted-before-final
        slots-eq' : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
                    readLoc s₁' (OnStack (current-frame alloc₁-reclaimed) slot) ≡
                    readLoc s-before-g (OnStack (current-frame alloc₁-reclaimed) slot)
        slots-eq' slot rf≤slot slot<rg =
          let
            loc = OnStack (current-frame alloc) slot

            -- s₁' preserves slot from s (f-trace writes below reclaim-f)
            s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
            s1-via-trace = sym (IRResultAWF.trace-correct result-f)

            s1-eq-s : readLoc s₁ loc ≡ readLoc s loc
            s1-eq-s = trans (cong (λ st → readLoc st loc) s1-via-trace)
                            (exec-trace-preserves-slot-above f-trace s alloc-after-backup
                               (current-frame alloc-after-backup) slot reclaim-f refl rf≤slot f-writes-below)

            s1'-eq-s : readLoc s₁' loc ≡ readLoc s loc
            s1'-eq-s = s1-eq-s  -- s₁' has same memory as s₁

            -- s-before-g preserves slot from s
            fst-slot-neq : fst-slot ≢ slot
            fst-slot-neq eq = <⇒≢ slot<rg (sym eq)

            -- setup preserves slot (writes only backup-slot < reclaim-f ≤ slot)
            backup-below-rf : backup-slot < reclaim-f
            backup-below-rf = IRResultAWF.reclaim-monotone result-f

            backup-neq : backup-slot ≢ slot
            backup-neq eq = <⇒≢ (≤-trans backup-below-rf rf≤slot) eq

            -- Setup preservation
            s-after-mov'' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
            alloc-after-mov'' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)

            mov-preserves' : readLoc s-after-mov'' loc ≡ readLoc s loc
            mov-preserves' = mov-to-output-preserves-readLoc s alloc loc not-halted

            not-halted-mov'' : halted s-after-mov'' ≡ false
            not-halted-mov'' = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted

            frame-after-mov'' : current-frame alloc-after-mov'' ≡ current-frame alloc
            frame-after-mov'' = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc

            loc-neq'' : OnStack (current-frame alloc-after-mov'') backup-slot ≢ loc
            loc-neq'' eq' = backup-neq (trans (cong slot-of eq') (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-mov''))))

            store-preserves' : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')) loc ≡
                               readLoc s-after-mov'' loc
            store-preserves' = store-at-slot-preserves-disjoint backup-slot s-after-mov'' alloc-after-mov'' loc loc-neq''

            decomp' : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'')
            decomp' = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc

            store-via-abstract' : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'') ≡
                                  proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')
            store-via-abstract' = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'' not-halted-mov'')

            setup-preserves' : readLoc s-after-setup' loc ≡ readLoc s loc
            setup-preserves' = trans (cong (λ st → readLoc st loc) decomp')
                                     (trans (cong (λ st → readLoc st loc) store-via-abstract')
                                            (trans store-preserves' mov-preserves'))

            -- store-fst-via-abstract for this context
            store-fst-via-abstract'' : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
            store-fst-via-abstract'' = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')

            -- s-before-g preserves slot from s
            s-before-g-eq-s : readLoc s-before-g loc ≡ readLoc s loc
            s-before-g-eq-s =
              trans (cong (λ st → readLoc st loc) s-before-g-eq)
                    (trans (restore-input-preserves-readLoc backup-slot s-after-store-fst alloc-after-store-fst input-loc loc not-halted-after-store-fst backup-has-input')
                           (trans (cong (λ st → readLoc st loc) store-fst-via-abstract'')
                                  (trans (store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f' loc
                                           (λ eq → fst-slot-neq (trans (cong slot-of eq)
                                                                       (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-f'))))))
                                         (trans (cong (λ st → readLoc st loc) (exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup setup-frame-eq setup-cap-eq))
                                                (trans (exec-trace-preserves-slot-above f-trace s-after-setup' alloc-after-backup
                                                         (current-frame alloc-after-backup) slot reclaim-f refl rf≤slot f-writes-below)
                                                       setup-preserves')))))
          in trans s1'-eq-s (sym s-before-g-eq-s)

        -- 4. loc' itself is equal in s₁' and s-before-g
        -- Case split on BeforeFrontier to handle stack-before, stack-ancestor, heap-before
        loc-eq' : readLoc s₁' loc' ≡ readLoc s-before-g loc'
        loc-eq' = loc-eq-by-case bf
          where
          -- Helper: s₁' preserves stack locations below suc backup-slot from s
          -- (f-trace writes above suc backup-slot, and s₁' = s₁ with regs modified)
          s1'-preserves-below-sb : ∀ slot → slot < suc backup-slot →
            readLoc s₁' (OnStack (current-frame alloc) slot) ≡
            readLoc s (OnStack (current-frame alloc) slot)
          s1'-preserves-below-sb slot slot<sb =
            let
              loc = OnStack (current-frame alloc) slot
              s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
              s1-via-trace = sym (IRResultAWF.trace-correct result-f)
              s1-eq-s : readLoc s₁ loc ≡ readLoc s loc
              s1-eq-s = trans (cong (λ st → readLoc st loc) s1-via-trace)
                              (exec-trace-preserves-disjoint f-trace s alloc-after-backup loc (suc backup-slot)
                                 (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                                 (λ slot' bound eq → <⇒≢ (<-≤-trans slot<sb bound) (sym (cong slot-of eq))))
            in s1-eq-s

          -- Helper: s-before-g preserves stack locations below suc backup-slot (excluding backup-slot) from s
          s-before-g-preserves-below-sb : ∀ slot → slot < suc backup-slot → slot ≢ backup-slot →
            readLoc s-before-g (OnStack (current-frame alloc) slot) ≡
            readLoc s (OnStack (current-frame alloc) slot)
          s-before-g-preserves-below-sb slot slot<sb neq-backup' =
            let
              loc = OnStack (current-frame alloc) slot

              -- Setup preserves loc (slot ≠ backup-slot)
              s-after-mov'' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov'' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              mov-preserves' : readLoc s-after-mov'' loc ≡ readLoc s loc
              mov-preserves' = mov-to-output-preserves-readLoc s alloc loc not-halted
              not-halted-mov'' : halted s-after-mov'' ≡ false
              not-halted-mov'' = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              frame-after-mov'' : current-frame alloc-after-mov'' ≡ current-frame alloc
              frame-after-mov'' = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
              loc-neq-backup : OnStack (current-frame alloc-after-mov'') backup-slot ≢ loc
              loc-neq-backup eq' = neq-backup' (sym (cong slot-of eq'))
              store-preserves' : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')) loc ≡
                                 readLoc s-after-mov'' loc
              store-preserves' = store-at-slot-preserves-disjoint backup-slot s-after-mov'' alloc-after-mov'' loc loc-neq-backup
              decomp' : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'')
              decomp' = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              store-via-abstract' : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'') ≡
                                    proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')
              store-via-abstract' = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'' not-halted-mov'')
              setup-preserves' : readLoc s-after-setup' loc ≡ readLoc s loc
              setup-preserves' = trans (cong (λ st → readLoc st loc) decomp')
                                       (trans (cong (λ st → readLoc st loc) store-via-abstract')
                                              (trans store-preserves' mov-preserves'))

              -- f-trace preserves loc (slot < suc backup-slot means outside f-trace write range)
              f-preserves : readLoc s-after-f' loc ≡ readLoc s-after-setup' loc
              f-preserves =
                trans (cong (λ st → readLoc st loc)
                         (exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup setup-frame-eq setup-cap-eq))
                      (exec-trace-preserves-disjoint f-trace s-after-setup' alloc-after-backup loc (suc backup-slot)
                         (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                         (λ slot' bound eq → <⇒≢ (<-≤-trans slot<sb bound) (sym (cong slot-of eq))))

              -- store-fst preserves loc (slot < suc backup-slot < reclaim-f ≤ fst-slot)
              fst-neq : fst-slot ≢ slot
              fst-neq eq = <⇒≢ (<-≤-trans slot<sb (≤-trans (IRResultAWF.reclaim-monotone result-f) (IRResultAWF.reclaim-monotone result-g))) (sym eq)
              store-fst-via-abstract'' : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
              store-fst-via-abstract'' = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')
              loc-neq-fst : OnStack (current-frame alloc-after-f') fst-slot ≢ loc
              loc-neq-fst eq = fst-neq (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f slot) (sym frame-after-f'))))
              store-fst-preserves : readLoc s-after-store-fst loc ≡ readLoc s-after-f' loc
              store-fst-preserves = trans (cong (λ st → readLoc st loc) store-fst-via-abstract'')
                                          (store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f' loc loc-neq-fst)

              -- restore-input preserves stack memory
              restore-preserves : readLoc s-after-restore loc ≡ readLoc s-after-store-fst loc
              restore-preserves = restore-input-preserves-readLoc backup-slot s-after-store-fst alloc-after-store-fst input-loc loc
                                    not-halted-after-store-fst backup-has-input'
            in trans (cong (λ st → readLoc st loc) s-before-g-eq)
                     (trans restore-preserves (trans store-fst-preserves (trans f-preserves setup-preserves')))

          -- Helper for stack-before case: decide whether k is below suc backup-slot or at/above reclaim-f
          stack-before-helper : ∀ k → k < reclaim-g → k ≢ backup-slot →
            readLoc s₁' (OnStack (current-frame alloc) k) ≡
            readLoc s-before-g (OnStack (current-frame alloc) k)
          stack-before-helper k slot<rg k-neq-backup with k <? suc backup-slot | reclaim-f ≤? k
          -- k < suc backup-slot: both preserve from s
          ... | yes k<sb | _ =
            let
              loc = OnStack (current-frame alloc) k
              s1'-eq : readLoc s₁' loc ≡ readLoc s loc
              s1'-eq = s1'-preserves-below-sb k k<sb
              sbg-eq : readLoc s-before-g loc ≡ readLoc s loc
              sbg-eq = s-before-g-preserves-below-sb k k<sb k-neq-backup
            in trans s1'-eq (sym sbg-eq)
          -- reclaim-f ≤ k: use slots-eq'
          ... | no _ | yes rf≤k = slots-eq' k rf≤k slot<rg
          -- suc backup-slot ≤ k < reclaim-f: both have f-trace output at k
          -- Use transitivity through s (both f-trace executions start from equivalent states)
          ... | no ¬k<sb | no ¬rf≤k =
            let
              loc = OnStack (current-frame alloc) k
              sb≤k : suc backup-slot ≤ k
              sb≤k = ≮⇒≥ ¬k<sb
              k<rf : k < reclaim-f
              k<rf = ≰⇒> ¬rf≤k

              -- Both s₁' and s-before-g have f-trace output at slot k
              -- s₁' = s₁ = f-trace(s) at k
              -- s-before-g = restore(store-fst(f-trace(setup(s)))) at k = f-trace(setup(s)) at k
              -- Since f-trace writes to k and k < reclaim-f ≤ fst-slot, store-fst preserves k
              -- Since restore doesn't write to stack, restore preserves k

              -- f-trace from s
              s1-via-f : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
              s1-via-f = sym (IRResultAWF.trace-correct result-f)

              -- s-after-f' is f-trace from s-after-setup'
              -- s-before-g = restore(store-fst(s-after-f'))
              -- k < reclaim-f ≤ fst-slot, so store-fst preserves k
              -- restore preserves stack, so s-before-g has same value at k as s-after-f'
              k<fst : k < fst-slot
              k<fst = <-≤-trans k<rf (IRResultAWF.reclaim-monotone result-g)

              fst-neq-k : fst-slot ≢ k
              fst-neq-k eq = <⇒≢ k<fst (sym eq)

              store-fst-via-abstract'' : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
              store-fst-via-abstract'' = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')

              loc-neq-fst : OnStack (current-frame alloc-after-f') fst-slot ≢ loc
              loc-neq-fst eq = fst-neq-k (trans (cong slot-of eq) (cong slot-of (cong (λ f → OnStack f k) (sym frame-after-f'))))

              store-fst-preserves-k : readLoc s-after-store-fst loc ≡ readLoc s-after-f' loc
              store-fst-preserves-k = trans (cong (λ st → readLoc st loc) store-fst-via-abstract'')
                                            (store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f' loc loc-neq-fst)

              restore-preserves-k : readLoc s-after-restore loc ≡ readLoc s-after-store-fst loc
              restore-preserves-k = restore-input-preserves-readLoc backup-slot s-after-store-fst alloc-after-store-fst input-loc loc
                                      not-halted-after-store-fst backup-has-input'

              sbg-via-f' : readLoc s-before-g loc ≡ readLoc s-after-f' loc
              sbg-via-f' = trans (cong (λ st → readLoc st loc) s-before-g-eq)
                                 (trans restore-preserves-k store-fst-preserves-k)

              -- s-after-f' = f-trace(s-after-setup') and we need to relate to f-trace(s)
              -- Both f-trace executions agree at k because:
              -- - Input registers are the same (setup preserves Input)
              -- - Slots in read range [suc backup-slot, reclaim-f) agree (setup preserves these)
              -- - k is in f-trace write range, so f-trace writes to k

              -- Use exec-trace-preserves-slot-above on f-trace(s-after-setup') for slot k ≥ suc backup-slot
              -- but k < reclaim-f, so this is the write range, not preserve range

              -- Actually, both s₁' and s-before-g have the OUTPUT of f-trace at k
              -- Since both f-traces start from equivalent states and agree on inputs,
              -- they produce the same output at k

              -- For s₁': readLoc s₁' loc = readLoc (f-trace s) loc
              s1'-via-f : readLoc s₁' loc ≡ readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) loc
              s1'-via-f = cong (λ st → readLoc st loc) s1-via-f

              -- For s-before-g: we showed sbg-via-f' : readLoc s-before-g loc ≡ readLoc s-after-f' loc
              -- s-after-f' = exec f-trace s-after-setup' alloc-after-setup'
              -- Need to show: exec f-trace s-after-setup' ... ≡ exec f-trace s ... at loc

              -- Use exec-trace-mem-equiv for f-trace comparing s and s-after-setup'
              -- setup-input-eq : Input s = Input s-after-setup'
              setup-input-eq' : readReg (regs s) Input ≡ readReg (regs s-after-setup') Input
              setup-input-eq' =
                let
                  s-after-mov = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
                  mov-input : readReg (regs s-after-mov) Input ≡ readReg (regs s) Input
                  mov-input = trans (cong (λ st → readReg (regs st) Input) (mov-to-output-state-eq s alloc not-halted))
                                    (writeReg-same (regs s) Output (readReg (regs s) Input))
                  alloc-after-mov = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
                  not-halted-mov : halted s-after-mov ≡ false
                  not-halted-mov = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
                  s-after-store = proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov alloc-after-mov)
                  store-input : readReg (regs s-after-store) Input ≡ readReg (regs s-after-mov) Input
                  store-input = trans (cong (λ st → readReg (regs st) Input)
                                            (store-at-slot-state-eq backup-slot s-after-mov alloc-after-mov not-halted-mov))
                                      (cong (λ r → readReg r Input)
                                            (writeLoc-regs s-after-mov (OnStack (current-frame alloc-after-mov) backup-slot) (readReg (regs s-after-mov) Output)))
                  decomp : s-after-setup' ≡ s-after-store
                  decomp = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
                in sym (trans (cong (λ st → readReg (regs st) Input) decomp) (trans store-input mov-input))

              -- setup-halted-eq' : halted s = halted s-after-setup'
              setup-halted-eq' : halted s ≡ halted s-after-setup'
              setup-halted-eq' = sym (trans not-halted-after-setup (sym not-halted))

              -- setup-slots-eq': slots in [suc backup-slot, reclaim-f) agree in s and s-after-setup'
              setup-slots-eq' : ∀ slot' → suc backup-slot ≤ slot' → slot' < reclaim-f →
                readLoc s (OnStack (current-frame alloc-after-backup) slot') ≡
                readLoc s-after-setup' (OnStack (current-frame alloc-after-backup) slot')
              setup-slots-eq' slot' sb≤slot' slot'<rf =
                sym (exec-trace-preserves-slot-above setup-seg s alloc (current-frame alloc) slot' (suc backup-slot) refl sb≤slot'
                      (≤-refl , tt))

              -- setup-loc-eq': k agrees in s and s-after-setup'
              -- Since k is in [suc backup-slot, reclaim-f), setup preserves k
              setup-loc-eq' : readLoc s loc ≡ readLoc s-after-setup' loc
              setup-loc-eq' = sym (exec-trace-preserves-slot-above setup-seg s alloc (current-frame alloc) k (suc backup-slot) refl sb≤k (≤-refl , tt))

              -- Use exec-trace-mem-equiv to relate the two f-trace executions
              f-same-frame' : proj₁ (exec-trace f-trace s-after-setup' alloc-after-setup') ≡
                              proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)
              f-same-frame' = exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup setup-frame-eq setup-cap-eq

              f-equiv : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) loc ≡
                        readLoc (proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)) loc
              f-equiv = exec-trace-mem-equiv f-trace s s-after-setup' alloc-after-backup
                          (suc backup-slot) reclaim-f loc
                          setup-input-eq' setup-halted-eq' not-halted setup-slots-eq' f-slot-reads f-slot-reads-below setup-loc-eq'

              -- Combine: s₁' at k = f-trace(s) at k = f-trace(s-after-setup') at k = s-after-f' at k = s-before-g at k
              s-after-f'-via-same-frame : readLoc s-after-f' loc ≡ readLoc (proj₁ (exec-trace f-trace s-after-setup' alloc-after-backup)) loc
              s-after-f'-via-same-frame = cong (λ st → readLoc st loc) f-same-frame'
            in trans s1'-via-f (trans f-equiv (trans (sym s-after-f'-via-same-frame) (sym sbg-via-f')))

          -- Case analysis on BeforeFrontier
          loc-eq-by-case : BeforeFrontier alloc₂-reclaimed loc' → readLoc s₁' loc' ≡ readLoc s-before-g loc'
          -- Case 1: stack-before - loc' is on current frame with slot < reclaim-g
          loc-eq-by-case (stack-before {k = k} frame-eq slot<rg) =
            let
              loc = OnStack (current-frame alloc) k
              loc'-eq-loc : loc' ≡ loc
              loc'-eq-loc = cong (λ f → OnStack f k) frame-eq

              k-neq-backup : k ≢ backup-slot
              k-neq-backup eq = neq-backup (trans (cong (λ f → OnStack f k) frame-eq) (cong (OnStack frame) eq))

              result : readLoc s₁' loc ≡ readLoc s-before-g loc
              result = stack-before-helper k slot<rg k-neq-backup
            in subst (λ l → readLoc s₁' l ≡ readLoc s-before-g l) (sym loc'-eq-loc) result

          -- Case 2: stack-ancestor - loc' is on ancestor frame
          loc-eq-by-case (stack-ancestor {f'} {k} f'≺frame _) =
            let
              -- Both s₁' and s-before-g preserve ancestor frame locations from s
              -- f-trace only writes to current frame, not ancestor frames
              loc = OnStack f' k

              -- s₁' = s₁ with modified regs, so readLoc s₁' = readLoc s₁
              s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
              s1-via-trace = sym (IRResultAWF.trace-correct result-f)

              -- f-trace preserves ancestor frames (writes to current frame only)
              -- alloc₂-reclaimed, alloc-after-backup, alloc all have the same current-frame
              f-preserves-ancestor : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) loc ≡ readLoc s loc
              f-preserves-ancestor = exec-trace-preserves-disjoint f-trace s alloc-after-backup loc (suc backup-slot)
                                       (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                                       (λ slot bound eq → ≺⇒≢ f'≺frame (trans refl (cong frame-of-loc eq)))

              s1'-eq-s : readLoc s₁' loc ≡ readLoc s loc
              s1'-eq-s = trans (cong (λ st → readLoc st loc) s1-via-trace) f-preserves-ancestor

              -- s-before-g also preserves ancestor frames
              -- Setup preserves (writes current frame only)
              s-after-mov'' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov'' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              mov-preserves' : readLoc s-after-mov'' loc ≡ readLoc s loc
              mov-preserves' = mov-to-output-preserves-readLoc s alloc loc not-halted
              not-halted-mov'' : halted s-after-mov'' ≡ false
              not-halted-mov'' = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              frame-after-mov'' : current-frame alloc-after-mov'' ≡ current-frame alloc
              frame-after-mov'' = exec-trace-preserves-frame (mov-to-output ∷ []) s alloc
              loc-neq-backup : OnStack (current-frame alloc-after-mov'') backup-slot ≢ loc
              loc-neq-backup eq' = ≺⇒≢ f'≺frame (trans (sym frame-after-mov'') (cong frame-of-loc eq'))
              store-preserves' : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')) loc ≡
                                 readLoc s-after-mov'' loc
              store-preserves' = store-at-slot-preserves-disjoint backup-slot s-after-mov'' alloc-after-mov'' loc loc-neq-backup
              decomp' : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'')
              decomp' = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              store-via-abstract' : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'') ≡
                                    proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')
              store-via-abstract' = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'' not-halted-mov'')
              setup-preserves' : readLoc s-after-setup' loc ≡ readLoc s loc
              setup-preserves' = trans (cong (λ st → readLoc st loc) decomp')
                                       (trans (cong (λ st → readLoc st loc) store-via-abstract')
                                              (trans store-preserves' mov-preserves'))

              -- f-trace preserves ancestor (already shown)
              f-preserves' : readLoc s-after-f' loc ≡ readLoc s-after-setup' loc
              f-preserves' =
                trans (cong (λ st → readLoc st loc)
                         (exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup setup-frame-eq setup-cap-eq))
                      (exec-trace-preserves-disjoint f-trace s-after-setup' alloc-after-backup loc (suc backup-slot)
                         (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                         (λ slot bound eq → ≺⇒≢ f'≺frame (cong frame-of-loc eq)))

              -- store-fst preserves ancestor
              store-fst-via-abstract'' : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
              store-fst-via-abstract'' = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')
              loc-neq-fst : OnStack (current-frame alloc-after-f') fst-slot ≢ loc
              loc-neq-fst eq = ≺⇒≢ f'≺frame (trans (sym frame-after-f') (cong frame-of-loc eq))
              store-fst-preserves : readLoc s-after-store-fst loc ≡ readLoc s-after-f' loc
              store-fst-preserves = trans (cong (λ st → readLoc st loc) store-fst-via-abstract'')
                                          (store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f' loc loc-neq-fst)

              -- restore-input preserves stack memory
              restore-preserves : readLoc s-after-restore loc ≡ readLoc s-after-store-fst loc
              restore-preserves = restore-input-preserves-readLoc backup-slot s-after-store-fst alloc-after-store-fst input-loc loc
                                    not-halted-after-store-fst backup-has-input'

              sbg-eq-s : readLoc s-before-g loc ≡ readLoc s loc
              sbg-eq-s = trans (cong (λ st → readLoc st loc) s-before-g-eq)
                               (trans restore-preserves (trans store-fst-preserves (trans f-preserves' setup-preserves')))
            in trans s1'-eq-s (sym sbg-eq-s)

          -- Case 3: heap-before - loc' is on heap
          loc-eq-by-case (heap-before {a} _) =
            let
              loc = OnHeap a

              -- Both s₁' and s-before-g preserve heap locations
              -- All stack operations preserve heap
              s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
              s1-via-trace = sym (IRResultAWF.trace-correct result-f)

              f-preserves-heap : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) loc ≡ readLoc s loc
              f-preserves-heap = exec-trace-preserves-disjoint f-trace s alloc-after-backup loc (suc backup-slot)
                                   (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                                   (λ _ _ ())

              s1'-eq-s : readLoc s₁' loc ≡ readLoc s loc
              s1'-eq-s = trans (cong (λ st → readLoc st loc) s1-via-trace) f-preserves-heap

              -- Setup preserves heap
              s-after-mov'' = proj₁ (exec-trace (mov-to-output ∷ []) s alloc)
              alloc-after-mov'' = proj₂ (exec-trace (mov-to-output ∷ []) s alloc)
              mov-preserves' : readLoc s-after-mov'' loc ≡ readLoc s loc
              mov-preserves' = mov-to-output-preserves-readLoc s alloc loc not-halted
              not-halted-mov'' : halted s-after-mov'' ≡ false
              not-halted-mov'' = trans (cong halted (mov-to-output-state-eq s alloc not-halted)) not-halted
              store-preserves' : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')) loc ≡
                                 readLoc s-after-mov'' loc
              store-preserves' = store-at-slot-preserves-disjoint backup-slot s-after-mov'' alloc-after-mov'' loc (λ ())
              decomp' : s-after-setup' ≡ proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'')
              decomp' = exec-trace-append-state (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc
              store-via-abstract' : proj₁ (exec-trace (store-at-slot backup-slot ∷ []) s-after-mov'' alloc-after-mov'') ≡
                                    proj₁ (exec-abstract (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'')
              store-via-abstract' = cong proj₁ (exec-trace-single (store-at-slot backup-slot) s-after-mov'' alloc-after-mov'' not-halted-mov'')
              setup-preserves' : readLoc s-after-setup' loc ≡ readLoc s loc
              setup-preserves' = trans (cong (λ st → readLoc st loc) decomp')
                                       (trans (cong (λ st → readLoc st loc) store-via-abstract')
                                              (trans store-preserves' mov-preserves'))

              -- f-trace preserves heap
              f-preserves' : readLoc s-after-f' loc ≡ readLoc s-after-setup' loc
              f-preserves' =
                trans (cong (λ st → readLoc st loc)
                         (exec-trace-state-same-frame f-trace s-after-setup' alloc-after-setup' alloc-after-backup setup-frame-eq setup-cap-eq))
                      (exec-trace-preserves-disjoint f-trace s-after-setup' alloc-after-backup loc (suc backup-slot)
                         (trace-writes-above-mono (suc backup-slot) (suc backup-slot) f-trace ≤-refl f-slot-writes)
                         (λ _ _ ()))

              -- store-fst preserves heap
              store-fst-via-abstract'' : s-after-store-fst ≡ proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f' alloc-after-f')
              store-fst-via-abstract'' = cong proj₁ (exec-trace-single (store-at-slot fst-slot) s-after-f' alloc-after-f' not-halted-after-f')
              store-fst-preserves : readLoc s-after-store-fst loc ≡ readLoc s-after-f' loc
              store-fst-preserves = trans (cong (λ st → readLoc st loc) store-fst-via-abstract'')
                                          (store-at-slot-preserves-disjoint fst-slot s-after-f' alloc-after-f' loc (λ ()))

              -- restore-input preserves heap
              restore-preserves : readLoc s-after-restore loc ≡ readLoc s-after-store-fst loc
              restore-preserves = restore-input-preserves-readLoc backup-slot s-after-store-fst alloc-after-store-fst input-loc loc
                                    not-halted-after-store-fst backup-has-input'

              sbg-eq-s : readLoc s-before-g loc ≡ readLoc s loc
              sbg-eq-s = trans (cong (λ st → readLoc st loc) s-before-g-eq)
                               (trans restore-preserves (trans store-fst-preserves (trans f-preserves' setup-preserves')))
            in trans s1'-eq-s (sym sbg-eq-s)

        -- Apply exec-trace-mem-equiv
        result : readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) loc' ≡
                 readLoc (proj₁ (exec-trace g-trace s-before-g alloc₁-reclaimed)) loc'
        result = exec-trace-mem-equiv g-trace s₁' s-before-g alloc₁-reclaimed
                   reclaim-f reclaim-g loc'
                   input-eq' halted-eq' not-halted-s1'' slots-eq' g-slot-reads g-slot-reads-below loc-eq'

        result-proof : readLoc s₂ loc' ≡ readLoc s-before-final loc'
        result-proof = trans (cong (λ st → readLoc st loc') s2-via-trace)
                             (trans result (sym (cong (λ st → readLoc st loc') s-before-final-via-g')))
      mem-agree-snd : ∀ loc' → BeforeFrontier alloc₂-reclaimed loc' →
                      loc' ≢ OnStack (current-frame alloc) backup-slot →
                      readLoc s₂ loc' ≡ readLoc s-final loc'
      -- Disjointness helper for snd
      disjoint-snd : ∀ loc' → BeforeFrontier alloc₂-reclaimed loc' →
                     ∀ slot' → reclaim-g ≤ slot' → OnStack frame slot' ≢ loc'
      disjoint-snd loc' (stack-before frame-eq slot<rg) slot' rg≤slot' eq =
        let slot'-eq : slot' ≡ slot-of loc'
            slot'-eq = cong slot-of eq
            slot-of-loc<rg : slot-of loc' < reclaim-g
            slot-of-loc<rg = subst (_< reclaim-g) (cong slot-of (cong (λ f → OnStack f (slot-of loc')) (sym frame-eq))) slot<rg
        in <⇒≢ (≤-trans slot-of-loc<rg rg≤slot') (sym slot'-eq)
      disjoint-snd loc' (stack-ancestor cf≺f _) slot' rg≤slot' eq =
        ≺⇒≢ cf≺f (cong frame-of-loc eq)
      disjoint-snd _ (heap-before _) _ _ ()

      mem-agree-snd loc' bf neq-backup =
        let
          disjoint : ∀ slot' → reclaim-g ≤ slot' → OnStack frame slot' ≢ loc'
          disjoint = disjoint-snd loc' bf

          final-preserves : readLoc (proj₁ (exec-trace final-trace s-before-final alloc-before-final)) loc' ≡
                            readLoc s-before-final loc'
          final-preserves = exec-trace-preserves-disjoint final-trace s-before-final alloc-before-final
                              loc' reclaim-g final-trace-writes-above
                              (λ slot bound eq → disjoint slot bound (trans (cong (λ f → OnStack f slot) (sym frame-preserved-trace)) eq))

          s-final-eq : readLoc s-final loc' ≡ readLoc s-before-final loc'
          s-final-eq = trans (cong (λ st → readLoc st loc') s-final-decomp) final-preserves
        in trans (s2-agrees-before-final loc' bf neq-backup) (sym s-final-eq)

      fst-valid-s-final : ValidAtWF mF alloc₃ (eval primSem f x) fst-loc s-final
      fst-valid-s-final = validityWF-frontier-advance (eval primSem f x) fst-loc s-final
                            refl  -- frame preserved
                            (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))  -- slot monotone
                            ≤-refl  -- heap monotone
                            (validityWF-mem-preserved-excluding
                              alloc₁-reclaimed
                              (eval primSem f x)
                              fst-loc
                              (current-frame alloc)
                              backup-slot
                              s₁
                              s-final
                              fst-before₁-reclaimed
                              mem-agree-fst
                              fst-valid-s1)

      snd-valid-s-final : ValidAtWF mG alloc₃ (eval primSem g x) snd-loc s-final
      snd-valid-s-final = validityWF-frontier-advance (eval primSem g x) snd-loc s-final
                            refl  -- frame preserved
                            (m≤m+n reclaim-g ps)  -- slot monotone
                            ≤-refl  -- heap monotone
                            (validityWF-mem-preserved-excluding
                              alloc₂-reclaimed
                              (eval primSem g x)
                              snd-loc
                              (current-frame alloc)
                              backup-slot
                              s₂
                              s-final
                              snd-before₂-reclaimed
                              mem-agree-snd
                              snd-valid-s2)

      pair-valid-wf-final : ValidAtWF m alloc₃ (pair (eval primSem f x) (eval primSem g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-wf fst-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before₃ fst-valid-s-final snd-valid-s-final

      pair-reclaim-preserves-validity : ∀ fits → ValidAtWF m alloc₃ (pair (eval primSem f x) (eval primSem g x)) pair-loc s-final
      pair-reclaim-preserves-validity fits = pair-valid-wf-final
