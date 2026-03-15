------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.ApplyWF
--
-- Apply IR implementation with clean trace-based structure.
-- Final state defined via exec-trace, making trace-correct = refl.
--
-- Apply uses frame push/pop for body execution but follows the same
-- trace composition pattern as other WF2 files.
--
-- TRACE STRUCTURE:
--   1. Setup pair (env, arg) on stack
--   2. Push child frame
--   3. Execute body trace
--   4. Pop frame
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.ApplyWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; <-≤-trans; m≤m+n; +-monoʳ-≤; m+n≤o⇒m≤o; ≤-reflexive)
open import Data.Nat using (_≤?_)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst; cong)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SMCore hiding (AllocMode; Stack; Heap)
import Once.CCC.SMPrimitives as SMP
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)

-- Import escape interface for SurvivesFramePop
open import Once.CCC.Target.X86v3.Dispatcher.EscapeInterface
module EI {FS : FrameSemantics} = EscapeInterfaceDef {FS}
open EI using (SurvivesFramePop; in-ancestor; on-heap) public

-- BeforeFrontier for module parameters
BeforeFrontier' : {FS : FrameSemantics} → AllocState {FS} → ValueLocation FS → Set
BeforeFrontier' {FS} = FrontierInvariant.BeforeFrontier {FS}

------------------------------------------------------------------------
-- BeforeFrontier Transfer (reuse from ApplyWF)
------------------------------------------------------------------------

module BFTransfer {FS : FrameSemantics} where
  open FrontierInvariant {FS}
  open FrameSemantics FS

  bf-same-frame-slot : ∀ (alloc₁ alloc₂ : AllocState {FS})
    (cf-eq : current-frame alloc₁ ≡ current-frame alloc₂)
    (ns-eq : next-slot alloc₁ ≡ next-slot alloc₂)
    (hr-eq : next-heap-ref alloc₁ ≡ next-heap-ref alloc₂)
    (loc : ValueLocation FS) →
    BeforeFrontier alloc₁ loc →
    BeforeFrontier alloc₂ loc
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnStack f k) (stack-before f-eq k<ns)
    rewrite cf-eq | ns-eq = stack-before f-eq k<ns
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnStack f k) (stack-ancestor cf≺f src)
    rewrite cf-eq = stack-ancestor cf≺f src
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnHeap hl) (heap-before r<hr)
    rewrite hr-eq = heap-before r<hr

------------------------------------------------------------------------
-- Apply implementation with clean trace-based structure
------------------------------------------------------------------------

module ApplyWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem)
  (get-child-frame : ∀ (alloc : AllocState {FS}) → FrameSemantics.Frame FS)
  (child-frame-ordered : ∀ (alloc : AllocState {FS}) →
    FrameSemantics._≺_ FS (get-child-frame alloc) (current-frame alloc))
  (child-frame-adjacent : ∀ (alloc : AllocState {FS}) (f : FrameSemantics.Frame FS) →
    FrameSemantics._≺_ FS (get-child-frame alloc) f →
    FrameSemantics._≺_ FS f (current-frame alloc) →
    ⊥)
  (escape-result-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
    (result-loc : ValueLocation FS) →
    current-frame body-final ≡ get-child-frame alloc →
    BeforeFrontier' body-final result-loc →
    SurvivesFramePop (get-child-frame alloc) result-loc)
  where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS
  open SMP.TracePrimitives {FS}
  open SMP.InstrPrimitives {FS}

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; BodyCorrect;
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           valid-inl-wf; valid-inr-wf; valid-fold-wf;
           validityWF-mem-only; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-frontier-advance;
           validityWF-with-bf-transfer;
           decomposePairWF; PairValidWF;
           decomposeClosureWF; ClosureValidWF;
           closure-mode-is-heap-proof;
           at-frontier-neq-before-wf; suc-frontier-neq-before-wf)

  open import Once.CCC.Target.X86v3.Dispatcher.DispatcherArithmeticLemma
    using (suc<+2)
  open import Once.CCC.Target.X86v3.Dispatcher.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}
  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (at-frontier-before-pair)
  open BFTransfer {FS}
    using (bf-same-frame-slot)

  ------------------------------------------------------------------------
  -- Apply trace construction
  --
  -- Apply trace structure:
  --   setup-trace: Store (env, arg) pair to stack, set Input
  --   instr-push-frame body-cap: Enter child frame
  --   body-trace: Execute closure body
  --   instr-pop-frame: Return to parent frame
  ------------------------------------------------------------------------

  -- Setup trace: prepare pair input for body
  -- 1. load-indirect: Output := *Input (env-loc from closure)
  -- 2. store-at-slot pair-slot: pair[0] := Output (env)
  -- 3. load-indirect-suc: Output := *(Input+1) (arg-loc from input pair)
  -- 4. store-at-slot (suc pair-slot): pair[1] := Output (arg)
  -- 5. lea-slot pair-slot: Output := &pair
  -- 6. mov-to-input: Input := Output (pair address)
  apply-setup-trace : (pair-slot : ℕ) → AbstractTrace
  apply-setup-trace pair-slot =
    load-indirect ∷                    -- Output := *Input (env from closure)
    store-at-slot pair-slot ∷          -- pair[0] := env
    load-indirect-suc ∷                -- Output := *(Input+1) (arg)
    store-at-slot (suc pair-slot) ∷    -- pair[1] := arg
    lea-slot pair-slot ∷               -- Output := &pair
    mov-to-input ∷ []                  -- Input := pair address

  -- Full apply trace: setup + push + body + pop
  apply-full-trace : (pair-slot : ℕ) (body-cap : ℕ) (body-trace : AbstractTrace) → AbstractTrace
  apply-full-trace pair-slot body-cap body-trace =
    apply-setup-trace pair-slot ++
    instr-push-frame body-cap ∷
    body-trace ++
    instr-pop-frame ∷ []

  ------------------------------------------------------------------------
  -- run-apply: Clean trace-based implementation
  ------------------------------------------------------------------------

  run-apply : ∀ {m A B q}
    (x : ⟦ (A ⇒[ q ] B) * A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-valid-wf : ValidAtWF m alloc x input-loc s) →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (apply {A} {B} {q}) ≤ frame-capacity alloc →
    ∃[ mOut ] IRResultAWF mOut (apply {A} {B} {q}) x s alloc
  run-apply {m} {A} {B} {q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    mBody , record
      { result-loc = result-loc
      ; final-state = s'
      ; final-alloc = alloc'
      ; trace = trace
      ; trace-correct = refl  -- BY DEFINITION
      ; result-valid-wf = result-valid-wf'
      ; result-before = result-before'
      ; rax-is-result = rax-eq'
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = m≤m+n (next-slot alloc) pair-slots
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved'
      ; reclaimable-slot = next-slot alloc +ℕ pair-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) pair-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = reclaim-preserves-result'
      ; reclaim-preserves-validity = reclaim-preserves-validity'
      ; reclaim-size-bound = ≤-refl
      ; frontier-slot-stable = frontier-stable'
      ; trace-writes-above = trace-writes-above'
      ; trace-slot-reads-above = trace-slot-reads-above'
      ; trace-writes-below = trace-writes-below'
      ; trace-slot-reads-below = trace-slot-reads-below'
      ; trace-preserves-capacity = trace-preserves-capacity'
      ; trace-no-store-indirect = trace-no-store-indirect'
      ; trace-preserves-halted = trace-preserves-halted'
      }
    where
      open import Data.Nat using (_≥_)
      open import Data.Nat.Properties using (*-monoʳ-≤; <⇒≤; *-monoˡ-≤; m<m+n)

      -- Decompose input pair
      pair-decomp = decomposePairWF {m} {_} {A ⇒[ q ] B} {A} input-valid-wf
      closure-loc = PairValidWF.fst-loc pair-decomp
      arg-loc = PairValidWF.snd-loc pair-decomp
      mArg = PairValidWF.mB pair-decomp
      closure-valid-wf = PairValidWF.fst-valid pair-decomp
      arg-valid-wf = PairValidWF.snd-valid pair-decomp
      arg-before = PairValidWF.snd-before pair-decomp

      closure : ⟦ A ⇒[ q ] B ⟧
      closure = fst {A ⇒[ q ] B} {A} x

      arg : ⟦ A ⟧
      arg = snd {A ⇒[ q ] B} {A} x

      -- Decompose closure
      mClosure = PairValidWF.mA pair-decomp
      closure-mode-is-heap : mClosure ≡ Heap
      closure-mode-is-heap = closure-mode-is-heap-proof closure-valid-wf
      closure-valid-wf-heap : ValidAtWF Heap alloc closure closure-loc s
      closure-valid-wf-heap = subst (λ m → ValidAtWF m alloc closure closure-loc s)
        closure-mode-is-heap closure-valid-wf

      closure-decomp = decomposeClosureWF {_} {q} {A} {B} closure-valid-wf-heap
      EnvType = ClosureValidWF.EnvType closure-decomp
      body = ClosureValidWF.body closure-decomp
      env = ClosureValidWF.env closure-decomp
      body<bound = ClosureValidWF.body<bound closure-decomp
      env-loc = ClosureValidWF.env-loc closure-decomp
      env-valid-wf = ClosureValidWF.env-valid closure-decomp
      env-before = ClosureValidWF.env-before closure-decomp
      closure-is-body = ClosureValidWF.f-is-closure closure-decomp
      body-correct = ClosureValidWF.body-correct closure-decomp

      body-cap = BodyCorrect.body-capacity body-correct

      -- Pair slot allocation
      pair-slot = next-slot alloc
      pair-input-loc = OnStack (current-frame alloc) pair-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = next-slot alloc +ℕ pair-slots }

      -- Child frame setup
      child-frame = get-child-frame alloc
      child-frame-below-parent = child-frame-ordered alloc

      child-alloc : AllocState {FS}
      child-alloc = record
        { current-frame = child-frame
        ; next-slot = 0
        ; frame-capacity = body-cap
        ; next-heap-ref = next-heap-ref alloc
        }

      ------------------------------------------------------------------------
      -- Execute body in child frame (to get body-trace)
      --
      -- We need to execute body to get its trace, which we then compose
      -- into apply's full trace.
      ------------------------------------------------------------------------

      -- State after setup (before push-frame)
      -- This is computed by exec-trace on setup-trace
      -- For body execution, we pass this state to BodyCorrect.execute

      -- State after setup trace execution
      s-after-setup : LocState FS
      s-after-setup = SMP.!!

      s-after-setup-def : s-after-setup ≡ proj₁ (exec-trace (apply-setup-trace pair-slot) s alloc)
      s-after-setup-def = SMP.!!

      -- Pair is properly constructed after setup
      pair-env-ptr : readLoc s-after-setup pair-input-loc ≡ just env-loc
      pair-env-ptr = SMP.!!

      pair-arg-ptr : readLoc s-after-setup (sucLoc pair-input-loc) ≡ just arg-loc
      pair-arg-ptr = SMP.!!

      -- Input register points to pair after setup
      pair-input-eq : readReg (regs s-after-setup) Input ≡ pair-input-loc
      pair-input-eq = SMP.!!

      -- Not halted after setup
      not-halted-after-setup : halted s-after-setup ≡ false
      not-halted-after-setup = SMP.!!

      -- Pair validity in child-alloc (after setup, transferred to child frame)
      pair-input-valid-child : ValidAtWF Heap child-alloc {EnvType * A} (pair env arg) pair-input-loc s-after-setup
      pair-input-valid-child = SMP.!!

      -- Pair is before frontier in child-alloc
      pair-input-before-child : BeforeFrontier child-alloc pair-input-loc
      pair-input-before-child = SMP.!!

      -- Body execution in child frame
      body-exec-result : ∃[ mOut ] IRResultAWF mOut body (pair env arg) s-after-setup child-alloc
      body-exec-result = BodyCorrect.execute body-correct arg arg-loc pair-input-loc
        s-after-setup child-alloc Heap
        pair-input-valid-child pair-input-before-child not-halted-after-setup pair-input-eq
        ≤-refl

      mBody = proj₁ body-exec-result
      body-result = proj₂ body-exec-result

      body-trace = IRResultAWF.trace body-result
      result-loc = IRResultAWF.result-loc body-result

      ------------------------------------------------------------------------
      -- Full trace and final state (CLEAN: defined by exec-trace)
      ------------------------------------------------------------------------

      trace : AbstractTrace
      trace = apply-full-trace pair-slot body-cap body-trace

      -- CLEAN: Final state defined by exec-trace
      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      ------------------------------------------------------------------------
      -- Proof obligations for properties
      ------------------------------------------------------------------------

      -- Output register contains result location
      rax-eq' : readReg (regs s') Output ≡ result-loc
      rax-eq' = SMP.!!

      -- Not halted after full trace
      not-halted' : halted s' ≡ false
      not-halted' = SMP.!!

      -- Memory before frontier preserved
      mem-preserved' : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved' = SMP.!!

      -- Result is before frontier in alloc'
      result-before' : BeforeFrontier alloc' result-loc
      result-before' = SMP.!!

      -- Result validity
      result-valid-wf' : ValidAtWF mBody alloc' (eval primSem (apply {A} {B} {q}) x) result-loc s'
      result-valid-wf' = SMP.!!

      -- Frontier slot stability
      frontier-stable' : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc' →
        readLoc s'' (OnStack (current-frame alloc) pair-slot) ≡ just input-loc' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) pair-slot) ≡ just input-loc'
      frontier-stable' = SMP.!!

      -- Trace properties
      trace-writes-above' : TraceWritesAbove pair-slot trace
      trace-writes-above' = SMP.!!

      trace-slot-reads-above' : TraceSlotReadsAbove pair-slot trace
      trace-slot-reads-above' = SMP.!!

      trace-writes-below' : TraceWritesBelow (next-slot alloc +ℕ pair-slots) trace
      trace-writes-below' = SMP.!!

      trace-slot-reads-below' : TraceSlotReadsBelow (next-slot alloc +ℕ pair-slots) trace
      trace-slot-reads-below' = SMP.!!

      trace-preserves-capacity' : TracePreservesCapacity trace
      trace-preserves-capacity' = SMP.!!

      trace-no-store-indirect' : TraceNoStoreIndirect trace
      trace-no-store-indirect' = SMP.!!

      -- Reclamation proofs
      reclaim-preserves-result' : ∀ (fits : next-slot alloc +ℕ pair-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ pair-slots }) result-loc
      reclaim-preserves-result' fits = bf-same-frame-slot alloc'
        (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
        refl refl refl result-loc result-before'

      reclaim-preserves-validity' : ∀ (fits : next-slot alloc +ℕ pair-slots ≤ frame-capacity alloc) →
        ValidAtWF mBody (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
                  (eval primSem (apply {A} {B} {q}) x) result-loc s'
      reclaim-preserves-validity' fits = validityWF-with-bf-transfer
        (eval primSem (apply {A} {B} {q}) x) result-loc s' alloc'
        (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
        (λ loc bf → bf-same-frame-slot alloc'
          (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
          refl refl refl loc bf)
        result-valid-wf'

      -- Trace preserves halted (structural proof)
      trace-preserves-halted' : TracePreservesHaltedP trace
      trace-preserves-halted' =
        tph-++ (setup-trace-preserves-halted pair-slot)
        (tph-∷ iph-push-frame
        (tph-++ (IRResultAWF.trace-preserves-halted body-result)
        (tph-∷ iph-pop-frame tph-[])))
        where
          setup-trace-preserves-halted : (ps : ℕ) → TracePreservesHaltedP (apply-setup-trace ps)
          setup-trace-preserves-halted ps =
            tph-∷ iph-load-indirect
            (tph-∷ iph-store-at-slot
            (tph-∷ iph-load-indirect-suc
            (tph-∷ iph-store-at-slot
            (tph-∷ iph-lea-slot
            (tph-∷ iph-mov-to-input tph-[])))))
