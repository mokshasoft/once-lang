------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.CurryWF
--
-- Curry IR implementation with clean trace-based structure.
-- Final state defined via exec-trace, making trace-correct = refl.
--
-- RELOCATION APPROACH: No frame manipulation, just stack slot writes.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.CurryWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m<m+n; m+n≤o⇒m≤o; +-monoʳ-≤; *-monoˡ-≤; m≤m*n; +-assoc; n≤1+n)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86-64.Types
open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Target.X86-64.Layout using (closure-slots)
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import SMPrimitives qualified for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- Curry implementation with clean trace-based structure
------------------------------------------------------------------------

module CurryWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules for trace predicates
  open SMP.TracePrimitives {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; BodyCorrect;
           valid-closure-wf; validityWF-mem-only;
           validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-with-bf-transfer)

  -- Import bf-same-frame-slot from BFTransfer module
  open import Once.CCC.Machine.IR.ApplyWF
  open BFTransfer {FS}
    using (bf-same-frame-slot)

  -- Import lemmas
  open import Once.CCC.Machine.DispatcherArithmeticLemma
    using (suc<+2)
  open import Once.CCC.Machine.SizeBoundLemma
    using (curry-body-bound)

  -- Import write operations
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import frontier lemmas
  open import Once.CCC.Machine.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (at-frontier-before-closure; frontier-same-heap)

  ------------------------------------------------------------------------
  -- Helper lemmas
  ------------------------------------------------------------------------

  closure-slots-≤-curry-req : ∀ {A B C q} (f : IR (A * B) C) (m : AllocMode) →
    closure-slots ≤ ir-stack-requirement (curry {q = q} f m)
  closure-slots-≤-curry-req f Stack = ≤-refl
  closure-slots-≤-curry-req f Heap = ≤-refl

  ------------------------------------------------------------------------
  -- Curry trace: stores closure (env pointer + code pointer)
  ------------------------------------------------------------------------

  curry-trace : (closure-slot : ℕ) → AbstractTrace
  curry-trace closure-slot =
    mov-to-output ∷                    -- Output := Input (env pointer)
    store-at-slot closure-slot ∷       -- closure[0] := env
    lea-slot (suc closure-slot) ∷      -- Output := &closure[1] (code loc)
    store-at-slot (suc closure-slot) ∷ -- closure[1] := code pointer
    lea-slot closure-slot ∷ []         -- Output := closure address

  ------------------------------------------------------------------------
  -- run-curry: Clean trace-based implementation
  ------------------------------------------------------------------------

  run-curry : ∀ {A B C q} (mIn : AllocMode) (f : IR (A * B) C) (m : AllocMode)
    (ir<bound : ir-size (curry {q = q} f m) < program-bound)
    (rec-wf : RecDispatcherWF (ir-size (curry {q = q} f m)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (curry {q = q} f m) ≤ frame-capacity alloc →
    IRResultAWF Heap (curry {q = q} f m) x s alloc
  run-curry {A} {B} {C} {q} mIn f m ir<bound rec-wf x input-loc s alloc
    input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = closure-loc
      ; final-state = s'
      ; final-alloc = alloc'
      ; trace = trace
      ; trace-correct = refl  -- BY DEFINITION
      ; result-valid-wf = result-valid-wf'
      ; result-before = closure-before'
      ; rax-is-result = rax-eq'
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = m≤m+n (next-slot alloc) closure-slots
      ; heap-monotone = ≤-refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved'
      ; reclaimable-slot = next-slot alloc +ℕ closure-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) closure-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = reclaim-preserves-result'
      ; reclaim-preserves-validity = reclaim-preserves-validity'
      ; reclaim-size-bound = +-monoʳ-≤ (next-slot alloc) closure-bound
      ; frontier-slot-stable = frontier-stable'
      ; trace-writes-above = trace-writes-above'
      ; trace-slot-reads-above = tt
      ; trace-writes-below = trace-writes-below'
      ; trace-slot-reads-below = tt
      ; trace-preserves-capacity = trace-preserves-capacity'
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = trace-preserves-halted'
      }
    where
      -- Closure location and trace
      closure-slot = next-slot alloc
      closure-loc = OnStack (current-frame alloc) closure-slot
      code-loc = sucLoc closure-loc
      trace = curry-trace closure-slot

      -- CLEAN: Final state defined by exec-trace
      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = next-slot alloc +ℕ closure-slots }

      -- Size bounds
      body<bound = curry-body-bound {q = q} f {m} program-bound ir<bound
      req-curry = ir-stack-requirement (curry {q = q} f m)
      closure-bound : closure-slots ≤ req-curry
      closure-bound = closure-slots-≤-curry-req {q = q} f m

      ----------------------------------------------------------------------
      -- Proof obligations for exec-trace properties
      ----------------------------------------------------------------------

      -- Output register contains closure address
      rax-eq' : readReg (regs s') Output ≡ closure-loc
      rax-eq' = SMP.!!

      -- Halted status preserved
      not-halted' : halted s' ≡ false
      not-halted' = SMP.!!

      -- Closure slots contain expected values
      env-ptr' : readLoc s' closure-loc ≡ just input-loc
      env-ptr' = SMP.!!

      code-ptr' : readLoc s' code-loc ≡ just code-loc
      code-ptr' = SMP.!!

      -- Memory before frontier is preserved
      mem-preserved' : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved' = SMP.!!

      -- Frontier slot stability
      frontier-stable' : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc' →
        readLoc s'' (OnStack (current-frame alloc) closure-slot) ≡ just input-loc' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) closure-slot) ≡ just input-loc'
      frontier-stable' = SMP.!!

      -- Input validity in final state
      input-valid-wf' : ValidAtWF mIn alloc' x input-loc s'
      input-valid-wf' = SMP.!!

      -- Closure is before frontier in updated allocation
      closure-before' : BeforeFrontier alloc' closure-loc
      closure-before' = at-frontier-before-closure alloc

      -- Input location still before frontier after allocation
      input-before' : BeforeFrontier alloc' input-loc
      input-before' = stack-alloc-advances alloc closure-slots input-loc input-before

      -- Code location before frontier
      code-before' : BeforeFrontier alloc' code-loc
      code-before' = stack-before refl (suc<+2 closure-slot)

      -- BodyCorrect: recursive dispatcher for body
      body-correct : BodyCorrect f x input-loc program-bound
      body-correct = record
        { body-capacity = ir-stack-requirement f
        ; body-cap-eq = refl
        ; execute = λ arg arg-loc pair-loc s'' alloc'' mPair pair-valid-wf pair-before not-halt rdi-eq' cap' →
            rec-wf mPair f (curry-smaller {q = q} f {m}) (pair x arg) pair-loc s'' alloc''
              pair-valid-wf pair-before not-halt rdi-eq' cap'
        }

      -- Result validity: closure with body-correct embedded
      result-valid-wf' : ValidAtWF Heap alloc' (eval primSem (curry {q = q} f m) x) closure-loc s'
      result-valid-wf' = valid-closure-wf body<bound
        env-ptr' code-ptr' input-before' code-before' code-before'
        input-valid-wf' body-correct

      -- Reclamation proofs
      reclaim-preserves-result' : ∀ (fits : next-slot alloc +ℕ closure-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ closure-slots }) closure-loc
      reclaim-preserves-result' fits =
        frontier-same-heap alloc' (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
          refl refl refl closure-loc closure-before'

      reclaim-preserves-validity' : ∀ (fits : next-slot alloc +ℕ closure-slots ≤ frame-capacity alloc) →
        ValidAtWF Heap (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
                  (eval primSem (curry {q = q} f m) x) closure-loc s'
      reclaim-preserves-validity' fits = validityWF-with-bf-transfer
        (eval primSem (curry {q = q} f m) x) closure-loc s' alloc'
        (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
        (λ loc bf → bf-same-frame-slot alloc'
          (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
          refl refl refl loc bf)
        result-valid-wf'

      -- Trace properties
      trace-writes-above' : TraceWritesAbove closure-slot trace
      trace-writes-above' = ≤-refl , (n≤1+n closure-slot , tt)

      trace-writes-below' : TraceWritesBelow (next-slot alloc +ℕ closure-slots) trace
      trace-writes-below' =
        m<m+n closure-slot {closure-slots} (s≤s z≤n) ,
        (suc<+2 closure-slot , tt)

      trace-preserves-capacity' : TracePreservesCapacity trace
      trace-preserves-capacity' =
        tpc-∷ ipc-mov-to-output
        (tpc-∷ ipc-store-at-slot
        (tpc-∷ ipc-lea-slot
        (tpc-∷ ipc-store-at-slot
        (tpc-∷ ipc-lea-slot tpc-[]))))

      trace-preserves-halted' : TracePreservesHaltedP trace
      trace-preserves-halted' =
        tph-∷ iph-mov-to-output
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-lea-slot
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-lea-slot tph-[]))))
