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
open import Data.Sum using (inj₁; inj₂)
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

-- Import proof obligation marker
import Once.ProofObligation as PO

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

  -- Open SMPrimitives modules for trace lemmas
  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; BodyCorrect;
           valid-closure-wf; validityWF-mem-only;
           validityWF-alloc-advance; validityWF-frontier-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-with-bf-transfer; validityWF-trace-preserves)

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
      -- Trace properties (defined first for use in proofs)
      ----------------------------------------------------------------------

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

      ----------------------------------------------------------------------
      -- Proof obligations for exec-trace properties
      ----------------------------------------------------------------------

      -- Halted status preserved (use exec-trace-preserves-halted)
      not-halted' : halted s' ≡ false
      not-halted' = exec-trace-preserves-halted trace s alloc not-halted trace-preserves-halted'

      -- Output register contains closure address
      -- The trace ends with lea-slot closure-slot, so Output = OnStack frame closure-slot
      -- Proof: split trace = prefix ++ [lea-slot closure-slot], use exec-trace-final-lea-slot
      prefix-trace : AbstractTrace
      prefix-trace = mov-to-output ∷ store-at-slot closure-slot ∷
                     lea-slot (suc closure-slot) ∷ store-at-slot (suc closure-slot) ∷ []

      prefix-tph : TracePreservesHaltedP prefix-trace
      prefix-tph = tph-∷ iph-mov-to-output
                   (tph-∷ iph-store-at-slot
                   (tph-∷ iph-lea-slot
                   (tph-∷ iph-store-at-slot tph-[])))

      not-halted-after-prefix : halted (proj₁ (exec-trace prefix-trace s alloc)) ≡ false
      not-halted-after-prefix = exec-trace-preserves-halted prefix-trace s alloc not-halted prefix-tph

      rax-eq' : readReg (regs s') Output ≡ closure-loc
      rax-eq' = exec-trace-final-lea-slot prefix-trace closure-slot s alloc not-halted-after-prefix

      -- Closure slot env-ptr': store-at-slot writes Input to closure-slot, preserved by rest
      -- Using prefix-store-preserve with:
      --   prefix = [mov-to-output]
      --   k = closure-slot
      --   suffix = [lea-slot (suc closure-slot), store-at-slot (suc closure-slot), lea-slot closure-slot]
      env-prefix : AbstractTrace
      env-prefix = mov-to-output ∷ []

      env-suffix : AbstractTrace
      env-suffix = lea-slot (suc closure-slot) ∷ store-at-slot (suc closure-slot) ∷
                   lea-slot closure-slot ∷ []

      env-prefix-tph : TracePreservesHaltedP env-prefix
      env-prefix-tph = tph-∷ iph-mov-to-output tph-[]

      -- env-suffix = lea-slot (suc cs) ∷ store-at-slot (suc cs) ∷ lea-slot cs ∷ []
      -- lea-slot doesn't write (nothing), store-at-slot (suc cs) writes to (suc cs)
      -- Need: suc cs ≤ suc cs for the store, rest is tt
      env-suffix-twa : TraceWritesAbove (suc closure-slot) env-suffix
      env-suffix-twa = ≤-refl , tt

      -- After mov-to-output: Output = Input = input-loc
      -- Use exec-abstract directly for definitional computation, then connect via exec-trace-single
      s-after-mov : LocState FS
      s-after-mov = proj₁ (exec-abstract mov-to-output s alloc)

      -- Output = Input after mov-to-output (definitional from exec-abstract)
      output-after-mov : readReg (regs s-after-mov) Output ≡ input-loc
      output-after-mov = trans (writeReg-same (regs s) Output (readReg (regs s) Input)) rdi-eq

      -- Connect exec-trace to exec-abstract
      exec-trace-env-prefix : exec-trace env-prefix s alloc ≡ exec-abstract mov-to-output s alloc
      exec-trace-env-prefix = exec-trace-single mov-to-output s alloc not-halted

      s-after-env-prefix : LocState FS
      s-after-env-prefix = proj₁ (exec-trace env-prefix s alloc)

      s-after-env-prefix-eq : s-after-env-prefix ≡ s-after-mov
      s-after-env-prefix-eq = cong proj₁ exec-trace-env-prefix

      output-after-env-prefix : readReg (regs s-after-env-prefix) Output ≡ input-loc
      output-after-env-prefix = subst (λ s'' → readReg (regs s'') Output ≡ input-loc)
                                      (sym s-after-env-prefix-eq) output-after-mov

      env-ptr' : readLoc s' closure-loc ≡ just input-loc
      env-ptr' = trans (prefix-store-preserve env-prefix closure-slot env-suffix s alloc
                          env-prefix-tph not-halted env-suffix-twa tt)
                       (cong just output-after-env-prefix)

      -- Code slot code-ptr': lea-slot sets Output=code-loc, store-at-slot stores it
      -- Using prefix-store-preserve with:
      --   prefix = [mov-to-output, store-at-slot closure-slot, lea-slot (suc closure-slot)]
      --   k = suc closure-slot
      --   suffix = [lea-slot closure-slot]
      code-prefix : AbstractTrace
      code-prefix = mov-to-output ∷ store-at-slot closure-slot ∷ lea-slot (suc closure-slot) ∷ []

      code-suffix : AbstractTrace
      code-suffix = lea-slot closure-slot ∷ []

      code-prefix-tph : TracePreservesHaltedP code-prefix
      code-prefix-tph = tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot (tph-∷ iph-lea-slot tph-[]))

      -- suc (suc closure-slot) > suc closure-slot, and lea-slot doesn't write
      code-suffix-twa : TraceWritesAbove (suc (suc closure-slot)) code-suffix
      code-suffix-twa = tt

      -- After code-prefix: Output = OnStack frame (suc closure-slot) = code-loc
      s-after-code-prefix : LocState FS
      s-after-code-prefix = proj₁ (exec-trace code-prefix s alloc)

      code-prefix-not-halted : halted s-after-code-prefix ≡ false
      code-prefix-not-halted = exec-trace-preserves-halted code-prefix s alloc not-halted code-prefix-tph

      -- lea-slot (suc closure-slot) puts OnStack frame (suc closure-slot) in Output
      -- Use exec-trace-final-lea-slot: code-prefix = prefix ++ [lea-slot k]
      -- where prefix = mov-to-output ∷ store-at-slot closure-slot ∷ []
      code-prefix-before-lea : AbstractTrace
      code-prefix-before-lea = mov-to-output ∷ store-at-slot closure-slot ∷ []

      code-prefix-before-lea-tph : TracePreservesHaltedP code-prefix-before-lea
      code-prefix-before-lea-tph = tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot tph-[])

      not-halted-before-lea : halted (proj₁ (exec-trace code-prefix-before-lea s alloc)) ≡ false
      not-halted-before-lea = exec-trace-preserves-halted code-prefix-before-lea s alloc not-halted
                                code-prefix-before-lea-tph

      output-after-code-prefix : readReg (regs s-after-code-prefix) Output ≡ code-loc
      output-after-code-prefix = exec-trace-final-lea-slot code-prefix-before-lea (suc closure-slot)
                                   s alloc not-halted-before-lea

      code-ptr' : readLoc s' code-loc ≡ just code-loc
      code-ptr' = trans (prefix-store-preserve code-prefix (suc closure-slot) code-suffix s alloc
                           code-prefix-tph not-halted code-suffix-twa tt)
                        (cong just output-after-code-prefix)

      -- Memory before frontier is preserved
      -- Trace writes above closure-slot, so slots below are preserved
      mem-preserved' : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved' (OnStack f' k) (stack-before {.f'} {.k} frame-eq k<next) =
        -- k < next-slot alloc = closure-slot, so slot k is below write region
        subst (λ f → readLoc s' (OnStack f k) ≡ readLoc s (OnStack f k))
              (sym frame-eq)
              (exec-trace-preserves-slot-below trace s alloc closure-slot k
                 trace-writes-above' tt k<next)
      mem-preserved' (OnStack f' k) (stack-ancestor {.f'} cf≺f' _) =
        -- f' is an ancestor frame (current-frame alloc ≺ f')
        exec-trace-preserves-ancestor trace s alloc f' k cf≺f' tt
      mem-preserved' (OnHeap h) (heap-before _) =
        -- Heap location, use preserves-heap-loc
        exec-trace-preserves-heap-loc trace s alloc h tt

      -- Frontier slot stability
      -- The trace writes to closure-slot, but writes the SAME value (input-loc'):
      --   1. mov-to-output: Output = Input = input-loc'
      --   2. store-at-slot closure-slot: slot = Output = input-loc'
      --   3. Rest of trace writes only to higher slots
      frontier-stable' : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc' →
        readLoc s'' (OnStack (current-frame alloc) closure-slot) ≡ just input-loc' →
        _
      frontier-stable' s'' input-loc' not-halted'' rdi-eq'' _ =
        let -- Use same decomposition as env-ptr': prefix = [mov-to-output], suffix = rest
            -- After mov-to-output in s'': Output = Input = input-loc'
            s''-after-mov = proj₁ (exec-abstract mov-to-output s'' alloc)

            output-after-mov'' : readReg (regs s''-after-mov) Output ≡ input-loc'
            output-after-mov'' = trans (writeReg-same (regs s'') Output (readReg (regs s'') Input)) rdi-eq''

            -- Connect exec-trace to exec-abstract
            exec-trace-env-prefix'' : exec-trace env-prefix s'' alloc ≡ exec-abstract mov-to-output s'' alloc
            exec-trace-env-prefix'' = exec-trace-single mov-to-output s'' alloc not-halted''

            s''-after-env-prefix = proj₁ (exec-trace env-prefix s'' alloc)

            s''-after-env-prefix-eq : s''-after-env-prefix ≡ s''-after-mov
            s''-after-env-prefix-eq = cong proj₁ exec-trace-env-prefix''

            output-after-env-prefix'' : readReg (regs s''-after-env-prefix) Output ≡ input-loc'
            output-after-env-prefix'' = subst (λ st → readReg (regs st) Output ≡ input-loc')
                                              (sym s''-after-env-prefix-eq) output-after-mov''

            -- Apply prefix-store-preserve
            result : readLoc (proj₁ (exec-trace trace s'' alloc))
                             (OnStack (current-frame alloc) closure-slot) ≡
                     just (readReg (regs s''-after-env-prefix) Output)
            result = prefix-store-preserve env-prefix closure-slot env-suffix s'' alloc
                       env-prefix-tph not-halted'' env-suffix-twa tt

        in inj₂ (inj₁ (trans result (cong just output-after-env-prefix'')))

      -- Input validity in final state
      -- Transfer validity across memory-preserving trace execution
      -- Step 1: Use validityWF-trace-preserves to preserve through trace execution
      -- Step 2: Use validityWF-frontier-advance to convert alloc → alloc'
      input-valid-at-s' : ValidAtWF mIn alloc x input-loc s'
      input-valid-at-s' = validityWF-trace-preserves alloc trace x input-loc s
                            input-before input-valid-wf trace-writes-above' tt

      input-valid-wf' : ValidAtWF mIn alloc' x input-loc s'
      input-valid-wf' = validityWF-frontier-advance x input-loc s'
                          refl (m≤m+n (next-slot alloc) closure-slots) ≤-refl
                          input-valid-at-s'

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

