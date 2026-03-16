------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.SimpleWF
--
-- Simple IR cases using the clean trace-based structure.
-- Final states defined by exec-trace, making trace-correct = refl.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.SimpleWF where

open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)

-- Import SMPrimitives for memory reasoning
import Once.CCC.SMPrimitives as SMP

------------------------------------------------------------------------
-- Simple IR implementations
------------------------------------------------------------------------

module SimpleWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules
  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; valid-unit-wf; valid-eff-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           decomposePairWF; PairValidWF)

  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap)

  ------------------------------------------------------------------------
  -- Identity: output is same as input
  ------------------------------------------------------------------------

  run-id : ∀ {m A}
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    IRResultAWF m (id {A}) x s alloc
  run-id x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = valid-s'
      ; result-before = input-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → input-before
      ; reclaim-preserves-validity = λ _ → valid-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      -- State equivalence via exec-trace-single
      s'-eq : s' ≡ exec (mov Output Input) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted

      valid-s' = subst (λ st → ValidAtWF _ alloc x input-loc st) (sym s'-eq)
                   (validityWF-mem-only x input-loc s (exec (mov Output Input) s) refl refl input-valid-wf)

      rax-eq : readReg (regs s') Output ≡ input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input s) rdi-eq)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (mov Output Input) s) s loc
                                 (mov-preserves-stackMem Output Input s)
                                 (mov-preserves-heapMem Output Input s))

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc'' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc''
      frontier-stable s'' _ not-halted'' _ slot-eq =
        let s''-final = proj₁ (exec-trace trace s'' alloc)
            s''-final-eq : s''-final ≡ exec (mov Output Input) s''
            s''-final-eq = cong proj₁ (exec-trace-single mov-to-output s'' alloc not-halted'')
        in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc))) s''-final-eq)
                 (trans (readLoc-stackMem-eq (exec (mov Output Input) s'') s''
                          (OnStack (current-frame alloc) (next-slot alloc))
                          (mov-preserves-stackMem Output Input s'')
                          (mov-preserves-heapMem Output Input s''))
                        slot-eq)

  ------------------------------------------------------------------------
  -- Fst: extract first component from pair
  ------------------------------------------------------------------------

  run-fst : ∀ {m A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    ∃[ mA ] IRResultAWF mA (fst-ir {A} {B}) x s alloc
  run-fst {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mA , record
      { result-loc = fst-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = fst-valid-s'
      ; result-before = fst-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → fst-before
      ; reclaim-preserves-validity = λ _ → fst-valid-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-preserves-capacity = tpc-∷ ipc-load-indirect tpc-[]
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-load-indirect tph-[]
      }
    where
      pair-decomp = decomposePairWF {m} input-valid-wf
      mA = PairValidWF.mA pair-decomp
      fst-loc = PairValidWF.fst-loc pair-decomp
      fst-valid-wf = PairValidWF.fst-valid pair-decomp
      fst-before = PairValidWF.fst-before pair-decomp

      mem-read : readLoc s (resolveSourceExt (regs s) (IndReg Input)) ≡ just fst-loc
      mem-read = subst (λ loc → readLoc s loc ≡ just fst-loc)
                       (sym rdi-eq) (PairValidWF.fst-ptr pair-decomp)

      trace : AbstractTrace
      trace = load-indirect ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (load Output (IndReg Input)) s
      s'-eq = cong proj₁ (exec-trace-single load-indirect s alloc not-halted)

      fst-valid-s' : ValidAtWF mA alloc (proj₁ x) fst-loc s'
      fst-valid-s' = subst (λ st → ValidAtWF mA alloc (proj₁ x) fst-loc st) (sym s'-eq)
                       (validityWF-mem-only (proj₁ x) fst-loc s (exec (load Output (IndReg Input)) s)
                          (load-preserves-stackMem Output (IndReg Input) s)
                          (load-preserves-heapMem Output (IndReg Input) s)
                          fst-valid-wf)

      rax-eq : readReg (regs s') Output ≡ fst-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (load-result Output (IndReg Input) s fst-loc mem-read)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq)
                      (load-no-halt Output (IndReg Input) s fst-loc mem-read not-halted)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (load Output (IndReg Input)) s) s loc
                                 (load-preserves-stackMem Output (IndReg Input) s)
                                 (load-preserves-heapMem Output (IndReg Input) s))

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc'' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc''
      frontier-stable s'' _ not-halted'' _ slot-eq =
        let s''-final = proj₁ (exec-trace trace s'' alloc)
            s''-final-eq : s''-final ≡ exec (load Output (IndReg Input)) s''
            s''-final-eq = cong proj₁ (exec-trace-single load-indirect s'' alloc not-halted'')
        in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc))) s''-final-eq)
                 (trans (readLoc-stackMem-eq (exec (load Output (IndReg Input)) s'') s''
                          (OnStack (current-frame alloc) (next-slot alloc))
                          (load-preserves-stackMem Output (IndReg Input) s'')
                          (load-preserves-heapMem Output (IndReg Input) s''))
                        slot-eq)

  ------------------------------------------------------------------------
  -- Snd: extract second component from pair
  ------------------------------------------------------------------------

  run-snd : ∀ {m A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    ∃[ mB ] IRResultAWF mB (snd-ir {A} {B}) x s alloc
  run-snd {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mB , record
      { result-loc = snd-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = snd-valid-s'
      ; result-before = snd-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → snd-before
      ; reclaim-preserves-validity = λ _ → snd-valid-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-preserves-capacity = tpc-∷ ipc-load-indirect-suc tpc-[]
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-load-indirect-suc tph-[]
      }
    where
      pair-decomp = decomposePairWF {m} input-valid-wf
      mB = PairValidWF.mB pair-decomp
      snd-loc = PairValidWF.snd-loc pair-decomp
      snd-valid-wf = PairValidWF.snd-valid pair-decomp
      snd-before = PairValidWF.snd-before pair-decomp

      mem-read : readLoc s (resolveSourceExt (regs s) (IndRegSuc Input)) ≡ just snd-loc
      mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just snd-loc)
                       (sym rdi-eq) (PairValidWF.snd-ptr pair-decomp)

      trace : AbstractTrace
      trace = load-indirect-suc ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (load Output (IndRegSuc Input)) s
      s'-eq = cong proj₁ (exec-trace-single load-indirect-suc s alloc not-halted)

      snd-valid-s' : ValidAtWF mB alloc (proj₂ x) snd-loc s'
      snd-valid-s' = subst (λ st → ValidAtWF mB alloc (proj₂ x) snd-loc st) (sym s'-eq)
                       (validityWF-mem-only (proj₂ x) snd-loc s (exec (load Output (IndRegSuc Input)) s)
                          (load-preserves-stackMem Output (IndRegSuc Input) s)
                          (load-preserves-heapMem Output (IndRegSuc Input) s)
                          snd-valid-wf)

      rax-eq : readReg (regs s') Output ≡ snd-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (load-result Output (IndRegSuc Input) s snd-loc mem-read)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq)
                      (load-no-halt Output (IndRegSuc Input) s snd-loc mem-read not-halted)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (load Output (IndRegSuc Input)) s) s loc
                                 (load-preserves-stackMem Output (IndRegSuc Input) s)
                                 (load-preserves-heapMem Output (IndRegSuc Input) s))

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc'' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc''
      frontier-stable s'' _ not-halted'' _ slot-eq =
        let s''-final = proj₁ (exec-trace trace s'' alloc)
            s''-final-eq : s''-final ≡ exec (load Output (IndRegSuc Input)) s''
            s''-final-eq = cong proj₁ (exec-trace-single load-indirect-suc s'' alloc not-halted'')
        in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc))) s''-final-eq)
                 (trans (readLoc-stackMem-eq (exec (load Output (IndRegSuc Input)) s'') s''
                          (OnStack (current-frame alloc) (next-slot alloc))
                          (load-preserves-stackMem Output (IndRegSuc Input) s'')
                          (load-preserves-heapMem Output (IndRegSuc Input) s''))
                        slot-eq)

  ------------------------------------------------------------------------
  -- Terminal: output unit
  ------------------------------------------------------------------------

  run-terminal : ∀ {m A}
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    IRResultAWF m (terminal {A}) x s alloc
  run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = valid-unit-wf
      ; result-before = input-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → input-before
      ; reclaim-preserves-validity = λ _ → valid-unit-wf
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted

      rax-eq : readReg (regs s') Output ≡ input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input s) rdi-eq)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (mov Output Input) s) s loc
                                 (mov-preserves-stackMem Output Input s)
                                 (mov-preserves-heapMem Output Input s))

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc'' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc''
      frontier-stable s'' _ not-halted'' _ slot-eq =
        let s''-final = proj₁ (exec-trace trace s'' alloc)
            s''-final-eq : s''-final ≡ exec (mov Output Input) s''
            s''-final-eq = cong proj₁ (exec-trace-single mov-to-output s'' alloc not-halted'')
        in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc))) s''-final-eq)
                 (trans (readLoc-stackMem-eq (exec (mov Output Input) s'') s''
                          (OnStack (current-frame alloc) (next-slot alloc))
                          (mov-preserves-stackMem Output Input s'')
                          (mov-preserves-heapMem Output Input s''))
                        slot-eq)

  ------------------------------------------------------------------------
  -- Free-heap: explicit heap deallocation (semantically a no-op)
  ------------------------------------------------------------------------

  run-free-heap : ∀ {m} (ref : HeapRef)
    (x : ⟦ Unit ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    IRResultAWF m (free-heap ref) x s alloc
  run-free-heap ref x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = valid-s'
      ; result-before = input-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → input-before
      ; reclaim-preserves-validity = λ _ → valid-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted

      valid-s' = subst (λ st → ValidAtWF _ alloc x input-loc st) (sym s'-eq)
                   (validityWF-mem-only x input-loc s (exec (mov Output Input) s) refl refl input-valid-wf)

      rax-eq : readReg (regs s') Output ≡ input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input s) rdi-eq)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (mov Output Input) s) s loc
                                 (mov-preserves-stackMem Output Input s)
                                 (mov-preserves-heapMem Output Input s))

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc'' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc''
      frontier-stable s'' _ not-halted'' _ slot-eq =
        let s''-final = proj₁ (exec-trace trace s'' alloc)
            s''-final-eq : s''-final ≡ exec (mov Output Input) s''
            s''-final-eq = cong proj₁ (exec-trace-single mov-to-output s'' alloc not-halted'')
        in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc))) s''-final-eq)
                 (trans (readLoc-stackMem-eq (exec (mov Output Input) s'') s''
                          (OnStack (current-frame alloc) (next-slot alloc))
                          (mov-preserves-stackMem Output Input s'')
                          (mov-preserves-heapMem Output Input s''))
                        slot-eq)

  ------------------------------------------------------------------------
  -- Arr: effectful morphism coercion (A ⇒[ q ] B) to (Eff A B)
  ------------------------------------------------------------------------

  run-arr : ∀ {m A B q}
    (x : ⟦ A ⇒[ q ] B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    IRResultAWF m (arr {A} {B} {q}) x s alloc
  run-arr {m} {A} {B} {q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = valid-eff
      ; result-before = input-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → input-before
      ; reclaim-preserves-validity = λ _ → valid-eff
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted

      valid-s' = subst (λ st → ValidAtWF _ alloc x input-loc st) (sym s'-eq)
                   (validityWF-mem-only x input-loc s (exec (mov Output Input) s) refl refl input-valid-wf)

      valid-eff : ValidAtWF m alloc {Eff A B} x input-loc s'
      valid-eff = valid-eff-wf {m} {A} {B} {q} valid-s'

      rax-eq : readReg (regs s') Output ≡ input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input s) rdi-eq)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (mov Output Input) s) s loc
                                 (mov-preserves-stackMem Output Input s)
                                 (mov-preserves-heapMem Output Input s))

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc'' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        readLoc (proj₁ (exec-trace trace s'' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc''
      frontier-stable s'' _ not-halted'' _ slot-eq =
        let s''-final = proj₁ (exec-trace trace s'' alloc)
            s''-final-eq : s''-final ≡ exec (mov Output Input) s''
            s''-final-eq = cong proj₁ (exec-trace-single mov-to-output s'' alloc not-halted'')
        in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc))) s''-final-eq)
                 (trans (readLoc-stackMem-eq (exec (mov Output Input) s'') s''
                          (OnStack (current-frame alloc) (next-slot alloc))
                          (mov-preserves-stackMem Output Input s'')
                          (mov-preserves-heapMem Output Input s''))
                        slot-eq)
