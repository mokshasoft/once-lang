------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.SimpleWF
--
-- Simple IR cases that don't require recursion: id, fst, snd, terminal.
-- Extracted from Dispatcher.agda to minimize the mutual block.
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
open import Once.CCC.SlotMachine hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)

-- Import SMPrimitives qualified for trace predicates
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

  -- Open SMPrimitives modules for trace predicates
  open SMP.TracePrimitives {FS}

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; valid-unit-wf; valid-eff-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           decomposePairWF; PairValidWF)

  -- Import frontier-same-heap for reclaim-preserves-result
  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap)

  ------------------------------------------------------------------------
  -- Trace state correctness proofs
  --
  -- IRResultAWF.trace-correct now proves proj₁ (exec-trace ...) ≡ final-state
  -- to separate runtime state from compile-time allocation tracking.
  --
  -- For load instructions, exec-abstract is now defined via exec,
  -- so these proofs are trivial by definitional equality + cong proj₁.
  ------------------------------------------------------------------------

  -- Helper: extract state part from full trace equality
  state-eq : ∀ {s s' : LocState FS} {alloc alloc' : AllocState {FS}} →
    (s , alloc) ≡ (s' , alloc') → s ≡ s'
  state-eq refl = refl

  -- mov-to-output state correctness
  mov-to-output-trace-state : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡ exec (mov Output Input) s
  mov-to-output-trace-state s alloc not-halted =
    cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

  -- Alias for frontier-slot-stable proofs
  mov-to-output-state-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡ exec (mov Output Input) s
  mov-to-output-state-eq = mov-to-output-trace-state

  -- load-indirect state correctness (PROVEN)
  load-indirect-trace-state : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (load-indirect ∷ []) s alloc) ≡ exec (load Output (IndReg Input)) s
  load-indirect-trace-state s alloc not-halted =
    cong proj₁ (exec-trace-single load-indirect s alloc not-halted)

  -- load-indirect-suc state correctness (PROVEN)
  load-indirect-suc-trace-state : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (load-indirect-suc ∷ []) s alloc) ≡ exec (load Output (IndRegSuc Input)) s
  load-indirect-suc-trace-state s alloc not-halted =
    cong proj₁ (exec-trace-single load-indirect-suc s alloc not-halted)

  ------------------------------------------------------------------------
  -- Identity: output is same as input (same mode preserved)
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
    let s' = exec (mov Output Input) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = mov-to-output ∷ []
      ; trace-correct = mov-to-output-trace-state s alloc not-halted
      ; result-valid-wf = validityWF-mem-only x input-loc s s' refl refl input-valid-wf
      ; result-before = input-before
      ; rax-is-result = trans (mov-result Output Input s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (mov-preserves-stackMem Output Input s)
            (mov-preserves-heapMem Output Input s)
      -- Reclamation: id doesn't allocate, so we can reclaim to original next-slot
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits → input-before
      ; reclaim-preserves-validity = λ fits →
          -- Then: s → s' (memory preserved)
          validityWF-mem-only x input-loc s s' refl refl input-valid-wf
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement id = 0
      -- Frontier slot stability: mov-to-output only modifies regs, not stackMem
      ; frontier-slot-stable = λ s'' input-loc'' s''-not-halted input-eq'' slot-eq'' →
          trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc)))
                      (mov-to-output-state-eq s'' alloc s''-not-halted))
                slot-eq''
      ; trace-writes-above = tt  -- mov-to-output has no stores
      ; trace-slot-reads-above = tt  -- no slot reads
      ; trace-writes-below = tt  -- no slot writes
      ; trace-slot-reads-below = tt  -- no slot reads
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-store-indirect = tt , tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }

  ------------------------------------------------------------------------
  -- Fst: extract first component from pair (any mode)
  --
  -- Reference-based model: both Stack and Heap use pointer indirection
  -- Output mode is component's mode (mA)
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
    let pair-decomp = decomposePairWF {m} input-valid-wf
        mA = PairValidWF.mA pair-decomp
        fst-loc = PairValidWF.fst-loc pair-decomp
        fst-valid-wf = PairValidWF.fst-valid pair-decomp
        fst-before = PairValidWF.fst-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndReg Input)) ≡ just fst-loc
        mem-read = subst (λ loc → readLoc s loc ≡ just fst-loc)
                         (sym rdi-eq) (PairValidWF.fst-ptr pair-decomp)
        s' = exec (load Output (IndReg Input)) s
        fst-valid-wf-s' = validityWF-mem-only (proj₁ x) fst-loc s s'
                            (load-preserves-stackMem Output (IndReg Input) s)
                            (load-preserves-heapMem Output (IndReg Input) s)
                            fst-valid-wf
    in mA , record
      { result-loc = fst-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = load-indirect ∷ []
      ; trace-correct = load-indirect-trace-state s alloc not-halted
      ; result-valid-wf = fst-valid-wf-s'
      ; result-before = fst-before
      ; rax-is-result = load-result Output (IndReg Input) s fst-loc mem-read
      ; not-halted = load-no-halt Output (IndReg Input) s fst-loc mem-read not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (load-preserves-stackMem Output (IndReg Input) s)
            (load-preserves-heapMem Output (IndReg Input) s)
      -- Reclamation: fst doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits → fst-before
      ; reclaim-preserves-validity = λ fits → fst-valid-wf-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement fst-ir = 0
      -- Frontier slot stability: load only modifies regs, not stackMem
      ; frontier-slot-stable = λ s'' input-loc'' s''-not-halted input-eq'' slot-eq'' →
          trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc)))
                      (load-indirect-trace-state s'' alloc s''-not-halted))
                (trans (readLoc-stackMem-eq (exec (load Output (IndReg Input)) s'') s''
                         (OnStack (current-frame alloc) (next-slot alloc))
                         (load-preserves-stackMem Output (IndReg Input) s'')
                         (load-preserves-heapMem Output (IndReg Input) s''))
                       slot-eq'')
      ; trace-writes-above = tt  -- load-indirect has no stores
      ; trace-slot-reads-above = tt  -- no slot reads
      ; trace-writes-below = tt  -- no slot writes
      ; trace-slot-reads-below = tt  -- no slot reads
      ; trace-preserves-capacity = tpc-∷ ipc-load-indirect tpc-[]
      ; trace-no-store-indirect = tt , tt
      ; trace-preserves-halted = tph-∷ iph-load-indirect tph-[]
      }

  ------------------------------------------------------------------------
  -- Snd: extract second component from pair (any mode)
  --
  -- Reference-based model: both Stack and Heap use pointer indirection
  -- Output mode is component's mode (mB)
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
    let pair-decomp = decomposePairWF {m} input-valid-wf
        mB = PairValidWF.mB pair-decomp
        snd-loc = PairValidWF.snd-loc pair-decomp
        snd-valid-wf = PairValidWF.snd-valid pair-decomp
        snd-before = PairValidWF.snd-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndRegSuc Input)) ≡ just snd-loc
        mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just snd-loc)
                         (sym rdi-eq) (PairValidWF.snd-ptr pair-decomp)
        s' = exec (load Output (IndRegSuc Input)) s
        snd-valid-wf-s' = validityWF-mem-only (proj₂ x) snd-loc s s'
                            (load-preserves-stackMem Output (IndRegSuc Input) s)
                            (load-preserves-heapMem Output (IndRegSuc Input) s)
                            snd-valid-wf
    in mB , record
      { result-loc = snd-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = load-indirect-suc ∷ []
      ; trace-correct = load-indirect-suc-trace-state s alloc not-halted
      ; result-valid-wf = snd-valid-wf-s'
      ; result-before = snd-before
      ; rax-is-result = load-result Output (IndRegSuc Input) s snd-loc mem-read
      ; not-halted = load-no-halt Output (IndRegSuc Input) s snd-loc mem-read not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (load-preserves-stackMem Output (IndRegSuc Input) s)
            (load-preserves-heapMem Output (IndRegSuc Input) s)
      -- Reclamation: snd doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits → snd-before
      ; reclaim-preserves-validity = λ fits → snd-valid-wf-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement snd-ir = 0
      -- Frontier slot stability: load only modifies regs, not stackMem
      ; frontier-slot-stable = λ s'' input-loc'' s''-not-halted input-eq'' slot-eq'' →
          trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc)))
                      (load-indirect-suc-trace-state s'' alloc s''-not-halted))
                (trans (readLoc-stackMem-eq (exec (load Output (IndRegSuc Input)) s'') s''
                         (OnStack (current-frame alloc) (next-slot alloc))
                         (load-preserves-stackMem Output (IndRegSuc Input) s'')
                         (load-preserves-heapMem Output (IndRegSuc Input) s''))
                       slot-eq'')
      ; trace-writes-above = tt  -- load-indirect-suc has no stores
      ; trace-slot-reads-above = tt  -- no slot reads
      ; trace-writes-below = tt  -- no slot writes
      ; trace-slot-reads-below = tt  -- no slot reads
      ; trace-preserves-capacity = tpc-∷ ipc-load-indirect-suc tpc-[]
      ; trace-no-store-indirect = tt , tt
      ; trace-preserves-halted = tph-∷ iph-load-indirect-suc tph-[]
      }

  ------------------------------------------------------------------------
  -- Terminal: output unit (any mode, unit is valid at any mode)
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
    let s' = exec (mov Output Input) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = mov-to-output ∷ []
      ; trace-correct = mov-to-output-trace-state s alloc not-halted
      ; result-valid-wf = valid-unit-wf
      ; result-before = input-before
      ; rax-is-result = trans (mov-result Output Input s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (mov-preserves-stackMem Output Input s)
            (mov-preserves-heapMem Output Input s)
      -- Reclamation: terminal doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits → input-before
      ; reclaim-preserves-validity = λ fits → valid-unit-wf
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement terminal = 0
      -- Frontier slot stability: mov-to-output only modifies regs, not stackMem
      ; frontier-slot-stable = λ s'' input-loc'' s''-not-halted input-eq'' slot-eq'' →
          trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc)))
                      (mov-to-output-state-eq s'' alloc s''-not-halted))
                slot-eq''
      ; trace-writes-above = tt  -- mov-to-output has no stores
      ; trace-slot-reads-above = tt  -- no slot reads
      ; trace-writes-below = tt  -- no slot writes
      ; trace-slot-reads-below = tt  -- no slot reads
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-store-indirect = tt , tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }

  ------------------------------------------------------------------------
  -- Free-heap: explicit heap deallocation
  --
  -- Semantically a no-op (returns input unchanged).
  -- Actual heap deallocation happens at runtime.
  -- TODO: Add CanFreeHeap proof requirement when EscapeInterface is ready.
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
    let s' = exec (mov Output Input) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = mov-to-output ∷ []
      ; trace-correct = mov-to-output-trace-state s alloc not-halted
      ; result-valid-wf = validityWF-mem-only x input-loc s s' refl refl input-valid-wf
      ; result-before = input-before
      ; rax-is-result = trans (mov-result Output Input s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (mov-preserves-stackMem Output Input s)
            (mov-preserves-heapMem Output Input s)
      -- Reclamation: free-heap doesn't allocate stack space
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits → input-before
      ; reclaim-preserves-validity = λ fits →
          validityWF-mem-only x input-loc s s' refl refl input-valid-wf
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement (free-heap _) = 0
      -- Frontier slot stability: mov-to-output only modifies regs, not stackMem
      ; frontier-slot-stable = λ s'' input-loc'' s''-not-halted input-eq'' slot-eq'' →
          trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc)))
                      (mov-to-output-state-eq s'' alloc s''-not-halted))
                slot-eq''
      ; trace-writes-above = tt  -- mov-to-output has no stores
      ; trace-slot-reads-above = tt  -- no slot reads
      ; trace-writes-below = tt  -- no slot writes
      ; trace-slot-reads-below = tt  -- no slot reads
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-store-indirect = tt , tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }

  ------------------------------------------------------------------------
  -- Arr: effectful morphism coercion
  --
  -- Converts (A ⇒[ q ] B) to (Eff A B). Semantically identity since
  -- ⟦ A ⇒[ q ] B ⟧ = ⟦ Eff A B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
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
    let s' = exec (mov Output Input) s
        -- Transfer validity from s to s' (memory preserved)
        valid-s' : ValidAtWF m alloc x input-loc s'
        valid-s' = validityWF-mem-only x input-loc s s' refl refl input-valid-wf
        -- Coerce type from (A ⇒[ q ] B) to (Eff A B)
        valid-eff : ValidAtWF m alloc {Eff A B} x input-loc s'
        valid-eff = valid-eff-wf {m} {A} {B} {q} valid-s'
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = mov-to-output ∷ []
      ; trace-correct = mov-to-output-trace-state s alloc not-halted
      ; result-valid-wf = valid-eff
      ; result-before = input-before
      ; rax-is-result = trans (mov-result Output Input s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (mov-preserves-stackMem Output Input s)
            (mov-preserves-heapMem Output Input s)
      -- Reclamation: arr doesn't allocate, so we can reclaim to original next-slot
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits → input-before
      ; reclaim-preserves-validity = λ fits →
          -- Transfer validity, then coerce type
          valid-eff-wf {m} {A} {B} {q} valid-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement arr = 0
      -- Frontier slot stability: mov-to-output only modifies regs, not stackMem
      ; frontier-slot-stable = λ s'' input-loc'' s''-not-halted input-eq'' slot-eq'' →
          trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc)))
                      (mov-to-output-state-eq s'' alloc s''-not-halted))
                slot-eq''
      ; trace-writes-above = tt  -- mov-to-output has no stores
      ; trace-slot-reads-above = tt  -- no slot reads
      ; trace-writes-below = tt  -- no slot writes
      ; trace-slot-reads-below = tt  -- no slot reads
      ; trace-preserves-capacity = tpc-∷ ipc-mov-to-output tpc-[]
      ; trace-no-store-indirect = tt , tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }
