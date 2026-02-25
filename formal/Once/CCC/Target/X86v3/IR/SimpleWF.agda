------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.SimpleWF
--
-- Simple IR cases that don't require recursion: id, fst, snd, terminal.
-- Extracted from Dispatcher.agda to minimize the mutual block.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.IR.SimpleWF where

open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine using (HeapRef)
open import Once.CCC.SlotMachine
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Simple IR implementations
------------------------------------------------------------------------

module SimpleWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  open import Once.CCC.Target.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; valid-unit-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           decomposePairWF; PairValidWF)

  -- Import frontier-same-heap for reclaim-preserves-result
  open import Once.CCC.Target.X86v3.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap)

  ------------------------------------------------------------------------
  -- Identity: output is same as input (same mode preserved)
  ------------------------------------------------------------------------

  run-id : ∀ {m A}
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultAWF m (id {A}) x s alloc
  run-id x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let s' = exec (mov RAX RDI) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = validityWF-mem-only x input-loc s s' refl refl input-valid-wf
      ; result-before = input-before
      ; rax-is-result = trans (mov-result RAX RDI s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (mov-preserves-stackMem RAX RDI s)
            (mov-preserves-heapMem RAX RDI s)
      -- Reclamation: id doesn't allocate, so we can reclaim to original next-slot
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl input-loc input-before
      ; reclaim-preserves-validity = λ fits →
          -- Transfer validity: alloc → reclaimed alloc (only slots-available differs)
          -- Then: s → s' (memory preserved)
          validityWF-frontier-advance x input-loc s' refl ≤-refl ≤-refl
            (validityWF-mem-only x input-loc s s' refl refl input-valid-wf)
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement id = 0
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
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mA ] IRResultAWF mA (fst-ir {A} {B}) x s alloc
  run-fst {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let pair-decomp = decomposePairWF {m} input-valid-wf
        mA = PairValidWF.mA pair-decomp
        fst-loc = PairValidWF.fst-loc pair-decomp
        fst-valid-wf = PairValidWF.fst-valid pair-decomp
        fst-before = PairValidWF.fst-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndReg RDI)) ≡ just fst-loc
        mem-read = subst (λ loc → readLoc s loc ≡ just fst-loc)
                         (sym rdi-eq) (PairValidWF.fst-ptr pair-decomp)
        s' = exec (load RAX (IndReg RDI)) s
        fst-valid-wf-s' = validityWF-mem-only (proj₁ x) fst-loc s s'
                            (load-preserves-stackMem RAX (IndReg RDI) s)
                            (load-preserves-heapMem RAX (IndReg RDI) s)
                            fst-valid-wf
    in mA , record
      { result-loc = fst-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = fst-valid-wf-s'
      ; result-before = fst-before
      ; rax-is-result = load-result RAX (IndReg RDI) s fst-loc mem-read
      ; not-halted = load-no-halt RAX (IndReg RDI) s fst-loc mem-read not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (load-preserves-stackMem RAX (IndReg RDI) s)
            (load-preserves-heapMem RAX (IndReg RDI) s)
      -- Reclamation: fst doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl fst-loc fst-before
      ; reclaim-preserves-validity = λ fits →
          -- Transfer from alloc to reclaimed alloc (only slots-available differs)
          validityWF-frontier-advance (proj₁ x) fst-loc s' refl ≤-refl ≤-refl fst-valid-wf-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement fst-ir = 0
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
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mB ] IRResultAWF mB (snd-ir {A} {B}) x s alloc
  run-snd {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let pair-decomp = decomposePairWF {m} input-valid-wf
        mB = PairValidWF.mB pair-decomp
        snd-loc = PairValidWF.snd-loc pair-decomp
        snd-valid-wf = PairValidWF.snd-valid pair-decomp
        snd-before = PairValidWF.snd-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndRegSuc RDI)) ≡ just snd-loc
        mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just snd-loc)
                         (sym rdi-eq) (PairValidWF.snd-ptr pair-decomp)
        s' = exec (load RAX (IndRegSuc RDI)) s
        snd-valid-wf-s' = validityWF-mem-only (proj₂ x) snd-loc s s'
                            (load-preserves-stackMem RAX (IndRegSuc RDI) s)
                            (load-preserves-heapMem RAX (IndRegSuc RDI) s)
                            snd-valid-wf
    in mB , record
      { result-loc = snd-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = snd-valid-wf-s'
      ; result-before = snd-before
      ; rax-is-result = load-result RAX (IndRegSuc RDI) s snd-loc mem-read
      ; not-halted = load-no-halt RAX (IndRegSuc RDI) s snd-loc mem-read not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (load-preserves-stackMem RAX (IndRegSuc RDI) s)
            (load-preserves-heapMem RAX (IndRegSuc RDI) s)
      -- Reclamation: snd doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl snd-loc snd-before
      ; reclaim-preserves-validity = λ fits →
          -- Transfer from alloc to reclaimed alloc (only slots-available differs)
          validityWF-frontier-advance (proj₂ x) snd-loc s' refl ≤-refl ≤-refl snd-valid-wf-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement snd-ir = 0
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
    readReg (regs s) RDI ≡ input-loc →
    IRResultAWF m (terminal {A}) x s alloc
  run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let s' = exec (mov RAX RDI) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = valid-unit-wf
      ; result-before = input-before
      ; rax-is-result = trans (mov-result RAX RDI s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (mov-preserves-stackMem RAX RDI s)
            (mov-preserves-heapMem RAX RDI s)
      -- Reclamation: terminal doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl input-loc input-before
      ; reclaim-preserves-validity = λ fits → valid-unit-wf
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement terminal = 0
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
    readReg (regs s) RDI ≡ input-loc →
    IRResultAWF m (free-heap ref) x s alloc
  run-free-heap ref x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let s' = exec (mov RAX RDI) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = validityWF-mem-only x input-loc s s' refl refl input-valid-wf
      ; result-before = input-before
      ; rax-is-result = trans (mov-result RAX RDI s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (mov-preserves-stackMem RAX RDI s)
            (mov-preserves-heapMem RAX RDI s)
      -- Reclamation: free-heap doesn't allocate stack space
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl input-loc input-before
      ; reclaim-preserves-validity = λ fits →
          validityWF-frontier-advance x input-loc s' refl ≤-refl ≤-refl
            (validityWF-mem-only x input-loc s s' refl refl input-valid-wf)
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0  -- ir-stack-requirement (free-heap _) = 0
      }
