------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.SimpleWF
--
-- Simple IR cases that don't require recursion: id, fst, snd, terminal.
-- Extracted from Dispatcher.agda to minimize the mutual block.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.SimpleWF where

open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)

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

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; valid-unit-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           decomposePairBoxedWF; PairBoxedValidWF;
           decomposePairUnboxedWF; PairUnboxedValidWF)

  -- Import frontier-same-heap for reclaim-preserves-result
  open import Once.Backend.X86v3.FrontierLemma using (module FrontierLemmas)
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
  -- Fst: extract first component from boxed pair
  -- Input must be Heap (boxed), output mode is component's mode (mA)
  ------------------------------------------------------------------------

  run-fst : ∀ {A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF Heap alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mA ] IRResultAWF mA (fst-ir {A} {B}) x s alloc
  run-fst {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let pair-decomp = decomposePairBoxedWF input-valid-wf
        mA = PairBoxedValidWF.mA pair-decomp
        fst-loc = PairBoxedValidWF.fst-loc pair-decomp
        fst-valid-wf = PairBoxedValidWF.fst-valid pair-decomp
        fst-before = PairBoxedValidWF.fst-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndReg RDI)) ≡ just fst-loc
        mem-read = subst (λ loc → readLoc s loc ≡ just fst-loc)
                         (sym rdi-eq) (PairBoxedValidWF.fst-ptr pair-decomp)
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
  -- Snd: extract second component from boxed pair
  -- Input must be Heap (boxed), output mode is component's mode (mB)
  ------------------------------------------------------------------------

  run-snd : ∀ {A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF Heap alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mB ] IRResultAWF mB (snd-ir {A} {B}) x s alloc
  run-snd {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let pair-decomp = decomposePairBoxedWF input-valid-wf
        mB = PairBoxedValidWF.mB pair-decomp
        snd-loc = PairBoxedValidWF.snd-loc pair-decomp
        snd-valid-wf = PairBoxedValidWF.snd-valid pair-decomp
        snd-before = PairBoxedValidWF.snd-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndRegSuc RDI)) ≡ just snd-loc
        mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just snd-loc)
                         (sym rdi-eq) (PairBoxedValidWF.snd-ptr pair-decomp)
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
  -- Fst-Stack: extract first component from unboxed pair
  -- Input must be Stack (unboxed), output mode is component's mode (mA)
  --
  -- For unboxed pairs, the first component IS at input-loc (no dereference)
  ------------------------------------------------------------------------

  run-stack-fst : ∀ {A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF Stack alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mA ] IRResultAWF mA (fst-ir {A} {B}) x s alloc
  run-stack-fst {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let pair-decomp = decomposePairUnboxedWF input-valid-wf
        mA = PairUnboxedValidWF.mA pair-decomp
        fst-valid-wf = PairUnboxedValidWF.fst-valid pair-decomp
        fst-before = PairUnboxedValidWF.fst-before pair-decomp
        -- For unboxed pairs, fst is at input-loc (no dereference needed)
        -- Just move RDI to RAX
        s' = exec (mov RAX RDI) s
        fst-valid-wf-s' = validityWF-mem-only (proj₁ x) input-loc s s'
                            (mov-preserves-stackMem RAX RDI s)
                            (mov-preserves-heapMem RAX RDI s)
                            fst-valid-wf
    in mA , record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = fst-valid-wf-s'
      ; result-before = fst-before
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
      -- Reclamation: fst doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl input-loc fst-before
      ; reclaim-preserves-validity = λ fits →
          validityWF-frontier-advance (proj₁ x) input-loc s' refl ≤-refl ≤-refl fst-valid-wf-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
      }

  ------------------------------------------------------------------------
  -- Snd-Stack: extract second component from unboxed pair
  -- Input must be Stack (unboxed), output mode is component's mode (mB)
  --
  -- For unboxed pairs, the second component is at offsetLoc input-loc (stack-type-slots A)
  -- No dereference needed - just compute the offset address
  ------------------------------------------------------------------------

  run-stack-snd : ∀ {A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF Stack alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mB ] IRResultAWF mB (snd-ir {A} {B}) x s alloc
  run-stack-snd {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let pair-decomp = decomposePairUnboxedWF input-valid-wf
        mB = PairUnboxedValidWF.mB pair-decomp
        snd-loc = offsetLoc input-loc (stack-type-slots A)
        snd-valid-wf = PairUnboxedValidWF.snd-valid pair-decomp
        snd-before = PairUnboxedValidWF.snd-before pair-decomp
        -- For unboxed pairs, snd is at offset (no dereference needed)
        -- Set RAX to the computed offset location
        s' = record s { regs = writeReg (regs s) RAX snd-loc }
        snd-valid-wf-s' = validityWF-mem-only (proj₂ x) snd-loc s s' refl refl snd-valid-wf
    in mB , record
      { result-loc = snd-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = snd-valid-wf-s'
      ; result-before = snd-before
      ; rax-is-result = writeReg-same (regs s) RAX snd-loc
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ → readLoc-stackMem-eq s' s loc refl refl  -- Only registers changed
      -- Reclamation: snd doesn't allocate
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl snd-loc snd-before
      ; reclaim-preserves-validity = λ fits →
          validityWF-frontier-advance (proj₂ x) snd-loc s' refl ≤-refl ≤-refl snd-valid-wf-s'
      ; reclaim-size-bound = m≤m+n (next-slot alloc) 0
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
