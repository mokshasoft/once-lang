-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.SimpleWF
--
-- Simple IR cases using the clean trace-based structure.
-- Final states defined by exec-trace, making trace-correct = refl.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.SimpleWF where

open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import SMPrimitives for memory reasoning
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- Simple IR implementations
------------------------------------------------------------------------

module SimpleWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
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

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RaxConstraint; rax-output-eq; rax-erased; valid-unit-wf; valid-coerce-kind-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           decomposePairWF; PairValidWF)

  open import Once.CCC.Machine.FrontierLemma using (module FrontierLemmas)
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
    readReg (regs s) Input1 ≡ input-loc →
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
      ; rax-is-result = rax-output-eq rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = input-before
      ; reclaim-preserves-validity = valid-s'
      ; max-slot-written = next-slot alloc
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
      ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      ; scratch-bounded = m≤m+n (next-slot alloc) 0
      }
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      -- State equivalence via exec-trace-single
      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted

      valid-s' = subst (λ st → ValidAtWF _ alloc x input-loc st) (sym s'-eq)
                   (validityWF-mem-only x input-loc s (exec (mov Output Input1) s) refl refl input-valid-wf)

      rax-eq : readReg (regs s') Output ≡ input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input1 s) rdi-eq)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (mov Output Input1) s) s loc
                                 (mov-preserves-stackMem Output Input1 s)
                                 (mov-preserves-heapMem Output Input1 s))

      -- IR doesn't allocate, so return inj₁ refl
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Fst: extract first component from pair
  ------------------------------------------------------------------------

  run-fst : ∀ {m A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    ∃[ mA ] IRResultAWF mA (fst {A} {B}) x s alloc
  run-fst {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mA , record
      { result-loc = fst-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = fst-valid-s'
      ; result-before = fst-before
      ; rax-is-result = rax-output-eq rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = fst-before
      ; reclaim-preserves-validity = fst-valid-s'
      ; max-slot-written = next-slot alloc
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
      ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-load-indirect tph-[]
      ; scratch-bounded = m≤m+n (next-slot alloc) 0
      }
    where
      pair-decomp = decomposePairWF {m} input-valid-wf
      mA = PairValidWF.mA pair-decomp
      fst-loc = PairValidWF.fst-loc pair-decomp
      fst-valid-wf = PairValidWF.fst-valid pair-decomp
      fst-before = PairValidWF.fst-before pair-decomp

      mem-read : readLoc s (resolveSourceExt (regs s) (IndReg Input1)) ≡ just fst-loc
      mem-read = subst (λ loc → readLoc s loc ≡ just fst-loc)
                       (sym rdi-eq) (PairValidWF.fst-ptr pair-decomp)

      trace : AbstractTrace
      trace = load-indirect ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (load Output (IndReg Input1)) s
      s'-eq = cong proj₁ (exec-trace-single load-indirect s alloc not-halted)

      fst-valid-s' : ValidAtWF mA alloc (proj₁ x) fst-loc s'
      fst-valid-s' = subst (λ st → ValidAtWF mA alloc (proj₁ x) fst-loc st) (sym s'-eq)
                       (validityWF-mem-only (proj₁ x) fst-loc s (exec (load Output (IndReg Input1)) s)
                          (load-preserves-stackMem Output (IndReg Input1) s)
                          (load-preserves-heapMem Output (IndReg Input1) s)
                          fst-valid-wf)

      rax-eq : readReg (regs s') Output ≡ fst-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (load-result Output (IndReg Input1) s fst-loc mem-read)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq)
                      (load-no-halt Output (IndReg Input1) s fst-loc mem-read not-halted)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (load Output (IndReg Input1)) s) s loc
                                 (load-preserves-stackMem Output (IndReg Input1) s)
                                 (load-preserves-heapMem Output (IndReg Input1) s))

      -- IR doesn't allocate, so return inj₁ refl
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Snd: extract second component from pair
  ------------------------------------------------------------------------

  run-snd : ∀ {m A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    ∃[ mB ] IRResultAWF mB (snd {A} {B}) x s alloc
  run-snd {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mB , record
      { result-loc = snd-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; trace = trace
      ; trace-correct = refl  -- s' DEFINED by trace
      ; result-valid-wf = snd-valid-s'
      ; result-before = snd-before
      ; rax-is-result = rax-output-eq rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = snd-before
      ; reclaim-preserves-validity = snd-valid-s'
      ; max-slot-written = next-slot alloc
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
      ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-load-indirect-suc tph-[]
      ; scratch-bounded = m≤m+n (next-slot alloc) 0
      }
    where
      pair-decomp = decomposePairWF {m} input-valid-wf
      mB = PairValidWF.mB pair-decomp
      snd-loc = PairValidWF.snd-loc pair-decomp
      snd-valid-wf = PairValidWF.snd-valid pair-decomp
      snd-before = PairValidWF.snd-before pair-decomp

      mem-read : readLoc s (resolveSourceExt (regs s) (IndRegSuc Input1)) ≡ just snd-loc
      mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just snd-loc)
                       (sym rdi-eq) (PairValidWF.snd-ptr pair-decomp)

      trace : AbstractTrace
      trace = load-indirect-suc ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (load Output (IndRegSuc Input1)) s
      s'-eq = cong proj₁ (exec-trace-single load-indirect-suc s alloc not-halted)

      snd-valid-s' : ValidAtWF mB alloc (proj₂ x) snd-loc s'
      snd-valid-s' = subst (λ st → ValidAtWF mB alloc (proj₂ x) snd-loc st) (sym s'-eq)
                       (validityWF-mem-only (proj₂ x) snd-loc s (exec (load Output (IndRegSuc Input1)) s)
                          (load-preserves-stackMem Output (IndRegSuc Input1) s)
                          (load-preserves-heapMem Output (IndRegSuc Input1) s)
                          snd-valid-wf)

      rax-eq : readReg (regs s') Output ≡ snd-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (load-result Output (IndRegSuc Input1) s snd-loc mem-read)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq)
                      (load-no-halt Output (IndRegSuc Input1) s snd-loc mem-read not-halted)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (load Output (IndRegSuc Input1)) s) s loc
                                 (load-preserves-stackMem Output (IndRegSuc Input1) s)
                                 (load-preserves-heapMem Output (IndRegSuc Input1) s))

      -- IR doesn't allocate, so return inj₁ refl
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Terminal: output unit
  ------------------------------------------------------------------------

  run-terminal : ∀ {m A}
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    IRResultAWF m (terminal {A}) x s alloc
  -- Plan 0.2.4.5 D1 (Unit erasure): terminal produces a Unit value
  -- which carries no information. result-loc = Erased, trace = []
  -- (no-op), and rax-is-result = rax-erased (no Output equation).
  -- The Unit value is genuinely "nowhere" — no register, no slot,
  -- no observable state delta.
  run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { result-loc = Erased
      ; final-state = s
      ; final-alloc = alloc
      ; trace = []
      ; trace-correct = refl
      ; result-valid-wf = valid-unit-wf
      ; result-before = erased-before
      ; rax-is-result = rax-erased
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; reclaim-preserves-result = erased-before
      ; reclaim-preserves-validity = valid-unit-wf
      ; max-slot-written = next-slot alloc
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
      ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-[]
      ; scratch-bounded = m≤m+n (next-slot alloc) 0
      }
    where
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Free-heap: explicit heap deallocation (semantically a no-op)
  ------------------------------------------------------------------------

  run-free-heap : ∀ {m} (ref : HeapRef)
    (x : ⟦ Unit ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
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
      ; rax-is-result = rax-output-eq rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = input-before
      ; reclaim-preserves-validity = valid-s'
      ; max-slot-written = next-slot alloc
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
      ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      ; scratch-bounded = m≤m+n (next-slot alloc) 0
      }
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted

      valid-s' = subst (λ st → ValidAtWF _ alloc x input-loc st) (sym s'-eq)
                   (validityWF-mem-only x input-loc s (exec (mov Output Input1) s) refl refl input-valid-wf)

      rax-eq : readReg (regs s') Output ≡ input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input1 s) rdi-eq)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (mov Output Input1) s) s loc
                                 (mov-preserves-stackMem Output Input1 s)
                                 (mov-preserves-heapMem Output Input1 s))

      -- IR doesn't allocate, so return inj₁ refl
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Arr: effectful morphism coercion (A ⇒[ mk-kind q pure ] B) to (A ⇒[ mk-kind Many eff ] B)
  ------------------------------------------------------------------------

  run-arr : ∀ {m A B q}
    (x : ⟦ A ⇒[ mk-kind q pure ] B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc {A ⇒[ mk-kind q pure ] B} x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
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
      ; rax-is-result = rax-output-eq rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = input-before
      ; reclaim-preserves-validity = valid-eff
      ; max-slot-written = next-slot alloc
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
      ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      ; scratch-bounded = m≤m+n (next-slot alloc) 0
      }
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted

      valid-s' : ValidAtWF m alloc {A ⇒[ mk-kind q pure ] B} x input-loc s'
      valid-s' = subst (λ st → ValidAtWF m alloc {A ⇒[ mk-kind q pure ] B} x input-loc st) (sym s'-eq)
                   (validityWF-mem-only x input-loc s (exec (mov Output Input1) s) refl refl input-valid-wf)

      valid-eff : ValidAtWF m alloc {A ⇒[ mk-kind Many eff ] B} x input-loc s'
      valid-eff = valid-coerce-kind-wf valid-s'

      rax-eq : readReg (regs s') Output ≡ input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input1 s) rdi-eq)

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = trans (cong (λ st → readLoc st loc) s'-eq)
                              (readLoc-stackMem-eq (exec (mov Output Input1) s) s loc
                                 (mov-preserves-stackMem Output Input1 s)
                                 (mov-preserves-heapMem Output Input1 s))

      -- IR doesn't allocate, so return inj₁ refl
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'' →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl