-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.SimpleWF
--
-- Simple IR cases using the clean trace-based structure.
-- Final states defined by exec-trace, making trace-correct = refl.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.SimpleWF where

open import Data.Nat using (ℕ; _<_; _≤_; z≤n) renaming (_+_ to _+ℕ_)
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
open import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import SMPrimitives for memory reasoning
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- Simple IR implementations
------------------------------------------------------------------------

module SimpleWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (FrameSemantics.float-format FS)

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
  open SMP.RecSchemeSemantics {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF;
           ResultPlace; unit-result; at-loc;
           valid-unit-wf; valid-coerce-kind-wf;
           mk-IRResultAWF-via-bump;
           validityWF-mem-only; validityWF-frontier-advance;
           decomposePairWF; PairValidWF; mem-preserved-from-tnhw)

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
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (id {A}) x s alloc
  run-id x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s' alloc trace bump-0 refl
      refl  -- trace-is-ir-to-trace
      refl  -- trace-correct
      (cong proj₂ (exec-trace-single mov-to-output s alloc not-halted))
      (at-loc input-loc valid-s' input-before rax-eq valid-s' input-before)
      not-halted'
      (mem-preserved-from-tnhw alloc trace s s' refl tt tt)
      (twf-∷ tt twf-[])
      (exec-trace-preserves-halted-WF trace)
      (tt , tt)
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = 0
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = 0
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
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

      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq)
                     (trans (mov-result Output Input1 s) rdi-eq)

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc'') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Fst: extract first component from pair
  ------------------------------------------------------------------------

  -- Plan 0.13.2/0.13.3: lifted to StoredValue input/output. Trace-preserves-halted
  -- now uses TraceWF; rax-eq witnesses readReg ≡ SV-Ptr fst-loc.
  run-fst : ∀ {m A B}
    (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mA ] IRResultAWF mA (fst {A} {B}) x s alloc
  run-fst {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mA , mk-IRResultAWF-via-bump
      s' alloc trace bump-0 refl
      refl  -- trace-is-ir-to-trace
      refl  -- trace-correct
      (trans (cong proj₂ (exec-trace-single load-indirect s alloc not-halted))
             (exec-abstract-load-indirect-preserves-alloc s alloc))
      (at-loc fst-loc fst-valid-s' fst-before rax-eq fst-valid-s' fst-before)
      not-halted'
      (mem-preserved-from-tnhw alloc trace s s' refl tt tt)
      (twf-∷ (input-loc , sv-as-loc-eq , SV-Ptr fst-loc , fst-ptr-eq) twf-[])
      (exec-trace-preserves-halted-WF trace)
      (tt , tt)
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = 0
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = 0
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      pair-decomp = decomposePairWF {m} input-valid-wf
      mA = PairValidWF.mA pair-decomp
      fst-loc = PairValidWF.fst-loc pair-decomp
      fst-valid-wf = PairValidWF.fst-valid pair-decomp
      fst-before = PairValidWF.fst-before pair-decomp

      -- InstrWF witness for load-indirect at state s.
      sv-as-loc-eq : sv-as-loc (readReg (regs s) Input1) ≡ just input-loc
      sv-as-loc-eq = cong sv-as-loc rdi-eq

      fst-ptr-eq : readLoc s input-loc ≡ just (SV-Ptr fst-loc)
      fst-ptr-eq = PairValidWF.fst-ptr pair-decomp

      trace : AbstractTrace
      trace = load-indirect ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      -- s' equals proj₁ (exec-abstract load-indirect s alloc) via exec-trace-single.
      -- Plan 0.13.2: chain through exec-abstract directly (the load
      -- now case-splits on `with sv-as-loc`, breaking the prior
      -- `≡ exec (load …)` definitional equality used by old SimpleWF).
      s-after : LocState FS
      s-after = proj₁ (exec-abstract load-indirect s alloc)

      s'-eq-abs : s' ≡ s-after
      s'-eq-abs = cong proj₁ (exec-trace-single load-indirect s alloc not-halted)

      fst-valid-s' : ValidAtWF mA alloc (proj₁ x) fst-loc s'
      fst-valid-s' = subst (λ st → ValidAtWF mA alloc (proj₁ x) fst-loc st) (sym s'-eq-abs)
                       (validityWF-mem-only (proj₁ x) fst-loc s s-after
                          (exec-abstract-load-indirect-preserves-stackMem s alloc)
                          (exec-abstract-load-indirect-preserves-heapMem s alloc)
                          fst-valid-wf)

      rax-eq : readReg (regs s') Output ≡ SV-Ptr fst-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq-abs)
                     (exec-abstract-load-indirect-output s alloc input-loc (SV-Ptr fst-loc) rdi-eq fst-ptr-eq)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq-abs)
                      (load-indirect-halted-success s alloc input-loc (SV-Ptr fst-loc) not-halted rdi-eq fst-ptr-eq)

      -- IR doesn't allocate, so return inj₁ refl
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc'') →
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
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mB ] IRResultAWF mB (snd {A} {B}) x s alloc
  run-snd {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mB , mk-IRResultAWF-via-bump
      s' alloc trace bump-0 refl
      refl refl
      (trans (cong proj₂ (exec-trace-single load-indirect-suc s alloc not-halted))
             (exec-abstract-load-indirect-suc-preserves-alloc s alloc))
      (at-loc snd-loc snd-valid-s' snd-before rax-eq snd-valid-s' snd-before)
      not-halted'
      (mem-preserved-from-tnhw alloc trace s s' refl tt tt)
      (twf-∷ (input-loc , sv-as-loc-eq , SV-Ptr snd-loc , snd-ptr-eq) twf-[])
      (exec-trace-preserves-halted-WF trace)
      (tt , tt)
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = 0
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = 0
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      pair-decomp = decomposePairWF {m} input-valid-wf
      mB = PairValidWF.mB pair-decomp
      snd-loc = PairValidWF.snd-loc pair-decomp
      snd-valid-wf = PairValidWF.snd-valid pair-decomp
      snd-before = PairValidWF.snd-before pair-decomp

      sv-as-loc-eq : sv-as-loc (readReg (regs s) Input1) ≡ just input-loc
      sv-as-loc-eq = cong sv-as-loc rdi-eq

      snd-ptr-eq : readLoc s (sucLoc input-loc) ≡ just (SV-Ptr snd-loc)
      snd-ptr-eq = PairValidWF.snd-ptr pair-decomp

      trace : AbstractTrace
      trace = load-indirect-suc ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s-after : LocState FS
      s-after = proj₁ (exec-abstract load-indirect-suc s alloc)

      s'-eq-abs : s' ≡ s-after
      s'-eq-abs = cong proj₁ (exec-trace-single load-indirect-suc s alloc not-halted)

      snd-valid-s' : ValidAtWF mB alloc (proj₂ x) snd-loc s'
      snd-valid-s' = subst (λ st → ValidAtWF mB alloc (proj₂ x) snd-loc st) (sym s'-eq-abs)
                       (validityWF-mem-only (proj₂ x) snd-loc s s-after
                          (exec-abstract-load-indirect-suc-preserves-stackMem s alloc)
                          (exec-abstract-load-indirect-suc-preserves-heapMem s alloc)
                          snd-valid-wf)

      rax-eq : readReg (regs s') Output ≡ SV-Ptr snd-loc
      rax-eq = trans (cong (λ st → readReg (regs st) Output) s'-eq-abs)
                     (exec-abstract-load-indirect-suc-output s alloc input-loc (SV-Ptr snd-loc) rdi-eq snd-ptr-eq)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq-abs)
                      (load-indirect-suc-halted-success s alloc input-loc (SV-Ptr snd-loc) not-halted rdi-eq snd-ptr-eq)

      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc'') →
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
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (terminal {A}) x s alloc
  -- Plan 0.2.4.5 D1 (Unit erasure): terminal produces a Unit value
  -- which has no observable content — no register, no slot, no
  -- state delta. result-place = unit-result (no location), trace =
  -- [] (no-op). The structural Unit-erasure: the spec doesn't carry
  -- any "where the value is" data because there is no value.
  run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s alloc [] bump-0 refl
      refl refl refl
      unit-result
      not-halted
      (mem-preserved-from-tnhw alloc [] s s refl tt tt)
      twf-[]
      (exec-trace-preserves-halted-WF [])
      tt
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = 0
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = 0
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc'') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Free-heap: explicit heap deallocation (semantically a no-op)
  ------------------------------------------------------------------------

  run-free-heap : ∀ {m} (ref : HeapRef)
    (x : ⟦ Unit ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc {Unit} x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (free-heap ref) x s alloc
  -- Plan 0.2.4.5 D1: free-heap : IR Unit Unit. Like terminal, it
  -- has a Unit-typed result — `unit-result` carries no location.
  run-free-heap ref x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s' alloc trace bump-0 refl
      refl refl
      (cong proj₂ (exec-trace-single mov-to-output s alloc not-halted))
      unit-result
      not-halted'
      (mem-preserved-from-tnhw alloc trace s s' refl tt tt)
      (twf-∷ tt twf-[])
      (exec-trace-preserves-halted-WF trace)
      (tt , tt)
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = 0
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = 0
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      trace : AbstractTrace
      trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      not-halted' : halted s' ≡ false
      not-halted' = subst (λ st → halted st ≡ false) (sym s'-eq) not-halted


      -- IR doesn't allocate, so return inj₁ refl
      frontier-stable : ∀ s'' input-loc'' →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc'') →
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
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (arr {A} {B} {q}) x s alloc
  run-arr {m} {A} {B} {q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s' alloc trace bump-0 refl
      refl refl
      (cong proj₂ (exec-trace-single mov-to-output s alloc not-halted))
      (at-loc input-loc valid-eff input-before rax-eq valid-eff input-before)
      not-halted'
      (mem-preserved-from-tnhw alloc trace s s' refl tt tt)
      (twf-∷ tt twf-[])
      (exec-trace-preserves-halted-WF trace)
      (tt , tt)
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = 0
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = 0
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
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

      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
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
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc'' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc'') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl