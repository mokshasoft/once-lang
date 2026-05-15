-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.SumRecWF
--
-- IR handlers for sum types (inl, inr, case, initial) and
-- recursion schemes (In, Cata, Out, Ana, Hylo).
--
-- OCP-0003: Renamed from SumFixWF. Old fold/unfold handlers removed
-- in favor of structured recursion schemes that guarantee totality
-- (Cata) and productivity (Ana via GuardedT).
------------------------------------------------------------------------

module Once.CCC.Machine.IR.SumRecWF where

open import Data.Nat using (ℕ; _<_; _≤_; suc; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; n<1+n; +-monoʳ-≤; m≤m*n; m<m+n; *-monoʳ-≤; ≤-irrelevant; <⇒≢; +-comm)
open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂; module ≡-Reasoning; ≢-sym)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧; sem-inl; sem-inr)
open import Once.CCC.IR
open import Once.Functor.Translate using (WellFormedF)
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.Memory.TypeSlots using (type-slots)

-- Import SMPrimitives qualified for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

-- Import consolidated postulates (shared with RecCoreWF, ParaWF, AnaWF)
import Once.CCC.Machine.IR.RecSchemePostulates as RSP

-- Import Lambek validity lemmas for In/Out operations
import Once.CCC.Machine.IR.LambekValidity as LV

------------------------------------------------------------------------
-- Sum and Fix IR implementations
------------------------------------------------------------------------

module SumRecWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules for trace predicates
  open SMP.TracePrimitives {FS}
  open SMP.RecSchemeSemantics {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; RecDispatcherWF; valid-unit-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance; validityWF-mem-preserved;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           decomposePairWF; PairValidWF;
           valid-inl-wf; valid-inr-wf;
           decomposeInlWF; decomposeInrWF;
           InlValidWF; InrValidWF)
  -- OCP-0003: valid-fold-wf, decomposeFoldWF, FoldValidWF removed.
  -- Use In/Cata/Out/Ana handlers instead.

  -- Import frontier lemmas
  open import Once.CCC.Machine.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap; at-frontier-becomes-before)

  -- Import write operations
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import suc<+2 lemma for Heap mode proofs
  open import Once.CCC.Machine.DispatcherArithmeticLemma using (suc<+2)

  ------------------------------------------------------------------------
  -- Trace state correctness
  --
  -- Each sum operation has a specific trace:
  -- - inl/inr: mov-to-output, store-at-slot, lea-slot (write payload, return sum addr)
  -- - case: dispatch trace (f-trace or g-trace depending on inl/inr)
  --
  -- Recursion schemes (In, Cata, Out, Ana, Hylo) are postulated.
  --
  -- Note: trace-correct now proves proj₁ (exec-trace trace s alloc) ≡ final-state
  -- This separates runtime state from compile-time allocation tracking.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Trace correctness lemmas
  --
  -- These show that specific instruction sequences produce the expected
  -- final state by unfolding exec-trace and exec-abstract definitions.
  ------------------------------------------------------------------------

  -- lea-slot state equality: executing lea-slot sets Output to the slot address
  lea-slot-state-eq : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (lea-slot slot ∷ []) s alloc) ≡
    record s { regs = writeReg (regs s) Output (SV-Ptr (AtStack (current-frame alloc) slot)) }
  lea-slot-state-eq slot s alloc not-halted =
    cong proj₁ (exec-trace-single (lea-slot slot) s alloc not-halted)

  -- load-indirect state equality: executing load-indirect dereferences Input1
  -- TODO (post-scaffold): under StoredValue, exec-abstract load-indirect
  -- splits on sv-as-loc Input1; restate accordingly.
  load-indirect-state-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (load-indirect ∷ []) s alloc) ≡ exec (load Output (IndReg Input1)) s
  load-indirect-state-eq s alloc not-halted = SMP.!!

  -- Postulate: trace correctness for inl/inr (Plan 0.13.1 tag-aware shape).
  --
  -- 5-instruction trace (matches `ir-to-trace`'s output for inl/inr):
  --   1. instr-load-tag-lit tag : Output := SV-Tag tag      (0 for inl, 1 for inr)
  --   2. store-at-slot result-slot : mem[result-slot] := SV-Tag tag
  --   3. mov-to-output : Output := Input1 = SV-Ptr input-loc (payload pointer)
  --   4. store-at-slot payload-slot : mem[payload-slot] := SV-Ptr input-loc
  --   5. lea-slot result-slot : Output := SV-Ptr result-loc
  --
  -- After all 5 steps:
  --   mem[result-slot] = SV-Tag tag
  --   mem[payload-slot] = SV-Ptr input-loc
  --   regs[Output] = SV-Ptr result-loc
  --   regs[Input1] = SV-Ptr input-loc (unchanged)
  --   halted = false (unchanged from precondition)
  --
  -- Note: the s-final shape on the caller side ONLY models the payload
  -- write and the Output register update (matching the pre-Plan-0.13.1
  -- s-final construction used by run-inl/run-inr). The tag write at
  -- result-slot is folded into this postulate's soundness debt: the
  -- proven equation is exec-trace = s-final-as-constructed, but
  -- s-final-as-constructed has the original (pre-tag) memory at
  -- result-slot, not SV-Tag tag. Migrating callers to a tag-aware
  -- s-final is the next step (requires a `validityWF-write-sv-at-frontier`
  -- sibling lemma in ClosureWellFormed).
  inl-inr-trace-state-correct : ∀ (tag : ℕ) (payload-slot result-slot : ℕ)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-loc : ValueLocation FS) (result-loc : ValueLocation FS)
    (s-final : LocState FS) →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    result-loc ≡ AtStack (current-frame alloc) result-slot →
    s-final ≡ record (write-loc s (AtStack (current-frame alloc) payload-slot) input-loc)
                { regs = writeReg (regs (write-loc s (AtStack (current-frame alloc) payload-slot) input-loc)) Output (SV-Ptr result-loc) } →
    halted s ≡ false →
    proj₁ (exec-trace
            (instr-load-tag-lit tag ∷
             store-at-slot result-slot ∷
             mov-to-output ∷
             store-at-slot payload-slot ∷
             lea-slot result-slot ∷ []) s alloc) ≡ s-final
  inl-inr-trace-state-correct _ _ _ _ _ _ _ _ _ _ _ _ = SMP.!!

  -- OCP-0003: fold-trace-state-correct removed (fold/unfold replaced by In/Cata/Out/Ana/Hylo)

  ------------------------------------------------------------------------
  -- Case Dispatch Trace Correctness Postulate
  --
  -- The case dispatch trace is: load-indirect-suc ∷ mov-to-input ∷ dispatch-trace
  --
  -- After execution:
  --   1. load-indirect-suc: Output := *(sucLoc Input1) = payload-loc
  --   2. mov-to-input: Input1 := Output = payload-loc
  --   3. Execute dispatch-trace with Input1 = payload-loc
  --
  -- Key insight (Output-independence):
  --   After steps 1-2, the state differs from s-setup only in Output:
  --   - Both have Input1 = payload-loc
  --   - Both have same stackMem, heapMem, halted
  --   - Actual state has Output = payload-loc
  --   - s-setup has Output = original Output
  --
  --   IR dispatch traces are Output-independent:
  --   - They read from Input1 to get input value
  --   - They may read from memory (stackMem, heapMem)
  --   - They write their result to Output (overwriting initial value)
  --   - They never READ the initial Output value
  --
  -- Therefore: exec-trace dispatch-trace s₂ alloc ≡ exec-trace dispatch-trace s-setup alloc
  --
  -- Justification (why this is PROVABLE):
  --   1. Define TraceOutputIndependent predicate
  --   2. Prove IR dispatch traces satisfy this predicate
  --   3. Prove exec-trace is insensitive to Output for such traces
  ------------------------------------------------------------------------
  -- Plan 0.13.2 StoredValue restate: input-loc threaded via SV-Ptr;
  -- payload reads now produce SV-Ptr payload-loc.
  postulate
    case-dispatch-output-independent : ∀ (dispatch-trace : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS})
      (input-loc payload-loc : ValueLocation FS)
      (s-setup : LocState FS) (s-final : LocState FS) →
      readReg (regs s) Input1 ≡ SV-Ptr input-loc →
      readLoc s (sucLoc input-loc) ≡ just (SV-Ptr payload-loc) →
      s-setup ≡ record s { regs = writeReg (regs s) Input1 (SV-Ptr payload-loc) } →
      proj₁ (exec-trace dispatch-trace s-setup alloc) ≡ s-final →
      halted s ≡ false →
      proj₁ (exec-trace (load-indirect-suc ∷ mov-to-input ∷ dispatch-trace) s alloc) ≡ s-final

  -- case trace correctness - delegated to postulate (Plan 0.13.2 restated)
  case-trace-state-correct : ∀ (dispatch-trace : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-loc payload-loc : ValueLocation FS)
    (s-setup : LocState FS) (s-final : LocState FS) →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    readLoc s (sucLoc input-loc) ≡ just (SV-Ptr payload-loc) →
    s-setup ≡ record s { regs = writeReg (regs s) Input1 (SV-Ptr payload-loc) } →
    proj₁ (exec-trace dispatch-trace s-setup alloc) ≡ s-final →
    halted s ≡ false →
    proj₁ (exec-trace (load-indirect-suc ∷ mov-to-input ∷ dispatch-trace) s alloc) ≡ s-final
  case-trace-state-correct = case-dispatch-output-independent

  -- OCP-0003: sem-fold-injective removed (fold/unfold replaced by recursion schemes)

  -- Helper: sem-inl is injective
  sem-inl-injective : ∀ {A B} {a b : ⟦ A ⟧} → sem-inl {A} {B} a ≡ sem-inl {A} {B} b → a ≡ b
  sem-inl-injective refl = refl

  -- Helper: sem-inr is injective
  sem-inr-injective : ∀ {A B} {a b : ⟦ B ⟧} → sem-inr {A} {B} a ≡ sem-inr {A} {B} b → a ≡ b
  sem-inr-injective refl = refl

  ------------------------------------------------------------------------
  -- Initial: absurd elimination (input is Void, so never executed)
  ------------------------------------------------------------------------

  run-initial : ∀ {m A}
    (x : ⟦ Void ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mOut ] IRResultAWF mOut (initial {A}) x s alloc
  run-initial () _ _ _ _ _ _ _  -- x : ⟦ Void ⟧ = ⊥, so pattern match is absurd

  -- OCP-0003: run-unfold removed (replaced by Out handler for ν-types)

  ------------------------------------------------------------------------
  -- Inl: inject left into sum type
  --
  -- Creates a sum value (inl x) by:
  -- 1. Allocating type-slots (A + B) slots at frontier
  -- 2. Writing input-loc (payload pointer) to sucLoc sum-loc
  -- 3. Returning sum-loc
  --
  -- Memory layout: sum-loc stores tag (implicit), sucLoc sum-loc stores payload ptr
  ------------------------------------------------------------------------

  -- Helper: type-slots (A + B) > 0
  sum-slots-pos : ∀ {A B} → 0 < type-slots (A + B)
  sum-slots-pos {A} {B} = s≤s z≤n

  run-inl : ∀ {A B} (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (inl {A} {B} m) x s alloc  -- Output mode is m (the inl's AllocMode)

  -- Stack mode: reference-based (tag + pointer), same as Heap mode
  run-inl {A} {B} mIn Stack x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s-final
        ; final-alloc = alloc₁
        ; trace = inl-trace
        ; trace-correct = inl-inr-trace-state-correct 0 (suc (next-slot alloc)) (next-slot alloc) s alloc input-loc sum-loc s-final rdi-eq refl refl not-halted
        ; result-place = at-loc sum-loc inl-valid-wf-final sum-before rax-eq inl-reclaim-preserves-validity inl-reclaim-preserves-result
        ; not-halted = not-halted
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))))
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF inl-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-monotone-inl
        ; max-slot-written = next-slot alloc +ℕ sum-slots
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (inl {A} {B} Stack)
        ; max-slot-usage-bound = reclaim-size-bound-inl
        ; slot-stays-in-budget = reclaim-size-bound-inl
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = ≤-refl , n≤1+n (next-slot alloc) , tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = <-trans (n<1+n (next-slot alloc)) (suc<+2 (next-slot alloc)) ,
                               suc<+2 (next-slot alloc) , tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (inl {A} {B} Stack)
        ; scratch-bounded = m≤m+n (next-slot alloc +ℕ 2) 2
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- Stack mode: sum-slots = stack-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = AtStack (current-frame alloc) (next-slot alloc)

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
                }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) Output (SV-Ptr sum-loc) }

      -- Stack mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0

      -- sucLoc sum-loc is BeforeFrontier after allocation
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input1 validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inl x (Stack mode = reference-based)
      inl-valid-wf-final : ValidAtWF Stack alloc₁ (sem-inl {A} {B} x) sum-loc s-final
      inl-valid-wf-final = valid-inl-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) Output ≡ SV-Ptr sum-loc
      rax-eq = writeReg-same (regs s₁) Output (SV-Ptr sum-loc)

      slot-monotone-inl : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inl = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inl : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inl loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-at-suc-frontier-preserves-before s alloc loc input-loc bf)

      -- Note: fits parameter removed in Phase 3
      inl-reclaim-preserves-result :
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots  }) sum-loc
      inl-reclaim-preserves-result = at-frontier-becomes-before alloc sum-slots sum-slots>0

      inl-reclaim-preserves-validity :
        ValidAtWF Stack (record alloc { next-slot = next-slot alloc +ℕ sum-slots  })
                  (sem-inl {A} {B} x) sum-loc s-final
      inl-reclaim-preserves-validity = inl-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inl Stack)
      reclaim-size-bound-inl : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inl {A} {B} Stack)
      reclaim-size-bound-inl = ≤-refl

      -- Inl trace: store payload pointer to sucLoc sum-loc, then set Output to sum address
      -- 1. mov-to-output: Output := Input1 (payload pointer)
      -- Plan 0.13.1 tag-aware 5-instruction trace (matches ir-to-trace):
      -- 1. instr-load-tag-lit 0: Output := SV-Tag 0
      -- 2. store-at-slot sum-slot: slot[sum] := SV-Tag 0
      -- 3. mov-to-output: Output := Input1 (payload pointer)
      -- 4. store-at-slot (suc sum-slot): slot[sum+1] := payload pointer
      -- 5. lea-slot sum-slot: Output := &slot[sum] (sum address)
      sum-slot = next-slot alloc
      inl-trace : AbstractTrace
      inl-trace = instr-load-tag-lit 0 ∷
                  store-at-slot sum-slot ∷
                  mov-to-output ∷
                  store-at-slot (suc sum-slot) ∷
                  lea-slot sum-slot ∷ []

      -- inl-frontier-stable removed: with the 5-instruction tag-aware trace,
      -- the frontier slot is written (SV-Tag 0) and no longer preserved as
      -- the input pointer. `frontier-slot-stable` now returns the ⊤ branch.

  -- Heap mode: boxed representation (tag + pointer)
  run-inl {A} {B} mIn Heap x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s-final
        ; final-alloc = alloc₁
        ; trace = inl-trace
        ; trace-correct = inl-inr-trace-state-correct 0 (suc (next-slot alloc)) (next-slot alloc) s alloc input-loc sum-loc s-final rdi-eq refl refl not-halted
        ; result-place = at-loc sum-loc inl-valid-wf-final sum-before rax-eq inl-reclaim-preserves-validity inl-reclaim-preserves-result
        ; not-halted = not-halted
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))))
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF inl-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-monotone-inl
        ; max-slot-written = next-slot alloc +ℕ sum-slots
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (inl {A} {B} Heap)
        ; max-slot-usage-bound = reclaim-size-bound-inl
        ; slot-stays-in-budget = reclaim-size-bound-inl
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = ≤-refl , n≤1+n (next-slot alloc) , tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = <-trans (n<1+n (next-slot alloc)) (suc<+2 (next-slot alloc)) ,
                               suc<+2 (next-slot alloc) , tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (inl {A} {B} Heap)
        ; scratch-bounded = m≤m+n (next-slot alloc +ℕ 2) 2
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- Heap mode: sum-slots = heap-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = AtStack (current-frame alloc) (next-slot alloc)

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
                }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) Output (SV-Ptr sum-loc) }

      -- Heap mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0

      -- sucLoc sum-loc is BeforeFrontier after allocation
      -- Need: suc (next-slot alloc) < next-slot alloc +ℕ 2
      -- Uses suc<+2 from DispatcherArithmeticLemma
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input1 validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inl x (Heap mode = boxed)
      -- valid-inl-wf needs: payload-ptr, payload-before, sucLoc-before, payload-valid
      inl-valid-wf-final : ValidAtWF Heap alloc₁ (sem-inl {A} {B} x) sum-loc s-final
      inl-valid-wf-final = valid-inl-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) Output ≡ SV-Ptr sum-loc
      rax-eq = writeReg-same (regs s₁) Output (SV-Ptr sum-loc)

      slot-monotone-inl : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inl = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inl : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inl loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-at-suc-frontier-preserves-before s alloc loc input-loc bf)

      -- Note: fits parameter removed in Phase 3
      inl-reclaim-preserves-result :
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots  }) sum-loc
      inl-reclaim-preserves-result = at-frontier-becomes-before alloc sum-slots sum-slots>0

      inl-reclaim-preserves-validity :
        ValidAtWF Heap (record alloc { next-slot = next-slot alloc +ℕ sum-slots  })
                  (sem-inl {A} {B} x) sum-loc s-final
      inl-reclaim-preserves-validity = inl-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inl Heap)
      reclaim-size-bound-inl : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inl {A} {B} Heap)
      reclaim-size-bound-inl = ≤-refl

      -- Inl trace (Heap mode): same 5-instr tag-aware trace as Stack mode.
      sum-slot = next-slot alloc
      inl-trace : AbstractTrace
      inl-trace = instr-load-tag-lit 0 ∷
                  store-at-slot sum-slot ∷
                  mov-to-output ∷
                  store-at-slot (suc sum-slot) ∷
                  lea-slot sum-slot ∷ []
      -- inl-frontier-stable removed (frontier slot is now written, not preserved).

  ------------------------------------------------------------------------
  -- Inr: inject right into sum type
  --
  -- Creates a sum value (inr x) by:
  -- 1. Allocating type-slots (A + B) slots at frontier
  -- 2. Writing input-loc (payload pointer) to sucLoc sum-loc
  -- 3. Returning sum-loc
  --
  -- Memory layout: sum-loc stores tag (implicit), sucLoc sum-loc stores payload ptr
  -- Same pattern as run-inl, but produces inr instead of inl
  ------------------------------------------------------------------------

  run-inr : ∀ {A B} (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (inr {A} {B} m) x s alloc  -- Output mode is m (the inr's AllocMode)

  -- Stack mode: reference-based (tag + pointer), same as Heap mode
  run-inr {A} {B} mIn Stack x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s-final
        ; final-alloc = alloc₁
        ; trace = inr-trace
        ; trace-correct = inl-inr-trace-state-correct 1 (suc (next-slot alloc)) (next-slot alloc) s alloc input-loc sum-loc s-final rdi-eq refl refl not-halted
        ; result-place = at-loc sum-loc inr-valid-wf-final sum-before rax-eq inr-reclaim-preserves-validity inr-reclaim-preserves-result
        ; not-halted = not-halted
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))))
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF inr-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-monotone-inr
        ; max-slot-written = next-slot alloc +ℕ sum-slots
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (inr {A} {B} Stack)
        ; max-slot-usage-bound = reclaim-size-bound-inr
        ; slot-stays-in-budget = reclaim-size-bound-inr
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = ≤-refl , n≤1+n (next-slot alloc) , tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = <-trans (n<1+n (next-slot alloc)) (suc<+2 (next-slot alloc)) ,
                               suc<+2 (next-slot alloc) , tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (inr {A} {B} Stack)
        ; scratch-bounded = m≤m+n (next-slot alloc +ℕ 2) 2
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- Stack mode: sum-slots = stack-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = AtStack (current-frame alloc) (next-slot alloc)

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
                }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) Output (SV-Ptr sum-loc) }

      -- Stack mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0

      -- sucLoc sum-loc is BeforeFrontier after allocation
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input1 validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inr x (Stack mode = reference-based)
      inr-valid-wf-final : ValidAtWF Stack alloc₁ (sem-inr {A} {B} x) sum-loc s-final
      inr-valid-wf-final = valid-inr-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) Output ≡ SV-Ptr sum-loc
      rax-eq = writeReg-same (regs s₁) Output (SV-Ptr sum-loc)

      slot-monotone-inr : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inr = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inr : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inr loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-at-suc-frontier-preserves-before s alloc loc input-loc bf)

      -- Note: fits parameter removed in Phase 3
      inr-reclaim-preserves-result :
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots  }) sum-loc
      inr-reclaim-preserves-result = at-frontier-becomes-before alloc sum-slots sum-slots>0

      inr-reclaim-preserves-validity :
        ValidAtWF Stack (record alloc { next-slot = next-slot alloc +ℕ sum-slots  })
                  (sem-inr {A} {B} x) sum-loc s-final
      inr-reclaim-preserves-validity = inr-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inr Stack)
      reclaim-size-bound-inr : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inr {A} {B} Stack)
      reclaim-size-bound-inr = ≤-refl

      -- Inr trace (Stack mode): 5-instr tag-aware, tag = 1.
      sum-slot = next-slot alloc
      inr-trace : AbstractTrace
      inr-trace = instr-load-tag-lit 1 ∷
                  store-at-slot sum-slot ∷
                  mov-to-output ∷
                  store-at-slot (suc sum-slot) ∷
                  lea-slot sum-slot ∷ []
      -- inr-frontier-stable removed (frontier slot now written).

  -- Heap mode: boxed representation (tag + pointer)
  run-inr {A} {B} mIn Heap x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s-final
        ; final-alloc = alloc₁
        ; trace = inr-trace
        ; trace-correct = inl-inr-trace-state-correct 1 (suc (next-slot alloc)) (next-slot alloc) s alloc input-loc sum-loc s-final rdi-eq refl refl not-halted
        ; result-place = at-loc sum-loc inr-valid-wf-final sum-before rax-eq inr-reclaim-preserves-validity inr-reclaim-preserves-result
        ; not-halted = not-halted
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))))
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF inr-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-monotone-inr
        ; max-slot-written = next-slot alloc +ℕ sum-slots
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (inr {A} {B} Heap)
        ; max-slot-usage-bound = reclaim-size-bound-inr
        ; slot-stays-in-budget = reclaim-size-bound-inr
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = ≤-refl , n≤1+n (next-slot alloc) , tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = <-trans (n<1+n (next-slot alloc)) (suc<+2 (next-slot alloc)) ,
                               suc<+2 (next-slot alloc) , tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (inr {A} {B} Heap)
        ; scratch-bounded = m≤m+n (next-slot alloc +ℕ 2) 2
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- Heap mode: sum-slots = heap-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = AtStack (current-frame alloc) (next-slot alloc)

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
                }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) Output (SV-Ptr sum-loc) }

      -- Heap mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0

      -- sucLoc sum-loc is BeforeFrontier after allocation
      -- Uses suc<+2 from DispatcherArithmeticLemma
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just (SV-Ptr input-loc)
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input1 validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inr x (Heap mode = boxed)
      -- valid-inr-wf needs: payload-ptr, payload-before, sucLoc-before, payload-valid
      inr-valid-wf-final : ValidAtWF Heap alloc₁ (sem-inr {A} {B} x) sum-loc s-final
      inr-valid-wf-final = valid-inr-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) Output ≡ SV-Ptr sum-loc
      rax-eq = writeReg-same (regs s₁) Output (SV-Ptr sum-loc)

      slot-monotone-inr : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inr = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inr : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inr loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-at-suc-frontier-preserves-before s alloc loc input-loc bf)

      -- Note: fits parameter removed in Phase 3
      inr-reclaim-preserves-result :
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots  }) sum-loc
      inr-reclaim-preserves-result = at-frontier-becomes-before alloc sum-slots sum-slots>0

      inr-reclaim-preserves-validity :
        ValidAtWF Heap (record alloc { next-slot = next-slot alloc +ℕ sum-slots  })
                  (sem-inr {A} {B} x) sum-loc s-final
      inr-reclaim-preserves-validity = inr-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inr Heap)
      reclaim-size-bound-inr : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inr {A} {B} Heap)
      reclaim-size-bound-inr = ≤-refl

      -- Inr trace (Heap mode): 5-instr tag-aware, tag = 1.
      sum-slot = next-slot alloc
      inr-trace : AbstractTrace
      inr-trace = instr-load-tag-lit 1 ∷
                  store-at-slot sum-slot ∷
                  mov-to-output ∷
                  store-at-slot (suc sum-slot) ∷
                  lea-slot sum-slot ∷ []
      -- inr-frontier-stable removed (frontier slot now written).

  -- OCP-0003: run-fold removed (replaced by In handler for μ-types)

  ------------------------------------------------------------------------
  -- Case: dispatch on sum type
  --
  -- For a sum value x : ⟦ A + B ⟧ (either inl a or inr b):
  -- 1. Read payload pointer from sucLoc input-loc
  -- 2. Load payload into Input1
  -- 3. Dispatch to f (for inl) or g (for inr) via RecDispatcherWF
  --
  -- Branches are mutually exclusive, so capacity is shared.
  -- ir-size (case f g) = suc (ir-size f + ir-size g)
  ------------------------------------------------------------------------

  run-case : ∀ {m A B C} (f : IR A C) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (case f g)))
    (x : ⟦ A + B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →  -- Reference-based: any mode works
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mOut ] IRResultAWF mOut (case f g) x s alloc

  -- Case for inl: dispatch to f
  run-case {m} {A} {B} {C} f g rec-wf (inj₁ a) input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mF , record
      { base = record
        { final-state = IRResultAWF.final-state result-f
        ; final-alloc = IRResultAWF.final-alloc result-f
        ; trace = case-inl-trace
        ; trace-correct = case-trace-state-correct f-trace s alloc input-loc payload-loc s-setup (IRResultAWF.final-state result-f)
                            rdi-eq
                            (InlValidWF.payload-ptr inl-decomp)
                            refl
                            (IRResultAWF.trace-correct result-f) not-halted
        ; result-place = IRResultAWF.result-place result-f
        ; not-halted = IRResultAWF.not-halted result-f
        ; frame-preserved = IRResultAWF.frame-preserved result-f
        ; trace-twf = SMP.!!  -- TODO: load-indirect-suc + result-f.trace-twf chained
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF case-inl-trace
        }
      ; stack-inv = record
        { slot-monotone = IRResultAWF.slot-monotone result-f
        ; max-slot-written = IRResultAWF.max-slot-written result-f
        ; max-slot-geq-final = IRResultAWF.max-slot-geq-final result-f
        ; stack-budget = IRResultAWF.stack-budget result-f
        ; max-slot-usage-bound = IRResultAWF.max-slot-usage-bound result-f
        ; slot-stays-in-budget = IRResultAWF.slot-stays-in-budget result-f
        ; frontier-slot-stable = case-frontier-stable
        ; trace-writes-above = IRResultAWF.trace-writes-above result-f
        ; trace-slot-reads-above = IRResultAWF.trace-slot-reads-above result-f
        ; trace-writes-below = IRResultAWF.trace-writes-below result-f
        ; trace-slot-reads-below = IRResultAWF.trace-slot-reads-below result-f
        ; scratch-budget = IRResultAWF.scratch-budget result-f
        ; scratch-bounded = IRResultAWF.scratch-bounded result-f
        }
      ; heap-inv = record
        { heap-monotone = IRResultAWF.heap-monotone result-f
        ; heap-budget = IRResultAWF.heap-budget result-f
        ; max-heap-ref-written = IRResultAWF.max-heap-ref-written result-f
        ; max-heap-ref-geq-final = IRResultAWF.max-heap-ref-geq-final result-f
        ; max-heap-usage-bound = IRResultAWF.max-heap-usage-bound result-f
        ; trace-no-heap-writes = IRResultAWF.trace-no-heap-writes result-f
        }
      }
    where
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-case = ir-stack-requirement (case f g)

      -- Decompose sum validity
      inl-decomp = decomposeInlWF input-valid-wf
      a' = InlValidWF.a inl-decomp
      mA = InlValidWF.mA inl-decomp
      payload-loc = InlValidWF.payload-loc inl-decomp
      payload-before = InlValidWF.payload-before inl-decomp
      payload-valid-wf' = InlValidWF.payload-valid inl-decomp

      -- v-is-inl : inl a ≡ inl a', so a ≡ a' by sem-inl-injective
      a-eq : a' ≡ a
      a-eq = sem-inl-injective (sym (InlValidWF.v-is-inl inl-decomp))

      -- Transport payload validity from a' to a
      payload-valid-wf : ValidAtWF mA alloc a payload-loc s
      payload-valid-wf = subst (λ x → ValidAtWF mA alloc x payload-loc s) a-eq payload-valid-wf'

      -- Capacity bound for f
      -- case-stack-req: ir-stack-requirement (case f g) = rf + rg
      -- So rf ≤ req-case, hence slot + rf ≤ slot + req-case
      cap-f-bound : next-slot alloc +ℕ rf ≤ next-slot alloc +ℕ req-case
      cap-f-bound = +-monoʳ-≤ (next-slot alloc) (m≤m+n rf rg)

      -- Put payload-loc in Input1 for dispatch
      s-setup = record s { regs = writeReg (regs s) Input1 (SV-Ptr payload-loc) }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) Input1 ≡ SV-Ptr payload-loc
      rdi-payload = writeReg-same (regs s) Input1 (SV-Ptr payload-loc)

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      payload-valid-wf-setup : ValidAtWF mA alloc a payload-loc s-setup
      payload-valid-wf-setup = validityWF-mem-only a payload-loc s s-setup refl refl payload-valid-wf

      -- Dispatch to f via recursive dispatch
      -- Note: cap-f argument removed in Phase 3
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f a s-setup alloc
      f-exec-result = rec-wf mA f (case-f-smaller f g) a payload-loc s-setup alloc
                        payload-valid-wf-setup payload-before not-halted-setup rdi-payload
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result

      -- Case (inl branch) trace:
      -- 1. Load payload pointer from sucLoc input-loc into Output
      -- 2. mov-to-input to set Input1 := payload-loc
      -- 3. Execute f's trace
      -- Note: The actual Dispatcher sets Input1 directly, we approximate with load + mov
      f-trace = IRResultAWF.trace result-f
      case-inl-trace : AbstractTrace
      case-inl-trace = load-indirect-suc ∷  -- Output := *(Input1+1) = payload-loc
                       mov-to-input ∷       -- Input1 := Output = payload-loc
                       f-trace

      -- Frontier slot stability for case (inl branch)
      -- Return uncertain (inj₂ (inj₂ tt)) since f may allocate at the frontier slot.
      -- This is safe: compose handles uncertainty correctly by propagating it.
      case-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
        readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      case-frontier-stable _ _ _ _ _ = inj₂ (inj₂ tt)

  -- Case for inr: dispatch to g
  run-case {m} {A} {B} {C} f g rec-wf (inj₂ b) input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mG , record
      { base = record
        { final-state = IRResultAWF.final-state result-g
        ; final-alloc = IRResultAWF.final-alloc result-g
        ; trace = case-inr-trace
        ; trace-correct = case-trace-state-correct g-trace s alloc input-loc payload-loc s-setup (IRResultAWF.final-state result-g)
                            rdi-eq
                            (InrValidWF.payload-ptr inr-decomp)
                            refl
                            (IRResultAWF.trace-correct result-g) not-halted
        ; result-place = IRResultAWF.result-place result-g
        ; not-halted = IRResultAWF.not-halted result-g
        ; frame-preserved = IRResultAWF.frame-preserved result-g
        ; trace-twf = SMP.!!  -- TODO: load-indirect-suc + result-g.trace-twf chained
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF case-inr-trace
        }
      ; stack-inv = record
        { slot-monotone = IRResultAWF.slot-monotone result-g
        ; max-slot-written = IRResultAWF.max-slot-written result-g
        ; max-slot-geq-final = IRResultAWF.max-slot-geq-final result-g
        ; stack-budget = IRResultAWF.stack-budget result-g
        ; max-slot-usage-bound = IRResultAWF.max-slot-usage-bound result-g
        ; slot-stays-in-budget = IRResultAWF.slot-stays-in-budget result-g
        ; frontier-slot-stable = case-frontier-stable
        ; trace-writes-above = IRResultAWF.trace-writes-above result-g
        ; trace-slot-reads-above = IRResultAWF.trace-slot-reads-above result-g
        ; trace-writes-below = IRResultAWF.trace-writes-below result-g
        ; trace-slot-reads-below = IRResultAWF.trace-slot-reads-below result-g
        ; scratch-budget = IRResultAWF.scratch-budget result-g
        ; scratch-bounded = IRResultAWF.scratch-bounded result-g
        }
      ; heap-inv = record
        { heap-monotone = IRResultAWF.heap-monotone result-g
        ; heap-budget = IRResultAWF.heap-budget result-g
        ; max-heap-ref-written = IRResultAWF.max-heap-ref-written result-g
        ; max-heap-ref-geq-final = IRResultAWF.max-heap-ref-geq-final result-g
        ; max-heap-usage-bound = IRResultAWF.max-heap-usage-bound result-g
        ; trace-no-heap-writes = IRResultAWF.trace-no-heap-writes result-g
        }
      }
    where
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-case = ir-stack-requirement (case f g)

      -- Decompose sum validity
      inr-decomp = decomposeInrWF input-valid-wf
      b' = InrValidWF.b inr-decomp
      mB = InrValidWF.mB inr-decomp
      payload-loc = InrValidWF.payload-loc inr-decomp
      payload-before = InrValidWF.payload-before inr-decomp
      payload-valid-wf' = InrValidWF.payload-valid inr-decomp

      -- v-is-inr : inr b ≡ inr b', so b ≡ b' by sem-inr-injective
      b-eq : b' ≡ b
      b-eq = sem-inr-injective (sym (InrValidWF.v-is-inr inr-decomp))

      -- Transport payload validity from b' to b
      payload-valid-wf : ValidAtWF mB alloc b payload-loc s
      payload-valid-wf = subst (λ x → ValidAtWF mB alloc x payload-loc s) b-eq payload-valid-wf'

      -- Capacity bound for g
      -- case-stack-req: ir-stack-requirement (case f g) = rf + rg
      -- So rg ≤ req-case, hence slot + rg ≤ slot + req-case
      cap-g-bound : next-slot alloc +ℕ rg ≤ next-slot alloc +ℕ req-case
      cap-g-bound = +-monoʳ-≤ (next-slot alloc) (m≤n+m rg rf)

      -- Put payload-loc in Input1 for dispatch
      s-setup = record s { regs = writeReg (regs s) Input1 (SV-Ptr payload-loc) }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) Input1 ≡ SV-Ptr payload-loc
      rdi-payload = writeReg-same (regs s) Input1 (SV-Ptr payload-loc)

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      payload-valid-wf-setup : ValidAtWF mB alloc b payload-loc s-setup
      payload-valid-wf-setup = validityWF-mem-only b payload-loc s s-setup refl refl payload-valid-wf

      -- Dispatch to g via recursive dispatch
      -- Note: cap-g argument removed in Phase 3
      g-exec-result : ∃[ mOut ] IRResultAWF mOut g b s-setup alloc
      g-exec-result = rec-wf mB g (case-g-smaller f g) b payload-loc s-setup alloc
                        payload-valid-wf-setup payload-before not-halted-setup rdi-payload
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result

      -- Case (inr branch) trace:
      -- 1. Load payload pointer from sucLoc input-loc into Output
      -- 2. mov-to-input to set Input1 := payload-loc
      -- 3. Execute g's trace
      g-trace = IRResultAWF.trace result-g
      case-inr-trace : AbstractTrace
      case-inr-trace = load-indirect-suc ∷  -- Output := *(Input1+1) = payload-loc
                       mov-to-input ∷       -- Input1 := Output = payload-loc
                       g-trace

      -- Frontier slot stability for case (inr branch)
      -- Return uncertain (inj₂ (inj₂ tt)) since g may allocate at the frontier slot.
      case-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
        readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      case-frontier-stable _ _ _ _ _ = inj₂ (inj₂ tt)

  ------------------------------------------------------------------------
  ------------------------------------------------------------------------
  -- OCP-0003: Recursion Scheme Handlers
  --
  -- These handlers implement machine-level code generation for the
  -- recursion scheme constructors: In, Cata, Out, Ana, Hylo.
  --
  -- The semantic correctness is established in:
  --   - Once/CCC/IR/Laws.agda (evaluation laws)
  --   - Once/Category/Laws.agda (categorical laws)
  --
  -- Implementation strategy:
  --   - In/out-μ: trivial pass-through (μ-type is representationally
  --               identical to F(μ-type) by Lambek's Lemma)
  --   - Out/in-ν: trivial pass-through (ν-type is representationally
  --               identical to F(ν-type) by dual Lambek's Lemma)
  --   - Cata: iterative consumption of μ-type (RecCoreWF)
  --   - Ana: lazy/demand-driven production of ν-type (thunk)
  --   - Hylo: fused cata ∘ ana without intermediate allocation
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Semantic Correctness for Isomorphism Operations
  --
  -- Uses targeted Lambek validity lemmas instead of general postulate.
  -- See LambekValidity.agda for documentation and justification.
  ------------------------------------------------------------------------
  open LV.LambekValidityImpl {FS} program-bound
    using (In-trace-valid; out-μ-trace-valid; in-ν-trace-valid; Out-trace-valid)

  ------------------------------------------------------------------------
  -- In: wrap functor layer into μ-type
  --
  -- By Lambek's Lemma, In : F(μF) → μF is an isomorphism, so the
  -- runtime representation of F(μF) IS the representation of μF.
  -- This is a trivial identity operation at the machine level.
  --
  -- The only work: if AllocMode requests allocation, store at slot.
  -- For Stack mode, we store input at frontier slot and return pointer.
  -- For Heap mode (currently same as Stack in reference model).
  ------------------------------------------------------------------------

  run-In : ∀ {F} (wf : WellFormedF F) (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (In {F} wf m) x s alloc
  run-In {F} wf mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s'
        ; final-alloc = alloc'
        ; trace = in-trace
        ; trace-correct = refl  -- s' DEFINED by trace
        ; result-place = at-loc result-loc result-valid result-bf rax-eq result-valid result-bf
        ; not-halted = not-halted'
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF in-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-mono
        ; max-slot-written = next-slot alloc'
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (In {F} wf m)
        ; max-slot-usage-bound = reclaim-bound
        ; slot-stays-in-budget = reclaim-bound
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = trace-wa
        ; trace-slot-reads-above = tt
        ; trace-writes-below = trace-wb
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (In {F} wf m)
        ; scratch-bounded = m≤m+n (suc (next-slot alloc)) 1
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- ir-stack-requirement (In _ _) = 1
      result-slot = next-slot alloc
      result-loc = AtStack (current-frame alloc) result-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = suc (next-slot alloc) }

      -- suc n ≤ n + 1: ir-stack-requirement (In wf m) ≡ 1 definitionally
      -- +-comm 1 n : 1 + n ≡ n + 1 where 1 + n = suc n
      -- So we get: suc n ≡ n + 1
      n = next-slot alloc
      suc-n≡n+1 : suc n ≡ n +ℕ 1
      suc-n≡n+1 = +-comm 1 n

      reclaim-bound : suc n ≤ n +ℕ ir-stack-requirement (In {F} wf m)
      reclaim-bound = ≤-reflexive suc-n≡n+1

      -- Trace: store input at slot, return slot address
      -- 1. mov-to-output: Output := Input1
      -- 2. store-at-slot: slot[n] := Output
      -- 3. lea-slot: Output := &slot[n] (result location)
      in-trace : AbstractTrace
      in-trace = mov-to-output ∷ store-at-slot result-slot ∷ lea-slot result-slot ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace in-trace s alloc)

      slot-mono : next-slot alloc ≤ next-slot alloc'
      slot-mono = n≤1+n (next-slot alloc)

      result-bf : BeforeFrontier alloc' result-loc
      result-bf = stack-before refl (n<1+n (next-slot alloc))

      -- Result validity: In semantically is identity, so input validity transfers
      -- The semantic eval (In wf m) x = InS x, which is representationally same as x
      result-valid : ValidAtWF m alloc' (eval (In wf m) x) result-loc s'
      result-valid = In-trace-valid wf m x

      rax-eq : readReg (regs s') Output ≡ SV-Ptr result-loc
      rax-eq = rec-scheme-output-is-slot result-slot s alloc not-halted

      not-halted' : halted s' ≡ false
      not-halted' = rec-scheme-preserves-halted-3 result-slot s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved (AtStack f k) (stack-before refl k<n) =
        rec-scheme-preserves-slot-below-3 result-slot k s alloc not-halted k<n
      mem-preserved (AtStack f k) (stack-ancestor cf≺f _) =
        rec-scheme-preserves-ancestor-3 result-slot s alloc f k not-halted (λ eq → ≺⇒≢ cf≺f (sym eq))
      mem-preserved (AtDynamic hl) (heap-before _) =
        rec-scheme-preserves-heap-3 result-slot s alloc hl not-halted

      trace-wa : SMP.TraceWritesAbove (next-slot alloc) in-trace
      trace-wa = ≤-refl , tt

      trace-wb : SMP.TraceWritesBelow (suc (next-slot alloc)) in-trace
      trace-wb = n<1+n (next-slot alloc) , tt

      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable s'' input-loc' _ _ _ = inj₂ (inj₂ tt)

  ------------------------------------------------------------------------
  -- out-μ: destruct μ-type to get functor layer (Lambek inverse of In)
  --
  -- By Lambek's Lemma, this is the inverse of In. At runtime, μF and
  -- F(μF) have identical representation, so this is identity.
  ------------------------------------------------------------------------

  run-out-μ : ∀ {F} (wf : WellFormedF F) (mIn : AllocMode)
    (x : ⟦ μ-type F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF Heap (out-μ {F} wf) x s alloc
  run-out-μ {F} wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s'
        ; final-alloc = alloc
        ; trace = out-μ-trace
        ; trace-correct = refl  -- s' DEFINED by trace
        ; result-place = at-loc input-loc result-valid input-before rax-eq result-valid input-before
        ; not-halted = not-halted'
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt twf-[]
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF out-μ-trace
        }
      ; stack-inv = record
        { slot-monotone = ≤-refl
        ; max-slot-written = next-slot alloc
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (out-μ {F} wf)
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (out-μ {F} wf)
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- ir-stack-requirement (out-μ _) = 0, so no allocation
      -- Trace: just pass through input to output
      out-μ-trace : AbstractTrace
      out-μ-trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace out-μ-trace s alloc)

      -- Result validity: out-μ extracts F(μF) from μF, representationally same
      result-valid : ValidAtWF Heap alloc (eval (out-μ wf) x) input-loc s'
      result-valid = out-μ-trace-valid wf x

      -- mov-to-output sets Output := Input1 = SV-Ptr input-loc
      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
      rax-eq = trans (passthrough-output-is-input s alloc not-halted) rdi-eq

      -- mov-to-output preserves halted
      not-halted' : halted s' ≡ false
      not-halted' = passthrough-preserves-halted s alloc not-halted

      -- mov-to-output doesn't write memory
      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc bf = passthrough-mem-preserved s alloc loc not-halted

      -- IR doesn't allocate, return inj₁ refl
      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Out: observe ν-type to extract functor layer
  --
  -- By dual Lambek's Lemma, Out : νF → F(νF) is an isomorphism.
  -- At runtime, νF and F(νF) have identical representation.
  -- This is a trivial identity operation.
  ------------------------------------------------------------------------

  run-Out : ∀ {F} (wf : WellFormedF F) (mIn : AllocMode)
    (x : ⟦ ν-type F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF Heap (Out {F} wf) x s alloc
  run-Out {F} wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s'
        ; final-alloc = alloc
        ; trace = out-trace
        ; trace-correct = refl  -- s' DEFINED by trace
        ; result-place = at-loc input-loc result-valid input-before rax-eq result-valid input-before
        ; not-halted = not-halted'
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt twf-[]
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF out-trace
        }
      ; stack-inv = record
        { slot-monotone = ≤-refl
        ; max-slot-written = next-slot alloc
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (Out {F} wf)
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; slot-stays-in-budget = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (Out {F} wf)
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- ir-stack-requirement (Out _) = 0, so no allocation
      out-trace : AbstractTrace
      out-trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace out-trace s alloc)

      -- Result validity: Out extracts F(νF) from νF, representationally same
      result-valid : ValidAtWF Heap alloc (eval (Out wf) x) input-loc s'
      result-valid = Out-trace-valid wf x

      -- rax-eq: Output = Input1 (from passthrough) = SV-Ptr input-loc (from rdi-eq)
      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
      rax-eq = trans (passthrough-output-is-input s alloc not-halted) rdi-eq

      not-halted' : halted s' ≡ false
      not-halted' = passthrough-preserves-halted s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = passthrough-mem-preserved s alloc loc not-halted

      -- IR doesn't allocate, return inj₁ refl
      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- in-ν: wrap functor layer into ν-type (Lambek inverse of Out)
  --
  -- By dual Lambek's Lemma, this is the inverse of Out. At runtime,
  -- F(νF) and νF have identical representation, so this is identity.
  -- Like In, if AllocMode requests allocation, we store at slot.
  ------------------------------------------------------------------------

  run-in-ν : ∀ {F} (wf : WellFormedF F) (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ ⟦ F ⟧T (ν-type F) ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF m (in-ν {F} wf m) x s alloc
  run-in-ν {F} wf mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    record
      { base = record
        { final-state = s'
        ; final-alloc = alloc'
        ; trace = in-ν-trace
        ; trace-correct = refl  -- s' DEFINED by trace
        ; result-place = at-loc result-loc result-valid result-bf rax-eq result-valid result-bf
        ; not-halted = not-halted'
        ; frame-preserved = refl
        ; trace-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))
        ; mem-preserved-before = λ _ _ → SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF in-ν-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-mono
        ; max-slot-written = next-slot alloc'
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (in-ν {F} wf m)
        ; max-slot-usage-bound = reclaim-bound
        ; slot-stays-in-budget = reclaim-bound
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = trace-wa
        ; trace-slot-reads-above = tt
        ; trace-writes-below = trace-wb
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (in-ν {F} wf m)
        ; scratch-bounded = m≤m+n (suc (next-slot alloc)) 1
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- ir-stack-requirement (in-ν _ _) = 1
      result-slot = next-slot alloc
      result-loc = AtStack (current-frame alloc) result-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = suc (next-slot alloc) }

      -- Trace: store input at slot, return slot address (same as In)
      -- 1. mov-to-output: Output := Input1
      -- 2. store-at-slot: slot[n] := Output
      -- 3. lea-slot: Output := &slot[n] (result location)
      in-ν-trace : AbstractTrace
      in-ν-trace = mov-to-output ∷ store-at-slot result-slot ∷ lea-slot result-slot ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace in-ν-trace s alloc)

      slot-mono : next-slot alloc ≤ next-slot alloc'
      slot-mono = n≤1+n (next-slot alloc)

      result-bf : BeforeFrontier alloc' result-loc
      result-bf = stack-before refl (n<1+n (next-slot alloc))

      -- Result validity: in-ν semantically wraps F(νF) → νF, representationally same
      result-valid : ValidAtWF m alloc' (eval (in-ν wf m) x) result-loc s'
      result-valid = in-ν-trace-valid wf m x

      -- suc n ≤ n + 1: ir-stack-requirement (in-ν wf m) ≡ 1 definitionally
      -- +-comm 1 n : 1 + n ≡ n + 1 where 1 + n = suc n
      n = next-slot alloc
      suc-n≡n+1 : suc n ≡ n +ℕ 1
      suc-n≡n+1 = +-comm 1 n

      reclaim-bound : suc n ≤ n +ℕ ir-stack-requirement (in-ν {F} wf m)
      reclaim-bound = ≤-reflexive suc-n≡n+1

      -- rax-eq: Output = slot address after lea-slot
      rax-eq : readReg (regs s') Output ≡ SV-Ptr result-loc
      rax-eq = rec-scheme-output-is-slot result-slot s alloc not-halted

      not-halted' : halted s' ≡ false
      not-halted' = rec-scheme-preserves-halted-3 result-slot s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved (AtStack f k) (stack-before refl k<n) =
        rec-scheme-preserves-slot-below-3 result-slot k s alloc not-halted k<n
      mem-preserved (AtStack f k) (stack-ancestor cf≺f _) =
        rec-scheme-preserves-ancestor-3 result-slot s alloc f k not-halted (≢-sym (≺⇒≢ cf≺f))
      mem-preserved (AtDynamic hl) (heap-before _) =
        rec-scheme-preserves-heap-3 result-slot s alloc hl not-halted

      trace-wa : SMP.TraceWritesAbove (next-slot alloc) in-ν-trace
      trace-wa = ≤-refl , tt

      trace-wb : SMP.TraceWritesBelow (suc (next-slot alloc)) in-ν-trace
      trace-wb = n<1+n (next-slot alloc) , tt

      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable s'' input-loc' _ _ _ = inj₂ (inj₂ tt)

  ------------------------------------------------------------------------
  -- Cata/Ana/Hylo/Fuse/Para: Complex recursion schemes
  --
  -- These are handled by separate modules:
  --   - RecCoreWF.agda: Unified core for Cata, Fuse, Hylo
  --   - ParaWF.agda: Paramorphism with subterm preservation
  --   - AnaWF.agda: Lazy corecursive production
  --
  -- See Dispatcher.agda for wiring.
  ------------------------------------------------------------------------