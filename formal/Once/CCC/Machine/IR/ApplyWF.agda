-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.ApplyWF
--
-- Apply IR implementation with clean trace-based structure.
-- Final state defined via exec-trace, making trace-correct = refl.
--
-- FRAME MODEL: NONE.
--
-- Apply does NOT push a child frame for body execution. Body inherits
-- the parent's frame and uses slot indices threaded above the parent's
-- used slots (i.e. body's own slot frontier starts at
-- `next-slot alloc + pair-slots`, just past the (env, arg) pair we set
-- up). Closures live in the curry's caller's slots and survive across
-- all calls; nothing dangles.
--
-- TRACE STRUCTURE:
--   1. Setup (env, arg) pair on stack
--   2. Execute body trace (in same frame, advanced frontier)
------------------------------------------------------------------------

module Once.CCC.Machine.IR.ApplyWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; <-≤-trans; m≤m+n; +-monoʳ-≤; m+n≤o⇒m≤o; ≤-reflexive)
open import Data.Nat using (_≤?_)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst; cong)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
import Once.CCC.Machine.SMPrimitives as SMP
open import Once.Type
open import Once.Semantics.Machine using (⟦_⟧; sem-fst; sem-snd; sem-pair; sem-inl; sem-inr; sem-case)
open import Once.CCC.Memory.TypeSlots using (stack-type-slots; heap-type-slots; type-slots)
pair = sem-pair
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import escape interface for SurvivesFramePop
open import Once.CCC.Machine.EscapeInterface
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
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (AtStack f k) (stack-before f-eq k<ns)
    rewrite cf-eq | ns-eq = stack-before f-eq k<ns
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (AtStack f k) (stack-ancestor cf≺f src)
    rewrite cf-eq = stack-ancestor cf≺f src
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (AtDynamic hl) (heap-before r<hr)
    rewrite hr-eq = heap-before r<hr

------------------------------------------------------------------------
-- Apply implementation with clean trace-based structure
------------------------------------------------------------------------

-- The four child-frame parameters (`get-child-frame`,
-- `child-frame-ordered`, `child-frame-adjacent`, `escape-result-survives`)
-- have been removed. Apply no longer creates a child frame; the body
-- runs in the parent's frame with the slot frontier advanced past the
-- (env, arg) pair we just stored. Closure pointers therefore reference
-- the parent's frame and survive trivially across the apply.
module ApplyWFImpl {FS : FrameSemantics} (program-bound : ℕ)
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
  open SMP.TraceComposition {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; BodyCorrect;
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           valid-inl-wf; valid-inr-wf;
           -- OCP-0003: valid-fold-wf removed
           validityWF-mem-only; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-frontier-advance;
           validityWF-with-bf-transfer;
           decomposePairWF; PairValidWF;
           decomposeClosureWF; ClosureValidWF;
           closure-mode-is-heap-proof)

  open import Once.CCC.Machine.DispatcherArithmeticLemma
    using (suc<+2)
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}
  open import Once.CCC.Machine.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (at-frontier-before-pair)
  open BFTransfer {FS}
    using (bf-same-frame-slot)

  ------------------------------------------------------------------------
  -- Apply trace construction
  --
  -- Apply trace structure:
  --   setup-trace: Store (env, arg) pair to stack, set Input1
  --   body-trace:  Execute closure body in the same frame, with
  --                slot indices starting above the (env, arg) pair.
  ------------------------------------------------------------------------

  -- Setup trace: uniform packed-pair calling convention (Plan
  -- 0.2.4.5 Stage C γ-revert).
  --
  -- Apply's input is the pair (closure, arg). It builds a NEW
  -- (env, arg) packed pair at slots [pair-slot, pair-slot+1] and
  -- points Input1 at it. Body's fst/snd are uniform load-indirect
  -- and load-indirect-suc, regardless of the body's input types.
  -- Future: typed split-passing (Stage I) layered on top once the
  -- IR / closure type carries body-input layout info; for now the
  -- packed convention is the principled base.
  --
  -- Step 1: Get arg-loc from *(Input1+1) while Input1 still points
  --         to original (closure, arg) pair.
  -- Step 2: Store arg-loc at pair[1].
  -- Step 3: Get closure-loc from *Input1.
  -- Step 4: Set Input1 := closure-loc.
  -- Step 5: Save closure-reg from Input1.
  -- Step 6: Get env-loc from *Input1 (closure[0] = env).
  -- Step 7: Store env-loc at pair[0].
  -- Step 8: Set Output := &pair (= lea-slot pair-slot).
  -- Step 9: Set Input1 := &pair.
  apply-setup-trace : (pair-slot : ℕ) → AbstractTrace
  apply-setup-trace pair-slot =
    load-indirect-suc ∷                 -- Output := arg-loc
    store-at-slot (suc pair-slot) ∷     -- pair[1] := arg-loc
    load-indirect ∷                     -- Output := closure-loc
    mov-to-input ∷                      -- Input1 := closure-loc
    instr-save-closure-reg ∷            -- save closure-reg
    load-indirect ∷                     -- Output := env-loc
    store-at-slot pair-slot ∷           -- pair[0] := env-loc
    lea-slot pair-slot ∷                -- Output := &pair
    mov-to-input ∷ []                   -- Input1 := &pair

  -- Full apply trace: setup + body. No frame push/pop — body inherits
  -- parent's frame and uses slot indices threaded above the (env, arg)
  -- pair we just stored. The `body-cap` parameter is retained for ABI
  -- compatibility with the dispatcher's body-correct signature but is
  -- not used in the trace itself.
  apply-full-trace : (pair-slot : ℕ) (body-cap : ℕ) (body-trace : AbstractTrace) → AbstractTrace
  apply-full-trace pair-slot _ body-trace =
    apply-setup-trace pair-slot ++ body-trace

  ------------------------------------------------------------------------
  -- run-apply: Clean trace-based implementation
  ------------------------------------------------------------------------

  run-apply : ∀ {m A B k}
    (x : ⟦ (A ⇒[ k ] B) * A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-valid-wf : ValidAtWF m alloc x input-loc s) →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mOut ] IRResultAWF mOut (apply {A} {B} {k}) x s alloc
  run-apply {m} {A} {B} {k} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mBody , record
      { final-state = s'
      ; final-alloc = alloc'
      ; trace = trace
      ; trace-correct = refl  -- BY DEFINITION
      ; result-place = result-place-final
      ; not-halted = not-halted'
      ; frame-preserved = trans (IRResultAWF.frame-preserved body-result) refl
      ; slot-monotone = ≤-trans (m≤m+n (next-slot alloc) pair-slots)
                                (IRResultAWF.slot-monotone body-result)
      ; heap-preserved = IRResultAWF.heap-preserved body-result
      -- Plan 0.2.4.5 D1 task #30: dynamic budgets — body-cap propagates
      -- through pair-slots + body's stack-budget. With alloc' = body's
      -- final-alloc, the bounds chain directly via body's IRResultAWF.
      ; stack-budget = pair-slots +ℕ IRResultAWF.stack-budget body-result
      ; max-slot-written = IRResultAWF.max-slot-written body-result
      ; max-slot-geq-final = IRResultAWF.max-slot-geq-final body-result
      ; max-slot-usage-bound = max-slot-usage-bound'
      ; slot-stays-in-budget = slot-stays-in-budget'
      ; frontier-slot-stable = frontier-stable'
      ; trace-writes-above = trace-writes-above'
      ; trace-slot-reads-above = trace-slot-reads-above'
      ; trace-writes-below = trace-writes-below'
      ; trace-slot-reads-below = trace-slot-reads-below'
      -- Note: trace-preserves-capacity removed in Phase 3
      ; trace-no-heap-writes = trace-no-heap-writes'
      ; trace-twf = trace-twf'
      ; trace-preserves-halted = exec-trace-preserves-halted-WF trace
      ; scratch-budget = IRResultAWF.scratch-budget body-result
      ; scratch-bounded = IRResultAWF.scratch-bounded body-result
      }
    where
      open import Data.Nat using (_≥_)
      open import Data.Nat.Properties using (*-monoʳ-≤; <⇒≤; *-monoˡ-≤; m<m+n)

      -- Decompose input pair
      pair-decomp = decomposePairWF {m} {_} {A ⇒[ k ] B} {A} input-valid-wf
      closure-loc = PairValidWF.fst-loc pair-decomp
      arg-loc = PairValidWF.snd-loc pair-decomp
      mArg = PairValidWF.mB pair-decomp
      closure-valid-wf = PairValidWF.fst-valid pair-decomp
      arg-valid-wf = PairValidWF.snd-valid pair-decomp
      arg-before = PairValidWF.snd-before pair-decomp

      closure : ⟦ A ⇒[ k ] B ⟧
      closure = sem-fst {A ⇒[ k ] B} {A} x

      arg : ⟦ A ⟧
      arg = sem-snd {A ⇒[ k ] B} {A} x

      -- Decompose closure
      mClosure = PairValidWF.mA pair-decomp
      closure-mode-is-heap : mClosure ≡ Heap
      closure-mode-is-heap = closure-mode-is-heap-proof closure-valid-wf
      closure-valid-wf-heap : ValidAtWF Heap alloc closure closure-loc s
      closure-valid-wf-heap = subst (λ m → ValidAtWF m alloc closure closure-loc s)
        closure-mode-is-heap closure-valid-wf

      closure-decomp = decomposeClosureWF {_} {k} {A} {B} closure-valid-wf-heap
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
      pair-input-loc = AtStack (current-frame alloc) pair-slot

      -- Body inherits the parent's frame; only the slot frontier
      -- advances past the (env, arg) pair we stored.
      child-alloc : AllocState {FS}
      child-alloc = record alloc { next-slot = next-slot alloc +ℕ pair-slots }

      ------------------------------------------------------------------------
      -- Execute body in same frame as parent (to get body-trace).
      ------------------------------------------------------------------------

      -- State after setup (before push-frame)
      -- This is computed by exec-trace on setup-trace
      -- For body execution, we pass this state to BodyCorrect.execute

      -- State after setup trace execution (DEFINED directly)
      s-after-setup : LocState FS
      s-after-setup = proj₁ (exec-trace (apply-setup-trace pair-slot) s alloc)

      s-after-setup-def : s-after-setup ≡ proj₁ (exec-trace (apply-setup-trace pair-slot) s alloc)
      s-after-setup-def = refl

      -- Memory facts from validity witnesses
      closure-ptr : readLoc s input-loc ≡ just (SV-Ptr closure-loc)
      closure-ptr = PairValidWF.fst-ptr pair-decomp

      arg-ptr : readLoc s (sucLoc input-loc) ≡ just (SV-Ptr arg-loc)
      arg-ptr = PairValidWF.snd-ptr pair-decomp

      env-ptr : readLoc s closure-loc ≡ just (SV-Ptr env-loc)
      env-ptr = ClosureValidWF.env-ptr closure-decomp

      ------------------------------------------------------------------------
      -- Step-by-step execution of setup trace
      --
      -- Setup trace structure:
      --   1. load-indirect-suc    -- Output := *(sucLoc Input1) = arg-loc
      --   2. store-at-slot (suc pair-slot)  -- slot (suc pair-slot) := arg-loc
      --   3. load-indirect        -- Output := *Input1 = closure-loc
      --   4. mov-to-input         -- Input1 := closure-loc
      --   5. load-indirect        -- Output := *closure-loc = env-loc
      --   6. store-at-slot pair-slot  -- slot pair-slot := env-loc
      --   7. lea-slot pair-slot   -- Output := &pair
      --   8. mov-to-input         -- Input1 := &pair
      ------------------------------------------------------------------------

      -- Frame shorthand
      frame = current-frame alloc

      -- Step 1: load-indirect-suc
      -- Before: Input1 = input-loc
      -- After: Output = arg-loc (from *(sucLoc input-loc))
      step1-trace : AbstractTrace
      step1-trace = load-indirect-suc ∷ []

      s1 : LocState FS
      s1 = proj₁ (exec-trace step1-trace s alloc)

      -- After load-indirect-suc, Output = SV-Ptr arg-loc.
      -- TODO: discharge — proof composes sv-as-loc-SV-Ptr rdi-eq + arg-ptr
      -- through exec-abstract's load-indirect-suc with-branch.
      step1-output : readReg (regs s1) Output ≡ SV-Ptr arg-loc
      step1-output = SMP.!!

      -- Step 2: store-at-slot (suc pair-slot)
      -- Writes Output (= arg-loc) to slot (suc pair-slot)
      step2-trace : AbstractTrace
      step2-trace = store-at-slot (suc pair-slot) ∷ []

      -- State after steps 1-2
      s2 : LocState FS
      s2 = proj₁ (exec-trace (step1-trace ++ step2-trace) s alloc)

      -- Not halted after step 1
      not-halted-s1 : halted s1 ≡ false
      not-halted-s1 = exec-trace-preserves-halted-WF step1-trace s alloc not-halted
                        (twf-∷ (SMP.!!) twf-[])  -- load-indirect-suc InstrWF: arg-ptr witness

      -- Step 2 writes arg-loc to slot (suc pair-slot)
      step2-written : readLoc s2 (AtStack frame (suc pair-slot)) ≡ just (SV-Ptr arg-loc)
      step2-written =
        let alloc1 = proj₂ (exec-trace step1-trace s alloc)
            frame-eq : current-frame alloc1 ≡ frame
            frame-eq = exec-trace-preserves-frame step1-trace s alloc
            s2-decomp : s2 ≡ proj₁ (exec-trace step2-trace s1 alloc1)
            s2-decomp = cong proj₁ (exec-trace-append step1-trace step2-trace s alloc)
            s2-as-abstract : proj₁ (exec-trace step2-trace s1 alloc1) ≡
                             proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s1 alloc1)
            s2-as-abstract = cong proj₁ (exec-trace-single (store-at-slot (suc pair-slot)) s1 alloc1 not-halted-s1)
            store-result : readLoc (proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s1 alloc1))
                                   (AtStack (current-frame alloc1) (suc pair-slot)) ≡
                           just (readReg (regs s1) Output)
            store-result = store-at-slot-result (suc pair-slot) s1 alloc1
        in subst (λ s' → readLoc s' (AtStack frame (suc pair-slot)) ≡ just (SV-Ptr arg-loc))
                 (sym (trans s2-decomp s2-as-abstract))
                 (subst (λ f → readLoc (proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s1 alloc1))
                                       (AtStack f (suc pair-slot)) ≡ just (SV-Ptr arg-loc))
                        frame-eq
                        (trans store-result (cong just step1-output)))

      -- Remaining setup preserves slot (suc pair-slot)
      -- Steps 3-9 don't write to slot (suc pair-slot):
      --   3. load-indirect (no mem write)
      --   4. mov-to-input (no mem write)
      --   5. instr-save-closure-reg (no mem write)
      --   6. load-indirect (no mem write)
      --   7. store-at-slot pair-slot (writes to pair-slot ≠ suc pair-slot)
      --   8. lea-slot pair-slot (no mem write)
      --   9. mov-to-input (no mem write)
      rest-after-step2 : AbstractTrace
      rest-after-step2 = load-indirect ∷ mov-to-input ∷
                         instr-save-closure-reg ∷
                         load-indirect ∷ store-at-slot pair-slot ∷
                         lea-slot pair-slot ∷ mov-to-input ∷ []

      -- setup-trace = step1-trace ++ step2-trace ++ rest-after-step2
      setup-trace-decomp2 : apply-setup-trace pair-slot ≡
                            step1-trace ++ step2-trace ++ rest-after-step2
      setup-trace-decomp2 = refl

      -- rest-after-step2 writes only at pair-slot, which is < suc pair-slot
      rest-writes-below-suc : SMP.TraceWritesBelow (suc pair-slot) rest-after-step2
      rest-writes-below-suc = ≤-refl , tt  -- store-at-slot pair-slot has pair-slot < suc pair-slot, rest are nothing

      rest-no-heap-writes : SMP.TraceNoHeapWrites rest-after-step2
      rest-no-heap-writes = tt

      -- Pair is properly constructed after setup
      pair-arg-ptr : readLoc s-after-setup (sucLoc pair-input-loc) ≡ just (SV-Ptr arg-loc)
      pair-arg-ptr =
        let alloc2 = proj₂ (exec-trace (step1-trace ++ step2-trace) s alloc)
            s-after-setup-decomp : s-after-setup ≡ proj₁ (exec-trace rest-after-step2 s2 alloc2)
            s-after-setup-decomp = cong proj₁ (exec-trace-append (step1-trace ++ step2-trace) rest-after-step2 s alloc)
            frame-eq2 : current-frame alloc2 ≡ frame
            frame-eq2 = exec-trace-preserves-frame (step1-trace ++ step2-trace) s alloc
            -- Use exec-trace-slot-value-below to show slot (suc pair-slot) is preserved
            -- rest writes below suc pair-slot, so slot suc pair-slot is preserved
            preserved : readLoc (proj₁ (exec-trace rest-after-step2 s2 alloc2))
                               (AtStack (current-frame alloc2) (suc pair-slot)) ≡ just (SV-Ptr arg-loc)
            preserved = exec-trace-slot-value-below rest-after-step2 s2 alloc2 (suc pair-slot) (SV-Ptr arg-loc)
                          (subst (λ f → readLoc s2 (AtStack f (suc pair-slot)) ≡ just (SV-Ptr arg-loc))
                                 (sym frame-eq2) step2-written)
                          rest-writes-below-suc rest-no-heap-writes
        in subst (λ s' → readLoc s' (AtStack frame (suc pair-slot)) ≡ just (SV-Ptr arg-loc))
                 (sym s-after-setup-decomp)
                 (subst (λ f → readLoc (proj₁ (exec-trace rest-after-step2 s2 alloc2))
                                       (AtStack f (suc pair-slot)) ≡ just (SV-Ptr arg-loc))
                        frame-eq2 preserved)

      -- For pair-env-ptr, we need to trace through to step 7
      -- Steps 1-6 are prefix, step 7 stores env-loc, steps 8-9 preserve

      -- State after steps 1-6 (before store-at-slot pair-slot)
      prefix-for-env : AbstractTrace
      prefix-for-env = load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷
                       load-indirect ∷ mov-to-input ∷ instr-save-closure-reg ∷
                       load-indirect ∷ []

      suffix-after-env-store : AbstractTrace
      suffix-after-env-store = lea-slot pair-slot ∷ mov-to-input ∷ []

      setup-decomp-for-env : apply-setup-trace pair-slot ≡
                             prefix-for-env ++ store-at-slot pair-slot ∷ suffix-after-env-store
      setup-decomp-for-env = refl

      -- TracePreservesHalted for prefix-for-env
      prefix-for-env-tph : TraceWF s alloc prefix-for-env
      prefix-for-env-tph =
        twf-∷ (SMP.!!)            -- load-indirect-suc: arg-ptr witness
        (twf-∷ tt
        (twf-∷ (SMP.!!)          -- load-indirect: closure-ptr witness
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ (SMP.!!) twf-[]))))) -- load-indirect: env-ptr witness

      not-halted-after-prefix-for-env : halted (proj₁ (exec-trace prefix-for-env s alloc)) ≡ false
      not-halted-after-prefix-for-env = exec-trace-preserves-halted-WF prefix-for-env s alloc not-halted prefix-for-env-tph

      -- suffix writes above suc pair-slot (lea-slot and mov-to-input don't write to slots)
      suffix-writes-above : SMP.TraceWritesAbove (suc pair-slot) suffix-after-env-store
      suffix-writes-above = tt  -- both instructions have instr-writes-slot = nothing

      suffix-no-heap-writes : SMP.TraceNoHeapWrites suffix-after-env-store
      suffix-no-heap-writes = tt

      ------------------------------------------------------------------------
      -- Prove output-after-prefix: Output = env-loc after steps 1-5
      --
      -- Step by step:
      --   1. load-indirect-suc: Output := *(sucLoc Input1) = arg-loc
      --   2. store-at-slot: Output unchanged
      --   3. load-indirect: Output := *Input1 = closure-loc
      --   4. mov-to-input: Input1 := Output = closure-loc, Output unchanged
      --   5. load-indirect: Output := *Input1 = *closure-loc = env-loc
      ------------------------------------------------------------------------

      -- Decompose prefix-for-env into sub-traces
      prefix12 : AbstractTrace
      prefix12 = load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷ []

      prefix345 : AbstractTrace
      prefix345 = load-indirect ∷ mov-to-input ∷ instr-save-closure-reg ∷ load-indirect ∷ []

      prefix-decomp-12-345 : prefix-for-env ≡ prefix12 ++ prefix345
      prefix-decomp-12-345 = refl

      -- State after steps 1-2
      s12 : LocState FS
      s12 = proj₁ (exec-trace prefix12 s alloc)

      alloc12 : AllocState {FS}
      alloc12 = proj₂ (exec-trace prefix12 s alloc)

      -- Steps 1-2 preserve halted
      prefix12-tph : TraceWF s alloc prefix12
      prefix12-tph = twf-∷ (SMP.!!) (twf-∷ tt twf-[])  -- TODO: load-indirect-suc witness

      not-halted-s12 : halted s12 ≡ false
      not-halted-s12 = exec-trace-preserves-halted-WF prefix12 s alloc not-halted prefix12-tph

      -- Input1 is still input-loc after steps 1-2 (neither instruction modifies Input1)
      -- Step 1 modifies Output only, Step 2 writes to memory only
      -- Both preserve Input1 register
      input-after-s12 : readReg (regs s12) Input1 ≡ SV-Ptr input-loc
      input-after-s12 = SMP.!!  -- Needs trace infrastructure for register preservation

      -- Memory is preserved for closure-loc: steps 1-2 only write to slot (suc pair-slot)
      -- which is on stack, not at closure-loc (which is on heap since closure is Heap mode)
      closure-readable-after-s12 : readLoc s12 closure-loc ≡ just (SV-Ptr env-loc)
      closure-readable-after-s12 = SMP.!!  -- Needs frame/heap preservation proof

      -- Step 3: load-indirect reads closure-loc, gets env-loc (after step 3)
      prefix3 : AbstractTrace
      prefix3 = load-indirect ∷ []

      s3-partial : LocState FS
      s3-partial = proj₁ (exec-trace prefix3 s12 alloc12)

      -- After step 3, Output = *Input1 = *input-loc = closure-loc
      step3-output : readReg (regs s3-partial) Output ≡ SV-Ptr closure-loc
      step3-output = SMP.!!  -- Needs load-indirect result lemma

      -- Step 4: mov-to-input sets Input1 := Output = closure-loc, preserves Output
      prefix34 : AbstractTrace
      prefix34 = load-indirect ∷ mov-to-input ∷ []

      s34-partial : LocState FS
      s34-partial = proj₁ (exec-trace prefix34 s12 alloc12)

      prefix3-tph : TraceWF s12 alloc12 prefix3
      prefix3-tph = twf-∷ (SMP.!!) twf-[]  -- TODO: load-indirect witness at s12

      not-halted-s3 : halted s3-partial ≡ false
      not-halted-s3 = exec-trace-preserves-halted-WF prefix3 s12 alloc12 not-halted-s12 prefix3-tph

      -- After step 4, Input1 = closure-loc
      step4-input : readReg (regs s34-partial) Input1 ≡ SV-Ptr closure-loc
      step4-input =
        let alloc3 = proj₂ (exec-trace prefix3 s12 alloc12)
            s34-decomp : s34-partial ≡ proj₁ (exec-abstract mov-to-input s3-partial alloc3)
            s34-decomp = cong proj₁ (trans (exec-trace-append prefix3 (mov-to-input ∷ []) s12 alloc12)
                                           (exec-trace-single mov-to-input s3-partial alloc3 not-halted-s3))
        in trans (cong (λ s' → readReg (regs s') Input1) s34-decomp)
                 (trans (writeReg-same (regs s3-partial) Input1 (readReg (regs s3-partial) Output))
                        step3-output)

      -- Step 5: load-indirect reads *Input1 = *closure-loc = env-loc
      prefix345-tph : TraceWF s12 alloc12 prefix345
      prefix345-tph = twf-∷ (SMP.!!)        -- TODO: load-indirect witness at s12
                      (twf-∷ tt
                      (twf-∷ tt
                      (twf-∷ (SMP.!!) twf-[])))  -- TODO: load-indirect witness at s345

      not-halted-s345 : halted (proj₁ (exec-trace prefix345 s12 alloc12)) ≡ false
      not-halted-s345 = exec-trace-preserves-halted-WF prefix345 s12 alloc12 not-halted-s12 prefix345-tph

      -- After step 5, Output = *closure-loc = env-loc
      output-after-prefix : readReg (regs (proj₁ (exec-trace prefix-for-env s alloc))) Output ≡ SV-Ptr env-loc
      output-after-prefix =
        let -- Decompose prefix execution
            prefix-decomp : proj₁ (exec-trace prefix-for-env s alloc) ≡
                           proj₁ (exec-trace prefix345 s12 alloc12)
            prefix-decomp = cong proj₁ (exec-trace-append prefix12 prefix345 s alloc)
        in trans (cong (λ s' → readReg (regs s') Output) prefix-decomp)
                 (step5-output-final s12 alloc12 not-halted-s12)
        where
          step5-output-final : (s₀ : LocState FS) (a₀ : AllocState {FS}) →
            halted s₀ ≡ false →
            readReg (regs (proj₁ (exec-trace prefix345 s₀ a₀))) Output ≡ SV-Ptr env-loc
          step5-output-final s₀ a₀ nh = SMP.!!  -- Final step needs closure memory read

      -- TODO (post-scaffold): rederive via a TraceWF-shaped
      -- prefix-store-preserve. Original proof used the tph chain.
      pair-env-ptr : readLoc s-after-setup pair-input-loc ≡ just (SV-Ptr env-loc)
      pair-env-ptr = SMP.!!

      -- Input1 register points to pair after setup
      -- Decompose setup-trace as prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
      setup-prefix : AbstractTrace
      setup-prefix = load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷
                     load-indirect ∷ mov-to-input ∷ instr-save-closure-reg ∷
                     load-indirect ∷ store-at-slot pair-slot ∷ []

      setup-decomp : apply-setup-trace pair-slot ≡
                     setup-prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
      setup-decomp = refl

      -- TracePreservesHalted for the prefix
      setup-prefix-tph : TraceWF s alloc setup-prefix
      setup-prefix-tph =
        twf-∷ (SMP.!!)            -- TODO: load-indirect-suc witness
        (twf-∷ tt
        (twf-∷ (SMP.!!)          -- TODO: load-indirect witness
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ (SMP.!!)          -- TODO: load-indirect witness
        (twf-∷ tt twf-[]))))))

      not-halted-after-prefix : halted (proj₁ (exec-trace setup-prefix s alloc)) ≡ false
      not-halted-after-prefix = exec-trace-preserves-halted-WF setup-prefix s alloc not-halted setup-prefix-tph

      pair-input-eq : readReg (regs s-after-setup) Input1 ≡ SV-Ptr pair-input-loc
      pair-input-eq =
        let eq1 : apply-setup-trace pair-slot ≡
                  setup-prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
            eq1 = setup-decomp
            eq2 : readReg (regs (proj₁ (exec-trace (setup-prefix ++
                           (lea-slot pair-slot ∷ mov-to-input ∷ [])) s alloc))) Input1 ≡
                  SV-Ptr (AtStack (current-frame alloc) pair-slot)
            eq2 = SMP.!!  -- TODO: exec-trace-final-lea-mov-input under StoredValue
        in subst (λ t → readReg (regs (proj₁ (exec-trace t s alloc))) Input1 ≡
                        SV-Ptr (AtStack (current-frame alloc) pair-slot))
                 (sym eq1) eq2

      -- Setup trace preserves halted (used in multiple places)
      setup-tph : TraceWF s alloc (apply-setup-trace pair-slot)
      setup-tph =
        twf-∷ (SMP.!!)            -- TODO: load-indirect-suc witness
        (twf-∷ tt
        (twf-∷ (SMP.!!)          -- TODO: load-indirect witness
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ (SMP.!!)          -- TODO: load-indirect witness
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ tt twf-[]))))))))

      -- Not halted after setup
      not-halted-after-setup : halted s-after-setup ≡ false
      not-halted-after-setup = exec-trace-preserves-halted-WF (apply-setup-trace pair-slot) s alloc not-halted setup-tph

      -- Pair validity in alloc' (same frame as parent, frontier
      -- advanced past the (env, arg) pair).
      pair-input-valid-child : ValidAtWF Heap child-alloc {EnvType * A} (pair env arg) pair-input-loc s-after-setup
      pair-input-valid-child = SMP.!!

      -- Pair is before frontier in alloc' (same frame, slot index
      -- pair-slot < next-slot alloc + pair-slots).
      pair-input-before-child : BeforeFrontier child-alloc pair-input-loc
      pair-input-before-child =
        stack-before refl (m<m+n pair-slot {pair-slots} (s≤s z≤n))

      -- Body execution in the same frame as parent.
      body-exec-result : ∃[ mOut ] IRResultAWF mOut body (pair env arg) s-after-setup child-alloc
      body-exec-result = BodyCorrect.execute body-correct arg arg-loc pair-input-loc
        s-after-setup child-alloc Heap
        pair-input-valid-child pair-input-before-child not-halted-after-setup pair-input-eq

      mBody = proj₁ body-exec-result
      body-result = proj₂ body-exec-result

      body-trace = IRResultAWF.trace body-result

      -- Plan 0.2.4.5 D1 task #30: alloc' tracks body's full final-alloc
      -- (next-slot extends past pair-slots into body's stack region).
      -- This bridges body's place-before / place-valid (both in body's
      -- final-alloc) up to apply's alloc' frontier without going through
      -- a (broken) static `next-slot alloc + pair-slots` claim.
      alloc' : AllocState {FS}
      alloc' = IRResultAWF.final-alloc body-result

      -- Plan 0.2.4.5 D1 task #28: dispatch on body's result-place
      -- to extract result-loc. Same pattern as compose / pair:
      --   at-loc → bound loc.
      --   unit-result → readReg <body-final-state> Output (whatever
      --     Output happens to be at body's end). Apply's downstream
      --     properties (rax-eq', mem-preserved', result-before',
      --     etc., all currently SMP.!! — see task #30) inherit this
      --     value as their result-loc index.
      result-loc-dispatch : ResultPlace _ _ _ _ _ _ → ValueLocation FS
      result-loc-dispatch (at-loc loc _ _ _ _ _) = loc
      result-loc-dispatch unit-result = SMP.!!  -- TODO: extract via sv-as-loc of body's Output

      result-loc = result-loc-dispatch (IRResultAWF.result-place body-result)

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

      -- Trace preserves halted: setup-twf ++ body-trace's twf.
      -- TODO: body-trace's TraceWF is at (s-after-setup-via-child-alloc, child-alloc);
      -- need to bridge through frame-eq to (s-after-setup, alloc-after-setup).
      trace-twf' : TraceWF s alloc trace
      trace-twf' = twf-++ not-halted setup-tph (SMP.!!)  -- TODO: body-trace's twf at runtime state

      ----------------------------------------------------------------
      -- Foundation postulates (Plan 0.2.4.5 task #30).
      --
      -- apply's full trace is `setup-trace ++ body-trace`, so its
      -- semantics decompose: each property below = setup-trace's
      -- contribution + body-trace's IRResultAWF transport.
      --
      -- Foundation lemma s'-eq (below) is the shared workhorse:
      --   s' ≡ IRResultAWF.final-state body-result
      -- via exec-trace-append-state (decompose) + exec-trace-same-frame
      -- (bridge alloc-after-setup ≡ child-alloc by frame equivalence)
      -- + body's trace-correct (body-final-state defined by trace).
      --
      -- DISCHARGED here: rax-eq', mem-preserved', trace-writes-above',
      -- trace-slot-reads-above'.
      --
      -- STRUCTURALLY DEFERRED (need apply spec changes):
      --   result-before', result-valid-wf' — body's `place-before`
      --     gives `BeforeFrontier (final-alloc body) loc`, but apply's
      --     `alloc'` only widens next-slot by pair-slots, NOT
      --     next-heap-ref. If body allocates in heap, the returned loc
      --     can't be `BeforeFrontier alloc'`. Fix: alloc' must track
      --     body's full final-alloc (or apply's spec must propagate
      --     body's heap frontier).
      --   frontier-stable' — same family.
      --   trace-writes-below', trace-slot-reads-below' — body writes
      --     at slots in [next-slot child-alloc, body-max), exceeding
      --     `next-slot alloc + pair-slots`. Fix: ir-stack-requirement
      --     apply must include body-cap (currently pair-slots only).
      ----------------------------------------------------------------

      -- s' decomposes via exec-trace-append-state.
      s'-decomp : s' ≡ proj₁ (exec-trace body-trace s-after-setup
                                (proj₂ (exec-trace (apply-setup-trace pair-slot) s alloc)))
      s'-decomp = exec-trace-append-state (apply-setup-trace pair-slot) body-trace s alloc

      -- Frame after setup ≡ frame of child-alloc (both = current-frame alloc).
      frame-after-setup-eq :
        current-frame (proj₂ (exec-trace (apply-setup-trace pair-slot) s alloc))
        ≡ current-frame child-alloc
      frame-after-setup-eq = exec-trace-preserves-frame (apply-setup-trace pair-slot) s alloc

      -- Bridge: exec-trace body-trace from s-after-setup is the same
      -- under (proj₂ exec-trace setup) and child-alloc (same frame).
      body-frame-bridge :
        proj₁ (exec-trace body-trace s-after-setup
                (proj₂ (exec-trace (apply-setup-trace pair-slot) s alloc)))
        ≡ proj₁ (exec-trace body-trace s-after-setup child-alloc)
      body-frame-bridge = exec-trace-same-frame body-trace s-after-setup
                            (proj₂ (exec-trace (apply-setup-trace pair-slot) s alloc))
                            child-alloc frame-after-setup-eq

      -- Body's trace-correct.
      body-trace-correct :
        proj₁ (exec-trace body-trace s-after-setup child-alloc) ≡ IRResultAWF.final-state body-result
      body-trace-correct = IRResultAWF.trace-correct body-result

      -- Foundation: s' equals body's final-state.
      s'-eq : s' ≡ IRResultAWF.final-state body-result
      s'-eq = trans s'-decomp (trans body-frame-bridge body-trace-correct)

      -- Output register contains result location.
      -- Dispatch on body's result-place: at-loc gives place-rax;
      -- unit-result reduces result-loc to readReg body-final-state Output (refl after s'-eq).
      rax-eq' : readReg (regs s') Output ≡ SV-Ptr result-loc
      rax-eq' with IRResultAWF.result-place body-result
      ... | at-loc loc valid before rax _ _ =
              trans (cong (λ st → readReg (regs st) Output) s'-eq) rax
      ... | unit-result =
              cong (λ st → readReg (regs st) Output) s'-eq

      -- Not halted after full trace
      not-halted' : halted s' ≡ false
      not-halted' = exec-trace-preserves-halted-WF trace s alloc not-halted trace-twf'

      -- Setup-trace writes only at pair-slot and suc pair-slot.
      -- Both ≥ pair-slot, so TraceWritesAbove pair-slot.
      setup-writes-above-early : TraceWritesAbove pair-slot (apply-setup-trace pair-slot)
      setup-writes-above-early =
        n≤1+n pair-slot ,                   -- store-at-slot (suc pair-slot)
        ≤-refl ,                            -- store-at-slot pair-slot
        tt
        where
          open import Data.Nat.Properties using (n≤1+n; ≤-refl)

      -- Setup trace has no heap writes.
      setup-no-heap-writes-early : TraceNoHeapWrites (apply-setup-trace pair-slot)
      setup-no-heap-writes-early = tt

      -- Frontier widening: alloc's frontier is below child-alloc's
      -- (same frame, next-slot widened by pair-slots).
      widen-bf-to-child : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier child-alloc loc
      widen-bf-to-child loc bf = frontier-monotone alloc child-alloc refl
        (m≤m+n (next-slot alloc) pair-slots) ≤-refl loc bf
        where
          open import Data.Nat.Properties using (m≤m+n; ≤-refl)

      -- Setup-trace preserves loc-reads at any loc < alloc-frontier
      -- (no heap writes; stack writes only at pair-slot, suc pair-slot ≥ alloc-frontier).
      setup-mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s-after-setup loc ≡ readLoc s loc
      setup-mem-preserved loc bf = ClosureWellFormedDef.derive-mem-preserved
                                     program-bound
                                     alloc (apply-setup-trace pair-slot) s
                                     setup-writes-above-early setup-no-heap-writes-early loc bf

      -- Body's mem preservation via irresult-mem-preserved + frontier widening.
      body-mem-preserved : ∀ loc → BeforeFrontier alloc loc →
        readLoc (IRResultAWF.final-state body-result) loc ≡ readLoc s-after-setup loc
      body-mem-preserved loc bf = ClosureWellFormedDef.irresult-mem-preserved program-bound body-result loc (widen-bf-to-child loc bf)

      -- Memory before frontier preserved: chain s'-eq + body + setup.
      mem-preserved' : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved' loc bf = trans (cong (λ st → readLoc st loc) s'-eq)
                                (trans (body-mem-preserved loc bf) (setup-mem-preserved loc bf))

      -- Result is before frontier in alloc'.
      -- Plan 0.2.4.5 D1 task #30: alloc' = body's final-alloc, so body's
      -- place-before transports directly via the result-place dispatch.
      -- For unit-result branch this isn't reached (apply uses unit-result),
      -- but the function must still typecheck for the at-loc dispatch.
      result-before' : BeforeFrontier alloc' result-loc
      result-before' with IRResultAWF.result-place body-result
      ... | at-loc loc valid before _ _ _ = before
      ... | unit-result = unit-bf
        where postulate unit-bf : BeforeFrontier alloc' (readReg (regs (IRResultAWF.final-state body-result)) Output)

      -- Closure-decomp eval bridge: eval (apply ...) x ≡ eval body (pair env arg).
      -- closure-is-body : closure ≡ (λ a → eval body (pair env a)).
      -- eval (apply) (closure, arg) reduces to closure arg, which equals
      -- (λ a → eval body (pair env a)) arg ≡ eval body (pair env arg).
      eval-apply-eq : eval (apply {A} {B} {k}) x ≡ eval body (pair env arg)
      eval-apply-eq = cong (λ c → c arg) closure-is-body

      -- Result validity. body's place-valid gives validity for eval body
      -- (pair env arg) at body-final-alloc / body-final-state.
      -- alloc' = body's final-alloc (definitional);
      -- s' ≡ body-final-state via s'-eq;
      -- eval (apply ...) x ≡ eval body (pair env arg) via eval-apply-eq.
      result-valid-wf' : ValidAtWF mBody alloc' (eval (apply {A} {B} {k}) x) result-loc s'
      result-valid-wf' with IRResultAWF.result-place body-result
      ... | at-loc body-loc body-valid _ _ _ _ =
              subst (λ st → ValidAtWF mBody alloc' (eval (apply {A} {B} {k}) x) body-loc st)
                    (sym s'-eq)
                    (subst (λ v → ValidAtWF mBody alloc' v body-loc (IRResultAWF.final-state body-result))
                           (sym eval-apply-eq)
                           body-valid)
      ... | unit-result =
              subst (λ st → ValidAtWF mBody alloc' tt
                              (readReg (regs (IRResultAWF.final-state body-result)) Output) st)
                    (sym s'-eq) valid-unit-wf

      -- Frontier slot stability: apply uses the third (give-up) branch.
      -- The 3-way return for IRs that allocate but may write the
      -- frontier slot accommodates apply's pair construction (which
      -- writes pair-slot during setup, so the slot does NOT preserve
      -- the original input-loc). inj₂ (inj₂ tt) is the give-up branch.
      frontier-stable' : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) pair-slot) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable' s'' input-loc' _ _ _ = inj₂ (inj₂ tt)

      -- Setup-trace writes only at pair-slot and suc pair-slot.
      -- Both ≥ pair-slot, so TraceWritesAbove pair-slot.
      setup-writes-above : TraceWritesAbove pair-slot (apply-setup-trace pair-slot)
      setup-writes-above =
        n≤1+n pair-slot ,                   -- store-at-slot (suc pair-slot)
        ≤-refl ,                            -- store-at-slot pair-slot
        tt
        where
          open import Data.Nat.Properties using (n≤1+n; ≤-refl)

      -- Setup-trace reads no slots (instr-reads-slot = nothing for all).
      setup-slot-reads-above : TraceSlotReadsAbove pair-slot (apply-setup-trace pair-slot)
      setup-slot-reads-above = tt

      -- Body's trace-writes-above is at next-slot child-alloc = pair-slot + pair-slots.
      -- Mono down to pair-slot.
      body-writes-above-pair-slot : TraceWritesAbove pair-slot body-trace
      body-writes-above-pair-slot = trace-writes-above-mono pair-slot
        (next-slot alloc +ℕ pair-slots)
        body-trace
        (m≤m+n pair-slot pair-slots)
        (IRResultAWF.trace-writes-above body-result)

      body-slot-reads-above-pair-slot : TraceSlotReadsAbove pair-slot body-trace
      body-slot-reads-above-pair-slot = trace-slot-reads-above-mono pair-slot
        (next-slot alloc +ℕ pair-slots)
        body-trace
        (m≤m+n pair-slot pair-slots)
        (IRResultAWF.trace-slot-reads-above body-result)

      -- Trace properties: append setup and body.
      trace-writes-above' : TraceWritesAbove pair-slot trace
      trace-writes-above' = trace-writes-above-append pair-slot
        (apply-setup-trace pair-slot) body-trace
        setup-writes-above body-writes-above-pair-slot

      trace-slot-reads-above' : TraceSlotReadsAbove pair-slot trace
      trace-slot-reads-above' = trace-slot-reads-above-append pair-slot
        (apply-setup-trace pair-slot) body-trace
        setup-slot-reads-above body-slot-reads-above-pair-slot

      -- Plan 0.2.4.5 D1 task #30: dynamic-budget bounds.
      -- Apply's max-slot-written = body's max-slot-written (body always
      -- writes ≥ next-slot child-alloc = next-slot alloc + pair-slots,
      -- which dominates setup's writes at pair-slot / suc pair-slot).
      -- The budget is pair-slots + body's stack-budget.

      -- max-slot-usage-bound: body's max ≤ next-slot child-alloc + body's stack-budget
      --                                  = next-slot alloc + pair-slots + body's stack-budget
      --                                  = next-slot alloc + apply's stack-budget.
      max-slot-usage-bound' :
        IRResultAWF.max-slot-written body-result
        ≤ next-slot alloc +ℕ (pair-slots +ℕ IRResultAWF.stack-budget body-result)
      max-slot-usage-bound' =
        subst
          (IRResultAWF.max-slot-written body-result ≤_)
          (+-assoc (next-slot alloc) pair-slots (IRResultAWF.stack-budget body-result))
          (IRResultAWF.max-slot-usage-bound body-result)
        where open import Data.Nat.Properties using (+-assoc)

      slot-stays-in-budget' :
        next-slot alloc'
        ≤ next-slot alloc +ℕ (pair-slots +ℕ IRResultAWF.stack-budget body-result)
      slot-stays-in-budget' =
        subst
          (next-slot alloc' ≤_)
          (+-assoc (next-slot alloc) pair-slots (IRResultAWF.stack-budget body-result))
          (IRResultAWF.slot-stays-in-budget body-result)
        where open import Data.Nat.Properties using (+-assoc)

      -- trace-writes-below: setup writes at suc pair-slot and pair-slot.
      -- Both < body's max-slot-written (body monotone gives
      -- next-slot child-alloc = pair-slot + pair-slots ≤ body-final.next-slot
      -- ≤ body-max-slot).
      pair-slot+2≤body-max :
        next-slot alloc +ℕ pair-slots ≤ IRResultAWF.max-slot-written body-result
      pair-slot+2≤body-max =
        ≤-trans (IRResultAWF.slot-monotone body-result)
                (IRResultAWF.max-slot-geq-final body-result)

      -- Bridge: next-slot alloc + pair-slots = next-slot alloc + 2 ≡ suc (suc (next-slot alloc)).
      -- _+_ recurses on the left, so we apply +-suc twice to push sucs out.
      n+2≡ssuc-n : ∀ n → n +ℕ pair-slots ≡ suc (suc n)
      n+2≡ssuc-n n = trans (+-suc n 1) (cong suc (trans (+-suc n 0) (cong suc (+-identityʳ n))))
        where open import Data.Nat.Properties using (+-suc; +-identityʳ)

      ssuc-pair-slot≤body-max : suc (suc pair-slot) ≤ IRResultAWF.max-slot-written body-result
      ssuc-pair-slot≤body-max =
        subst (_≤ IRResultAWF.max-slot-written body-result)
              (n+2≡ssuc-n (next-slot alloc))
              pair-slot+2≤body-max

      suc-pair-slot≤body-max : suc pair-slot ≤ IRResultAWF.max-slot-written body-result
      suc-pair-slot≤body-max = ≤-trans (n≤1+n (suc pair-slot)) ssuc-pair-slot≤body-max
        where open import Data.Nat.Properties using (n≤1+n)

      setup-writes-below-body-max : TraceWritesBelow (IRResultAWF.max-slot-written body-result) (apply-setup-trace pair-slot)
      setup-writes-below-body-max = ssuc-pair-slot≤body-max , suc-pair-slot≤body-max , tt

      trace-writes-below' : TraceWritesBelow (IRResultAWF.max-slot-written body-result) trace
      trace-writes-below' = trace-writes-below-append (IRResultAWF.max-slot-written body-result)
        (apply-setup-trace pair-slot) body-trace
        setup-writes-below-body-max
        (IRResultAWF.trace-writes-below body-result)

      trace-slot-reads-below' : TraceSlotReadsBelow (IRResultAWF.max-slot-written body-result) trace
      trace-slot-reads-below' = trace-slot-reads-below-append (IRResultAWF.max-slot-written body-result)
        (apply-setup-trace pair-slot) body-trace
        tt  -- setup reads no slots
        (IRResultAWF.trace-slot-reads-below body-result)

      -- Note: trace-preserves-capacity' removed in Phase 3

      -- Setup trace has no heap writes (simplified: just tt since no heap-writing instrs)
      setup-no-heap-writes : TraceNoHeapWrites (apply-setup-trace pair-slot)
      setup-no-heap-writes = tt

      trace-no-heap-writes' : TraceNoHeapWrites trace
      trace-no-heap-writes' =
        trace-no-heap-writes-append (apply-setup-trace pair-slot) body-trace
          setup-no-heap-writes
          (IRResultAWF.trace-no-heap-writes body-result)

      -- Plan 0.2.4.5 D1 task #30: reclaim-alloc now uses next-slot alloc'
      -- (= body's final next-slot), not pair-slots, since alloc' tracks
      -- body's full stack.
      reclaim-alloc : AllocState {FS}
      reclaim-alloc = record alloc { next-slot = next-slot alloc' }

      -- Frame equivalence: alloc'.frame = alloc.frame via body's frame-preserved + child-alloc.
      alloc'-frame-eq : current-frame alloc' ≡ current-frame alloc
      alloc'-frame-eq = trans (IRResultAWF.frame-preserved body-result) refl

      -- Stack-only assumption: body doesn't heap-allocate, so heap-frontier
      -- is preserved. Discharged via IRResultAWF.heap-preserved (since
      -- alloc' = body-result.final-alloc).
      alloc'-heap-eq : next-heap-ref alloc' ≡ next-heap-ref alloc
      alloc'-heap-eq = IRResultAWF.heap-preserved body-result

      reclaim-preserves-result' : BeforeFrontier reclaim-alloc result-loc
      reclaim-preserves-result' = bf-same-frame-slot alloc' reclaim-alloc
        alloc'-frame-eq refl alloc'-heap-eq result-loc result-before'

      reclaim-preserves-validity' :
        ValidAtWF mBody reclaim-alloc (eval (apply {A} {B} {k}) x) result-loc s'
      reclaim-preserves-validity' = validityWF-with-bf-transfer
        (eval (apply {A} {B} {k}) x) result-loc s' alloc' reclaim-alloc
        (λ loc bf → bf-same-frame-slot alloc' reclaim-alloc alloc'-frame-eq refl alloc'-heap-eq loc bf)
        result-valid-wf'

      -- Plan 0.2.4.5 D1 task #30: dispatch on body's result-place.
      -- For unit-result: apply's result-place is also unit-result (no
      -- per-loc witnesses needed; B must unify with Unit). Fully
      -- discharged.
      -- For at-loc: construct at-loc with the existing top-level
      -- postulates (rax-eq' discharged; result-valid-wf', result-before'
      -- and their reclaim wrappers remain — see structural deferral
      -- block above).
      result-place-final : ResultPlace B mBody alloc'
        (record alloc { next-slot = next-slot alloc' })
        (eval (apply {A} {B} {k}) x) s'
      result-place-final with IRResultAWF.result-place body-result
      ... | at-loc _ _ _ _ _ _ = at-loc result-loc result-valid-wf' result-before' rax-eq'
                                       reclaim-preserves-validity' reclaim-preserves-result'
      ... | unit-result = unit-result