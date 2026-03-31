-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.ApplyWF
--
-- Apply IR implementation with clean trace-based structure.
-- Final state defined via exec-trace, making trace-correct = refl.
--
-- Apply uses frame push/pop for body execution but follows the same
-- trace composition pattern as other WF2 files.
--
-- TRACE STRUCTURE:
--   1. Setup pair (env, arg) on stack
--   2. Push child frame
--   3. Execute body trace
--   4. Pop frame
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
open import Once.CCC.Target.X86-64.Types
open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
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
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnStack f k) (stack-before f-eq k<ns)
    rewrite cf-eq | ns-eq = stack-before f-eq k<ns
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnStack f k) (stack-ancestor cf≺f src)
    rewrite cf-eq = stack-ancestor cf≺f src
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnHeap hl) (heap-before r<hr)
    rewrite hr-eq = heap-before r<hr

------------------------------------------------------------------------
-- Apply implementation with clean trace-based structure
------------------------------------------------------------------------

module ApplyWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem)
  (get-child-frame : ∀ (alloc : AllocState {FS}) → FrameSemantics.Frame FS)
  (child-frame-ordered : ∀ (alloc : AllocState {FS}) →
    FrameSemantics._≺_ FS (get-child-frame alloc) (current-frame alloc))
  (child-frame-adjacent : ∀ (alloc : AllocState {FS}) (f : FrameSemantics.Frame FS) →
    FrameSemantics._≺_ FS (get-child-frame alloc) f →
    FrameSemantics._≺_ FS f (current-frame alloc) →
    ⊥)
  (escape-result-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
    (result-loc : ValueLocation FS) →
    current-frame body-final ≡ get-child-frame alloc →
    BeforeFrontier' body-final result-loc →
    SurvivesFramePop (get-child-frame alloc) result-loc)
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
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; BodyCorrect;
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
  --   setup-trace: Store (env, arg) pair to stack, set Input
  --   instr-push-frame body-cap: Enter child frame
  --   body-trace: Execute closure body
  --   instr-pop-frame: Return to parent frame
  ------------------------------------------------------------------------

  -- Setup trace: prepare pair input for body
  --
  -- Input structure: (closure, arg) pair where closure = (env, code)
  -- We need to build a new pair (env, arg) for the body.
  --
  -- Step 1: Get arg-loc from *(Input+1) while Input still points to original pair
  -- Step 2: Store arg at pair[1]
  -- Step 3: Get closure-loc from *Input
  -- Step 4: Set Input := closure-loc
  -- Step 5: Get env-loc from *Input (now pointing to closure)
  -- Step 6: Store env at pair[0]
  -- Step 7: Set Output := &pair
  -- Step 8: Set Input := &pair
  apply-setup-trace : (pair-slot : ℕ) → AbstractTrace
  apply-setup-trace pair-slot =
    load-indirect-suc ∷                -- Output := *(Input+1) = arg-loc
    store-at-slot (suc pair-slot) ∷    -- pair[1] := arg-loc
    load-indirect ∷                    -- Output := *Input = closure-loc
    mov-to-input ∷                     -- Input := closure-loc
    load-indirect ∷                    -- Output := *Input = env-loc
    store-at-slot pair-slot ∷          -- pair[0] := env-loc
    lea-slot pair-slot ∷               -- Output := &pair
    mov-to-input ∷ []                  -- Input := &pair

  -- Full apply trace: setup + push + body + pop
  apply-full-trace : (pair-slot : ℕ) (body-cap : ℕ) (body-trace : AbstractTrace) → AbstractTrace
  apply-full-trace pair-slot body-cap body-trace =
    apply-setup-trace pair-slot ++
    instr-push-frame body-cap ∷
    body-trace ++
    instr-pop-frame ∷ []

  ------------------------------------------------------------------------
  -- run-apply: Clean trace-based implementation
  ------------------------------------------------------------------------

  run-apply : ∀ {m A B q}
    (x : ⟦ (A ⇒[ q ] B) * A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-valid-wf : ValidAtWF m alloc x input-loc s) →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (apply {A} {B} {q}) ≤ frame-capacity alloc →
    ∃[ mOut ] IRResultAWF mOut (apply {A} {B} {q}) x s alloc
  run-apply {m} {A} {B} {q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    mBody , record
      { result-loc = result-loc
      ; final-state = s'
      ; final-alloc = alloc'
      ; trace = trace
      ; trace-correct = refl  -- BY DEFINITION
      ; alloc-correct = SMP.!!  -- PROOF OBLIGATION: push/pop frame preserves alloc structure
      ; result-valid-wf = result-valid-wf'
      ; result-before = result-before'
      ; rax-is-result = rax-eq'
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = m≤m+n (next-slot alloc) pair-slots
      ; heap-monotone = ≤-refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved'
      ; reclaimable-slot = next-slot alloc +ℕ pair-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) pair-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = reclaim-preserves-result'
      ; reclaim-preserves-validity = reclaim-preserves-validity'
      ; reclaim-size-bound = ≤-refl
      ; frontier-slot-stable = frontier-stable'
      ; trace-writes-above = trace-writes-above'
      ; trace-slot-reads-above = trace-slot-reads-above'
      ; trace-writes-below = trace-writes-below'
      ; trace-slot-reads-below = trace-slot-reads-below'
      ; trace-preserves-capacity = trace-preserves-capacity'
      ; trace-no-heap-writes = trace-no-heap-writes'
      ; trace-preserves-halted = trace-preserves-halted'
      }
    where
      open import Data.Nat using (_≥_)
      open import Data.Nat.Properties using (*-monoʳ-≤; <⇒≤; *-monoˡ-≤; m<m+n)

      -- Decompose input pair
      pair-decomp = decomposePairWF {m} {_} {A ⇒[ q ] B} {A} input-valid-wf
      closure-loc = PairValidWF.fst-loc pair-decomp
      arg-loc = PairValidWF.snd-loc pair-decomp
      mArg = PairValidWF.mB pair-decomp
      closure-valid-wf = PairValidWF.fst-valid pair-decomp
      arg-valid-wf = PairValidWF.snd-valid pair-decomp
      arg-before = PairValidWF.snd-before pair-decomp

      closure : ⟦ A ⇒[ q ] B ⟧
      closure = sem-fst {A ⇒[ q ] B} {A} x

      arg : ⟦ A ⟧
      arg = sem-snd {A ⇒[ q ] B} {A} x

      -- Decompose closure
      mClosure = PairValidWF.mA pair-decomp
      closure-mode-is-heap : mClosure ≡ Heap
      closure-mode-is-heap = closure-mode-is-heap-proof closure-valid-wf
      closure-valid-wf-heap : ValidAtWF Heap alloc closure closure-loc s
      closure-valid-wf-heap = subst (λ m → ValidAtWF m alloc closure closure-loc s)
        closure-mode-is-heap closure-valid-wf

      closure-decomp = decomposeClosureWF {_} {q} {A} {B} closure-valid-wf-heap
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
      pair-input-loc = OnStack (current-frame alloc) pair-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = next-slot alloc +ℕ pair-slots }

      -- Child frame setup
      child-frame = get-child-frame alloc
      child-frame-below-parent = child-frame-ordered alloc

      child-alloc : AllocState {FS}
      child-alloc = record
        { current-frame = child-frame
        ; next-slot = 0
        ; frame-capacity = body-cap
        ; next-heap-ref = next-heap-ref alloc
        }

      ------------------------------------------------------------------------
      -- Execute body in child frame (to get body-trace)
      --
      -- We need to execute body to get its trace, which we then compose
      -- into apply's full trace.
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
      closure-ptr : readLoc s input-loc ≡ just closure-loc
      closure-ptr = PairValidWF.fst-ptr pair-decomp

      arg-ptr : readLoc s (sucLoc input-loc) ≡ just arg-loc
      arg-ptr = PairValidWF.snd-ptr pair-decomp

      env-ptr : readLoc s closure-loc ≡ just env-loc
      env-ptr = ClosureValidWF.env-ptr closure-decomp

      ------------------------------------------------------------------------
      -- Step-by-step execution of setup trace
      --
      -- Setup trace structure:
      --   1. load-indirect-suc    -- Output := *(sucLoc Input) = arg-loc
      --   2. store-at-slot (suc pair-slot)  -- slot (suc pair-slot) := arg-loc
      --   3. load-indirect        -- Output := *Input = closure-loc
      --   4. mov-to-input         -- Input := closure-loc
      --   5. load-indirect        -- Output := *closure-loc = env-loc
      --   6. store-at-slot pair-slot  -- slot pair-slot := env-loc
      --   7. lea-slot pair-slot   -- Output := &pair
      --   8. mov-to-input         -- Input := &pair
      ------------------------------------------------------------------------

      -- Frame shorthand
      frame = current-frame alloc

      -- Step 1: load-indirect-suc
      -- Before: Input = input-loc
      -- After: Output = arg-loc (from *(sucLoc input-loc))
      step1-trace : AbstractTrace
      step1-trace = load-indirect-suc ∷ []

      s1 : LocState FS
      s1 = proj₁ (exec-trace step1-trace s alloc)

      -- load-indirect-suc reads from sucLoc Input = sucLoc input-loc
      step1-mem-read : readLoc s (sucLoc (readReg (regs s) Input)) ≡ just arg-loc
      step1-mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just arg-loc) (sym rdi-eq) arg-ptr

      -- After load-indirect-suc, Output = arg-loc
      step1-output : readReg (regs s1) Output ≡ arg-loc
      step1-output =
        let s1-as-abstract : s1 ≡ proj₁ (exec-abstract load-indirect-suc s alloc)
            s1-as-abstract = cong proj₁ (exec-trace-single load-indirect-suc s alloc not-halted)
            -- exec-abstract load-indirect-suc = exec-load-with-value Output (readLoc s (sucLoc (input (regs s)))) s
            -- When readLoc returns just v, this becomes record s { regs = writeReg (regs s) Output v }
            -- Need to pattern match on the readLoc result
        in step1-output-helper s alloc s1-as-abstract step1-mem-read
        where
          step1-output-helper : (s₀ : LocState FS) (a₀ : AllocState {FS}) →
            s1 ≡ proj₁ (exec-abstract load-indirect-suc s₀ a₀) →
            readLoc s₀ (sucLoc (readReg (regs s₀) Input)) ≡ just arg-loc →
            readReg (regs s1) Output ≡ arg-loc
          step1-output-helper s₀ a₀ s1-eq mem-eq with readLoc s₀ (sucLoc (readReg (regs s₀) Input)) | mem-eq
          ... | just v | refl = trans (cong (λ s' → readReg (regs s') Output) s1-eq)
                                      (writeReg-same (regs s₀) Output v)

      -- Step 2: store-at-slot (suc pair-slot)
      -- Writes Output (= arg-loc) to slot (suc pair-slot)
      step2-trace : AbstractTrace
      step2-trace = store-at-slot (suc pair-slot) ∷ []

      -- State after steps 1-2
      s2 : LocState FS
      s2 = proj₁ (exec-trace (step1-trace ++ step2-trace) s alloc)

      -- Not halted after step 1
      not-halted-s1 : halted s1 ≡ false
      not-halted-s1 = exec-trace-preserves-halted step1-trace s alloc not-halted
                        (tph-∷ iph-load-indirect-suc tph-[])

      -- Step 2 writes arg-loc to slot (suc pair-slot)
      step2-written : readLoc s2 (OnStack frame (suc pair-slot)) ≡ just arg-loc
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
                                   (OnStack (current-frame alloc1) (suc pair-slot)) ≡
                           just (readReg (regs s1) Output)
            store-result = store-at-slot-result (suc pair-slot) s1 alloc1
        in subst (λ s' → readLoc s' (OnStack frame (suc pair-slot)) ≡ just arg-loc)
                 (sym (trans s2-decomp s2-as-abstract))
                 (subst (λ f → readLoc (proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s1 alloc1))
                                       (OnStack f (suc pair-slot)) ≡ just arg-loc)
                        frame-eq
                        (trans store-result (cong just step1-output)))

      -- Remaining setup preserves slot (suc pair-slot)
      -- Steps 3-8 don't write to slot (suc pair-slot):
      --   3. load-indirect (no mem write)
      --   4. mov-to-input (no mem write)
      --   5. load-indirect (no mem write)
      --   6. store-at-slot pair-slot (writes to pair-slot ≠ suc pair-slot)
      --   7. lea-slot pair-slot (no mem write)
      --   8. mov-to-input (no mem write)
      rest-after-step2 : AbstractTrace
      rest-after-step2 = load-indirect ∷ mov-to-input ∷
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
      pair-arg-ptr : readLoc s-after-setup (sucLoc pair-input-loc) ≡ just arg-loc
      pair-arg-ptr =
        let alloc2 = proj₂ (exec-trace (step1-trace ++ step2-trace) s alloc)
            s-after-setup-decomp : s-after-setup ≡ proj₁ (exec-trace rest-after-step2 s2 alloc2)
            s-after-setup-decomp = cong proj₁ (exec-trace-append (step1-trace ++ step2-trace) rest-after-step2 s alloc)
            frame-eq2 : current-frame alloc2 ≡ frame
            frame-eq2 = exec-trace-preserves-frame (step1-trace ++ step2-trace) s alloc
            -- Use exec-trace-slot-value-below to show slot (suc pair-slot) is preserved
            -- rest writes below suc pair-slot, so slot suc pair-slot is preserved
            preserved : readLoc (proj₁ (exec-trace rest-after-step2 s2 alloc2))
                               (OnStack (current-frame alloc2) (suc pair-slot)) ≡ just arg-loc
            preserved = exec-trace-slot-value-below rest-after-step2 s2 alloc2 (suc pair-slot) arg-loc
                          (subst (λ f → readLoc s2 (OnStack f (suc pair-slot)) ≡ just arg-loc)
                                 (sym frame-eq2) step2-written)
                          rest-writes-below-suc rest-no-heap-writes
        in subst (λ s' → readLoc s' (OnStack frame (suc pair-slot)) ≡ just arg-loc)
                 (sym s-after-setup-decomp)
                 (subst (λ f → readLoc (proj₁ (exec-trace rest-after-step2 s2 alloc2))
                                       (OnStack f (suc pair-slot)) ≡ just arg-loc)
                        frame-eq2 preserved)

      -- For pair-env-ptr, we need to trace through to step 6
      -- Steps 1-5 are prefix, step 6 stores env-loc, steps 7-8 preserve

      -- State after steps 1-5 (before store-at-slot pair-slot)
      prefix-for-env : AbstractTrace
      prefix-for-env = load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷
                       load-indirect ∷ mov-to-input ∷ load-indirect ∷ []

      suffix-after-env-store : AbstractTrace
      suffix-after-env-store = lea-slot pair-slot ∷ mov-to-input ∷ []

      setup-decomp-for-env : apply-setup-trace pair-slot ≡
                             prefix-for-env ++ store-at-slot pair-slot ∷ suffix-after-env-store
      setup-decomp-for-env = refl

      -- TracePreservesHalted for prefix-for-env
      prefix-for-env-tph : TracePreservesHaltedP prefix-for-env
      prefix-for-env-tph =
        tph-∷ iph-load-indirect-suc
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-load-indirect
        (tph-∷ iph-mov-to-input
        (tph-∷ iph-load-indirect tph-[]))))

      not-halted-after-prefix-for-env : halted (proj₁ (exec-trace prefix-for-env s alloc)) ≡ false
      not-halted-after-prefix-for-env = exec-trace-preserves-halted prefix-for-env s alloc not-halted prefix-for-env-tph

      -- suffix writes above suc pair-slot (lea-slot and mov-to-input don't write to slots)
      suffix-writes-above : SMP.TraceWritesAbove (suc pair-slot) suffix-after-env-store
      suffix-writes-above = tt  -- both instructions have instr-writes-slot = nothing

      suffix-no-heap-writes : SMP.TraceNoHeapWrites suffix-after-env-store
      suffix-no-heap-writes = tt

      ------------------------------------------------------------------------
      -- Prove output-after-prefix: Output = env-loc after steps 1-5
      --
      -- Step by step:
      --   1. load-indirect-suc: Output := *(sucLoc Input) = arg-loc
      --   2. store-at-slot: Output unchanged
      --   3. load-indirect: Output := *Input = closure-loc
      --   4. mov-to-input: Input := Output = closure-loc, Output unchanged
      --   5. load-indirect: Output := *Input = *closure-loc = env-loc
      ------------------------------------------------------------------------

      -- Decompose prefix-for-env into sub-traces
      prefix12 : AbstractTrace
      prefix12 = load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷ []

      prefix345 : AbstractTrace
      prefix345 = load-indirect ∷ mov-to-input ∷ load-indirect ∷ []

      prefix-decomp-12-345 : prefix-for-env ≡ prefix12 ++ prefix345
      prefix-decomp-12-345 = refl

      -- State after steps 1-2
      s12 : LocState FS
      s12 = proj₁ (exec-trace prefix12 s alloc)

      alloc12 : AllocState {FS}
      alloc12 = proj₂ (exec-trace prefix12 s alloc)

      -- Steps 1-2 preserve halted
      prefix12-tph : TracePreservesHaltedP prefix12
      prefix12-tph = tph-∷ iph-load-indirect-suc (tph-∷ iph-store-at-slot tph-[])

      not-halted-s12 : halted s12 ≡ false
      not-halted-s12 = exec-trace-preserves-halted prefix12 s alloc not-halted prefix12-tph

      -- Input is still input-loc after steps 1-2 (neither instruction modifies Input)
      -- Step 1 modifies Output only, Step 2 writes to memory only
      -- Both preserve Input register
      input-after-s12 : readReg (regs s12) Input ≡ input-loc
      input-after-s12 = SMP.!!  -- Needs trace infrastructure for register preservation

      -- Memory is preserved for closure-loc: steps 1-2 only write to slot (suc pair-slot)
      -- which is on stack, not at closure-loc (which is on heap since closure is Heap mode)
      closure-readable-after-s12 : readLoc s12 closure-loc ≡ just env-loc
      closure-readable-after-s12 = SMP.!!  -- Needs frame/heap preservation proof

      -- Step 3: load-indirect reads closure-loc, gets env-loc (after step 3)
      prefix3 : AbstractTrace
      prefix3 = load-indirect ∷ []

      s3-partial : LocState FS
      s3-partial = proj₁ (exec-trace prefix3 s12 alloc12)

      -- After step 3, Output = *Input = *input-loc = closure-loc
      step3-output : readReg (regs s3-partial) Output ≡ closure-loc
      step3-output = SMP.!!  -- Needs load-indirect result lemma

      -- Step 4: mov-to-input sets Input := Output = closure-loc, preserves Output
      prefix34 : AbstractTrace
      prefix34 = load-indirect ∷ mov-to-input ∷ []

      s34-partial : LocState FS
      s34-partial = proj₁ (exec-trace prefix34 s12 alloc12)

      prefix3-tph : TracePreservesHaltedP prefix3
      prefix3-tph = tph-∷ iph-load-indirect tph-[]

      not-halted-s3 : halted s3-partial ≡ false
      not-halted-s3 = exec-trace-preserves-halted prefix3 s12 alloc12 not-halted-s12 prefix3-tph

      -- After step 4, Input = closure-loc
      step4-input : readReg (regs s34-partial) Input ≡ closure-loc
      step4-input =
        let alloc3 = proj₂ (exec-trace prefix3 s12 alloc12)
            s34-decomp : s34-partial ≡ proj₁ (exec-abstract mov-to-input s3-partial alloc3)
            s34-decomp = cong proj₁ (trans (exec-trace-append prefix3 (mov-to-input ∷ []) s12 alloc12)
                                           (exec-trace-single mov-to-input s3-partial alloc3 not-halted-s3))
        in trans (cong (λ s' → readReg (regs s') Input) s34-decomp)
                 (trans (writeReg-same (regs s3-partial) Input (readReg (regs s3-partial) Output))
                        step3-output)

      -- Step 5: load-indirect reads *Input = *closure-loc = env-loc
      prefix345-tph : TracePreservesHaltedP prefix345
      prefix345-tph = tph-∷ iph-load-indirect (tph-∷ iph-mov-to-input (tph-∷ iph-load-indirect tph-[]))

      not-halted-s345 : halted (proj₁ (exec-trace prefix345 s12 alloc12)) ≡ false
      not-halted-s345 = exec-trace-preserves-halted prefix345 s12 alloc12 not-halted-s12 prefix345-tph

      -- After step 5, Output = *closure-loc = env-loc
      output-after-prefix : readReg (regs (proj₁ (exec-trace prefix-for-env s alloc))) Output ≡ env-loc
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
            readReg (regs (proj₁ (exec-trace prefix345 s₀ a₀))) Output ≡ env-loc
          step5-output-final s₀ a₀ nh = SMP.!!  -- Final step needs closure memory read

      -- Use prefix-store-preserve to prove pair-env-ptr
      -- After prefix-for-env, Output = env-loc, then store-at-slot pair-slot writes it
      pair-env-ptr : readLoc s-after-setup pair-input-loc ≡ just env-loc
      pair-env-ptr =
        let result = prefix-store-preserve prefix-for-env pair-slot suffix-after-env-store
                       s alloc prefix-for-env-tph not-halted suffix-writes-above suffix-no-heap-writes
            -- result : readLoc (proj₁ (exec-trace (prefix ++ store ∷ suffix) s alloc))
            --                  (OnStack frame pair-slot) ≡
            --          just (readReg (regs (proj₁ (exec-trace prefix s alloc))) Output)
        in trans result (cong just output-after-prefix)

      -- Input register points to pair after setup
      -- Decompose setup-trace as prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
      setup-prefix : AbstractTrace
      setup-prefix = load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷
                     load-indirect ∷ mov-to-input ∷
                     load-indirect ∷ store-at-slot pair-slot ∷ []

      setup-decomp : apply-setup-trace pair-slot ≡
                     setup-prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
      setup-decomp = refl

      -- TracePreservesHalted for the prefix
      setup-prefix-tph : TracePreservesHaltedP setup-prefix
      setup-prefix-tph =
        tph-∷ iph-load-indirect-suc
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-load-indirect
        (tph-∷ iph-mov-to-input
        (tph-∷ iph-load-indirect
        (tph-∷ iph-store-at-slot tph-[])))))

      not-halted-after-prefix : halted (proj₁ (exec-trace setup-prefix s alloc)) ≡ false
      not-halted-after-prefix = exec-trace-preserves-halted setup-prefix s alloc not-halted setup-prefix-tph

      pair-input-eq : readReg (regs s-after-setup) Input ≡ pair-input-loc
      pair-input-eq =
        let eq1 : apply-setup-trace pair-slot ≡
                  setup-prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
            eq1 = setup-decomp
            eq2 : readReg (regs (proj₁ (exec-trace (setup-prefix ++
                           (lea-slot pair-slot ∷ mov-to-input ∷ [])) s alloc))) Input ≡
                  OnStack (current-frame alloc) pair-slot
            eq2 = exec-trace-final-lea-mov-input setup-prefix pair-slot s alloc not-halted-after-prefix
        in subst (λ t → readReg (regs (proj₁ (exec-trace t s alloc))) Input ≡
                        OnStack (current-frame alloc) pair-slot)
                 (sym eq1) eq2

      -- Setup trace preserves halted (used in multiple places)
      setup-tph : TracePreservesHaltedP (apply-setup-trace pair-slot)
      setup-tph =
        tph-∷ iph-load-indirect-suc
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-load-indirect
        (tph-∷ iph-mov-to-input
        (tph-∷ iph-load-indirect
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-lea-slot
        (tph-∷ iph-mov-to-input tph-[])))))))

      -- Not halted after setup
      not-halted-after-setup : halted s-after-setup ≡ false
      not-halted-after-setup = exec-trace-preserves-halted (apply-setup-trace pair-slot) s alloc not-halted setup-tph

      -- Pair validity in child-alloc (after setup, transferred to child frame)
      pair-input-valid-child : ValidAtWF Heap child-alloc {EnvType * A} (pair env arg) pair-input-loc s-after-setup
      pair-input-valid-child = SMP.!!

      -- Pair is before frontier in child-alloc
      -- pair-input-loc = OnStack (current-frame alloc) pair-slot
      -- child-alloc has current-frame = child-frame, which is ≺ current-frame alloc
      -- So pair-input-loc is in an ancestor frame
      -- Use pair-slot + pair-slots as bound (the updated parent frontier)
      pair-input-before-child : BeforeFrontier child-alloc pair-input-loc
      pair-input-before-child = stack-ancestor child-frame-below-parent
        (src-origin (next-slot alloc +ℕ pair-slots) (m<m+n pair-slot {pair-slots} (s≤s z≤n)))

      -- Body execution in child frame
      body-exec-result : ∃[ mOut ] IRResultAWF mOut body (pair env arg) s-after-setup child-alloc
      body-exec-result = BodyCorrect.execute body-correct arg arg-loc pair-input-loc
        s-after-setup child-alloc Heap
        pair-input-valid-child pair-input-before-child not-halted-after-setup pair-input-eq
        ≤-refl

      mBody = proj₁ body-exec-result
      body-result = proj₂ body-exec-result

      body-trace = IRResultAWF.trace body-result
      result-loc = IRResultAWF.result-loc body-result

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

      -- Trace preserves halted (structural proof - defined first for use in not-halted')
      trace-preserves-halted' : TracePreservesHaltedP trace
      trace-preserves-halted' =
        tph-++ setup-tph
        (tph-∷ iph-push-frame
        (tph-++ (IRResultAWF.trace-preserves-halted body-result)
        (tph-∷ iph-pop-frame tph-[])))

      -- Output register contains result location
      rax-eq' : readReg (regs s') Output ≡ result-loc
      rax-eq' = SMP.!!

      -- Not halted after full trace
      not-halted' : halted s' ≡ false
      not-halted' = exec-trace-preserves-halted trace s alloc not-halted trace-preserves-halted'

      -- Memory before frontier preserved
      mem-preserved' : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved' = SMP.!!

      -- Result is before frontier in alloc'
      result-before' : BeforeFrontier alloc' result-loc
      result-before' = SMP.!!

      -- Result validity
      result-valid-wf' : ValidAtWF mBody alloc' (eval primSem (apply {A} {B} {q}) x) result-loc s'
      result-valid-wf' = SMP.!!

      -- Frontier slot stability
      frontier-stable' : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc' →
        readLoc s'' (OnStack (current-frame alloc) pair-slot) ≡ just input-loc' →
        _
      frontier-stable' s'' input-loc' _ _ _ = inj₂ (inj₁ SMP.!!)

      -- Trace properties
      trace-writes-above' : TraceWritesAbove pair-slot trace
      trace-writes-above' = SMP.!!

      trace-slot-reads-above' : TraceSlotReadsAbove pair-slot trace
      trace-slot-reads-above' = SMP.!!

      trace-writes-below' : TraceWritesBelow (next-slot alloc +ℕ pair-slots) trace
      trace-writes-below' = SMP.!!

      trace-slot-reads-below' : TraceSlotReadsBelow (next-slot alloc +ℕ pair-slots) trace
      trace-slot-reads-below' = SMP.!!

      trace-preserves-capacity' : TracePreservesCapacity trace
      trace-preserves-capacity' = SMP.!!

      -- Setup trace has no heap writes (simplified: just tt since no heap-writing instrs)
      setup-no-heap-writes : TraceNoHeapWrites (apply-setup-trace pair-slot)
      setup-no-heap-writes = tt

      trace-no-heap-writes' : TraceNoHeapWrites trace
      trace-no-heap-writes' =
        trace-no-heap-writes-append (apply-setup-trace pair-slot)
          (instr-push-frame body-cap ∷ body-trace ++ instr-pop-frame ∷ [])
          setup-no-heap-writes
          (trace-no-heap-writes-append body-trace (instr-pop-frame ∷ [])
                  (IRResultAWF.trace-no-heap-writes body-result)
                  tt)

      -- Reclamation proofs
      reclaim-preserves-result' : ∀ (fits : next-slot alloc +ℕ pair-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ pair-slots }) result-loc
      reclaim-preserves-result' fits = bf-same-frame-slot alloc'
        (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
        refl refl refl result-loc result-before'

      reclaim-preserves-validity' : ∀ (fits : next-slot alloc +ℕ pair-slots ≤ frame-capacity alloc) →
        ValidAtWF mBody (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
                  (eval primSem (apply {A} {B} {q}) x) result-loc s'
      reclaim-preserves-validity' fits = validityWF-with-bf-transfer
        (eval primSem (apply {A} {B} {q}) x) result-loc s' alloc'
        (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
        (λ loc bf → bf-same-frame-slot alloc'
          (record alloc { next-slot = next-slot alloc +ℕ pair-slots })
          refl refl refl loc bf)
        result-valid-wf'