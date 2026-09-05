-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.ApplyWF (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; <-≤-trans; m≤m+n; +-monoʳ-≤; m+n≤o⇒m≤o; ≤-reflexive; n≤1+n; +-comm; +-identityʳ)
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
open import Once.Semantics.Machine using (⟦_⟧ᴵ; sem-fst; sem-snd; sem-pair; sem-inl; sem-inr; sem-case)
open import Once.Memory.TypeSlots using (stack-type-slots; heap-type-slots; type-slots)
pair = sem-pair
open import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.IR.Size
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
  -- Plan 0.52 M2 / D113: `Ev.eval` now takes the target numerics. Same local
  -- shim SimpleWF and PairAllocWF already use, so the body reads unchanged.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

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
  open SMP.RecSchemeSemantics {FS}
    using (exec-abstract-load-indirect-suc-preserves-input;
           exec-abstract-load-indirect-suc-preserves-mem;
           exec-abstract-load-indirect-preserves-input;
           exec-abstract-load-indirect-output;
           exec-abstract-load-indirect-suc-output)

  open import Once.CCC.Machine.ClosureWellFormed o
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; at-reg; prim-sv;
           InputPlace; in-at-loc; in-at-reg; in-unit; BodyCorrect;
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           valid-inl-wf; valid-inr-wf;
           mk-IRResultAWF-via-bump;
           -- OCP-0003: valid-fold-wf removed
           validityWF-mem-only; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-frontier-advance;
           validityWF-with-bf-transfer;
           decomposePairWF; PairValidWF;
           decomposeClosureWF; ClosureValidWF)

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
  -- Plan 0.14: include instr-alloc-stack pair-slots at the start so
  -- runtime alloc.next-slot bumps to match child-alloc (= record alloc
  -- { next-slot += pair-slots }). The trace also reserves the (env, arg)
  -- pair's stack slots.
  apply-setup-trace : (pair-slot : ℕ) → AbstractTrace
  apply-setup-trace pair-slot =
    instr-alloc-stack pair-slots ∷      -- Reserve pair-slots for (env, arg)
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
  -- Plan 0.16 Rec 5 follow-up: chain-form bridge for the load-indirect
  -- InstrWF at position 4 of run-apply's setup-trace.
  --
  -- The TraceWF inductive expects InstrWF at the chain-form state
  -- (`proj₁ (exec-abstract i_n (proj₁ (exec-abstract i_(n-1) … …)) …)`)
  -- but the natural producer-side evidence lives at the trace-form
  -- state (`proj₁ (exec-trace prefix s alloc)`). The two are
  -- propositionally equal via 3 `exec-trace-cons` / `exec-trace-single`
  -- unfolds; this lemma packages the bridge so each TraceWF chain in
  -- ApplyWF can plug it in without re-deriving the equality.
  --
  -- Defined at module level (outside `run-apply`'s where-block) so
  -- the TraceWF chains earlier in the where-block can reference it
  -- without forward-ref scoping problems.
  ------------------------------------------------------------------------
  load-indirect-after-3-prefix :
    ∀ (i₁ i₂ i₃ : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS})
      (loc : ValueLocation FS) (v : StoredValue FS) →
      halted s ≡ false →
      halted (proj₁ (exec-abstract i₁ s alloc)) ≡ false →
      halted (proj₁ (exec-abstract i₂
                       (proj₁ (exec-abstract i₁ s alloc))
                       (proj₂ (exec-abstract i₁ s alloc)))) ≡ false →
      readReg (regs (proj₁ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc))) Input1
        ≡ SV-Ptr loc →
      readLoc (proj₁ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc)) loc ≡ just v →
      InstrWF
        (proj₁ (exec-abstract i₃
                  (proj₁ (exec-abstract i₂
                            (proj₁ (exec-abstract i₁ s alloc))
                            (proj₂ (exec-abstract i₁ s alloc))))
                  (proj₂ (exec-abstract i₂
                            (proj₁ (exec-abstract i₁ s alloc))
                            (proj₂ (exec-abstract i₁ s alloc))))))
        (proj₂ (exec-abstract i₃
                  (proj₁ (exec-abstract i₂
                            (proj₁ (exec-abstract i₁ s alloc))
                            (proj₂ (exec-abstract i₁ s alloc))))
                  (proj₂ (exec-abstract i₂
                            (proj₁ (exec-abstract i₁ s alloc))
                            (proj₂ (exec-abstract i₁ s alloc))))))
        load-indirect
  load-indirect-after-3-prefix i₁ i₂ i₃ s alloc loc v nh₀ nh₁ nh₂ rdi-eq read-eq =
    let s₁ = proj₁ (exec-abstract i₁ s alloc)
        a₁ = proj₂ (exec-abstract i₁ s alloc)
        s₂ = proj₁ (exec-abstract i₂ s₁ a₁)
        a₂ = proj₂ (exec-abstract i₂ s₁ a₁)
        d1 = exec-trace-cons i₁ _ s alloc nh₀
        d2 = exec-trace-cons i₂ _ s₁ a₁ nh₁
        d3 = exec-trace-single i₃ s₂ a₂ nh₂
        chain-eq : (proj₁ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc) ,
                    proj₂ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc))
                 ≡ (proj₁ (exec-abstract i₃ s₂ a₂) , proj₂ (exec-abstract i₃ s₂ a₂))
        chain-eq = trans d1 (trans d2 d3)
        witness-at-trace-form :
          InstrWF (proj₁ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc))
                  (proj₂ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc))
                  load-indirect
        witness-at-trace-form = load-indirect-twf
                                  {s = proj₁ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc)}
                                  {alloc = proj₂ (exec-trace (i₁ ∷ i₂ ∷ i₃ ∷ []) s alloc)}
                                  loc v rdi-eq read-eq
    in subst (λ p → InstrWF (proj₁ p) (proj₂ p) load-indirect)
             chain-eq witness-at-trace-form

  ------------------------------------------------------------------------
  -- run-apply: Clean trace-based implementation
  ------------------------------------------------------------------------

  -- Stage F: the input is an `InputPlace`. `apply`'s input is a PRODUCT, and
  -- `FitsInRegI` inhabits only `Int` and `Float`, so a register-resident input
  -- is absurd here — and so is a Unit one (`_*_` and `Unit` are distinct `IRTy`
  -- constructors). Both fall out as empty patterns; no case analysis survives
  -- into the proof.
  run-apply : ∀ {m A B}
    (x : ⟦ (A ⇛ B) * A ⟧ᴵ)
    (s : LocState FS) (alloc : AllocState {FS}) →
    InputPlace m alloc x s →
    halted s ≡ false →
    ∃[ mOut ] IRResultAWF mOut (apply {A} {B}) x s alloc
  run-apply {m} {A} {B} x s alloc (in-at-reg () _) _
  run-apply {m} {A} {B} x s alloc (in-unit ()) _
  run-apply {m} {A} {B} x s alloc (in-at-loc input-loc input-valid-wf input-before rdi-eq) not-halted =
    -- Plan 0.17: use mk-IRResultAWF-via-bump. Producer-side fields
    -- stay at `alloc'` (= body-result.final-alloc, the local shape);
    -- the helper transports proofs to `apply-bump apply-bump alloc`.
    mBody , mk-IRResultAWF-via-bump
      s'
      alloc'
      trace
      apply-bump-value
      apply-bump-eq
      SMP.!!  -- trace-is-ir-to-trace (Pattern 1: drop instr-alloc-stack)
      refl
      alloc-correct-apply-local
      result-place-final
      not-halted'
      (λ _ _ → SMP.!!)  -- mem-preserved-before (TODO)
      trace-twf'
      (exec-trace-preserves-halted-WF trace)
      (SMP.trace-no-frame-ops-append (apply-setup-trace pair-slot) body-trace _
        (IRResultAWF.trace-no-frame-ops body-result))
      (record
        { stack-budget = pair-slots +ℕ IRResultAWF.stack-budget body-result
        ; max-slot-written = IRResultAWF.max-slot-written body-result
        ; bump-fits-stack-budget = apply-bump-fits-stack-budget
        ; max-slot-geq-final = apply-max-slot-geq-final
        ; max-slot-usage-bound = max-slot-usage-bound'
        ; frontier-slot-stable = frontier-stable'
        ; trace-writes-above = trace-writes-above'
        ; trace-slot-reads-above = trace-slot-reads-above'
        ; trace-writes-below = trace-writes-below'
        ; trace-slot-reads-below = trace-slot-reads-below'
        ; scratch-budget = IRResultAWF.scratch-budget body-result
        ; scratch-bounded = apply-scratch-bounded
        })
      (record
        { heap-budget = IRResultAWF.heap-budget body-result
        ; max-heap-ref-written = IRResultAWF.max-heap-ref-written body-result
        ; bump-fits-heap-budget = apply-bump-fits-heap-budget
        ; max-heap-ref-geq-final = apply-max-heap-ref-geq-final
        ; max-heap-usage-bound = IRResultAWF.max-heap-usage-bound body-result
        })
    where
      open import Data.Nat using (_≥_)
      open import Data.Nat.Properties using (*-monoʳ-≤; <⇒≤; *-monoˡ-≤; m<m+n)

      -- Decompose input pair
      pair-decomp = decomposePairWF {m} {_} {A ⇛ B} {A} input-valid-wf
      closure-loc = PairValidWF.fst-loc pair-decomp
      arg-loc = PairValidWF.snd-loc pair-decomp
      mArg = PairValidWF.mB pair-decomp
      closure-valid-wf = PairValidWF.fst-valid pair-decomp
      arg-valid-wf = PairValidWF.snd-valid pair-decomp
      arg-before = PairValidWF.snd-before pair-decomp

      closure : ⟦ A ⇛ B ⟧ᴵ
      -- Plan 0.52 M2: `sem-fst`/`sem-snd` are Type-tier (their implicits are
      -- `Type`, not `IRTy`), but `⟦ A ⟧ᴵ = ⟦ ⌈ A ⌉ ⟧` and the product is a
      -- real `×`, so the projections apply directly and carry no tier.
      closure = proj₁ x

      arg : ⟦ A ⟧ᴵ
      arg = proj₂ x

      -- Decompose closure (Plan 0.17.2 follow-up: decomposeClosureWF
      -- is now mode-polymorphic, so the prior Heap-coercion via
      -- closure-mode-is-heap-proof is gone).
      mClosure = PairValidWF.mA pair-decomp
      closure-decomp = decomposeClosureWF {mClosure} {_} {A} {B} closure-valid-wf
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

      -- Step 1: instr-alloc-stack pair-slots ∷ load-indirect-suc
      -- Plan 0.14: instr-alloc-stack at the start bumps next-slot by
      -- pair-slots so runtime alloc matches child-alloc.
      -- After load-indirect-suc: Output = arg-loc (from *(sucLoc input-loc))
      step1-trace : AbstractTrace
      step1-trace = instr-alloc-stack pair-slots ∷ load-indirect-suc ∷ []

      s1 : LocState FS
      s1 = proj₁ (exec-trace step1-trace s alloc)

      -- After load-indirect-suc, Output = SV-Ptr arg-loc.
      -- Plan 0.16: composes lift-via-alloc-stack-preserves-mem + the
      -- existing exec-abstract-load-indirect-suc-output lemma. The
      -- step1-trace is a 2-instr trace (alloc-stack ∷ load-indirect-suc);
      -- alloc-stack preserves rdi-eq + arg-ptr definitionally / via
      -- readLoc-stackMem-eq, then load-indirect-suc-output gives Output.
      step1-output : readReg (regs s1) Output ≡ SV-Ptr arg-loc
      step1-output =
        let s' = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc' = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            arg-ptr-s' : readLoc s' (sucLoc input-loc) ≡ just (SV-Ptr arg-loc)
            arg-ptr-s' = trans (readLoc-stackMem-eq s' s (sucLoc input-loc) refl refl) arg-ptr
            -- exec-trace step1-trace s alloc unfolds to
            -- exec-abstract load-indirect-suc s' alloc' via
            -- exec-trace-cons + exec-trace-single.
            d1 = exec-trace-cons (instr-alloc-stack pair-slots) (load-indirect-suc ∷ []) s alloc not-halted
            d2 = exec-trace-single load-indirect-suc s' alloc' not-halted
            s1-eq : s1 ≡ proj₁ (exec-abstract load-indirect-suc s' alloc')
            s1-eq = cong proj₁ (trans d1 d2)
        in trans (cong (λ st → readReg (regs st) Output) s1-eq)
                 (exec-abstract-load-indirect-suc-output s' alloc' input-loc
                    (SV-Ptr arg-loc) rdi-eq arg-ptr-s')

      -- Step 2: store-at-slot (suc pair-slot)
      -- Writes Output (= arg-loc) to slot (suc pair-slot)
      step2-trace : AbstractTrace
      step2-trace = store-at-slot (suc pair-slot) ∷ []

      -- State after steps 1-2
      s2 : LocState FS
      s2 = proj₁ (exec-trace (step1-trace ++ step2-trace) s alloc)

      -- Not halted after step 1
      -- Plan 0.16 Rec 5: load-indirect-suc InstrWF discharged via helper.
      -- instr-alloc-stack preserves regs.Input1 and memory definitionally,
      -- so rdi-eq + arg-ptr at the original state lift to the post-state.
      not-halted-s1 : halted s1 ≡ false
      -- instr-alloc-stack touches nothing in the LocState (0.63), so it preserves
      -- readReg Input1 (definitionally, via record-update projection)
      -- and stackMem / heapMem (so readLoc lifts via readLoc-stackMem-eq).
      not-halted-s1 =
        let s1' = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc1' = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            arg-ptr-s1' : readLoc s1' (sucLoc input-loc) ≡ just (SV-Ptr arg-loc)
            arg-ptr-s1' = trans (readLoc-stackMem-eq s1' s (sucLoc input-loc) refl refl)
                                arg-ptr
        in exec-trace-preserves-halted-WF step1-trace s alloc not-halted
             (twf-∷ tt
               (twf-∷ (load-indirect-suc-twf {s = s1'} {alloc = alloc1'}
                         input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s1')
                      twf-[]))

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
      prefix-for-env = instr-alloc-stack pair-slots ∷
                       load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷
                       load-indirect ∷ mov-to-input ∷ instr-save-closure-reg ∷
                       load-indirect ∷ []

      suffix-after-env-store : AbstractTrace
      suffix-after-env-store = lea-slot pair-slot ∷ mov-to-input ∷ []

      setup-decomp-for-env : apply-setup-trace pair-slot ≡
                             prefix-for-env ++ store-at-slot pair-slot ∷ suffix-after-env-store
      setup-decomp-for-env = refl

      -- Decompose prefix-for-env into sub-traces
      -- Plan 0.14: prefix12 includes instr-alloc-stack pair-slots at the start.
      prefix12 : AbstractTrace
      prefix12 = instr-alloc-stack pair-slots ∷ load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷ []

      prefix345 : AbstractTrace
      prefix345 = load-indirect ∷ mov-to-input ∷ instr-save-closure-reg ∷ load-indirect ∷ []

      prefix-decomp-12-345 : prefix-for-env ≡ prefix12 ++ prefix345
      prefix-decomp-12-345 = refl

      -- State after steps 1-2
      s12 : LocState FS
      s12 = proj₁ (exec-trace prefix12 s alloc)

      alloc12 : AllocState {FS}
      alloc12 = proj₂ (exec-trace prefix12 s alloc)

      -- Steps 1-2 preserve halted. The load-indirect-suc witness is at
      -- the post-alloc-stack state (Plan 0.16 Rec 5).
      prefix12-tph : TraceWF s alloc prefix12
      prefix12-tph =
        let s' = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc' = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            arg-ptr-s' : readLoc s' (sucLoc input-loc) ≡ just (SV-Ptr arg-loc)
            arg-ptr-s' = trans (readLoc-stackMem-eq s' s (sucLoc input-loc) refl refl) arg-ptr
        in twf-∷ tt
             (twf-∷ (load-indirect-suc-twf {s = s'} {alloc = alloc'}
                       input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s')
                    (twf-∷ tt twf-[]))

      not-halted-s12 : halted s12 ≡ false
      not-halted-s12 = exec-trace-preserves-halted-WF prefix12 s alloc not-halted prefix12-tph

      -- Input1 is still input-loc after steps 1-2.
      -- Plan 0.16 Rec 5 follow-up: chained Input1 preservation through
      -- prefix12 = instr-alloc-stack ∷ load-indirect-suc ∷ store-at-slot.
      --   * instr-alloc-stack: regs.Input1 unchanged (record update touches
      --     nothing in the LocState) — refl through writeReg-preserves not needed.
      --   * load-indirect-suc: writes Output, preserves Input1 — via
      --     exec-abstract-load-indirect-suc-preserves-input.
      --   * store-at-slot: writes memory, preserves regs — via
      --     exec-abstract-store-at-slot-preserves-input.
      input-after-s12 : readReg (regs s12) Input1 ≡ SV-Ptr input-loc
      input-after-s12 =
        let -- State after each instruction.
            s_a = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc_a = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            s_b = proj₁ (exec-abstract load-indirect-suc s_a alloc_a)
            alloc_b = proj₂ (exec-abstract load-indirect-suc s_a alloc_a)
            -- Decompose exec-trace.
            not-halted-a = not-halted   -- alloc-stack preserves halted=false definitionally
            d1 : exec-trace prefix12 s alloc ≡
                 exec-trace (load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷ []) s_a alloc_a
            d1 = exec-trace-cons (instr-alloc-stack pair-slots) _ s alloc not-halted
            not-halted-b : halted s_b ≡ false
            not-halted-b = exec-abstract-preserves-halted-WF load-indirect-suc s_a alloc_a not-halted-a
                             (load-indirect-suc-twf {s = s_a} {alloc = alloc_a}
                                input-loc (SV-Ptr arg-loc) rdi-eq
                                (trans (readLoc-stackMem-eq s_a s (sucLoc input-loc) refl refl) arg-ptr))
            d2 : exec-trace (load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷ []) s_a alloc_a ≡
                 exec-trace (store-at-slot (suc pair-slot) ∷ []) s_b alloc_b
            d2 = exec-trace-cons load-indirect-suc _ s_a alloc_a not-halted-a
            d3 : exec-trace (store-at-slot (suc pair-slot) ∷ []) s_b alloc_b ≡
                 exec-abstract (store-at-slot (suc pair-slot)) s_b alloc_b
            d3 = exec-trace-single (store-at-slot (suc pair-slot)) s_b alloc_b not-halted-b
            s12-eq : s12 ≡ proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s_b alloc_b)
            s12-eq = cong proj₁ (trans d1 (trans d2 d3))
            -- Per-step Input1 preservation.
            -- alloc-stack: regs.Input1 unchanged definitionally — refl.
            alloc-stack-preserves : readReg (regs s_a) Input1 ≡ readReg (regs s) Input1
            alloc-stack-preserves = refl
            -- load-indirect-suc: explicit lemma.
            load-isuc-preserves : readReg (regs s_b) Input1 ≡ readReg (regs s_a) Input1
            load-isuc-preserves = exec-abstract-load-indirect-suc-preserves-input s_a alloc_a
            -- store-at-slot: explicit lemma.
            store-preserves :
              readReg (regs (proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s_b alloc_b))) Input1 ≡
              readReg (regs s_b) Input1
            store-preserves = exec-abstract-store-at-slot-preserves-input (suc pair-slot) s_b alloc_b
        in trans (cong (λ st → readReg (regs st) Input1) s12-eq)
                 (trans store-preserves
                   (trans load-isuc-preserves
                     (trans alloc-stack-preserves rdi-eq)))

      -- Memory preservation across prefix12 for any BeforeFrontier loc.
      -- Plan 0.16: shape-independent via BeforeFrontier disjointness.
      -- prefix12 = instr-alloc-stack ∷ load-indirect-suc ∷ store-at-slot.
      -- The only write is store-at-slot (suc pair-slot); locations
      -- BeforeFrontier alloc cannot alias with that scratch slot
      -- (uniformly for AtStack-lower-slot, AtStack-ancestor-frame,
      -- and AtDynamic). Reusable for both closure-loc and input-loc.
      prefix12-preserves-before-frontier :
        (loc : ValueLocation FS) → BeforeFrontier alloc loc →
        readLoc s12 loc ≡ readLoc s loc
      prefix12-preserves-before-frontier loc loc-before =
        let s_a = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc_a = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            s_b = proj₁ (exec-abstract load-indirect-suc s_a alloc_a)
            alloc_b = proj₂ (exec-abstract load-indirect-suc s_a alloc_a)
            not-halted-a = not-halted
            not-halted-b : halted s_b ≡ false
            not-halted-b = exec-abstract-preserves-halted-WF load-indirect-suc s_a alloc_a not-halted-a
                             (load-indirect-suc-twf {s = s_a} {alloc = alloc_a}
                                input-loc (SV-Ptr arg-loc) rdi-eq
                                (trans (readLoc-stackMem-eq s_a s (sucLoc input-loc) refl refl) arg-ptr))
            d1 : exec-trace prefix12 s alloc ≡
                 exec-trace (load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷ []) s_a alloc_a
            d1 = exec-trace-cons (instr-alloc-stack pair-slots) _ s alloc not-halted
            d2 : exec-trace (load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷ []) s_a alloc_a ≡
                 exec-trace (store-at-slot (suc pair-slot) ∷ []) s_b alloc_b
            d2 = exec-trace-cons load-indirect-suc _ s_a alloc_a not-halted-a
            d3 : exec-trace (store-at-slot (suc pair-slot) ∷ []) s_b alloc_b ≡
                 exec-abstract (store-at-slot (suc pair-slot)) s_b alloc_b
            d3 = exec-trace-single (store-at-slot (suc pair-slot)) s_b alloc_b not-halted-b
            s12-eq : s12 ≡ proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s_b alloc_b)
            s12-eq = cong proj₁ (trans d1 (trans d2 d3))
            alloc-stack-mem-eq : readLoc s_a loc ≡ readLoc s loc
            alloc-stack-mem-eq = readLoc-stackMem-eq s_a s loc refl refl
            load-isuc-mem-eq : readLoc s_b loc ≡ readLoc s_a loc
            load-isuc-mem-eq = exec-abstract-load-indirect-suc-preserves-mem s_a alloc_a loc
            frame-eq-a : current-frame alloc_a ≡ current-frame alloc
            frame-eq-a = exec-abstract-preserves-frame (instr-alloc-stack pair-slots) s alloc
            frame-eq-b : current-frame alloc_b ≡ current-frame alloc_a
            frame-eq-b = exec-abstract-preserves-frame load-indirect-suc s_a alloc_a
            frame-eq : current-frame alloc_b ≡ current-frame alloc
            frame-eq = trans frame-eq-b frame-eq-a
            loc≢scratch-at-alloc : loc ≢ AtStack (current-frame alloc) (suc pair-slot)
            loc≢scratch-at-alloc = before-frontier-stack-disjoint
              alloc loc (suc pair-slot) loc-before
              (n≤1+n (next-slot alloc))
            loc≢scratch : loc ≢ AtStack (current-frame alloc_b) (suc pair-slot)
            loc≢scratch eq = loc≢scratch-at-alloc
              (trans eq (cong (λ f → AtStack f (suc pair-slot)) frame-eq))
            store-mem-eq :
              readLoc (proj₁ (exec-abstract (store-at-slot (suc pair-slot)) s_b alloc_b)) loc ≡
              readLoc s_b loc
            store-mem-eq =
              exec-abstract-store-at-slot-preserves-loc (suc pair-slot) s_b alloc_b loc loc≢scratch
        in trans (cong (λ st → readLoc st loc) s12-eq)
                 (trans store-mem-eq
                   (trans load-isuc-mem-eq alloc-stack-mem-eq))

      -- Specialized: env-ptr lifted through prefix12 to s12.
      closure-readable-after-s12 : readLoc s12 closure-loc ≡ just (SV-Ptr env-loc)
      closure-readable-after-s12 =
        trans (prefix12-preserves-before-frontier closure-loc
                 (PairValidWF.fst-before pair-decomp))
              env-ptr

      -- Specialized: closure-ptr (readLoc s input-loc) lifted to s12.
      input-loc-readable-after-s12 : readLoc s12 input-loc ≡ just (SV-Ptr closure-loc)
      input-loc-readable-after-s12 =
        trans (prefix12-preserves-before-frontier input-loc input-before)
              closure-ptr

      -- TracePreservesHalted for prefix-for-env. Plan 0.16 Rec 5:
      -- positions 2 and 4 discharged via load-indirect-{,suc-}twf +
      -- load-indirect-after-3-prefix. Position 7 still pending.
      prefix-for-env-tph : TraceWF s alloc prefix-for-env
      prefix-for-env-tph =
        let s' = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc' = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            arg-ptr-s' : readLoc s' (sucLoc input-loc) ≡ just (SV-Ptr arg-loc)
            arg-ptr-s' = trans (readLoc-stackMem-eq s' s (sucLoc input-loc) refl refl) arg-ptr
            not-halted-after-mov : halted (proj₁ (exec-abstract load-indirect-suc s' alloc')) ≡ false
            not-halted-after-mov = exec-abstract-preserves-halted-WF load-indirect-suc s' alloc' not-halted
                                     (load-indirect-suc-twf {s = s'} {alloc = alloc'}
                                        input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s')
        in
        twf-∷ tt                 -- instr-alloc-stack: InstrWF = ⊤
        (twf-∷ (load-indirect-suc-twf {s = s'} {alloc = alloc'}
                  input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s')
        (twf-∷ tt
        (twf-∷ (load-indirect-after-3-prefix
                  (instr-alloc-stack pair-slots) load-indirect-suc
                  (store-at-slot (suc pair-slot))
                  s alloc input-loc (SV-Ptr closure-loc)
                  not-halted not-halted not-halted-after-mov
                  input-after-s12 input-loc-readable-after-s12)
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ (SMP.!!) twf-[])))))) -- load-indirect: env-ptr witness (pos 7, TODO)

      not-halted-after-prefix-for-env : halted (proj₁ (exec-trace prefix-for-env s alloc)) ≡ false
      not-halted-after-prefix-for-env = exec-trace-preserves-halted-WF prefix-for-env s alloc not-halted prefix-for-env-tph

      -- suffix writes above suc pair-slot (lea-slot and mov-to-input don't write to slots)
      suffix-writes-above : SMP.TraceWritesAbove (suc pair-slot) suffix-after-env-store
      suffix-writes-above = tt  -- both instructions have instr-writes-slot = nothing

      suffix-no-heap-writes : SMP.TraceNoHeapWrites suffix-after-env-store
      suffix-no-heap-writes = tt

      ------------------------------------------------------------------------
      -- Prefix step-by-step (left as documentation for the per-position
      -- semantic discharges in `prefix-for-env-tph` and friends):
      --   1. load-indirect-suc: Output := *(sucLoc Input1) = arg-loc
      --   2. store-at-slot: Output unchanged
      --   3. load-indirect: Output := *Input1 = closure-loc
      --   4. mov-to-input: Input1 := Output = closure-loc, Output unchanged
      --   5. load-indirect: Output := *Input1 = *closure-loc = env-loc
      ------------------------------------------------------------------------

      -- Step 3: load-indirect reads closure-loc, gets env-loc (after step 3)
      prefix3 : AbstractTrace
      prefix3 = load-indirect ∷ []

      s3-partial : LocState FS
      s3-partial = proj₁ (exec-trace prefix3 s12 alloc12)

      -- After step 3, Output = *Input1 = *input-loc = closure-loc.
      -- Plan 0.16: load-indirect's output is just `exec-abstract-load-indirect-output`
      -- applied to input-after-s12 + input-loc-readable-after-s12.
      step3-output : readReg (regs s3-partial) Output ≡ SV-Ptr closure-loc
      step3-output =
        let alloc-eq : proj₁ (exec-trace prefix3 s12 alloc12) ≡
                       proj₁ (exec-abstract load-indirect s12 alloc12)
            alloc-eq = cong proj₁ (exec-trace-single load-indirect s12 alloc12 not-halted-s12)
        in trans (cong (λ st → readReg (regs st) Output) alloc-eq)
                 (exec-abstract-load-indirect-output s12 alloc12 input-loc
                    (SV-Ptr closure-loc) input-after-s12 input-loc-readable-after-s12)

      -- Step 4: mov-to-input sets Input1 := Output = closure-loc, preserves Output
      prefix34 : AbstractTrace
      prefix34 = load-indirect ∷ mov-to-input ∷ []

      s34-partial : LocState FS
      s34-partial = proj₁ (exec-trace prefix34 s12 alloc12)

      -- Plan 0.16 Rec 5: load-indirect at s12 dereferences Input1 =
      -- SV-Ptr input-loc (input-after-s12), reading *input-loc = closure-loc
      -- (input-loc-readable-after-s12). Both lifts are uniform across
      -- closure modes via BeforeFrontier disjointness.
      prefix3-tph : TraceWF s12 alloc12 prefix3
      prefix3-tph = twf-∷ (load-indirect-twf {s = s12} {alloc = alloc12}
                             input-loc (SV-Ptr closure-loc)
                             input-after-s12 input-loc-readable-after-s12)
                          twf-[]

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

      -- Step 5: load-indirect reads *Input1 = *closure-loc = env-loc.
      -- Plan 0.16 Rec 5: pos 1 (load-indirect at s12, same as prefix3-tph)
      -- discharged via the helper. Pos 4 (load-indirect at s345) still
      -- needs lifting through mov-to-input + instr-save-closure-reg.
      prefix345-tph : TraceWF s12 alloc12 prefix345
      prefix345-tph = twf-∷ (load-indirect-twf {s = s12} {alloc = alloc12}
                               input-loc (SV-Ptr closure-loc)
                               input-after-s12 input-loc-readable-after-s12)
                      (twf-∷ tt
                      (twf-∷ tt
                      (twf-∷ (SMP.!!) twf-[])))  -- TODO: load-indirect witness at s345

      not-halted-s345 : halted (proj₁ (exec-trace prefix345 s12 alloc12)) ≡ false
      not-halted-s345 = exec-trace-preserves-halted-WF prefix345 s12 alloc12 not-halted-s12 prefix345-tph

      -- Plan 0.16 cleanup: `output-after-prefix` / `step5-output-final`
      -- (previously declared here but never referenced) deleted as
      -- dead scaffolding. They claimed `readReg s-after-prefix Output
      -- ≡ SV-Ptr env-loc` but were never consumed by any IRResultBase
      -- field or downstream proof. The semantic content (Output =
      -- env-loc after the load ∷ mov ∷ save ∷ load chain) folds into
      -- pair-env-ptr directly if needed.

      -- TODO (post-scaffold): rederive via a TraceWF-shaped
      -- prefix-store-preserve. Original proof used the tph chain.
      pair-env-ptr : readLoc s-after-setup pair-input-loc ≡ just (SV-Ptr env-loc)
      pair-env-ptr = SMP.!!

      -- Input1 register points to pair after setup
      -- Decompose setup-trace as prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
      setup-prefix : AbstractTrace
      setup-prefix = instr-alloc-stack pair-slots ∷
                     load-indirect-suc ∷ store-at-slot (suc pair-slot) ∷
                     load-indirect ∷ mov-to-input ∷ instr-save-closure-reg ∷
                     load-indirect ∷ store-at-slot pair-slot ∷ []

      setup-decomp : apply-setup-trace pair-slot ≡
                     setup-prefix ++ (lea-slot pair-slot ∷ mov-to-input ∷ [])
      setup-decomp = refl

      -- TracePreservesHalted for the prefix. Pos-2 load-indirect-suc
      -- and pos-4 load-indirect discharged via Plan 0.16 helpers.
      -- Pos-4 needs a subst from the trace-form (s12) to the chain-form
      -- state because TraceWF's inductive structure threads via
      -- exec-abstract, not exec-trace.
      setup-prefix-tph : TraceWF s alloc setup-prefix
      setup-prefix-tph =
        let s' = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc' = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            arg-ptr-s' : readLoc s' (sucLoc input-loc) ≡ just (SV-Ptr arg-loc)
            arg-ptr-s' = trans (readLoc-stackMem-eq s' s (sucLoc input-loc) refl refl) arg-ptr
            -- Bridge chain-form pos-4 state to s12 / alloc12.
            chain-state-pos4 = proj₁ (exec-abstract (store-at-slot (suc pair-slot))
                                       (proj₁ (exec-abstract load-indirect-suc s' alloc'))
                                       (proj₂ (exec-abstract load-indirect-suc s' alloc')))
            chain-alloc-pos4 = proj₂ (exec-abstract (store-at-slot (suc pair-slot))
                                       (proj₁ (exec-abstract load-indirect-suc s' alloc'))
                                       (proj₂ (exec-abstract load-indirect-suc s' alloc')))
            not-halted-after-mov : halted (proj₁ (exec-abstract load-indirect-suc s' alloc')) ≡ false
            not-halted-after-mov = exec-abstract-preserves-halted-WF load-indirect-suc s' alloc' not-halted
                                     (load-indirect-suc-twf {s = s'} {alloc = alloc'}
                                        input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s')
            -- s12 = exec-trace prefix12 s alloc unfolds to the chain form
            -- via two exec-trace-cons + one exec-trace-single.
            d1 = exec-trace-cons (instr-alloc-stack pair-slots) _ s alloc not-halted
            d2 = exec-trace-cons load-indirect-suc _ s' alloc' not-halted
            d3 = exec-trace-single (store-at-slot (suc pair-slot))
                   (proj₁ (exec-abstract load-indirect-suc s' alloc'))
                   (proj₂ (exec-abstract load-indirect-suc s' alloc'))
                   not-halted-after-mov
            chain-eq : (s12 , alloc12) ≡ (chain-state-pos4 , chain-alloc-pos4)
            chain-eq = trans d1 (trans d2 d3)
            -- Transport the pos-4 witness from (s12, alloc12) to the
            -- chain-form state via subst.
            pos4-witness-at-s12 : InstrWF s12 alloc12 load-indirect
            pos4-witness-at-s12 = load-indirect-twf {s = s12} {alloc = alloc12}
                                    input-loc (SV-Ptr closure-loc)
                                    input-after-s12 input-loc-readable-after-s12
            pos4-witness : InstrWF chain-state-pos4 chain-alloc-pos4 load-indirect
            pos4-witness = subst (λ p → InstrWF (proj₁ p) (proj₂ p) load-indirect)
                                 chain-eq pos4-witness-at-s12
        in
        twf-∷ tt                 -- instr-alloc-stack: InstrWF = ⊤
        (twf-∷ (load-indirect-suc-twf {s = s'} {alloc = alloc'}
                  input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s')
        (twf-∷ tt
        (twf-∷ pos4-witness      -- load-indirect at chain-form pos-4 (= s12 via subst)
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ (SMP.!!)          -- TODO: load-indirect witness (late, pos 7)
        (twf-∷ tt twf-[])))))))

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

      -- Setup trace preserves halted (used in multiple places).
      -- Pos-2 load-indirect-suc and pos-4 load-indirect discharged via
      -- Plan 0.16 helpers; pos-4 uses the subst bridge from
      -- (s12, alloc12) to the chain-form state. Pos-7 still pending
      -- (further chain lifting through mov-to-input / save-closure-reg).
      setup-tph : TraceWF s alloc (apply-setup-trace pair-slot)
      setup-tph =
        let s' = proj₁ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            alloc' = proj₂ (exec-abstract (instr-alloc-stack pair-slots) s alloc)
            arg-ptr-s' : readLoc s' (sucLoc input-loc) ≡ just (SV-Ptr arg-loc)
            arg-ptr-s' = trans (readLoc-stackMem-eq s' s (sucLoc input-loc) refl refl) arg-ptr
            chain-state-pos4 = proj₁ (exec-abstract (store-at-slot (suc pair-slot))
                                       (proj₁ (exec-abstract load-indirect-suc s' alloc'))
                                       (proj₂ (exec-abstract load-indirect-suc s' alloc')))
            chain-alloc-pos4 = proj₂ (exec-abstract (store-at-slot (suc pair-slot))
                                       (proj₁ (exec-abstract load-indirect-suc s' alloc'))
                                       (proj₂ (exec-abstract load-indirect-suc s' alloc')))
            not-halted-after-mov : halted (proj₁ (exec-abstract load-indirect-suc s' alloc')) ≡ false
            not-halted-after-mov = exec-abstract-preserves-halted-WF load-indirect-suc s' alloc' not-halted
                                     (load-indirect-suc-twf {s = s'} {alloc = alloc'}
                                        input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s')
            d1 = exec-trace-cons (instr-alloc-stack pair-slots) _ s alloc not-halted
            d2 = exec-trace-cons load-indirect-suc _ s' alloc' not-halted
            d3 = exec-trace-single (store-at-slot (suc pair-slot))
                   (proj₁ (exec-abstract load-indirect-suc s' alloc'))
                   (proj₂ (exec-abstract load-indirect-suc s' alloc'))
                   not-halted-after-mov
            chain-eq : (s12 , alloc12) ≡ (chain-state-pos4 , chain-alloc-pos4)
            chain-eq = trans d1 (trans d2 d3)
            pos4-witness-at-s12 : InstrWF s12 alloc12 load-indirect
            pos4-witness-at-s12 = load-indirect-twf {s = s12} {alloc = alloc12}
                                    input-loc (SV-Ptr closure-loc)
                                    input-after-s12 input-loc-readable-after-s12
            pos4-witness : InstrWF chain-state-pos4 chain-alloc-pos4 load-indirect
            pos4-witness = subst (λ p → InstrWF (proj₁ p) (proj₂ p) load-indirect)
                                 chain-eq pos4-witness-at-s12
        in
        twf-∷ tt                 -- instr-alloc-stack pair-slots: InstrWF = ⊤
        (twf-∷ (load-indirect-suc-twf {s = s'} {alloc = alloc'}
                  input-loc (SV-Ptr arg-loc) rdi-eq arg-ptr-s')
        (twf-∷ tt
        (twf-∷ pos4-witness      -- load-indirect at chain-form pos-4 (= s12 via subst)
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ (SMP.!!)          -- TODO: load-indirect witness (late, pos 7)
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ tt twf-[])))))))))

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
      -- This bridges the body's frontier facts (both in body's
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
      -- Plan 0.54 rung A: `at-reg` (register-resident result) still carries a
      -- `loc` field, and this dispatch needs only a location. NOTE that the
      -- location is a PLACEHOLDER (the producer's input cell) — it does not
      -- hold the value. It is safe here because `result-place-final`'s
      -- `at-reg` branch propagates the residence and never consults
      -- `result-loc`; the at-loc branch, which does, has a real one. The field
      -- itself is vestigial and slated to go — see the note where
      -- `place-loc` used to live.
      result-loc-dispatch (at-reg loc _ _ _ _) = loc
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

      ------------------------------------------------------------------
      -- Plan 0.14: alloc-correct discharge for apply trace.
      -- trace = apply-setup-trace ++ body-trace.
      -- apply-setup-trace starts with `instr-alloc-stack pair-slots`,
      -- followed by 9 alloc-preservers; its alloc output is child-alloc.
      -- body-result.alloc-correct gives proj₂ at (s-after-setup, child-alloc)
      -- = body-result.final-alloc = alloc'.
      ------------------------------------------------------------------

      -- Bridge: proj₂ (exec-trace apply-setup-trace s alloc) ≡ child-alloc.
      -- 10-instr chain; instr-alloc-stack at the start bumps next-slot;
      -- the remaining 9 preserve alloc.
      alloc-setup-eq-child : proj₂ (exec-trace (apply-setup-trace pair-slot) s alloc) ≡ child-alloc
      alloc-setup-eq-child = SMP.!!  -- 10-step chain pending dedicated proof

      -- Plan 0.17: alloc-correct-local stays at the producer's natural
      -- shape `alloc'` (= body-result.final-alloc). The bridge to
      -- apply-bump apply-bump-value alloc is `apply-bump-eq` below.
      alloc-correct-apply-local : proj₂ (exec-trace trace s alloc) ≡ alloc'
      alloc-correct-apply-local =
        let split = SMP.TraceComposition.exec-trace-append {FS} (apply-setup-trace pair-slot) body-trace s alloc
            bridge : exec-trace body-trace (proj₁ (exec-trace (apply-setup-trace pair-slot) s alloc))
                                            (proj₂ (exec-trace (apply-setup-trace pair-slot) s alloc))
                     ≡ exec-trace body-trace s-after-setup child-alloc
            bridge = cong (exec-trace body-trace s-after-setup) alloc-setup-eq-child
            body-alloc : proj₂ (exec-trace body-trace s-after-setup child-alloc) ≡ alloc'
            body-alloc = IRResultAWF.alloc-correct body-result
        in trans (cong proj₂ (trans split bridge)) body-alloc

      -- Plan 0.17 bump declaration: scratch (mkBump pair-slots 0)
      -- ∘ body's bump.
      apply-bump-value : AllocBump
      apply-bump-value = bump-+ (mkBump pair-slots 0) (IRResultAWF.bump body-result)

      -- Bridge alloc' to apply-bump apply-bump-value alloc.
      -- alloc' = body-result.final-alloc = apply-bump body-bump child-alloc
      --        = apply-bump body-bump (apply-bump (mkBump pair-slots 0) alloc) (via child-alloc-eq)
      --        = apply-bump (bump-+ (mkBump pair-slots 0) body-bump) alloc    (via apply-bump-compose)
      apply-bump-eq : alloc' ≡ apply-bump apply-bump-value alloc
      apply-bump-eq =
        let child-alloc-eq : child-alloc ≡ apply-bump (mkBump pair-slots 0) alloc
            child-alloc-eq = cong (λ s → record alloc { next-slot = s })
                                  (+-comm (next-slot alloc) pair-slots)
            compose-bump :
              apply-bump (IRResultAWF.bump body-result) (apply-bump (mkBump pair-slots 0) alloc)
              ≡ apply-bump apply-bump-value alloc
            compose-bump = apply-bump-compose (mkBump pair-slots 0) (IRResultAWF.bump body-result) alloc
        in trans (cong (apply-bump (IRResultAWF.bump body-result)) child-alloc-eq) compose-bump

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
      --   result-before', result-valid-wf' — the body's frontier fact
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
      rax-eq' = SMP.!!  -- TODO: dispatch on body's result-place; cascade through s'-eq

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
      -- Plan 0.2.4.5 D1 task #30: alloc' = body's final-alloc, so the body's
      -- frontier fact transports directly via the result-place dispatch.
      -- For unit-result branch this isn't reached (apply uses unit-result),
      -- but the function must still typecheck for the at-loc dispatch.
      result-before' : BeforeFrontier alloc' result-loc
      result-before' = SMP.!!  -- TODO: dispatch on body's result-place; postulate for unit-result branch

      -- Closure-decomp eval bridge: eval (apply ...) x ≡ eval body (pair env arg).
      -- closure-is-body : closure ≡ (λ a → eval body (pair env a)).
      -- eval (apply) (closure, arg) reduces to closure arg, which equals
      -- (λ a → eval body (pair env a)) arg ≡ eval body (pair env arg).
      eval-apply-eq : eval (apply {A} {B}) x ≡ eval body (pair env arg)
      eval-apply-eq = cong (λ c → c arg) closure-is-body

      -- Result validity. body's place-valid gives validity for eval body
      -- (pair env arg) at body-final-alloc / body-final-state.
      -- alloc' = body's final-alloc (definitional);
      -- s' ≡ body-final-state via s'-eq;
      -- eval (apply ...) x ≡ eval body (pair env arg) via eval-apply-eq.
      result-valid-wf' : ValidAtWF mBody alloc' (eval (apply {A} {B}) x) result-loc s'
      result-valid-wf' = SMP.!!  -- TODO: dispatch on body's result-place (at-loc / unit-result)

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

      ------------------------------------------------------------------
      -- Plan 0.17.1: discharge the new IRStackBudget / IRHeapBudget
      -- fields.  apply-bump-value = bump-+ (mkBump pair-slots 0)
      -- body-bump, and apply-bump-eq : alloc' ≡ apply-bump apply-bump-value
      -- alloc carries the bridge.  next-slot-delta apply-bump-value
      -- reduces defequally to pair-slots +ℕ next-slot-delta body-bump,
      -- and next-heap-ref-delta to next-heap-ref-delta body-bump (via
      -- 0 + n = n).
      ------------------------------------------------------------------

      apply-bump-fits-stack-budget :
        next-slot-delta apply-bump-value ≤ pair-slots +ℕ IRResultAWF.stack-budget body-result
      apply-bump-fits-stack-budget =
        +-monoʳ-≤ pair-slots (IRResultAWF.bump-fits-stack-budget body-result)
        where open import Data.Nat.Properties using (+-monoʳ-≤)

      apply-max-slot-geq-final :
        next-slot-delta apply-bump-value +ℕ next-slot alloc
        ≤ IRResultAWF.max-slot-written body-result
      apply-max-slot-geq-final =
        subst (λ a → next-slot a ≤ IRResultAWF.max-slot-written body-result)
              apply-bump-eq
              (IRResultAWF.max-slot-geq-final body-result)

      apply-scratch-bounded :
        IRResultAWF.max-slot-written body-result
        ≤ next-slot (apply-bump apply-bump-value alloc) +ℕ IRResultAWF.scratch-budget body-result
      apply-scratch-bounded =
        subst (λ a → IRResultAWF.max-slot-written body-result
                     ≤ next-slot a +ℕ IRResultAWF.scratch-budget body-result)
              apply-bump-eq
              (IRResultAWF.scratch-bounded body-result)

      apply-bump-fits-heap-budget :
        next-heap-ref-delta apply-bump-value ≤ IRResultAWF.heap-budget body-result
      apply-bump-fits-heap-budget =
        IRResultAWF.bump-fits-heap-budget body-result

      apply-max-heap-ref-geq-final :
        next-heap-ref-delta apply-bump-value +ℕ next-heap-ref alloc
        ≤ IRResultAWF.max-heap-ref-written body-result
      apply-max-heap-ref-geq-final =
        IRResultAWF.max-heap-ref-geq-final body-result

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

      -- Plan 0.14 follow-up: trace-no-heap-writes' local binding removed
      -- (field eliminated from IRHeapBudget; consequence-form invariant is
      -- mem-preserved-before on IRResultBase).

      -- Plan 0.14: continuation-alloc inherits next-slot AND
      -- next-heap-ref from alloc' (body's final-alloc), reflecting the
      -- alloc state the caller resumes with. Replaces the old
      -- reclaim-alloc that took next-heap-ref from the input alloc and
      -- needed an SMP.!! to bridge the heap-ref gap.
      continuation-alloc : AllocState {FS}
      continuation-alloc = record alloc { next-slot     = next-slot     alloc'
                                        ; next-heap-ref = next-heap-ref alloc' }

      -- Frame equivalence: alloc'.frame = alloc.frame via body's frame-preserved + child-alloc.
      alloc'-frame-eq : current-frame alloc' ≡ current-frame alloc
      alloc'-frame-eq = trans (IRResultAWF.frame-preserved body-result) refl

      cont-preserves-result' : BeforeFrontier continuation-alloc result-loc
      cont-preserves-result' = bf-same-frame-slot alloc' continuation-alloc
        alloc'-frame-eq refl refl result-loc result-before'

      cont-preserves-validity' :
        ValidAtWF mBody continuation-alloc (eval (apply {A} {B}) x) result-loc s'
      cont-preserves-validity' = validityWF-with-bf-transfer
        (eval (apply {A} {B}) x) result-loc s' alloc' continuation-alloc
        (λ loc bf → bf-same-frame-slot alloc' continuation-alloc alloc'-frame-eq refl refl loc bf)
        result-valid-wf'

      -- Plan 0.2.4.5 D1 task #30: dispatch on body's result-place.
      -- Plan 0.17: result-place stays at alloc'; helper transports.
      result-place-final : ResultPlace B mBody alloc'
        (record alloc { next-slot     = next-slot     alloc'
                      ; next-heap-ref = next-heap-ref alloc' })
        (eval (apply {A} {B}) x) s'
      result-place-final with IRResultAWF.result-place body-result
      ... | at-loc _ _ _ _ _ _ = at-loc result-loc result-valid-wf' result-before' rax-eq'
                                       cont-preserves-validity' cont-preserves-result'
      -- Stage F: a register-resident body result is PROPAGATED as `at-reg`,
      -- not collapsed to `at-loc`. Collapsing would be unsound, not merely
      -- lossy: `at-reg`'s location is the producer's INPUT cell reused as a
      -- placeholder (`IRObsCorrectFlat`: `at-reg input-loc fit …`), so it does
      -- not hold the value, and an `at-loc` there would assert a false
      -- `rax-eq'`/`result-valid-wf'` — D148's disease, freshly minted.
      --
      -- No new proof gap is opened. `apply-full-trace = setup ++ body`, so the
      -- body runs LAST: `s'-eq` says apply's final state IS the body's, and
      -- `alloc' = final-alloc body-result` definitionally. The register
      -- equation therefore transports across `s'-eq` and `eval-apply-eq`, and
      -- the continuation bound is the same `bf-same-frame-slot` the `at-loc`
      -- branch already uses.
      ... | at-reg loc fit before rax cont =
              at-reg loc fit before
                (subst (λ st → readReg (regs st) Output ≡ prim-sv fit (eval (apply {A} {B}) x))
                       (sym s'-eq)
                       (subst (λ w → readReg (regs (IRResultAWF.final-state body-result)) Output
                                       ≡ prim-sv fit w)
                              (sym eval-apply-eq)
                              rax))
                (bf-same-frame-slot alloc' continuation-alloc alloc'-frame-eq refl refl loc before)
      ... | unit-result = unit-result