------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.ApplyWF
--
-- Apply IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Apply does NOT need RecDispatcherWF because it uses BodyCorrect.execute
-- which was pre-computed by Curry.
--
-- PURE RECLAMATION APPROACH:
-- Body executes in the same frame starting at slot + pair-slots.
-- After body completes, we use reclaim-preserves-result and
-- reclaim-preserves-validity to transfer result to reclaimed allocation.
-- Body's stack allocations are reclaimed, only result persists.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.ApplyWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; <-≤-trans; m≤m+n; +-monoʳ-≤; m+n≤o⇒m≤o; ≤-reflexive)
open import Data.Nat using (_≤?_)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst; cong)
open import Relation.Nullary using (yes; no)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)

-- Import escape interface for SurvivesFramePop
open import Once.Backend.X86v3.EscapeInterface
module EI {FS : FrameSemantics} = EscapeInterfaceDef {FS}
open EI using (SurvivesFramePop; in-ancestor; on-heap) public

-- BeforeFrontier for module parameters - use qualified name to avoid ambiguity
BeforeFrontier' : {FS : FrameSemantics} → AllocState {FS} → ValueLocation FS → Set
BeforeFrontier' {FS} = FrontierInvariant.BeforeFrontier {FS}

------------------------------------------------------------------------
-- BeforeFrontier Transfer Lemmas (independent of program-bound)
--
-- These lemmas transfer BeforeFrontier between allocation states.
-- Extracted to a separate module so they can be used without
-- providing child-frame parameters.
------------------------------------------------------------------------

module BFTransfer {FS : FrameSemantics} where
  open FrontierInvariant {FS}
  open FrameSemantics FS

  -- Transfer BeforeFrontier when allocation states have same frame and slot
  -- but different proof terms. Used for final-alloc to reclaim-alloc transfer.
  --
  -- When current-frame, next-slot, and next-heap-ref are propositionally equal,
  -- BeforeFrontier transfers directly by substitution.
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
    rewrite cf-eq = stack-ancestor cf≺f src  -- Frame ordering and provenance preserved via equality
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnHeap hl) (heap-before r<hr)
    rewrite hr-eq = heap-before r<hr

------------------------------------------------------------------------
-- Apply implementation
------------------------------------------------------------------------

module ApplyWFImpl {FS : FrameSemantics} (program-bound : ℕ)
  -- Child frame support for body execution
  (get-child-frame : ∀ (alloc : AllocState {FS}) → FrameSemantics.Frame FS)
  (child-frame-ordered : ∀ (alloc : AllocState {FS}) →
    FrameSemantics._≺_ FS (get-child-frame alloc) (current-frame alloc))
  -- Immediate adjacency: no frame exists between child and parent
  (child-frame-adjacent : ∀ (alloc : AllocState {FS}) (f : FrameSemantics.Frame FS) →
    FrameSemantics._≺_ FS (get-child-frame alloc) f →
    FrameSemantics._≺_ FS f (current-frame alloc) →
    ⊥)
  (child-capacity : ℕ)
  (child-cap-sufficient : pair-slots *ℕ program-bound ≤ child-capacity)
  -- Escape analysis: body results survive child frame pop
  -- This is the MINIMAL interface - escape analysis proves this for each body
  (escape-result-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
    (result-loc : ValueLocation FS) →
    current-frame body-final ≡ get-child-frame alloc →
    BeforeFrontier' body-final result-loc →
    SurvivesFramePop (get-child-frame alloc) result-loc)
  -- Bound tracking: bounds set by bf-transfer equal final-alloc.next-slot
  -- This is a property of how values are transferred through child frame execution
  (parent-bound-eq : ∀ (alloc : AllocState {FS}) (bound : ℕ) →
    bound ≡ next-slot alloc Data.Nat.+ pair-slots)
  where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; BodyCorrect;
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           valid-inl-wf; valid-inr-wf; valid-fold-wf;
           validityWF-mem-only; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-frontier-advance;
           validityWF-with-bf-transfer;
           decomposePairWF; PairValidWF;
           decomposeClosureWF; ClosureValidWF;
           closure-mode-is-heap-proof;
           at-frontier-neq-before-wf; suc-frontier-neq-before-wf)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (suc<+2)

  -- Import write operations
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import frontier lemmas
  open import Once.Backend.X86v3.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (at-frontier-before-pair)

  -- Import BeforeFrontier transfer lemma from BFTransfer module
  open BFTransfer {FS}
    using (bf-same-frame-slot)

  ------------------------------------------------------------------------
  -- Helper: Extract body-capacity from apply input's closure
  --
  -- This extracts body-capacity from the ValidAtWF proof for (closure, arg).
  -- By computing this directly from input-valid-wf, we avoid needing a
  -- separate body-cap parameter that must match the closure's capacity.
  ------------------------------------------------------------------------

  closure-body-capacity : ∀ {m A B alloc loc s}
    (x : ⟦ (A ⇒ B) * A ⟧)
    (input-valid-wf : ValidAtWF m alloc x loc s) → ℕ  -- Reference-based: any mode works
  closure-body-capacity {m} {A} {B} {alloc} {loc} {s} x input-valid-wf =
    let pair-decomp = decomposePairWF {m} {_} {A ⇒[ Many ] B} {A} input-valid-wf
        closure-loc = PairValidWF.fst-loc pair-decomp
        closure = proj₁ x
        closure-valid-wf = PairValidWF.fst-valid pair-decomp
        closure-mode-eq = closure-mode-is-heap-proof closure-valid-wf
        closure-valid-wf-heap = subst (λ m → ValidAtWF m alloc closure closure-loc s)
                                       closure-mode-eq closure-valid-wf
        closure-decomp = decomposeClosureWF {_} {Many} {A} {B} closure-valid-wf-heap
        body-correct = ClosureValidWF.body-correct closure-decomp
    in BodyCorrect.body-capacity body-correct

  ------------------------------------------------------------------------
  -- Apply: Uses body-correct.execute instead of recursive run-ir call
  --
  -- Does NOT need RecDispatcherWF because it extracts BodyCorrect from
  -- the closure and calls execute, which was pre-computed by Curry.
  --
  -- PURE RECLAMATION APPROACH:
  -- Body executes in the same frame starting at slot + pair-slots.
  -- After body completes, we use body's reclaim-preserves-result and
  -- all-escape to transfer result to apply's reclaimed allocation.
  --
  -- Why this works:
  -- 1. Body runs in same frame with alloc-pair (next-slot = slot + pair-slots)
  -- 2. Body's result must escape the "reclaimed region" [slot + pair-slots, ...)
  -- 3. Result is either on heap (heap-before), from input (slot < slot + pair-slots),
  --    or stack-allocated in reclaimed region (IMPOSSIBLE by all-escape)
  -- 4. Escape analysis ensures escaping values are heap-allocated
  --
  -- KEY: Body executes in a child frame with child-capacity.
  -- Body's capacity proof is derived from child-cap-sufficient + body<bound.
  -- Apply's reclaimable-slot = slot + pair-slots (body allocations in child).
  ------------------------------------------------------------------------

  run-apply : ∀ {m A B}
    (x : ⟦ (A ⇒ B) * A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-valid-wf : ValidAtWF m alloc x input-loc s) →  -- Reference-based: any mode works
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- Capacity using ir-stack-requirement (= pair-slots for apply)
    next-slot alloc +ℕ ir-stack-requirement (apply {A} {B}) ≤ frame-capacity alloc →
    -- Body executes in child frame - no dynamic capacity parameter needed
    ∃[ mOut ] IRResultAWF mOut (apply {A} {B}) x s alloc
  run-apply {m} {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    mBody , record
      { result-loc = result-loc
      ; final-state = s-final
      ; final-alloc = final-alloc
      ; result-valid-wf = result-valid-wf
      ; result-before = result-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = frame-preserved-apply
      ; slot-monotone = slot-monotone-apply
      ; heap-monotone = heap-monotone-apply
      ; heap-preserved = heap-preserved-apply
      ; capacity-preserved = capacity-preserved-apply
      ; mem-preserved-before = mem-preserved-apply
      -- Reclamation: apply uses slot + pair-slots (body allocations in child)
      ; reclaimable-slot = apply-reclaimable-slot
      ; reclaim-monotone = apply-reclaim-monotone
      ; reclaim-bounded = apply-reclaim-bounded
      ; reclaim-preserves-result = apply-reclaim-preserves-result
      ; reclaim-preserves-validity = apply-reclaim-preserves-validity
      ; reclaim-size-bound = apply-reclaim-size-bound
      }
    where
      open import Data.Nat using (_≥_)
      open import Data.Nat.Properties using (*-monoʳ-≤; <⇒≤; *-monoˡ-≤)

      -- Step 1: Decompose input as pair (closure, arg) using ValidAtWF
      -- Explicit type: pair type is (A ⇒[ Many ] B) * A
      -- Reference-based: any mode works since pairs use pointer representation
      pair-decomp = decomposePairWF {m} {_} {A ⇒[ Many ] B} {A} input-valid-wf
      closure-loc = PairValidWF.fst-loc pair-decomp
      arg-loc = PairValidWF.snd-loc pair-decomp
      mArg = PairValidWF.mB pair-decomp  -- Mode of argument component
      closure-valid-wf = PairValidWF.fst-valid pair-decomp
      arg-valid-wf = PairValidWF.snd-valid pair-decomp
      arg-before = PairValidWF.snd-before pair-decomp

      -- Extract closure and arg with explicit types to help inference
      -- fst and snd need explicit type params because ⟦ A ⇒[ q ] B ⟧ = ⟦ A ⟧ → ⟦ B ⟧ for any q
      closure : ⟦ A ⇒[ Many ] B ⟧
      closure = fst {A ⇒[ Many ] B} {A} x

      arg : ⟦ A ⟧
      arg = snd {A ⇒[ Many ] B} {A} x

      -- Step 2: Decompose closure to get body-correct!
      -- Note: fst x : ⟦ A ⇒ B ⟧ = ⟦ A ⇒[ Many ] B ⟧
      -- Closures are always Heap mode - extract mA=Heap from ValidAtWF proof
      mClosure = PairValidWF.mA pair-decomp
      -- For closure types, the only constructor is valid-closure-wf which produces Heap
      -- So mClosure must be Heap. Proven by pattern matching in closure-mode-is-heap-proof.
      closure-mode-is-heap : mClosure ≡ Heap
      closure-mode-is-heap = closure-mode-is-heap-proof closure-valid-wf
      closure-valid-wf-heap : ValidAtWF Heap alloc closure closure-loc s
      closure-valid-wf-heap = subst (λ m → ValidAtWF m alloc closure closure-loc s) closure-mode-is-heap closure-valid-wf

      closure-decomp = decomposeClosureWF {_} {Many} {A} {B} closure-valid-wf-heap
      EnvType = ClosureValidWF.EnvType closure-decomp
      body = ClosureValidWF.body closure-decomp
      env = ClosureValidWF.env closure-decomp
      body<bound = ClosureValidWF.body<bound closure-decomp
      env-loc = ClosureValidWF.env-loc closure-decomp
      env-valid-wf = ClosureValidWF.env-valid closure-decomp
      env-before = ClosureValidWF.env-before closure-decomp
      closure-is-body = ClosureValidWF.f-is-closure closure-decomp
      body-correct = ClosureValidWF.body-correct closure-decomp

      -- Extract body-capacity from body-correct
      closure-body-cap = BodyCorrect.body-capacity body-correct
      closure-body-cap-eq = BodyCorrect.body-cap-eq body-correct

      -- Step 3: Allocate pair-slots for (env, arg) pair in parent frame
      pair-input-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- apply-pair-fits: slot + pair-slots ≤ capacity
      -- Derived from combined-cap since ir-stack-requirement apply = pair-slots
      apply-pair-fits : next-slot alloc +ℕ pair-slots ≤ frame-capacity alloc
      apply-pair-fits = combined-cap

      alloc-pair : AllocState {FS}
      alloc-pair = record alloc
        { next-slot = next-slot alloc +ℕ pair-slots
        ; slots-available = apply-pair-fits
        }

      -- Write env-loc and arg-loc to pair slots
      s-write-env = write-loc s pair-input-loc env-loc
      s-write-arg = write-loc s-write-env (sucLoc pair-input-loc) arg-loc
      s-pair = record s-write-arg { regs = writeReg (regs s-write-arg) RDI pair-input-loc }

      pair-not-halted : halted s-pair ≡ false
      pair-not-halted = not-halted

      pair-rdi-eq : readReg (regs s-pair) RDI ≡ pair-input-loc
      pair-rdi-eq = writeReg-same (regs s-write-arg) RDI pair-input-loc

      ------------------------------------------------------------------------
      -- Step 4: Create child frame for body execution
      --
      -- Body executes in a child frame with child-capacity.
      -- Body's capacity proof derived from child-cap-sufficient + body<bound.
      ------------------------------------------------------------------------

      -- Get child frame
      child-frame = get-child-frame alloc
      child-frame-below-parent = child-frame-ordered alloc

      -- Create child allocation state
      child-slots-available : 0 ≤ child-capacity
      child-slots-available = z≤n

      child-alloc : AllocState {FS}
      child-alloc = record
        { current-frame = child-frame
        ; next-slot = 0
        ; slots-available = child-slots-available
        ; frame-capacity = child-capacity
        ; next-heap-ref = next-heap-ref alloc
        }

      -- Derive body capacity proof from child-cap-sufficient + body<bound
      -- body-capacity ≤ pair-slots * ir-size body (from ir-req-≤-pair-slots*size)
      -- pair-slots * ir-size body < pair-slots * program-bound (from body<bound)
      -- pair-slots * program-bound ≤ child-capacity (from child-cap-sufficient)
      body-cap-in-child : 0 +ℕ closure-body-cap ≤ child-capacity
      body-cap-in-child = ≤-trans body-cap-bounded child-cap-sufficient
        where
          open import Once.Backend.X86v3.IR using (ir-req-≤-pair-slots*size)
          -- body-capacity = ir-stack-requirement body
          -- ir-stack-requirement body ≤ pair-slots * ir-size body ≤ pair-slots * (program-bound - 1) < pair-slots * program-bound
          body-cap-bounded : closure-body-cap ≤ pair-slots *ℕ program-bound
          body-cap-bounded = ≤-trans
            (subst (_≤ pair-slots *ℕ ir-size body) (sym closure-body-cap-eq) (ir-req-≤-pair-slots*size body))
            (*-monoʳ-≤ pair-slots (<⇒≤ body<bound))

      -- slot bounds for pair-input-loc components (needed for child frame transfer)
      pair-slot-bound : next-slot alloc < next-slot alloc +ℕ pair-slots
      pair-slot-bound = m<m+n (next-slot alloc) {pair-slots} (s≤s z≤n)
        where
          open import Data.Nat.Properties using (m<m+n)

      sucLoc-pair-slot-bound : suc (next-slot alloc) < next-slot alloc +ℕ pair-slots
      sucLoc-pair-slot-bound = suc<+2 (next-slot alloc)

      -- pair-input-loc is BeforeFrontier in child-alloc via stack-ancestor
      -- (pair-input-loc is in parent frame, which is above child frame)
      pair-input-before-child : BeforeFrontier child-alloc pair-input-loc
      pair-input-before-child = stack-ancestor child-frame-below-parent (src-origin (next-slot alloc +ℕ pair-slots) pair-slot-bound)

      -- BeforeFrontier for pair components in alloc-pair (for constructing ValidAtWF)
      pair-input-before-pair : BeforeFrontier alloc-pair pair-input-loc
      pair-input-before-pair = stack-before refl pair-slot-bound

      sucLoc-pair-before-pair : BeforeFrontier alloc-pair (sucLoc pair-input-loc)
      sucLoc-pair-before-pair = stack-before refl sucLoc-pair-slot-bound

      -- env-loc and arg-loc are BeforeFrontier in child-alloc via stack-ancestor
      env-before-child : BeforeFrontier child-alloc env-loc
      env-before-child = bf-transfer-to-child env-loc env-before
        where
          bf-transfer-to-child : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier child-alloc loc
          bf-transfer-to-child (OnStack f k) (stack-before refl k<ns) =
            stack-ancestor child-frame-below-parent (src-origin (next-slot alloc) k<ns)
          bf-transfer-to-child (OnStack f k) (stack-ancestor cf≺f src) =
            stack-ancestor (≺-trans child-frame-below-parent cf≺f) src
          bf-transfer-to-child (OnHeap hl) (heap-before r<hr) = heap-before r<hr

      arg-before-child : BeforeFrontier child-alloc arg-loc
      arg-before-child = bf-transfer-to-child arg-loc arg-before
        where
          bf-transfer-to-child : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier child-alloc loc
          bf-transfer-to-child (OnStack f k) (stack-before refl k<ns) =
            stack-ancestor child-frame-below-parent (src-origin (next-slot alloc) k<ns)
          bf-transfer-to-child (OnStack f k) (stack-ancestor cf≺f src) =
            stack-ancestor (≺-trans child-frame-below-parent cf≺f) src
          bf-transfer-to-child (OnHeap hl) (heap-before r<hr) = heap-before r<hr

      -- env-loc and arg-loc are BeforeFrontier in alloc-pair (for ValidAtWF construction)
      env-before-pair : BeforeFrontier alloc-pair env-loc
      env-before-pair = stack-alloc-advances alloc pair-slots apply-pair-fits env-loc env-before

      arg-before-pair : BeforeFrontier alloc-pair arg-loc
      arg-before-pair = stack-alloc-advances alloc pair-slots apply-pair-fits arg-loc arg-before

      -- Modes for env and arg from decomposition
      mEnv = ClosureValidWF.mEnv closure-decomp

      -- PROVEN: env-valid-wf-pair via write helpers and alloc-advance
      env-valid-wf-pair : ValidAtWF mEnv alloc-pair env env-loc s-pair
      env-valid-wf-pair =
        validityWF-alloc-advance env env-loc s-pair pair-slots apply-pair-fits
          (validityWF-mem-only env env-loc s-write-arg s-pair refl refl
            (validityWF-write-at-suc-frontier env env-loc s-write-env arg-loc env-before
              (validityWF-write-at-frontier env env-loc s env-loc env-before
                env-valid-wf)))

      -- PROVEN: arg-valid-wf-pair via write helpers and alloc-advance
      arg-valid-wf-pair : ValidAtWF mArg alloc-pair arg arg-loc s-pair
      arg-valid-wf-pair =
        validityWF-alloc-advance arg arg-loc s-pair pair-slots apply-pair-fits
          (validityWF-mem-only arg arg-loc s-write-arg s-pair refl refl
            (validityWF-write-at-suc-frontier arg arg-loc s-write-env arg-loc arg-before
              (validityWF-write-at-frontier arg arg-loc s env-loc arg-before
                arg-valid-wf)))

      pair-env-ptr : readLoc s-pair pair-input-loc ≡ just env-loc
      pair-env-ptr = trans refl (trans
                       (write-preserves-disjoint s-write-env (sucLoc pair-input-loc) arg-loc pair-input-loc
                         (sucLoc-neq pair-input-loc))
                       (write-read-same s pair-input-loc env-loc stack-valid))

      pair-arg-ptr : readLoc s-pair (sucLoc pair-input-loc) ≡ just arg-loc
      pair-arg-ptr = write-read-same s-write-env (sucLoc pair-input-loc) arg-loc stack-valid

      -- Construct ValidAtWF for the pair in alloc-pair
      -- The constructed pair is boxed (Heap mode) with env and arg components
      pair-input-valid-pair : ValidAtWF Heap alloc-pair {EnvType * A} (pair env arg) pair-input-loc s-pair
      pair-input-valid-pair = valid-pair-wf pair-env-ptr pair-arg-ptr
                                env-before-pair arg-before-pair sucLoc-pair-before-pair
                                env-valid-wf-pair arg-valid-wf-pair

      -- Transfer pair validity to child-alloc for body execution
      -- Need ValidAtWF in child-alloc, but body expects input in the same alloc
      -- We use validityWF-with-bf-transfer to transfer
      pair-input-valid-child : ValidAtWF Heap child-alloc {EnvType * A} (pair env arg) pair-input-loc s-pair
      pair-input-valid-child = validityWF-with-bf-transfer {Heap} {EnvType * A}
        (pair env arg) pair-input-loc s-pair
        alloc-pair child-alloc
        bf-transfer pair-input-valid-pair
        where
          bf-transfer : ∀ loc' → BeforeFrontier alloc-pair loc' → BeforeFrontier child-alloc loc'
          bf-transfer (OnStack f k) (stack-before refl k<ns) =
            stack-ancestor child-frame-below-parent (src-origin (next-slot alloc +ℕ pair-slots) k<ns)
          bf-transfer (OnStack f k) (stack-ancestor cf≺f src) =
            stack-ancestor (≺-trans child-frame-below-parent cf≺f) src
          bf-transfer (OnHeap hl) (heap-before r<hr) = heap-before r<hr

      ------------------------------------------------------------------------
      -- Step 5: Execute body in child frame
      --
      -- Body executes with child-alloc (fresh child frame with child-capacity).
      -- Body's stack allocations are in child frame (not parent).
      -- Result must be on heap (all-escape property) to be valid in parent.
      ------------------------------------------------------------------------

      body-exec-result : ∃[ mOut ] IRResultAWF mOut body (pair env arg) s-pair child-alloc
      body-exec-result = BodyCorrect.execute body-correct arg arg-loc pair-input-loc
                           s-pair child-alloc Heap
                           pair-input-valid-child pair-input-before-child pair-not-halted pair-rdi-eq
                           body-cap-in-child
      mBody = proj₁ body-exec-result
      body-result = proj₂ body-exec-result

      ------------------------------------------------------------------------
      -- Step 6: Apply's reclaim = slot + pair-slots (body allocations in child)
      --
      -- Body's allocations are in child frame, so apply's reclaimable-slot
      -- is simply slot + pair-slots.
      ------------------------------------------------------------------------

      -- Extract fields from body result
      result-loc = IRResultAWF.result-loc body-result
      s-final = IRResultAWF.final-state body-result
      rax-eq = IRResultAWF.rax-is-result body-result
      not-halted-final = IRResultAWF.not-halted body-result

      -- Apply's final-alloc uses slot + pair-slots (not body's reclaimable)
      final-alloc : AllocState {FS}
      final-alloc = record alloc
        { next-slot = next-slot alloc +ℕ pair-slots
        ; slots-available = apply-pair-fits
        }

      -- Result BeforeFrontier transfer: child-alloc → final-alloc (parent)
      --
      -- ALL-ESCAPE PROPERTY: Body's result must be on heap because it escapes
      -- the child frame. Stack-allocated results in child frame would become
      -- invalid when child frame is deallocated.
      --
      -- With all-escape, result-loc is OnHeap, so transfer is trivial via heap-before.
      -- The OnStack cases are impossible by all-escape.
      body-final-alloc = IRResultAWF.final-alloc body-result

      ------------------------------------------------------------------------
      -- FRAME TRANSFER PROOF
      --
      -- Transfer BeforeFrontier from body-final-alloc (child) to final-alloc (parent).
      -- Uses LIFO stack discipline: escaping values can only reference ancestor frames.
      --
      -- Case 1: stack-before (f = child-frame)
      --   Impossible for escaping values - would be use-after-free.
      --   If escape analysis is correct, this case never occurs.
      --
      -- Case 2: stack-ancestor (child ≺ f)
      --   Using ≺-compare f parent:
      --   - parent ≺ f: use stack-ancestor directly
      --   - f ≡ parent: extract bound from src, use stack-before
      --   - f ≺ parent: impossible (would mean f between child and parent)
      ------------------------------------------------------------------------

      -- Helper: the parent frame for clarity
      parent-frame = current-frame alloc

      -- Frame preserved: body-final-alloc has same frame as child-alloc
      body-frame-is-child : current-frame body-final-alloc ≡ child-frame
      body-frame-is-child = trans (IRResultAWF.frame-preserved body-result) refl

      -- Bound tracking note: bounds in StackAncestorSource are set to
      -- next-slot alloc + pair-slots by bf-transfer, which equals
      -- next-slot final-alloc by definition of final-alloc.

      -- Derive SurvivesFramePop for any location with BeforeFrontier body-final
      get-survives : ∀ loc → BeforeFrontier body-final-alloc loc → SurvivesFramePop child-frame loc
      get-survives loc bf = escape-result-survives alloc body-final-alloc loc body-frame-is-child bf

      -- Helper: convert bound to final-alloc.next-slot using parent-bound-eq
      k<final : ∀ {k} (bound : ℕ) → k < bound → k < next-slot final-alloc
      k<final {k} bound k<bound = subst (k <_) (parent-bound-eq alloc bound) k<bound

      -- Helper: transfer stack-ancestor with frame comparison
      -- StackAncestorSource has type: origin-frame → Frame → ℕ → ℕ → Set
      transfer-ancestor : ∀ origin-frame f k bound →
        child-frame ≺ f →
        StackAncestorSource origin-frame f k bound →
        BeforeFrontier final-alloc (OnStack f k)
      transfer-ancestor origin-frame f k bound child≺f src with ≺-compare f parent-frame
      transfer-ancestor .f f k bound child≺f (src-origin _ k<bound) | inj₂ (inj₂ pf≺f) = stack-ancestor pf≺f (src-origin bound k<bound)
      transfer-ancestor .f f k bound child≺f (src-origin _ k<bound) | inj₂ (inj₁ refl) = stack-before refl (k<final bound k<bound)
      transfer-ancestor .f f k bound child≺f (src-origin _ k<bound) | inj₁ f≺pf = ⊥-elim (child-frame-adjacent alloc f child≺f f≺pf)
      transfer-ancestor origin-frame f k bound child≺f (src-above-origin of≺f _ k<bound) | inj₂ (inj₂ pf≺f) = stack-ancestor pf≺f (src-above-origin of≺f bound k<bound)
      transfer-ancestor origin-frame f k bound child≺f (src-above-origin of≺f _ k<bound) | inj₂ (inj₁ refl) = stack-before refl (k<final bound k<bound)
      transfer-ancestor origin-frame f k bound child≺f (src-above-origin of≺f _ k<bound) | inj₁ f≺pf = ⊥-elim (child-frame-adjacent alloc f child≺f f≺pf)

      -- Transfer BeforeFrontier from child's final-alloc to parent's final-alloc
      -- Uses SurvivesFramePop (from escape analysis) to eliminate stack-before case
      bf-child-to-parent-stack : ∀ f k →
        BeforeFrontier body-final-alloc (OnStack f k) →
        BeforeFrontier final-alloc (OnStack f k)
      bf-child-to-parent-stack f k bf with get-survives (OnStack f k) bf
      -- Case 1: stack-before means f = child-frame (impossible by escape analysis)
      bf-child-to-parent-stack f k (stack-before f≡body-frame k<ns) | in-ancestor child≺f =
        ⊥-elim (≺-irrefl (subst (child-frame ≺_) (trans f≡body-frame body-frame-is-child) child≺f))
      -- Case 2: stack-ancestor
      bf-child-to-parent-stack f k (stack-ancestor {origin-frame = origin-frame} {bound = bound} cf≺f src) | in-ancestor child≺f =
        transfer-ancestor origin-frame f k bound child≺f src

      bf-child-to-parent : ∀ loc → BeforeFrontier body-final-alloc loc → BeforeFrontier final-alloc loc
      bf-child-to-parent (OnHeap hl) (heap-before r<hr) =
        heap-before (subst (ref-id (heap-ref hl) <_) heap-ref-chain r<hr)
          where
            heap-ref-chain : next-heap-ref body-final-alloc ≡ next-heap-ref final-alloc
            heap-ref-chain = trans (IRResultAWF.heap-preserved body-result) refl
      bf-child-to-parent (OnStack f k) bf = bf-child-to-parent-stack f k bf

      result-before : BeforeFrontier final-alloc result-loc
      result-before = bf-child-to-parent result-loc (IRResultAWF.result-before body-result)

      ------------------------------------------------------------------------
      -- Memory preservation proof
      ------------------------------------------------------------------------

      -- BeforeFrontier alloc → BeforeFrontier alloc-pair
      bf-alloc-to-pair : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-pair loc
      bf-alloc-to-pair loc bf = stack-alloc-advances alloc pair-slots apply-pair-fits loc bf

      -- BeforeFrontier alloc → BeforeFrontier child-alloc
      bf-alloc-to-child : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier child-alloc loc
      bf-alloc-to-child (OnStack f k) (stack-before refl k<ns) =
        stack-ancestor child-frame-below-parent (src-origin (next-slot alloc) k<ns)
      bf-alloc-to-child (OnStack f k) (stack-ancestor cf≺f src) =
        stack-ancestor (≺-trans child-frame-below-parent cf≺f) src
      bf-alloc-to-child (OnHeap hl) (heap-before r<hr) = heap-before r<hr

      mem-preserved-apply : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-apply loc bf = trans step1 (trans step2 (trans step3 step4))
        where
          bf-child : BeforeFrontier child-alloc loc
          bf-child = bf-alloc-to-child loc bf

          -- Step 1: s-final → s-pair (body execution preserves before-frontier in child-alloc)
          step1 : readLoc s-final loc ≡ readLoc s-pair loc
          step1 = IRResultAWF.mem-preserved-before body-result loc bf-child

          -- Step 2: s-pair → s-write-arg (register change only)
          step2 : readLoc s-pair loc ≡ readLoc s-write-arg loc
          step2 = readLoc-stackMem-eq s-pair s-write-arg loc refl refl

          -- Step 3: s-write-arg → s-write-env (write at suc-frontier preserves)
          step3 : readLoc s-write-arg loc ≡ readLoc s-write-env loc
          step3 = write-preserves-disjoint s-write-env (sucLoc pair-input-loc) arg-loc loc
                    (λ eq → suc-frontier-neq-before-wf alloc loc bf eq)

          -- Step 4: s-write-env → s (write at frontier preserves)
          step4 : readLoc s-write-env loc ≡ readLoc s loc
          step4 = write-preserves-disjoint s pair-input-loc env-loc loc
                    (λ eq → at-frontier-neq-before-wf alloc loc bf eq)

      ------------------------------------------------------------------------
      -- Frame/slot/heap properties
      ------------------------------------------------------------------------

      frame-preserved-apply : current-frame final-alloc ≡ current-frame alloc
      frame-preserved-apply = refl

      -- slot-monotone: alloc.slot ≤ slot + pair-slots
      slot-monotone-apply : next-slot alloc ≤ next-slot final-alloc
      slot-monotone-apply = m≤m+n (next-slot alloc) pair-slots

      heap-monotone-apply : next-heap-ref alloc ≤ next-heap-ref final-alloc
      heap-monotone-apply = ≤-refl

      heap-preserved-apply : next-heap-ref final-alloc ≡ next-heap-ref alloc
      heap-preserved-apply = refl

      capacity-preserved-apply : frame-capacity final-alloc ≡ frame-capacity alloc
      capacity-preserved-apply = refl

      ------------------------------------------------------------------------
      -- Result validity
      --
      -- Body's result must be valid in parent frame.
      -- If result is on heap, validity transfers directly.
      -- If result is on stack-ancestor, validity transfers via ancestor.
      ------------------------------------------------------------------------

      -- Transfer validity from child's final-alloc to parent's final-alloc
      -- (body-final-alloc already defined above)

      result-valid-wf : ValidAtWF mBody final-alloc {B} (eval apply x) result-loc s-final
      result-valid-wf = subst (λ f → ValidAtWF mBody final-alloc {B} (f arg) result-loc s-final)
                              (sym closure-is-body)
                              body-result-valid-at-final
        where
          -- Transfer body result validity to final-alloc
          -- Reuses bf-child-to-parent which handles OnHeap (proven) and OnStack (via escape params)
          body-result-valid-at-final : ValidAtWF mBody final-alloc {B} (eval body (pair env arg)) result-loc s-final
          body-result-valid-at-final = validityWF-with-bf-transfer {mBody} {B}
            (eval body (pair env arg)) result-loc s-final
            body-final-alloc final-alloc
            bf-child-to-parent  -- Same transfer function as result-before
            (IRResultAWF.result-valid-wf body-result)

      ------------------------------------------------------------------------
      -- Reclamation: apply's reclaimable-slot = slot + pair-slots
      --
      -- PROVEN! Body allocations are in child frame, so parent only has
      -- the pair allocation at slot + pair-slots.
      ------------------------------------------------------------------------

      apply-reclaimable-slot : ℕ
      apply-reclaimable-slot = next-slot alloc +ℕ pair-slots

      -- alloc.slot ≤ slot + pair-slots
      apply-reclaim-monotone : next-slot alloc ≤ apply-reclaimable-slot
      apply-reclaim-monotone = m≤m+n (next-slot alloc) pair-slots

      -- slot + pair-slots ≤ slot + pair-slots (final-alloc.slot = slot + pair-slots)
      apply-reclaim-bounded : apply-reclaimable-slot ≤ next-slot final-alloc
      apply-reclaim-bounded = ≤-refl

      apply-reclaim-preserves-result : ∀ (fits : apply-reclaimable-slot ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = apply-reclaimable-slot ; slots-available = fits }) result-loc
      apply-reclaim-preserves-result fits = bf-same-frame-slot final-alloc
        (record alloc { next-slot = apply-reclaimable-slot ; slots-available = fits })
        refl refl refl result-loc result-before

      -- Validity at reclaimed allocation - same as final-alloc
      apply-reclaim-preserves-validity : ∀ (fits : apply-reclaimable-slot ≤ frame-capacity alloc) →
        ValidAtWF mBody (record alloc { next-slot = apply-reclaimable-slot ; slots-available = fits })
                  (eval apply x) result-loc s-final
      apply-reclaim-preserves-validity fits = validityWF-with-bf-transfer {mBody} (eval apply x) result-loc s-final
        final-alloc
        (record alloc { next-slot = apply-reclaimable-slot ; slots-available = fits })
        (λ loc' bf → bf-same-frame-slot final-alloc
          (record alloc { next-slot = apply-reclaimable-slot ; slots-available = fits })
          refl refl refl loc' bf)
        result-valid-wf

      -- reclaim-size-bound: PROVEN! slot + pair-slots ≤ slot + ir-stack-requirement apply
      -- Since ir-stack-requirement apply = pair-slots, this is ≤-refl
      apply-reclaim-size-bound : apply-reclaimable-slot ≤ next-slot alloc +ℕ ir-stack-requirement (apply {A} {B})
      apply-reclaim-size-bound = ≤-refl
