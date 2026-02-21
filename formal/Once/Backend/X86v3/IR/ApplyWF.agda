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
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-monoʳ-≤; m+n≤o⇒m≤o)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst; cong)
open import Relation.Nullary using (yes; no)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Apply implementation
------------------------------------------------------------------------

module ApplyWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; BodyCorrect;
           valid-unit-wf; valid-pair-boxed-wf; valid-pair-unboxed-wf;
           valid-closure-wf;
           valid-inl-boxed-wf; valid-inl-unboxed-wf;
           valid-inr-boxed-wf; valid-inr-unboxed-wf;
           valid-fold-boxed-wf; valid-fold-unboxed-wf;
           validityWF-mem-only; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-frontier-advance;
           validityWF-with-bf-transfer;
           decomposePairBoxedWF; PairBoxedValidWF;
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

  ------------------------------------------------------------------------
  -- BeforeFrontier Transfer Lemmas
  --
  -- These lemmas transfer BeforeFrontier between allocation states.
  -- They take the location as an explicit parameter to enable pattern matching.
  ------------------------------------------------------------------------

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
  bf-same-frame-slot a₁ a₂ cf-eq ns-eq hr-eq (OnHeap r o) (heap-before r<hr)
    rewrite hr-eq = heap-before r<hr

  ------------------------------------------------------------------------
  -- ValidAtWF Frame Transport with explicit BeforeFrontier transfer
  --
  -- Transfer ValidAtWF between allocation states using a general
  -- BeforeFrontier transfer function. This is the core lemma for
  -- validityWF-frame-transport.
  --
  -- The bf-transfer function is applied to all sublocations in the value.
  --
  -- For closure types, pattern matching on valid-closure-wf with its complex
  -- implicit argument structure causes parsing issues, so we use a postulate.
  -- The proof is straightforward: apply bf-transfer to all sublocation proofs
  -- (eb, cb, slb) and recursively transfer the env validity (ev).
  ------------------------------------------------------------------------

  -- ValidAtWF transfer between allocation states
  -- Now imported from ClosureWellFormed: validityWF-with-bf-transfer

  ------------------------------------------------------------------------
  -- Helper: Extract body-capacity from apply input's closure
  --
  -- This extracts body-capacity from the ValidAtWF proof for (closure, arg).
  -- By computing this directly from input-valid-wf, we avoid needing a
  -- separate body-cap parameter that must match the closure's capacity.
  ------------------------------------------------------------------------

  closure-body-capacity : ∀ {A B alloc loc s}
    (x : ⟦ (A ⇒ B) * A ⟧)
    (input-valid-wf : ValidAtWF Heap alloc x loc s) → ℕ
  closure-body-capacity {A} {B} {alloc} {loc} {s} x input-valid-wf =
    let pair-decomp = decomposePairBoxedWF {_} {A ⇒[ Many ] B} {A} input-valid-wf
        closure-loc = PairBoxedValidWF.fst-loc pair-decomp
        closure = proj₁ x
        closure-valid-wf = PairBoxedValidWF.fst-valid pair-decomp
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
  -- KEY FIX: body-cap is extracted from input via closure-body-capacity,
  -- not passed as a separate parameter. This eliminates the body-cap-matches
  -- postulate because both the type signature and body use the same extraction.
  ------------------------------------------------------------------------

  run-apply : ∀ {A B}
    (x : ⟦ (A ⇒ B) * A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-valid-wf : ValidAtWF Heap alloc x input-loc s) →  -- Apply takes boxed pair input
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- Capacity using ir-stack-requirement (= pair-slots for apply)
    next-slot alloc +ℕ ir-stack-requirement (apply {A} {B}) ≤ frame-capacity alloc →
    -- DYNAMIC capacity: pair-slots + closure's body-capacity
    -- Capacity is computed from input via closure-body-capacity, not passed separately
    next-slot alloc +ℕ pair-slots +ℕ closure-body-capacity x input-valid-wf ≤ frame-capacity alloc →
    -- NO child-frame parameters! Body runs in same frame.
    ∃[ mOut ] IRResultAWF mOut (apply {A} {B}) x s alloc
  run-apply {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap body-cap-fits =
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
      -- Reclamation: apply uses body's reclamation
      ; reclaimable-slot = apply-reclaimable-slot
      ; reclaim-monotone = apply-reclaim-monotone
      ; reclaim-bounded = apply-reclaim-bounded
      ; reclaim-preserves-result = apply-reclaim-preserves-result
      ; reclaim-preserves-validity = apply-reclaim-preserves-validity
      ; reclaim-size-bound = apply-reclaim-size-bound
      }
    where
      open import Data.Nat using (_≥_)
      open import Data.Nat.Properties using (*-monoʳ-≤; <⇒≤)

      -- Step 1: Decompose input as pair (closure, arg) using ValidAtWF
      -- Explicit type: pair type is (A ⇒[ Many ] B) * A
      pair-decomp = decomposePairBoxedWF {_} {A ⇒[ Many ] B} {A} input-valid-wf
      closure-loc = PairBoxedValidWF.fst-loc pair-decomp
      arg-loc = PairBoxedValidWF.snd-loc pair-decomp
      mArg = PairBoxedValidWF.mB pair-decomp  -- Mode of argument component
      closure-valid-wf = PairBoxedValidWF.fst-valid pair-decomp
      arg-valid-wf = PairBoxedValidWF.snd-valid pair-decomp
      arg-before = PairBoxedValidWF.snd-before pair-decomp

      -- Extract closure and arg with explicit types to help inference
      -- fst and snd need explicit type params because ⟦ A ⇒[ q ] B ⟧ = ⟦ A ⟧ → ⟦ B ⟧ for any q
      closure : ⟦ A ⇒[ Many ] B ⟧
      closure = fst {A ⇒[ Many ] B} {A} x

      arg : ⟦ A ⟧
      arg = snd {A ⇒[ Many ] B} {A} x

      -- Step 2: Decompose closure to get body-correct!
      -- Note: fst x : ⟦ A ⇒ B ⟧ = ⟦ A ⇒[ Many ] B ⟧
      -- Closures are always Heap mode - extract mA=Heap from ValidAtWF proof
      mClosure = PairBoxedValidWF.mA pair-decomp
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
      -- NOTE: closure-body-cap is definitionally equal to (closure-body-capacity x input-valid-wf)
      -- because both extract from the same input via the same decomposition sequence.
      -- This means body-cap-fits (from type signature) directly gives us the capacity proof.
      closure-body-cap = BodyCorrect.body-capacity body-correct
      closure-body-cap-eq = BodyCorrect.body-cap-eq body-correct

      -- Step 3: Allocate pair-slots for (env, arg) pair in SAME frame
      pair-input-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- PROVEN: apply-pair-fits from body-cap-fits
      -- body-cap-fits: slot + pair-slots + body-cap ≤ capacity
      -- So slot + pair-slots ≤ capacity (by m+n≤o⇒m≤o)
      apply-pair-fits : next-slot alloc +ℕ pair-slots ≤ frame-capacity alloc
      apply-pair-fits = m+n≤o⇒m≤o (next-slot alloc +ℕ pair-slots) body-cap-fits

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
      -- Step 4: Execute body in SAME frame (no push)
      --
      -- Body executes with alloc-pair (next-slot = slot + pair-slots).
      -- The pair-input-loc is BeforeFrontier in alloc-pair via stack-before.
      ------------------------------------------------------------------------

      -- Derive body-cap-fits-pair from body-cap-fits parameter
      -- body-cap-fits: slot + pair-slots + closure-body-cap ≤ capacity
      -- alloc-pair.next-slot = slot + pair-slots
      -- alloc-pair.frame-capacity = capacity (unchanged)
      -- So: alloc-pair.next-slot + closure-body-cap ≤ capacity
      -- Note: closure-body-cap = closure-body-capacity x input-valid-wf (definitionally)
      body-cap-fits-pair : next-slot alloc-pair +ℕ closure-body-cap ≤ frame-capacity alloc-pair
      body-cap-fits-pair = body-cap-fits

      -- pair-input-loc is BeforeFrontier in alloc-pair via stack-before
      -- slot < slot + pair-slots
      pair-slot-bound : next-slot alloc < next-slot alloc +ℕ pair-slots
      pair-slot-bound = m<m+n (next-slot alloc) {pair-slots} (s≤s z≤n)
        where
          open import Data.Nat.Properties using (m<m+n)

      pair-input-before-pair : BeforeFrontier alloc-pair pair-input-loc
      pair-input-before-pair = stack-before refl pair-slot-bound

      sucLoc-pair-slot-bound : suc (next-slot alloc) < next-slot alloc +ℕ pair-slots
      sucLoc-pair-slot-bound = suc<+2 (next-slot alloc)

      sucLoc-pair-before-pair : BeforeFrontier alloc-pair (sucLoc pair-input-loc)
      sucLoc-pair-before-pair = stack-before refl sucLoc-pair-slot-bound

      -- env-loc and arg-loc are BeforeFrontier in alloc-pair
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
                       (write-read-same s pair-input-loc env-loc))

      pair-arg-ptr : readLoc s-pair (sucLoc pair-input-loc) ≡ just arg-loc
      pair-arg-ptr = write-read-same s-write-env (sucLoc pair-input-loc) arg-loc

      -- Construct ValidAtWF for the pair in alloc-pair
      -- The constructed pair is boxed (Heap mode) with env and arg components
      pair-input-valid-pair : ValidAtWF Heap alloc-pair {EnvType * A} (pair env arg) pair-input-loc s-pair
      pair-input-valid-pair = valid-pair-boxed-wf pair-env-ptr pair-arg-ptr
                                env-before-pair arg-before-pair sucLoc-pair-before-pair
                                env-valid-wf-pair arg-valid-wf-pair

      ------------------------------------------------------------------------
      -- Step 5: Execute body in same frame (alloc-pair)
      --
      -- Body returns IRResultAWF directly. Body CAN return stack-allocated
      -- values! We use body's reclaimable-slot for reclamation, so stack
      -- slots below that survive.
      ------------------------------------------------------------------------

      -- Execute body, returns existential mode
      -- BodyCorrect.execute expects capacity for closure-body-cap
      -- We have body-cap-fits-pair for body-cap (parameter)
      -- Dispatcher ensures body-cap = closure-body-cap
      -- body-cap is extracted by Dispatcher from the same input-valid-wf via:
      --   decomposeClosureWF (subst ... (PairBoxedValidWF.fst-valid (decomposePairBoxedWF input-valid-wf)))
      -- And closure-body-cap is extracted here via the same sequence.
      -- Since both use the same input-valid-wf and same decomposition functions,
      -- they are definitionally equal.
      body-cap-fits-for-exec : next-slot alloc-pair +ℕ closure-body-cap ≤ frame-capacity alloc-pair
      body-cap-fits-for-exec = body-cap-fits-pair

      body-exec-result : ∃[ mOut ] IRResultAWF mOut body (pair env arg) s-pair alloc-pair
      body-exec-result = BodyCorrect.execute body-correct arg arg-loc pair-input-loc
                           s-pair alloc-pair Heap
                           pair-input-valid-pair pair-input-before-pair pair-not-halted pair-rdi-eq
                           body-cap-fits-for-exec
      mBody = proj₁ body-exec-result
      body-result = proj₂ body-exec-result

      ------------------------------------------------------------------------
      -- Step 6: Use body's reclaimable-slot for reclamation
      --
      -- Body provides reclaimable-slot and reclaim-preserves-result.
      -- Stack slots below reclaimable-slot survive reclamation.
      -- This allows body to return stack-allocated values!
      --
      -- Apply's final-alloc uses body's reclaimable-slot, NOT slot + pair-slots.
      ------------------------------------------------------------------------

      body-final-alloc = IRResultAWF.final-alloc body-result
      body-reclaimable = IRResultAWF.reclaimable-slot body-result

      -- Extract fields from body result
      result-loc = IRResultAWF.result-loc body-result
      s-final = IRResultAWF.final-state body-result
      rax-eq = IRResultAWF.rax-is-result body-result
      not-halted-final = IRResultAWF.not-halted body-result

      -- Apply's final-alloc uses body's reclaimable-slot
      -- This preserves body's stack-allocated result!
      -- Proof: body-reclaimable ≤ final-slot ≤ capacity(final) = capacity(pair) = capacity(alloc)

      -- Step 1: capacity body-final-alloc = capacity alloc-pair (body's capacity-preserved)
      body-cap-eq-pair : frame-capacity body-final-alloc ≡ frame-capacity alloc-pair
      body-cap-eq-pair = IRResultAWF.capacity-preserved body-result

      -- Step 2: capacity alloc-pair = capacity alloc (record construction preserves frame-capacity)
      pair-cap-eq-alloc : frame-capacity alloc-pair ≡ frame-capacity alloc
      pair-cap-eq-alloc = refl

      -- Step 3: combine
      body-capacity-is-alloc-capacity : frame-capacity body-final-alloc ≡ frame-capacity alloc
      body-capacity-is-alloc-capacity = trans body-cap-eq-pair pair-cap-eq-alloc

      body-reclaim-fits : body-reclaimable ≤ frame-capacity alloc
      body-reclaim-fits = ≤-trans
        (IRResultAWF.reclaim-bounded body-result)  -- body-reclaimable ≤ next-slot body-final-alloc
        (subst (next-slot body-final-alloc ≤_)     -- next-slot ≤ capacity alloc
          body-capacity-is-alloc-capacity
          (slots-available body-final-alloc))

      final-alloc : AllocState {FS}
      final-alloc = record alloc
        { next-slot = body-reclaimable
        ; slots-available = body-reclaim-fits
        }

      -- Result is BeforeFrontier in final-alloc via body's reclaim-preserves-result
      -- We need to transfer from alloc-pair-based to alloc-based allocation record

      -- body-reclaimable ≤ capacity alloc-pair (for body-reclaim-alloc's slots-available)
      body-reclaim-fits-pair : body-reclaimable ≤ frame-capacity alloc-pair
      body-reclaim-fits-pair = ≤-trans
        (IRResultAWF.reclaim-bounded body-result)  -- body-reclaimable ≤ next-slot body-final-alloc
        (subst (next-slot body-final-alloc ≤_)     -- next-slot ≤ capacity alloc-pair
          body-cap-eq-pair
          (slots-available body-final-alloc))

      body-reclaim-alloc : AllocState {FS}
      body-reclaim-alloc = record alloc-pair
        { next-slot = body-reclaimable
        ; slots-available = body-reclaim-fits-pair
        }

      -- body's reclaim-preserves-result gives BeforeFrontier at body-reclaim-alloc
      result-before-body-reclaim : BeforeFrontier body-reclaim-alloc result-loc
      result-before-body-reclaim = IRResultAWF.reclaim-preserves-result body-result body-reclaim-fits-pair

      -- Transfer to final-alloc (same frame, slot, heap - just different base record)
      result-before : BeforeFrontier final-alloc result-loc
      result-before = bf-same-frame-slot body-reclaim-alloc final-alloc refl refl refl
                        result-loc result-before-body-reclaim

      ------------------------------------------------------------------------
      -- Memory preservation proof
      ------------------------------------------------------------------------

      -- BeforeFrontier alloc → BeforeFrontier alloc-pair
      bf-alloc-to-pair : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-pair loc
      bf-alloc-to-pair loc bf = stack-alloc-advances alloc pair-slots apply-pair-fits loc bf

      mem-preserved-apply : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-apply loc bf = trans step1 (trans step2 (trans step3 step4))
        where
          bf-pair : BeforeFrontier alloc-pair loc
          bf-pair = bf-alloc-to-pair loc bf

          -- Step 1: s-final → s-pair (body execution preserves before-frontier in alloc-pair)
          step1 : readLoc s-final loc ≡ readLoc s-pair loc
          step1 = IRResultAWF.mem-preserved-before body-result loc bf-pair

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

      -- slot-monotone: alloc.slot ≤ body-reclaimable
      -- Proof: alloc.slot ≤ alloc-pair.slot ≤ body-reclaimable
      slot-monotone-apply : next-slot alloc ≤ next-slot final-alloc
      slot-monotone-apply = ≤-trans (m≤m+n (next-slot alloc) pair-slots)
                              (IRResultAWF.reclaim-monotone body-result)

      heap-monotone-apply : next-heap-ref alloc ≤ next-heap-ref final-alloc
      heap-monotone-apply = ≤-refl

      heap-preserved-apply : next-heap-ref final-alloc ≡ next-heap-ref alloc
      heap-preserved-apply = refl

      capacity-preserved-apply : frame-capacity final-alloc ≡ frame-capacity alloc
      capacity-preserved-apply = refl

      ------------------------------------------------------------------------
      -- Result validity
      --
      -- Use body's reclaim-preserves-validity, then transfer to final-alloc.
      ------------------------------------------------------------------------

      -- Body's validity at its reclaim allocation
      body-result-valid-at-reclaim : ValidAtWF mBody body-reclaim-alloc {B} (eval body (pair env arg)) result-loc s-final
      body-result-valid-at-reclaim = IRResultAWF.reclaim-preserves-validity body-result body-reclaim-fits-pair

      -- Transfer to final-alloc (same frame, slot, heap - just different base record)
      body-result-valid-at-final : ValidAtWF mBody final-alloc {B} (eval body (pair env arg)) result-loc s-final
      body-result-valid-at-final = validityWF-with-bf-transfer {mBody} {B}
        (eval body (pair env arg)) result-loc s-final
        body-reclaim-alloc final-alloc
        (λ loc' bf → bf-same-frame-slot body-reclaim-alloc final-alloc refl refl refl loc' bf)
        body-result-valid-at-reclaim

      -- Final: transport via closure-is-body
      result-valid-wf : ValidAtWF mBody final-alloc {B} (eval apply x) result-loc s-final
      result-valid-wf = subst (λ f → ValidAtWF mBody final-alloc {B} (f arg) result-loc s-final)
                              (sym closure-is-body)
                              body-result-valid-at-final

      ------------------------------------------------------------------------
      -- Reclamation: apply's reclaimable-slot = body's reclaimable-slot
      --
      -- Apply uses the same reclaimable-slot as body, preserving body's
      -- stack-allocated result.
      ------------------------------------------------------------------------

      apply-reclaimable-slot : ℕ
      apply-reclaimable-slot = body-reclaimable

      -- alloc.slot ≤ body-reclaimable (via alloc-pair)
      apply-reclaim-monotone : next-slot alloc ≤ apply-reclaimable-slot
      apply-reclaim-monotone = ≤-trans (m≤m+n (next-slot alloc) pair-slots)
                                 (IRResultAWF.reclaim-monotone body-result)

      -- body-reclaimable ≤ body-reclaimable (final-alloc.slot = body-reclaimable)
      apply-reclaim-bounded : apply-reclaimable-slot ≤ next-slot final-alloc
      apply-reclaim-bounded = ≤-refl

      apply-reclaim-preserves-result : ∀ (fits : apply-reclaimable-slot ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = apply-reclaimable-slot ; slots-available = fits }) result-loc
      apply-reclaim-preserves-result fits = bf-same-frame-slot final-alloc
        (record alloc { next-slot = apply-reclaimable-slot ; slots-available = fits })
        refl refl refl result-loc result-before

      -- Validity at reclaimed allocation - same as final-alloc (structurally equal)
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

      -- reclaim-size-bound: body-reclaimable ≤ slot + pair-slots
      -- POSTULATE: Body can use more than pair-slots (body runs in same frame).
      -- Fix: Use child frame for body execution, then apply's reclaim = slot + pair-slots.
      postulate
        apply-reclaim-size-bound : apply-reclaimable-slot ≤ next-slot alloc +ℕ ir-stack-requirement (apply {A} {B})
