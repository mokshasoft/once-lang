-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.ClosureWellFormed
--
-- Well-formedness predicate for closures with pre-computed body proofs.
--
-- This is the key to eliminating termination issues in Apply.
-- Instead of Apply calling run-ir recursively, it uses a pre-computed
-- proof stored in the closure.
--
-- Pattern from X86:
-- 1. Curry constructs ClosureWellFormed with body-correct proof
-- 2. body-correct is built using rec (the recursive dispatcher)
-- 3. Apply extracts and uses body-correct instead of calling run-ir
--
-- This breaks the recursive cycle: Apply doesn't call run-ir,
-- it just uses the stored proof.
------------------------------------------------------------------------

module Once.CCC.Machine.ClosureWellFormed where

open import Data.Nat using (ℕ; _<_; _≤_; _≥_; suc; zero) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
import Once.CCC.Machine.SMPrimitives as SMP
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import μ-type/ν-type and WellFormedF for recursive type validity
open import Once.Type using (μ-type; ν-type; Functor)
open import Once.Functor.Translate using (WellFormedF)

-- Import MuValidity for μValid/νValid
import Once.CCC.Machine.IR.MuValidity as MV

------------------------------------------------------------------------
-- BodyResult: Result type for body execution
--
-- When a closure body executes with (env, arg), it produces this result.
-- This is essentially IRResultA specialized to the body.
------------------------------------------------------------------------

module ClosureWellFormedDef {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.CCC.Machine.Validity
  open ValidityDef {FS} program-bound
    using (readLoc-stack-heap-eq)
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open AbstractExec {FS}
  open TracePrimitives {FS}
  open FrameSemantics FS

  -- Import μValid/νValid and preservation lemmas from MuValidity
  open MV.MuValidityImpl {FS} program-bound
    using (μValid; νValid;
           μValid-mem-only; νValid-mem-only;
           μValid-frontier-advance; νValid-frontier-advance;
           μValid-bf-transfer; νValid-bf-transfer;
           μValid-mem-preserved; νValid-mem-preserved)

  -- Import write operations for validity preservation proofs
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- NOTE: Old static capacity reasoning (CapacityInvariant, SlotInWorking) has been removed.
  -- Dynamic capacity is now per-closure via BodyCorrect.body-capacity.

  ------------------------------------------------------------------------
  -- Mutual block for ValidAtWF, IRResultAWF, BodyCorrect
  --
  -- ValidAtWF is indexed by AllocMode as FIRST parameter.
  -- Each constructor FIXES its output mode in the type:
  --   valid-pair-boxed-wf  : ... → ValidAtWF Heap alloc {A * B} ...
  --   valid-pair-unboxed-wf : ... → ValidAtWF Stack alloc {A * B} ...
  --
  -- This enforces correct representation at the type level:
  -- - Handler for ⟨ f , g ⟩ Stack MUST produce ValidAtWF Stack (unboxed)
  -- - Handler for ⟨ f , g ⟩ Heap MUST produce ValidAtWF Heap (boxed)
  --
  -- Non-allocating handlers (fst, snd, id, etc.) pattern match on input
  -- ValidAtWF to discover the mode, and return the same mode.
  ------------------------------------------------------------------------

  mutual
    --------------------------------------------------------------------
    -- ValidAtWF: Mode-indexed validity
    --
    -- First parameter is AllocMode - determines memory representation.
    -- Constructor choice is FORCED by the mode:
    --   Stack → must use unboxed constructors
    --   Heap  → must use boxed constructors
    --------------------------------------------------------------------

    data ValidAtWF : AllocMode → AllocState {FS} →
         {A : Type} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set where

      -- Unit: valid at any mode (no representation difference)
      valid-unit-wf : ∀ {m alloc loc s} →
        ValidAtWF m alloc {Unit} tt loc s

      -- Pair (any mode): two pointers at pair-loc, sucLoc pair-loc
      -- Reference-based model: Stack and Heap use identical representation
      valid-pair-wf : ∀ {m A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
        {alloc : AllocState {FS}}
        {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS}
        {mA mB : AllocMode} →  -- Component modes can be anything
        readLoc s pair-loc ≡ just fst-loc →
        readLoc s (sucLoc pair-loc) ≡ just snd-loc →
        BeforeFrontier alloc fst-loc →
        BeforeFrontier alloc snd-loc →
        BeforeFrontier alloc (sucLoc pair-loc) →
        ValidAtWF mA alloc a fst-loc s →
        ValidAtWF mB alloc b snd-loc s →
        ValidAtWF m alloc {A * B} (a , b) pair-loc s

      -- Closure: always boxed (env-ptr + code-ptr), output mode is Heap
      -- Kind-polymorphic: handles both pure (⇒[ mk-kind q pure ]) and effectful (Eff) arrows
      -- since their runtime representation is identical.
      valid-closure-wf : ∀ {EnvType k A B}
        {body : IR (EnvType * A) B}
        {env : ⟦ EnvType ⟧}
        {alloc : AllocState {FS}}
        (body<bound : ir-size body < program-bound) →
        {closure-loc env-loc code-loc : ValueLocation FS} {s : LocState FS}
        {mEnv : AllocMode} →  -- Env mode can be anything
        readLoc s closure-loc ≡ just env-loc →
        readLoc s (sucLoc closure-loc) ≡ just code-loc →
        BeforeFrontier alloc env-loc →
        BeforeFrontier alloc code-loc →
        BeforeFrontier alloc (sucLoc closure-loc) →
        ValidAtWF mEnv alloc env env-loc s →
        BodyCorrect body env env-loc program-bound →
        ValidAtWF Heap alloc {A ⇒[ k ] B} (λ arg → eval body (pair env arg)) closure-loc s

      -- Sum inl (any mode): tag + payload-ptr
      -- Reference-based model: Stack and Heap use identical representation
      valid-inl-wf : ∀ {m A B} {a : ⟦ A ⟧}
        {alloc : AllocState {FS}}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS}
        {mA : AllocMode} →
        readLoc s (sucLoc sum-loc) ≡ just payload-loc →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        ValidAtWF mA alloc a payload-loc s →
        ValidAtWF m alloc {A + B} (sem-inl a) sum-loc s

      -- Sum inr (any mode): tag + payload-ptr
      -- Reference-based model: Stack and Heap use identical representation
      valid-inr-wf : ∀ {m A B} {b : ⟦ B ⟧}
        {alloc : AllocState {FS}}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS}
        {mB : AllocMode} →
        readLoc s (sucLoc sum-loc) ≡ just payload-loc →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        ValidAtWF mB alloc b payload-loc s →
        ValidAtWF m alloc {A + B} (sem-inr b) sum-loc s

      -- OCP-0003: μ-type and ν-type validity via MuValidity predicates
      -- These wrap μValid/νValid from MuValidity, avoiding pattern matching issues
      -- by keeping the layer type opaque to ValidAtWF pattern matching.
      valid-μ-wf : ∀ {m F}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS}
        (wf : WellFormedF F)
        (x : ⟦ μ-type F ⟧) →
        μValid alloc wf x loc s →
        ValidAtWF m alloc {μ-type F} x loc s

      valid-ν-wf : ∀ {m F}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS}
        (wf : WellFormedF F)
        (x : ⟦ ν-type F ⟧) →
        νValid alloc wf x loc s →
        ValidAtWF m alloc {ν-type F} x loc s

      -- Primitive types: valid at any mode if location is before frontier
      -- Primitives are single-slot values (Int, Float, Str, Buffer).
      -- No structural constraints needed - just location validity.
      valid-int-wf : ∀ {m} {n : ⟦ Int ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Int} n loc s

      valid-float-wf : ∀ {m} {x : ⟦ Float ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Float} x loc s

      valid-str-wf : ∀ {m} {x : ⟦ Str ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Str} x loc s

      valid-buffer-wf : ∀ {m} {x : ⟦ Buffer ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Buffer} x loc s

      -- Effectful morphism: runtime-identical to a pure closure.
      -- `arr` coerces a pure closure (A ⇒[ mk-kind q pure ] B) to the effect-tagged
      -- shape (A ⇒[ mk-kind Many eff ] B) without altering the witness.
      valid-coerce-kind-wf : ∀ {m A B q}
        {f : ⟦ A ⟧ → ⟦ B ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        ValidAtWF m alloc {A ⇒[ mk-kind q pure ] B} f loc s →
        ValidAtWF m alloc {A ⇒[ mk-kind Many eff ] B} f loc s

    --------------------------------------------------------------------
    -- valid-primitive-wf: Dispatch on FitsInReg evidence
    --
    -- For register-fittable primitive types, ValidAtWF only needs
    -- BeforeFrontier. Plan 0.2.4.5: legacy IsPrimitive retired —
    -- Unit is erased (no slot), Str/Buffer are 2-slot compounds with
    -- their own valid-str-wf / valid-buffer-wf witnesses. The only
    -- inhabitants left are Int and Float.
    --------------------------------------------------------------------

    valid-primitive-wf : ∀ {m} {B : Type} {v : ⟦ B ⟧}
      {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS} →
      FitsInReg B →
      BeforeFrontier alloc loc →
      ValidAtWF m alloc {B} v loc s
    valid-primitive-wf fits-int   bf = valid-int-wf bf
    valid-primitive-wf fits-float bf = valid-float-wf bf

    --------------------------------------------------------------------
    -- IRResultAWF: Mode-indexed IR execution result
    --
    -- Indexed by output mode m. For allocating IRs:
    --   run-pair for ⟨ f , g ⟩ Stack → IRResultAWF Stack ...
    --   run-pair for ⟨ f , g ⟩ Heap  → IRResultAWF Heap ...
    --
    -- For non-allocating IRs (fst, snd, id, etc.), the mode comes
    -- from pattern matching on input validity.
    --------------------------------------------------------------------

    -- Plan 0.2.4.5 D1 (Unit erasure): for Unit-typed results the
    -- value is genuinely "nowhere" — no register, no slot, no
    -- observable content. `rax-is-result` ("Output holds the
    -- result-loc") gets a vacuous case for Unit so the spec doesn't
    -- have to lie about a non-existent equation.
    --
    -- Modeled as a data type so it works with B as a free variable:
    -- producers pick the constructor (`rax-output-eq` for non-Unit,
    -- `rax-erased` for Unit), consumers case-split. For non-Unit B
    -- the existing equation is preserved unchanged.
    data RaxConstraint : (B : Type) → LocState FS → ValueLocation FS → Set where
      rax-output-eq : ∀ {B s loc} → readReg (regs s) Output ≡ loc → RaxConstraint B s loc
      rax-erased    : ∀ {s loc} → RaxConstraint Unit s loc

    -- Plan 0.2.4.5 D1: extract the Output equation from the
    -- type-indexed rax-is-result. Used by consumers (compose,
    -- pair, RecTrace) that haven't yet split their proofs into a
    -- Unit-aware case branch. The Unit case requires a postulate
    -- stub — this is a TODO until consumers learn to dispatch on
    -- the constructor properly. (Run-terminal is the only producer
    -- that currently emits `rax-erased`, so the postulate is hit
    -- only when terminal is composed without elaboration eliding
    -- the redundancy first.)
    extract-rax-eq : ∀ {B s loc} → RaxConstraint B s loc →
                     readReg (regs s) Output ≡ loc
    extract-rax-eq (rax-output-eq eq) = eq
    extract-rax-eq {Unit} {s} {loc} rax-erased = unit-rax-stub s loc
      where postulate unit-rax-stub : ∀ s loc → readReg (regs s) Output ≡ loc

    record IRResultAWF (m : AllocMode)
                       {A B : Type}
                       (ir : IR A B)
                       (x : ⟦ A ⟧)
                       (s : LocState FS)
                       (alloc : AllocState {FS}) : Set where
      inductive
      field
        result-loc : ValueLocation FS
        final-state : LocState FS
        -- Compile-time allocation state (Dispatcher's bookkeeping)
        -- Has incremented next-slot for BeforeFrontier/validity reasoning
        final-alloc : AllocState {FS}
        -- Trace: sequence of abstract instructions that produces this result
        trace : AbstractTrace
        -- Runtime trace correctness: proves state transformation
        -- Note: exec-trace returns (final-state, alloc) for non-apply IRs
        -- since next-slot is compile-time only and traces don't modify it
        trace-correct : proj₁ (exec-trace trace s alloc) ≡ final-state
        -- Existing validity fields
        result-valid-wf : ValidAtWF m final-alloc (eval ir x) result-loc final-state
        result-before : BeforeFrontier final-alloc result-loc
        rax-is-result : RaxConstraint B final-state result-loc
        not-halted : halted final-state ≡ false
        frame-preserved : current-frame final-alloc ≡ current-frame alloc
        slot-monotone : next-slot alloc ≤ next-slot final-alloc
        heap-monotone : next-heap-ref alloc ≤ next-heap-ref final-alloc
        -- Note: capacity-preserved removed in Phase 3 (frame-capacity removed from AllocState)
        -- Note: mem-preserved-before removed in Phase 4 - use irresult-mem-preserved instead
        -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
        --   With perfect reclaim, reclaimable-slot ≡ next-slot final-alloc, so:
        --   - reclaim-monotone = slot-monotone
        --   - reclaim-size-bound = slot-stays-in-budget
        -- Result is BeforeFrontier relative to original alloc with advanced next-slot
        -- (Needed for compositional proofs - can't be derived from result-before for heap results)
        reclaim-preserves-result :
          BeforeFrontier (record alloc { next-slot = next-slot final-alloc }) result-loc
        -- Validity preserved in reclaimed alloc state
        reclaim-preserves-validity :
          ValidAtWF m (record alloc { next-slot = next-slot final-alloc })
                    (eval ir x) result-loc final-state
        -- High-water mark of slot allocation (maximum slot ever written)
        -- With reclamation, next-slot final-alloc may be < max slots actually written
        max-slot-written : ℕ
        -- max-slot-written is at least next-slot final-alloc (was: reclaimable-slot)
        max-slot-geq-final : next-slot final-alloc ≤ max-slot-written
        -- max-slot-written is bounded by input next-slot + ir-stack-requirement
        max-slot-usage-bound : max-slot-written ≤ next-slot alloc +ℕ ir-stack-requirement ir
        -- Stack discipline: execution stays within stack requirement budget
        -- Final stack frontier bounded by requirement (pointers/tags/temps)
        -- Even with arbitrary-sized output (on heap), stack usage (pointers/tags) is bounded
        -- Enables compositional capacity proofs: if f and g stay in bounds, so does f;g
        slot-stays-in-budget : next-slot final-alloc ≤ next-slot alloc +ℕ ir-stack-requirement ir
        -- Frontier slot stability: if input-loc is at frontier initially, it stays there
        -- This is because IR traces either:
        --   1. Don't write to frontier slot (e.g., inl/inr write to suc)
        --   2. Write Input1 to frontier slot (via mov-to-output; store-at-slot)
        --   3. Push a frame, so writes go to child frame (apply)
        -- This property enables pair's backup-slot preservation proof.
        --
        -- Returns a 3-way sum:
        --   inj₁: IR doesn't allocate (final-alloc = input alloc)
        --   inj₂ (inj₁ proof): IR allocates and preserves the slot
        --   inj₂ (inj₂ tt): IR allocates but might not preserve (edge case in compose)
        --
        -- The third case arises in compose when f doesn't allocate but returns a
        -- different location (like fst, snd), and g allocates. In this case, g writes
        -- f's result (not the original input) to the frontier slot.
        frontier-slot-stable : ∀ (s' : LocState FS) (input-loc : ValueLocation FS) →
          halted s' ≡ false →
          readReg (regs s') Input1 ≡ input-loc →
          readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc →
          (next-slot alloc ≡ next-slot final-alloc) ⊎
          ((readLoc (proj₁ (exec-trace trace s' alloc))
                   (AtStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc) ⊎ ⊤)
        -- Trace slot bound: all stack writes are at slots ≥ next-slot alloc.
        -- This enables compositional proofs that traces don't write below their frontier.
        -- Key for pair's g-preserves-backup proof via exec-trace-preserves-disjoint.
        trace-writes-above : TraceWritesAbove (next-slot alloc) trace
        -- Trace slot read bound: all stack reads are from slots ≥ next-slot alloc.
        -- This enables frame-independence proofs: running a trace on a state with
        -- a slot written (below frontier) produces the same result with that slot preserved.
        -- Key for pair's trustMe-pair-stack/heap proofs via exec-trace-slot-independent.
        trace-slot-reads-above : TraceSlotReadsAbove (next-slot alloc) trace
        -- Trace upper bound: all stack writes are at slots < max-slot-written.
        -- Combined with trace-writes-above, this gives: writes are in [next-slot alloc, max-slot-written).
        -- With reclamation, traces may write up to max-slot-written, then reclaim back to reclaimable-slot.
        -- Key for pair's g-fst-slot preservation: g writes in [reclaim-f, max-slot-g), so fst-slot = reclaim-g is safe.
        trace-writes-below : TraceWritesBelow max-slot-written trace
        -- Trace slot read upper bound: all stack reads are from slots < max-slot-written.
        -- Combined with trace-slot-reads-above, this gives: reads are in [next-slot alloc, max-slot-written).
        -- With reclamation, traces may read up to max-slot-written before reclaiming back.
        -- Key for pair's g-fst-indep: g reads in [reclaim-f, max-slot-g), so fst-slot = reclaim-g is independent.
        trace-slot-reads-below : TraceSlotReadsBelow max-slot-written trace
        -- OCP-0003: Scratch bounded relative to OUTPUT frontier (not input)
        -- This is the key insight from stack-model-design.md:
        --   - Output: unbounded, runtime-determined (how much frontier advanced)
        --   - Scratch: bounded, static (temporary space above output)
        -- max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement
        -- Combined with slot-monotone, this enables MAX-based composition
        scratch-bounded : max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement ir
        -- Note: trace-preserves-capacity removed in Phase 3 (frame-capacity removed)
        -- Trace contains no heap-writing instructions.
        -- Heap writes (store-indirect) write to arbitrary memory (wherever Input1 points),
        -- so traces containing them require additional disjointness preconditions.
        -- Our IR traces don't write to heap (they use store-at-slot instead).
        trace-no-heap-writes : TraceNoHeapWrites trace
        -- Trace preserves halted: all instructions in trace preserve halted status.
        -- This enables proving halted preservation through composed traces.
        -- Combined with not-halted precondition, proves intermediate states are not halted.
        -- Key for pair's fst-ptr/snd-ptr proofs which need not-halted at intermediate states.
        trace-preserves-halted : TracePreservesHaltedP trace

    --------------------------------------------------------------------
    -- BodyCorrect: Pre-computed body execution proof
    --
    -- Input1 pair is constructed by Apply as Heap (boxed).
    -- Output mode comes from body's actual output.
    --------------------------------------------------------------------

    {-# NO_POSITIVITY_CHECK #-}
    record BodyCorrect {EnvType A B : Type}
                       (body : IR (EnvType * A) B)
                       (env : ⟦ EnvType ⟧)
                       (env-loc : ValueLocation FS)
                       (bound : ℕ) : Set where
      inductive
      field
        body-capacity : ℕ
        body-cap-eq : body-capacity ≡ ir-stack-requirement body

        -- Execute returns mode-indexed result
        -- Input1 pair is Heap (boxed) - constructed by Apply
        -- Output mode is existentially quantified (body decides)
        -- Note: capacity precondition removed in Phase 3 (frame-capacity removed)
        execute : ∀ (arg : ⟦ A ⟧) (arg-loc pair-loc : ValueLocation FS)
          (s : LocState FS) (alloc : AllocState {FS})
          (mPair : AllocMode) →  -- Input1 pair mode (Apply provides Heap)
          ValidAtWF mPair alloc (pair env arg) pair-loc s →
          BeforeFrontier alloc pair-loc →
          halted s ≡ false →
          readReg (regs s) Input1 ≡ pair-loc →
          ∃[ mOut ] IRResultAWF mOut body (pair env arg) s alloc

  open IRResultAWF public
  open BodyCorrect public

  ------------------------------------------------------------------------
  -- ClosureWellFormed: Closure with pre-computed body execution proof
  --
  -- This extends the basic closure validity with body-correct.
  -- Curry constructs this, Apply uses it.
  ------------------------------------------------------------------------

  record ClosureWellFormed {EnvType A B : Type}
                           (body : IR (EnvType * A) B)
                           (env : ⟦ EnvType ⟧)
                           (body<bound : ir-size body < program-bound)
                           (closure-loc env-loc code-loc : ValueLocation FS)
                           (s : LocState FS)
                           (alloc : AllocState {FS}) : Set where
    field
      -- Memory layout
      env-ptr : readLoc s closure-loc ≡ just env-loc
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just code-loc
      -- Frontier tracking
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      -- Env validity (now using ValidAtWF with mode)
      mEnv : AllocMode
      env-valid : ValidAtWF mEnv alloc env env-loc s
      -- PRE-COMPUTED body execution proof with program-bound
      body-correct : BodyCorrect body env env-loc program-bound

  open ClosureWellFormed public

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF closures
  ------------------------------------------------------------------------

  record ClosureValidWF (alloc : AllocState {FS}) {k : ArrowKind} {A B : Type}
                        (f : ⟦ A ⇒[ k ] B ⟧)
                        (closure-loc : ValueLocation FS)
                        (s : LocState FS) : Set where
    field
      EnvType : Type
      body : IR (EnvType * A) B
      env : ⟦ EnvType ⟧
      body<bound : ir-size body < program-bound
      env-loc : ValueLocation FS
      code-loc : ValueLocation FS
      mEnv : AllocMode  -- Mode of env
      env-ptr : readLoc s closure-loc ≡ just env-loc
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just code-loc
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      env-valid : ValidAtWF mEnv alloc env env-loc s
      -- THE KEY: body-correct is extracted with program-bound!
      body-correct : BodyCorrect body env env-loc program-bound
      f-is-closure : f ≡ (λ arg → eval body (pair env arg))

  -- Closures are always Heap mode. Kind-polymorphic: works for both pure
  -- (⇒[ mk-kind q pure ]) and effectful (Eff) arrows, unwrapping valid-coerce-kind-wf
  -- as needed.
  decomposeClosureWF : ∀ {alloc k A B} {f : ⟦ A ⇒[ k ] B ⟧} {loc s} →
    ValidAtWF Heap alloc {A ⇒[ k ] B} f loc s → ClosureValidWF alloc {k = k} f loc s
  decomposeClosureWF (valid-closure-wf {EnvType} {_} {_} {_} {body} {env} {_}
                       bb {_} {el} {cl} {_} {mE} ep cp eb cb slb ev bc) = record
    { EnvType = EnvType
    ; body = body
    ; env = env
    ; body<bound = bb
    ; env-loc = el
    ; code-loc = cl
    ; mEnv = mE
    ; env-ptr = ep
    ; code-ptr = cp
    ; env-before = eb
    ; code-before = cb
    ; sucLoc-before = slb
    ; env-valid = ev
    ; body-correct = bc
    ; f-is-closure = refl
    }
  decomposeClosureWF (valid-coerce-kind-wf {q = _} cv) with decomposeClosureWF cv
  ... | inner = record
    { EnvType = ClosureValidWF.EnvType inner
    ; body = ClosureValidWF.body inner
    ; env = ClosureValidWF.env inner
    ; body<bound = ClosureValidWF.body<bound inner
    ; env-loc = ClosureValidWF.env-loc inner
    ; code-loc = ClosureValidWF.code-loc inner
    ; mEnv = ClosureValidWF.mEnv inner
    ; env-ptr = ClosureValidWF.env-ptr inner
    ; code-ptr = ClosureValidWF.code-ptr inner
    ; env-before = ClosureValidWF.env-before inner
    ; code-before = ClosureValidWF.code-before inner
    ; sucLoc-before = ClosureValidWF.sucLoc-before inner
    ; env-valid = ClosureValidWF.env-valid inner
    ; body-correct = ClosureValidWF.body-correct inner
    ; f-is-closure = ClosureValidWF.f-is-closure inner
    }

  -- Closures are always Heap mode - extract mode equality from validity proof
  -- Works for both valid-closure-wf (direct) and valid-coerce-kind-wf (eff wrapper).
  closure-mode-is-heap-proof : ∀ {m alloc k A B} {f : ⟦ A ⇒[ k ] B ⟧} {loc s} →
    ValidAtWF m alloc {A ⇒[ k ] B} f loc s → m ≡ Heap
  closure-mode-is-heap-proof (valid-closure-wf _ _ _ _ _ _ _ _) = refl
  closure-mode-is-heap-proof (valid-coerce-kind-wf cv) = closure-mode-is-heap-proof cv

  ------------------------------------------------------------------------
  -- RecDispatcherWF: Recursive dispatcher interface with ValidAtWF
  --
  -- Used by Curry to construct BodyCorrect.
  -- Takes ValidAtWF input and returns IRResultAWF with ValidAtWF output.
  --
  -- SIMPLIFIED: Only needs linear capacity (pair-slots * ir-size).
  -- No global invariants needed - capacity is threaded dynamically per closure.
  ------------------------------------------------------------------------

  -- Note: capacity precondition removed in Phase 3 (frame-capacity removed)
  RecDispatcherWF : ℕ → Set
  RecDispatcherWF bound = ∀ {A B} (mIn : AllocMode) (ir : IR A B) →
    ir-size ir < bound →
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS) (s : LocState FS)
    (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    ∃[ mOut ] IRResultAWF mOut ir x s alloc

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF pairs (any mode)
  --
  -- Reference-based model: two pointers at pair-loc and sucLoc pair-loc
  ------------------------------------------------------------------------

  record PairValidWF (alloc : AllocState {FS}) {A B : Type}
                     (p : ⟦ A * B ⟧)
                     (pair-loc : ValueLocation FS)
                     (s : LocState FS) : Set where
    field
      fst-loc : ValueLocation FS
      snd-loc : ValueLocation FS
      mA : AllocMode  -- Component A mode
      mB : AllocMode  -- Component B mode
      fst-ptr : readLoc s pair-loc ≡ just fst-loc
      snd-ptr : readLoc s (sucLoc pair-loc) ≡ just snd-loc
      fst-before : BeforeFrontier alloc fst-loc
      snd-before : BeforeFrontier alloc snd-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc pair-loc)
      fst-valid : ValidAtWF mA alloc (proj₁ p) fst-loc s
      snd-valid : ValidAtWF mB alloc (proj₂ p) snd-loc s

  decomposePairWF : ∀ {m alloc A B} {p : ⟦ A * B ⟧} {loc s} →
    ValidAtWF m alloc p loc s → PairValidWF alloc p loc s
  decomposePairWF (valid-pair-wf {_} {_} {_} {_} {_} {_} {_} {fl} {sl} {_} {mA} {mB}
                    fp sp fb sb slb fv sv) = record
    { fst-loc = fl
    ; snd-loc = sl
    ; mA = mA
    ; mB = mB
    ; fst-ptr = fp
    ; snd-ptr = sp
    ; fst-before = fb
    ; snd-before = sb
    ; sucLoc-before = slb
    ; fst-valid = fv
    ; snd-valid = sv
    }

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF sum types (inl/inr) - any mode
  --
  -- Reference-based model: tag + payload-ptr (identical for all modes)
  ------------------------------------------------------------------------

  record InlValidWF (alloc : AllocState {FS}) {A B : Type}
                    (v : ⟦ A + B ⟧)
                    (sum-loc : ValueLocation FS)
                    (s : LocState FS) : Set where
    field
      a : ⟦ A ⟧
      mA : AllocMode
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just payload-loc
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAtWF mA alloc a payload-loc s
      v-is-inl : v ≡ sem-inl a

  record InrValidWF (alloc : AllocState {FS}) {A B : Type}
                    (v : ⟦ A + B ⟧)
                    (sum-loc : ValueLocation FS)
                    (s : LocState FS) : Set where
    field
      b : ⟦ B ⟧
      mB : AllocMode
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just payload-loc
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAtWF mB alloc b payload-loc s
      v-is-inr : v ≡ sem-inr b

  decomposeInlWF : ∀ {m alloc A B} {a : ⟦ A ⟧} {loc s} →
    ValidAtWF m alloc {A + B} (sem-inl a) loc s → InlValidWF alloc {A} {B} (sem-inl a) loc s
  decomposeInlWF {A = A} {B = B} (valid-inl-wf {_} {_} {_} {a} {_} {_} {pl} {_} {mA} pp pb slb pv) = record
    { a = a
    ; mA = mA
    ; payload-loc = pl
    ; payload-ptr = pp
    ; payload-before = pb
    ; sucLoc-before = slb
    ; payload-valid = pv
    ; v-is-inl = refl
    }

  decomposeInrWF : ∀ {m alloc A B} {b : ⟦ B ⟧} {loc s} →
    ValidAtWF m alloc {A + B} (sem-inr b) loc s → InrValidWF alloc {A} {B} (sem-inr b) loc s
  decomposeInrWF {A = A} {B = B} (valid-inr-wf {_} {_} {_} {b} {_} {_} {pl} {_} {mB} pp pb slb pv) = record
    { b = b
    ; mB = mB
    ; payload-loc = pl
    ; payload-ptr = pp
    ; payload-before = pb
    ; sucLoc-before = slb
    ; payload-valid = pv
    ; v-is-inr = refl
    }

  ------------------------------------------------------------------------
  -- OCP-0003: FoldValidWF record and decomposeFoldWF removed.
  -- Use μ-type/ν-type validity instead.

  ------------------------------------------------------------------------
  -- Lift ValidAt to ValidAtWF for non-closure types
  --
  -- For Unit and pairs of non-closures, we can convert ValidAt to ValidAtWF.
  -- This is used when we don't have body-correct info but need ValidAtWF.
  ------------------------------------------------------------------------

  valid-to-validWF-unit : ∀ {m alloc loc s} →
    ValidAtWF m alloc {Unit} tt loc s
  valid-to-validWF-unit = valid-unit-wf

  ------------------------------------------------------------------------
  -- ValidAtWF memory-only dependence
  --
  -- ValidAtWF only depends on memory, not registers. When memory is
  -- preserved, validity transfers to a new state.
  ------------------------------------------------------------------------

  -- ValidAtWF only depends on memory, not registers
  -- When memory is preserved (stackMem and heapMem equal), validity transfers
  -- By structural induction on ValidAtWF
  validityWF-mem-only : ∀ {m alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    stackMem s₂ ≡ stackMem s₁ →
    heapMem s₂ ≡ heapMem s₁ →
    ValidAtWF m alloc v loc s₁ → ValidAtWF m alloc v loc s₂

  validityWF-mem-only {m} {alloc} {Unit} tt loc s₁ s₂ stack-eq heap-eq valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-mem-only {m} {alloc} {A * B} (a , b) loc s₁ s₂ stack-eq heap-eq
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      fp' : readLoc s₂ loc ≡ just fl
      fp' = trans (readLoc-stack-heap-eq s₂ s₁ loc stack-eq heap-eq) fp

      sp' : readLoc s₂ (sucLoc loc) ≡ just sl
      sp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) sp

      fv' = validityWF-mem-only a fl s₁ s₂ stack-eq heap-eq fv
      sv' = validityWF-mem-only b sl s₁ s₂ stack-eq heap-eq sv

  validityWF-mem-only {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s₁ s₂ stack-eq heap-eq
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      ep' : readLoc s₂ loc ≡ just el
      ep' = trans (readLoc-stack-heap-eq s₂ s₁ loc stack-eq heap-eq) ep

      cp' : readLoc s₂ (sucLoc loc) ≡ just cl
      cp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) cp

      ev' = validityWF-mem-only env el s₁ s₂ stack-eq heap-eq ev

  -- Kind-coerced closure: recurse on underlying validity, re-coerce.
  validityWF-mem-only {m} {alloc} {A ⇒[ _ ] B} f loc s₁ s₂ stack-eq heap-eq (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-mem-only f loc s₁ s₂ stack-eq heap-eq cv)

  -- Eff (effectful morphism): recurse on underlying closure validity

  -- inl (any mode)
  validityWF-mem-only {m} {alloc} {A + B} .(sem-inl a) loc s₁ s₂ stack-eq heap-eq
    (valid-inl-wf {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl-wf pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just pl
      pp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) pp

      pv' = validityWF-mem-only a pl s₁ s₂ stack-eq heap-eq pv

  -- inr (any mode)
  validityWF-mem-only {m} {alloc} {A + B} .(sem-inr b) loc s₁ s₂ stack-eq heap-eq
    (valid-inr-wf {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr-wf pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just pl
      pp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) pp

      pv' = validityWF-mem-only b pl s₁ s₂ stack-eq heap-eq pv

  -- OCP-0003: μ-type and ν-type validity preservation
  -- Uses proven lemmas from MuValidity
  validityWF-mem-only {m} {alloc} {μ-type F} x loc s₁ s₂ stack-eq heap-eq (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-only alloc wf x loc s₁ s₂ stack-eq heap-eq μv)

  validityWF-mem-only {m} {alloc} {ν-type F} x loc s₁ s₂ stack-eq heap-eq (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-only alloc wf x loc s₁ s₂ stack-eq heap-eq νv)

  -- Primitives: memory-independent (BeforeFrontier doesn't depend on state)
  validityWF-mem-only {m} {alloc} {Int} _ loc s₁ s₂ stack-eq heap-eq (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-mem-only {m} {alloc} {Float} _ loc s₁ s₂ stack-eq heap-eq (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-mem-only {m} {alloc} {Str} _ loc s₁ s₂ stack-eq heap-eq (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-mem-only {m} {alloc} {Buffer} _ loc s₁ s₂ stack-eq heap-eq (valid-buffer-wf bf) =
    valid-buffer-wf bf

  ------------------------------------------------------------------------
  -- ValidAtWF preservation under writes to frontier locations
  --
  -- These are ValidAtWF versions of validity-write-at-frontier and
  -- validity-write-at-suc-frontier from ValidityWriteLemma.agda.
  ------------------------------------------------------------------------

  -- Import helpers for frontier inequality
  -- ValidAtWF is preserved when writing to at-frontier location
  validityWF-write-at-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc v loc s →
    ValidAtWF m alloc v loc (write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val)

  validityWF-write-at-frontier {m} {alloc} {Unit} _ loc s val loc-before valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-write-at-frontier {m} {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      fp' = trans (write-at-frontier-preserves-before s alloc loc val loc-before) fp
      sp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) sp
      fv' = validityWF-write-at-frontier a fl s val fb fv
      sv' = validityWF-write-at-frontier b sl s val sb sv

  validityWF-write-at-frontier {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      ep' = trans (write-at-frontier-preserves-before s alloc loc val loc-before) ep
      cp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) cp
      ev' = validityWF-write-at-frontier env el s val eb ev

  -- Kind-coerced closure
  validityWF-write-at-frontier {m} {alloc} {A ⇒[ _ ] B} f loc s val loc-before (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-write-at-frontier f loc s val loc-before cv)

  -- inl (any mode)
  validityWF-write-at-frontier {m} {alloc} {A + B} .(sem-inl a) loc s val loc-before
    (valid-inl-wf {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl-wf pp' pb slb pv'
    where
      pp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-frontier a pl s val pb pv

  -- inr (any mode)
  validityWF-write-at-frontier {m} {alloc} {A + B} .(sem-inr b) loc s val loc-before
    (valid-inr-wf {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr-wf pp' pb slb pv'
    where
      pp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-frontier b pl s val pb pv

  -- OCP-0003: μ-type and ν-type cases - using μValid-mem-preserved
  -- Writing at frontier preserves memory at all BeforeFrontier locations
  validityWF-write-at-frontier {m} {alloc} {μ-type F} x loc s val loc-before (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-preserved alloc wf x loc s s' loc-before mem-eq μv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-frontier-preserves-before s alloc loc' val bf

  validityWF-write-at-frontier {m} {alloc} {ν-type F} x loc s val loc-before (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-preserved alloc wf x loc s s' loc-before mem-eq νv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-frontier-preserves-before s alloc loc' val bf

  -- Primitives: BeforeFrontier unchanged
  validityWF-write-at-frontier {m} {alloc} {Int} _ loc s val loc-before (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-write-at-frontier {m} {alloc} {Float} _ loc s val loc-before (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-write-at-frontier {m} {alloc} {Str} _ loc s val loc-before (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-write-at-frontier {m} {alloc} {Buffer} _ loc s val loc-before (valid-buffer-wf bf) =
    valid-buffer-wf bf

  -- ValidAtWF is preserved when writing to suc-frontier location
  validityWF-write-at-suc-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc v loc s →
    ValidAtWF m alloc v loc (write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val)

  validityWF-write-at-suc-frontier {m} {alloc} {Unit} _ loc s val loc-before valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-write-at-suc-frontier {m} {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      fp' = trans (write-at-suc-frontier-preserves-before s alloc loc val loc-before) fp
      sp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) sp
      fv' = validityWF-write-at-suc-frontier a fl s val fb fv
      sv' = validityWF-write-at-suc-frontier b sl s val sb sv

  validityWF-write-at-suc-frontier {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      ep' = trans (write-at-suc-frontier-preserves-before s alloc loc val loc-before) ep
      cp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) cp
      ev' = validityWF-write-at-suc-frontier env el s val eb ev

  -- Kind-coerced closure
  validityWF-write-at-suc-frontier {m} {alloc} {A ⇒[ _ ] B} f loc s val loc-before (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-write-at-suc-frontier f loc s val loc-before cv)

  -- inl (any mode)
  validityWF-write-at-suc-frontier {m} {alloc} {A + B} .(sem-inl a) loc s val loc-before
    (valid-inl-wf {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl-wf pp' pb slb pv'
    where
      pp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-suc-frontier a pl s val pb pv

  -- inr (any mode)
  validityWF-write-at-suc-frontier {m} {alloc} {A + B} .(sem-inr b) loc s val loc-before
    (valid-inr-wf {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr-wf pp' pb slb pv'
    where
      pp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-suc-frontier b pl s val pb pv

  -- OCP-0003: μ-type and ν-type cases - using μValid-mem-preserved
  -- Writing at suc-frontier preserves memory at all BeforeFrontier locations
  validityWF-write-at-suc-frontier {m} {alloc} {μ-type F} x loc s val loc-before (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-preserved alloc wf x loc s s' loc-before mem-eq μv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-suc-frontier-preserves-before s alloc loc' val bf

  validityWF-write-at-suc-frontier {m} {alloc} {ν-type F} x loc s val loc-before (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-preserved alloc wf x loc s s' loc-before mem-eq νv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-suc-frontier-preserves-before s alloc loc' val bf

  -- Primitives: BeforeFrontier unchanged
  validityWF-write-at-suc-frontier {m} {alloc} {Int} _ loc s val loc-before (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-write-at-suc-frontier {m} {alloc} {Float} _ loc s val loc-before (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-write-at-suc-frontier {m} {alloc} {Str} _ loc s val loc-before (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-write-at-suc-frontier {m} {alloc} {Buffer} _ loc s val loc-before (valid-buffer-wf bf) =
    valid-buffer-wf bf

  ------------------------------------------------------------------------
  -- Validity transport across allocation advancement
  --
  -- When the frontier advances (next-slot increases), ValidAtWF can be
  -- transported to the new alloc. This is needed when writing to fresh
  -- slots and then proving existing values are still valid.
  --
  -- Key insight: BeforeFrontier locations stay before the new frontier,
  -- so all constraints in ValidAtWF constructors are preserved.
  ------------------------------------------------------------------------

  validityWF-alloc-advance : ∀ {m alloc A} (v : ⟦ A ⟧) loc s (n : ℕ) →
    ValidAtWF m alloc v loc s →
    let alloc' = record alloc { next-slot = next-slot alloc +ℕ n }
    in ValidAtWF m alloc' v loc s

  validityWF-alloc-advance {m} {alloc} {Unit} tt loc s n valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-alloc-advance {m} {alloc} {A * B} (a , b) loc s n
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp sp fb' sb' slb' fv' sv'
    where
      fb' = stack-alloc-advances alloc n fl fb
      sb' = stack-alloc-advances alloc n sl sb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      fv' = validityWF-alloc-advance a fl s n fv
      sv' = validityWF-alloc-advance b sl s n sv

  validityWF-alloc-advance {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s n
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep cp eb' cb' slb' ev' bc
    where
      eb' = stack-alloc-advances alloc n el eb
      cb' = stack-alloc-advances alloc n cl cb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      ev' = validityWF-alloc-advance env el s n ev

  -- Kind-coerced closure
  validityWF-alloc-advance {m} {alloc} {A ⇒[ _ ] B} f loc s n (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-alloc-advance f loc s n cv)

  -- inl (any mode)
  validityWF-alloc-advance {m} {alloc} {A + B} .(sem-inl a) loc s n
    (valid-inl-wf {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl-wf pp pb' slb' pv'
    where
      pb' = stack-alloc-advances alloc n pl pb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      pv' = validityWF-alloc-advance a pl s n pv

  -- inr (any mode)
  validityWF-alloc-advance {m} {alloc} {A + B} .(sem-inr b) loc s n
    (valid-inr-wf {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr-wf pp pb' slb' pv'
    where
      pb' = stack-alloc-advances alloc n pl pb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      pv' = validityWF-alloc-advance b pl s n pv

  -- OCP-0003: μ-type and ν-type cases - using μValid-frontier-advance
  validityWF-alloc-advance {m} {alloc} {μ-type F} x loc s n (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-frontier-advance alloc alloc' wf x loc s refl slot-≤ ≤-refl μv)
    where
      open import Data.Nat.Properties using (≤-refl; m≤m+n)
      alloc' = record alloc { next-slot = next-slot alloc +ℕ n }
      slot-≤ : next-slot alloc ≤ next-slot alloc'
      slot-≤ = m≤m+n (next-slot alloc) n

  validityWF-alloc-advance {m} {alloc} {ν-type F} x loc s n (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-frontier-advance alloc alloc' wf x loc s refl slot-≤ ≤-refl νv)
    where
      open import Data.Nat.Properties using (≤-refl; m≤m+n)
      alloc' = record alloc { next-slot = next-slot alloc +ℕ n }
      slot-≤ : next-slot alloc ≤ next-slot alloc'
      slot-≤ = m≤m+n (next-slot alloc) n

  -- Primitives: advance BeforeFrontier
  validityWF-alloc-advance {m} {alloc} {Int} _ loc s n (valid-int-wf bf) =
    valid-int-wf (stack-alloc-advances alloc n loc bf)
  validityWF-alloc-advance {m} {alloc} {Float} _ loc s n (valid-float-wf bf) =
    valid-float-wf (stack-alloc-advances alloc n loc bf)
  validityWF-alloc-advance {m} {alloc} {Str} _ loc s n (valid-str-wf bf) =
    valid-str-wf (stack-alloc-advances alloc n loc bf)
  validityWF-alloc-advance {m} {alloc} {Buffer} _ loc s n (valid-buffer-wf bf) =
    valid-buffer-wf (stack-alloc-advances alloc n loc bf)

  ------------------------------------------------------------------------
  -- Validity transport across arbitrary frontier advancement
  --
  -- More general than validityWF-alloc-advance: works for any alloc'
  -- related by frontier-monotone properties (frame-preserved, slot/heap
  -- monotone). Used when transporting validity through IR execution.
  ------------------------------------------------------------------------

  validityWF-frontier-advance : ∀ {m alloc alloc' A} (v : ⟦ A ⟧) loc (s : LocState FS) →
    current-frame alloc' ≡ current-frame alloc →
    next-slot alloc ≤ next-slot alloc' →
    next-heap-ref alloc ≤ next-heap-ref alloc' →
    ValidAtWF m alloc v loc s →
    ValidAtWF m alloc' v loc s

  validityWF-frontier-advance {m} {alloc} {alloc'} {Unit} tt loc s cf-eq slot-≤ heap-≤ valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-frontier-advance {m} {alloc} {alloc'} {A * B} (a , b) loc s cf-eq slot-≤ heap-≤
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp sp fb' sb' slb' fv' sv'
    where
      fb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ fl fb
      sb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ sl sb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      fv' = validityWF-frontier-advance a fl s cf-eq slot-≤ heap-≤ fv
      sv' = validityWF-frontier-advance b sl s cf-eq slot-≤ heap-≤ sv

  validityWF-frontier-advance {.Heap} {alloc} {alloc'} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s cf-eq slot-≤ heap-≤
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep cp eb' cb' slb' ev' bc
    where
      eb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ el eb
      cb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ cl cb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      ev' = validityWF-frontier-advance env el s cf-eq slot-≤ heap-≤ ev

  -- Kind-coerced closure
  validityWF-frontier-advance {m} {alloc} {alloc'} {A ⇒[ _ ] B} f loc s cf-eq slot-≤ heap-≤ (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-frontier-advance f loc s cf-eq slot-≤ heap-≤ cv)

  -- inl (any mode)
  validityWF-frontier-advance {m} {alloc} {alloc'} {A + B} .(sem-inl a) loc s cf-eq slot-≤ heap-≤
    (valid-inl-wf {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl-wf pp pb' slb' pv'
    where
      pb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ pl pb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      pv' = validityWF-frontier-advance a pl s cf-eq slot-≤ heap-≤ pv

  -- inr (any mode)
  validityWF-frontier-advance {m} {alloc} {alloc'} {A + B} .(sem-inr b) loc s cf-eq slot-≤ heap-≤
    (valid-inr-wf {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr-wf pp pb' slb' pv'
    where
      pb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ pl pb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      pv' = validityWF-frontier-advance b pl s cf-eq slot-≤ heap-≤ pv

  -- OCP-0003: μ-type and ν-type cases - using proven lemmas from MuValidity
  validityWF-frontier-advance {m} {alloc} {alloc'} {μ-type F} x loc s cf-eq slot-≤ heap-≤ (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-frontier-advance alloc alloc' wf x loc s cf-eq slot-≤ heap-≤ μv)

  validityWF-frontier-advance {m} {alloc} {alloc'} {ν-type F} x loc s cf-eq slot-≤ heap-≤ (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-frontier-advance alloc alloc' wf x loc s cf-eq slot-≤ heap-≤ νv)

  -- Primitives: advance BeforeFrontier
  validityWF-frontier-advance {m} {alloc} {alloc'} {Int} _ loc s cf-eq slot-≤ heap-≤ (valid-int-wf bf) =
    valid-int-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)
  validityWF-frontier-advance {m} {alloc} {alloc'} {Float} _ loc s cf-eq slot-≤ heap-≤ (valid-float-wf bf) =
    valid-float-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)
  validityWF-frontier-advance {m} {alloc} {alloc'} {Str} _ loc s cf-eq slot-≤ heap-≤ (valid-str-wf bf) =
    valid-str-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)
  validityWF-frontier-advance {m} {alloc} {alloc'} {Buffer} _ loc s cf-eq slot-≤ heap-≤ (valid-buffer-wf bf) =
    valid-buffer-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)

  ------------------------------------------------------------------------
  -- ValidAtWF transfer between allocation states with BeforeFrontier transfer
  --
  -- Transfer ValidAtWF m a₁ → ValidAtWF m a₂ using a general bf-transfer
  -- function. This is more general than validityWF-frontier-advance.
  --
  -- The proof applies bf-transfer to all sublocation BeforeFrontier proofs
  -- and recursively transfers nested validity.
  ------------------------------------------------------------------------

  validityWF-with-bf-transfer : ∀ {m A} (v : ⟦ A ⟧) loc (s : LocState FS)
    (a₁ a₂ : AllocState {FS})
    (bf-transfer : ∀ loc' → BeforeFrontier a₁ loc' → BeforeFrontier a₂ loc') →
    ValidAtWF m a₁ v loc s →
    ValidAtWF m a₂ v loc s

  validityWF-with-bf-transfer {m} {Unit} tt loc s a₁ a₂ bf valid-unit-wf = valid-unit-wf

  -- Pair (any mode)
  validityWF-with-bf-transfer {m} {A * B} (a , b) loc s a₁ a₂ bf
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp sp (bf fl fb) (bf sl sb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer a fl s a₁ a₂ bf fv)
      (validityWF-with-bf-transfer b sl s a₁ a₂ bf sv)

  -- Closure
  validityWF-with-bf-transfer {.Heap} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s a₁ a₂ bf
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep cp (bf el eb) (bf cl cb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer env el s a₁ a₂ bf ev) bc

  -- Kind-coerced closure
  validityWF-with-bf-transfer {m} {A ⇒[ _ ] B} f loc s a₁ a₂ bf (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-with-bf-transfer f loc s a₁ a₂ bf cv)

  -- inl (any mode)
  validityWF-with-bf-transfer {m} {A + B} .(sem-inl a) loc s a₁ a₂ bf
    (valid-inl-wf {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl-wf pp (bf pl pb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer a pl s a₁ a₂ bf pv)

  -- inr (any mode)
  validityWF-with-bf-transfer {m} {A + B} .(sem-inr b) loc s a₁ a₂ bf
    (valid-inr-wf {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr-wf pp (bf pl pb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer b pl s a₁ a₂ bf pv)

  -- OCP-0003: μ-type and ν-type cases - using proven lemmas from MuValidity
  validityWF-with-bf-transfer {m} {μ-type F} x loc s a₁ a₂ bf (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-bf-transfer a₁ a₂ wf x loc s bf μv)

  validityWF-with-bf-transfer {m} {ν-type F} x loc s a₁ a₂ bf (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-bf-transfer a₁ a₂ wf x loc s bf νv)

  -- Primitives: transfer BeforeFrontier
  validityWF-with-bf-transfer {m} {Int} _ loc s a₁ a₂ bf (valid-int-wf bfr) =
    valid-int-wf (bf loc bfr)
  validityWF-with-bf-transfer {m} {Float} _ loc s a₁ a₂ bf (valid-float-wf bfr) =
    valid-float-wf (bf loc bfr)
  validityWF-with-bf-transfer {m} {Str} _ loc s a₁ a₂ bf (valid-str-wf bfr) =
    valid-str-wf (bf loc bfr)
  validityWF-with-bf-transfer {m} {Buffer} _ loc s a₁ a₂ bf (valid-buffer-wf bfr) =
    valid-buffer-wf (bf loc bfr)

  ------------------------------------------------------------------------
  -- Validity preservation when memory at BeforeFrontier is preserved
  --
  -- Key lemma for IR execution: if memory at all BeforeFrontier locations
  -- is preserved (same readLoc values), then ValidAtWF is preserved.
  -- This is more precise than validityWF-mem-only (full memory equality).
  --
  -- The proof works because ValidAtWF at a BeforeFrontier location means
  -- all reachable sub-locations are also BeforeFrontier (structural).
  ------------------------------------------------------------------------

  validityWF-mem-preserved : ∀ {m alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    BeforeFrontier alloc loc →
    (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
    ValidAtWF m alloc v loc s₁ →
    ValidAtWF m alloc v loc s₂

  validityWF-mem-preserved {m} {alloc} {Unit} tt loc s₁ s₂ loc-before mem-eq valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-mem-preserved {m} {alloc} {A * B} (a , b) loc s₁ s₂ loc-before mem-eq
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      fp' = trans (mem-eq loc loc-before) fp
      sp' = trans (mem-eq (sucLoc loc) slb) sp
      fv' = validityWF-mem-preserved a fl s₁ s₂ fb mem-eq fv
      sv' = validityWF-mem-preserved b sl s₁ s₂ sb mem-eq sv

  validityWF-mem-preserved {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s₁ s₂ loc-before mem-eq
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      ep' = trans (mem-eq loc loc-before) ep
      cp' = trans (mem-eq (sucLoc loc) slb) cp
      ev' = validityWF-mem-preserved env el s₁ s₂ eb mem-eq ev

  -- Kind-coerced closure
  validityWF-mem-preserved {m} {alloc} {A ⇒[ _ ] B} f loc s₁ s₂ loc-before mem-eq (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-mem-preserved f loc s₁ s₂ loc-before mem-eq cv)

  -- inl (any mode)
  validityWF-mem-preserved {m} {alloc} {A + B} .(sem-inl a) loc s₁ s₂ loc-before mem-eq
    (valid-inl-wf {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl-wf pp' pb slb pv'
    where
      pp' = trans (mem-eq (sucLoc loc) slb) pp
      pv' = validityWF-mem-preserved a pl s₁ s₂ pb mem-eq pv

  -- inr (any mode)
  validityWF-mem-preserved {m} {alloc} {A + B} .(sem-inr b) loc s₁ s₂ loc-before mem-eq
    (valid-inr-wf {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr-wf pp' pb slb pv'
    where
      pp' = trans (mem-eq (sucLoc loc) slb) pp
      pv' = validityWF-mem-preserved b pl s₁ s₂ pb mem-eq pv

  -- OCP-0003: μ-type and ν-type cases - using proven lemmas from MuValidity
  validityWF-mem-preserved {m} {alloc} {μ-type F} x loc s₁ s₂ loc-before mem-eq (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-preserved alloc wf x loc s₁ s₂ loc-before mem-eq μv)

  validityWF-mem-preserved {m} {alloc} {ν-type F} x loc s₁ s₂ loc-before mem-eq (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-preserved alloc wf x loc s₁ s₂ loc-before mem-eq νv)

  -- Primitives: BeforeFrontier unchanged
  validityWF-mem-preserved {m} {alloc} {Int} _ loc s₁ s₂ loc-before mem-eq (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-mem-preserved {m} {alloc} {Float} _ loc s₁ s₂ loc-before mem-eq (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-mem-preserved {m} {alloc} {Str} _ loc s₁ s₂ loc-before mem-eq (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-mem-preserved {m} {alloc} {Buffer} _ loc s₁ s₂ loc-before mem-eq (valid-buffer-wf bf) =
    valid-buffer-wf bf

  ------------------------------------------------------------------------
  -- Validity preservation with excluded slot
  --
  -- Variant of validityWF-mem-preserved for when memory differs at one
  -- specific slot (the "gap slot"). This is used by pair's validity proof
  -- where backup-slot is modified but no sub-location uses it.
  --
  -- The key insight is that IR results have sub-locations that are either:
  --   1. Input1 locations at slots < start-frontier (inherited from input)
  --   2. Fresh allocations at slots ≥ suc start-frontier (allocated by IR)
  -- So slot = start-frontier is a "gap" never used by sub-locations.
  --
  -- Parameters:
  --   gap-slot : the slot to exclude from memory preservation
  --   gap-unused : proof that no sub-location is at the gap slot
  --   mem-eq : memory preserved for all OTHER BeforeFrontier locations
  ------------------------------------------------------------------------

  -- Helper: extract slot from AtStack location (for documentation, may be used later)
  private
    slot-of-loc : ValueLocation FS → ℕ
    slot-of-loc (AtStack _ k) = k
    slot-of-loc (AtDynamic _) = 0  -- dummy, heap locations don't use slot comparison
    slot-of-loc Erased        = 0  -- dummy, Unit has no slot

  ------------------------------------------------------------------------
  -- Validity preservation with gap slot
  --
  -- Key insight for pair validity: when IR f executes starting at
  -- next-slot = suc backup-slot, its result has sub-locations at:
  --   - Input1 locations: slots < backup-slot (inherited from input)
  --   - Fresh allocations: slots ≥ suc backup-slot (allocated by f)
  -- Therefore NO sub-location is at exactly backup-slot.
  --
  -- This means we can transfer validity even when memory differs at
  -- the gap slot, as long as memory agrees on all other BeforeFrontier
  -- locations.
  ------------------------------------------------------------------------

  -- Validity transfers when memory differs only at gap slot.
  -- The gap slot is NOT accessed because of disjoint slot ranges:
  --   - Input1 data is at slots < gap-slot
  --   - Fresh allocations are at slots ≥ suc gap-slot
  --   - gap-slot falls between these ranges
  validityWF-mem-preserved-excluding :
    ∀ {m A} (alloc : AllocState {FS}) (v : ⟦ A ⟧) (loc : ValueLocation FS)
      (gap-frame : Frame) (gap-slot : ℕ)
      (s₁ s₂ : LocState FS) →
    -- Location is before frontier
    BeforeFrontier alloc loc →
    -- Memory agrees on all BeforeFrontier locations except the gap
    (∀ (loc' : ValueLocation FS) →
       BeforeFrontier alloc loc' →
       loc' ≢ AtStack gap-frame gap-slot →
       readLoc s₁ loc' ≡ readLoc s₂ loc') →
    -- Validity transfers
    ValidAtWF m alloc v loc s₁ →
    ValidAtWF m alloc v loc s₂
  validityWF-mem-preserved-excluding = SMP.!!

  ------------------------------------------------------------------------
  -- Validity preservation with positive region bounds
  --
  -- Positive characterization: instead of excluding a gap slot, we specify
  -- the two disjoint regions where sub-locations can exist:
  --   1. Input1 region: [0, input-bound) - inherited from input value
  --   2. Fresh region: [fresh-start, frontier) - newly allocated by IR
  --
  -- The gap [input-bound, fresh-start) contains no sub-locations, so we
  -- don't need memory agreement there.
  --
  -- This is semantically equivalent to validityWF-mem-preserved-excluding
  -- but uses positive bounds rather than negative (≢) reasoning.
  ------------------------------------------------------------------------

  validityWF-mem-preserved-in-regions :
    ∀ {m A} (alloc : AllocState {FS}) (v : ⟦ A ⟧) (loc : ValueLocation FS)
      (input-bound fresh-start : ℕ)
      (s₁ s₂ : LocState FS) →
    -- Location is before frontier
    BeforeFrontier alloc loc →
    -- Regions are properly ordered: input-bound ≤ fresh-start ≤ frontier
    input-bound ≤ fresh-start →
    fresh-start ≤ next-slot alloc →
    -- Memory agrees on input region [0, input-bound) on current frame
    (∀ slot → slot < input-bound →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    -- Memory agrees on fresh region [fresh-start, frontier) on current frame
    (∀ slot → fresh-start ≤ slot → slot < next-slot alloc →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    -- Memory agrees on heap locations (sub-locations may be on heap)
    (∀ h → readLoc s₂ (AtDynamic h) ≡ readLoc s₁ (AtDynamic h)) →
    -- Memory agrees on ancestor frames (sub-locations may be there)
    (∀ f k → current-frame alloc ≺ f →
      readLoc s₂ (AtStack f k) ≡ readLoc s₁ (AtStack f k)) →
    -- Validity transfers
    ValidAtWF m alloc v loc s₁ →
    ValidAtWF m alloc v loc s₂
  validityWF-mem-preserved-in-regions = SMP.!!

  ------------------------------------------------------------------------
  -- Stack Reclamation
  --
  -- After an IR completes, only the result needs to persist. Intermediate
  -- allocations can be reclaimed by creating a new allocation state with
  -- next-slot = reclaimable-slot.
  --
  -- Key property: BeforeFrontier is preserved since reclaimable-slot ≥ next-slot
  -- (from reclaim-monotone).
  ------------------------------------------------------------------------

  -- Create reclaimed allocation state
  reclaim-alloc : (alloc : AllocState {FS}) (reclaim-slot : ℕ) →
    AllocState {FS}
  reclaim-alloc alloc rs = record alloc { next-slot = rs }

  -- BeforeFrontier is preserved after reclamation (frontier only advances)
  reclaim-preserves-frontier : ∀ (alloc : AllocState {FS}) reclaim-slot
    (monotone : next-slot alloc ≤ reclaim-slot)
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    BeforeFrontier (reclaim-alloc alloc reclaim-slot) loc
  reclaim-preserves-frontier alloc rs monotone loc bf =
    stack-alloc-advances' alloc rs monotone loc bf
    where
      -- Helper using existing stack-alloc-advances pattern
      stack-alloc-advances' : ∀ (alloc : AllocState {FS}) (rs : ℕ)
        (monotone : next-slot alloc ≤ rs)
        (loc : ValueLocation FS) →
        BeforeFrontier alloc loc →
        BeforeFrontier (record alloc { next-slot = rs }) loc
      stack-alloc-advances' alloc rs monotone (AtStack f k) (stack-before refl k<next) =
        stack-before refl (<-≤-trans k<next monotone)
        where open import Data.Nat.Properties using (<-≤-trans)
      stack-alloc-advances' alloc rs monotone (AtStack f k) (stack-ancestor cf≺f src) =
        stack-ancestor cf≺f src  -- Frame ordering and provenance unchanged (same current-frame)
      stack-alloc-advances' alloc rs monotone (AtDynamic hl) (heap-before r<next) =
        heap-before r<next
      stack-alloc-advances' alloc rs monotone Erased erased-before = erased-before

  -- ValidAtWF is preserved after reclamation
  validityWF-reclaim : ∀ {m alloc A} (v : ⟦ A ⟧) loc s reclaim-slot
    (monotone : next-slot alloc ≤ reclaim-slot)
    (loc-before : BeforeFrontier alloc loc) →
    ValidAtWF m alloc v loc s →
    ValidAtWF m (reclaim-alloc alloc reclaim-slot) v loc s
  validityWF-reclaim {m} {alloc} v loc s rs mono loc-bf valid =
    validityWF-frontier-advance v loc s refl mono ≤-refl valid
    where
      open import Data.Nat.Properties using (≤-refl)

  ------------------------------------------------------------------------
  -- Trace-Based Validity Preservation
  --
  -- KEY LEMMA: If a trace writes only at slots ≥ n (TraceWritesAbove n),
  -- and all sub-locations of a valid value are at slots < n (captured by
  -- BeforeFrontier with appropriate next-slot), then validity is preserved.
  --
  -- This is the core insight for PairWF and similar proofs:
  --   - IR results have sub-locations at slots < reclaimable-slot
  --   - Subsequent traces write at slots ≥ reclaimable-slot
  --   - Therefore validity is preserved through those traces
  --
  -- The proof combines:
  --   1. derive-mem-preserved: memory at BeforeFrontier locations preserved
  --   2. validityWF-mem-preserved: validity transfers when memory preserved
  ------------------------------------------------------------------------

  -- Phase 2 Core: Derive memory preservation from trace write bounds
  --
  -- This is the UNIFIED derivation function that routes to the appropriate
  -- positive characterization lemma based on BeforeFrontier constructor:
  --   - stack-before: exec-trace-preserves-slot-below (slot < frontier)
  --   - stack-ancestor: exec-trace-preserves-ancestor (ancestor frame)
  --   - heap-before: exec-trace-preserves-heap-loc (heap location)
  --
  -- Usage: Instead of storing mem-preserved-before in IRResultAWF,
  -- callers can derive it using this function from trace-writes-above
  -- and trace-no-heap-writes.

  -- General variant: derive preservation for slots below an explicit boundary
  -- Useful for composition where the boundary may differ from next-slot alloc
  derive-mem-preserved-at : ∀ (alloc : AllocState {FS}) (start : ℕ)
    (trace : AbstractTrace) (s : LocState FS) →
    TraceWritesAbove start trace →
    TraceNoHeapWrites trace →
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    start ≥ next-slot alloc →  -- start is at or above frontier
    readLoc (proj₁ (exec-trace trace s alloc)) loc ≡ readLoc s loc
  derive-mem-preserved-at alloc start trace s twa tnhw (AtStack f k) (stack-before f≡cf k<next) start≥frontier =
    -- k < next-slot alloc ≤ start, so k < start and slot k is below write region
    subst (λ f' → readLoc (proj₁ (exec-trace trace s alloc)) (AtStack f' k) ≡
                  readLoc s (AtStack f' k))
          (sym f≡cf)
          (exec-trace-preserves-slot-below trace s alloc start k twa tnhw k<start)
    where
      open import Data.Nat.Properties using (<-≤-trans)
      k<start = <-≤-trans k<next start≥frontier
  derive-mem-preserved-at alloc start trace s twa tnhw (AtStack f k) (stack-ancestor cf≺f _) _ =
    -- f is an ancestor frame (current-frame alloc ≺ f)
    exec-trace-preserves-ancestor trace s alloc f k cf≺f tnhw
  derive-mem-preserved-at alloc start trace s twa tnhw (AtDynamic h) (heap-before _) _ =
    -- Heap location
    exec-trace-preserves-heap-loc trace s alloc h tnhw
  derive-mem-preserved-at alloc start trace s twa tnhw Erased erased-before _ = refl

  -- Standard variant: derive preservation for slots below next-slot alloc
  derive-mem-preserved : ∀ (alloc : AllocState {FS})
    (trace : AbstractTrace) (s : LocState FS) →
    TraceWritesAbove (next-slot alloc) trace →
    TraceNoHeapWrites trace →
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    readLoc (proj₁ (exec-trace trace s alloc)) loc ≡ readLoc s loc
  derive-mem-preserved alloc trace s twa tnhw loc bf =
    derive-mem-preserved-at alloc (next-slot alloc) trace s twa tnhw loc bf ≤-refl
    where open import Data.Nat.Properties using (≤-refl)

  -- Main lemma: trace preserves validity when writing above frontier
  -- Now uses derive-mem-preserved instead of inline proof
  validityWF-trace-preserves : ∀ {m A} (alloc : AllocState {FS})
    (trace : AbstractTrace) (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) →
    -- Validity at start
    BeforeFrontier alloc loc →
    ValidAtWF m alloc v loc s →
    -- Trace only writes at slots ≥ next-slot alloc
    TraceWritesAbove (next-slot alloc) trace →
    TraceNoHeapWrites trace →
    -- Validity preserved after trace
    ValidAtWF m alloc v loc (proj₁ (exec-trace trace s alloc))
  validityWF-trace-preserves alloc trace v loc s loc-bf valid twa tnhw =
    validityWF-mem-preserved v loc s (proj₁ (exec-trace trace s alloc)) loc-bf
      (derive-mem-preserved alloc trace s twa tnhw) valid

  ------------------------------------------------------------------------
  -- Phase 4: Derive mem-preserved from IRResultAWF
  --
  -- This function replaces the stored mem-preserved-before field.
  -- It derives preservation from trace-writes-above and trace-no-heap-writes,
  -- using trace-correct to translate from exec-trace to final-state.
  ------------------------------------------------------------------------

  irresult-mem-preserved : ∀ {m A B} {ir : IR A B} {x : ⟦ A ⟧}
    {s : LocState FS} {alloc : AllocState {FS}}
    (result : IRResultAWF m ir x s alloc) →
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    readLoc (IRResultAWF.final-state result) loc ≡ readLoc s loc
  irresult-mem-preserved {s = s} {alloc = alloc} result loc bf =
    subst (λ fs → readLoc fs loc ≡ readLoc s loc)
      (IRResultAWF.trace-correct result)
      (derive-mem-preserved alloc (IRResultAWF.trace result) s
        (IRResultAWF.trace-writes-above result)
        (IRResultAWF.trace-no-heap-writes result)
        loc bf)
    where open import Relation.Binary.PropositionalEquality using (subst)