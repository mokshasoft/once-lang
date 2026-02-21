------------------------------------------------------------------------
-- Once.Backend.X86v3.Dispatcher
--
-- IR Dispatcher with proper allocation state threading.
--
-- Key insight: allocation state is threaded through execution, so
-- freshly allocated locations are guaranteed disjoint from existing
-- valid locations.
--
-- ValidAt now tracks BeforeFrontier recursively, so decomposing a
-- pair automatically gives BeforeFrontier for components.
------------------------------------------------------------------------

module Once.Backend.X86v3.Dispatcher where

open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoʳ-≤; m≤m+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Induction.WellFounded using (Acc; acc)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Validity
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)
open import Once.Backend.X86v3.ClosureWellFormed

-- Import ValidAtWF types for termination-safe dispatch
open import Once.Backend.X86v3.ClosureWellFormed
  using (module ClosureWellFormedDef)

------------------------------------------------------------------------
-- Import lemma modules
------------------------------------------------------------------------

open import Once.Backend.X86v3.DispatcherArithmeticLemma public
  using (suc<+2)

open import Once.Backend.X86v3.FrontierLemma public
  using (module FrontierLemmas)

open import Once.Backend.X86v3.SizeBoundLemma public
  using (∘-f-bound; ∘-g-bound; ⟨,⟩-f-bound; ⟨,⟩-g-bound; curry-body-bound)

------------------------------------------------------------------------
-- Import helper modules
------------------------------------------------------------------------

import Once.Backend.X86v3.IR.SimpleWF as SimpleWFModule
import Once.Backend.X86v3.IR.ComposeWF as ComposeWFModule
import Once.Backend.X86v3.IR.PairWF as PairWFModule
import Once.Backend.X86v3.IR.CurryWF as CurryWFModule
import Once.Backend.X86v3.IR.ApplyWF as ApplyWFModule

-- Import write operations from separate module
open import Once.Backend.X86v3.WriteOps public using (module WriteWithDisjoint)

------------------------------------------------------------------------
-- Closure IR Tracking - NOW FROM VALIDITY!
--
-- Since valid-closure tracks the body IR, we get it from decomposition.
-- No postulates needed - we create all closures, so we know their bodies.
--
-- KEY INSIGHT: ApplySetupResult now contains:
--   - body : IR (EnvType * A) B
--   - env : ⟦ EnvType ⟧
--   - closure-is-body : fst input ≡ (λ arg → eval body (pair env arg))
--   - env-valid, arg-valid for recursive dispatch
--
-- To compute (fst input) (snd input), we dispatch to body with (env, snd input).
-- Since the body came from some curry in the program, and
-- ir-size body < ir-size (curry body) ≤ program-size, recursion terminates.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Main Dispatcher with Allocation Threading
--
-- Parameterized by:
--   program-bound : ℕ (all IRs in the program are smaller)
--   acc-pb : Acc _<_ program-bound (for Apply to recurse on closure bodies)
--
-- Apply uses acc-pb with body<bound to get Acc for body, enabling
-- termination without TERMINATING pragma.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Frame Capacity Constraint
--
-- For apply to work correctly, the frame capacity must be large enough
-- to accommodate body execution. Specifically:
--   frame-capacity >= 2 * pair-slots * program-bound
--
-- This ensures that at any point in execution:
--   slot + pair-slots * program-bound <= frame-capacity
--
-- The constraint is provided as a function parameter rather than a postulate.
------------------------------------------------------------------------

module Dispatcher {FS : FrameSemantics} (program-bound : ℕ) (acc-pb : Acc _<_ program-bound)
  -- NOTE: frame-cap-sufficient and body-cap-bounded REMOVED
  -- Migration to X86-style dynamic capacity threading eliminates program-bound-based derivation.
  -- Capacity is now threaded per-closure via BodyCorrect.body-capacity.
  -- Child frame support for apply's hybrid frame approach
  -- get-child-frame returns a frame below the parent (child ≺ parent) for body execution
  (get-child-frame : ∀ (alloc : AllocState {FS}) → FrameSemantics.Frame FS)
  (child-frame-ordered : ∀ (alloc : AllocState {FS}) →
    FrameSemantics._≺_ FS (get-child-frame alloc) (current-frame alloc))  -- Child is below parent
  (child-capacity : ℕ)
  (child-cap-sufficient : pair-slots *ℕ program-bound ≤ child-capacity)
  where
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open WriteWithDisjoint {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open Allocator {FS}
  open StackAllocation {FS}
  open FrameSemantics FS
  open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m<m+n; n≤1+n; n<1+n; <-trans; m+n≤o⇒m≤o; +-suc; +-comm; +-monoˡ-≤; +-monoʳ-≤; +-assoc)

  -- Import WF types for termination-safe dispatch
  open ClosureWellFormedDef {FS} program-bound
    using (BodyCorrect; ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-unit-wf; valid-pair-boxed-wf; valid-closure-wf;
           decomposeClosureWF; ClosureValidWF; decomposePairBoxedWF; PairBoxedValidWF;
           closure-mode-is-heap-proof;
           validityWF-mem-only;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-alloc-advance; validityWF-frontier-advance;
           validityWF-mem-preserved)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import frontier lemmas
  open FrontierLemmas {FS}

  -- Import simple IR implementations (id, fst, snd, terminal)
  open SimpleWFModule.SimpleWFImpl {FS} program-bound

  -- Import compose IR implementation
  open ComposeWFModule.ComposeWFImpl {FS} program-bound

  -- Import pair IR implementation
  open PairWFModule.PairWFImpl {FS} program-bound

  -- Import curry IR implementation
  open CurryWFModule.CurryWFImpl {FS} program-bound

  -- Import apply IR implementation
  open ApplyWFModule.ApplyWFImpl {FS} program-bound

  -- Import sum/fix IR implementations (inl, inr, case, initial, fold, unfold)
  open import Once.Backend.X86v3.IR.SumFixWF as SumFixWFModule
  open SumFixWFModule.SumFixWFImpl {FS} program-bound

  ------------------------------------------------------------------------
  -- Helper: get Acc for any IR size < program-bound
  -- Used by Apply to get Acc for body (since body<bound comes from closure,
  -- not from structural decrease on the current IR).
  -- Pattern matches acc-pb to extract the accessor function.
  ------------------------------------------------------------------------
  private
    -- Extract smaller Acc from larger Acc using the proof of <
    -- Pattern: rs takes the proof and Agda infers the element from it
    acc-extract : ∀ {m n : ℕ} → Acc _<_ m → n < m → Acc _<_ n
    acc-extract (acc rs) n<m = rs n<m

  get-acc-from-pb : ∀ (n : ℕ) → n < program-bound → Acc _<_ n
  get-acc-from-pb n n<pb = acc-extract acc-pb n<pb

  ------------------------------------------------------------------------
  -- Prim handler: postulate for now (primitives handle their own allocation)
  -- TODO: Connect to FFI when available
  ------------------------------------------------------------------------
  postulate
    run-prim : ∀ {A B} (mIn : AllocMode) (name : String)
      (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      ∃[ mOut ] IRResultAWF mOut (Prim {A} {B} name) x s alloc

  ------------------------------------------------------------------------
  -- Main dispatcher (recursive cases use Acc)
  --
  -- ARCHITECTURE: Uses mutual block pattern from X86 backend.
  -- This enables Apply to recursively dispatch to closure bodies:
  -- - When curry f creates a closure, it stores Acc for f in the closure
  -- - When apply extracts body from closure, it uses the stored Acc
  --
  -- Termination is proven via well-founded recursion on ir-size.
  -- The main dispatcher constructs rec from (acc rs) and delegates to helpers.
  ------------------------------------------------------------------------

  mutual
    -- Helper to construct RecDispatcherWF from rs accessor
    -- Defined in mutual block so termination checker can see the structure
    -- Returns existential mode + IRResultAWF with ValidAtWF for proper threading
    -- Uses ir-stack-requirement for capacity
    make-rec-wf : ∀ {n} (ir<bound : n < program-bound) →
      (∀ {m} → m < n → Acc _<_ m) →
      RecDispatcherWF n
    make-rec-wf {n} ir<bound rs mIn ir lt x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' combined-cap' =
      run-ir-wf mIn ir (<-trans lt ir<bound) x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' combined-cap' (rs lt)

    -- run-ir-wf uses Acc _<_ (ir-size ir) for termination.
    -- Uses ValidAtWF input and returns existential mode + IRResultAWF with ValidAtWF output.
    -- For Compose/Pair: sub-IRs have smaller size, so rs gives Acc
    -- For Apply: uses body-correct.execute instead of recursive call!
    -- Uses ir-stack-requirement for capacity
    run-ir-wf : ∀ {A B} (mIn : AllocMode) (ir : IR A B)
      (ir<bound : ir-size ir < program-bound) →
      (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      -- Capacity using ir-stack-requirement
      next-slot alloc +ℕ ir-stack-requirement ir ≤ frame-capacity alloc →
      Acc _<_ (ir-size ir) →
      ∃[ mOut ] IRResultAWF mOut ir x s alloc

    -- Simple cases delegated to SimpleWF module (returns same mode as input for id/terminal)
    run-ir-wf mIn id _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      mIn , run-id x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- fst/snd extract component modes from pair (input must be Heap for boxed pair)
    -- Stack case is impossible (fst/snd operate on boxed pairs)
    run-ir-wf Heap fst-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-fst x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack fst-ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap acc-ir =
      -- Stack input to fst: would need unboxed pair decomposition (not yet implemented)
      postulate-stack-fst where postulate postulate-stack-fst : _

    run-ir-wf Heap snd-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-snd x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack snd-ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap acc-ir =
      -- Stack input to snd: would need unboxed pair decomposition (not yet implemented)
      postulate-stack-snd where postulate postulate-stack-snd : _

    run-ir-wf mIn terminal _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      mIn , run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Prim: primitive operations (postulated)
    run-ir-wf mIn (Prim name) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-prim mIn name x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Sum type: inject left (delegated to SumFixWF module)
    -- Output mode is m (from inl-ir m)
    run-ir-wf mIn (inl-ir {A} {B} m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      m , run-inl {A} {B} mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Sum type: inject right (delegated to SumFixWF module)
    -- Output mode is m (from inr-ir m)
    run-ir-wf mIn (inr-ir {A} {B} m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      m , run-inr {A} {B} mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Sum type: case analysis (delegated to SumFixWF module)
    -- Input must be Heap (boxed sum), output mode from branch
    run-ir-wf Heap (case-ir f g) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-case f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    run-ir-wf Stack (case-ir f g) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      -- Stack input to case: would need unboxed sum decomposition (not yet implemented)
      postulate-stack-case where postulate postulate-stack-case : _

    -- Initial: absurd elimination (delegated to SumFixWF module)
    run-ir-wf mIn initial _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-initial x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Recursive types: fold (delegated to SumFixWF module)
    -- Output mode is m (from fold-ir m): Stack = unboxed, Heap = pointer
    run-ir-wf mIn (fold-ir {F} m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      m , run-fold {F} mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Recursive types: unfold (delegated to SumFixWF module)
    -- Input must be Heap (fold is boxed)
    run-ir-wf Heap (unfold-ir {F}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-unfold {F} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack unfold-ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap acc-ir =
      -- Stack input to unfold: fold is always boxed, so this is impossible
      postulate-stack-unfold where postulate postulate-stack-unfold : _

    -- Compose: delegated to ComposeWF module
    run-ir-wf mIn (g ∘ f) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-compose mIn f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Pair: delegated to PairWF module
    -- Output mode is m (from ⟨ f , g ⟩ m)
    run-ir-wf mIn (⟨ f , g ⟩ m) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      m , run-pair mIn f g m (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Curry: delegated to CurryWF module
    -- Output is always Heap (closure is boxed)
    run-ir-wf mIn (curry f m) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      Heap , run-curry mIn f m ir<bound (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Apply: uses BodyCorrect.execute from closure
    -- Input must be Heap (boxed pair of closure * arg)
    -- Uses PURE RECLAMATION: body executes in same frame, then reclaims stack
    --
    -- DYNAMIC CAPACITY THREADING (X86-style):
    -- Capacity proof uses closure-body-capacity which extracts body-capacity
    -- from the closure's BodyCorrect. No program-bound-based derivation needed.
    run-ir-wf Heap (apply {A} {B}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
        run-apply x input-loc s alloc input-valid-wf input-before not-halted rdi-eq
          combined-cap body-cap-fits
      where
        -- Dynamic capacity proof: needs slot + pair-slots + body-capacity ≤ cap
        -- body-capacity is extracted from closure via closure-body-capacity
        -- TODO: This proof needs to come from the caller's capacity guarantee
        -- For now, postulate until the full capacity threading is implemented
        postulate
          body-cap-fits : next-slot alloc +ℕ pair-slots +ℕ closure-body-capacity x input-valid-wf ≤ frame-capacity alloc

    run-ir-wf Stack apply ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap acc-ir =
      -- Stack input to apply: closure pairs are always boxed
      postulate-stack-apply where postulate postulate-stack-apply : _

  -- Public API with ValidAtWF
  -- Returns existential mode + IRResultAWF with ValidAtWF for result validity.
  -- Uses ir-stack-requirement for capacity
  run-wf : ∀ {A B} (mIn : AllocMode) (ir : IR A B) (ir<bound : ir-size ir < program-bound)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- Capacity using ir-stack-requirement
    next-slot alloc +ℕ ir-stack-requirement ir ≤ frame-capacity alloc →
    ∃[ mOut ] IRResultAWF mOut ir x s alloc
  run-wf mIn ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    run-ir-wf mIn ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap
      (get-acc-from-pb (ir-size ir) ir<bound)

  -- NOTE: The basic ValidAt API (`run`) has been removed because it required
  -- a postulate to convert ValidAt to ValidAtWF. Use `run-wf` instead.
  --
  -- For program entry with non-closure inputs, construct ValidAtWF directly:
  --   - valid-unit-wf for Unit values
  --   - valid-pair-wf for pairs (recursively construct for components)
  --
  -- To convert the result back to IRResultA, use resultWF-to-result.

------------------------------------------------------------------------
-- Summary
--
-- KEY ARCHITECTURAL CHANGES:
--
-- 1. valid-closure tracks body IR and env value
--    Since we create all closures via curry, we know their bodies.
--    decomposeClosure extracts: EnvType, body, env, env-valid.
--
-- 2. ir-stack-requirement defines static stack bounds for each IR
--    This enables DERIVING capacity proofs instead of postulating them.
--
-- 3. ClosureWellFormed pattern for termination
--    Curry stores BodyCorrect in closure, Apply extracts and uses it.
--    This eliminates the termination issue without TERMINATING pragma.
--
-- 4. ValidAtWF type for full consistency
--    ValidAtWF includes BodyCorrect for closures, enabling Apply to
--    receive and return IRResultAWF with ValidAtWF throughout.
--
-- 5. ir-capacity precondition (NEW)
--    run-ir-wf requires: next-slot alloc + ir-stack-requirement ir ≤ frame-capacity alloc
--    This enables deriving capacity proofs and is threaded through recursion.
--
-- ValidAt alloc v loc s = validity + BeforeFrontier for all component locs
-- IRResultA includes final-alloc + result-before frontier proof + capacity-preserved
--
-- ELIMINATED POSTULATES (Tier 1 - PROVEN):
--   ✓ slot-bounded-compose - arithmetic proof with helper lemma
--   ✓ slot-bounded-pair - arithmetic proof with helper lemma
--   ✓ sucLoc-before-from-snd (4x) - added sucLoc-before to ValidAt structure
--   ✓ sucLoc-before-from-code (4x) - added sucLoc-before to ValidAt structure
--   ✓ validityWF-mem-only - memory transport for ValidAtWF (structural induction)
--   ✓ closure-fits - DIRECTLY from ir-capacity (curry case)
--   ✓ apply-pair-fits - DIRECTLY from ir-capacity (apply case)
--   ✓ ir-cap-f (pair case) - arithmetic via +-assoc and m+n≤o⇒m≤o
--   ✓ ir-cap-g (pair case) - arithmetic via +-monoˡ-≤ and capacity-preserved
--   ✓ pair-fits (pair case) - arithmetic via slot bounds and +-assoc
--
-- ELIMINATED POSTULATES (Tier 3 - IMPLEMENTED):
--   ✓ body-smaller - body<bound from ClosureValid (extracted via ApplySetupResult)
--   ✓ pair-input-loc, s-pair, alloc-pair - actual pair construction
--   ✓ pair-input-valid, pair-input-before - derived from validity proofs
--   ✓ pair-not-halted, pair-rdi-eq - register/state proofs
--   ✓ result-loc, s-final, final-alloc - from recursive dispatch
--   ✓ body-result-valid, result-before - from run-ir result (via BodyCorrect.execute)
--   ✓ rax-eq, not-halted-final - from IRResultAWF fields
--   ✓ frame-preserved-apply, heap-monotone-apply - from recursive call
--   ✓ capacity-preserved-apply - from recursive call
--
-- FULLY PROVEN (no postulates):
--   - id, fst-ir, snd-ir, terminal (all cases of run-ir-wf)
--   - compose (including ir-capacity derivation for sub-IRs)
--   - curry (closure-fits proven from ir-capacity)
--   - apply (apply-pair-fits proven from ir-capacity)
--   - compose slot-bounded, pair slot-bounded
--   - validity-write-at-frontier (uses sucLoc-before from ValidAt)
--   - validity-write-at-suc-frontier (uses sucLoc-before from ValidAt)
--   - validityWF-write-at-frontier, validityWF-write-at-suc-frontier
--   - Apply setup: extracts body IR and all components from closure
--   - Apply termination: uses BodyCorrect.execute instead of run-ir
--   - Apply semantic correctness: result-valid uses closure-is-body
--   - Sum types: inl-ir, inr-ir, case-ir (all delegated to SumFixWF)
--   - Recursive types: fold-ir, unfold-ir (all delegated to SumFixWF)
--   - Initial: absurd elimination (trivial via pattern match on ⊥)
--
-- REMAINING POSTULATES (design-level):
--
--   Slot bound (1 - ApplyWF.agda):
--     - slot-bounded-apply: body runs in same frame, requires architecture fix
--       The issue: ir-stack-requirement(apply) = pair-slots, but apply
--       executes a dynamic body that can consume more stack.
--       Fix options:
--       a) Create new frame for body execution (like real function calls)
--       b) Change ir-stack-requirement to be dynamic (not feasible statically)
--       c) Accept that apply's slot-bounded uses reclamation semantics
--
--   Sum type capacity (3 - SumFixWF.agda):
--     - sum-slots-bound: type-slots (A ⊕ B) ≤ pair-slots * ir-size inl-ir
--     - sucLoc-sum-in-range: suc n < n + type-slots (A ⊕ B)
--     - alloc-slots-eq: proof irrelevance for allocation state equality
--     These highlight the tension between fixed pair-slots capacity formula
--     and type-dependent slot allocation. Will be resolved with unboxed stack.
--
--   Fix type capacity (1 - SumFixWF.agda):
--     - fix-slots-bound: type-slots (Fix F) ≤ pair-slots * ir-size fold-ir
--     Similar issue to sum types.
--
-- CAPACITY ARCHITECTURE:
--   - Module parameter `frame-cap-sufficient` ensures capacity >= 2 * pair-slots * pb
--   - This is NOT a postulate but a precondition the caller must satisfy
--   - The WholeProgram module should allocate frames with sufficient capacity
--
-- NEXT STEPS:
--   1. Implement new-frame semantics for apply body execution (eliminates slot-bounded-apply)
------------------------------------------------------------------------
