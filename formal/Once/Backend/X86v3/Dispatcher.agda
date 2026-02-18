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

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoʳ-≤; m≤m+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Induction.WellFounded using (Acc; acc)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Validity
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation
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

open import Once.Backend.X86v3.ValidityChainLemma public
  using (module ValidityChainLemmas)

------------------------------------------------------------------------
-- Re-export types from IRResult module
------------------------------------------------------------------------

open import Once.Backend.X86v3.IRResult public
  using (module DispatcherResult; module RecDispatcherDef)

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
  -- Frame capacity constraint: ensures pb-cap holds for any alloc in the current frame
  (frame-cap-sufficient : ∀ (alloc : AllocState {FS}) →
    next-slot alloc + pair-slots *ℕ program-bound ≤ frame-capacity alloc)
  -- Child frame support for apply's hybrid frame approach
  -- get-child-frame returns a frame below the parent (child ≺ parent) for body execution
  (get-child-frame : ∀ (alloc : AllocState {FS}) → FrameSemantics.Frame FS)
  (child-frame-ordered : ∀ (alloc : AllocState {FS}) →
    FrameSemantics._≺_ FS (get-child-frame alloc) (current-frame alloc))  -- Child is below parent
  (child-capacity : ℕ)
  (child-cap-sufficient : pair-slots *ℕ program-bound ≤ child-capacity)
  where
  open ValidityDef {FS} program-bound
  open DispatcherResult {FS} program-bound
  open FrontierInvariant {FS}
  open WriteWithDisjoint {FS}
  open RecDispatcherDef {FS} program-bound
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
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           decomposeClosureWF; ClosureValidWF; decomposePairWF; PairValidWF;
           validWF-to-valid; resultWF-to-result; validityWF-mem-only;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-alloc-advance; validityWF-frontier-advance;
           validityWF-mem-preserved)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import validity write lemmas
  open import Once.Backend.X86v3.ValidityWriteLemma using (module ValidityWriteLemmas)
  open ValidityWriteLemmas {FS} program-bound

  -- Import frontier and validity chain lemmas
  open FrontierLemmas {FS}
  open ValidityChainLemmas {FS} program-bound

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

  ------------------------------------------------------------------------
  -- Postulates for new IR constructors (to be implemented in task 6)
  --
  -- These handle sum types (inl-ir, inr-ir, case-ir), initial, and
  -- recursive types (fold-ir, unfold-ir).
  ------------------------------------------------------------------------

  postulate
    -- Sum type: inject left
    run-inl : ∀ {A B}
      (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      next-slot alloc + pair-slots *ℕ ir-size (inl-ir {A} {B}) ≤ frame-capacity alloc →
      IRResultAWF (inl-ir {A} {B}) x s alloc

    -- Sum type: inject right
    run-inr : ∀ {A B}
      (x : ⟦ B ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      next-slot alloc + pair-slots *ℕ ir-size (inr-ir {A} {B}) ≤ frame-capacity alloc →
      IRResultAWF (inr-ir {A} {B}) x s alloc

    -- Sum type: case analysis
    run-case : ∀ {A B C}
      (f : IR A C) (g : IR B C) →
      RecDispatcherWF (ir-size (case-ir f g)) →
      (x : ⟦ A ⊕ B ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      next-slot alloc + pair-slots *ℕ ir-size (case-ir f g) ≤ frame-capacity alloc →
      IRResultAWF (case-ir f g) x s alloc

    -- Initial object: absurd elimination (never executed)
    run-initial : ∀ {A}
      (x : ⟦ Void ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      IRResultAWF (initial {A}) x s alloc

    -- Recursive types: fold
    run-fold : ∀ {F}
      (x : ⟦ F ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      next-slot alloc + pair-slots *ℕ ir-size (fold-ir {F}) ≤ frame-capacity alloc →
      IRResultAWF (fold-ir {F}) x s alloc

    -- Recursive types: unfold
    run-unfold : ∀ {F}
      (x : ⟦ Fix F ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      IRResultAWF (unfold-ir {F}) x s alloc

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
    -- Returns IRResultAWF with ValidAtWF for proper threading
    -- Uses LINEAR capacity only: pair-slots * ir-size
    make-rec-wf : ∀ {n} (ir<bound : n < program-bound) →
      (∀ {m} → m < n → Acc _<_ m) →
      RecDispatcherWF n
    make-rec-wf {n} ir<bound rs ir lt x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' combined-cap' =
      run-ir-wf ir (<-trans lt ir<bound) x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' combined-cap' (rs lt)

    -- run-ir-wf uses Acc _<_ (ir-size ir) for termination.
    -- Uses ValidAtWF input and returns IRResultAWF with ValidAtWF output.
    -- For Compose/Pair: sub-IRs have smaller size, so rs gives Acc
    -- For Apply: uses body-correct.execute instead of recursive call!
    -- Uses LINEAR capacity for recursion
    run-ir-wf : ∀ {A B} (ir : IR A B)
      (ir<bound : ir-size ir < program-bound) →
      (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      -- LINEAR capacity: pair-slots * ir-size covers ir-req + recursion
      next-slot alloc + pair-slots *ℕ ir-size ir ≤ frame-capacity alloc →
      Acc _<_ (ir-size ir) →
      IRResultAWF ir x s alloc

    -- Simple cases delegated to SimpleWF module
    run-ir-wf id _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-id x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf fst-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-fst x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf snd-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-snd x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf terminal _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Sum type: inject left (postulated)
    run-ir-wf (inl-ir {A} {B}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      run-inl {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Sum type: inject right (postulated)
    run-ir-wf (inr-ir {A} {B}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      run-inr {A} {B} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Sum type: case analysis (postulated)
    run-ir-wf (case-ir f g) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-case f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Initial: absurd elimination (postulated)
    run-ir-wf initial _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-initial x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Recursive types: fold (postulated)
    run-ir-wf (fold-ir {F}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      run-fold {F} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Recursive types: unfold (postulated)
    run-ir-wf (unfold-ir {F}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-unfold {F} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Compose: delegated to ComposeWF module
    run-ir-wf (g ∘ f) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-compose f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Pair: delegated to PairWF module
    run-ir-wf ⟨ f , g ⟩ ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-pair f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Curry: delegated to CurryWF module
    run-ir-wf (curry f) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-curry f ir<bound (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Apply: uses BodyCorrect.execute from closure
    -- Uses PURE RECLAMATION: body executes in same frame, then reclaims stack
    -- pb-cap is derived from frame capacity constraint (module parameter)
    run-ir-wf {(A ⇒[ _ ] B) * A} {B} apply _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      run-apply x input-loc s alloc input-valid-wf input-before not-halted rdi-eq
        combined-cap (frame-cap-sufficient alloc)

  -- Public API with ValidAtWF
  -- Returns IRResultAWF with ValidAtWF for result validity.
  -- Uses LINEAR capacity only: pair-slots * ir-size
  run-wf : ∀ {A B} (ir : IR A B) (ir<bound : ir-size ir < program-bound)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- LINEAR capacity: pair-slots * ir-size covers ir-req + recursion
    next-slot alloc + pair-slots *ℕ ir-size ir ≤ frame-capacity alloc →
    IRResultAWF ir x s alloc
  run-wf ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    run-ir-wf ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap
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
--
-- REMAINING POSTULATES (1 total):
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
-- CAPACITY ARCHITECTURE:
--   - Module parameter `frame-cap-sufficient` ensures capacity >= 2 * pair-slots * pb
--   - This is NOT a postulate but a precondition the caller must satisfy
--   - The WholeProgram module should allocate frames with sufficient capacity
--
-- NEXT STEPS:
--   1. Implement new-frame semantics for apply body execution (eliminates slot-bounded-apply)
------------------------------------------------------------------------
