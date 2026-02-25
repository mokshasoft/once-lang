------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.Dispatcher
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

module Once.CCC.Target.X86v3.Dispatcher where

open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoʳ-≤; m≤m+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Induction.WellFounded using (Acc; acc)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Allocation hiding (AllocMode)
open import Once.CCC.Target.X86v3.ClosureWellFormed

-- Import ValidAtWF types for termination-safe dispatch
open import Once.CCC.Target.X86v3.ClosureWellFormed
  using (module ClosureWellFormedDef)

------------------------------------------------------------------------
-- Import lemma modules
------------------------------------------------------------------------

open import Once.CCC.Target.X86v3.DispatcherArithmeticLemma public
  using (suc<+2)

open import Once.CCC.Target.X86v3.FrontierLemma public
  using (module FrontierLemmas)

open import Once.CCC.Target.X86v3.SizeBoundLemma public
  using (∘-f-bound; ∘-g-bound; ⟨,⟩-f-bound; ⟨,⟩-g-bound; curry-body-bound)

------------------------------------------------------------------------
-- Import helper modules
------------------------------------------------------------------------

import Once.CCC.Target.X86v3.IR.SimpleWF as SimpleWFModule
import Once.CCC.Target.X86v3.IR.ComposeWF as ComposeWFModule
import Once.CCC.Target.X86v3.IR.PairWF as PairWFModule
import Once.CCC.Target.X86v3.IR.CurryWF as CurryWFModule
import Once.CCC.Target.X86v3.IR.ApplyWF as ApplyWFModule

-- Import write operations from separate module
open import Once.CCC.Target.X86v3.WriteOps public using (module WriteWithDisjoint)

------------------------------------------------------------------------
-- Prim Proof Interface
--
-- PrimProofV3: what a proof for a primitive must provide
-- PrimProofProviderV3: interface for domain compilers
--
-- With opaque Prim (just a name), the provider gives:
--   - Contract c: stack requirements and output mode
--   - Proof: that execution produces correct result
--
-- The semantics comes from PrimSem (module parameter).
------------------------------------------------------------------------

module PrimProofInterface {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS} using (BeforeFrontier)
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF)

  -- What a proof for a primitive must provide
  -- NOTE: For opaque Prim, eval primSem (Prim name) x = evalPrim primSem name x
  -- The proof shows that execution of Prim produces eval primSem (Prim name) x
  PrimProofV3 : ∀ {A B : Type}
    (c : PrimContractV3 A B)
    (ir : IR A B) →  -- The actual Prim IR
    Set
  PrimProofV3 {A} {B} c ir =
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      next-slot alloc +ℕ stack-requirement c ≤ frame-capacity alloc →
      IRResultAWF (output-mode c) ir x s alloc

  -- Interface for domain compilers
  -- For each primitive name, provide:
  --   - A contract (stack requirements, output mode)
  --   - A proof that execution is correct
  PrimProofProviderV3 : Set
  PrimProofProviderV3 =
    ∀ {A B : Type} (name : String) →
    ∃[ c ] PrimProofV3 {A} {B} c (Prim name)

------------------------------------------------------------------------
-- Closure IR Tracking
--
-- Since valid-closure tracks the body IR, we get it from decomposition.
--
-- KEY INSIGHT: ApplySetupResult now contains:
--   - body : IR (EnvType * A) B
--   - env : ⟦ EnvType ⟧
--   - closure-is-body : fst input ≡ (λ arg → eval primSem body (pair env arg))
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
------------------------------------------------------------------------

module Dispatcher {FS : FrameSemantics} (program-bound : ℕ) (acc-pb : Acc _<_ program-bound)
  -- PrimSem provides semantics for all primitives (required for eval)
  (primSem : PrimSem)
  -- NOTE: frame-cap-sufficient and body-cap-bounded REMOVED
  -- Migration to X86-style dynamic capacity threading eliminates program-bound-based derivation.
  -- Capacity is now threaded per-closure via BodyCorrect.body-capacity.
  -- Child frame support for apply's hybrid frame approach
  -- get-child-frame returns a frame below the parent (child ≺ parent) for body execution
  (get-child-frame : ∀ (alloc : AllocState {FS}) → FrameSemantics.Frame FS)
  (child-frame-ordered : ∀ (alloc : AllocState {FS}) →
    FrameSemantics._≺_ FS (get-child-frame alloc) (current-frame alloc))  -- Child is below parent
  -- Immediate adjacency: no frame exists between child and parent
  (child-frame-adjacent : ∀ (alloc : AllocState {FS}) (f : FrameSemantics.Frame FS) →
    FrameSemantics._≺_ FS (get-child-frame alloc) f →
    FrameSemantics._≺_ FS f (current-frame alloc) →
    ⊥)
  (child-capacity : ℕ)
  (child-cap-sufficient : pair-slots *ℕ program-bound ≤ child-capacity)
  -- Escape analysis guarantees (provided by escape analysis pass)
  -- Body results survive child frame pop (the MINIMAL escape interface)
  (escape-result-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
    (result-loc : ValueLocation FS) →
    current-frame body-final ≡ get-child-frame alloc →
    ApplyWFModule.BeforeFrontier' body-final result-loc →
    ApplyWFModule.SurvivesFramePop (get-child-frame alloc) result-loc)
  (parent-bound-eq : ∀ (alloc : AllocState {FS}) (bound : ℕ) →
    bound ≡ next-slot alloc Data.Nat.+ pair-slots)
  -- Prim proof provider (from domain compilers)
  (prim-proof : PrimProofInterface.PrimProofProviderV3 {FS} program-bound primSem)
  where
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
  open ClosureWellFormedDef {FS} program-bound primSem
    using (BodyCorrect; ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           decomposeClosureWF; ClosureValidWF; decomposePairWF; PairValidWF;
           closure-mode-is-heap-proof;
           validityWF-mem-only;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-alloc-advance; validityWF-frontier-advance;
           validityWF-mem-preserved)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import frontier lemmas
  open FrontierLemmas {FS}

  -- Import simple IR implementations (id, fst, snd, terminal)
  open SimpleWFModule.SimpleWFImpl {FS} program-bound primSem

  -- Import compose IR implementation
  open ComposeWFModule.ComposeWFImpl {FS} program-bound primSem

  -- Import pair IR implementation
  open PairWFModule.PairWFImpl {FS} program-bound primSem

  -- Import curry IR implementation
  open CurryWFModule.CurryWFImpl {FS} program-bound primSem

  -- Import apply IR implementation (pass child-frame and escape analysis parameters)
  open ApplyWFModule.ApplyWFImpl {FS} program-bound primSem
    get-child-frame child-frame-ordered child-frame-adjacent child-capacity child-cap-sufficient
    escape-result-survives parent-bound-eq

  -- Import sum/fix IR implementations (inl, inr, case, initial, fold, unfold)
  open import Once.CCC.Target.X86v3.IR.SumFixWF as SumFixWFModule
  open SumFixWFModule.SumFixWFImpl {FS} program-bound primSem

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
  -- Prim handler: uses PrimProofProviderV3 from module parameter
  --
  -- With opaque Prim (just a name), we:
  --   1. Get (contract, proof) from prim-proof
  --   2. Use proof to execute
  ------------------------------------------------------------------------
  run-prim : ∀ {A B} (mIn : AllocMode) (name : String)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- NOTE: Capacity check needs contract from proof provider
    -- We check against pair-slots as upper bound (contract.stack-requirement ≤ 2)
    next-slot alloc +ℕ pair-slots ≤ frame-capacity alloc →
    ∃[ c ] IRResultAWF (output-mode c) (Prim {A} {B} name) x s alloc
  run-prim {A} {B} mIn name x input-loc s alloc valid bf nh rdi cap =
    let (c , proof) = prim-proof {A} {B} name
        -- Contract guarantees stack-requirement c ≤ pair-slots
        cap' = ≤-trans (+-monoʳ-≤ (next-slot alloc) (stack-req-bounded c)) cap
    in c , proof mIn x input-loc s alloc valid bf nh rdi cap'

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

    run-ir-wf Stack fst-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      -- Reference-based model: Stack and Heap use same pointer representation
      run-fst x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Heap snd-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-snd x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack snd-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      -- Reference-based model: Stack and Heap use same pointer representation
      run-snd x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf mIn terminal _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      mIn , run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Arr: effectful morphism coercion (delegated to SimpleWF module)
    -- Converts (A ⇒[ q ] B) to (Eff A B) - semantically identity
    run-ir-wf mIn (arr {A} {B} {q}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      mIn , run-arr {mIn} {A} {B} {q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Prim: primitive operations (uses proof provider)
    -- With opaque Prim (just name), contract comes from proof provider
    run-ir-wf mIn (Prim name) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      let (c , result) = run-prim mIn name x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap
      in output-mode c , result

    -- Sum type: inject left (delegated to SumFixWF module)
    -- Output mode is m (from inl-ir m)
    run-ir-wf mIn (inl-ir {A} {B} m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      m , run-inl {A} {B} mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Sum type: inject right (delegated to SumFixWF module)
    -- Output mode is m (from inr-ir m)
    run-ir-wf mIn (inr-ir {A} {B} m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      m , run-inr {A} {B} mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Sum type: case analysis (delegated to SumFixWF module)
    -- Reference-based model: any mode works since sums use pointer representation
    run-ir-wf Heap (case-ir f g) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-case {Heap} f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    run-ir-wf Stack (case-ir f g) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      -- Reference-based model: Stack and Heap use same pointer representation for sums
      run-case {Stack} f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Initial: absurd elimination (delegated to SumFixWF module)
    run-ir-wf mIn initial _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-initial x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Recursive types: fold (delegated to SumFixWF module)
    -- Output mode is m (from fold-ir m): Stack = unboxed, Heap = pointer
    run-ir-wf mIn (fold-ir {F} m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
      m , run-fold {F} mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Recursive types: unfold (delegated to SumFixWF module)
    -- Reference-based model: any mode works since folds use pointer representation
    run-ir-wf Heap (unfold-ir {F}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      run-unfold {Heap} {F} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack (unfold-ir {F}) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap acc-ir =
      -- Reference-based model: Stack and Heap use same pointer representation for folds
      run-unfold {Stack} {F} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Compose: delegated to ComposeWF module
    run-ir-wf mIn (g ∘ f) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      run-compose mIn f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Pair: delegated to PairWF module
    -- Output mode is m (from ⟨ f , g ⟩ m)
    run-ir-wf mIn (⟨ f , g ⟩ m) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      m , run-pair mIn f g m (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Curry: delegated to CurryWF module (quantity-polymorphic)
    -- Output is always Heap (closure is boxed)
    run-ir-wf mIn (curry {q = q} f m) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap (acc rs) =
      Heap , run-curry {q = q} mIn f m ir<bound (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Apply: uses BodyCorrect.execute from closure (quantity-polymorphic)
    -- Input must be Heap (boxed pair of closure * arg)
    -- Uses PURE RECLAMATION: body executes in same frame, then reclaims stack
    --
    -- DYNAMIC CAPACITY THREADING (X86-style):
    -- Capacity proof uses closure-body-capacity which extracts body-capacity
    -- from the closure's BodyCorrect. No program-bound-based derivation needed.
    -- Apply: CHILD FRAME EXECUTION
    -- Body executes in child frame with child-capacity (from module params).
    -- Body capacity proven via child-cap-sufficient - NO POSTULATES NEEDED!
    run-ir-wf Heap (apply {A} {B} {q}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap _ =
        run-apply {q = q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    run-ir-wf Stack (apply {A} {B} {q}) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap acc-ir =
      -- Reference-based model: Stack and Heap use same pointer representation for pairs
      run-apply {q = q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap

    -- Free-heap: explicit heap deallocation (delegated to SimpleWF module)
    -- Semantically a no-op (returns input unchanged).
    run-ir-wf mIn (free-heap ref) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      mIn , run-free-heap ref x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

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

  -- NOTE: Use `run-wf` with ValidAtWF inputs. The basic ValidAt API was removed.
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
--   - WholeProgram module allocates frames with sufficient capacity
--
-- NEXT STEPS:
--   1. Implement new-frame semantics for apply body execution (eliminates slot-bounded-apply)
------------------------------------------------------------------------
