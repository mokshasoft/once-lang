-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine
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

module Once.CCC.Machine.Dispatcher where

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
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.IR
open import Once.Functor.Translate using (WellFormedF)
open import Once.CCC.Eval using (eval)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

-- Import ValidAtWF types for termination-safe dispatch
open import Once.CCC.Machine.ClosureWellFormed
  using (module ClosureWellFormedDef)

------------------------------------------------------------------------
-- Import lemma modules
------------------------------------------------------------------------

open import Once.CCC.Machine.DispatcherArithmeticLemma public
  using (suc<+2)

open import Once.CCC.Machine.FrontierLemma public
  using (module FrontierLemmas)

open import Once.CCC.Machine.SizeBoundLemma public
  using (∘-f-bound; ∘-g-bound; ⟨,⟩-f-bound; ⟨,⟩-g-bound; curry-body-bound)

------------------------------------------------------------------------
-- Import helper modules
------------------------------------------------------------------------

import Once.CCC.Machine.IR.SimpleWF as SimpleWFModule
import Once.CCC.Machine.IR.ComposeWF as ComposeWFModule
import Once.CCC.Machine.IR.PairStackWF as PairWFModule
import Once.CCC.Machine.IR.PairAllocWF as PairAllocWFModule
import Once.CCC.Machine.IR.CurryStackWF as CurryStackWFModule
import Once.CCC.Machine.IR.CurryAllocWF as CurryAllocWFModule
import Once.CCC.Machine.IR.SumInlAllocWF as SumInlAllocWFModule
import Once.CCC.Machine.IR.SumInrAllocWF as SumInrAllocWFModule
import Once.CCC.Machine.IR.ApplyWF as ApplyWFModule
import Once.CCC.Machine.IR.RecCoreWF as RecCoreWFModule
import Once.CCC.Machine.IR.ParaWF as ParaWFModule
import Once.CCC.Machine.IR.AnaWF as AnaWFModule

-- Import write operations from separate module
open import Once.CCC.Machine.WriteOps public using (module WriteWithDisjoint)

------------------------------------------------------------------------
-- SigOp Contract (imported from Once.CCC.SigOp.Contract)
------------------------------------------------------------------------

import Once.CCC.SigOp.Contract as PrimContractModule
module SigOpContract {FS : FrameSemantics} (program-bound : ℕ) =
  PrimContractModule.Def {FS} program-bound

------------------------------------------------------------------------
-- Closure IR Tracking
--
-- Since valid-closure tracks the body IR, we get it from decomposition.
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
-- Dynamic Capacity Design
--
-- Each closure carries its body-capacity (= ir-stack-requirement body).
-- When apply creates a child frame, it uses the closure's body-capacity
-- as the frame-capacity. No global worst-case allocation needed.
--
-- Capacity check: next-slot alloc + ir-stack-requirement ir ≤ frame-capacity alloc
------------------------------------------------------------------------

module Dispatcher {FS : FrameSemantics} (program-bound : ℕ) (acc-pb : Acc _<_ program-bound)
  -- The four child-frame parameters (`get-child-frame`,
  -- `child-frame-ordered`, `child-frame-adjacent`,
  -- `escape-result-survives`) have been removed. Apply no longer
  -- creates a child frame; body inherits the parent's frame. See
  -- `Once.CCC.Machine.IR.ApplyWF` for the no-frame model.
  --
  -- SigOp contract provider (from domain compilers)
  (sigOp-proof : SigOpContract.Provider {FS} program-bound)
  where
  open FrontierInvariant {FS}
  open WriteWithDisjoint {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open Once.CCC.Machine.Allocation.Allocator {FS}
  open StackAllocation {FS}
  open FrameSemantics FS
  open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m<m+n; n≤1+n; n<1+n; <-trans; m+n≤o⇒m≤o; +-suc; +-comm; +-monoˡ-≤; +-monoʳ-≤; +-assoc)

  -- Import WF types for termination-safe dispatch
  open ClosureWellFormedDef {FS} program-bound
    using (BodyCorrect; ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           decomposeClosureWF; ClosureValidWF; decomposePairWF; PairValidWF;
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

  -- Import pair IR implementation. Plan 0.14: Stack-mode pairs go to
  -- PairStackWF.run-pair; Heap-mode pairs go to PairAllocWF.run-pair-heap.
  -- Mode is read off the IR (`⟨ f , g ⟩ m`) and case-split in run-ir-wf.
  open PairWFModule.PairStackWFImpl {FS} program-bound
  open PairAllocWFModule.PairAllocWFImpl {FS} program-bound

  -- Import curry IR implementation
  open CurryStackWFModule.CurryStackWFImpl {FS} program-bound
  open CurryAllocWFModule.CurryAllocWFImpl {FS} program-bound
  open SumInlAllocWFModule.SumInlAllocWFImpl {FS} program-bound
  open SumInrAllocWFModule.SumInrAllocWFImpl {FS} program-bound

  -- Import apply IR implementation (no-frame model: body inherits
  -- parent's frame; child-frame parameters no longer exist).
  open ApplyWFModule.ApplyWFImpl {FS} program-bound

  -- Import sum IR implementations (inl, inr, case, initial)
  -- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana handlers instead.
  open import Once.CCC.Machine.IR.SumRecWF as SumRecWFModule
  open SumRecWFModule.SumRecWFImpl {FS} program-bound

  -- Import recursion scheme core (Cata, Fuse, Hylo)
  open RecCoreWFModule.RecCoreWFImpl {FS} program-bound

  -- Import paramorphism handler (Para)
  open ParaWFModule.ParaWFImpl {FS} program-bound

  -- Import anamorphism handler (Ana)
  open AnaWFModule.AnaWFImpl {FS} program-bound

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
  -- SigOp handler: uses Provider from module parameter
  --
  -- With opaque SigOp (just a name), we:
  --   1. Get (contract, proof) from sigOp-proof
  --   2. Use proof to execute
  ------------------------------------------------------------------------
  -- Primitives manage their own stack - no capacity precondition.
  --
  -- With the partial `Provider` (D1a), `sigOp-proof` returns
  -- `just (m , proof)` when the provider covers this SigOp, or
  -- `nothing` otherwise. The `nothing` case is handled via
  -- `uncovered-sigOp-placeholder` for Phase A; Phase E introduces
  -- a coverage precondition that rules it out structurally.
  run-sigOp : ∀ {A B} (mIn : AllocMode) (si : SigOpInfo A B)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ m ] IRResultAWF m (SigOp {A} {B} si) x s alloc
  run-sigOp {A} {B} mIn si x input-loc s alloc valid bf nh rdi
    with sigOp-proof {A} {B} si
  ... | just (m , proof) = m , proof mIn x input-loc s alloc valid bf nh rdi
  ... | nothing = uncovered-sigOp-placeholder
    where postulate
      uncovered-sigOp-placeholder : ∃[ m ] IRResultAWF m (SigOp {A} {B} si) x s alloc

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
    -- Note: capacity argument removed in Phase 3
    make-rec-wf : ∀ {n} (ir<bound : n < program-bound) →
      (∀ {m} → m < n → Acc _<_ m) →
      RecDispatcherWF n
    make-rec-wf {n} ir<bound rs mIn ir lt x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' =
      run-ir-wf mIn ir (<-trans lt ir<bound) x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' (rs lt)

    -- run-ir-wf uses Acc _<_ (ir-size ir) for termination.
    -- Uses ValidAtWF input and returns existential mode + IRResultAWF with ValidAtWF output.
    -- For Compose/Pair: sub-IRs have smaller size, so rs gives Acc
    -- For Apply: uses body-correct.execute instead of recursive call!
    -- Note: capacity argument removed in Phase 3
    run-ir-wf : ∀ {A B} (mIn : AllocMode) (ir : IR A B)
      (ir<bound : ir-size ir < program-bound) →
      (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) Input1 ≡ SV-Ptr input-loc →
      Acc _<_ (ir-size ir) →
      ∃[ mOut ] IRResultAWF mOut ir x s alloc

    -- Simple cases delegated to SimpleWF module (returns same mode as input for id/terminal)
    run-ir-wf mIn id _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      mIn , run-id x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- fst/snd extract component modes from pair (input must be Heap for boxed pair)
    -- Stack case is impossible (fst/snd operate on boxed pairs)
    run-ir-wf Heap fst _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      run-fst x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack fst _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      -- Reference-based model: Stack and Heap use same pointer representation
      run-fst x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Heap snd _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      run-snd x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack snd _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      -- Reference-based model: Stack and Heap use same pointer representation
      run-snd x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf mIn terminal _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      mIn , run-terminal x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Arr: effectful morphism coercion (delegated to SimpleWF module)
    -- Converts (A ⇒[ mk-kind q pure ] B) to (A ⇒[ mk-kind Many eff ] B) - semantically identity
    run-ir-wf mIn (arr {A} {B} {q}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      mIn , run-arr {mIn} {A} {B} {q} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- SigOp: signature operations (uses partial proof provider)
    -- The SigOp carries a SigOpInfo; the provider maps the info to
    -- its contract proof (via `run-sigOp`, which handles the Maybe).
    run-ir-wf mIn (SigOp si) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      let (m , result) = run-sigOp mIn si x input-loc s alloc input-valid-wf input-before not-halted rdi-eq
      in m , result

    -- Sum type: inject left
    -- Plan 0.14 (Camp 2): Stack-mode routes to SumRecWF.run-inl (stack-allocated
    -- sum); Heap-mode routes to SumInlAllocWF.run-inl-heap (heap-allocated via
    -- instr-alloc-heap).
    run-ir-wf mIn (inl {A} {B} Stack) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      Stack , run-inl {A} {B} mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq
    run-ir-wf mIn (inl {A} {B} Heap) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      Heap , run-inl-heap {A} {B} mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Sum type: inject right (symmetric to inl)
    run-ir-wf mIn (inr {A} {B} Stack) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      Stack , run-inr {A} {B} mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq
    run-ir-wf mIn (inr {A} {B} Heap) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      Heap , run-inr-heap {A} {B} mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Sum type: case analysis (delegated to SumRecWF module)
    -- Reference-based model: any mode works since sums use pointer representation
    run-ir-wf Heap (case f g) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      run-case {Heap} f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack (case f g) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      -- Reference-based model: Stack and Heap use same pointer representation for sums
      run-case {Stack} f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Initial: absurd elimination (delegated to SumRecWF module)
    run-ir-wf mIn initial _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      run-initial x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- OCP-0003: fold/unfold cases removed. Use In/Cata/Out/Ana instead.

    -- Compose: delegated to ComposeWF module
    run-ir-wf mIn (g ∘ f) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      run-compose mIn f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Pair: delegated to PairWF / PairAllocWF based on mode.
    -- Plan 0.14: the IR carries the mode (`⟨ f , g ⟩ m`); Stack routes
    -- to run-pair (stack-allocated pair), Heap routes to run-pair-heap
    -- (heap-allocated pair via instr-alloc-heap).
    run-ir-wf mIn (⟨ f , g ⟩ Stack) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      Stack , run-pair mIn f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq
    run-ir-wf mIn (⟨ f , g ⟩ Heap) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      Heap , run-pair-heap mIn f g (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Curry: case-split on mode.
    -- Plan 0.14 (Camp 2): Stack-mode routes to CurryStackWF (closure stored on
    -- stack via instr-alloc-stack closure-slots); Heap-mode routes to
    -- CurryAllocWF (closure heap-allocated via instr-alloc-heap 2).
    run-ir-wf mIn (curry {k = k} f Stack) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      Stack , run-curry {k = k} mIn f Stack ir<bound (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq
    run-ir-wf mIn (curry {k = k} f Heap) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      Heap , run-curry-heap {k = k} mIn f ir<bound (make-rec-wf ir<bound rs) x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Apply: uses BodyCorrect.execute from closure (quantity-polymorphic)
    -- Input1 must be Heap (boxed pair of closure * arg)
    -- Uses PURE RECLAMATION: body executes in same frame, then reclaims stack
    --
    -- DYNAMIC CAPACITY THREADING (X86-style):
    -- Capacity proof uses closure-body-capacity which extracts body-capacity
    -- from the closure's BodyCorrect. No program-bound-based derivation needed.
    -- Apply: CHILD FRAME EXECUTION
    -- Body executes in child frame with child-capacity (from module params).
    -- Body capacity follows from child-cap-sufficient
    run-ir-wf Heap (apply {A} {B} {k}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
        run-apply {k = k} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    run-ir-wf Stack (apply {A} {B} {k}) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      -- Reference-based model: Stack and Heap use same pointer representation for pairs
      run-apply {k = k} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- D032/0.5.1: `applyEff` removed. `apply {k = effK}` covers effectful
    -- application uniformly — the kind-polymorphic `run-apply` above.

    -- Free-heap: explicit heap deallocation (delegated to SimpleWF module)
    -- Semantically a no-op (returns input unchanged).
    run-ir-wf mIn (free-heap ref) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      mIn , run-free-heap ref x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Plan 0.11: const literal. The dispatcher needs an
    -- IRResultAWF for `const p vI vM`. Postulated for now —
    -- per-primitive-type discharge produces concrete IRResultAWFs
    -- (similar in shape to SimpleWFImpl's run-X). Audit-visible
    -- trusted-base entry until then.
    run-ir-wf mIn (const p vI vM) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      mIn , run-const-postulate
      where
        postulate
          run-const-postulate : IRResultAWF mIn (const p vI vM) x s alloc

    --------------------------------------------------------------------------
    -- OCP-0003: Recursion Schemes
    --
    -- In/out-μ/Out/in-ν are implemented in SumRecWF (trivial pass-through).
    -- Cata/Fuse/Hylo use the unified RecCoreWF pattern.
    -- Para uses ParaWF with subterm preservation.
    -- Ana uses AnaWF for lazy thunk creation.
    --------------------------------------------------------------------------

    -- In: wrap into μ-type (initial algebra constructor)
    -- By Lambek's Lemma, In : F(μF) → μF is an isomorphism at runtime.
    -- Implementation: allocates 1 slot and stores the pointer.
    run-ir-wf mIn (In {F} wf m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      m , run-In wf mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- out-μ: destruct μ-type (Lambek inverse of In)
    -- By Lambek's Lemma, this is identity at runtime (just pass-through).
    run-ir-wf mIn (out-μ {F} wf) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      Heap , run-out-μ wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Cata: catamorphism (fold over μ-type)
    -- Uses unified RecCoreWF with Cata configuration
    run-ir-wf mIn (Cata {F} wf alg) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      run-cata-core wf alg (make-rec-wf ir<bound rs) mIn x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Para: paramorphism (fold with access to original substructure)
    -- Takes algebra: IR (⟦ F ⟧T (μF × A)) A, recursively applies to μF
    -- Uses ParaWF handler with subterm preservation
    run-ir-wf mIn (Para {F} wf alg) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      run-para-core wf alg (make-rec-wf ir<bound rs) mIn x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Out: observe ν-type (final coalgebra destructor)
    -- By dual Lambek's Lemma, Out : νF → F(νF) is identity at runtime.
    run-ir-wf mIn (Out {F} wf) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      Heap , run-Out wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- in-ν: construct ν-type (Lambek inverse of Out)
    -- By dual Lambek's Lemma, this allocates 1 slot (like In).
    run-ir-wf mIn (in-ν {F} wf m) _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ =
      m , run-in-ν wf mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq

    -- Ana: anamorphism (unfold to build ν-type)
    -- Takes coalgebra: IR A (⟦ F ⟧T A), corecursively builds νF
    -- Uses AnaWF handler for lazy thunk creation
    run-ir-wf mIn (Ana {F} wf coalg) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      run-ana-core wf coalg (make-rec-wf ir<bound rs) mIn x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Hylo: hylomorphism (fused cata ∘ ana)
    -- Combines algebra and coalgebra without intermediate structure
    -- OCP-0003: Based on Fuse, structurally terminating on μG input
    -- Uses unified RecCoreWF with Hylo configuration
    run-ir-wf mIn (Hylo {F} {G} wfF wfG alg coalg) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      run-hylo-core wfF wfG alg coalg (make-rec-wf ir<bound rs) mIn x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Fuse: μ-anchored fusion (correct by construction)
    -- Structural recursion on μG - termination guaranteed by well-foundedness
    -- Uses unified RecCoreWF with Fuse configuration
    run-ir-wf mIn (Fuse {F} {G} wfF wfG alg transform) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq (acc rs) =
      run-fuse-core wfF wfG alg transform (make-rec-wf ir<bound rs) mIn x input-loc s alloc
        input-valid-wf input-before not-halted rdi-eq

    -- Guard/Unguard removed: productivity follows from IR totality

  -- Public API with ValidAtWF
  -- Returns existential mode + IRResultAWF with ValidAtWF for result validity.
  -- Phase 3: capacity parameter removed (frame-capacity is now a shim)
  run-wf : ∀ {A B} (mIn : AllocMode) (ir : IR A B) (ir<bound : ir-size ir < program-bound)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mOut ] IRResultAWF mOut ir x s alloc
  run-wf mIn ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    run-ir-wf mIn ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq
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
--   Sum type capacity (3 - SumRecWF.agda):
--     - sum-slots-bound: type-slots (A + B) ≤ pair-slots * ir-size inl
--     - sucLoc-sum-in-range: suc n < n + type-slots (A + B)
--     - alloc-slots-eq: proof irrelevance for allocation state equality
--     These highlight the tension between fixed pair-slots capacity formula
--     and type-dependent slot allocation. Will be resolved with unboxed stack.
--
--   Fix type capacity (1 - SumRecWF.agda):
--     - fix-slots-bound: type-slots (Fix F) ≤ pair-slots * ir-size fold
--     Similar issue to sum types.
--
-- CAPACITY ARCHITECTURE (DYNAMIC):
--   - Each closure's BodyCorrect.body-capacity determines child frame size
--   - No global worst-case allocation - each apply gets exactly what its body needs
--   - RuntimeContract at CCC boundary provides linker/runtime guarantees
--
-- NEXT STEPS:
--   1. Implement new-frame semantics for apply body execution (eliminates slot-bounded-apply)
------------------------------------------------------------------------