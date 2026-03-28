------------------------------------------------------------------------
-- Once.CCC.Machine.IR.RecCoreWF
--
-- Unified recursive core for μ-consuming recursion schemes.
--
-- OCP-0003: This module provides a single parameterized implementation
-- that handles Cata, Fuse, and Hylo. The differences are:
--   - Cata: transform = id (no transformation)
--   - Fuse: transform = user-provided IR
--   - Hylo: transform = coalg ∘ In
--
-- Key insight: All μ-consuming schemes share the same iteration pattern:
--   1. Destructure μ-type (out-μ)
--   2. Dispatch on functor structure (K/Id/⊕/⊗)
--   3. For each recursive position: recurse
--   4. Apply processing IR(s)
--   5. Return result
------------------------------------------------------------------------

module Once.CCC.Machine.IR.RecCoreWF where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86-64.Types
open import Once.CCC.IR
open import Once.Type using (Functor)
open import Once.Functor.Translate using (WellFormedF)
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import functor dispatch helpers
open import Once.CCC.Machine.IR.FunctorDispatch

-- Import SMPrimitives for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- RecConfig: Configuration record for the unified recursive core
--
-- This parameterizes the recursion scheme by:
--   - wfF, wfG: well-formedness proofs for functors
--   - algebra: the consuming algebra F(B) → B
--   - transform: optional transformation G(μG) → F(μG)
--     - Nothing for Cata (identity, F = G)
--     - Just trans for Fuse/Hylo
------------------------------------------------------------------------

record RecConfig {F G : Functor} (wfF : WellFormedF F) (wfG : WellFormedF G)
                 (B : Type) : Set where
  field
    algebra : IR (⟦ F ⟧T B) B
    -- Transform: Nothing means identity (Cata), Just means Fuse/Hylo
    has-transform : Maybe (IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))

open RecConfig public

------------------------------------------------------------------------
-- Configuration constructors
------------------------------------------------------------------------

-- | Cata configuration: F = G, no transform (identity)
cata-config : ∀ {F B} (wf : WellFormedF F) (alg : IR (⟦ F ⟧T B) B)
            → RecConfig wf wf B
cata-config wf alg = record
  { algebra = alg
  ; has-transform = nothing
  }

-- | Fuse configuration: transform G-layers to F-layers
fuse-config : ∀ {F G B} (wfF : WellFormedF F) (wfG : WellFormedF G)
            → (alg : IR (⟦ F ⟧T B) B)
            → (transform : IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))
            → RecConfig wfF wfG B
fuse-config wfF wfG alg transform = record
  { algebra = alg
  ; has-transform = just transform
  }

-- | Hylo configuration: coalg ∘ In is the transform
-- Note: The coalg here is μG → F(μG), and we need G(μG) → F(μG)
-- For Hylo, G = F and we use coalg directly on the destructed layer
hylo-config : ∀ {F G B} (wfF : WellFormedF F) (wfG : WellFormedF G)
            → (alg : IR (⟦ F ⟧T B) B)
            → (coalg : IR (μ-type G) (⟦ F ⟧T (μ-type G)))
            → RecConfig wfF wfG B
hylo-config wfF wfG alg coalg = record
  { algebra = alg
  -- For Hylo, transform wraps In around the G-layer then applies coalg
  -- G(μG) → μG → F(μG)
  -- This is: coalg ∘ In
  ; has-transform = just (coalg ∘ In wfG Heap)
  }

------------------------------------------------------------------------
-- NOTE: RecConfig is used for design documentation.
-- Stack requirements are computed from the actual IR constructors
-- via ir-stack-requirement in IR/Stack.agda.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Slot Layout for Recursive Core
--
-- [backup-slot] [layer-slot] [acc-slot] [work-slots...] [alg/trans-workspace]
--      ↑            ↑            ↑           ↑                  ↑
--   input       F/G-layer    accumulator  recursion        IR workspace
------------------------------------------------------------------------

-- | Slot offsets relative to frontier
backup-offset : ℕ
backup-offset = 0

layer-offset : ℕ
layer-offset = 1

acc-offset : ℕ
acc-offset = 2

work-offset : ℕ
work-offset = 3

------------------------------------------------------------------------
-- RecCoreWF Implementation
--
-- The unified recursive pattern with postulated core operations.
-- Full proof obligations will be discharged when the functor
-- dispatch infrastructure is complete.
------------------------------------------------------------------------

module RecCoreWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules
  open SMP.TracePrimitives {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance)

  ------------------------------------------------------------------------
  -- Specialized Entry Points for Recursion Schemes
  --
  -- Each scheme is postulated with its specific IR constructor.
  -- The underlying recursive pattern is the same:
  --   1. Store input at backup-slot
  --   2. Apply out-μ to get G-layer
  --   3. Optional: apply transform (G-layer → F-layer)
  --   4. Dispatch on functor structure
  --   5. Apply algebra to get result
  --   6. Return result in Output register
  --
  -- Termination: structural recursion on μG.
  ------------------------------------------------------------------------

  -- | Cata: catamorphism (fold over μ-type)
  -- Note: rec-wf bound matches ir-size (Cata wf alg) for proper recursion
  postulate
    run-cata-core : ∀ {F A}
      → (wf : WellFormedF F)
      → (alg : IR (⟦ F ⟧T A) A)
      → (rec-wf : RecDispatcherWF (ir-size (Cata wf alg)))
      → (mIn : AllocMode)
      → (x : ⟦ μ-type F ⟧)
      → (input-loc : ValueLocation FS)
      → (s : LocState FS)
      → (alloc : AllocState {FS})
      → ValidAtWF mIn alloc x input-loc s
      → BeforeFrontier alloc input-loc
      → halted s ≡ false
      → readReg (regs s) Input ≡ input-loc
      → next-slot alloc +ℕ ir-stack-requirement (Cata wf alg) ≤ frame-capacity alloc
      → ∃[ mOut ] IRResultAWF mOut (Cata wf alg) x s alloc

  -- | Fuse: μ-anchored fusion
  -- Note: rec-wf bound matches ir-size (Fuse ...) for proper recursion
  postulate
    run-fuse-core : ∀ {F G B}
      → (wfF : WellFormedF F)
      → (wfG : WellFormedF G)
      → (alg : IR (⟦ F ⟧T B) B)
      → (transform : IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))
      → (rec-wf : RecDispatcherWF (ir-size (Fuse wfF wfG alg transform)))
      → (mIn : AllocMode)
      → (x : ⟦ μ-type G ⟧)
      → (input-loc : ValueLocation FS)
      → (s : LocState FS)
      → (alloc : AllocState {FS})
      → ValidAtWF mIn alloc x input-loc s
      → BeforeFrontier alloc input-loc
      → halted s ≡ false
      → readReg (regs s) Input ≡ input-loc
      → next-slot alloc +ℕ ir-stack-requirement (Fuse wfF wfG alg transform) ≤ frame-capacity alloc
      → ∃[ mOut ] IRResultAWF mOut (Fuse wfF wfG alg transform) x s alloc

  -- | Hylo: hylomorphism (fused cata ∘ ana)
  -- Note: rec-wf bound matches ir-size (Hylo ...) for proper recursion
  postulate
    run-hylo-core : ∀ {F G B}
      → (wfF : WellFormedF F)
      → (wfG : WellFormedF G)
      → (alg : IR (⟦ F ⟧T B) B)
      → (coalg : IR (μ-type G) (⟦ F ⟧T (μ-type G)))
      → (rec-wf : RecDispatcherWF (ir-size (Hylo wfF wfG alg coalg)))
      → (mIn : AllocMode)
      → (x : ⟦ μ-type G ⟧)
      → (input-loc : ValueLocation FS)
      → (s : LocState FS)
      → (alloc : AllocState {FS})
      → ValidAtWF mIn alloc x input-loc s
      → BeforeFrontier alloc input-loc
      → halted s ≡ false
      → readReg (regs s) Input ≡ input-loc
      → next-slot alloc +ℕ ir-stack-requirement (Hylo wfF wfG alg coalg) ≤ frame-capacity alloc
      → ∃[ mOut ] IRResultAWF mOut (Hylo wfF wfG alg coalg) x s alloc

------------------------------------------------------------------------
-- Summary
--
-- RecCoreWF provides:
--   1. RecConfig: configuration record for scheme parameters
--   2. cata-config, fuse-config, hylo-config: configuration constructors
--   3. run-rec-core: postulated unified recursive handler
--   4. run-cata-core, run-fuse-core, run-hylo-core: specialized entry points
--
-- The postulated run-rec-core captures the full proof obligation.
-- When fully implemented, it will use structural recursion on μG
-- to guarantee termination.
------------------------------------------------------------------------
