------------------------------------------------------------------------
-- Once.CCC.Machine.IR.ParaWF
--
-- Paramorphism handler extending the unified recursive core.
--
-- OCP-0003: Para is similar to Cata, but the algebra receives both
-- the original substructure and the recursive result for each
-- recursive position: F(μF × A) → A instead of F(A) → A.
--
-- Implementation: Extends RecCoreWF pattern with subterm preservation.
-- For each recursive position, we save the original μF value before
-- recursing, then pair it with the recursive result.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.ParaWF where

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
-- Slot Layout for Paramorphism
--
-- Para extends the RecCore slot layout with an additional slot for
-- preserving the original subterm at each recursive position.
--
-- [backup-slot] [layer-slot] [acc-slot] [subterm-slot] [work-slots...] [alg-workspace]
--      ↑            ↑            ↑            ↑              ↑              ↑
--   input       F-layer    accumulator   orig μF     recursion work    IR workspace
------------------------------------------------------------------------

-- | Para-specific slot offsets (extends RecCore layout)
subterm-offset : ℕ
subterm-offset = 3

para-work-offset : ℕ
para-work-offset = 4

------------------------------------------------------------------------
-- ParaWF Implementation
--
-- The paramorphism pattern with postulated core operation.
-- Full proof obligations will be discharged when implementation is complete.
------------------------------------------------------------------------

module ParaWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
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
  -- Para: Paramorphism (fold with original substructure access)
  --
  -- Semantically: para alg x = cata (alg ∘ F(id △ rec)) x
  --
  -- Where (id △ rec) pairs each subterm with its recursive result:
  --   id △ rec : μF → μF × A
  --
  -- The algebra then sees F(μF × A) for each layer.
  --
  -- Implementation strategy:
  --   1. Destruct μF to get F(μF) layer
  --   2. For each recursive position:
  --      a. Save original μF subterm at subterm-slot
  --      b. Recursively process to get A result
  --      c. Build pair (μF, A)
  --   3. Apply algebra to F(μF × A) → A
  --   4. Return result
  --
  -- Termination: structural recursion on μF (same as Cata).
  ------------------------------------------------------------------------

  -- | run-para-core: paramorphism handler
  -- Note: rec-wf bound matches ir-size (Para wf alg) for proper recursion
  postulate
    run-para-core : ∀ {F A}
      → (wf : WellFormedF F)
      → (alg : IR (⟦ F ⟧T (μ-type F * A)) A)
      → (rec-wf : RecDispatcherWF (ir-size (Para wf alg)))
      → (mIn : AllocMode)
      → (x : ⟦ μ-type F ⟧)
      → (input-loc : ValueLocation FS)
      → (s : LocState FS)
      → (alloc : AllocState {FS})
      → ValidAtWF mIn alloc x input-loc s
      → BeforeFrontier alloc input-loc
      → halted s ≡ false
      → readReg (regs s) Input ≡ input-loc
      → next-slot alloc +ℕ ir-stack-requirement (Para wf alg) ≤ frame-capacity alloc
      → ∃[ mOut ] IRResultAWF mOut (Para wf alg) x s alloc

------------------------------------------------------------------------
-- Summary
--
-- ParaWF provides:
--   1. Slot layout extension for subterm preservation
--   2. run-para-core: postulated paramorphism handler
--
-- Para extends the RecCoreWF pattern by:
--   - Saving original subterms before recursive calls
--   - Building (μF, A) pairs after recursive calls
--   - Passing F(μF × A) to the algebra instead of F(A)
--
-- The postulated run-para-core captures the full proof obligation.
-- When fully implemented, it will use structural recursion on μF
-- to guarantee termination.
------------------------------------------------------------------------
