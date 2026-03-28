------------------------------------------------------------------------
-- Once.CCC.Machine.IR.AnaWF
--
-- Anamorphism handler for lazy corecursive production.
--
-- OCP-0003: Ana (anamorphism) is fundamentally different from Cata/Para.
-- While those eagerly consume μ-types, Ana lazily produces ν-types.
--
-- Implementation: ν-types are represented as thunks containing:
--   - coalg-ref: reference to the coalgebra IR
--   - seed: the current seed value
--
-- When observed via Out, the thunk is forced by applying coalg to seed,
-- producing an F-layer with new seeds for recursive positions.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.AnaWF where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
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

-- Import SMPrimitives for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- ν-Type Representation
--
-- ν-types (final coalgebras) are represented as lazy thunks:
--
-- [thunk-slot] = { coalg-ref, seed }
--      ↑
--   νF pointer
--
-- The thunk contains:
--   - coalg-ref: pointer to the coalgebra closure/code
--   - seed: current seed value of type A
--
-- When Out observes the ν-value:
--   1. Load coalg and seed from thunk
--   2. Apply coalg to seed: A → F(A)
--   3. For each recursive position in F(A):
--      - Create new thunk with same coalg and new sub-seed
--   4. Return F(νF) with thunks at recursive positions
------------------------------------------------------------------------

-- | Thunk slot layout
thunk-coalg-offset : ℕ
thunk-coalg-offset = 0

thunk-seed-offset : ℕ
thunk-seed-offset = 1

------------------------------------------------------------------------
-- AnaWF Implementation
--
-- Ana creates a thunk representing the ν-value.
-- No recursion needed - we just package coalg + seed.
------------------------------------------------------------------------

module AnaWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
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
  -- Ana: Anamorphism (unfold to build ν-type)
  --
  -- Semantically: ana coalg x produces the infinite structure νF
  -- where each observation (Out) reveals one F-layer.
  --
  -- Implementation: Create a thunk { coalg-ref, seed }
  --   1. Allocate thunk slot
  --   2. Store coalg reference (or inline code pointer)
  --   3. Store seed value
  --   4. Return pointer to thunk
  --
  -- Note: The coalgebra is not applied here - that happens in Out.
  -- This is the essence of lazy production: delay computation until
  -- observation forces it.
  --
  -- Productivity: Guaranteed by IR totality of coalgebra.
  -- Each Out application terminates, producing one F-layer.
  ------------------------------------------------------------------------

  -- | run-ana-core: anamorphism handler (lazy thunk creation)
  -- Note: rec-wf bound matches ir-size (Ana wf coalg) for recursion in coalg
  -- Though Ana itself doesn't recurse, the coalgebra execution may need it
  postulate
    run-ana-core : ∀ {F A}
      → (wf : WellFormedF F)
      → (coalg : IR A (⟦ F ⟧T A))
      → (rec-wf : RecDispatcherWF (ir-size (Ana wf coalg)))
      → (mIn : AllocMode)
      → (x : ⟦ A ⟧)
      → (input-loc : ValueLocation FS)
      → (s : LocState FS)
      → (alloc : AllocState {FS})
      → ValidAtWF mIn alloc x input-loc s
      → BeforeFrontier alloc input-loc
      → halted s ≡ false
      → readReg (regs s) Input ≡ input-loc
      → next-slot alloc +ℕ ir-stack-requirement (Ana wf coalg) ≤ frame-capacity alloc
      → ∃[ mOut ] IRResultAWF mOut (Ana wf coalg) x s alloc

------------------------------------------------------------------------
-- Summary
--
-- AnaWF provides:
--   1. Thunk representation for ν-types (coalg-ref + seed)
--   2. run-ana-core: postulated anamorphism handler
--
-- Key difference from Cata/Para:
--   - Cata/Para: eagerly consume μ-types via structural recursion
--   - Ana: lazily produce ν-types by creating thunks
--
-- The thunk representation enables:
--   - Infinite structures (productivity, not termination)
--   - Lazy evaluation (compute on demand via Out)
--   - Sharing (same coalg + different seeds)
--
-- When Out observes a ν-value:
--   1. Extract coalg and seed from thunk
--   2. Execute coalg on seed to get F(A)
--   3. For each recursive A in F(A), create new thunk
--   4. Return F(νF) with thunks at recursive positions
--
-- The postulated run-ana-core captures the thunk creation.
-- Observation semantics are handled by Out in SumRecWF.
------------------------------------------------------------------------
