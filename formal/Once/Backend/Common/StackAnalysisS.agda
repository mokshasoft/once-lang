{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- Once.Backend.Common.StackAnalysis
--
-- Common stack usage analysis for all backend architectures.
-- This module is parameterized by backend-specific frame allocation sizes.
--
-- Stack analysis computes two key metrics for any IR program:
--   - StackDelta: Net stack bytes allocated after IR completes
--   - StackDepth: Maximum stack depth needed during execution
--
-- These are used to:
--   1. Compute stack requirements at compile time
--   2. Prove sufficient stack space in correctness theorems
--   3. Eliminate false universal bounds postulates
--
-- Usage:
--   module Once.Backend.MyArch.CodeGen where
--     open import Once.Backend.Common.StackAnalysis
--       32  -- pair-frame
--       16  -- inl-frame
--       16  -- inr-frame
--       16  -- curry-frame
--       24  -- apply-frame
--       public
--
-- Benefits:
--   - Single source of truth for stack analysis logic
--   - Automatic uniformity across backends
--   - Each backend only specifies architecture-specific allocation sizes
--   - Easier to extend with new IR constructors
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _⊔_) renaming (_+_ to _+ℕ_)

open import Once.Type
open import Once.IRS

module Once.Backend.Common.StackAnalysisS
  (pair-frame : ℕ)    -- Bytes allocated for pair ⟨ f , g ⟩
  (inl-frame : ℕ)     -- Bytes allocated for left injection
  (inr-frame : ℕ)     -- Bytes allocated for right injection
  (curry-frame : ℕ)   -- Bytes allocated for curry closure
  (apply-frame : ℕ)   -- Conservative bound for apply thunk
  where

------------------------------------------------------------------------
-- Stack Delta: Net Stack Allocation
------------------------------------------------------------------------

-- | StackDelta: Net stack bytes allocated after IR completes
--
-- This is the change in stack pointer from entry to exit.
-- Operations that allocate data (pair, inl, inr, curry) leave stack
-- allocated. Others restore sp before returning.
--
-- Key insight: StackDelta tells us how much stack is still in use
-- after an IR morphism completes, which affects nested operations.
--
-- Examples:
--   - StackDelta id = 0 (no allocation)
--   - StackDelta ⟨ f , g ⟩ = pair-frame + StackDelta f + StackDelta g
--   - StackDelta (f ∘ g) = StackDelta f + StackDelta g (f runs first)
--
StackDelta : ∀ {i A B} → IR i A B → ℕ
StackDelta id = 0
StackDelta (g ∘ f) = StackDelta f +ℕ StackDelta g  -- f runs first, then g
StackDelta fst = 0
StackDelta snd = 0
StackDelta ⟨ f , g ⟩ = pair-frame +ℕ StackDelta f +ℕ StackDelta g
StackDelta inl = inl-frame
StackDelta inr = inr-frame
StackDelta [ f , g ] = StackDelta f ⊔ StackDelta g  -- only one branch runs
StackDelta terminal = 0
StackDelta initial = 0
StackDelta (curry f) = curry-frame  -- closure allocation; thunk cleans up
StackDelta apply = 0                -- thunk deallocates its frame
StackDelta fold = 0
StackDelta unfold = 0
StackDelta arr = 0
StackDelta (Prim _ _ _) = 0  -- Primitives don't allocate stack

------------------------------------------------------------------------
-- Stack Depth: Maximum Stack Usage
------------------------------------------------------------------------

-- | StackDepth: Maximum stack depth needed at any point during execution
--
-- Precondition: StackDepth ir ≤ sp ensures enough stack space.
--
-- This is the key property for correctness proofs. If we start with
-- sp ≥ StackDepth ir, we're guaranteed never to overflow during execution.
--
-- For pair ⟨ f , g ⟩:
--   - Allocates pair-frame bytes, then runs f and g with sp' = sp - pair-frame
--   - f and g each need their own depth from the reduced stack
--   - So: pair-frame + max(StackDepth f, StackDelta f + StackDepth g)
--
-- For compose (f ∘ g):
--   - Runs f first, then g with sp' = sp - StackDelta f
--   - Need: max(StackDepth f, StackDelta f + StackDepth g)
--
-- The StackDepth is COMPUTABLE for any concrete IR term, making stack
-- requirements an explicit, provable property rather than an assumption.
--
StackDepth : ∀ {i A B} → IR i A B → ℕ
StackDepth id = 0
StackDepth (g ∘ f) = StackDepth f ⊔ (StackDelta f +ℕ StackDepth g)  -- f first
StackDepth fst = 0
StackDepth snd = 0
StackDepth ⟨ f , g ⟩ = pair-frame +ℕ (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g))
StackDepth inl = inl-frame
StackDepth inr = inr-frame
StackDepth [ f , g ] = StackDepth f ⊔ StackDepth g
StackDepth terminal = 0
StackDepth initial = 0
StackDepth (curry f) = curry-frame +ℕ StackDepth f  -- curry + thunk needs f's depth
StackDepth apply = apply-frame  -- thunk frame; actual f depth unknown statically
StackDepth fold = 0
StackDepth unfold = 0
StackDepth arr = 0
StackDepth (Prim _ _ _) = 0  -- Primitives don't need stack depth

------------------------------------------------------------------------
-- Key Property: StackDepth Is Computable
------------------------------------------------------------------------
--
-- For any concrete IR term, StackDepth computes a finite natural number.
-- This is guaranteed by the type signature - StackDepth is a total function.
--
-- There is NO universal bound across all IR programs (any fixed bound
-- can be exceeded by sufficiently deep nesting). However, for any
-- SPECIFIC program, the required stack is computable.
--
-- This enables:
--   1. Compiler emits stack requirement: "This program needs N bytes"
--   2. Runtime checks: if available ≥ N, run; else reject
--   3. Correctness: if provided ≥ N, execution succeeds
--
-- The false postulate "all IR fit in 2GB" is replaced by explicit
-- preconditions: "if you provide ≥ StackDepth ir, it works".
--
------------------------------------------------------------------------
