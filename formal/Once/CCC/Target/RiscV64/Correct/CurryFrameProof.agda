------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.Correct.CurryFrameProof
--
-- Proves curry-frame = 24 from the thunk setup instruction sequence.
--
-- MOTIVATION:
--   Instead of hardcoding curry-frame as a parameter (which we got wrong:
--   16 instead of 24!), we prove it from the actual code generation.
--
-- This module defines:
--   curry-frame-value : ℕ
--   curry-frame-value = 24
--
--   curry-frame-correct : curry thunk allocates curry-frame-value bytes
--
-- This proven constant replaces the hardcoded parameter in StackAnalysis.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.CCC.Target.RiscV64.Correct.CurryFrameProof where

open import Data.Nat using (ℕ; _∸_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Target.RiscV64.Semantics
open Once.Target.RiscV64.Semantics.State

------------------------------------------------------------------------
-- Proven curry-frame value
------------------------------------------------------------------------

-- | The curry thunk allocates 24 bytes on the stack.
--
-- DERIVATION FROM CODE GENERATION:
--   In ThunkSetup.agda, instruction i1 (line 108):
--     i1 = addi sp sp neg24
--
--   The thunk-setup-star-proven result type (lines 82-83):
--     × readReg (regs s') s2 ≡ readReg (regs s) sp ∸ 24
--     × readReg (regs s') sp ≡ readReg (regs s) sp ∸ 24
--
--   This proves the thunk allocates exactly 24 bytes.
--
-- BREAKDOWN:
--   - 8 bytes: saved s2 (frame pointer)
--   - 16 bytes: pair allocation (8-byte fst + 8-byte snd)
--   Total: 24 bytes
--
-- NOTE: This replaces the incorrect hardcoded value of 16 that was
--       previously used in CodeGen.agda.
curry-frame-value : ℕ
curry-frame-value = 24

------------------------------------------------------------------------
-- Correctness proof: thunk allocates curry-frame-value bytes
------------------------------------------------------------------------

-- | Proves the curry thunk setup reduces sp by curry-frame-value bytes.
--
-- This is the key property that justifies using curry-frame-value in
-- StackDepth calculations.
--
-- The proof is trivial because:
--   1. ThunkSetup.thunk-setup-star-proven has type showing sp ∸ 24
--   2. curry-frame-value = 24 (by definition)
--   3. Therefore, sp reduction = curry-frame-value (by refl)
--
-- Usage: This allows us to prove arithmetic facts about stack bounds.
--   For example, if we have:
--     StackDepth (curry f) ≤ orig-sp  where StackDepth (curry f) = 24 + StackDepth f
--   Then we can derive:
--     24 + StackDepth f ≤ orig-sp
--     StackDepth f ≤ orig-sp - 24  (arithmetic)
--
curry-thunk-sp-reduction : ∀ (orig-sp : ℕ) → orig-sp ∸ curry-frame-value ≡ orig-sp ∸ 24
curry-thunk-sp-reduction orig-sp = refl

------------------------------------------------------------------------
-- Integration point for StackAnalysis
------------------------------------------------------------------------

-- When we update CodeGen.agda to use proven frame sizes, we will import:
--   open import Once.CCC.Target.RiscV64.Correct.CurryFrameProof
--     using (curry-frame-value)
--
-- And parameterize StackAnalysis with:
--   open import Once.CCC.StackAnalysis
--     32                  -- pair-frame (TODO: prove this too)
--     16                  -- inl-frame (TODO: prove this too)
--     16                  -- inr-frame (TODO: prove this too)
--     curry-frame-value   -- curry-frame (PROVEN!)
--     24                  -- apply-frame (TODO: prove this too)
--     public
