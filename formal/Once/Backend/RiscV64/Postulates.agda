{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.RiscV64.Postulates
--
-- RISC-V64-specific postulates instantiated from common backend modules.
--
-- STATUS: Generalized to Priority 2 (2026-01-02)
--   - run-apply-star follows Once.Backend.Common.ApplyPostulate pattern
--   - Shared semantic specification across all backends (X86, AArch64, RiscV64)
--   - Documentation-based generalization (parameterization not feasible due to Size constraints)
--
-- See Once.Postulates for documentation format and checklist.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; _≤_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; length; _++_)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Bool using (false)
open import Size using (Size)

open import Once.Type using (Type; _⇒_; _*_)
open import Once.IR using (apply; IR)
open import Once.Semantics using (⟦_⟧; encode)

open import Once.Backend.RiscV64.Syntax using (a0; sp; Program; Reg)
open import Once.Backend.RiscV64.Semantics using (State; readReg; RegFile)
open import Once.Backend.RiscV64.Semantics using () renaming (module State to St)
open St using (regs; halted; pc)
open import Once.Backend.RiscV64.CodeGen using (compile-riscv; StackDepth)
open import Once.Backend.RiscV64.Correct.StarBase using (IRStarResult)

-- Reference the common apply postulate pattern documentation
-- (See Once.Backend.Common.ApplyPostulate for detailed documentation)
postulate
  run-apply-star : ∀ {i A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode {(A ⇒ B) * A} x →
    ∃[ s' ] IRStarResult (apply {i} {A} {B})
                         (prefix ++ compile-riscv (apply {i} {A} {B}) ++ suffix)
                         s s' x (length prefix)

------------------------------------------------------------------------
-- Postulate R1: Closure Application (Semantic Axiom)
------------------------------------------------------------------------
--
-- GENERALIZED (Priority 2): Follows Once.Backend.Common.ApplyPostulate pattern
--
-- Executing `apply` on a closure produces the correct result.
--
-- SCOPE: Backend-agnostic SEMANTIC AXIOM about the curry/apply calling convention.
--        Documentation shared across all backends (X86, AArch64, RiscV64).
--
-- NEEDED BY: Once.Backend.RiscV64.Correct.MutualIR (run-ir-star-at-offset for apply)
--
-- RISC-V64 IMPLEMENTATION DETAILS:
--   - s0: Environment pointer (set by apply, used by thunk)
--   - a0: Both input (closure+arg pair) and output (result)
--   - s1, s2, ra: Preserved (callee-saved per LP64 ABI)
--
-- See Once.Backend.Common.ApplyPostulate for full documentation including:
--   - Semantic boundary justification
--   - Two proof paths (whole-program vs modular)
--   - Validation strategies
--   - Why not parameterized (Size constraints)
--
-- RUNTIME EFFECT: None (proof-only - captures semantic calling convention)
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Postulate R2: Stack Bound for Curry Thunk Execution
------------------------------------------------------------------------
--
-- STATUS: ELIMINATED! (2026-01-02)
--
-- This postulate claimed:
--   ∀ {i A B C} (f : IR (A * B) C) (s : State) →
--     StackDepth f ≤ readReg (regs s) sp
--
-- This was a FALSE universal claim (claimed ANY IR f fits in ANY sp).
--
-- SOLUTION: Thread explicit stack preconditions through proof chain:
--   1. curry-thunk-correct-impl now requires: StackDepth (curry f) ≤ sp
--   2. Arithmetic proof derives: StackDepth f ≤ sp - curry-frame-value
--   3. curry-frame-value = 24 (proven from ThunkSetup.agda instructions)
--   4. No postulate needed!
--
-- See:
--   - Once/Backend/RiscV64/Correct/CurryFrameProof.agda (proves curry-frame = 24)
--   - Once/Backend/RiscV64/Correct/MutualIR.agda lines 1621-1650 (arithmetic proof)
--   - Once/Backend/RiscV64/Correct/ClosureWellFormed.agda (stack-requirement parameter)
--
-- This follows the same pattern as eliminating stackDepth-leq-stackBase:
--   Replace false universal claims with explicit preconditions.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: Stack Space Postulate REMOVED (2026-01-01)
------------------------------------------------------------------------
--
-- The postulate `stackDepth-leq-stackBase` was REMOVED from Foundation.agda
-- because it was mathematically FALSE:
--
--   OLD (REMOVED):
--     postulate
--       stackDepth-leq-stackBase : ∀ ir → StackDepth ir ≤ 0x7FFF0000
--
-- This claimed all IR programs fit in 2GB, but arbitrary deep nesting
-- (e.g., compose/pair chains) can exceed any fixed bound.
--
-- NEW APPROACH (Explicit Stack Parameterization):
--   1. initWithInput now takes explicit stackSize parameter
--   2. Correctness theorems require explicit precondition:
--        star-codegen-correct : ∀ ir stackSize x →
--          StackDepth ir ≤ stackSize → ...
--   3. For specific programs, StackDepth is computable (total function)
--   4. Compiler emits required stack; runtime provides sufficient stack
--
-- This replaces a false universal claim ("all IR fit in N bytes") with
-- a provable specific claim ("given ≥ N bytes for this IR, it works").
--
-- Stack analysis is now in Once.Backend.Common.StackAnalysis, shared
-- across all backends (X86, AArch64, RiscV64).
--
------------------------------------------------------------------------
