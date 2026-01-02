{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.RiscV64.Postulates
--
-- RISC-V64-specific postulates. Separated from Once.Postulates to avoid
-- cyclic imports with RISC-V64 modules.
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

open import Once.Backend.RiscV64.Syntax using (a0; sp; Program)
open import Once.Backend.RiscV64.Semantics using (State; readReg)
open import Once.Backend.RiscV64.Semantics using () renaming (module State to St)
open St using (regs; halted; pc)
open import Once.Backend.RiscV64.CodeGen using (compile-riscv; StackDepth)
open import Once.Backend.RiscV64.Correct.StarBase using (IRStarResult)

------------------------------------------------------------------------
-- Postulate R1: Closure Application (Semantic Axiom)
------------------------------------------------------------------------
--
-- Executing `apply` on a closure produces the correct result.
--
-- SCOPE: This is a SEMANTIC AXIOM about the curry/apply calling convention.
--        It states that closures created by curry can be successfully invoked
--        by apply, producing the expected result.
--
-- NEEDED BY: Once.Backend.RiscV64.Correct.MutualIR (run-ir-star-at-offset for apply)
--
-- ========================================================================
-- JUSTIFICATION: Why This is a Semantic Boundary
-- ========================================================================
--
-- The `apply` generator compiles to code that performs an indirect call:
--   1. Load closure from a0 (pair containing env + code pointer)
--   2. Extract environment pointer → s0
--   3. Extract code pointer → temporary register
--   4. Extract argument from pair
--   5. jalr to code pointer (indirect call to curry thunk)
--
-- The curry thunk code is NOT part of the apply instruction sequence.
-- When proving apply in isolation (at an arbitrary program offset), the
-- thunk code doesn't exist in the local context.
--
-- Therefore, we cannot prove that the indirect call produces the correct
-- result without reasoning about the entire program containing both the
-- curry generator (which created the thunk) and the apply generator.
--
-- This postulate axiomatizes the curry/apply calling convention:
--   - curry creates a closure: (encoded-env, thunk-code-ptr)
--   - apply loads env → s0, extracts arg, calls thunk
--   - thunk pairs (s0, arg), calls f, returns result in a0
--
-- ========================================================================
-- VERIFICATION STRATEGY: Two Proof Paths
-- ========================================================================
--
-- PATH 1: Whole-Program Proofs (POSTULATE-FREE)
--   For closed programs where every apply has a corresponding curry:
--   1. run-curry-star-with-wf produces ClosureWellFormed proof
--   2. Thread WF proof through compose/pair/case
--   3. run-apply-with-wf consumes the WF proof (IR/Apply.agda)
--   4. Result: Zero postulates needed for closed programs
--
-- PATH 2: Modular Proofs (USES THIS POSTULATE)
--   For open program fragments or modular reasoning:
--   1. Apply may receive closures from external sources
--   2. Cannot construct ClosureWellFormed without curry context
--   3. This axiom captures the calling convention semantics
--
-- ========================================================================
-- VALIDATION
-- ========================================================================
--
-- This postulate can be validated through:
--   1. End-to-end trace proofs (e.g., apply ∘ ⟨curry fst, id⟩)
--   2. Inspection of generated assembly
--   3. Whole-program proofs using ClosureWellFormed threading
--
-- See formal/Once/Backend/RiscV64/Examples/CurryApplyTrace.agda (when created)
-- for step-by-step validation that the curry/apply protocol works.
--
-- ARCHITECTURAL NOTE:
--   RISC-V uses s0 for the environment pointer (not preserved across IR nodes).
--   This is part of the closed-world curry/apply contract, not the general
--   RISC-V LP64 ABI. The closure protocol is:
--     - s0: Environment pointer (set by apply, used by thunk)
--     - a0: Both input (closure+arg pair) and output (result)
--     - s1, s2, ra: Preserved (callee-saved per LP64 ABI)
--
-- RUNTIME EFFECT: None (proof-only - captures semantic calling convention)
--
------------------------------------------------------------------------

postulate
  run-apply-star : ∀ {i A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode {(A ⇒ B) * A} x →
    let prog = prefix ++ compile-riscv (apply {i} {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResult (apply {i} {A} {B}) prog s s' x (length prefix)

------------------------------------------------------------------------
-- Postulate R2: Stack Bound for Curry Thunk Execution
------------------------------------------------------------------------
--
-- STATUS: ELIMINATED! (2026-01-02)
--
-- This postulate claimed:
--   ∀ {i A B C} (f : IR i (A * B) C) (s : State) →
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
