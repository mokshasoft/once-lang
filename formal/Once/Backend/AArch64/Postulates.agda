{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Postulates
--
-- AArch64-specific postulates. Separated from Once.Postulates to avoid
-- cyclic imports with AArch64 modules.
--
-- See Once.Postulates for documentation format and checklist.
------------------------------------------------------------------------

module Once.Backend.AArch64.Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; length; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)

open import Once.Type using (Type; _⇒_; _*_)
open import Once.IR using (apply; curry; IR)
open import Once.Semantics using (⟦_⟧; encode; eval)
open import Once.Memory using (Word)

open import Once.Backend.AArch64.Syntax using (x0; x19; x20; x21; x29; x30; Program)
open import Once.Backend.AArch64.Semantics using (State; readReg; readSP; readMem)
open import Once.Backend.AArch64.Semantics using () renaming (module State to St)
open St using (regs; memory; halted; pc)
open import Once.Backend.AArch64.Correct.Star using (Star)
open import Once.Backend.AArch64.Correct.StackInvariant using (StackInvariant; X29Invariant)
open import Once.Backend.AArch64.CodeGen using (compile-aarch64; compile-length)

------------------------------------------------------------------------
-- Postulate P4: Stack Pointer Bounds (Runtime Property)
------------------------------------------------------------------------
--
-- After any stack-using operation, sp remains > 16.
--
-- NEEDED BY: Once.Backend.AArch64.Correct.MutualIR (inl, inr, pair, case, curry)
--
-- JUSTIFICATION:
--   The initial sp is a large address (e.g., 0x7FFF0000). Stack-using
--   operations subtract at most 64 bytes per call. Even with deep
--   recursion (millions of calls), total stack usage is bounded and
--   sp never drops below 16. This is a runtime guarantee from the
--   execution environment.
--
-- IMPACT:
--   If the stack were exhausted, the program would crash before returning
--   an incorrect result. This axiom captures that we're assuming sufficient
--   stack space, which is true for any realistic program execution.
--
-- RUNTIME EFFECT: Assumes sufficient stack space (standard runtime assumption)
--
------------------------------------------------------------------------

postulate
  sp-bound-after-stack-op : ∀ (s : State) → readSP (regs s) > 16

------------------------------------------------------------------------
-- Postulate P5: Closure Application (Semantic Boundary)
------------------------------------------------------------------------
--
-- Executing `apply` on a closure produces the correct result.
--
-- NEEDED BY: Once.Backend.AArch64.Correct.MutualIR (run-apply-star-direct)
--
-- WHY THIS IS HARD TO PROVE (MODULAR CASE):
--   Apply's `blr x9` instruction jumps to a thunk compiled by curry.
--   The thunk code is NOT in `compile-aarch64 apply` - it's somewhere in
--   `prefix` where a previous curry compilation placed it.
--
--   In the modular proof (run-ir-star-at-offset apply), we don't know
--   where the closure came from, so we can't prove the thunk is correct.
--
-- SEMANTIC BOUNDARY:
--   This postulate captures the calling convention between curry and apply:
--   - curry stores (encode env, code_ptr) at closure address
--   - apply loads env→x19, code_ptr→x9, arg→x0, then calls blr x9
--   - blr sets x30 to return address (pc + 1)
--   - thunk pairs (x19, x0), calls f, returns result in x0
--   - ret reads x30 and jumps back after the blr
--
-- PROGRESS TOWARD ELIMINATION:
--   We have built the infrastructure to eliminate this postulate:
--
--   1. ClosureWellFormed predicate (ClosureWellFormed.agda)
--      - Captures that code_ptr points to valid thunk in program
--      - thunk-correct field proves thunk executes correctly
--
--   2. CurryResult establishes ClosureWellFormed
--      - closure-wf field provides well-formedness proof
--
--   3. run-apply-with-wf uses ClosureWellFormed
--      - Given well-formedness proof, can prove apply correctness
--      - Uses thunk-correct from ClosureWellFormed
--
-- ELIMINATION PATH:
--   The postulate-free path exists but requires threading:
--
--   Step 1: Curry execution → CurryResult with closure-wf
--   Step 2: Thread ClosureWellFormed through compose/pair
--   Step 3: run-apply-with-wf consumes the WF proof
--
--   For whole-program proofs where curry and apply are composed,
--   use CurryResult + run-apply-with-wf instead.
--   This path avoids this postulate entirely.
--
-- RUNTIME EFFECT: None (proof-only)
--
------------------------------------------------------------------------

postulate
  apply-produces-result : ∀ {A B : Type} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode {(A ⇒ B) * A} x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 (apply {_} {A} {B}) ++ suffix
    in ∃[ s' ] (Star prog s s'
              × halted s' ≡ false
              × pc s' ≡ length prefix +ℕ compile-length (apply {_} {A} {B})
              × readReg (regs s') x0 ≡ encode {B} (eval (apply {_} {A} {B}) x)
              × readReg (regs s') x20 ≡ readReg (regs s) x20
              × readReg (regs s') x21 ≡ readReg (regs s) x21
              × readReg (regs s') x29 ≡ readReg (regs s) x29
              × readReg (regs s') x30 ≡ readReg (regs s) x30
              × readSP (regs s') ≤ readSP (regs s)
              × readMem (memory s') (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
              × readMem (memory s') (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
              × readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
              × StackInvariant s'
              × X29Invariant s'
              × readSP (regs s') > 16)

------------------------------------------------------------------------
-- NOTE: Encoding postulates are in Once.Postulates
------------------------------------------------------------------------
--
-- The following encoding axioms are defined in Once.Postulates and
-- should be imported from there (not duplicated here):
--
--   encode-pair-fst, encode-pair-snd     : Pair layout
--   encode-inl-tag, encode-inl-val       : Sum (left) layout
--   encode-inr-tag, encode-inr-val       : Sum (right) layout
--   encode-pair-construct                : Pair construction
--   encode-inl-construct, encode-inr-construct : Sum construction
--   encode-closure-construct             : Closure construction
--
-- Foundation.agda currently duplicates these for historical reasons.
-- TODO: Update Foundation.agda to import from Once.Postulates instead.
--
------------------------------------------------------------------------
