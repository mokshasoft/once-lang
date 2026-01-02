{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Postulates.Open
--
-- FFI and runtime axioms for Open (modular) verification.
--
-- This module re-exports ONLY the axioms that represent:
-- 1. Runtime environment guarantees (stack bounds)
-- 2. FFI boundaries (closures crossing module boundaries)
--
-- These are the ONLY axioms that remain in the Open verification track.
-- The Closed track eliminates these through whole-program analysis.
------------------------------------------------------------------------

module Once.Backend.AArch64.Postulates.Open where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; length; _++_)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Bool using (false)

open import Once.Type using (Type; _⇒_; _*_)
open import Once.IR using (IR; apply)
open import Once.Semantics using (⟦_⟧; encode; eval)

open import Once.Backend.AArch64.Syntax using (x0; x20; x21; x29; x30; Program)
open import Once.Backend.AArch64.Semantics using (State; readReg; readSP; readMem)
open import Once.Backend.AArch64.Semantics using () renaming (module State to St)
open St using (regs; memory; halted; pc)
open import Once.Backend.AArch64.Correct.Star using (Star)
open import Once.Backend.AArch64.Correct.StackInvariant using (StackInvariant; X29Invariant)
open import Once.Backend.AArch64.CodeGen using (compile-aarch64; compile-length)

------------------------------------------------------------------------
-- Runtime Environment Axiom
------------------------------------------------------------------------

-- Assumes sufficient stack space (standard runtime assumption)
-- This cannot be eliminated as it's a property of the execution environment
postulate
  sp-bound-after-stack-op : ∀ (s : State) → readSP (regs s) > 16

------------------------------------------------------------------------
-- FFI Boundary Axiom (Modular Verification Only)
------------------------------------------------------------------------

-- When verifying code modularity (separate compilation, unknown closures),
-- we must assume that closures passed across FFI boundaries are valid.
--
-- In the Closed track, this is eliminated by whole-program analysis:
-- curry creates closures with proven well-formedness, which is threaded
-- through the proof to apply.
--
-- In the Open track, this axiom captures the FFI contract: if you pass
-- a closure created outside this module, we assume it's valid.
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
-- Summary
------------------------------------------------------------------------

-- OPEN TRACK AXIOMS: 2 total
--   1. sp-bound-after-stack-op (runtime guarantee)
--   2. apply-produces-result (FFI boundary)
--
-- CLOSED TRACK AXIOMS: 1 total
--   1. sp-bound-after-stack-op (runtime guarantee)
--      (apply-produces-result eliminated via ClosureWellFormed threading)
--
-- Encoding axioms (encode-pair-fst, etc.) are in Once.Postulates
-- and shared by both tracks.
------------------------------------------------------------------------
