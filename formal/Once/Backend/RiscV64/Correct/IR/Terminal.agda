{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Terminal
--
-- Correctness proof for the Terminal IR construct.
-- Follows modular extraction pattern from X86 backend.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Terminal where

open import Size
open import Data.Bool using (Bool; false)
open import Data.Nat using (_≤_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym; subst)

open import Once.Type
open import Once.IRS
open import Once.SemanticsS

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen using (compile-riscv; StackDepth)

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.StarBase
  using (run-terminal-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Terminal Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful terminal runner: output address = 0 (unit encoding)
run-terminal-star-s : ∀ {i : Size} {A : Type} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  StackDepth (terminal {i} {A}) ≤ readReg (regs s) sp →
  let prog = prefix ++ compile-riscv (terminal {i} {A}) ++ suffix
  in ∃[ s' ] IRStarResultS (terminal {i} {A}) prog s s' 0 (length prefix)
run-terminal-star-s {i} {A} prefix suffix x s h-false pc-eq a0-eq sp-bound =
  let (s' , res) = run-terminal-star {i} {A} prefix suffix x s h-false pc-eq a0-eq
  in s' , convert-to-stateful (terminal {i} {A}) _ s s' x _ res
