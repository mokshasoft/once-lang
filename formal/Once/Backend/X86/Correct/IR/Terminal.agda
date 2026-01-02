{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Terminal
--
-- Correctness proof for the Terminal IR construct.
-- Follows RISC-V modular extraction pattern.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Terminal where

open import Size
open import Data.Nat using (_>_)
open import Once.Backend.X86.Correct.Foundation
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StarBase
  using (run-terminal-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Terminal Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful terminal runner: output address = 0 (unit encoding)
run-terminal-star-s : ∀ {i : Size} {A : Type} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (terminal {i} {A}) ++ suffix
  in ∃[ s' ] IRStarResultS (terminal {i} {A}) prog s s' 0 (length prefix)
run-terminal-star-s {i} {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-terminal-star {i} {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv
  in s' , convert-to-stateful (terminal {i} {A}) _ s s' x _ res
