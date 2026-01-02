{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Fold
--
-- Correctness proof for the Fold IR construct.
-- Follows RISC-V modular extraction pattern.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Fold where

open import Size
open import Data.Nat using (_>_)
open import Once.Backend.X86.Correct.Foundation
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StarBase
  using (run-fold-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Fold Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful fold runner: input address = output address (Fix ≅ A)
run-fold-star-s : ∀ {i F} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode x ≡ addr-in →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fold {i} {F}) ++ suffix
  in ∃[ s' ] IRStarResultS (fold {i} {F}) prog s s' addr-in (length prefix)
run-fold-star-s {i} {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-fold-star {i} {F} prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (fold {i} {F}) ++ suffix
      res-s = convert-to-stateful (fold {i} {F}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (fold {i} {F}) prog s s' addr (length prefix)) enc-eq res-s
