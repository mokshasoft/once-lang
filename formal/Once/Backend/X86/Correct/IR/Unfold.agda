------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Unfold
--
-- Correctness proof for the Unfold IR construct.
-- Follows RISC-V modular extraction pattern.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Unfold where

open import Data.Nat using (_>_)
open import Once.Backend.X86.Correct.Foundation
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StarBase
  using (run-unfold-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Unfold Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful unfold runner: input address = output address (Fix ≅ A)
run-unfold-star-s : ∀ {F} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode x ≡ addr-in →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
  in ∃[ s' ] IRStarResultS (unfold {F}) prog s s' addr-in (length prefix)
run-unfold-star-s {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-unfold-star {F} prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
      res-s = convert-to-stateful (unfold {F}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (unfold {F}) prog s s' addr (length prefix)) enc-eq res-s
