------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Id
--
-- Correctness proof for the Id (identity) IR construct.
-- Follows RISC-V modular extraction pattern.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Id where

open import Data.Nat using (_>_)
open import Once.Backend.X86.Correct.Foundation
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StarBase
  using (run-id-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Id Runner (Stateful)
------------------------------------------------------------------------

-- | Run id: just returns input address unchanged
run-id-star-s : ∀ {A : Type} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode x ≡ addr-in →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
  in ∃[ s' ] IRStarResultS (id {A}) prog s s' addr-in (length prefix)
run-id-star-s {A} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-id-star {A} prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (id {A}) ++ suffix
      res-s = convert-to-stateful (id {A}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (id {A}) prog s s' addr (length prefix)) enc-eq res-s
