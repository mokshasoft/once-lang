------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Arr
--
-- Correctness proof for the Arr IR construct.
-- Follows RISC-V modular extraction pattern.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Arr where

open import Data.Nat using (_>_)
open import Once.Backend.X86.Correct.Foundation
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StarBase
  using (run-arr-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Arr Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful arr runner: input address = output address (Eff ≅ Closure)
run-arr-star-s : ∀ {A B : Type} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode {A ⇒ B} x ≡ addr-in →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultS (arr {A} {B}) prog s s' addr-in (length prefix)
run-arr-star-s {A} {B} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let x-typed : ⟦ A ⇒ B ⟧
      x-typed = x
      (s' , res) = run-arr-star {A} {B} prefix suffix x-typed s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
      res-s = convert-to-stateful (arr {A} {B}) prog s s' x-typed (length prefix) res
  in s' , subst (λ addr → IRStarResultS (arr {A} {B}) prog s s' addr (length prefix)) enc-eq res-s
