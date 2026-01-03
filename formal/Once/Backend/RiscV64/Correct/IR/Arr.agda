{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Arr
--
-- Correctness proof for the Arr IR construct.
-- Follows modular extraction pattern from X86 backend.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Arr where

open import Size
open import Data.Bool using (Bool; false)
open import Data.Nat using (_≤_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym; subst)

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates
  using (encode)

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.StarBase
  using (run-arr-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Arr Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful arr runner: input address = output address (Eff ≅ Closure)
run-arr-star-s : ∀ {i : Size} {A B : Type} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  encode {A ⇒ B} x ≡ addr-in →
  StackDepth (arr {i} {A} {B}) ≤ readReg (regs s) sp →
  let prog = prefix ++ compile-riscv (arr {i} {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultS (arr {i} {A} {B}) prog s s' addr-in (length prefix)
run-arr-star-s {i} {A} {B} prefix suffix addr-in x s h-false pc-eq a0-eq enc-eq sp-bound =
  let x-typed : ⟦ A ⇒ B ⟧
      x-typed = x
      (s' , res) = run-arr-star {i} {A} {B} prefix suffix x-typed s h-false pc-eq (trans a0-eq (sym enc-eq))
      prog = prefix ++ compile-riscv (arr {i} {A} {B}) ++ suffix
      res-s = convert-to-stateful (arr {i} {A} {B}) prog s s' x-typed (length prefix) res
  in s' , subst (λ addr → IRStarResultS (arr {i} {A} {B}) prog s s' addr (length prefix)) enc-eq res-s
