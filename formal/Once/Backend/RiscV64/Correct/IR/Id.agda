{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Id
--
-- Correctness proof for the Id (identity) IR construct.
-- Follows modular extraction pattern from X86 backend.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Id where

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
  using (run-id-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Id Runner (Stateful)
------------------------------------------------------------------------

-- | Run id: just returns input address unchanged
run-id-star-s : ∀ {i : Size} {A : Type} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  encode x ≡ addr-in →
  StackDepth (id {i} {A}) ≤ readReg (regs s) sp →
  let prog = prefix ++ compile-riscv (id {i} {A}) ++ suffix
  in ∃[ s' ] IRStarResultS (id {i} {A}) prog s s' addr-in (length prefix)
run-id-star-s {i} {A} prefix suffix addr-in x s h-false pc-eq a0-eq enc-eq sp-bound =
  let (s' , res) = run-id-star {i} {A} prefix suffix x s h-false pc-eq (trans a0-eq (sym enc-eq))
      prog = prefix ++ compile-riscv (id {i} {A}) ++ suffix
      res-s = convert-to-stateful (id {i} {A}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (id {i} {A}) prog s s' addr (length prefix)) enc-eq res-s
