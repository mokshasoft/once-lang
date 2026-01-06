{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Fold
--
-- Correctness proof for the Fold IR construct.
-- Follows modular extraction pattern from X86 backend.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Fold where

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
  using (run-fold-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Fold Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful fold runner: input address = output address (Fix ≅ F)
run-fold-star-s : ∀ {i F} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  encode x ≡ addr-in →
  StackDepth (fold {i} {F}) ≤ readReg (regs s) sp →
  let prog = prefix ++ compile-riscv (fold {i} {F}) ++ suffix
  in ∃[ s' ] IRStarResultS (fold {i} {F}) prog s s' addr-in (length prefix)
run-fold-star-s {i} {F} prefix suffix addr-in x s h-false pc-eq a0-eq enc-eq sp-bound =
  let (s' , res) = run-fold-star {i} {F} prefix suffix x s h-false pc-eq (trans a0-eq (sym enc-eq))
      prog = prefix ++ compile-riscv (fold {i} {F}) ++ suffix
      res-s = convert-to-stateful (fold {i} {F}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (fold {i} {F}) prog s s' addr (length prefix)) enc-eq res-s
