{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Unfold
--
-- Correctness proof for the Unfold IR construct.
-- Follows modular extraction pattern from X86 backend.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Unfold where

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
  using (run-unfold-star; convert-to-stateful; IRStarResultS)

------------------------------------------------------------------------
-- Unfold Runner (Stateful)
------------------------------------------------------------------------

-- | Stateful unfold runner: input address = output address (Fix ≅ F)
run-unfold-star-s : ∀ {i F} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  encode x ≡ addr-in →
  StackDepth (unfold {i} {F}) ≤ readReg (regs s) sp →
  let prog = prefix ++ compile-riscv (unfold {i} {F}) ++ suffix
  in ∃[ s' ] IRStarResultS (unfold {i} {F}) prog s s' addr-in (length prefix)
run-unfold-star-s {i} {F} prefix suffix addr-in x s h-false pc-eq a0-eq enc-eq sp-bound =
  let (s' , res) = run-unfold-star {i} {F} prefix suffix x s h-false pc-eq (trans a0-eq (sym enc-eq))
      prog = prefix ++ compile-riscv (unfold {i} {F}) ++ suffix
      res-s = convert-to-stateful (unfold {i} {F}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (unfold {i} {F}) prog s s' addr (length prefix)) enc-eq res-s
