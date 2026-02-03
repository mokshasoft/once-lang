------------------------------------------------------------------------
-- Once.Backend.X86.Correct.RecDispatcher
--
-- Size-bounded recursive dispatcher type for x86 IR proofs.
-- This module instantiates Common.IRDispatcher.RecDispatcherType with
-- x86-specific types, providing RecDispatcher for all x86 IR modules.
--
-- The dispatcher represents the recursive function that IR implementations
-- receive to make recursive calls on sub-terms of strictly smaller size.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.RecDispatcher where

-- Import consolidated Foundation module (provides State, halted, pc, regs, memory, etc.)
open import Once.Backend.X86.Correct.Foundation
open import Once.Backend.X86.Semantics using (Memory)

open import Once.Backend.X86.Layout using (StackPointer)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (StackCapacity; ir-stack-requirement)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV; ClosureWFOutput; no-closure)

-- Import Common dispatcher infrastructure (parameterized with X86ContractInterface)
open import Once.Backend.X86.Correct.PrimContract using (X86ContractInterface)
open import Once.Backend.Common.IRDispatcher X86ContractInterface

-- ir-size is now re-exported from Foundation (parameterized with X86ContractInterface)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- RecDispatcher: Instantiate Common.RecDispatcherType with x86 types
--
-- For any IR smaller than bound, produce an execution result.
-- This is the type of the `rec` function passed to IR implementation modules.
--
-- Usage in MutualIR.agda dispatcher:
--   run-ir-star-at-offset-v (⟨ f , g ⟩) ... (acc rs) =
--     let rec : RecDispatcher (ir-size ⟨ f , g ⟩)
--         rec ir' lt ... = run-ir-star-at-offset-v ir' ... (rs lt)
--     in Pair.run-pair-star-v ... rec ...
------------------------------------------------------------------------

-- x86 input register reader: arguments are passed in rdi
private
  x86-readInputReg : State → ℕ
  x86-readInputReg s = readReg (regs s) rdi

-- Instantiate RecDispatcherType with x86-specific types
open RecDispatcherType
  {State} {Memory} {Program} {StackPointer}
  halted
  pc
  x86-readInputReg
  memory
  ValidAt
  StackInvariant
  StackCapacity
  RbpInvariant
  compile-x86
  _++_
  length
  ir-stack-requirement
  IRStarResultV
  public

------------------------------------------------------------------------
-- RecDispatcherWithWF: Extended dispatcher with closure context
--
-- Like RecDispatcher, but also takes a ClosureWFOutput as input.
-- This enables threading closure well-formedness from curry through
-- compose to apply, eliminating postulates in apply.
--
-- Usage: Compose passes f's ir-closure-wf to g's rec call.
--        Other cases (pair, case) pass no-closure.
------------------------------------------------------------------------

RecDispatcherWithWF : ℕ → Set₁
RecDispatcherWithWF bound =
  ∀ {A B} (ir : IR A B) → ir-size ir < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (x86-readInputReg s) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement ir) →
  RbpInvariant s →
  ClosureWFOutput (prefix ++ compile-x86 ir ++ suffix) s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix)

-- | Convert RecDispatcherWithWF to RecDispatcher by passing no-closure
unwrap-rec : ∀ {bound} → RecDispatcherWithWF bound → RecDispatcher bound
unwrap-rec rec ir lt prefix suffix caller-sp x s h-eq pc-eq v-in si sc ri =
  rec ir lt prefix suffix caller-sp x s h-eq pc-eq v-in si sc ri no-closure
