------------------------------------------------------------------------
-- Once.Backend.X86.Correct.RecDispatcher
--
-- Size-bounded recursive dispatcher type for x86 IR proofs.
-- This module defines RecDispatcher once for all x86 IR implementations
-- (Pair, Compose, Case, Curry) to import.
--
-- The dispatcher represents the recursive function that IR implementations
-- receive to make recursive calls on sub-terms of strictly smaller size.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.RecDispatcher where

-- Import consolidated Foundation module (provides State, halted, pc, regs, memory, etc.)
open import Once.Backend.X86.Correct.Foundation

open import Once.Backend.X86.Layout using (StackPointer)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (StackCapacity; ir-stack-requirement)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV)
open import Once.Backend.X86.Correct.IRSize using (ir-size)

------------------------------------------------------------------------
-- RecDispatcher: Size-bounded recursive dispatcher type
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

RecDispatcher : ℕ → Set₁
RecDispatcher bound =
  ∀ {A B} (ir : IR A B) → ir-size ir < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement ir) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix)
