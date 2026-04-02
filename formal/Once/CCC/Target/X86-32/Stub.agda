-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Stub
--
-- x86-32 (IA-32) target portability demonstration.
--
-- This module demonstrates that the Machine/ modules are truly
-- arch-independent by showing they can be instantiated with the
-- concrete FrameSemantics for x86-32.
--
-- Key differences from X86-64:
--   - 32-bit registers (eax, ebx, etc. instead of rax, rbx)
--   - 4-byte word size instead of 8-byte
--   - Different calling conventions (cdecl, stdcall, fastcall)
--   - Fewer registers available
--
-- STATUS: COMPLETE
--   ✓ Syntax.agda: x86-32 registers and instructions
--   ✓ Types.agda: Type slot calculations
--   ✓ StackGrowth.agda: Stack growth implementation
--   ✓ Layout.agda: Memory layout
--   ✓ FrameInstantiation.agda: FrameSemantics instance
--   ✓ RuntimeContract.agda: Runtime contract
--   ✓ AbstractToX86-32.agda: Abstract trace to x86-32 instructions
--   ✓ DirectSimulation.agda: Simulation proofs
--   ✓ Correct.agda: Correctness theorem
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Stub where

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc)
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.IR using (IR; AllocMode)
open import Once.CCC.Eval using (PrimSem)

------------------------------------------------------------------------
-- Concrete FrameSemantics for x86-32
--
-- x86-32 uses:
--   - esp: stack pointer, grows downward
--   - ebp: frame pointer
--   - Slots grow upward from frame base (same as x86-64)
--   - 4-byte word size (vs 8 bytes for x86-64)
------------------------------------------------------------------------

open import Once.CCC.Target.X86-32.FrameInstantiation
  using (x86-32-frame-semantics)

X86-32-FrameSemantics : FrameSemantics
X86-32-FrameSemantics = x86-32-frame-semantics

------------------------------------------------------------------------
-- Instantiate Machine types with X86-32 FrameSemantics
--
-- This demonstrates the Machine/ types are portable.
------------------------------------------------------------------------

open import Once.CCC.Machine.SMCore
  using (ValueLocation; LocState; halted; regs; readReg)

-- Instantiate types for our FrameSemantics
X86-32-ValueLocation : Set
X86-32-ValueLocation = ValueLocation X86-32-FrameSemantics

X86-32-LocState : Set
X86-32-LocState = LocState X86-32-FrameSemantics

-- Import allocation state (also parameterized)
open import Once.CCC.Machine.Allocation
  using (AllocState; next-slot; current-frame; frame-capacity)

X86-32-AllocState : Set
X86-32-AllocState = AllocState {X86-32-FrameSemantics}

------------------------------------------------------------------------
-- Instantiate Dispatcher with X86-32 FrameSemantics
------------------------------------------------------------------------

open import Once.CCC.Machine.Dispatcher
  using (module Dispatcher; module PrimContract)

-- Example: instantiate PrimContract for X86-32
module X86-32-PrimContract (pb : ℕ) (ps : PrimSem) =
  PrimContract {X86-32-FrameSemantics} pb ps

------------------------------------------------------------------------
-- PORTABILITY VERIFIED
--
-- The fact that this module compiles proves:
--   1. SMCore types work with any FrameSemantics
--   2. Allocation works with any FrameSemantics
--   3. PrimContract works with any FrameSemantics
--   4. The Dispatcher can be instantiated for any FrameSemantics
--
-- The Machine/ modules are truly architecture-independent!
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Re-export target-specific modules for convenience
------------------------------------------------------------------------

-- Syntax
open import Once.CCC.Target.X86-32.Syntax public
  using (Reg; Instr; Program)

-- Types
open import Once.CCC.Target.X86-32.Types public
  using (Type; ⟦_⟧; stack-type-slots; heap-type-slots)

-- Layout
open import Once.CCC.Target.X86-32.Layout public
  using (word-size; x86-32-layout; slot-addr; StackPointer)

-- Code generation
open import Once.CCC.Target.X86-32.AbstractToX86-32 public
  using (compile-abstract; compile-trace)