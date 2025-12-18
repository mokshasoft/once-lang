------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Simulation
--
-- Simulation relations for CompCert-style correctness proofs.
-- Defines what it means for x86 state to correctly simulate IR evaluation.
--
-- Level 1 - depends on Star, StackInvariant
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Simulation where

open import Once.Type
open import Once.IR
open import Once.Semantics using (⟦_⟧; eval)

open import Once.Backend.X86.Syntax using (Program; Reg; rax; rdi; rsp)
open import Once.Backend.X86.Semantics using (State; readReg)
open Once.Backend.X86.Semantics.State

open import Once.Backend.X86.CodeGen using (compile-x86)

open import Once.Backend.X86.Correct.Star using (Star)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant)

open import Once.Postulates using (encode)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Simulation Pre-conditions
------------------------------------------------------------------------

-- | Simulates: x86 state correctly represents IR input
--
-- This captures the pre-conditions needed before executing compiled IR:
-- - Input value is correctly encoded in rdi
-- - Execution hasn't halted yet
-- - Stack invariant holds (for pair/curry stack management)
-- - Sufficient stack space (rsp > 16)

record Simulates {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) : Set where
  field
    -- Input is correctly encoded in rdi
    input-encoded : readReg (regs s) rdi ≡ encode x
    -- Execution hasn't halted yet
    not-halted : halted s ≡ false
    -- Stack invariant holds
    stack-inv : StackInvariant s
    -- Sufficient stack space
    rsp-valid : readReg (regs s) rsp > 16

open Simulates public

------------------------------------------------------------------------
-- Result Post-conditions
------------------------------------------------------------------------

-- | HasResult: x86 state correctly represents IR output
--
-- This captures the post-conditions after executing compiled IR:
-- - Output value is correctly encoded in rax
-- - Execution has halted (reached end of code)

record HasResult {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) : Set where
  field
    -- Output is correctly encoded in rax
    output-encoded : readReg (regs s) rax ≡ encode (eval ir x)
    -- Execution has halted
    is-halted : halted s ≡ true

open HasResult public

------------------------------------------------------------------------
-- Extended Result (for recursive proofs)
------------------------------------------------------------------------

-- | IntermediateResult: x86 state after executing IR but NOT halted
--
-- For recursive IR (compose, pair, case), we need to chain executions.
-- The intermediate states after sub-IR execution should NOT halt,
-- allowing further execution to continue.

record IntermediateResult {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) : Set where
  field
    -- Output is correctly encoded in rax
    output-encoded : readReg (regs s) rax ≡ encode (eval ir x)
    -- Execution has NOT halted (more to come)
    not-halted : halted s ≡ false
    -- Stack invariant preserved
    stack-inv : StackInvariant s
    -- Stack space still valid
    rsp-valid : readReg (regs s) rsp > 16

open IntermediateResult public renaming
  ( output-encoded to int-output-encoded
  ; not-halted to int-not-halted
  ; stack-inv to int-stack-inv
  ; rsp-valid to int-rsp-valid
  )

------------------------------------------------------------------------
-- Helper: construct Simulates from components
------------------------------------------------------------------------

mkSimulates : ∀ {A B : Type} {ir : IR A B} {x : ⟦ A ⟧} {s : State} →
  readReg (regs s) rdi ≡ encode x →
  halted s ≡ false →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  Simulates ir x s
mkSimulates inp h si rsp-v = record
  { input-encoded = inp
  ; not-halted = h
  ; stack-inv = si
  ; rsp-valid = rsp-v
  }

------------------------------------------------------------------------
-- Helper: construct HasResult from components
------------------------------------------------------------------------

mkHasResult : ∀ {A B : Type} {ir : IR A B} {x : ⟦ A ⟧} {s : State} →
  readReg (regs s) rax ≡ encode (eval ir x) →
  halted s ≡ true →
  HasResult ir x s
mkHasResult out h = record
  { output-encoded = out
  ; is-halted = h
  }

------------------------------------------------------------------------
-- Helper: construct IntermediateResult from components
------------------------------------------------------------------------

mkIntermediateResult : ∀ {A B : Type} {ir : IR A B} {x : ⟦ A ⟧} {s : State} →
  readReg (regs s) rax ≡ encode (eval ir x) →
  halted s ≡ false →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  IntermediateResult ir x s
mkIntermediateResult out h si rsp-v = record
  { output-encoded = out
  ; not-halted = h
  ; stack-inv = si
  ; rsp-valid = rsp-v
  }
