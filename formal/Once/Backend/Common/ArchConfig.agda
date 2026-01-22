------------------------------------------------------------------------
-- Once.Backend.Common.ArchConfig
--
-- Architecture configuration record for parameterizing correctness proofs.
-- This captures the architecture-specific types and operations needed by
-- the generic dispatcher and proof infrastructure.
--
-- Design principles:
-- 1. Minimal interface - only what's needed for dispatcher abstraction
-- 2. No constraints on implementation - architectures have full flexibility
-- 3. No semantic assumptions - purely structural/syntactic abstractions
------------------------------------------------------------------------

module Once.Backend.Common.ArchConfig where

open import Once.Type using (Type)
open import Once.IR using (IR)
open import Once.Semantics using (⟦_⟧)

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level using (Level; suc; _⊔_)

------------------------------------------------------------------------
-- Architecture Configuration Record
--
-- This record captures the architecture-specific types needed for the
-- generic dispatcher. Architectures instantiate this with their concrete
-- types (e.g., x86 State, x86 Program, etc.)
------------------------------------------------------------------------

record ArchConfig : Set₁ where
  field
    -- Core execution types
    State   : Set        -- Machine state (registers, memory, pc, flags)
    Program : Set        -- Executable program (list of instructions)
    Instr   : Set        -- Individual instruction type

    -- Program structure
    _++ₚ_   : Program → Program → Program  -- Program concatenation
    []ₚ     : Program                       -- Empty program
    lengthₚ : Program → ℕ                   -- Program length

    -- State inspection
    halted : State → Bool   -- Is the machine halted?
    pc     : State → ℕ      -- Program counter

    -- Code generation (architecture-specific compilation)
    compile : ∀ {A B} → IR A B → Program

------------------------------------------------------------------------
-- Proof Configuration Record
--
-- This record captures the architecture-specific proof types needed for
-- correctness proofs. It's parameterized by ArchConfig to ensure
-- consistent types.
------------------------------------------------------------------------

record ProofConfig (arch : ArchConfig) : Set₁ where
  open ArchConfig arch

  field
    -- Memory region type (for tracking where values are stored)
    StackPointer : Set

    -- Validity predicate: "value x is validly represented at address a in memory m"
    -- This is the key abstraction replacing encode postulates
    ValidAt : ∀ {A : Type} → ⟦ A ⟧ → ℕ → State → Set

    -- Stack invariants (architecture-specific stack discipline)
    StackInvariant : State → Set

    -- Stack capacity (enough space for IR execution)
    -- Takes state and number of slots needed
    StackCapacity : State → ℕ → Set

    -- Frame pointer invariant (for proper stack frame management)
    RbpInvariant : State → Set

    -- Input register (where arguments are passed)
    -- Returns the value in the input register
    readInputReg : State → ℕ

------------------------------------------------------------------------
-- Star Result Record
--
-- Generic result type for IR execution proofs. Architectures instantiate
-- this with their specific fields, but the structure is common.
------------------------------------------------------------------------

record IRStarResultConfig (arch : ArchConfig) (proof : ProofConfig arch) : Set₂ where
  open ArchConfig arch
  open ProofConfig proof

  field
    -- The result record type for a given IR, program, states, input, and offset
    IRStarResultV : ∀ {A B : Type} → IR A B → Program →
                    State → State → ⟦ A ⟧ → ℕ → Set₁

------------------------------------------------------------------------
-- Full Configuration Bundle
--
-- Combines architecture config, proof config, and result config for
-- convenient passing to parameterized modules.
------------------------------------------------------------------------

record FullConfig : Set₂ where
  field
    arch   : ArchConfig
    proof  : ProofConfig arch
    result : IRStarResultConfig arch proof

  open ArchConfig arch public
  open ProofConfig proof public
  open IRStarResultConfig result public
