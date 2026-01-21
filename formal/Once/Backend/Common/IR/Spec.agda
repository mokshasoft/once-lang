------------------------------------------------------------------------
-- Once.Backend.Common.IR.Spec
--
-- Architecture-independent correctness specifications for IR.
--
-- This module defines WHAT correctness means for each IR constructor,
-- parameterized by architecture-specific details.
--
-- DESIGN PRINCIPLE: These types are extracted from X86's working proofs,
-- not invented abstractly. They match what X86 actually provides.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold)
open import Once.Type using (Type; _*_; _⇒_; Eff) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode)

module Once.Backend.Common.IR.Spec where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Abstract Machine Interface
--
-- Core types and operations each architecture provides.
-- Derived from X86's working implementation, designed to generalize
-- to AArch64 and RISC-V.
------------------------------------------------------------------------

record MachineInterface : Set₁ where
  field
    -- Core types
    State : Set
    Program : Set
    Word : Set
    Memory : Set

    -- State accessors
    pc : State → ℕ
    halted : State → Bool
    memory : State → Memory

    -- Register accessors (architecture names the registers)
    -- Input register: where function arguments arrive (rdi / x0 / a0)
    input-value : State → Word
    -- Output register: where results are placed (rax / x0 / a0)
    output-value : State → Word

    -- Memory operations
    readMem : Memory → Word → Maybe Word

    -- Program operations
    program-length : Program → ℕ

    -- Execution
    step : Program → State → Maybe State

------------------------------------------------------------------------
-- Invariant Interface
--
-- Architecture-specific invariants that must be maintained.
-- Extracted from X86's StackInvariant, RbpInvariant, etc.
------------------------------------------------------------------------

record InvariantInterface (M : MachineInterface) : Set₁ where
  open MachineInterface M

  field
    -- Stack invariant (frame pointer discipline)
    StackInvariant : State → Set

    -- Stack capacity (enough space for N slots)
    StackCapacity : State → ℕ → Set

    -- Frame pointer invariant (rbp chain valid, etc.)
    FramePtrInvariant : State → Set

    -- Saved registers preserved between states
    SavedRegsPreserved : State → State → Set

    -- RSP/SP delta tracking (for capacity threading)
    -- Returns how much stack pointer changes after executing IR
    rsp-delta-slots : State → State → ℕ → Set

    -- Memory regions
    InStack : Word → Set
    InHeap : Word → Set
    InCode : Word → Set

    -- Memory preservation predicates
    HeapPreserved : State → State → Set
    CodePreserved : State → State → Set
    FramePreserved : State → State → Set

------------------------------------------------------------------------
-- Validity Interface
--
-- ValidAt predicate: "value v is correctly represented at addr in memory"
------------------------------------------------------------------------

record ValidityInterface (M : MachineInterface) (Inv : InvariantInterface M) : Set₁ where
  open MachineInterface M
  open InvariantInterface Inv

  field
    -- Core validity predicate
    ValidAt : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set

    -- Validity preserved under heap-preserving operations
    valid-preserved-heap : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m₁ m₂ : Memory} →
      ValidAt v addr m₁ →
      (∀ a → InHeap a → readMem m₂ a ≡ readMem m₁ a) →
      ValidAt v addr m₂

------------------------------------------------------------------------
-- Code Generation Interface
------------------------------------------------------------------------

record CodeGenInterface (M : MachineInterface) : Set₁ where
  open MachineInterface M

  field
    -- Compile IR to program
    compile : ∀ {A B} → IR A B → Program

    -- Length of compiled code
    compile-length : ∀ {A B} → IR A B → ℕ

    -- Stack requirements
    ir-stack-requirement : ∀ {A B} → IR A B → ℕ
    ir-output-capacity : ∀ {A B} → IR A B → ℕ
    ir-rsp-delta : ∀ {A B} → IR A B → ℕ

------------------------------------------------------------------------
-- IRCorrectness: The Core Specification
--
-- This matches X86's IRStarResultV structure exactly.
-- Architecture provides this record; Common defines what fields mean.
--
-- Note: Star is provided as a parameter rather than via an interface,
-- since each architecture's Star has slightly different constructor
-- signatures (X86's step* requires halted proof, etc.)
------------------------------------------------------------------------

module IRSpecs
    (M : MachineInterface)
    (Inv : InvariantInterface M)
    (Val : ValidityInterface M Inv)
    (CG : CodeGenInterface M)
    (Star : MachineInterface.Program M → MachineInterface.State M → MachineInterface.State M → Set)
    where

  open MachineInterface M
  open InvariantInterface Inv
  open ValidityInterface Val
  open CodeGenInterface CG

  -- Preconditions for IR execution
  -- Matches X86's run-*-star-vv preconditions exactly
  record Preconditions {A : Type} (s : State) (x : ⟦ A ⟧)
                       (prefix : Program) (cap-needed : ℕ) : Set₁ where
    field
      pre-halted : halted s ≡ false
      pre-pc : pc s ≡ program-length prefix
      pre-input-valid : ValidAt x (input-value s) (memory s)
      pre-stack-inv : StackInvariant s
      pre-capacity : StackCapacity s cap-needed
      pre-frame-inv : FramePtrInvariant s

  -- Core correctness result
  -- Matches X86's IRStarResultV structure
  record IRCorrectness {A B : Type} (ir : IR A B)
      (prog : Program) (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
    field
      -- Execution
      exec-star : Star prog s s'
      exec-halted : halted s' ≡ false
      exec-pc : pc s' ≡ offset + compile-length ir

      -- Output validity (THE key correctness property)
      exec-output-valid : ValidAt (eval ir x) (output-value s') (memory s')

      -- Register/state preservation
      exec-saved-regs : SavedRegsPreserved s s'

      -- Memory preservation
      exec-heap-preserved : HeapPreserved s s'
      exec-code-preserved : CodePreserved s s'
      exec-frame-preserved : FramePreserved s s'

      -- Invariants maintained
      exec-stack-inv : StackInvariant s'
      exec-capacity : StackCapacity s' (ir-output-capacity ir)
      exec-frame-inv : FramePtrInvariant s'

  ------------------------------------------------------------------------
  -- Phase Specifications for Composite IR
  --
  -- These match X86's phase result records.
  ------------------------------------------------------------------------

  module PairSpecs {A B C : Type} (f : IR C A) (g : IR C B) where

    -- After setup: registers saved, ready for f
    record SetupPost (s s₁ : State) (x : ⟦ C ⟧) : Set₁ where
      field
        setup-halted : halted s₁ ≡ false
        setup-stack-inv : StackInvariant s₁
        setup-input-valid : ValidAt x (input-value s₁) (memory s₁)
        setup-capacity : StackCapacity s₁ (ir-stack-requirement f)
        setup-frame-inv : FramePtrInvariant s₁

    -- After middle: f's result stored, ready for g
    record MiddlePost (s₁ s₂ s₃ : State) (x : ⟦ C ⟧) (fx : ⟦ A ⟧) : Set₁ where
      field
        middle-halted : halted s₃ ≡ false
        middle-stack-inv : StackInvariant s₃
        middle-input-valid : ValidAt x (input-value s₃) (memory s₃)
        middle-capacity : StackCapacity s₃ (ir-stack-requirement g)
        middle-frame-inv : FramePtrInvariant s₃
        -- f's result is preserved somewhere for later pair construction

    -- After cleanup: pair constructed
    record CleanupPost (s s₅ : State) (x : ⟦ C ⟧)
                       (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) : Set₁ where
      field
        cleanup-halted : halted s₅ ≡ false
        cleanup-stack-inv : StackInvariant s₅
        cleanup-capacity : StackCapacity s₅ (ir-output-capacity ⟨ f , g ⟩)
        cleanup-output-valid : ValidAt {A * B} (fx , gx) (output-value s₅) (memory s₅)
        cleanup-saved-regs : SavedRegsPreserved s s₅
        cleanup-frame-inv : FramePtrInvariant s₅

  module CurrySpecs {A B C : Type} (f : IR (A * B) C) where

    record SetupPost (s s₁ : State) (x : ⟦ A ⟧) : Set₁ where
      field
        setup-halted : halted s₁ ≡ false
        setup-stack-inv : StackInvariant s₁
        setup-capacity : StackCapacity s₁ (ir-output-capacity (curry f))
        setup-output-valid : ValidAt {B ⇒ C} (eval (curry f) x) (output-value s₁) (memory s₁)
        setup-saved-regs : SavedRegsPreserved s s₁
        setup-frame-inv : FramePtrInvariant s₁

  module CaseSpecs {A B C : Type} (f : IR A C) (g : IR B C) where

    record DispatchLeftPost (s s₁ : State) (a : ⟦ A ⟧) : Set where
      field
        dispatch-halted : halted s₁ ≡ false
        dispatch-stack-inv : StackInvariant s₁
        dispatch-input-valid : ValidAt a (input-value s₁) (memory s₁)
        dispatch-capacity : StackCapacity s₁ (ir-stack-requirement f)

    record DispatchRightPost (s s₁ : State) (b : ⟦ B ⟧) : Set where
      field
        dispatch-halted : halted s₁ ≡ false
        dispatch-stack-inv : StackInvariant s₁
        dispatch-input-valid : ValidAt b (input-value s₁) (memory s₁)
        dispatch-capacity : StackCapacity s₁ (ir-stack-requirement g)

------------------------------------------------------------------------
-- Summary
--
-- This module defines architecture-independent types that MATCH what
-- X86 actually provides:
--
--   - Preconditions: includes input ValidAt (X86 has this!)
--   - IRCorrectness: matches IRStarResultV fields
--   - Phase specs: match X86's phase result records
--
-- Key additions from original design:
--   - input-value in MachineInterface (rdi / x0 / a0)
--   - FramePtrInvariant in InvariantInterface (RbpInvariant)
--   - pre-input-valid in Preconditions
--   - StarInterface (each arch provides Star)
------------------------------------------------------------------------
