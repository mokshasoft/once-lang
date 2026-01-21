{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.Common.IR.Spec
--
-- Architecture-independent correctness specifications for IR.
--
-- This module defines WHAT correctness means for each IR constructor,
-- without specifying HOW to prove it (that's architecture-specific).
--
-- Key abstractions:
--   - IRCorrectness: the core correctness predicate
--   - Phase postconditions: what each phase must establish
--
-- These specs are parameterized by a MachineInterface that abstracts
-- over architecture-specific details (registers, state, etc.)
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
-- Each architecture must provide these types and operations.
-- This allows correctness specs to be stated without mentioning
-- specific registers like rax, r14, x0, a0, etc.
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

    -- Abstract "output location" (rax / x0 / a0)
    output-value : State → Word

    -- Memory operations
    readMem : Memory → Word → Maybe Word

    -- Execution
    step : Program → State → Maybe State

------------------------------------------------------------------------
-- Abstract Invariants
--
-- These are architecture-independent concepts that each backend
-- instantiates with its specific register/frame layout.
------------------------------------------------------------------------

record InvariantInterface (M : MachineInterface) : Set₁ where
  open MachineInterface M

  field
    -- Stack invariant (frame pointer discipline)
    StackInvariant : State → Set

    -- Stack capacity (enough space for N slots)
    StackCapacity : State → ℕ → Set

    -- Saved registers preserved between states
    -- (abstracts over which registers: {r14,r15,rbp} vs {x20,x21} vs {s1,s2})
    SavedRegsPreserved : State → State → Set

    -- Memory regions
    InStack : Word → Set
    InHeap : Word → Set
    InCode : Word → Set

    -- Memory preservation predicates
    HeapPreserved : State → State → Set
    CodePreserved : State → State → Set
    FramePreserved : State → State → Set

------------------------------------------------------------------------
-- Abstract Validity
--
-- ValidAt is the core correctness predicate: "value v is correctly
-- represented at address addr in memory m"
--
-- Parameterized by InvariantInterface to access InHeap.
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
-- Star (Reflexive-Transitive Closure)
--
-- Already exists in Common/Star.agda, but we need the type here.
------------------------------------------------------------------------

-- Import from Common.Star or define abstractly
-- For now, we assume it's provided
postulate
  Star : ∀ {M : MachineInterface} →
         MachineInterface.Program M →
         MachineInterface.State M →
         MachineInterface.State M → Set

------------------------------------------------------------------------
-- Code Generation Interface
--
-- What each architecture's code generator must provide.
------------------------------------------------------------------------

record CodeGenInterface (M : MachineInterface) : Set₁ where
  open MachineInterface M

  field
    -- Compile IR to program
    compile : ∀ {A B} → IR A B → Program

    -- Length of compiled code (for PC advancement proofs)
    compile-length : ∀ {A B} → IR A B → ℕ

    -- Stack requirements
    ir-stack-requirement : ∀ {A B} → IR A B → ℕ
    ir-output-capacity : ∀ {A B} → IR A B → ℕ
    ir-rsp-delta : ∀ {A B} → IR A B → ℕ

------------------------------------------------------------------------
-- IRCorrectness: The Core Specification
--
-- This is what it means for IR execution to be correct.
-- Architecture-independent statement; architecture-specific proof.
------------------------------------------------------------------------

module IRSpecs
    (M : MachineInterface)
    (Inv : InvariantInterface M)
    (Val : ValidityInterface M Inv)
    (CG : CodeGenInterface M) where

  open MachineInterface M
  open InvariantInterface Inv
  open ValidityInterface Val
  open CodeGenInterface CG

  -- Preconditions for IR execution
  record Preconditions (s : State) (x-addr : Word) (cap-needed : ℕ) : Set where
    field
      pre-halted : halted s ≡ false
      pre-stack-inv : StackInvariant s
      pre-capacity : StackCapacity s cap-needed

  -- Core correctness: executing IR produces valid output
  record IRCorrectness {A B : Type} (ir : IR A B)
      (prog : Program) (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
    field
      -- Execution happened
      exec-star : Star {M} prog s s'

      -- Machine state after execution
      exec-halted : halted s' ≡ false
      exec-pc : pc s' ≡ offset + compile-length ir

      -- Output is valid (the key correctness property!)
      exec-output-valid : ValidAt (eval ir x) (output-value s') (memory s')

      -- Invariants maintained
      exec-stack-inv : StackInvariant s'
      exec-capacity : StackCapacity s' (ir-output-capacity ir)

      -- Registers/memory preserved
      exec-saved-regs : SavedRegsPreserved s s'
      exec-heap-preserved : HeapPreserved s s'
      exec-code-preserved : CodePreserved s s'
      exec-frame-preserved : FramePreserved s s'

  ------------------------------------------------------------------------
  -- Phase Specifications
  --
  -- For composite IR (pair, curry, case), execution is split into phases.
  -- Each phase has pre/post conditions. The combining logic is shared;
  -- the phase proofs are architecture-specific.
  ------------------------------------------------------------------------

  -- Pair phases: setup → f → middle → g → cleanup
  module PairSpecs {A B C : Type} (f : IR C A) (g : IR C B) where

    -- After setup: registers saved, pair space allocated, ready for f
    record SetupPost (s s₁ : State) (x : ⟦ C ⟧) : Set where
      field
        setup-halted : halted s₁ ≡ false
        setup-stack-inv : StackInvariant s₁
        -- f can now execute with input x
        setup-ready-for-f : StackCapacity s₁ (ir-stack-requirement f)

    -- After middle: f's result stored, ready for g
    record MiddlePost (s₁ s₂ s₃ : State) (x : ⟦ C ⟧) (fx : ⟦ A ⟧) : Set where
      field
        middle-halted : halted s₃ ≡ false
        middle-stack-inv : StackInvariant s₃
        -- f's result is stored somewhere (architecture tracks where)
        -- g can now execute with input x
        middle-ready-for-g : StackCapacity s₃ (ir-stack-requirement g)

    -- After cleanup: pair constructed, result valid
    record CleanupPost (s s₁ s₃ s₄ s₅ : State) (x : ⟦ C ⟧)
                       (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) : Set₁ where
      field
        cleanup-halted : halted s₅ ≡ false
        cleanup-stack-inv : StackInvariant s₅
        cleanup-capacity : StackCapacity s₅ (ir-output-capacity ⟨ f , g ⟩)
        -- The key result: output is valid pair
        cleanup-output-valid : ValidAt {A * B} (fx , gx) (output-value s₅) (memory s₅)
        -- Saved registers restored
        cleanup-saved-regs : SavedRegsPreserved s s₅

  -- Curry phases: setup (create closure, skip thunk)
  module CurrySpecs {A B C : Type} (f : IR (A * B) C) where

    -- After setup: closure created, thunk skipped
    record SetupPost (s s₁ : State) (x : ⟦ A ⟧) : Set₁ where
      field
        setup-halted : halted s₁ ≡ false
        setup-stack-inv : StackInvariant s₁
        setup-capacity : StackCapacity s₁ (ir-output-capacity (curry f))
        -- The key result: closure is valid
        setup-output-valid : ValidAt {B ⇒ C} (eval (curry f) x) (output-value s₁) (memory s₁)
        setup-saved-regs : SavedRegsPreserved s s₁

  -- Case phases: dispatch → (left branch | right branch)
  module CaseSpecs {A B C : Type} (f : IR A C) (g : IR B C) where

    -- After dispatch for left: tag checked, ready for f
    record DispatchLeftPost (s s₁ : State) (a : ⟦ A ⟧) : Set where
      field
        dispatch-halted : halted s₁ ≡ false
        dispatch-stack-inv : StackInvariant s₁
        dispatch-ready-for-f : StackCapacity s₁ (ir-stack-requirement f)
        -- Input is now just 'a', not 'inj₁ a'

    -- After dispatch for right: tag checked, ready for g
    record DispatchRightPost (s s₁ : State) (b : ⟦ B ⟧) : Set where
      field
        dispatch-halted : halted s₁ ≡ false
        dispatch-stack-inv : StackInvariant s₁
        dispatch-ready-for-g : StackCapacity s₁ (ir-stack-requirement g)
        -- Input is now just 'b', not 'inj₂ b'

------------------------------------------------------------------------
-- Summary
--
-- This module defines:
--   1. MachineInterface - abstract machine (State, step, etc.)
--   2. InvariantInterface - abstract invariants (StackInvariant, etc.)
--   3. ValidityInterface - abstract validity (ValidAt)
--   4. CodeGenInterface - abstract codegen (compile, compile-length)
--   5. IRCorrectness - what it means for IR to be correct
--   6. Phase specs - pre/post conditions for composite IR phases
--
-- Each architecture provides instances of these interfaces,
-- then proves its phases satisfy the specs.
------------------------------------------------------------------------
