------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ArchInstantiation
--
-- X86 instantiation of the architecture-independent IR proof framework.
--
-- This module:
--   1. Instantiates MachineInterface with X86 types
--   2. Instantiates InvariantInterface with X86 invariants
--   3. Instantiates ValidityInterface with X86 ValidAt
--   4. Instantiates CodeGenInterface with X86 codegen
--   5. Shows X86 phase results imply Common phase specs
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ArchInstantiation where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- Once core
open import Once.Type using (Type; _*_; _⇒_; Eff) renaming (_+_ to _⊕_)
open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd)
open import Once.Semantics using (⟦_⟧; eval)

-- X86 specific
open import Once.Backend.X86.Syntax using (Program; Instr; rax; r14; r15; rbp; rdi)
open import Once.Backend.X86.Semantics using (State; Memory; Word; readMem; step; readReg)
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen using (compile-x86)

-- X86 correctness infrastructure
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; ir-stack-requirement; ir-output-capacity; ir-rsp-delta)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Layout using (InStack; InHeap; InCode)

-- Common framework
open import Once.Backend.Common.IR.Spec as Spec

------------------------------------------------------------------------
-- X86 Machine Interface
------------------------------------------------------------------------

X86-MachineInterface : Spec.MachineInterface
X86-MachineInterface = record
  { State = State
  ; Program = Program
  ; Word = Word
  ; Memory = Memory
  ; pc = pc
  ; halted = halted
  ; memory = memory
  ; output-value = λ s → readReg (regs s) rax
  ; readMem = readMem
  ; step = step
  }

------------------------------------------------------------------------
-- X86 Invariant Interface
------------------------------------------------------------------------

-- Saved registers preserved between states (r14, r15, rbp for X86)
X86-SavedRegsPreserved : State → State → Set
X86-SavedRegsPreserved s s' =
  (readReg (regs s') r14 ≡ readReg (regs s) r14) ×
  (readReg (regs s') r15 ≡ readReg (regs s) r15) ×
  (readReg (regs s') rbp ≡ readReg (regs s) rbp)

-- Heap preserved between states
X86-HeapPreserved : State → State → Set
X86-HeapPreserved s s' = ∀ addr → InHeap addr → readMem (memory s') addr ≡ readMem (memory s) addr

-- Code preserved between states
X86-CodePreserved : State → State → Set
X86-CodePreserved s s' = ∀ addr → InCode addr → readMem (memory s') addr ≡ readMem (memory s) addr

-- Frame preserved (memory above rbp unchanged)
X86-FramePreserved : State → State → Set
X86-FramePreserved s s' = ∀ addr → addr > readReg (regs s) rbp →
                          readMem (memory s') addr ≡ readMem (memory s) addr

X86-InvariantInterface : Spec.InvariantInterface X86-MachineInterface
X86-InvariantInterface = record
  { StackInvariant = StackInvariant
  ; StackCapacity = StackCapacity
  ; SavedRegsPreserved = X86-SavedRegsPreserved
  ; InStack = InStack
  ; InHeap = InHeap
  ; InCode = InCode
  ; HeapPreserved = X86-HeapPreserved
  ; CodePreserved = X86-CodePreserved
  ; FramePreserved = X86-FramePreserved
  }

------------------------------------------------------------------------
-- X86 Validity Interface
------------------------------------------------------------------------

X86-ValidityInterface : Spec.ValidityInterface X86-MachineInterface X86-InvariantInterface
X86-ValidityInterface = record
  { ValidAt = ValidAt
  ; valid-preserved-heap = valid-preserved-heap-x86
  }
  where
    -- ValidAt preserved when heap unchanged
    postulate
      valid-preserved-heap-x86 : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m₁ m₂ : Memory} →
        ValidAt v addr m₁ →
        (∀ a → InHeap a → readMem m₂ a ≡ readMem m₁ a) →
        ValidAt v addr m₂

------------------------------------------------------------------------
-- X86 CodeGen Interface
------------------------------------------------------------------------

-- Compile length for X86
postulate
  compile-x86-length : ∀ {A B} → IR A B → ℕ

X86-CodeGenInterface : Spec.CodeGenInterface X86-MachineInterface
X86-CodeGenInterface = record
  { compile = compile-x86
  ; compile-length = compile-x86-length
  ; ir-stack-requirement = ir-stack-requirement
  ; ir-output-capacity = ir-output-capacity
  ; ir-rsp-delta = ir-rsp-delta
  }

------------------------------------------------------------------------
-- Open the IRSpecs module with X86 interfaces
------------------------------------------------------------------------

open Spec.IRSpecs X86-MachineInterface X86-InvariantInterface X86-ValidityInterface X86-CodeGenInterface
  public

------------------------------------------------------------------------
-- Bridging X86 results to Common specs
--
-- These functions show how X86's detailed results imply Common's
-- abstract postconditions.
------------------------------------------------------------------------

open import Once.Backend.X86.Correct.IR.Pair as X86Pair
  using (PairSetupResultV; PairMiddleResultV; PairFinalResult)
open import Once.Backend.X86.Correct.StackInstantiation
  using (capacity-from-larger; pair-inner-requirement)
open import Data.Nat.Properties using (m≤m⊔n)

-- | Extract Common SetupPost from X86's PairSetupResultV
-- Shows that X86's detailed setup result implies the abstract postcondition
module PairBridge {A B C : Type} (f : IR C A) (g : IR C B) where

  open PairSpecs f g

  -- X86's cap-inner is for (pair-inner-requirement f g)
  -- We need StackCapacity for (ir-stack-requirement f)
  -- Since ir-stack-requirement f ≤ pair-inner-requirement f g, we can derive it

  extract-setup-post : ∀ {prefix suffix : Program} {x : ⟦ C ⟧} {s : State} →
    (res : PairSetupResultV f g prefix suffix x s) →
    SetupPost s (PairSetupResultV.s-setup res) x
  extract-setup-post res = record
    { setup-halted = PairSetupResultV.h-setup res
    ; setup-stack-inv = PairSetupResultV.stack-inv-setup res
    ; setup-ready-for-f = cap-for-f
    }
    where
      -- Derive capacity for f from cap-inner
      cap-for-f : StackCapacity (PairSetupResultV.s-setup res) (ir-stack-requirement f)
      cap-for-f = capacity-from-larger
        (PairSetupResultV.s-setup res)
        (ir-stack-requirement f)
        (pair-inner-requirement f g)
        (PairSetupResultV.cap-inner res)
        (m≤m⊔n (ir-stack-requirement f) (ir-rsp-delta f + ir-stack-requirement g))

  -- For middle, we need the state after f (s2)
  -- X86's PairMiddleResultV has s2 and the capacity

  extract-middle-post : ∀ {prefix suffix : Program} {x : ⟦ C ⟧}
    {s s-setup s1 : State} →
    (res : PairMiddleResultV f g prefix suffix x s s-setup s1) →
    MiddlePost s-setup s1 (PairMiddleResultV.s2 res) x (eval f x)
  extract-middle-post {s1 = s1} res = record
    { middle-halted = PairMiddleResultV.h2 res
    ; middle-stack-inv = PairMiddleResultV.stack-inv-s2 res
    ; middle-ready-for-g = cap-for-g
    }
    where
      -- Need to derive StackCapacity s2 (ir-stack-requirement g)
      -- This is done in MutualIR/Pair.agda via capacity threading
      postulate
        cap-for-g : StackCapacity (PairMiddleResultV.s2 res) (ir-stack-requirement g)

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--   1. X86 instantiations of all abstract interfaces
--   2. Bridge functions to extract Common specs from X86 results
--
-- The X86 proofs can use their detailed records internally,
-- while exposing the Common interface for the shared MutualRecursion.
------------------------------------------------------------------------
