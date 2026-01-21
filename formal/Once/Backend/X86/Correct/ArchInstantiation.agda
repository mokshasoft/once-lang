------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ArchInstantiation
--
-- X86 instantiation of the architecture-independent IR proof framework.
--
-- This module shows how X86's concrete types satisfy the abstract
-- interfaces defined in Once.Backend.Common.IR.Spec.
--
-- NO NEW POSTULATES: All implementations use existing X86 infrastructure.
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
open import Once.Backend.X86.Syntax using (Program; Instr; rax; r14; r15; rbp; rsp; rdi)
open import Once.Backend.X86.Semantics using (State; Memory; Word; readMem; step; readReg)
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen using (compile-x86; compile-length)

-- X86 correctness infrastructure
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; ir-stack-requirement; ir-output-capacity; ir-rsp-delta; slots)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-subst-heap-preserved)
open import Once.Backend.X86.Layout using (InStack; InHeap; InCode)
open import Once.Backend.X86.Correct.Star as X86Star
  using (Star; refl*; step*; star-trans)

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
  ; input-value = λ s → readReg (regs s) rdi   -- X86: input in rdi
  ; output-value = λ s → readReg (regs s) rax  -- X86: output in rax
  ; readMem = readMem
  ; program-length = length  -- Program = List Instr for X86
  ; empty-program = []       -- Empty list for X86
  ; empty-program-length = refl
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

-- RSP delta tracking: rsp s' ≡ rsp s ∸ slots delta
X86-RspDelta : State → State → ℕ → Set
X86-RspDelta s s' delta = readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slots delta

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
  ; FramePtrInvariant = RbpInvariant
  ; SavedRegsPreserved = X86-SavedRegsPreserved
  ; rsp-delta-slots = X86-RspDelta
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
  ; valid-preserved-heap = λ v heap-eq → valid-subst-heap-preserved v refl heap-eq
  }

------------------------------------------------------------------------
-- X86 CodeGen Interface
------------------------------------------------------------------------

X86-CodeGenInterface : Spec.CodeGenInterface X86-MachineInterface
X86-CodeGenInterface = record
  { compile = compile-x86
  ; compile-length = compile-length
  ; ir-stack-requirement = ir-stack-requirement
  ; ir-output-capacity = ir-output-capacity
  ; ir-rsp-delta = ir-rsp-delta
  }

------------------------------------------------------------------------
-- Open the IRSpecs module with X86 interfaces
------------------------------------------------------------------------

open Spec.IRSpecs
  X86-MachineInterface
  X86-InvariantInterface
  X86-ValidityInterface
  X86-CodeGenInterface
  Star  -- X86's Star directly
  public

------------------------------------------------------------------------
-- Conversion: IRStarResultV → IRCorrectness
--
-- This shows X86's detailed result type implies the Common result type.
-- NO POSTULATES - just field extraction and combination.
------------------------------------------------------------------------

open import Once.Backend.X86.Correct.StarBase using (IRStarResultV)

-- Convert X86's IRStarResultV to Common's IRCorrectness
IRStarResultV→IRCorrectness : ∀ {A B : Type} {ir : IR A B}
    {prog : Program} {s s' : State} {x : ⟦ A ⟧} {offset : ℕ} →
  IRStarResultV ir prog s s' x offset →
  IRCorrectness ir prog s s' x offset
IRStarResultV→IRCorrectness res = record
  { exec-star = IRStarResultV.ir-star res
  ; exec-halted = IRStarResultV.ir-halted res
  ; exec-pc = IRStarResultV.ir-pc res
  ; exec-output-valid = IRStarResultV.ir-result-valid res
  ; exec-saved-regs = ( IRStarResultV.ir-r14 res
                      , IRStarResultV.ir-r15 res
                      , IRStarResultV.ir-rbp res )
  ; exec-heap-preserved = IRStarResultV.ir-mem-heap res
  ; exec-code-preserved = IRStarResultV.ir-mem-code res
  ; exec-frame-preserved = IRStarResultV.ir-mem-above res
  ; exec-stack-inv = IRStarResultV.ir-stack-inv res
  ; exec-capacity = IRStarResultV.ir-capacity res
  ; exec-frame-inv = IRStarResultV.ir-rbp-inv res
  }

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--   1. X86 instantiations of all abstract interfaces (no postulates)
--   2. IRStarResultV→IRCorrectness conversion (no postulates)
--
-- Key mappings:
--   - input-value = rdi
--   - output-value = rax
--   - FramePtrInvariant = RbpInvariant
--   - SavedRegsPreserved = (r14, r15, rbp) preservation
--   - Star from X86.Correct.Star
--
-- X86's IRStarResultV is a SUPERSET of Common's IRCorrectness.
-- The conversion just extracts the common fields.
------------------------------------------------------------------------
