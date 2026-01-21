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

  -- | Extract Common CleanupPost from X86's PairFinalResult
  --
  -- State mapping:
  --   s = initial state
  --   s₁ = after setup
  --   s₃ = after middle (ready for g) - s3 precondition state
  --   s₄ = after g execution
  --   s₅ = final (s-final in PairFinalResult)
  --
  -- Note: cleanup-output-valid requires the pair ValidAt which is constructed
  -- from f and g's ValidAt proofs - this is passed as an additional parameter.
  extract-cleanup-post : ∀ {prefix suffix : Program} {x : ⟦ C ⟧}
    {s s-setup s-mid s₄ : State}
    (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) →
    (fin : PairFinalResult f g prefix suffix s s₄) →
    -- Capacity for output (derived from initial capacity + rsp restoration)
    (cap-out : StackCapacity (PairFinalResult.s-final fin) (ir-output-capacity ⟨ f , g ⟩)) →
    -- ValidAt for the pair (constructed from f and g validity)
    (pair-valid : ValidAt {A * B} (fx , gx)
                          (readReg (regs (PairFinalResult.s-final fin)) rax)
                          (memory (PairFinalResult.s-final fin))) →
    CleanupPost s s-setup s-mid s₄ (PairFinalResult.s-final fin) x fx gx
  extract-cleanup-post {s = s} fx gx fin cap-out pair-valid = record
    { cleanup-halted = PairFinalResult.h-final fin
    ; cleanup-stack-inv = PairFinalResult.stack-inv-fin fin
    ; cleanup-capacity = cap-out
    ; cleanup-output-valid = pair-valid
    ; cleanup-saved-regs = saved-regs
    }
    where
      s-final = PairFinalResult.s-final fin
      saved-regs : X86-SavedRegsPreserved s s-final
      saved-regs = ( PairFinalResult.r14-fin fin
                   , PairFinalResult.r15-fin fin
                   , PairFinalResult.rbp-fin fin
                   )

------------------------------------------------------------------------
-- X86 ArchCorrectness Implementation (Skeleton)
--
-- This section shows how to implement the ArchCorrectness interface
-- for X86 by wiring together:
--   - X86's existing phase proofs (pair-setup-star-v, etc.)
--   - The bridge extractors defined above
--
-- Currently using postulates; full implementation would:
--   1. Call X86 phase functions (pair-setup-star-v, etc.)
--   2. Extract Common postconditions using PairBridge extractors
--   3. Combine into ArchCorrectness record
------------------------------------------------------------------------

open import Once.Backend.Common.IR.ArchInterface as Arch

-- Postulate leaf lemmas (would delegate to X86's StarBase proofs)
postulate
  x86-id-correct : ∀ {A : Type} (x : ⟦ A ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement (id {A})) →
    ∃[ s' ] IRCorrectness (id {A}) (compile-x86 (id {A})) s s' x 0

  x86-inl-correct : ∀ {A B : Type} (a : ⟦ A ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement (inl {A} {B})) →
    ∃[ s' ] IRCorrectness (inl {A} {B}) (compile-x86 (inl {A} {B})) s s' a 0

  x86-inr-correct : ∀ {A B : Type} (b : ⟦ B ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement (inr {A} {B})) →
    ∃[ s' ] IRCorrectness (inr {A} {B}) (compile-x86 (inr {A} {B})) s s' b 0

  x86-fst-correct : ∀ {A B : Type} (p : ⟦ A * B ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement (fst {A} {B})) →
    ∃[ s' ] IRCorrectness (fst {A} {B}) (compile-x86 (fst {A} {B})) s s' p 0

  x86-snd-correct : ∀ {A B : Type} (p : ⟦ A * B ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement (snd {A} {B})) →
    ∃[ s' ] IRCorrectness (snd {A} {B}) (compile-x86 (snd {A} {B})) s s' p 0

-- Postulate phase lemmas (would delegate to X86 phase proofs + bridges)
postulate
  x86-pair-setup-correct : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
    (x : ⟦ C ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement ⟨ f , g ⟩) →
    ∃[ s₁ ] PairSpecs.SetupPost f g s s₁ x

  x86-pair-middle-correct : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
    (x : ⟦ C ⟧) (s s₁ s₂ : State) (fx : ⟦ A ⟧) →
    ∃[ s₃ ] PairSpecs.MiddlePost f g s₁ s₂ s₃ x fx

  x86-pair-cleanup-correct : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
    (x : ⟦ C ⟧) (s s₁ s₃ s₄ : State) (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) →
    ∃[ s₅ ] PairSpecs.CleanupPost f g s s₁ s₃ s₄ s₅ x fx gx

  x86-curry-setup-correct : ∀ {A B C : Type} (f : IR (A * B) C)
    (x : ⟦ A ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement (curry f)) →
    ∃[ s₁ ] CurrySpecs.SetupPost f s s₁ x

  x86-case-dispatch-left : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
    (a : ⟦ A ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement [ f , g ]) →
    ∃[ s₁ ] CaseSpecs.DispatchLeftPost f g s s₁ a

  x86-case-dispatch-right : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
    (b : ⟦ B ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement [ f , g ]) →
    ∃[ s₁ ] CaseSpecs.DispatchRightPost f g s s₁ b

  x86-compose-enables-second : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
    (x : ⟦ A ⟧) (s s' : State) →
    IRCorrectness g (compile-x86 g) s s' x 0 →
    Preconditions s' (readReg (regs s') rax) (ir-stack-requirement f)

  x86-apply-correct :
    (ih : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
          Preconditions s (readReg (regs s) rax) (ir-stack-requirement ir) →
          ∃[ s' ] IRCorrectness ir (compile-x86 ir) s s' x 0) →
    ∀ {A B : Type} (p : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    Preconditions s (readReg (regs s) rax) (ir-stack-requirement (apply {A} {B})) →
    ∃[ s' ] IRCorrectness (apply {A} {B}) (compile-x86 (apply {A} {B})) s s' p 0

------------------------------------------------------------------------
-- X86 ArchCorrectness Record
--
-- This bundles all the interfaces and lemmas into the ArchCorrectness
-- record that MutualRecursion requires.
------------------------------------------------------------------------

X86-ArchCorrectness : Arch.ArchCorrectness
X86-ArchCorrectness = record
  { machine = X86-MachineInterface
  ; invariants = X86-InvariantInterface
  ; validity = X86-ValidityInterface
  ; codegen = X86-CodeGenInterface
  -- Leaf lemmas
  ; id-correct = x86-id-correct
  ; inl-correct = x86-inl-correct
  ; inr-correct = x86-inr-correct
  ; fst-correct = x86-fst-correct
  ; snd-correct = x86-snd-correct
  -- Phase lemmas
  ; pair-setup-correct = x86-pair-setup-correct
  ; pair-middle-correct = x86-pair-middle-correct
  ; pair-cleanup-correct = x86-pair-cleanup-correct
  ; curry-setup-correct = x86-curry-setup-correct
  ; case-dispatch-left = x86-case-dispatch-left
  ; case-dispatch-right = x86-case-dispatch-right
  ; compose-enables-second = x86-compose-enables-second
  ; apply-correct = x86-apply-correct
  }

------------------------------------------------------------------------
-- Instantiate MutualRecursion with X86
--
-- This gives us the full IR correctness theorem for X86!
------------------------------------------------------------------------

open import Once.Backend.Common.IR.MutualRecursion as MR

module X86-IRCorrect = MR.IRCorrect X86-ArchCorrectness

-- Export the main theorem
x86-ir-correct : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  Preconditions s (readReg (regs s) rax) (ir-stack-requirement ir) →
  ∃[ s' ] IRCorrectness ir (compile-x86 ir) s s' x 0
x86-ir-correct = X86-IRCorrect.ir-correct

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--   1. X86 instantiations of all abstract interfaces
--   2. Bridge functions to extract Common specs from X86 results
--   3. X86-ArchCorrectness record (currently with postulates)
--   4. x86-ir-correct: full IR correctness for X86 via MutualRecursion
--
-- To complete the wiring (eliminate postulates):
--   - Implement leaf lemmas by wrapping X86's run-*-star-v functions
--   - Implement phase lemmas by calling X86 phase proofs + PairBridge
--   - Each postulate has a corresponding X86 proof that needs adapting
------------------------------------------------------------------------
