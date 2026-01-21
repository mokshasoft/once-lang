# Architecture-Independent IR Proofs

This document describes the target architecture for making IR correctness proofs portable across backends (X86, AArch64, RISC-V).

## Overview

The key insight is separating **proof structure** (which is universal) from **proof content** (which is architecture-specific).

For any IR constructor like `pair ⟨f,g⟩`, the proof follows the same pattern:
1. Execute setup phase
2. Recursively prove `f` correct
3. Execute middle phase
4. Recursively prove `g` correct
5. Execute cleanup phase
6. Combine results

This STRUCTURE is identical across architectures. What differs is what "setup phase" means in terms of actual instructions.

## Layered Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  Layer 7: Phase Lemmas (ARCH-SPECIFIC)                          │
│    X86/Phases/, AArch64/Phases/, RiscV64/Phases/                │
│    - Actual instruction-by-instruction proofs                   │
│    - Register-specific reasoning                                │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ implements
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  Layer 6: Mutual Recursion Structure (COMMON)                   │
│    Common/IR/MutualRecursion.agda                               │
│    - Recursive traversal over IR                                │
│    - Parameterized by ArchCorrectness interface                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ uses
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  Layer 5: Proof Combinators (COMMON)                            │
│    Common/IR/Combinators.agda                                   │
│    - pair-from-phases, curry-from-phases, case-from-phases      │
│    - How to combine phase results into full correctness         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ uses
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  Layer 4: IR Correctness Specs (COMMON)                         │
│    Common/IR/Spec.agda                                          │
│    - PairCorrectness, CurryCorrectness, CaseCorrectness         │
│    - What correctness MEANS (not how to prove it)               │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ uses
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  Layer 3: Execution Model (COMMON, parameterized)               │
│    Common/Star.agda, Common/Fetch.agda                          │
│    - Reflexive-transitive closure of step                       │
│    - Program fetching lemmas                                    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ uses
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  Layer 2: Memory Validity Model (COMMON, parameterized)         │
│    Common/ValidAt.agda, Common/MemoryStructures.agda            │
│    - ValidAt predicate for all types                            │
│    - PairAtS, InlAtS, InrAtS, ClosureAtS                        │
│    - Validity preservation under writes                         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ uses
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  Layer 1: Pure Semantics (COMMON)                               │
│    Once/IR.agda, Once/Semantics.agda, Once/Type.agda            │
│    - IR definition, eval function, type interpretation          │
│    - No machine model, pure mathematics                         │
└─────────────────────────────────────────────────────────────────┘
```

## The ArchCorrectness Interface

Each architecture must implement this interface to plug into the common proof structure:

```agda
record ArchCorrectness : Set₁ where
  field
    ---------------------------------------------------------
    -- Machine Model
    ---------------------------------------------------------
    State : Set
    Instr : Set
    Program : Set

    -- State accessors (abstract over register names)
    pc : State → ℕ
    memory : State → Memory
    halted : State → Bool
    output-value : State → Word      -- rax / x0 / a0

    -- Execution
    step : Program → State → Maybe State

    ---------------------------------------------------------
    -- Code Generation
    ---------------------------------------------------------
    compile : ∀ {A B} → IR A B → Program
    compile-length : ∀ {A B} → IR A B → ℕ

    ---------------------------------------------------------
    -- Invariants (abstract over specific register sets)
    ---------------------------------------------------------
    StackInvariant : State → Set
    StackCapacity : State → ℕ → Set
    SavedRegistersPreserved : State → State → Set

    ---------------------------------------------------------
    -- Phase Lemmas for Composite IR
    ---------------------------------------------------------

    -- Pair: setup → f → middle → g → cleanup
    pair-phases : ∀ {A B C} (f : IR C A) (g : IR C B) →
                  PairPhases f g

    -- Curry: setup → (thunk: f) → skip-thunk
    curry-phases : ∀ {A B C} (f : IR (A × B) C) →
                   CurryPhases f

    -- Case: dispatch → (branch-left: f | branch-right: g)
    case-phases : ∀ {A B C} (f : IR A C) (g : IR B C) →
                  CasePhases f g

    -- Compose: f → g (simple sequential)
    compose-phases : ∀ {A B C} (f : IR A B) (g : IR B C) →
                     ComposePhases f g

    ---------------------------------------------------------
    -- Leaf Cases (no sub-IR, direct proof)
    ---------------------------------------------------------
    id-correct : ∀ {A} → LeafCorrect (id {A})
    inl-correct : ∀ {A B} → LeafCorrect (inl {A} {B})
    inr-correct : ∀ {A B} → LeafCorrect (inr {A} {B})

    ---------------------------------------------------------
    -- Apply (special: needs induction hypothesis for thunk)
    ---------------------------------------------------------
    apply-correct :
      (ih : ∀ {A B} (ir : IR A B) → IRCorrect ir) →
      ∀ {A B} → ApplyCorrect {A} {B}
```

## Phase Structures

Each composite IR has a "phases" record that captures what the architecture-specific code does:

### PairPhases

```agda
record PairPhases {A B C} (f : IR C A) (g : IR C B) : Set₁ where
  field
    -- Phase 1: Setup
    -- Save registers, allocate space for pair, prepare for f
    setup-len : ℕ
    setup-correct : ∀ x s →
      Preconditions s →
      ∃ s₁ → Star setup-len s s₁
           × SetupPostconditions s s₁ x

    -- Phase 2: Middle (between f and g)
    -- Store f's result, prepare input for g
    middle-len : ℕ
    middle-correct : ∀ x s₁ s₂ →
      -- s₂ is state after executing f
      ∃ s₃ → Star middle-len s₂ s₃
           × MiddlePostconditions s₁ s₂ s₃ x (eval f x)

    -- Phase 3: Cleanup
    -- Store g's result, construct pair, restore registers
    cleanup-len : ℕ
    cleanup-correct : ∀ x s₁ s₃ s₄ →
      -- s₄ is state after executing g
      ∃ s₅ → Star cleanup-len s₄ s₅
           × CleanupPostconditions s₁ s₃ s₄ s₅ x (eval f x) (eval g x)
           × ValidAt (eval f x , eval g x) (output-value s₅) (memory s₅)
```

### CurryPhases

```agda
record CurryPhases {A B C} (f : IR (A × B) C) : Set where
  field
    -- Phase 1: Setup (create closure, skip over thunk)
    setup-len : ℕ
    setup-correct : ∀ x s →
      Preconditions s →
      ∃ s₁ → Star setup-len s s₁
           × ClosureCreated s s₁ x (compile-length f)

    -- Thunk structure (for when closure is invoked via apply)
    thunk-entry-offset : ℕ
    thunk-len : ℕ  -- = compile-length f + epilogue
```

### CasePhases

```agda
record CasePhases {A B C} (f : IR A C) (g : IR B C) : Set where
  field
    -- Phase 1: Dispatch (read tag, branch)
    dispatch-len : ℕ
    dispatch-correct-left : ∀ a s →
      input-is-inl a s →
      ∃ s₁ → Star dispatch-len s s₁
           × ReadyForLeftBranch s₁ a

    dispatch-correct-right : ∀ b s →
      input-is-inr b s →
      ∃ s₁ → Star dispatch-len s s₁
           × ReadyForRightBranch s₁ b

    -- Join point handling
    left-epilogue-len : ℕ
    right-epilogue-len : ℕ
```

## The Mutual Recursion Module

This is the heart of the shared proof structure:

```agda
module Common.IR.MutualRecursion (Arch : ArchCorrectness) where

open ArchCorrectness Arch

-- Import combinators that know how to assemble phase results
open import Common.IR.Combinators Arch

mutual
  -- Main theorem: all IR is correct
  ir-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
               Preconditions s →
               ∃ s' → IRCorrectness ir x s s'

  -- Identity: delegate to arch
  ir-correct id x s pre = Arch.id-correct x s pre

  -- Composition: f then g
  ir-correct (compose g f) x s pre =
    let (s₁ , f-correct) = ir-correct f x s pre
        (s₂ , g-correct) = ir-correct g (eval f x) s₁ (from-f-post f-correct)
    in compose-combine f-correct g-correct (Arch.compose-phases f g)

  -- Pair: setup → f → middle → g → cleanup
  ir-correct (pair ⟨f,g⟩) x s pre =
    let phases = Arch.pair-phases f g
        (s₁ , setup-done) = PairPhases.setup-correct phases x s pre
        (s₂ , f-correct) = ir-correct f x s₁ (setup-enables-f setup-done)
        (s₃ , middle-done) = PairPhases.middle-correct phases x s₁ s₂
        (s₄ , g-correct) = ir-correct g x s₃ (middle-enables-g middle-done)
        (s₅ , cleanup-done) = PairPhases.cleanup-correct phases x s₁ s₃ s₄
    in s₅ , pair-combine setup-done f-correct middle-done g-correct cleanup-done

  -- Curry: setup (closure created, thunk skipped)
  ir-correct (curry f) x s pre =
    let phases = Arch.curry-phases f
        (s₁ , setup-done) = CurryPhases.setup-correct phases x s pre
    in s₁ , curry-combine setup-done

  -- Apply: arch handles this specially, passing IH for thunk
  ir-correct apply x s pre =
    Arch.apply-correct (λ ir → ir-correct ir) x s pre

  -- Case: dispatch then appropriate branch
  ir-correct (case [f,g]) x s pre with inspect-sum x
  ... | is-inl a =
    let phases = Arch.case-phases f g
        (s₁ , dispatch-done) = CasePhases.dispatch-correct-left phases a s pre
        (s₂ , f-correct) = ir-correct f a s₁ (dispatch-enables-f dispatch-done)
    in case-combine-left dispatch-done f-correct
  ... | is-inr b =
    let phases = Arch.case-phases f g
        (s₁ , dispatch-done) = CasePhases.dispatch-correct-right phases b s pre
        (s₂ , g-correct) = ir-correct g b s₁ (dispatch-enables-g dispatch-done)
    in case-combine-right dispatch-done g-correct

  -- Inl/Inr: delegate to arch
  ir-correct inl x s pre = Arch.inl-correct x s pre
  ir-correct inr x s pre = Arch.inr-correct x s pre
```

## What's Shared vs Architecture-Specific

| Component | Location | Status |
|-----------|----------|--------|
| IR definition | `Once/IR.agda` | Shared |
| Semantics (eval) | `Once/Semantics.agda` | Shared |
| ValidAt predicate | `Common/ValidAt.agda` | Shared (to move) |
| Memory structures | `Common/MemoryStructures.agda` | Shared (to move) |
| Validity preservation | `Common/ValidityPreservation.agda` | Shared (to move) |
| Star relation | `Common/Star.agda` | Shared (exists) |
| Fetch lemmas | `Common/Fetch.agda` | Shared (exists) |
| Correctness specs | `Common/IR/Spec.agda` | Shared (to create) |
| Proof combinators | `Common/IR/Combinators.agda` | Shared (to create) |
| Mutual recursion | `Common/IR/MutualRecursion.agda` | Shared (to create) |
| ArchCorrectness interface | `Common/IR/ArchInterface.agda` | Shared (to create) |
| X86 phases | `X86/Correct/Phases/*.agda` | X86-specific |
| AArch64 phases | `AArch64/Correct/Phases/*.agda` | AArch64-specific |
| RISC-V phases | `RiscV64/Correct/Phases/*.agda` | RISC-V-specific |

## Benefits

1. **Single source of truth** for proof structure
   - Bug fixes to mutual recursion benefit all backends
   - Consistent proof strategy across architectures

2. **Clear interface** for new backends
   - Implement `ArchCorrectness` interface
   - Provide phase lemmas
   - Get full IR correctness for free

3. **Separation of concerns**
   - Common code: what correctness means, how proofs combine
   - Arch code: actual instruction sequences, register allocation

4. **Reduced duplication**
   - Current: ~3000 LOC per backend for IR proofs
   - Target: ~500 LOC common + ~1500 LOC per backend for phases

## Migration Path

1. **Phase 1**: Create `Common/IR/Spec.agda` with correctness specifications
2. **Phase 2**: Create `Common/IR/ArchInterface.agda` with the interface
3. **Phase 3**: Create `Common/IR/Combinators.agda` with phase combiners
4. **Phase 4**: Move `ValidAt` and memory structures to Common
5. **Phase 5**: Refactor X86 proofs into phase lemmas
6. **Phase 6**: Create `Common/IR/MutualRecursion.agda`
7. **Phase 7**: Implement interface for AArch64 and RISC-V

## Relationship to Escape Analysis

The `ValidAt` predicate currently assumes all valid addresses are in heap (via the `valid-in-heap` postulate). With escape analysis:

- Non-escaping values can be stack-allocated
- The validity model needs to track WHERE a value lives
- Phase lemmas need to prove appropriate disjointness

This architecture supports that evolution:
- `ValidAt` can be extended with region tracking in Common
- Phase lemmas prove region-appropriate preservation
- The mutual recursion structure remains unchanged

## Open Questions

1. **Apply and thunks**: Apply needs the IH to prove the thunk correct. The current design passes `ir-correct` to `apply-correct`. Is there a cleaner way?

2. **ClosureWellFormed**: Currently X86 has `ClosureWellFormed` tracking thunk structure. Should this be part of the common interface?

3. **StackCapacity threading**: Currently threaded manually. Should the interface abstract over this?

4. **Compose optimization**: Compose of two simple IR might not need phases at all. Should we special-case?
