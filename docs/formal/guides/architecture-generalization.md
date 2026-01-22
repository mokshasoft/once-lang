# Architecture Generalization: Generic IR Proof Infrastructure

## Overview

This document describes the strategy for extracting generic proof infrastructure
from the x86 backend into Common modules, enabling AArch64 and RISC-V to share
the same dispatcher pattern, result records, and proof structure.

**Critical Constraint:** No new postulates are introduced. All abstraction is
achieved through parameterization and proper module design.

## The Problem

Currently, each architecture has its own implementation of:
- The mutual recursion dispatcher (`MutualIR.agda`)
- IR proof result records (`IRStarResult`, `IRStarResultV`)
- Stack/memory invariant patterns
- IR size measures and capacity tracking

This leads to:
1. **Code duplication** across x86, AArch64, and RISC-V
2. **Inconsistent patterns** (x86 uses Acc, AArch64/RISC-V use sized types)
3. **Maintenance burden** when fixing bugs or adding features
4. **Unnecessary `MutualIR/*.agda` modules** that exist only for module parameterization

### Current x86 Structure

```
MutualIR.agda (dispatcher - 1,673 lines)
    │
    ├── opens MutualIR/Pair.agda as parameterized module
    │       └── receives `run-ir-star` via module parameter
    │       └── calls IR/Pair.agda helpers
    │
    ├── opens MutualIR/Compose.agda as parameterized module
    │       └── receives `run-ir-star` via module parameter
    │       └── calls IR/Compose.agda helpers
    │
    └── opens MutualIR/Case.agda as parameterized module
            └── receives `run-ir-star` via module parameter
            └── calls IR/Case.agda helpers
```

The `MutualIR/*.agda` modules are thin wrappers that:
1. Receive the recursive dispatcher via module parameter
2. Call helpers from `IR/*.agda`
3. Thread the dispatcher to sub-IR calls

## The Key Insight

The parameterized module pattern is unnecessary. We can pass the recursive
dispatcher as a **function argument** instead:

```agda
-- Before (parameterized module pattern):
module MutualIR.Pair (bound : ℕ) (run-ir-star : RecDispatcher bound) where
  run-pair-star-v f g ... = ... run-ir-star f ... run-ir-star g ...

-- In MutualIR.agda:
run-ir-star-at-offset (⟨ f , g ⟩) ... (acc rs) =
  let open PairModule (ir-size ⟨ f , g ⟩) (make-rec rs)
  in run-pair-star-v f g ...

-- After (function argument pattern):
-- In IR/Pair.agda:
run-pair-star-v : ... → (rec : RecDispatcher bound) → ...
run-pair-star-v f g ... rec = ... rec f ... rec g ...

-- In generic dispatcher:
run-ir (⟨ f , g ⟩) ... (acc rs) =
  run-pair-star-v f g ... (make-rec rs) ...
```

This eliminates `MutualIR/*.agda` entirely and makes the dispatcher generic.

## Target Architecture

### Layer 1: Generic Types (Common/)

```
Common/
├── ArchConfig.agda        # Architecture configuration record
├── IRProofTypes.agda      # Preconditions, IRStarResult, RecDispatcher
├── IRSize.agda            # ir-size measure (purely IR-structural)
├── IRCapacity.agda        # ir-stack-requirement (purely IR-structural)
├── ValidAt.agda           # Validity predicate (purely value-structural)
└── IRDispatcher.agda      # Generic mutual block + IRImplementations interface
```

### Layer 2: Architecture Instantiation (X86/, AArch64/, RISC-V/)

Each architecture provides:
1. `ArchConfig` instantiation (registers, semantics)
2. `IRImplementations` record (base case + recursive case functions)
3. Individual `IR/*.agda` proofs that take `rec` as function argument

### ArchConfig Record

```agda
record ArchConfig : Set₁ where
  field
    -- Core types
    State   : Set
    Program : Set
    Reg     : Set

    -- Execution semantics
    halted  : State → Bool
    step    : Program → State → Maybe State
    pc      : State → ℕ

    -- Register access
    readReg  : State → Reg → ℕ
    memory   : State → Memory

    -- Distinguished registers
    resultReg  : Reg    -- x86=rax, AArch64=x0, RISC-V=a0
    argReg     : Reg    -- x86=rdi, AArch64=x0, RISC-V=a0
    envReg     : Reg    -- x86=r15, AArch64=x21, RISC-V=s11
    frameReg   : Reg    -- x86=rbp, AArch64=x29, RISC-V=s0
    stackReg   : Reg    -- x86=rsp, AArch64=sp, RISC-V=sp

    -- Constants
    wordSize : ℕ       -- All 64-bit: 8
```

### RecDispatcher Type

```agda
RecDispatcher : ArchConfig → ℕ → Set₁
RecDispatcher arch bound =
  ∀ {A B} (ir : IR A B) → ir-size ir < bound →
  (prefix suffix : Program arch) (x : ⟦ A ⟧) (s : State arch) →
  Preconditions arch ir s →
  ∃[ s' ] IRStarResult arch ir prog s s' x (length prefix)
```

### IRImplementations Interface

```agda
record IRImplementations (arch : ArchConfig) : Set₁ where
  field
    -- Base cases (non-recursive, ignore Acc)
    run-id       : BaseCaseType arch id
    run-terminal : BaseCaseType arch terminal
    run-fold     : BaseCaseType arch fold
    run-unfold   : BaseCaseType arch unfold
    run-arr      : BaseCaseType arch arr
    run-prim     : ∀ name → BaseCaseType arch (Prim name)
    run-fst      : BaseCaseType arch fst
    run-snd      : BaseCaseType arch snd
    run-inl      : BaseCaseType arch inl
    run-inr      : BaseCaseType arch inr

    -- Recursive cases (take RecDispatcher as first argument)
    run-pair    : ∀ {A B C} (f : IR C A) (g : IR C B) →
                  RecDispatcher arch (ir-size ⟨ f , g ⟩) →
                  ir-size f < ir-size ⟨ f , g ⟩ →
                  ir-size g < ir-size ⟨ f , g ⟩ →
                  ... → ∃[ s' ] IRStarResult arch ⟨ f , g ⟩ ...

    run-compose : ∀ {A B C} (f : IR A B) (g : IR B C) →
                  RecDispatcher arch (ir-size (g ∘ f)) →
                  ... → ∃[ s' ] IRStarResult arch (g ∘ f) ...

    run-case    : ∀ {A B C} (f : IR A C) (g : IR B C) →
                  RecDispatcher arch (ir-size [ f , g ]) →
                  ... → ∃[ s' ] IRStarResult arch [ f , g ] ...

    run-curry   : ∀ {A B C} (f : IR (A * B) C) →
                  RecDispatcher arch (ir-size (curry f)) →
                  ... → ∃[ s' ] IRStarResult arch (curry f) ...

    run-apply   : RecDispatcher arch (ir-size apply) →
                  ... → ∃[ s' ] IRStarResult arch apply ...
```

### Generic Dispatcher

```agda
module IRDispatcher (arch : ArchConfig) (impl : IRImplementations arch) where

mutual
  run-ir : ∀ {A B} (ir : IR A B) ... → Acc _<_ (ir-size ir) →
           ∃[ s' ] IRStarResult arch ir prog s s' x offset

  -- Base cases (ignore Acc)
  run-ir id ... _ = impl.run-id ...
  run-ir terminal ... _ = impl.run-terminal ...
  run-ir (inl) ... _ = impl.run-inl ...
  run-ir (inr) ... _ = impl.run-inr ...
  run-ir fold ... _ = impl.run-fold ...
  run-ir unfold ... _ = impl.run-unfold ...
  run-ir arr ... _ = impl.run-arr ...
  run-ir (Prim name) ... _ = impl.run-prim name ...
  run-ir fst ... _ = impl.run-fst ...
  run-ir snd ... _ = impl.run-snd ...

  -- Recursive cases (pass make-rec as function argument)
  run-ir (⟨ f , g ⟩) ... (acc rs) =
    impl.run-pair f g (make-rec rs) (⟨,⟩-f-smaller f g) (⟨,⟩-g-smaller f g) ...

  run-ir (g ∘ f) ... (acc rs) =
    impl.run-compose f g (make-rec rs) (∘-f-smaller f g) (∘-g-smaller f g) ...

  run-ir [ f , g ] ... (acc rs) =
    impl.run-case f g (make-rec rs) ([,]-f-smaller f g) ([,]-g-smaller f g) ...

  run-ir (curry f) ... (acc rs) =
    impl.run-curry f (make-rec rs) (curry-smaller f) ...

  run-ir apply ... (acc rs) =
    impl.run-apply (make-rec rs) ...

  -- Helper: construct RecDispatcher from Acc destructor
  make-rec : ∀ {n} → (∀ {m} → m < n → Acc _<_ m) → RecDispatcher arch n
  make-rec rs ir lt ... = run-ir ir ... (rs lt)
```

## What's Generic vs Architecture-Specific

### Generic (Goes to Common/)

| Component | Why Generic |
|-----------|-------------|
| `ir-size` measure | Purely IR-structural |
| `ir-stack-requirement` | Purely IR-structural |
| `ValidAt` predicate | Purely value-structural |
| `IRStarResult` record | Parameterized by ArchConfig |
| `Preconditions` record | Parameterized by ArchConfig |
| Dispatcher skeleton | Parameterized by IRImplementations |
| `RecDispatcher` type | Parameterized by ArchConfig |

### Architecture-Specific (Stays in X86/, AArch64/, RISC-V/)

| Component | Why Specific |
|-----------|--------------|
| Instruction sequences | Different opcodes |
| Register lemmas | ISA-specific |
| Frame constants | Calling conventions |
| Setup/cleanup traces | Instruction-level |
| `IR/*.agda` implementations | Trace actual instructions |

## Migration Path

### Phase 1: Documentation (This Document)
Document the strategy and target architecture.

### Phase 2: Core Type Abstractions
Create in `Common/`:
1. `ArchConfig.agda` - configuration record
2. `IRProofTypes.agda` - result records, preconditions
3. `IRSize.agda` - move from x86's IRSize.agda
4. `IRCapacity.agda` - extract from StackInstantiation
5. `ValidAt.agda` - move from x86's MemoryValid.agda

### Phase 3: Generic Dispatcher
Create `Common/IRDispatcher.agda`:
1. Define `IRImplementations` interface
2. Implement generic mutual block

### Phase 4: Refactor x86
1. Modify `IR/*.agda` to take `rec` as function argument
2. Delete `MutualIR/*.agda` modules
3. Create `Implementations.agda` collecting all IR functions
4. Replace `MutualIR.agda` with generic dispatcher instantiation

### Phase 5: Apply to AArch64/RISC-V (Future)
1. Migrate from sized-types to Acc-based termination
2. Implement `IRImplementations` interface
3. Delete architecture-specific dispatcher code

## Benefits

1. **Single source of truth** for dispatcher logic
2. **Consistent termination** via Acc across all architectures
3. **Reduced maintenance** - fix once, apply everywhere
4. **Clearer architecture** - what's generic vs specific is explicit
5. **Easier onboarding** - new architectures just implement interface
6. **No new postulates** - all abstraction via parameterization

## Files to Create

```
docs/formal/guides/architecture-generalization.md  (this document)
formal/Once/Backend/Common/ArchConfig.agda
formal/Once/Backend/Common/IRProofTypes.agda
formal/Once/Backend/Common/IRSize.agda
formal/Once/Backend/Common/IRCapacity.agda
formal/Once/Backend/Common/ValidAt.agda
formal/Once/Backend/Common/IRDispatcher.agda
formal/Once/Backend/X86/Correct/Implementations.agda
```

## Files to Delete

```
formal/Once/Backend/X86/Correct/MutualIR/Pair.agda
formal/Once/Backend/X86/Correct/MutualIR/Compose.agda
formal/Once/Backend/X86/Correct/MutualIR/Case.agda
formal/Once/Backend/X86/Correct/MutualIR/Dispatcher.agda
```

## Related Documents

- `memory-region-instantiation.md` - Similar layered abstraction pattern
- `d041-region-migration.md` - Abstract region approach
- `splitting-large-mutual-blocks.md` - Mutual block extraction strategies
