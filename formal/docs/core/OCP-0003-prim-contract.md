# OCP-0003: PrimContract - Unified Interface for Domain Compilers

## Status

**Phase 2 Complete** - Integer arithmetic postulates eliminated

## Summary

Define `PrimContract` as a uniform interface that domain compilers (Arith, future Loop compiler, IO interpretations) must satisfy. This eliminates postulates and provides a clean integration point between the CCC compiler and external/domain-specific code generators.

## Core Principles

### 1. No Postulates for Arithmetic

The semantic foundation uses **MachineInterface** directly:

```agda
⟦ Int ⟧ = Word  (from MachineInterface, not ℤ)
```

This eliminates the "encode gap":
- **Old approach**: `⟦ Int ⟧ = ℤ`, requiring `postulate encode-add : encode a + encode b ≡ encode (a + b)`
- **New approach**: `⟦ Int ⟧ = Word`, where `word-add` IS the semantic operation

The only trust is in `MachineInterface` instantiation (e.g., `Word64Interface`), documented once in `Word64.agda`.

### 2. No TrivialContract

**TrivialContract has been eliminated.** It was a design smell:

- TrivialContract produced empty programs (`[]`)
- ContractInterface required `contract-nonempty : length (contract-program c) ≥ 1`
- This was resolved via a **postulate asserting a falsehood**

The correct solution: modules either use real contracts (for compilation) or work directly with semantic functions (for reasoning). There is no "trivial" middle ground that lies about its capabilities.

### 3. Portable Proofs via Parameterization

Word size is a **backend detail**, not visible to core logic:

```agda
-- Core modules are PARAMETERIZED by MachineInterface:
module CoreProof (MI : MachineInterface) where
  open import Once.SemanticBaseMachine MI
  open import Once.IRMachine MI
  -- ... proofs work for ANY word size ...

-- Only at the EDGE do we instantiate:
open import Once.Backend.Word64 using (Word64Interface)
open import CoreProof Word64Interface  -- x86-64
-- or
open import Once.Backend.Word32 using (Word32Interface)
open import CoreProof Word32Interface  -- 32-bit targets
```

Benefits:
- Proofs written **once**, portable across word sizes
- Switching x86-64 → RISC-V 32-bit changes only the **instantiation**
- Clean separation of concerns

### 4. Single Source of ⟦_⟧ (Critical for Agda)

**Submodules must NOT import `SemanticBaseMachine MI` internally.**

When multiple modules each import `SemanticBaseMachine MI`, Agda treats each import as a separate instantiation. Even with the same `MI`, the `⟦_⟧` from different imports are not automatically unified.

**WRONG (creates multiple copies of ⟦_⟧):**
```agda
module ContractInterfaceMachine (MI : MachineInterface) where
  open import Once.SemanticBaseMachine MI using (⟦_⟧)  -- copy 1
  ...

module ArithContracts (MI : MachineInterface) where
  open import Once.SemanticBaseMachine MI using (⟦_⟧)  -- copy 2
  ...

module BoundaryMachine where
  open import ContractInterfaceMachine Word64Interface  -- uses copy 1
  open import ArithContracts Word64Interface            -- uses copy 2
  -- Agda can't unify them!
```

**CORRECT (single source of ⟦_⟧):**
```agda
-- Submodules receive ⟦_⟧ as a parameter, don't import it
module ContractInterfaceMachine (⟦_⟧ : Type → Set) where
  ...

module ArithContracts (⟦_⟧ : Type → Set) where
  ...

-- Parent module imports SemanticBaseMachine ONCE and passes ⟦_⟧ down
module BoundaryMachine (MI : MachineInterface) where
  open import Once.SemanticBaseMachine MI using (⟦_⟧)  -- ONE import
  open ContractInterfaceMachine ⟦_⟧                     -- pass it down
  open ArithContracts ⟦_⟧                               -- pass it down
  -- Everything shares the same ⟦_⟧
```

This pattern:
- Keeps modules portable (parameterized by `⟦_⟧`, not by `MI`)
- Avoids Agda's module instantiation issues
- Makes dependencies explicit

## Architecture

### Module Stack

```
┌─────────────────────────────────────────────────────────────┐
│                    Backend Instantiation                     │
│  (Word64Interface for x86-64, Word32Interface for 32-bit)   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│              Parameterized Core (MI : MachineInterface)      │
│                                                              │
│   SemanticBaseMachine MI    ⟦ Int ⟧ = Word                  │
│   ContractInterfaceMachine MI                                │
│   IRMachine MI                                               │
│   MachineContracts MI                                        │
│   BoundaryMachine MI                                         │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                    MachineInterface                          │
│                                                              │
│   Word : Set                                                 │
│   word-add, word-sub, word-mul, ... : Word × Word → Word    │
│   word-lt, word-eq, ... : Word × Word → Word                │
└─────────────────────────────────────────────────────────────┘
```

### Trust Boundary

The **only** trust is in `MachineInterface` instantiation:

```agda
-- Word64.agda documents the trust:
--   word64-add (a, b)  ≡  x86 ADD instruction (modulo 2^64)
--   word64-sub (a, b)  ≡  x86 SUB instruction (modulo 2^64)
--   word64-mul (a, b)  ≡  x86 IMUL instruction (low 64 bits)
--   etc.
```

This is stated **once**, not scattered across multiple files with encode postulates.

### Compilation Flow

```
Source Code
    │
    ▼
Elaborator (recognizes arithmetic patterns)
    │
    ├──► Arith Compiler ──► (Program, PrimContract proof)
    │                                    │
    ▼                                    ▼
CCC Compiler ◄───────────────────────────┘
    │         receives proven assembly block directly
    ▼
x86/AArch64/RISC-V Code
```

Key points:
- CCC receives **proven assembly blocks directly** - no string-named Prim indirection
- The `PrimContract` IS the proof (Agda-verified), not a claim to be trusted
- No postulates required

## Design

### ContractInterface (Parameterized by ⟦_⟧)

```agda
-- NOTE: Parameterized by ⟦_⟧ directly, NOT by MachineInterface
-- This avoids multiple-instantiation issues
module Once.Backend.ContractInterfaceMachine (⟦_⟧ : Type → Set) where

  record ContractInterface : Set₁ where
    field
      Contract : ∀ {A B : Type} → (⟦ A ⟧ → ⟦ B ⟧) → Set
      contract-length : ∀ {A B} {sem : ⟦ A ⟧ → ⟦ B ⟧} → Contract sem → ℕ
      contract-assembly : ∀ {A B} {sem : ⟦ A ⟧ → ⟦ B ⟧} → Contract sem → List Instr
```

### IR with Explicit Semantics

```agda
-- Parameterized by ⟦_⟧, receives it from parent
module Once.IRMachine (⟦_⟧ : Type → Set) where

  module IRDef (CI : ContractInterface) where
    open ContractInterface CI

    data IR : Type → Type → Set where
      -- ... standard CCC constructors ...

      -- Primitives carry explicit semantics and contract
      Prim : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) → Contract sem → IR A B
```

The `sem` field makes evaluation trivial: `eval (Prim _ sem _) x = sem x`

### MachineContracts (Word-Specialized Contracts)

```agda
-- Semantic functions use MachineInterface for word operations
module Once.Arith.MachineContracts where

  module Semantics (MI : MachineInterface) where
    open MachineInterface MI

    -- Semantic functions ARE the machine operations
    add-int-sem : Word × Word → Word
    add-int-sem = word-add  -- No encode gap!

  -- Contract record uses Word directly, avoiding ⟦_⟧ unification issues
  module ArithContracts (MI : MachineInterface) where
    open MachineInterface MI
    open Semantics MI

    -- Word-specialized contract types avoid ⟦_⟧ module instantiation issues
    record ArithMachineContracts
        (BinOpContract : (Word × Word → Word) → Set)
        (UnaryOpContract : (Word → Word) → Set)
        (ConstContract : ∀ (n : Word) → (⊤ → Word) → Set)
        : Set₁ where
      field
        add-int-contract : BinOpContract add-int-sem
        neg-int-contract : UnaryOpContract neg-int-sem
        const-int-contract : ∀ (n : Word) → ConstContract n (const-int-sem n)
        -- etc.
```

### BoundaryMachine (Portable, Parameterized by MI)

```agda
module Once.Arith.BoundaryMachine (MI : MachineInterface) where
  -- Import SemanticBaseMachine MI for ⟦_⟧
  open import Once.SemanticBaseMachine MI using (⟦_⟧)

  -- Pass ⟦_⟧ to ContractInterfaceMachine and IRMachine
  open import Once.Backend.ContractInterfaceMachine ⟦_⟧
  open import Once.IRMachine ⟦_⟧
  open import Once.Arith.MachineContracts using (module Semantics; module ArithContracts)
  open ArithContracts MI

  -- Define IntWord from MachineInterface
  private IntWord = MachineInterface.Word MI

  -- Specialize contract types: this works because ⟦ Int ⟧ = IntWord
  module _ (CI : ContractInterface) where
    open ContractInterface CI
    BinOpContract : (IntWord × IntWord → IntWord) → Set
    BinOpContract = Contract {Int * Int} {Int}
    -- etc.

  module EmbedDef (CI : ContractInterface)
      (contracts : ArithMachineContracts (BinOpContract CI) ...) where
    ...
```

**Key insight**: The `ArithMachineContracts` record uses `Word` directly instead of `⟦_⟧`. The caller (`BoundaryMachine`) then specializes `ContractInterface.Contract` to `Word` types. This works because `⟦ Int ⟧ = Word` by definition in `SemanticBaseMachine MI`, allowing the type checker to unify them.

## Implementation Status

### Phase 1: Define Interfaces ✓
- [x] `MachineInterface` - parameterized word operations
- [x] `Word64Interface`, `Word32Interface` - concrete instantiations
- [x] `SemanticBaseMachine` - `⟦_⟧` parameterized by MachineInterface

### Phase 2: Migration ✓
- [x] Update Makefile to use machine-based files
- [x] Remove TrivialContract (was hiding a false postulate)
- [x] Remove default TrivialInterface instantiations
- [x] **Restructure modules for portability**
  - [x] `ContractInterfaceMachine` - parameterize by ⟦_⟧
  - [x] `IRMachine` - parameterize by ⟦_⟧
  - [x] `ArithContracts` - use Word-specialized contract types
  - [x] `BoundaryMachine` - parameterize by MI, specialize contracts
- [x] Add `word-to-ℕ` to MachineInterface (eliminates encode-int postulate)
- [x] Integrate with x86 backend (instantiate with Word64Interface)
- [x] Test full compilation pipeline (make x86-compiler passes)

### Phase 3: Eliminate Old Infrastructure
- [ ] Delete `Once/SemanticBase.agda` (uses ℤ)
- [ ] Delete `Once/Backend/ContractInterface.agda` (has postulate)
- [ ] Delete `Once/IR.agda` (uses old SemanticBase)
- [ ] Delete `Once/Arith/Contracts.agda` (uses ℤ)
- [ ] Delete `Once/Arith/Boundary.agda` (uses old stack)

### Phase 4: Proven Arithmetic Contracts
- [ ] `add-int-contract` - proven correct (no postulates)
- [ ] `sub-int-contract`
- [ ] `mul-int-contract`
- [ ] Remaining operations

## Files

### New (Machine-based)
- `Once/Backend/MachineInterface.agda` - word operation interface
- `Once/Backend/Word64.agda` - 64-bit instantiation
- `Once/Backend/Word32.agda` - 32-bit instantiation
- `Once/SemanticBaseMachine.agda` - parameterized type interpretation
- `Once/Backend/ContractInterfaceMachine.agda` - parameterized contracts
- `Once/IRMachine.agda` - parameterized IR
- `Once/Arith/MachineContracts.agda` - arithmetic contracts
- `Once/Arith/BoundaryMachine.agda` - Arith→IR embedding

### To Delete (ℤ-based, has postulates)
- `Once/SemanticBase.agda`
- `Once/Backend/ContractInterface.agda`
- `Once/IR.agda`
- `Once/Arith/Contracts.agda`
- `Once/Arith/Boundary.agda`

## Related Work

- **OCP-0001**: Orthogonal Arithmetic Compiler
- **OCP-0002**: Type conversion support in Arith
