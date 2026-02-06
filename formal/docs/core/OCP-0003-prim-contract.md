# OCP-0003: PrimContract - Unified Interface for Domain Compilers

## Status

**Complete** - Non-indexed contract design implemented and operational.

## Summary

Define `PrimContract` as a uniform interface that domain compilers (Arith, future Loop compiler, IO) must satisfy. Primitives carry their semantics explicitly, and domain compilers provide correctness proofs via `PrimProofProvider`.

## Architecture

### Non-Indexed Contract Design

The key design decision: **Contract is NOT indexed by semantics**.

```agda
-- Once.Contract
record ContractInterface : Set₁ where
  field
    Contract : (A B : Type) → Set           -- Just types, no semantics index
    contract-assembly : Contract A B → List String
    contract-nonempty : length (contract-assembly c) ≥ 1
```

Semantics are passed explicitly to `Prim`:

```agda
-- Once.IR ⟦_⟧
Prim : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) → Contract A B → IR A B
```

This design:
- Keeps `Contract` simple (just assembly + structural properties)
- Makes semantics explicit at the IR level
- Allows `eval (Prim _ sem _) x = sem x` trivially
- Enables domain compilers to pair any semantics with any contract

### Module Structure

```
Once.Contract                    -- ContractInterface (non-indexed)
Once.IR ⟦_⟧                      -- IR parameterized by type interpretation
Once.Semantics MI                -- eval function, Closure-η lemma
Once.SemanticBaseMachine MI      -- ⟦_⟧ type interpretation from MachineInterface

Once.Arith.Contracts             -- ArithContractsRecord (non-indexed)
Once.Arith.Boundary MI           -- embedArith : ArithIR → IR

Once.Backend.Common.PrimContract -- Architecture-independent contract record
Once.Backend.X86.Correct.StarBase -- PrimProofProvider pattern
```

### Two-Stage IR

```
SurfaceIR (CCC + Let + Prim[semantics])
    │
    ▼  Desugar (eliminates Let, compiles primitives)
    │
IR (CCC + Prim[name, sem, contract])
    │
    ▼  CCC Compiler (domain-agnostic composition)
    │
Assembly
```

## Core Principles

### 1. No Postulates for Arithmetic

The semantic foundation uses **MachineInterface** directly:

```agda
⟦ Int ⟧ = Word  (from MachineInterface, not ℤ)
```

This eliminates the "encode gap":
- **Old approach**: `⟦ Int ⟧ = ℤ`, requiring `postulate encode-add : encode a + encode b ≡ encode (a + b)`
- **Current approach**: `⟦ Int ⟧ = Word`, where `word-add` IS the semantic operation

The only trust is in `MachineInterface` instantiation (e.g., `Word64Interface`).

### 2. Orthogonal Proof Obligations

Domain compilers must satisfy two independent requirements:

**CCC Invariant Preservation:**
- Preserve registers: {r14, r15, rbp}
- Preserve rsp (or restore it)
- Don't corrupt stack/heap memory regions
- CCC verifies this via `PrimProofProvider`

**Semantic Correctness:**
- Assembly implements the semantic function correctly
- `rax` contains `sem(input)` after execution
- Domain compiler proves this internally

These are orthogonal: CCC doesn't know what `add` computes, only that it preserves invariants.

### 3. PrimProofProvider Pattern

In `StarBase.agda`, correctness proofs are provided via parameterization:

```agda
-- Type of proof for a single Prim
PrimProof : ∀ {A B} → (⟦ A ⟧ → ⟦ B ⟧) → PrimContract A B → Set₁

-- Provider maps any contract to its proof
PrimProofProvider : Set₁
PrimProofProvider = ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (c : PrimContract A B) → PrimProof sem c

-- MutualIR is parameterized by the provider
module MutualIR (prim-proof : PrimProofProvider) where
  -- Dispatcher uses prim-proof for Prim cases
```

Domain compilers instantiate `MutualIR` with their proof provider.

### 4. Portable Proofs via Parameterization

Word size is a **backend detail**, not visible to core logic:

```agda
-- Core modules parameterized by MachineInterface
module Once.Arith.Boundary (MI : MachineInterface) where
  open import Once.SemanticBaseMachine MI using (⟦_⟧)
  -- Works for any word size

-- Instantiated at edges
open import Once.Backend.Word64 using (Word64Interface)
open import Once.Arith.Boundary Word64Interface  -- x86-64
```

## Implementation

### Arithmetic Domain Compiler

```agda
-- Once.Arith.Contracts
record ArithContractsRecord : Set where
  field
    add-int-contract : Contract (Int * Int) Int
    sub-int-contract : Contract (Int * Int) Int
    -- etc.

-- Once.Arith.Boundary
prim-add : IR (Int * Int) Int
prim-add = Prim "arith.add" add-int-sem add-int-contract
```

### CCC Backend

```agda
-- Once.Backend.X86.Correct.StarBase
run-prim-star-vv : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧)
                   (contract : Contract A B) ... →
  ∃[ s' ] IRStarResultV (Prim name sem contract) prog s s' x offset

-- With PrimProofProvider
run-prim-star-vv-auto name sem contract ... =
  prim-proof sem contract name ...
```

## Files

### Core Infrastructure
- `Once/Contract.agda` - ContractInterface (non-indexed)
- `Once/IR.agda` - IR with Prim(name, sem, contract)
- `Once/Semantics.agda` - eval function, Closure-η
- `Once/SemanticBaseMachine.agda` - ⟦_⟧ from MachineInterface
- `Once/Backend/MachineInterface.agda` - Word operations interface
- `Once/Backend/Word64.agda` - 64-bit instantiation

### Arithmetic Compiler
- `Once/Arith/Contracts.agda` - ArithContractsRecord (non-indexed)
- `Once/Arith/Boundary.agda` - embedArith using Prim

### X86 Backend
- `Once/Backend/Common/PrimContract.agda` - PrimContract record
- `Once/Backend/X86/Correct/StarBase.agda` - PrimProofProvider, run-prim-star-vv
- `Once/Backend/X86/Correct/MutualIR.agda` - Dispatcher parameterized by proofs

## Design Rationale

### Why Non-Indexed Contracts?

**Indexed approach** (`Contract {A} {B} sem`):
- Contract type includes semantics in its index
- Type system enforces contract matches semantics
- More complex module structure needed

**Non-indexed approach** (`Contract A B`):
- Simpler types and modules
- Semantics explicit in Prim constructor
- Pairing happens at IR construction, not type level
- Easier to work with in Agda (fewer unification issues)

### Why PrimProofProvider?

Instead of embedding proofs in IR or Contract:
- Keeps IR clean (no proof terms in AST)
- Allows different proof strategies per backend
- CCC compiler receives proofs via parameterization
- Domain compilers provide proofs when instantiating

## Related Work

- **OCP-0001**: Orthogonal Arithmetic Compiler
- **OCP-0002**: Type conversion support in Arith
