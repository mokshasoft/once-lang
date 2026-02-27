# X86v3 Prim Proof Architecture

## Problem Statement

Eliminate all postulates in the Arith X86v3 primitive proofs while trusting **only** CPU instruction semantics.

### Trust Boundary

The only trust should be:
- **CPU instruction semantics**: ADD, SUB, MUL, etc. do what we expect
- **2's complement arithmetic model**: defined in Word64.agda

Everything else should be proven.

## The Core Issue

### What CCC Needs

When CCC executes a `Prim`, it needs a proof that produces `IRResultAWF`, which includes:

```agda
result-valid-wf : ValidAtWF m alloc {B} (eval ir x) result-loc s
```

### What ValidAtWF Requires

For primitive types (Int, Float, Str, Buffer), `ValidAtWF` only needs `BeforeFrontier`:

```agda
valid-int-wf : BeforeFrontier alloc loc → ValidAtWF m alloc {Int} n loc s
valid-float-wf : BeforeFrontier alloc loc → ValidAtWF m alloc {Float} x loc s
-- etc.
```

For compound types (pairs, sums, closures), `ValidAtWF` requires structural proofs (both components valid, etc.).

### The Type Dispatch Problem

The original postulate was:

```agda
postulate
  arith-result-valid : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    {alloc} {result-loc} {s} →
    BeforeFrontier alloc result-loc →
    ValidAtWF m alloc {B} (sem x) result-loc s
```

This postulate exists because:
1. We have `BeforeFrontier` (sufficient for primitives)
2. We have `valid-int-wf`, `valid-float-wf`, etc.
3. But `B` is abstract - we can't dispatch to the right constructor

## Key Insight: CPUs Only Produce Primitive Types

CPUs don't create ADTs. They only produce:
- Integers (via arithmetic, comparisons)
- Floats (via FP operations)
- Addresses/pointers (primitive at machine level)

ADT construction (pairs, sums, closures) is done by IR composition, not CPU primitives.

Therefore, any `Prim` that interfaces with the CPU will have a primitive output type.

## Solution Approaches

### Approach 1: IsPrimitive Evidence in Contract (Rejected)

Add evidence to `PrimContractV3`:

```agda
record PrimContractV3 (A B : Type) : Set where
  field
    stack-requirement : ℕ
    output-mode : AllocMode
    output-primitive : IsPrimitive B  -- Evidence here
```

**Problem**: CCC doesn't need to know about `IsPrimitive`. This leaks Arith-specific knowledge into the generic interface.

### Approach 2: IsPrimitive in Prim Constructor (Rejected)

Embed evidence in IR:

```agda
Prim : ∀ {A B} → String → (⟦ A ⟧ → ⟦ B ⟧) → PrimContractV3 A B → IsPrimitive B → IR A B
```

**Problem**: Same as above - CCC shouldn't need to handle `IsPrimitive`.

### Approach 3: Concrete Proofs per Primitive (Recommended)

Each primitive has its own proof at concrete types:

```agda
-- Arith defines concrete primitive
add-int-sem : ⟦ Int * Int ⟧ → ⟦ Int ⟧
add-int-sem (a , b) = a + b

add-int-contract : PrimContractV3 (Int * Int) Int
add-int-contract = record { ... }

-- Proof knows B = Int, can use valid-int-wf directly
add-int-proof : PrimProofV3 add-int-sem add-int-contract (Prim "add-int" ...)
add-int-proof mIn x input-loc s alloc ... =
  record
    { ...
    ; result-valid-wf = valid-int-wf result-before  -- No dispatch needed!
    ; ...
    }
```

**Advantage**: No `IsPrimitive` needed anywhere. The proof is written at concrete types where `B = Int` is known.

## Architecture Options for CCC Integration

Given concrete proofs per primitive, how does CCC use them?

### Option A: Registry/Lookup

CCC maintains a registry of primitives and their proofs. When processing `Prim name sem c`, it looks up the proof by name.

```agda
PrimRegistry : Set
PrimRegistry = List (∃ λ A → ∃ λ B → Σ (PrimDef A B) (PrimProof A B))

lookupPrimProof : PrimRegistry → String → Maybe (∃ PrimProof)
```

**Tradeoff**: Runtime lookup, need to handle "not found" case.

### Option B: Proof Embedded in IR

`Prim` carries its proof directly:

```agda
Prim : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) (c : PrimContractV3 A B)
     → PrimProofV3 sem c (Prim name sem c)
     → IR A B
```

**Tradeoff**: Changes IR structure, proof is part of syntax.

### Option C: Module Parameterization

CCC is parameterized by a record containing all primitive proofs:

```agda
record ArithProofs : Set where
  field
    add-int-proof : PrimProofV3 add-int-sem add-int-contract ...
    sub-int-proof : PrimProofV3 sub-int-sem sub-int-contract ...
    -- etc.

module CCC (arith : ArithProofs) where
  -- Use arith.add-int-proof when processing add-int Prim
```

**Tradeoff**: Static, all primitives known at module instantiation.

### Option D: Generic Provider with Evidence Parameter

Keep generic `PrimProofProviderV3` but pass evidence:

```agda
PrimProofProviderV3 : Set
PrimProofProviderV3 = ∀ {A B} (is-prim : IsPrimitive B)
  (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) (c : PrimContractV3 A B) →
  PrimProofV3 sem c (Prim name sem c)
```

Caller provides evidence. For Arith primitives, evidence comes from concrete definitions.

**Tradeoff**: Caller must have evidence, but this is available at Prim construction time.

## Comparison with X86 Architecture

X86 on `x86-arch-clean` branch uses:

1. **Word64.agda**: Defines CPU operations (trust boundary)
   ```agda
   word64-add : ℕ × ℕ → ℕ
   word64-add (a , b) = (a + b) % 2^64  -- DEFINED, not postulated
   ```

2. **MachineContract**: Per-primitive contracts with trivial correctness
   ```agda
   record X86MachineContract (sem : A → B) : Set where
     field
       assembly : List String
       correct : ⊤  -- Trivial! Trust is in Word64
   ```

3. **PrimProofProvider postulate at CCC boundary**:
   ```agda
   postulate
     prim-proof : PrimProofProvider
   ```

X86 still has a postulate, but it's at the module boundary - domain compilers provide the implementation.

## Recommended Architecture for X86v3

1. **Keep `PrimContractV3` generic** (no `IsPrimitive`)

2. **Define `IsPrimitive` in IR.agda** (available for domain compilers)

3. **Arith defines concrete primitives with evidence**:
   ```agda
   record ArithPrimitive (A B : Type) : Set where
     field
       name : String
       sem : ⟦ A ⟧ → ⟦ B ⟧
       contract : PrimContractV3 A B
       is-prim : IsPrimitive B
   ```

4. **Arith provides concrete proofs**:
   ```agda
   add-int-proof : PrimProofV3 (sem add-int-prim) (contract add-int-prim) ...
   add-int-proof = ... valid-int-wf ...  -- Uses is-int directly
   ```

5. **CCC integration via Option C or D** (module param or evidence param)

## Summary

| Aspect | Postulate Approach | IsPrimitive Approach |
|--------|-------------------|---------------------|
| Trust boundary | Unclear | CPU semantics only |
| CCC knowledge | Opaque | Still opaque |
| Type dispatch | Postulated | Via IsPrimitive evidence |
| Where evidence lives | N/A | ArithPrimitive record |
| Proof structure | Generic | Concrete per primitive |

The key insight is that **concrete proofs at concrete types** don't need type dispatch. The `IsPrimitive` evidence is only needed if we want a single generic proof function, and even then, it stays within the domain compiler (Arith), not in CCC.
