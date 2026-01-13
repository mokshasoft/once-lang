# Validity-Based Correctness Architecture

## Overview

This document describes the validity-based approach to proving x86-64 backend correctness, which replaces the encode-based approach that required 10+ postulates about memory layout.

## The Problem with Encode-Based Correctness

The original correctness statement used the abstract `encode` function:

```agda
record IRStarResult {A B : Type} (ir : IR A B) (prog : Program)
                    (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
  field
    ir-rax : readReg (regs s') rax ≡ encode (eval ir x)  -- ← Problem
    ...
```

This statement says "rax contains the encoded representation of the semantic result." But this requires:

1. An abstract `encode : ⟦ A ⟧ → Word` function that returns addresses
2. Postulates about what's at those addresses:
   - `encode-pair-fst : readMem m (encode (a, b)) ≡ just (encode a)`
   - `encode-pair-snd : readMem m (encode (a, b) +ℕ 8) ≡ just (encode b)`
   - `encode-inl-tag : readMem m (encode (inj₁ a)) ≡ just 0`
   - `encode-inl-val : readMem m (encode (inj₁ a) +ℕ 8) ≡ just (encode a)`
   - ... (10 total encoding postulates)

### The Heap/Stack Contradiction

Worse, these postulates led to a contradiction:
- `encode-in-heap` postulated that encoded values are in the heap region
- But the compiler allocates pairs/sums on the **stack** at `rsp - k`
- `encode-inl-construct` claimed `new-rsp ≡ encode (inj₁ x)`
- This is contradictory if stack and heap are disjoint regions!

## The Validity-Based Solution

Instead of claiming "rax equals some abstract encode address", we directly prove "the result value is correctly represented at rax in memory":

```agda
-- NEW: Validity-based correctness statement
record IRStarResultV {A B : Type} (ir : IR A B) (prog : Program)
                     (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
  field
    ir-result-valid : ValidAt (eval ir x) (readReg (regs s') rax) (memory s')
    ...
```

### The ValidAt Predicate

`ValidAt` is a type family that says "value v is correctly represented at address a in memory m":

```agda
data ValidAt : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set where
  -- Unit: value 0, no memory needed
  valid-unit : ∀ m → ValidAt tt 0 m

  -- Pair: both components valid at their addresses, pair structure at addr
  valid-pair : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr-a addr-b addr : Word} {m} →
    ValidAt a addr-a m →
    ValidAt b addr-b m →
    PairAtS addr-a addr-b addr m →  -- Memory layout: [addr-a, addr-b] at addr
    ValidAt (a , b) addr m

  -- Left sum: tag=0, value valid
  valid-inl : ∀ {A B} {a : ⟦ A ⟧} {addr-a addr : Word} {m} →
    ValidAt a addr-a m →
    InlAtS addr-a addr m →  -- Memory layout: [0, addr-a] at addr
    ValidAt {A + B} (inj₁ a) addr m

  -- Right sum: tag=1, value valid
  valid-inr : ∀ {A B} {b : ⟦ B ⟧} {addr-b addr : Word} {m} →
    ValidAt b addr-b m →
    InrAtS addr-b addr m →  -- Memory layout: [1, addr-b] at addr
    ValidAt {A + B} (inj₂ b) addr m

  -- Closure: env and code-ptr at addr
  valid-closure : ∀ {A B} {cl : Closure A B} {addr : Word} {m} →
    ClosureAtS (Closure.env-addr cl) (Closure.code-ptr cl) addr m →
    ValidAt cl addr m

  -- Fix: validity of unwrapped value
  valid-fix : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m} →
    ValidAt x addr m →
    ValidAt (wrap x) addr m
```

### Memory Layout Predicates

The `*AtS` predicates capture concrete memory layout (already exist in MemoryValid.agda):

```agda
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ slot-size) ≡ just addr-b

record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ slot-size) ≡ just addr-val

record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  field
    tag-valid : readMem m addr-sum ≡ just 1
    val-valid : readMem m (addr-sum +ℕ slot-size) ≡ just addr-val

record ClosureAtS (env-addr code-ptr addr-closure : Word) (m : Memory) : Set where
  field
    env-valid : readMem m addr-closure ≡ just env-addr
    code-valid : readMem m (addr-closure +ℕ slot-size) ≡ just code-ptr
```

## Why This Works

### Producers Create Validity

When the compiler allocates a pair on the stack:
```agda
-- In IR/Pair.agda:
-- After executing: mov [rsp-40], rax-a ; mov [rsp-40+8], rax-b
pair-at : PairAtS addr-a addr-b new-rsp (memory s')
pair-at = pair-at-s mem-write-a mem-write-b  -- PROVEN from actual writes

result-valid : ValidAt (a, b) new-rsp (memory s')
result-valid = valid-pair valid-a valid-b pair-at  -- PROVEN, not postulated
```

### Consumers Use Validity

When the compiler reads a pair component:
```agda
-- In run-fst-star-v:
-- Precondition: ValidAt (a, b) addr m
-- Extract: PairAtS addr-a addr-b addr m
-- Use fst-valid to prove: readMem m addr ≡ just addr-a
```

### No Encode Function Needed

The key insight: we never need to talk about `encode` at all. We just prove:
1. **Producers**: After allocation, memory satisfies `ValidAt`
2. **Consumers**: Given `ValidAt`, we can read from memory correctly
3. **Composition**: `ValidAt` threads through naturally

## Benefits

1. **No encode postulates** - Memory layout proven from writes, not assumed
2. **More direct** - Says what we mean without abstraction indirection
3. **Composable** - Validity threads through IR composition naturally
4. **No heap/stack confusion** - Allocation location doesn't matter, only memory layout
5. **Future-proof** - Works with both stack allocation (current) and heap allocation (escape analysis)

## Relationship to Existing Infrastructure

This approach builds on:

- **D041 Region Abstractions** - Stack/heap/code disjointness for memory preservation
- **MemoryValid.agda** - PairAtS, InlAtS, InrAtS already exist
- **StatefulEncoding.agda** - Proven encoding theorems (validates the approach)
- **ClosureWellFormed** - Already tracks closure validity separately

## Migration Path

### Phase 1: Add ClosureAtS and ValidAt to MemoryValid.agda
### Phase 2: Define IRStarResultV in StarBase.agda
### Phase 3: Migrate producers (inl, inr, pair, curry) to emit validity
### Phase 4: Migrate consumers (fst, snd, case, apply) to use validity
### Phase 5: Thread validity through composition
### Phase 6: Remove encode postulates from Postulates.agda

## Key Files

| File | Role |
|------|------|
| `Once/Backend/X86/Correct/MemoryValid.agda` | ValidAt, *AtS predicates |
| `Once/Backend/X86/Correct/StarBase.agda` | IRStarResultV, IRRunnerV |
| `Once/Backend/X86/Correct/IR/Inl.agda` | Emit InlAtS + valid-inl |
| `Once/Backend/X86/Correct/IR/Inr.agda` | Emit InrAtS + valid-inr |
| `Once/Backend/X86/Correct/IR/Pair.agda` | Emit PairAtS + valid-pair |
| `Once/Backend/X86/Correct/IR/Curry.agda` | Emit ClosureAtS + valid-closure |
| `Once/Backend/X86/Correct/MutualIR.agda` | Thread validity through composition |

## Summary

The shift from encode-based to validity-based correctness:

| Aspect | Encode-Based | Validity-Based |
|--------|--------------|----------------|
| Statement | `rax ≡ encode (eval ir x)` | `ValidAt (eval ir x) rax memory` |
| Proof method | Postulate layout properties | Derive from actual writes |
| Abstraction | Abstract `encode` function | Direct memory predicates |
| Heap/stack | Must be in heap (contradiction!) | Location-agnostic |
| Postulates needed | 10+ encoding postulates | 0 |

The key insight: **instead of "address equals abstract encode," we prove "memory at address represents value."**
