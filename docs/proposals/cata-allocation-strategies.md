# Cata Allocation Strategies

## Overview

Catamorphism (cata) folds a finite inductive structure `μF` into a result `A`:

```
cata : (F A → A) → μF → A
```

Because the input is finite and its size is known before traversal, allocation can be optimized.

**Architecture note**: These optimizations happen during *translation* from TreeTrace
(proof layer) to AbstractTrace (operational layer). TreeTrace proves correctness via
structural induction; the translator chooses execution strategy based on linearity and
algebra category. AbstractTrace then maps 1-to-1 to machine instructions.
See "Three-Layer Architecture" below.

## Baseline: Frontier Allocation (Unoptimized)

Before discussing optimizations, we define the baseline unoptimized implementation.
This is what the Agda proofs verify, and what optimized versions must semantically match.

### Core Model

The unoptimized cata processes **one element at a time**, allocating at the stack frontier:

```
┌─────────────────────────────────────────┐
│  Stack Frame                            │
├─────────────────────────────────────────┤
│  ... previous data ...                  │
├─────────────────────────────────────────┤
│  ← frontier (next-slot)                 │
│                                         │
│  (available space for allocation)       │
│                                         │
└─────────────────────────────────────────┘
```

**Key principle**: Allocation always happens at the frontier. The frontier advances
when slots are allocated, and can recede when temporary slots are reclaimed.

### Two Types of Slots

1. **Temporary slots** (for traversal):
   - Product save-slots: save pointer while processing left, restore for right
   - Reclaimed after use (frontier recedes)
   - Budget: `product-depth wfG` slots maximum at any time

2. **Output slots** (for results):
   - Allocated by the algebra as it produces output
   - Persist after cata completes
   - Size depends on algebra semantics (0 for fold, n for map, etc.)

### Processing Flow

```
cata alg (In layer) =
  1. Traverse layer structure (using temporary slots)
     - Product: save pointer, process left, reclaim, process right
     - Sum: dispatch on tag
     - Id: recursively call cata (temporary slots reclaimed after)
     - K: base value, no slots needed

  2. Apply algebra to processed layer
     - Algebra receives: ⟦F⟧ A (layer with recursive results filled in)
     - Algebra allocates: output slots at frontier as needed
     - Algebra returns: result location
```

### Slot Reclamation

The key insight enabling bounded stack usage:

```
Processing Product (left, right):

  frontier →  ┌─────────────┐
              │ save-slot   │  ← save pointer to (left, right)
              ├─────────────┤
              │             │  ← process left (may use more slots)
              │   ...       │
              └─────────────┘
                    ↓
              (left complete, RECLAIM temporary slots)
                    ↓
  frontier →  ┌─────────────┐
              │ save-slot   │  ← still holding pointer
              ├─────────────┤
              │             │  ← process right (REUSES same space)
              │   ...       │
              └─────────────┘
                    ↓
              (right complete, RECLAIM save-slot too)
                    ↓
  frontier →  ┌─────────────┐
              │             │  ← pair results, continue
              └─────────────┘
```

Left and right **share** temporary slot space, not **add** to each other.

### Algebra Allocates Output

The algebra is responsible for output allocation:

```agda
-- Filter: conditionally allocate
filter-alg : F (List A) → List A
filter-alg (Nil)        = []                    -- 0 slots
filter-alg (Cons x xs)  = if p x
                          then alloc-cons x xs  -- 1 slot (at frontier)
                          else xs               -- 0 slots

-- Map: always allocate
map-alg : F (List B) → List B
map-alg (Nil)       = alloc-nil               -- 1 slot
map-alg (Cons x xs) = alloc-cons (f x) xs     -- 1 slot

-- Fold: no allocation (accumulator in register)
sum-alg : F Int → Int
sum-alg (Nil)       = 0                       -- 0 slots
sum-alg (Cons x xs) = x + xs                  -- 0 slots
```

### Capacity Requirements

For unoptimized cata with functor G and algebra alg:

```
Total capacity = product-depth wfG     -- temporary (shared, reclaimed)
               + output-slots(alg)     -- depends on input size & algebra
               + pair-slots            -- for pairing results
```

The `product-depth wfG` portion is **bounded** regardless of input size.
The `output-slots(alg)` grows with output, allocated incrementally at frontier.

### Why This Model?

1. **Simple to prove correct**: Structural induction on μ-values
2. **Baseline for optimization**: Optimized versions must produce same results
3. **No pre-allocation guessing**: Output allocated as produced
4. **Bounded temporary space**: Only `product-depth` slots for traversal
5. **Works for any algebra**: No static analysis required

The optimizations below transform this baseline into more efficient implementations
when static analysis can determine algebra properties.

---

## Key Insight

Allocation strategy is determined by pattern matching on **linearity** and **algebra**:

| Match | Strategy |
|-------|----------|
| Linear (any algebra) | 0 allocations (reuse in-place) |
| Non-linear + known algebra | 1 bulk allocation (exact size) |
| Non-linear + unknown algebra | Frontier allocation (baseline) |

The compiler recognizes known algebras (map, fold, etc.) and their output sizes.
Unknown algebras use the baseline frontier allocation - no guessing.

## Output Size Categories

The algebra `F A → A` determines the relationship between input and output size:

| Category | Output vs Input | Example |
|----------|-----------------|---------|
| Collapsing | O(1) | `sum`, `length`, `all` |
| Preserving | = input | `map f` |
| Shrinking | ≤ input | `filter p` |
| Growing | > input | `duplicate`, `flatMap` |

## Static Analysis

The compiler analyzes the algebra's structure to determine its category.

### Analysis Rules

**Collapsing**: Result type `A` is not `μF`
```
A ≠ μF  →  collapsing
```

**Preserving**: Each constructor maps to same constructor
```
Nil  → Nil
Cons → Cons
```

**Shrinking**: Constructor can map to recursive result (skipping)
```
Cons x xs → xs   (possible branch)
```

**Growing**: Constructor can produce multiple constructors
```
Cons x xs → Cons x (Cons x xs)
```

### Analysis Algorithm

For each constructor `C` in functor `F`, examine all code paths in the algebra:

1. If `A ≠ μF`: **collapsing**
2. Else for each constructor `C`:
   - If any path maps `C` to different constructor: **shrinking** or **growing**
   - If any path produces more constructors than input: **growing**
   - If all paths preserve constructor: **preserving**

## Allocation Strategy by Category

### Collapsing (e.g., `sum`)

Output is O(1) regardless of input.

| Linearity | Strategy |
|-----------|----------|
| Linear | 0 allocations, traverse and accumulate |
| Non-linear | 0 allocations, traverse and accumulate |

When `A` is a scalar type (Int, Bool, etc.), no heap allocation is needed - the result is returned in a register.

### Preserving (e.g., `map`)

Output size equals input size.

| Linearity | Strategy |
|-----------|----------|
| Linear | 0 allocations, update payloads in-place |
| Non-linear | 1 allocation, bulk allocate output structure |

### Shrinking (e.g., `filter`)

Output size ≤ input size, but unknown until traversal.

| Linearity | Strategy |
|-----------|----------|
| Linear | 0 allocations, update pointers to skip elements |
| Non-linear | Frontier allocation (baseline) |

### Growing (e.g., `duplicate`)

Output size > input size.

| Linearity | Strategy |
|-----------|----------|
| Linear | Allocate only new cells (output - input) |
| Non-linear (predictable) | 1 bulk allocation (e.g., 2× for duplicate) |
| Non-linear (unpredictable) | Frontier allocation (baseline) |

### Unknown Algebra (baseline)

When static analysis cannot determine the category:

| Linearity | Strategy |
|-----------|----------|
| Linear | 0 allocations (always safe) |
| Non-linear | Frontier allocation |

## Summary

```
┌─────────────┬─────────────────────────────────────┐
│             │            Linearity                │
│  Category   ├──────────────┬──────────────────────┤
│             │   Linear     │    Non-linear        │
├─────────────┼──────────────┼──────────────────────┤
│ Collapsing  │ 0 alloc      │ 0 alloc              │
│ Preserving  │ 0 alloc      │ 1 alloc (exact)      │
│ Shrinking   │ 0 alloc      │ n alloc (frontier)   │
│ Growing*    │ k alloc      │ 1 alloc (exact)      │
│ Unknown     │ 0 alloc      │ n alloc (frontier)   │
└─────────────┴──────────────┴──────────────────────┘

* Growing with predictable factor (e.g., duplicate = 2×)
  k = new cells beyond input (output - input)
```

**Decision tree:**

1. Linear? → 0 allocations (reuse in-place)
2. Known algebra with exact output size? → 1 bulk allocation
3. Otherwise → frontier allocation (baseline)

## Three-Layer Architecture: Proofs, Operations, Machine

The Once compiler separates concerns into three distinct layers.

**Note**: Two proof approaches are being explored:
1. **Top-down (TreeTrace)**: Abstract proofs over SM* modules, then generate AbstractTrace
2. **Bottom-up (RecTrace)**: Build AbstractTrace directly, prove properties at that level

Both validate the same semantics from different angles. The architecture below
describes the top-down approach; see "Current Status: Agda Verification" for
the bottom-up work in RecTrace.agda.

```
TreeTrace (proof layer)
    ↓ optimizing translation
AbstractTrace (operational layer)
    ↓ 1-to-1 mapping
Machine instructions (x86, RISC-V, ARM, WASM)
```

### Layer 1: TreeTrace (Proof Space)

TreeTrace (`SMCore.agda`) represents recursive control flow for proofs:

```agda
data TreeTrace : Set where
  ε        : TreeTrace                      -- empty
  instr    : AbstractInstr → TreeTrace      -- single instruction
  _▸_      : TreeTrace → TreeTrace → TreeTrace  -- sequence
  branch   : Slot → TreeTrace → TreeTrace → TreeTrace  -- sum dispatch
  call-sub : TreeTrace → TreeTrace          -- recursive position marker
```

The `cata-tree-μ` function builds TreeTrace by structural induction on μ-values:

```
cata-tree-μ wf alg-trace x =
  destruct-tree ▸
  cata-tree-layer ... (sem-Out wf x) ▸
  alg-tree alg-trace
```

**Key insight: `call-sub` marks WHERE recursion happens, not HOW to execute it.**

Proofs use structural induction on μ-values. They don't care about:
- Whether the input is linear or shared
- Whether the algebra is collapsing, preserving, or growing
- What execution order is used at runtime

### Layer 2: TreeTrace → AbstractTrace (Optimization Space)

All optimizations from this document happen here. The translator pattern-matches on:

1. **Linearity** (from type system): Linear → in-place mutation
2. **Algebra category** (from static analysis): Determines allocation strategy
3. **Data structure shape**: List → forward loop, Tree → worklist/recursion
4. **Algebra properties**: Commutative → allow reordering/parallelism

Translation choices for `call-sub`:
- **Lists**: Compile to forward loop (no call stack)
- **Trees**: Compile to worklist-push/pop or actual function calls
- **Tail position**: Inline directly

### Layer 3: AbstractTrace → Machine (1-to-1 Mapping)

AbstractTrace instructions map directly to machine instructions:

| AbstractInstr | x86-64 |
|---------------|--------|
| `mov-to-output` | `mov rax, rdi` |
| `load-indirect` | `mov rax, [rdi]` |
| `store-at-slot n` | `mov [rbp-8*n], rax` |

This layer has no optimization decisions — it's a direct translation.
Proofs at the AbstractTrace level transfer directly to machine code.

### Why This Separation?

| Layer | Concerns | Doesn't Care About |
|-------|----------|-------------------|
| TreeTrace | Correctness, termination | Allocation, execution order |
| Translation | Performance, allocation | Proof structure |
| AbstractTrace→Machine | Encoding, calling convention | Semantics (already proven) |

Benefits:
- **Simpler proofs**: One structural induction proof covers all execution strategies
- **Flexible optimization**: Can change strategies without reproving correctness
- **Backend independence**: Same TreeTrace, different AbstractTrace strategies per target
- **Verified machine code**: AbstractTrace→machine is simple enough to trust (or verify separately)

## Execution Order Freedom

The semantic definition of cata implies bottom-up recursion:
```
cata alg (In x) = alg (fmap (cata alg) x)
```

But this is just the *specification*. The actual execution can differ:

| Scenario | Semantic Order | Actual Execution |
|----------|---------------|------------------|
| `map f` on list | Recurse to end, build backwards | Forward loop |
| `sum` on list | Recurse to end, accumulate backwards | Forward loop with accumulator |
| `sum` on tree | Post-order traversal | Any order (+ is commutative) |
| `length` | Recurse to end, count backwards | Forward loop with counter |

TreeTrace marks *where* recursive positions are (via `call-sub`), not *how* to execute
them. The TreeTrace → AbstractTrace translation chooses:

- **Lists**: Compile to simple loop (no call stack needed)
- **Trees + commutative op**: Parallel execution, any traversal order
- **Trees + non-commutative**: Must respect dependency order

## Implementation Notes

1. **Static analysis happens at compile time** - no runtime overhead
2. **Linearity determined by type system** - not user annotation
3. **Conservative fallback**: Unknown algebra → frontier allocation (no guessing)
4. **Bulk allocation**: Use arena/bump allocator for known-size cases
5. **Pattern matching priority**: Linear check first, then algebra recognition
6. **Proofs are strategy-agnostic**: Abstract trace correctness implies all valid execution strategies are correct

## Current Status: Agda Verification

The baseline frontier allocation model is being formally verified in Agda:

- **File**: `formal/Once/CCC/Machine/IR/RecTrace.agda`
- **Key structure**: `ProcessedLayerResult` tracks slot reclamation
- **Proof approach**: Structural induction on μ-values and functor structure

### Verified Properties

1. **Trace correctness**: Executing the trace produces the expected final state
2. **Memory preservation**: Locations before frontier unchanged
3. **Slot reclamation**: Temporary slots properly reclaimed after use
4. **Semantic correctness**: Result matches denotational semantics of cata

### Remaining Work

- **Capacity proofs**: Need tighter `layer-slot-bound` (product-depth, not full requirement)
- **Validity proofs**: Blocked on linear trace design for pair/sum composition
- **Algebra integration**: Verify algebra's output allocation at frontier

## Future Work

- Extend analysis to nested cata compositions
- Handle mutual recursion in algebras
- Size-type inference for tighter bounds on growing category
- Automatic commutativity detection for parallel execution
- **Prove optimization equivalence**: Show optimized strategies produce same results as baseline
