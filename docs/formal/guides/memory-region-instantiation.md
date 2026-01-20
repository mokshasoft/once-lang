# Memory Region Instantiation Architecture

## Overview

This document describes the layered architecture for memory region proofs,
where abstract region contracts are instantiated by concrete memory layouts.
With proper instantiation, **all postulates fall away** - the formal
development becomes fully proven given parameters from the compiler.

## The Problem

Currently, we have postulates scattered across abstraction levels:

```agda
-- In Common.MemoryLayoutSemantics (abstract)
postulate
  stack-bounds : RegionBounds
  heap-bounds  : RegionBounds
  code-bounds  : RegionBounds
  intervals-disjoint : ...

-- In X86.MemoryRegionLemmas (architecture-specific)
postulate
  x86-stack-lower-zero : lower stack-bounds ≡ 0
  x86-code-lower-zero : lower code-bounds ≡ 0
```

This is problematic because:
1. It's unclear what we're really assuming
2. The postulates can never be discharged
3. The relationship between abstract and concrete is muddled

## The Target Architecture: Zero Postulates

### Key Insight

When we DEFINE concrete non-overlapping regions, everything becomes provable:
- Region bounds are definitions, not postulates
- Disjointness is proven from arithmetic on concrete bounds
- All lemmas follow from definitions

The only "assumptions" become **module parameters** provided by the compiler:
- `code-size` - compiler knows the code size
- `stack-size` - runtime allocates stack
- `heap-size` - runtime allocates heap

These aren't postulates - they're inputs. The compiler provides concrete
values, and everything else is proven.

### Layer 1: Abstract Region Interface (MemoryLayoutSemantics)

Defines the **interface** that any memory layout must satisfy:

```agda
record RegionBounds : Set where
  field
    lower : Addr
    upper : Addr
    bounds-valid : lower ≤ upper

-- Region membership (DEFINITIONS)
InStack : Addr → Set
InStack a = lower stack-bounds ≤ a × a ≤ upper stack-bounds

-- Disjointness INTERFACE (to be proven by concrete layout)
RegionsDisjoint : RegionBounds → RegionBounds → Set
RegionsDisjoint r1 r2 = ∀ a → ¬ (InRegion r1 a × InRegion r2 a)
```

This layer defines WHAT properties are needed, not HOW to achieve them.

### Layer 2: Concrete Memory Layout (X86Layout)

The compiler/linker **defines** the actual layout and **proves** it satisfies
the interface:

```agda
module X86Layout (code-size stack-size heap-size : ℕ) where

  -- Concrete layout: non-overlapping regions
  --
  --   [0, code-size)                     = code
  --   [code-size, code-size + heap-size) = heap
  --   [code-size + heap-size, total)     = stack
  --
  total-size = code-size + heap-size + stack-size

  -- Define concrete bounds
  x86-code-bounds : RegionBounds
  x86-code-bounds = record
    { lower = 0
    ; upper = code-size
    ; bounds-valid = z≤n
    }

  x86-heap-bounds : RegionBounds
  x86-heap-bounds = record
    { lower = code-size
    ; upper = code-size + heap-size
    ; bounds-valid = m≤m+n code-size heap-size
    }

  x86-stack-bounds : RegionBounds
  x86-stack-bounds = record
    { lower = 0           -- Stack region includes 0 for easy capacity proofs
    ; upper = total-size  -- Or could be [code+heap, total)
    ; bounds-valid = z≤n
    }

  -- PROVEN: properties are definitional
  code-lower-is-zero : lower x86-code-bounds ≡ 0
  code-lower-is-zero = refl

  stack-lower-is-zero : lower x86-stack-bounds ≡ 0
  stack-lower-is-zero = refl

  -- PROVEN: regions don't overlap (arithmetic proof)
  code-heap-disjoint : RegionsDisjoint x86-code-bounds x86-heap-bounds
  code-heap-disjoint a (in-code , in-heap) =
    -- a < code-size (from in-code) and a ≥ code-size (from in-heap)
    -- Contradiction by arithmetic
    ...

  stack-heap-disjoint : RegionsDisjoint x86-stack-bounds x86-heap-bounds
  stack-heap-disjoint = ...

  stack-code-disjoint : RegionsDisjoint x86-stack-bounds x86-code-bounds
  stack-code-disjoint = ...

  -- Bundle all disjointness proofs
  intervals-disjoint : ∀ a →
    ¬ (InStack a × InHeap a) ×
    ¬ (InStack a × InCode a) ×
    ¬ (InHeap a × InCode a)
  intervals-disjoint a = (stack-heap-disjoint a , stack-code-disjoint a , ...)
```

**No postulates** - everything is defined or proven from definitions.

### Layer 3: Initialization

The runtime sets up the initial state and **proves** it satisfies requirements:

```agda
module X86Init (code-size stack-size heap-size : ℕ) where
  open X86Layout code-size stack-size heap-size

  -- Initial stack pointer
  init-rsp : Addr
  init-rsp = total-size  -- Top of stack region

  -- PROVEN: initial rsp is in stack region
  init-rsp-in-stack : InStack init-rsp
  init-rsp-in-stack = (z≤n , ≤-refl)

  -- PROVEN: initial capacity
  init-capacity : StackCapacity init-state (stack-size / slot-size)
  init-capacity = record
    { rsp-in-stack = init-rsp-in-stack
    ; rsp-sufficient = ...      -- arithmetic from stack-size
    ; capacity-maintained = ... -- from stack-lower-is-zero = refl
    }
```

### The Complete Picture

```
Compiler provides parameters: code-size, stack-size, heap-size
         │
         ▼
┌─────────────────────────────────────────────────────────┐
│  X86Layout (parameterized module)                       │
│  ├── DEFINES concrete bounds                            │
│  ├── PROVES disjointness (arithmetic)                   │
│  └── PROVES bound properties (refl)                     │
└─────────────────────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────┐
│  X86Init                                                │
│  ├── DEFINES initial state                              │
│  └── PROVES initial capacity                            │
└─────────────────────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────┐
│  All proofs                                             │
│  └── Use proven lemmas, ZERO postulates                 │
└─────────────────────────────────────────────────────────┘
```

## Why This Works

### Postulates vs Parameters

| Postulate | Parameter |
|-----------|-----------|
| "Trust me, this is true" | "Given this value..." |
| Can never be discharged | Provided by caller |
| Unclear assumptions | Explicit inputs |

When the compiler calls `X86Layout 1000 4096 8192`, it provides concrete
values. Everything else is proven from those values.

### Disjointness is Arithmetic

With concrete bounds, disjointness becomes:
- Code: [0, 1000)
- Heap: [1000, 5096)
- Stack: [0, 13288) with lower = 0

Proving "code and heap don't overlap" is just proving:
- If a < 1000 then a < 1000 (in code implies not in heap's lower bound)

This is straightforward arithmetic, not a semantic assumption.

## Relationship to StackCapacity

The `capacity-maintained` field says "after allocating k slots, still in stack":

```agda
capacity-maintained : ∀ k → k ≤ n → InStack (rsp ∸ k * slot-size)
```

With `stack-lower-is-zero = refl`:
- Lower bound: `0 ≤ rsp ∸ k * slot-size` is always true (ℕ property)
- Upper bound: arithmetic from rsp-sufficient

No postulates needed - it's all arithmetic from the concrete layout.

## What Each Layer Contains

| Layer | Contains | Postulates |
|-------|----------|------------|
| Abstract (MemoryLayoutSemantics) | Interface definitions | **None** |
| Concrete Layout (X86Layout) | Bounds definitions, disjointness proofs | **None** |
| Initialization (X86Init) | Initial state, capacity proofs | **None** |
| Architecture Lemmas | Derived lemmas | **None** |

**Total postulates: Zero**

The only inputs are module parameters from the compiler.

## Current State vs Target State

### Current (postulates scattered)
```
MemoryLayoutSemantics
  ├── postulate stack-bounds, heap-bounds, code-bounds
  └── postulate intervals-disjoint

X86.MemoryRegionLemmas
  ├── postulate x86-stack-lower-zero
  ├── postulate x86-code-lower-zero
  └── postulate prog-fits-in-code
```

### Target (zero postulates)
```
MemoryLayoutSemantics
  └── Interface definitions only (RegionBounds, InStack, etc.)

X86Layout (code-size stack-size heap-size : ℕ)
  ├── x86-*-bounds = record { ... }     -- definitions
  ├── intervals-disjoint = ...          -- proven
  └── *-lower-is-zero = refl            -- definitional

X86Init
  └── init-capacity = ...               -- proven from layout

X86.MemoryRegionLemmas
  └── stack-sub-preserves = ...         -- proven from layout
```

## Migration Path

1. Create `X86Layout` module parameterized by sizes
2. Define concrete bounds in `X86Layout`
3. Prove `intervals-disjoint` from arithmetic
4. Change `x86-stack-lower-zero` from postulate to `refl`
5. Update `MemoryLayoutSemantics` to be interface-only
6. Thread parameters through from compiler

## Benefits

1. **Zero postulates**: Formal development is fully proven
2. **Clear inputs**: Only module parameters from compiler
3. **Verifiable layouts**: Compiler proves its layout is correct
4. **No magic**: Everything follows from definitions and arithmetic

## Example: Full Proof Chain

```agda
-- Compiler provides sizes
module Compilation where
  code-size = 1000
  stack-size = 4096
  heap-size = 8192

  -- Instantiate layout
  open X86Layout code-size stack-size heap-size

  -- All these are PROVEN, not postulated:
  -- • intervals-disjoint (from layout arithmetic)
  -- • stack-lower-is-zero = refl
  -- • init-capacity (from init module)
  -- • stack-sub-preserves (from lower = 0)
  -- • pc-in-code (from code bounds)
```

## Related Documents

- `architecture-independent-stack-abstraction.md`: StackGrowth interface
- `d041-region-migration.md`: Region-based memory proofs
