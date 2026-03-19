# Reference-Based Stack / Heap Design for SlotMachine

## Overview

A simplified memory model where all values are accessed by reference (pointer),
with Stack vs Heap mode determining only WHERE allocation occurs, not HOW
values are represented.

## Core Principles

### 1. All Values Accessed by Reference

Every value, regardless of type or allocation mode, is accessed through a
pointer (ValueLocation). This includes:
- Pairs
- Sums
- Closures
- Primitive types (Int, Float, etc.)
- Recursive types

### 2. No Memory-to-Memory Copying

Data is never copied between stack and heap, or between stack locations.
The only transfers are:
- Register → Memory (store)
- Memory → Register (load)

### 3. Stack vs Heap = Allocation Location Only

The AllocMode (Stack/Heap) determines WHERE a value is allocated:
- **Stack**: Allocated in current stack frame, lifetime bound to frame
- **Heap**: Allocated on heap, lifetime managed separately

Both modes use the SAME representation: pointers to components.

### 4. Linearity Enables Zero-Copy

Linear types (used exactly once) enable passing references without copying:
- **Linear value**: Pass reference, consumer takes ownership, no copy
- **Non-linear value**: Explicit copy when value used multiple times

Copy is a SEMANTIC operation (duplication for non-linear use), not a
mechanical operation (relocating data).

## Value Representations

### Pairs (Both Modes)

```
Pair (a, b) at location L:
  slot[L]   = pointer to a
  slot[L+1] = pointer to b

Total: 2 slots (always)
```

Stack mode and Heap mode pairs have identical structure. The only difference
is whether L is a stack location or heap location.

### Closures

```
Closure at location L:
  slot[L]   = pointer to environment
  slot[L+1] = pointer to code

Total: 2 slots (always)
```

Closures are typically heap-allocated (they may escape), but the
representation is the same regardless.

### Sum Types

```
inl a at location L:
  slot[L]   = tag (0)
  slot[L+1] = pointer to a

inr b at location L:
  slot[L]   = tag (1)
  slot[L+1] = pointer to b

Total: 2 slots (always)
```

### Primitive Types

```
Int/Float at location L:
  slot[L] = the value (or pointer to value)

Total: 1 slot
```

### Recursive Types (Fix F)

```
fold v at location L:
  slot[L] = pointer to unfolded value

Total: 1 slot
```

### Unit

```
Unit has no runtime representation (0 slots).
Validity is trivial at any location.
```

## SlotMachine Model

### Memory

```agda
StackMem FS = Frame → Slot → Maybe (ValueLocation FS)
HeapMem FS = HeapRef → HeapOffset → Maybe (ValueLocation FS)
```

Memory stores pointers (ValueLocation). This is unchanged from the current
boxed design.

### Operations

The only memory operations needed:
- `readLoc`: Read a pointer from memory
- `writeLoc`: Write a pointer to memory
- Register operations: `readReg`, `writeReg`

No multi-slot copy operation needed for the core model.

## Pair Construction

For `⟨ f , g ⟩ mode`:

```
1. Run f with input x → get pointer to f's result (fst-loc)
2. Run g with input x → get pointer to g's result (snd-loc)
3. Allocate 2 slots (on stack or heap per mode) → pair-loc
4. Write fst-loc to pair-loc
5. Write snd-loc to pair-loc + 1
6. Return pair-loc
```

This is IDENTICAL for Stack and Heap mode, except step 3 allocates in
different regions.

**No value copying occurs** - we only copy pointers (which is a register →
memory transfer).

## Pair Projection

For `fst` and `snd`:

```
fst:
  1. Input: pair-loc in RDI
  2. Read pointer from pair-loc → fst-loc
  3. Return fst-loc in RAX

snd:
  1. Input: pair-loc in RDI
  2. Read pointer from pair-loc + 1 → snd-loc
  3. Return snd-loc in RAX
```

Identical for both modes - just pointer reads.

## Linearity and Copying

### Linear Case (No Copy)

When a value is used exactly once:
```
f : A ⊸ B    -- linear function
x : A        -- linear value

f x          -- x is consumed, reference passed, no copy
```

### Non-Linear Case (Copy Required)

When a value is used multiple times:
```
⟨ f , g ⟩ x  -- x used by both f and g
```

If x is linear, the IR must include an explicit copy:
```
let x' = copy x in
⟨ f , g ⟩ (x, x')  -- f uses x, g uses x'
```

The `copy` operation:
1. Allocates new space for the value
2. Recursively copies the structure (following pointers)
3. Returns pointer to the copy

This is a SEMANTIC operation required by linearity, not a mechanical
relocation.

### Copy-on-Write Optimization

For immutable values, copy can be deferred:
- Share reference initially
- Copy only when mutation would occur
- Since Once is functional, mutation is rare/controlled

## ValidAtWF Simplification

With uniform pointer-based representation, we need fewer constructors:

```agda
data ValidAtWF : AllocMode → AllocState → {A : Type} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set where

  valid-unit-wf : ∀ {m alloc loc s} →
    ValidAtWF m alloc {Unit} tt loc s

  valid-pair-wf : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    {alloc : AllocState} {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS}
    {mA mB : AllocMode} →
    readLoc s pair-loc ≡ just fst-loc →
    readLoc s (sucLoc pair-loc) ≡ just snd-loc →
    BeforeFrontier alloc fst-loc →
    BeforeFrontier alloc snd-loc →
    ValidAtWF mA alloc a fst-loc s →
    ValidAtWF mB alloc b snd-loc s →
    ValidAtWF m alloc {A * B} (a , b) pair-loc s  -- m can be Stack or Heap

  -- Similar for closures, sums, etc.
```

Note: `valid-pair-wf` works for BOTH Stack and Heap mode because the
representation is identical.

## What This Eliminates

1. **`stack-type-slots` for layout**: Not needed - all compound types use
   fixed pointer-based layout

2. **Contiguous placement requirements**: Components can be anywhere, we
   just store pointers to them

3. **Separate Stack/Heap validity constructors**: One constructor works
   for both modes

4. **Mechanical copying**: No need to relocate values to specific locations

5. **Complex offset calculations**: Just pointer arithmetic (sucLoc)

## What Remains

1. **Semantic copy for non-linear use**: Required by linearity semantics

2. **Stack vs Heap allocation tracking**: BeforeFrontier distinguishes
   stack slots from heap refs

3. **Escape analysis**: Determines which mode to use (Stack for non-escaping,
   Heap for escaping values)

## IR Stack Requirements

Simplified calculation:

```agda
ir-stack-requirement : ∀ {A B} → IR A B → ℕ
ir-stack-requirement id = 0
ir-stack-requirement (g ∘ f) = ir-req f + ir-req g
ir-stack-requirement (⟨ f , g ⟩ _) = ir-req f + ir-req g + 2  -- always 2 for pair
ir-stack-requirement fst-ir = 0
ir-stack-requirement snd-ir = 0
ir-stack-requirement (curry f _) = ir-req f + 2  -- closure is 2 slots
ir-stack-requirement apply = 2  -- pair for (env, arg)
ir-stack-requirement (inl-ir _) = 2  -- tag + pointer
ir-stack-requirement (inr-ir _) = 2  -- tag + pointer
ir-stack-requirement (case-ir f g) = max (ir-req f) (ir-req g)
-- etc.
```

No type-dependent slot calculations needed.

## Code Generation Correspondence

This design maps directly to x86:

| Operation | SlotMachine | x86 |
|-----------|-------------|-----|
| Read pointer | readLoc | mov rax, [rbp + offset] |
| Write pointer | writeLoc | mov [rbp + offset], rax |
| Pass argument | writeReg RDI | mov rdi, rax |
| Return result | writeReg RAX | mov rax, ... |
| Allocate stack | advance next-slot | sub rsp, N |
| Allocate heap | (heap allocator) | call malloc |

## Summary

The key insight: **Stack vs Heap is about allocation lifetime, not representation**.

Both modes use pointer-based representation. This:
- Simplifies the proof architecture
- Eliminates mechanical copying
- Enables linearity-based optimizations
- Maps cleanly to actual machine code
