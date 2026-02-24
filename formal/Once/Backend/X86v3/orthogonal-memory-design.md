# Orthogonal Memory Design

## Overview

This document proposes a redesign of the memory model to make proofs **orthogonal** -- each concern is independent and changes don't cascade through the system.

## Core Principle: Separation of Concerns

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  Stack Concerns │     │  Heap Concerns  │     │   Deallocation  │
├─────────────────┤     ├─────────────────┤     ├─────────────────┤
│ Frame semantics │     │ HeapLocation    │     │ free-heap IR    │
│ BeforeFrontier  │     │ Heap → Heap     │     │ CanFreeHeap     │
│ Frame pop       │     │ graph           │     │ witness         │
└────────┬────────┘     └────────┬────────┘     └────────┬────────┘
         │                       │                       │
         └───────────────────────┴───────────────────────┘
                                 │
                  Separated by HeapLocation invariant
                  No cross-references between concerns
```

## Key Invariant: Heap Only References Heap

**The invariant:** Heap-allocated values can only contain references to other heap-allocated values, never to stack.

**Why:**
- Heap values may outlive stack frames
- If heap referenced stack, frame pop would create dangling pointers
- With this invariant, stack deallocation (frame pop) is always safe

**Direction allowed:**
- Stack → Heap: YES (heap is stable, safe to reference)
- Heap → Stack: NO (stack dies, would dangle)

## Type-Level Encoding

### Current Design (SlotMachine.agda)

```agda
data ValueLocation (FS : FrameSemantics) : Set where
  OnStack : Frame FS → Slot → ValueLocation FS
  OnHeap  : HeapRef → HeapOffset → ValueLocation FS

-- Problem: Both can store any ValueLocation
StackMem FS = Frame → Slot → Maybe (ValueLocation FS)
HeapMem FS = HeapRef → HeapOffset → Maybe (ValueLocation FS)
```

### Proposed Design

```agda
-- Heap-only location (subset of ValueLocation)
record HeapLocation (FS : FrameSemantics) : Set where
  constructor heap-loc
  field
    ref : HeapRef
    offset : HeapOffset

-- Full location (stack can reference either)
data ValueLocation (FS : FrameSemantics) : Set where
  OnStack : Frame FS → Slot → ValueLocation FS
  OnHeap  : HeapLocation FS → ValueLocation FS

-- Stack can store any location
StackMem FS = Frame → Slot → Maybe (ValueLocation FS)

-- Heap can ONLY store heap locations -- invariant by construction!
HeapMem FS = HeapLocation FS → Maybe (HeapLocation FS)
```

**Result:** Code that tries to store `OnStack` in heap memory won't typecheck.

## Escape Analysis as Separate Pass

### Workflow

```
IR (conceptually all stack/local)
         ↓
  Escape Analysis Pass
         ↓
  Determines: which values escape their frame?
         ↓
IR with explicit Stack/Heap mode annotations
  + EscapeWitness for each stack allocation
         ↓
  IR Execution (just follows annotations)
```

### Interface

```agda
-- Escape analysis provides this witness for stack allocations
record StackAllocationSafe (frame : Frame) : Set where
  field
    -- After frame is popped, no surviving value references it
    no-surviving-refs : ∀ {loc} →
      SurvivesFramePop frame loc →
      ∀ k → ¬ References loc (OnStack frame k)

-- What survives a frame pop (structural, not analysis-dependent)
data SurvivesFramePop (frame : Frame) : Location → Set where
  in-ancestor : ∀ {f k} → frame ≺ f → SurvivesFramePop frame (OnStack f k)
  on-heap : ∀ {addr} → SurvivesFramePop frame (OnHeap addr)
```

### IR Doesn't Prove Escape Safety

The IR operations (apply, pair, curry, etc.) don't prove escape analysis is correct. They receive the witness and use it.

**Before (entangled):**
- IR proofs reason about escape, references, frame survival
- Postulates shuffle around as we try to prove things we can't

**After (orthogonal):**
- Escape analysis proves safety, provides witness
- IR just uses the witness
- IR proofs only prove: "given valid inputs, produce valid outputs"

## Explicit Heap Deallocation

### The `free-heap` IR

Instead of runtime reference counting or GC, the compiler emits explicit deallocation:

```agda
data IR : Type → Type → Set where
  ...
  free-heap : HeapRef → IR Unit Unit
```

### Proof Interface

```agda
-- Compiler provides this witness when emitting free-heap
record CanFreeHeap (block : HeapRef) (alloc : AllocState) : Set where
  field
    no-refs : ∀ loc → LiveAt alloc loc → ¬ ReferencesBlock loc block
```

### Compiler Strategies

Different higher-level strategies all produce the same IR:

| Strategy | When to emit free-heap |
|----------|------------------------|
| Linear ownership | Owner consumed |
| Region-based | Region ends |
| Lifetime analysis | Last use identified |
| Manual + verified | User annotates, compiler verifies |
| Conservative | Never free (correct but leaks) |

**Key insight:** A simple compiler can heap-allocate everything and never free. It's correct! Then optimization passes can be added incrementally without changing IR proofs.

## Correct by Construction

This design makes incorrect programs untypeable:

| Operation | Requires | Can't emit if... |
|-----------|----------|------------------|
| `free-heap block` | `CanFreeHeap` proof | Can't construct proof |
| Stack mode allocation | `StackAllocationSafe` witness | No witness from escape analysis |
| Store stack ref in heap | `HeapLocation` type | Won't typecheck (type mismatch) |

**Soundness:** Invalid programs can't be constructed.

**Completeness:** We may reject some valid programs if proofs are too weak, but that's conservative (safe).

## Module Changes Required

### SlotMachine.agda (Common)

- [ ] Add `HeapLocation` record type
- [ ] Change `OnHeap` to take `HeapLocation` instead of `HeapRef × HeapOffset`
- [ ] Change `HeapMem` to return `Maybe (HeapLocation FS)`
- [ ] Update `sucLoc`, `offsetLoc` for new structure

### Validity.agda (X86v3)

- [ ] Update `ValidAt` to use new location types
- [ ] Heap validity constructors only reference `HeapLocation`
- [ ] Stack validity can reference either

### Allocation.agda (X86v3)

- [ ] Update `BeforeFrontier` for new location types
- [ ] Add `StackAllocationSafe` record (or import from new module)
- [ ] Frame pop safety follows from HeapLocation invariant

### IR.agda (X86v3)

- [ ] Add `free-heap` IR constructor
- [ ] IR operations receive escape witness (not prove it)

### New Module: EscapeInterface.agda

- [ ] `StackAllocationSafe` record
- [ ] `CanFreeHeap` record
- [ ] `SurvivesFramePop` data type
- [ ] Interface that escape analysis must satisfy

### WF Modules (ApplyWF, PairWF, etc.)

- [ ] Remove postulates about escape/references
- [ ] Receive and use escape witness instead
- [ ] Proofs simplify significantly

## Migration Path

### Phase 1: HeapLocation Invariant
1. Add `HeapLocation` type to SlotMachine
2. Update `HeapMem` to use it
3. Fix type errors that propagate (these show where invariant was violated)

### Phase 2: Escape Interface
1. Create EscapeInterface module with record types
2. Add witness parameters to Stack-mode IR operations
3. Remove escape-related postulates from WF modules

### Phase 3: Explicit Deallocation
1. Add `free-heap` IR constructor
2. Add `CanFreeHeap` interface
3. (Optional) Implement deallocation strategies in higher compiler

## Benefits Summary

| Before | After |
|--------|-------|
| Postulates shuffle around | Each concern has clean proof |
| IR proves escape safety | IR uses escape witness |
| Implicit deallocation reasoning | Explicit free-heap with proof |
| Stack/heap concerns entangled | Orthogonal by HeapLocation type |
| Complex proofs | Simpler, modular proofs |
| Changes cascade | Changes localized |

## Simple Compiler Example

A minimal correct compiler:

```
1. All allocations → Heap (no escape analysis needed)
2. No free-heap instructions (memory leaks, but correct)
3. No stack mode (no witness needed)
```

This compiles and runs correctly. Optimizations can be added later:
- Add escape analysis → some allocations move to stack
- Add lifetime analysis → emit free-heap instructions

Each optimization is independent and doesn't require changing IR proofs.
