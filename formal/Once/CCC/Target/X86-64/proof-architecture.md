# X86 Proof Architecture: Trace-Based Refinement

## Overview

This document describes the proof architecture for compiling IR to x86 machine code.
The key innovation is the **AbstractInstr layer** - an intermediate representation between
IR and x86 that enables compositional proofs.

## AbstractInstr Layer

### Architecture Problem (Before)

Two independent proof efforts that don't compose well:
- **Dispatcher**: Proves IR → LocState (abstract machine state)
- **Runner** (FramelessPairRunner): Proves LocState → x86 (duplicated per IR)

This leads to:
- Per-IR runner proofs (N proofs for N IR constructors)
- Postulates to bridge the gap
- Complex, non-compositional reasoning

### Solution: Trace-Based Refinement

If codegen follows SlotMachine 1-to-1, then:
1. **SlotMachine emits traces** (what operations happen)
2. **Each trace operation compiles to concrete instructions**
3. **Per-instruction simulation proofs compose automatically**
4. **No per-IR runner needed** - FramelessPairRunner.agda is eliminated

### Two-Register Model

The abstract machine uses only two logical registers:

```agda
data AbstractReg : Set where
  Input  : AbstractReg    -- argument location (maps to RDI)
  Output : AbstractReg    -- result location (maps to RAX)
```

This simplifies reasoning - all IR operations either read from Input, write to Output,
or access memory via these registers.

### Abstract Instructions

```agda
data AbstractInstr : Set where
  -- Register operations
  mov-to-output      : AbstractInstr              -- Output := Input

  -- Memory load operations (slot-level, not physical address arithmetic)
  load-indirect      : AbstractInstr              -- Output := *Input
  load-indirect-suc  : AbstractInstr              -- Output := *(sucLoc Input)  -- e.g., pair.snd, closure.code-ptr
  load-from-slot     : Slot → AbstractInstr       -- Output := stack[slot]

  -- Memory store operations
  store-at-slot      : Slot → AbstractInstr       -- stack[slot] := Output
  store-indirect     : AbstractInstr              -- *Input := Output
  store-indirect-suc : AbstractInstr              -- *(Input + 1) := Output

  -- Address computation
  lea-slot           : Slot → AbstractInstr       -- Output := &stack[slot]
  restore-input      : Slot → AbstractInstr       -- Input := stack[slot]

  -- Stack management
  alloc-stack        : ℕ → AbstractInstr          -- allocate N slots
  dealloc-stack      : ℕ → AbstractInstr          -- deallocate N slots

  -- Apply-specific (function calls)
  push-frame         : ℕ → AbstractInstr          -- push new frame with capacity
  pop-frame          : AbstractInstr              -- restore caller frame
  call-closure       : AbstractInstr              -- jump to closure code
```

### Traces

```agda
AbstractTrace : Set
AbstractTrace = List AbstractInstr
```

Each IR execution produces a trace. Traces compose via list concatenation:
- `compose f g`: `f-trace ++ bridge ++ g-trace`
- `pair f g`: `setup ++ f-trace ++ middle ++ g-trace ++ cleanup`

### Proof Structure

```
IR ─────────────────────────────────────────────────────────── x86
 │                                                              │
 │ dispatch                                           compile   │
 ↓                                                              ↓
LocState ──────── AbstractTrace ──────── Program ──────────── State
         emit            compile-abstract      Star transitivity

IRResultAWF                                    AbstractSimulation
(with trace field)                             (per-instruction proofs)
```

1. **Dispatcher** (IRResultAWF): Proves IR → (LocState, AbstractTrace)
2. **AbstractToX86**: Compiles AbstractTrace → x86 Program
3. **AbstractSimulation**: Proves each AbstractInstr refines to x86
4. **TraceRunner**: Composes simulation proofs via Star transitivity

### What Gets Eliminated

| Old Component | Replacement | Why |
|---------------|-------------|-----|
| FramelessPairRunner.agda | TraceRunner.agda | Per-IR proofs → trace composition |
| Complex StateCorresponds | Trace-level correspondence | Simpler invariants |
| Capacity postulates | Derived from trace semantics | Explicit in trace |

---

## Disjointness (Memory Safety)

### Core Insight

IR proofs need to show their writes don't corrupt other data. This requires **disjointness** - proving written locations are different from preserved locations.

## Three Memory Domains

| Domain | Structure | Disjointness Source |
|--------|-----------|---------------------|
| Stack | Frames with slots | Frame ordering (`f₁ ≺ f₂`) |
| Heap | Allocated blocks | Allocator freshness |
| Regions | Stack / Heap / Code | Linker placement |

## What IR Proofs Must Prove

### Stack: Frame Ordering

To show a write to `(f₁, s₁)` doesn't affect `(f₂, s₂)`:

| Case | Proof Obligation |
|------|------------------|
| Same frame, different slot | `s₁ ≢ s₂` |
| Different frames | `f₁ ≺ f₂` (or `f₂ ≺ f₁`) + capacity bound |

Frame ordering comes from call structure - callee frames are below caller frames.

See: `Common/FrameSemantics.agda`, `Common/SlotMemory.agda`, `X86/FrameInstantiation.agda`, `X86/SlotInstantiation.agda`

### Heap: Writes Within Allocated Blocks

To show a heap write doesn't corrupt other heap data:

| Proof Obligation |
|------------------|
| Write is within bounds of an allocated block (`i < n`) |

That's it. IR doesn't prove cross-block disjointness (`addr₁ ≢ addr₂`) - IR doesn't control allocation, so it can't prove this. The allocator guarantees all allocated blocks are pairwise disjoint via freshness.

Heap is actually **simpler** than stack from IR's perspective - the allocator handles all cross-block disjointness automatically.

See: `Common/AllocatorSemantics.agda`

### Cross-Domain: Automatic

| Case | Proof Obligation |
|------|------------------|
| Stack write vs heap data | None (region disjointness) |
| Heap write vs stack data | None (region disjointness) |

See: `Common/Regions.agda` (linker proof obligation via `MemoryLayout`)

## Summary: IR Proof Obligations

```
Stack preservation:
  - Prove frame ordering (f₁ ≺ f₂) OR slot inequality (s₁ ≢ s₂)
  - Prove capacity bounds (slot within allocated gap)

Heap preservation:
  - Prove writes are within allocated block bounds (i < n)
  - Cross-block disjointness: automatic (allocator's job, not IR's)

Cross-domain:
  - Nothing (automatic from region separation)
```

## Allocator Contract

The allocator (not IR) guarantees:

1. **Freshness**: Each allocation returns an address disjoint from all previous allocations
2. **Block integrity**: Slots within a block are contiguous
3. **Heap region**: All allocated addresses are in the heap region

This is why IR doesn't prove cross-block disjointness - IR doesn't control allocation, so it cannot prove freshness. The allocator owns this responsibility and provides the guarantee to IR.

See: `Common/AllocatorSemantics.agda`

## Allocation Location: Stack vs Heap

The IR specifies where each value is allocated:

| Location | When Safe | Trade-off |
|----------|-----------|-----------|
| HeapAlloc | Always | Slower (allocation overhead) |
| StackAlloc | Value doesn't escape | Faster (just bump stack pointer) |

A value **escapes** if it outlives its stack frame (returned, stored in closure, etc.).

See: `X86/Correct/MemoryValid.agda` (`AllocMode`, `ValidAt`)

## Value Representation: Unboxed Stack / Boxed Heap

Allocation location determines value **representation**:

| AllocMode | Representation | Memory Layout |
|-----------|----------------|---------------|
| Stack | **Unboxed** | Values stored inline, variable size |
| Heap | **Boxed** | Pointers to heap data, fixed size |

### Unboxed (Stack)

Values are stored directly in stack slots:

```
Pair (a, b) unboxed at slot S:
  slot[S .. S + type-slots A - 1] = value a (inline)
  slot[S + type-slots A .. ]      = value b (inline)
  Total: type-slots A + type-slots B slots
```

### Boxed (Heap)

Values are stored as pointers:

```
Pair (a, b) boxed at slot S:
  slot[S]   = pointer to a
  slot[S+1] = pointer to b
  Total: 2 slots (always)
```

### Representation by Type

| Type | Stack Mode (Unboxed) | Heap Mode (Boxed) | Implementation Status |
|------|---------------------|-------------------|----------------------|
| Recursive (`Fix F`) | F data inline, size = `stack-type-slots F` | pointer (1 slot) | ✅ Both modes fully proven |
| Closures (`A ⇒ B`) | Not yet implemented | env-ptr + code-ptr (2 slots) | ⚠️ Heap only |
| Sum (`A + B`) | tag + payload inline | tag + pointer (2 slots) | ⚠️ Heap only |
| Pair (`A * B`) | both inline | two pointers (2 slots) | ⚠️ Heap only |

### Fold Implementation Details

`fold-ir` takes an `AllocMode` parameter:

```agda
fold-ir : ∀ {F} → AllocMode → IR F (Fix F)
```

| Mode | Implementation | Allocation |
|------|----------------|------------|
| `fold-ir Stack` | F value IS the Fix F value at same location | None (zero slots) |
| `fold-ir Heap` | Allocate slot, store pointer to unfolded value | 1 slot |

Stack mode uses `valid-fold-unboxed-wf`: the input `ValidAtWF mIn alloc v loc s` becomes `ValidAtWF Stack alloc (fold v) loc s` - same location, just wrapped validity.

Heap mode uses `valid-fold-boxed-wf`: stores pointer to unfolded value, producing boxed representation.

### ValidAtWF: Mode-Indexed Validity

`ValidAtWF` takes `AllocMode` as its **first parameter**, enforcing correct representation:

```agda
data ValidAtWF : AllocMode → AllocState → {A : Type} → ⟦ A ⟧ → ValueLocation → LocState → Set where
  valid-pair-boxed-wf   : ... → ValidAtWF Heap ...   -- Heap mode: boxed
  valid-pair-unboxed-wf : ... → ValidAtWF Stack ...  -- Stack mode: unboxed
  valid-closure-wf      : ... → ValidAtWF Heap ...   -- Closures: always Heap
```

This ensures handlers produce the correct representation for their declared mode.

See: `X86v3/ClosureWellFormed.agda` (`ValidAtWF`), `X86v3/unboxed-stack-design.md`

## Stack Capacity: Design Goals

When using stack allocation, we need capacity proofs. Key design properties:

### O(1) Overhead

**We want O(1) stack overhead, not O(depth) overhead.**

- Actual stack usage is inherently O(depth) for nested IRs - unavoidable
- But ADDITIONAL overhead (reserved-but-unused space) must be O(1)
- Any solution that wastes O(bound) or O(depth) space is rejected

### Dynamic Capacity Threading (X86 Pattern)

Capacity proofs use **dynamic threading**, not bounded reasoning:

| Approach | Description | Overhead |
|----------|-------------|----------|
| ❌ Bounded | Reserve `pair-slots * program-bound` everywhere | O(bound) waste |
| ✅ Dynamic | Each closure carries its `body-capacity` | O(1) overhead |

**Dynamic capacity flow:**

```
Curry: Creates closure with body-capacity = ir-stack-requirement body
         ↓
Compose/Pair: Threads closure (with capacity) through unchanged
         ↓
Apply: Extracts body-capacity from closure, verifies capacity fits
```

**Key insight:** The Dispatcher doesn't need to know body capacity statically. It ensures initial frame has enough space for worst-case `ir-stack-requirement`. Each `Apply` then verifies the specific closure's body fits.

**Anti-pattern (causes postulates):** Trying to prove `ir-stack-requirement ≤ pair-slots * ir-size` globally. This fails for Stack-mode pairs where `stack-type-slots` can exceed `pair-slots`.

See: `X86v3/capacity-migration-plan.md`, `X86/Correct/StarBase.agda` (`ClosureWFOutput`, `ApplyReady`)

### Escape Analysis

Escape analysis is an **IR-to-IR transformation**, not part of the proof:

```
IR (all heap)  →  escape analysis  →  IR (stack where safe)
```

1. **Initial IR**: Conservative - all allocations on heap
2. **Escape analysis**: Identifies values that don't escape their stack frame
3. **Transformed IR**: Non-escaping values rewritten to stack allocation

The correctness proofs support both locations - they don't perform the analysis. The IR itself (post-transformation) specifies each allocation location via `StackAlloc` or `HeapAlloc`.

## Orthogonal Memory Design (Future Direction)

See: `X86v3/orthogonal-memory-design.md` for full details.

### Core Principle

Make proofs **orthogonal** by separating concerns:

| Concern | Handled By | Independent Of |
|---------|------------|----------------|
| Stack allocation/deallocation | Frame semantics | Heap concerns |
| Heap allocation | HeapLocation type | Stack concerns |
| Heap deallocation | Explicit `free-heap` IR | Allocation strategy |
| Escape analysis | Separate pass with witness | IR execution |

### Key Invariant: Heap → Heap Only

Heap-allocated values can only reference other heap values, never stack:

```agda
-- HeapLocation is a subset, can only point to heap
record HeapLocation : Set where ...

-- HeapMem can ONLY store HeapLocation (enforced by types)
HeapMem FS = HeapLocation FS → Maybe (HeapLocation FS)
```

This makes stack deallocation (frame pop) trivially safe -- heap values don't reference stack.

### Explicit Deallocation

Instead of runtime GC/refcounting, compiler emits `free-heap` with proof:

```agda
free-heap : HeapRef → IR Unit Unit

-- Compiler provides witness that no live refs exist
record CanFreeHeap (block : HeapRef) : Set where
  field
    no-refs : ∀ loc → LiveAt loc → ¬ ReferencesBlock loc block
```

### Correct by Construction

Invalid programs can't typecheck:
- `free-heap` without proof → won't compile
- Stack allocation without escape witness → won't compile
- Store stack ref in heap → type error (HeapLocation vs ValueLocation)

### Simple Compiler Strategy

A minimal correct compiler:
1. All allocations → Heap (no escape analysis)
2. No `free-heap` instructions (leaks memory, but correct)

Optimizations (escape analysis, deallocation) can be added incrementally without changing IR proofs.
