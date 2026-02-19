# X86 Proof Architecture: Disjointness

## Core Insight

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
