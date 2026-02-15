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

## Stack Capacity: Design Goals

When using stack allocation, we need capacity proofs. Key design properties:

### O(1) Overhead

**We want O(1) stack overhead, not O(depth) overhead.**

- Actual stack usage is inherently O(depth) for nested IRs - unavoidable
- But ADDITIONAL overhead (reserved-but-unused space) must be O(1)
- Any solution that wastes O(bound) or O(depth) space is rejected

### Escape Analysis

Escape analysis is an **IR-to-IR transformation**, not part of the proof:

```
IR (all heap)  →  escape analysis  →  IR (stack where safe)
```

1. **Initial IR**: Conservative - all allocations on heap
2. **Escape analysis**: Identifies values that don't escape their stack frame
3. **Transformed IR**: Non-escaping values rewritten to stack allocation

The correctness proofs support both locations - they don't perform the analysis. The IR itself (post-transformation) specifies each allocation location via `StackAlloc` or `HeapAlloc`.
