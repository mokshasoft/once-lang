# Slot-Based Ownership Architecture

## Overview

This document describes the unified slot-based ownership model for memory
preservation proofs. The key insight is that **exact slot addressing**
(not inequalities) enables proving caller-input preservation without
postulates for internal function calls.

## Problem: Inequality-Based Ownership Allows Gaps

The previous ownership model used inequalities:

```agda
-- OLD: inequality-based
owned-pair-caller-stack : ... →
  addr ≥ rsp →                    -- "somewhere above rsp"
  OwnedBy Caller va rsp
```

Problems with this approach:

1. **Allows gaps**: `addr ≥ rsp` doesn't prove tight layout. The address
   could be `rsp + 1000000` — wasting stack space.

2. **Requires postulates**: We had to postulate `caller-input-owned` because
   we couldn't prove WHERE the input came from:

   ```agda
   postulate
     caller-input-owned : ∀ {A} {v : ⟦ A ⟧} {addr} {m} {rsp}
       (va : ValidAt v addr m) →
       InStack rsp →
       OwnedBy Caller va rsp
   ```

3. **Large trust boundary**: The postulate applied to ALL function entries,
   not just initial program entry.

## Solution: Exact Slot Addressing

The new model uses exact slot positions:

```agda
-- NEW: slot-based
owned-pair-caller-frame : ... →
  (caller-frame : Frame) →
  (slot : ℕ) →
  addr ≡ slot-addr caller-frame slot →   -- exact position!
  OwnedBy Caller va caller-frame
```

Benefits:

1. **Proves tight layout**: Address is at exactly `slot-addr frame k`.
   No gaps possible.

2. **Enables proof flow**: At Apply compilation, we produce evidence
   `addr ≡ slot-addr caller-frame k`. This evidence flows through.

3. **Minimal trust boundary**: Only initial program entry needs a postulate.
   Internal calls (Apply) are PROVEN.

## Architecture: Two Parallel Slot Systems

### Stack: FrameSemantics

For stack-allocated data, `FrameSemantics` provides:

```agda
record FrameSemantics : Set₁ where
  field
    Frame : Set                              -- stack frame identity
    slot-addr : Frame → ℕ → Addr             -- exact slot address
    _≺_ : Frame → Frame → Set                -- frame ordering
    frame-disjoint : ∀ f₁ f₂ k₁ k₂ →         -- ordered frames don't overlap
      f₁ ≺ f₂ → slot-addr f₁ k₁ ≢ slot-addr f₂ k₂
```

The caller/callee relationship:
- Caller's frame: where caller allocated data before the call
- Callee's frame: where callee allocates (after `sub sp, N`)
- Ordering: `callee-frame ≺ caller-frame`
- Preservation: callee writes to its frame don't touch caller's frame

### Heap: AllocatorSemantics

For heap-allocated data, `AllocatorSemantics` provides:

```agda
-- Already exists in Common/AllocatorSemantics.agda
Allocated : Addr → ℕ → Set               -- witness for n slots at addr
block-in-heap : Allocated addr n →       -- slots are in heap region
  ∀ i → i < n → InHeap (addr + i * slot-size)
blocks-disjoint : Allocated addr₁ n₁ →   -- distinct allocs don't overlap
  Allocated addr₂ n₂ → addr₁ ≢ addr₂ →
  ∀ i j → (addr₁ + i * slot-size) ≢ (addr₂ + j * slot-size)
```

### Cross-Region: Regions

Stack and heap are disjoint regions:

```agda
-- From Common/Regions.agda
stack-heap-disjoint : ∀ a → InStack a → InHeap a → ⊥
```

## OwnedBy: Unified Ownership Predicate

The `OwnedBy` predicate tracks ownership using exact slot evidence:

```agda
data OwnedBy : Owner → {A : Type} → {v : ⟦ A ⟧} → {addr : Word} → {m : Memory} →
               ValidAt v addr m → Frame → Set where

  -- Unit: always caller-owned (no memory footprint)
  owned-unit : ∀ {m} {caller-frame} →
    OwnedBy Caller valid-unit caller-frame

  -- Pair in Stack: at exact slot in caller's frame
  owned-pair-stack : ∀ {A B} {a b} {addr-a addr-b addr} {m}
    {va : ValidAt a addr-a m} {vb : ValidAt b addr-b m}
    {pairS} {is : InStack addr} →
    (slot : ℕ) →
    addr ≡ slot-addr caller-frame slot →     -- EXACT position
    OwnedBy Caller va caller-frame →
    OwnedBy Caller vb caller-frame →
    OwnedBy Caller (valid-pair va vb pairS Stack is) caller-frame

  -- Pair in Heap: uses Allocated witness
  owned-pair-heap : ∀ {A B} {a b} {addr-a addr-b addr} {m}
    {va : ValidAt a addr-a m} {vb : ValidAt b addr-b m}
    {pairS} {ih : InHeap addr} →
    Allocated addr 2 →                        -- heap allocation witness
    OwnedBy Caller va caller-frame →
    OwnedBy Caller vb caller-frame →
    OwnedBy Caller (valid-pair va vb pairS Heap ih) caller-frame

  -- ... similar for Inl, Inr, Closure, Eff, Fix
```

## Preservation Proof Strategy

### For Stack Data (FrameSemantics)

When callee writes to its frame:

```
Given:
  - OwnedBy Caller va caller-frame
  - callee-frame ≺ caller-frame (callee's frame is "further")
  - Write to slot-addr callee-frame j

Prove preservation:
  - va has addr ≡ slot-addr caller-frame k (from OwnedBy evidence)
  - By frame-disjoint: slot-addr callee-frame j ≢ slot-addr caller-frame k
  - Therefore write doesn't affect va's address
```

### For Heap Data (Region Separation)

```
Given:
  - OwnedBy Caller va caller-frame (with Allocated witness for heap addr)
  - Write to stack address

Prove preservation:
  - va's heap address satisfies InHeap
  - Write address satisfies InStack
  - By stack-heap-disjoint: addresses are different
  - Therefore write doesn't affect va
```

## Eliminating caller-input-owned

### Old Approach (Postulate)

```agda
-- Applied to ALL function entries
postulate
  caller-input-owned : ValidAt v addr m → InStack rsp → OwnedBy Caller va rsp
```

### New Approach (Proven for Apply, Postulate for Init)

**For Apply (internal calls)**: PROVEN from compilation

```agda
-- In Apply.agda
-- Caller allocates input at specific slot before call
input-slot-evidence : input-addr ≡ slot-addr caller-frame k

-- This evidence constructs OwnedBy without postulate
apply-input-owned : OwnedBy Caller input-valid caller-frame
apply-input-owned = owned-pair-stack k input-slot-evidence ...
```

**For InitState (program entry)**: Postulate (trust boundary)

```agda
-- In InitState.agda
postulate
  init-input-at-slot : init-input-addr ≡ slot-addr init-frame k

-- Constructed from postulate
init-input-owned : OwnedBy Caller init-valid init-frame
```

The trust boundary shrinks from "every function entry" to "just initial
program entry".

## Implementation Plan

### Phase 1: Update FrameSemantics ✓

Already done. `FrameSemantics` now uses:
- `Frame` type instead of `Boundary`
- `slot-addr` for exact addressing
- `_≺_` for frame ordering
- `frame-disjoint` for slot disjointness

### Phase 2: Refactor OwnedBy

1. Change parameter from `rsp : Word` to `caller-frame : Frame`
2. Replace `addr ≥ rsp` evidence with `addr ≡ slot-addr frame k`
3. Add `Allocated` witness for heap cases
4. Update all constructors

### Phase 3: Update owned-caller-preserved

1. Preservation now uses `frame-disjoint` instead of `≥` reasoning
2. Cross-region uses existing `stack-heap-disjoint`

### Phase 4: Prove apply-input-owned

1. In Apply compilation, track slot allocation
2. Produce `addr ≡ slot-addr caller-frame k` evidence
3. Construct `OwnedBy` from evidence (no postulate needed)

### Phase 5: Move postulate to InitState

1. Create `InitState.agda` with initial state setup
2. Postulate only `init-input-at-slot`
3. Remove general `caller-input-owned` postulate

## Files Affected

- `Once/Backend/Common/FrameSemantics.agda` - slot-based interface ✓
- `Once/Backend/X86/FrameInstantiation.agda` - X86 instantiation ✓
- `Once/Backend/X86/Correct/Ownership.agda` - refactor OwnedBy
- `Once/Backend/X86/Correct/Apply.agda` - prove input ownership
- `Once/Backend/X86/Correct/InitState.agda` - new file for init postulate

## Connection to AllocatorSemantics

Both `FrameSemantics` (stack) and `AllocatorSemantics` (heap) follow the
same pattern:

| Aspect | Stack (FrameSemantics) | Heap (AllocatorSemantics) |
|--------|------------------------|---------------------------|
| Block type | `Frame` | `Allocated addr n` |
| Slot address | `slot-addr frame k` | `addr + k * slot-size` |
| Disjointness source | Frame ordering `≺` | Different base addresses |
| Disjointness proof | `frame-disjoint` | `blocks-disjoint` |

The unified pattern: **abstract witness + exact slot addressing + disjointness**.

## Summary

The slot-based ownership architecture:

1. **Replaces inequalities with exact positions** - no gaps allowed
2. **Uses frame ordering for stack preservation** - callee ≺ caller
3. **Uses region separation for heap preservation** - InStack vs InHeap
4. **Enables proving caller-input ownership** for internal calls
5. **Minimizes trust boundary** to just initial program entry
