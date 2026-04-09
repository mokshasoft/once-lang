# Stack Model Design Document

**Date:** 2026-04-09
**Status:** Principled design

---

## Overview

This document describes the principled stack execution model for Once IR. The key insight is that scratch space is a **local** property of each IR, requiring no global program analysis. With **perfect scratch reclaim**, each IR uses its declared scratch and returns to baseline, enabling local reasoning and MAX-based composition.

---

## 1. Core Principles

### 1.1 Unbounded Stack (No Artificial Limits)

The formal model does not assume any hardware stack limits. The stack is:
- **Unbounded**: No artificial cap on how much an IR can require
- **Not infinite**: Operations consume scratch and must declare their requirements
- **Hardware-agnostic**: Deployment checks fit against specific targets

### 1.2 Local Reasoning

Each IR is self-contained:
- Declares its scratch requirement: `ir-scratch-requirement this-ir`
- Proves it uses ≤ that requirement
- No knowledge of siblings, ancestors, or the whole program needed

### 1.3 Output vs Scratch

The stack has two kinds of allocation:

**Output slots**: Written at frontier, persist, frontier advances
- Results that live beyond the current IR
- Size may be unbounded (e.g., Cata output depends on input)

**Scratch slots**: Above outputs, fully reclaimed
- Temporary working space during computation
- Statically bounded by `ir-scratch-requirement`
- Reclaimed back to output boundary after IR completes

### 1.4 Perfect Scratch Reclaim

**Core invariants**: Frontier advances, scratch is bounded and reclaimed.

```agda
-- Frontier only advances (outputs accumulate)
output-monotone : next-slot alloc ≤ next-slot final-alloc

-- Scratch bounded relative to final frontier
scratch-bounded : max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement ir
```

After an IR completes:
- Frontier has advanced by output (runtime amount, possibly unbounded)
- All scratch above final frontier is reclaimed
- Scratch used was bounded by `ir-scratch-requirement`

**Type enforcement idea**: These invariants could be required fields in IRResultAWF - the type system would refuse to construct a valid result without providing both proofs.

---

## 2. Stack Layout

### 2.1 Frontier Model

```
┌─────────────────────────────────────┐
│  Scratch Space                      │  ← Temporary, RECLAIMED
│  - Used during current IR           │
│  - Fully reclaimed after IR         │
├─────────────────────────────────────┤ ← Scratch boundary
│  Current IR's Output                │  ← PERSISTS
│  - Written at frontier              │
│  - Advances frontier                │
├─────────────────────────────────────┤ ← Initial frontier (next-slot alloc)
│  Previous Outputs / Preserved Data  │  ← Protected from writes
│  - Results from earlier operations  │
└─────────────────────────────────────┘
```

**Type enforcement idea**: `BeforeFrontier` could be a type witness rather than just a predicate. Write operations might require proof that the target is at or above the frontier, making writes below frontier unrepresentable.

### 2.2 Dynamic Growth and Shrink

Each IR fully reclaims its own scratch (per invariants). Outputs persist at frontier.

```
Execute ⟨f, g⟩ with frontier = n:

1. f runs:
   - Output (fst) at n, frontier = n+1
   - f uses scratch above n+1
   - f reclaims its scratch (invariant: scratch-bounded)

2. g runs:
   - Output (snd) at n+1, frontier = n+2
   - g uses scratch above n+2
   - g reclaims its scratch (invariant: scratch-bounded)

Final frontier = n+2 (fst, snd persist), all scratch reclaimed
```

This follows from the invariants - no special handling needed.

---

## 3. Local Scratch Requirement

### 3.1 One Static Metric

Each IR has one statically-computable property:

```agda
ir-scratch-requirement : ∀ {A B} → IR A B → ℕ  -- max scratch slots (reclaimed)
```

This is a **local** property - computed from just this IR's structure.

Output size is NOT statically known (e.g., Cata output depends on input).

**Type enforcement idea**: `ir-scratch-requirement` could be defined by pattern matching on IR constructors, ensuring totality and guaranteeing the computation is purely structural with no escape hatches.

### 3.2 Local Correctness

Each IR proves:

```agda
-- Frontier only advances
output-monotone : next-slot alloc ≤ next-slot final-alloc

-- Scratch bounded relative to final frontier
scratch-bounded : max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement ir
```

Combined, these ensure:
- Outputs persist at frontier (wherever it ends up)
- Scratch is fully reclaimed
- Scratch usage is statically bounded

### 3.3 No Global Analysis

To know scratch usage at any point:
- Scratch: `ir-scratch-requirement current-ir` (static)
- Output: wherever frontier ends up (runtime)
- No knowledge of siblings or ancestors needed

---

## 4. Composition with Perfect Reclaim

Since each IR satisfies the invariants (`output-monotone`, `scratch-bounded`), each IR
fully reclaims its own scratch. This enables MAX-based composition.

### 4.1 Sequential Composition (Compose)

```
Execute g ∘ f with frontier = n:

1. f runs:
   - Output at n, frontier advances to n + output-f
   - f uses scratch above, f reclaims (per invariants)

2. g runs (input is f's output):
   - Output at frontier, frontier advances
   - g uses scratch above, g reclaims (per invariants)
```

```agda
ir-scratch-requirement (g ∘ f) = max scratch-f scratch-g
```

MAX because f fully reclaims before g starts - they share scratch region.

**Type enforcement idea**: The composition proof could require sub-proofs for f and g, then combine them structurally. Given that f satisfies `scratch-bounded` and g satisfies `scratch-bounded`, the composed proof follows from the MAX formula.

### 4.2 Parallel Composition (Pair)

```
Execute ⟨f, g⟩ with frontier = n:

1. f runs:
   - Output (fst) at n, frontier = n+1
   - f uses scratch above, f reclaims (per invariants)

2. g runs:
   - Output (snd) at n+1, frontier = n+2
   - g uses scratch above, g reclaims (per invariants)

3. Pair result references fst, snd
```

```agda
ir-scratch-requirement (⟨ f , g ⟩) = 1 + max scratch-f scratch-g  -- 1 for save-slot
```

MAX because f reclaims before g starts.

### 4.3 Sum (Case)

Only one branch executes, and it reclaims per invariants:

```agda
ir-scratch-requirement (case f g) = max scratch-f scratch-g
```

### 4.4 Recursion Schemes

For Cata, Ana, etc.:
- Output: unbounded (depends on input structure)
- Scratch: bounded by functor structure (product-depth, sum-depth) + algebra scratch

Each layer reclaims per invariants. Scratch has no dependence on input size.

---

## 5. Output vs Scratch

### 5.1 Scratch (Temporary)

- Allocated above current output frontier
- Used during computation
- Fully reclaimed after IR completes
- **Statically bounded** by `ir-scratch-requirement`

### 5.2 Output (Persistent)

- Written at frontier, advances frontier
- Persists after IR completes
- Becomes input for next IR or final result
- **Not statically bounded** (e.g., Cata depends on input)

### 5.3 AllocMode

**Heap mode**:
- Output allocated on heap
- Stack holds pointer (small, bounded)

**Stack mode**:
- Output written directly to stack
- May be large (unbounded for recursive outputs)

### 5.4 The Key Distinction

```
Output:  runtime size, persists, frontier advances
Scratch: static bound, temporary, reclaimed after IR
```

The invariant `scratch-bounded` is relative to final frontier:
```agda
max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement ir
```

This works regardless of how much output was produced.

**Type enforcement idea**: The type system doesn't need to track output size - `scratch-bounded` is relative to `final-alloc`, so output size cancels out. One could also consider indexed types to distinguish scratch slots from output slots, though this may be unnecessary overhead.

---

## 6. Curry/Apply and Child Frames

### 6.1 Curry

Creates a closure (code pointer + captured environment):
- Output: closure representation (persists)
- Scratch: whatever needed to build closure (reclaimed per invariants)
- Captures body's `ir-scratch-requirement` for use by apply

```agda
ir-scratch-requirement (curry body) = closure-build-scratch
```

### 6.2 Apply

Invokes closure in a **child frame**:
- Pushes new frame for body execution
- Child frame has its own frontier (starts at 0)
- Body satisfies same invariants in child frame (reclaims its scratch)
- Body's output returned to parent

```agda
ir-scratch-requirement apply = call-overhead  -- in parent frame
-- Child frame: body satisfies same invariants independently
```

### 6.3 Recursive Application

Each frame (parent or child) satisfies the same invariants:
```agda
output-monotone : next-slot alloc ≤ next-slot final-alloc
scratch-bounded : max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement ir
```

Reclaim follows from these invariants. The model applies uniformly to all frames.

**Type enforcement idea**: Frame identity could be indexed in the AllocState type. A child frame would have a different Frame value, making its slots distinct from the parent's. The type system would prevent cross-frame slot access.

---

## 7. Input/Output and Linearity

### 7.1 Uniform Execution Model

Every IR:
- Reads from Input location
- Writes to Output location
- Never writes directly to Input

This is uniform - IR logic doesn't branch on linearity.

### 7.2 Linearity via Aliasing

For linear cases (input consumed exactly once), Output is aliased to Input:

```
Non-linear:
  Input  → [location A] ← read
  Output → [location B] ← write (separate)

Linear (aliased):
  Input  → [location A] ← read
  Output → [location A] ← write (same location!)
```

The aliasing is set up BEFORE IR runs, based on linearity analysis.

### 7.3 Benefits

- IR logic is uniform: always read Input, write Output
- No special "write to Input" semantics in IR
- Linearity analysis decides aliasing (proven once at IR level)
- In-place update is a consequence of aliasing, not special IR behavior
- Targets implement uniformly, no extra proof per architecture

**Type enforcement idea**: Aliasing could be encoded as a type parameter or data type (e.g., `AliasMode` with `Separate` and `Aliased` constructors). IR execution would be parametric over this mode, using the same code path either way. The linearity proof at IR level would justify which mode to use.

### 7.4 Memory Preservation (via Positive Reasoning)

With aliasing, preservation follows from positive characterization of writes:

```agda
-- Positive: where IR writes
writes-region : writes ∈ [next-slot alloc, max-slot-written) ∪ {output-loc}
```

Preservation is derived, not stored:
- If `loc ∉ writes-region`, then `loc` is unchanged
- `BeforeFrontier` locations are below `next-slot alloc`, hence not in writes-region
- Output location (which may alias Input) IS in writes-region

No `mem-preserved-before` field needed - just check set membership.

---

## 8. Deployment: Checking Hardware Fit

### 8.1 Compiler Emits Scratch Bounds

The compiler can emit `ir-scratch-requirement` for any IR:
```agda
ir-scratch-requirement ir -- max scratch slots (static)
```

This is a structural property, computable from IR.

Output size is NOT statically known for all IRs (e.g., Cata).

### 8.2 Fit Check

For programs with bounded output (no Cata, or Cata with bounded algebra):
```
max-stack-usage ≤ target-hardware-stack-size
```

For programs with unbounded output:
- Scratch is still bounded
- Output may require dynamic/streaming approach
- Or: heap mode for large outputs

### 8.3 No Limits in Formal Model

The formal model proves:
- Each IR satisfies `scratch-bounded` (scratch stays within requirement)
- Reclaim follows from the invariants

It does NOT prove fit against hardware - that's deployment's job.

---

## 9. Simplified IRResultAWF

### 9.1 Required Fields

With the output/scratch distinction and positive reasoning:

```agda
record IRResultAWF ... where
  field
    -- Result
    result-loc : ValueLocation FS
    final-state : LocState FS
    final-alloc : AllocState

    -- Frontier advances (output persists)
    output-monotone : next-slot alloc ≤ next-slot final-alloc

    -- Scratch bounded relative to final frontier
    scratch-bounded : max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement ir

    -- Positive characterization of writes (replaces mem-preserved-before)
    trace-writes-above : TraceWritesAbove (next-slot alloc) trace
    trace-writes-below : TraceWritesBelow max-slot-written trace
    -- Combined: writes ∈ [next-slot alloc, max-slot-written) ∪ {result-loc}

    -- ... other semantic fields
```

Memory preservation is **derived** from the positive write bounds, not stored as a field.

**Type enforcement idea**: The record structure itself serves as enforcement - one cannot construct an IRResultAWF without providing all required proofs. Derived properties like memory preservation would be functions that compute from the stored fields, not separate obligations.

### 9.2 Removed Fields

| Field | Status |
|-------|--------|
| `frame-capacity` | Removed - no capacity limits |
| `reclaimable-slot` | Removed - implicit (= next-slot final-alloc) |
| `reclaim-monotone` | Subsumed by `output-monotone` |
| `reclaim-bounded` | Subsumed by `scratch-bounded` |
| `mem-preserved-before` | Removed - derived from positive `writes-region` |
| `frame-preserved` | Removed - use `alloc-changes` |
| `capacity-preserved` | Removed - with `frame-capacity` |

---

## 10. Positive vs Negative Invariants

### 10.1 The Problem with Negative Invariants

Current IRResultAWF has many "preserved" invariants:
- `mem-preserved-before`: memory below frontier is preserved
- `frame-preserved`: frame is preserved
- `capacity-preserved`: capacity is preserved
- `trace-preserves-capacity`: trace doesn't push frames
- `trace-no-heap-writes`: trace doesn't write heap
- `trace-preserves-halted`: trace doesn't change halted

These are NEGATIVE - they say what ISN'T changed. Better to have POSITIVE invariants that say what IS done, then derive preservation.

### 10.2 Current Positive Invariants (Good)

We already have positive characterizations:
```agda
-- Where writes go (positive)
trace-writes-above : TraceWritesAbove (next-slot alloc) trace    -- writes ≥ frontier
trace-writes-below : TraceWritesBelow max-slot-written trace     -- writes < max-slot
result-loc : ValueLocation FS                                     -- output location

-- Combined: writes are in [next-slot, max-slot) ∪ {result-loc}
```

From this, `mem-preserved-before` is DERIVABLE:
- If writes are in [next-slot, max-slot) ∪ {result-loc}
- Then locations outside this region are preserved
- `BeforeFrontier` locations are outside (below frontier)
- Therefore they are preserved

### 10.3 Migration Plan

| Negative (current) | Positive (target) | Status |
|--------------------|-------------------|--------|
| `mem-preserved-before` | Derive from `trace-writes-above/below` | Should migrate |
| `frame-preserved` | "IR only modifies next-slot, next-heap-ref" | Should migrate |
| `capacity-preserved` | Same as above | Should migrate (or remove with frame-capacity) |
| `trace-preserves-capacity` | "trace ∈ allowed-instructions" | Could migrate |
| `trace-no-heap-writes` | Same | Could migrate |
| `trace-preserves-halted` | Same | Could migrate |

### 10.4 Target Model

**Positive invariants only:**
```agda
-- What IR writes (positive characterization)
writes-region : writes ∈ [next-slot alloc, max-slot-written) ∪ {result-loc}

-- What AllocState fields change
alloc-changes : IR modifies only {next-slot, next-heap-ref}
```

**No negative invariants or lemmas.** When a proof needs to know about location X:
```agda
-- Question: "Is X unchanged?"
-- Answer: Check X ∉ writes-region
--         If X ∉ writes-region, then X is unchanged (immediate)
--         No lemma needed - just set membership
```

### 10.5 Benefits

1. **Single source of truth**: `writes-region` answers all preservation questions
2. **No lemmas**: Preservation is set membership, not a separate proof
3. **Clearer semantics**: "IR writes here" vs "IR doesn't write there, there, there..."
4. **Compositionality**: Positive regions compose (union), negative lists don't
5. **Fewer fields**: No stored negative invariants at all

**Type enforcement idea**: `writes-region` could be represented as a decidable set membership type. The question "is X unchanged?" becomes checking `X ∉ writes-region`, which is decidable given the bounds. This shifts from proving preservation to computing region membership.

---

## 11. Renaming and Removal

### 11.1 Renamings

| Current Name | New Name | Rationale |
|--------------|----------|-----------|
| `ir-stack-requirement` | `ir-scratch-requirement` | It's scratch, not total stack |
| `layer-capacity` | `layer-scratch` | Same |
| `slot-stays-in-budget` | `scratch-bounded` | Clarifies what's bounded |

### 11.2 Removals (use positive reasoning instead)

| Current Name | Replacement | Rationale |
|--------------|-------------|-----------|
| `frame-capacity` | (removed) | No capacity limits needed |
| `mem-preserved-before` | Use `writes-region` | Positive: check X ∉ writes-region |
| `frame-preserved` | Use `alloc-changes` | Positive: frame ∉ {next-slot, next-heap-ref} |
| `capacity-preserved` | (removed) | Removed with frame-capacity |
| `trace-preserves-capacity` | Use `writes-region` | Positive reasoning |
| `trace-no-heap-writes` | Use `writes-region` | Positive reasoning |
| `trace-preserves-halted` | Use `writes-region` | Positive reasoning |

---

## 12. Summary

**One static metric per IR**:
```agda
ir-scratch-requirement ir -- max scratch slots (static, reclaimed)
```

Output size is runtime (may be unbounded for Cata).

**Core invariants**:
```agda
-- Frontier advances (output persists)
output-monotone : next-slot alloc ≤ next-slot final-alloc

-- Scratch bounded relative to final frontier
scratch-bounded : max-slot-written ≤ next-slot final-alloc +ℕ ir-scratch-requirement ir
```

**Composition**:
- Scratch is shared (MAX) - each IR satisfies invariants, so each reclaims its scratch

**No global analysis**: Scratch requirement is a local property of IR structure

**Unbounded stack**: No artificial limits; hardware fit is a deployment concern

**Linearity via aliasing**:
- IR always reads Input, writes Output (uniform)
- For linear cases: Output aliased to Input (set up before IR runs)
- In-place update is a consequence, not special IR logic
- Proven once at IR level, targets implement uniformly

**Positive reasoning only**:
- `writes-region`: where IR writes (positive characterization)
- `alloc-changes`: which AllocState fields change
- No negative invariants - preservation is just "X ∉ writes-region"

**Benefits**:
- Clear distinction: output persists (runtime size), scratch reclaimed (static bound)
- Simple local reasoning
- No capacity threading
- MAX-based scratch composition (smaller stack usage)
- Uniform linearity handling (no per-target proofs)
- Positive invariants only (no negative lemmas)
- Clean separation of formal model and deployment

**Type enforcement approach**: The general pattern is to make illegal states unrepresentable. Rather than proving properties after construction, the types could be structured so that required proofs are part of construction, write operations require valid-target evidence, composition proofs follow structurally from sub-proofs, and preservation becomes a computed property rather than a stored invariant.
