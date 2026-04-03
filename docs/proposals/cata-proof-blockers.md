# Cata Proof Blockers Analysis

## Current State (2026-04-03)

**17 SMP.!! markers remain** across RecTrace.agda and Stack.agda.

The cata implementation uses a capacity model based on `layer-capacity`, which tracks stack usage per functor layer. The main blocker is a mismatch between what `slot-usage-bound` proves and what Sum/Prod wrapper allocation needs.

## The Core Problem: Tight vs Non-Tight Allocation

### What slot-usage-bound proves

```agda
slot-usage-bound : reclaimable-slot ≤ next-slot alloc + layer-capacity wfF wfG alg
```

This bounds `reclaimable-slot` — where we *can* reclaim to.

### What Sum wrapper allocation needs

Sum allocates its wrapper at `next-slot final-alloc` (the actual frontier), then needs to prove:

```agda
next-slot final-alloc + 2 ≤ next-slot alloc + layer-capacity (wf-Sum wfL wfR) wfG alg
```

This requires bounding `next-slot final-alloc`, not `reclaimable-slot`.

### The gap

For most cases: `reclaimable-slot = next-slot final-alloc` (tight allocation)

But for **Prod**: `reclaimable-slot = next-slot alloc` (back to start!), while `next-slot final-alloc` is much higher.

```
Prod allocation:
  Start: slot S
  After: reclaimable = S, but next-slot final-alloc = S + 1 + capL + capR

  The pair result is stored at a location < S (heap or input location),
  so we CAN reclaim back to S. But the allocator frontier is still high.
```

When Sum wraps a Prod child:
1. Prod finishes with `reclaimable = start`, `next-slot = start + lots`
2. Sum allocates wrapper at `next-slot` (high), not at `reclaimable` (low)
3. We can't prove the wrapper fits because we only have a bound on `reclaimable`

## Capacity Model

### layer-capacity formula

```agda
layer-capacity wf-Id wfG alg = ir-stack-requirement (Cata wfG alg)
layer-capacity (wf-K _) _ alg = ir-stack-requirement alg + pair-slots
layer-capacity (wf-Sum wfL wfR) wfG alg = 2 + (capL ⊔ capR)  -- wrapper AFTER child
layer-capacity (wf-Prod wfL wfR) wfG alg = 1 + (capL ⊔ capR)  -- save-slot during children
```

### Why Sum uses `2 + max` not `max ⊔ 2`

With reclamation, Sum processing is:
1. Process child → uses capChild slots, reclaims to `l-reclaimable`
2. Allocate wrapper at reclaimed position → uses 2 more slots
3. Final: `l-reclaimable + 2 ≤ start + capChild + 2`

The wrapper is allocated AFTER the child reclaims, so we ADD 2, not take max.

### layer-cap-bound is blocked

The lemma `layer-capacity wfF wfG alg ≤ ir-stack-requirement (Cata wfG alg)` fails for Sum/Prod when children contain Id:

```
Example: wf-Sum wf-Id (wf-K Unit)
  capL = layer-capacity wf-Id = ir-stack-requirement (full!)
  layer-capacity Sum = 2 + capL = 2 + ir-req > ir-req ✗
```

The issue: Id gives the full `ir-stack-requirement`, leaving no room for parent wrappers.

## Remaining Gaps

### Category 1: Sum slot-usage-bound (2 markers)

| Location | Description |
|----------|-------------|
| Sum inj₁ | `slot-usage-bound = SMP.!!` |
| Sum inj₂ | `slot-usage-bound = SMP.!!` |

**Blocked by**: Non-tight allocation from Prod children. See core problem above.

### Category 2: layer-cap-bound (2 markers in Stack.agda)

| Location | Description |
|----------|-------------|
| Sum case | `layer-cap-bound (wf-Sum ...) = SMP.!!` |
| Prod case | `layer-cap-bound (wf-Prod ...) = SMP.!!` |

**Blocked by**: Id children give full ir-req, leaving no room for wrappers.

### Category 3: Prod reclamation proofs (2 markers)

| Location | Description |
|----------|-------------|
| Prod | `reclaim-preserves-result` |
| Prod | `reclaim-preserves-validity` |

**Blocked by**: Need to show pair result location is valid after reclaiming to start.

### Category 4: Prod capacity for right child (1 marker)

| Location | Description |
|----------|-------------|
| Prod | `r-cap` - capacity proof for right child processing |

**Blocked by**: Need `l-reclaimable ≤ suc (next-slot alloc)` to derive right child capacity.

### Category 5: Other gaps (10 markers)

| Location | Description |
|----------|-------------|
| Id case | `heap-preserved` - heap might change for heap-allocating algebras |
| K case | `valid-basetype-wf` (2x) - compound base types need decomposition |
| Prod | `alloc-correct-proof` - alloc threading through 4-phase trace |
| Prod | `processed-valid-proof` - pair validity after processing |
| Prod | `l-trace-twb`, `l-trace-tsrb` - trace bounds |
| cata-dispatched | `cap-alg` - capacity for algebra application |
| cata-dispatched | `reclaim-size-bound` - final reclamation bound |

## Potential Fixes

### Option 1: Require tight allocation

Add constraint: `reclaimable-slot = next-slot final-alloc`

**Pros**: Simplest conceptually
**Cons**: Prod can't satisfy this — it legitimately reclaims back to start

### Option 2: Add slot-bound field

Add to ProcessedLayerResult:
```agda
slot-bound : next-slot final-alloc ≤ next-slot alloc + layer-capacity wfF wfG alg
```

**Pros**: Directly proves what we need
**Cons**:
- Requires proving this for all cases
- For Prod: `next-slot final-alloc ≤ start + 1 + capL + capR`, but `layer-capacity Prod = 1 + max(capL, capR)` — doesn't fit!

### Option 3: Change Prod's layer-capacity

```agda
layer-capacity (wf-Prod wfL wfR) = 1 + capL + capR  -- not max
```

**Pros**: Matches actual Prod allocation
**Cons**:
- Larger capacity requirement
- Still need to prove `ir-stack-requirement ≥ layer-capacity`

### Option 4: Implement actual reclamation in traces

Before wrapper allocation, execute a "reclaim" that resets `next-slot`:
```agda
alloc-reclaimed = record alloc-after-sub { next-slot = l-reclaimable }
-- Execute wrapper trace from alloc-reclaimed
```

**Pros**: Wrapper is allocated at bounded position
**Cons**:
- `alloc-correct` no longer holds as equality
- Trace execution semantics become more complex

### Option 5: Change ir-stack-requirement formula

Include explicit overhead for all possible wrappers:
```agda
ir-stack-requirement (Cata wfG alg) =
  full-depth wfG * 3 + ir-stack-requirement alg + pair-slots
  -- 3 = max(2 for Sum wrapper, 1 for Prod save-slot) + safety margin
```

**Pros**: Guaranteed to have enough space
**Cons**: Over-allocates significantly

## Recommendation

**Option 4** (actual reclamation) is the cleanest semantic match:

1. Child processes, allocates up to some high-water mark
2. Child reclaims to `reclaimable-slot` (result is valid here)
3. Parent allocates wrapper starting at `reclaimable-slot`
4. Final `next-slot = reclaimable-slot + wrapper-size`

This matches the *logical* reclamation model and makes proofs straightforward. The cost is added complexity in trace execution semantics — we need to track that `final-alloc` uses the reclaimed frontier, not the actual trace output.

## Summary

The core issue is a mismatch between:
- **Logical model**: Child reclaims, parent allocates at reclaimed position
- **Actual traces**: Parent allocates at child's high-water mark

The slot-usage-bound interface proves the logical bound but the trace execution uses the actual frontier. Fixing this requires either changing the traces to match the logical model (Option 4) or changing the capacity formulas to account for actual allocation (Options 2, 3, 5).
