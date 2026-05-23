# Slot Reclamation vs Trace Bounds: A Structural Analysis

## Problem Statement

The `IRResultAWF` record currently uses a single field `reclaimable-slot` for two distinct purposes:

1. **Result preservation bound**: The lowest slot index where we can safely "reclaim" (reset the frontier) without invalidating the result
2. **Trace write bound**: Upper bound on slots written by the trace

These are the same value in simple cases, but diverge when reclamation is involved.

## Background: The Slot Allocation Model

### Compile-Time vs Runtime

The Once compiler uses a **compile-time slot allocation** model:

- `next-slot`: Compile-time pointer to the next available slot
- Traces write to slots, but `next-slot` is bookkeeping only
- `exec-trace` returns a runtime `AllocState` that may differ from compile-time tracking

### Reclamation

**Reclamation** is an optimization where we reset `next-slot` to a lower value after processing, allowing slot reuse:

```
Before reclamation:
  Slots: [0...start...high-water-mark)
                |         |
          next-slot    slots written

After reclamation:
  Slots: [0...reclaim-point...high-water-mark)
                |                  |
          next-slot           still written!
```

The key insight: **reclamation changes compile-time accounting but not runtime reality**. The slots in `[reclaim-point, high-water-mark)` were still written; they just contain "dead" data that can be overwritten.

## The Two Concepts

### 1. Reclaimable Slot (Result Preservation)

The **reclaimable slot** is the lowest frontier where the result remains valid:

```agda
reclaim-preserves-result : ∀ (fits : reclaimable-slot ≤ frame-capacity) →
  BeforeFrontier (record alloc { next-slot = reclaimable-slot }) result-loc
```

This says: "If you reset `next-slot` to `reclaimable-slot`, the result location is still 'before' the frontier (i.e., valid to read)."

**Property**: The result must be stored at a slot < `reclaimable-slot`, or on heap/register.

### 2. Max Slot Written (Trace Bound)

The **max slot written** is the high-water mark of slot writes:

```agda
trace-writes-below : TraceWritesBelow max-slot-written trace
```

This says: "Every `instr-store-at-slot n` in the trace has `n < max-slot-written`."

**Property**: This bounds where the trace actually wrote, regardless of reclamation.

## Why They Diverge

Consider processing a functor layer with reclamation:

```
1. Start at next-slot = 10
2. Process children, writing to slots [10, 25)
3. Children reclaim, result at slot 12
4. Reclaim to slot 15 (child result + wrapper)
5. Final state:
   - reclaimable-slot = 15 (result is at slot 12, safe to reclaim here)
   - max-slot-written = 25 (we actually wrote up to slot 25)
```

The slots `[15, 25)` contain **dead data** from intermediate computations. They were written but are no longer needed.

## The Composition Problem

When composing IR results (e.g., cata = layer processing + algebra), we need:

```agda
-- Combined trace = layer-trace ++ alg-trace
trace-writes-below : TraceWritesBelow ? (layer-trace ++ alg-trace)
```

What should `?` be?

### Current Approach (Broken)

Currently, `IRResultAWF` uses `reclaimable-slot` for both purposes:

```agda
; reclaimable-slot = alg.reclaimable-slot
; trace-writes-below : TraceWritesBelow reclaimable-slot trace  -- WRONG!
```

This fails because:
- `layer.trace-writes-below` is bounded by `layer.max-slot-written`
- `layer.max-slot-written` can exceed `alg.reclaimable-slot`
- So the combined bound doesn't hold

### Attempted Fix (Also Broken)

Using `max(layer.max-slot-written, alg.reclaimable-slot)`:

```agda
; reclaimable-slot = max(layer.max-slot-written, alg.reclaimable-slot)
```

This fixes `trace-writes-below` but breaks `reclaim-bounded`:

```agda
reclaim-bounded : reclaimable-slot ≤ next-slot final-alloc
```

Because `final-alloc.next-slot` could be less than `layer.max-slot-written`.

## Solution: Separate the Concepts

### New IRResultAWF Fields

```agda
record IRResultAWF ... where
  field
    -- Result preservation (existing, unchanged semantics)
    reclaimable-slot : ℕ
    reclaim-monotone : next-slot alloc ≤ reclaimable-slot
    reclaim-bounded : reclaimable-slot ≤ next-slot final-alloc
    reclaim-preserves-result : ...
    reclaim-preserves-validity : ...

    -- NEW: Trace bound (high-water mark)
    max-slot-written : ℕ
    max-slot-geq-reclaim : reclaimable-slot ≤ max-slot-written
    max-slot-bounded : max-slot-written ≤ next-slot alloc +ℕ ir-stack-requirement ir

    -- CHANGED: Use max-slot-written instead of reclaimable-slot
    trace-writes-below : TraceWritesBelow max-slot-written trace
    trace-slot-reads-below : TraceSlotReadsBelow max-slot-written trace
```

### Invariant Relationships

```
next-slot alloc ≤ reclaimable-slot ≤ max-slot-written ≤ next-slot alloc + stack-requirement
                                   ≤ next-slot final-alloc + stack-requirement
```

The key insight: `max-slot-written` can exceed `next-slot final-alloc` when reclamation occurs, but it's still bounded by the stack requirement.

### Composition

For cata (layer + algebra):

```agda
cata.reclaimable-slot = alg.reclaimable-slot  -- Result is algebra's result
cata.max-slot-written = max(layer.max-slot-written, alg.max-slot-written)

-- Trace bound proof:
--   layer-trace bounded by layer.max-slot-written ≤ max(...)  ✓
--   alg-trace bounded by alg.max-slot-written ≤ max(...)      ✓
```

## Implementation Strategy

### Phase 1: Add max-slot-written to IRResultAWF

1. Add the new fields to the record
2. For non-reclaiming IRs: `max-slot-written = reclaimable-slot = next-slot final-alloc`
3. Update all constructors (295 usages across 11 files)

### Phase 2: Update Reclaiming Cases

Cases where reclamation creates divergence:
- `ProcessedLayerResult` (already has `max-slot-used`)
- `cata-dispatched-new` (composition)
- Any IR that reclaims internally

### Phase 3: Propagate Through Composition

- `ComposeWF`: `max-slot-written = max(f.max-slot-written, g.max-slot-written)`
- `PairWF`: `max-slot-written = max(fst.max-slot-written, snd.max-slot-written)`
- etc.

## Alternative: Lazy Approach

If full refactoring is too costly, a partial solution:

1. Keep `reclaimable-slot` as-is for non-cata IRs
2. Add `max-slot-written` only to `ProcessedLayerResult` (already done)
3. For cata composition, use a **separate proof** that the combined trace is bounded

This avoids changing IRResultAWF but requires case-specific handling for each composition point.

## Implementation Status (2026-04-05)

### What's Done

1. **Field types changed in ClosureWellFormed.agda** (lines 342-348):
   ```agda
   trace-writes-below : TraceWritesBelow max-slot-written trace
   trace-slot-reads-below : TraceSlotReadsBelow max-slot-written trace
   ```

2. **New field added to IRResultAWF** for the max=reclaim invariant:
   ```agda
   max-slot-eq-reclaim : max-slot-written ≡ reclaimable-slot
   ```

3. **ComposeWF.agda updated**: Uses `compose-max-slot = max-slot-f ⊔ max-slot-g` with monotonicity lifting

4. **RecTrace.agda gaps filled**: `trace-writes-below` and `trace-slot-reads-below` for cata now use proper composition

5. **RecCoreWF.agda fixed**: Pre-existing capacity conversion issue resolved

### What Needs Updating

All IR implementations need to provide the new `max-slot-eq-reclaim` field:

| IR Module | Expected Proof |
|-----------|----------------|
| SimpleWF.agda | `refl` (both defined to same value) |
| SumRecWF.agda | `refl` (both defined to same value) |
| CurryStackWF.agda | `refl` (both defined to same value) |
| ApplyWF.agda | `refl` (both defined to same value) |
| ComposeWF.agda | Prove from sub-IR equalities |
| PairWF.agda | Prove from sub-IR equalities (set max=reclaim) |
| RecCoreWF.agda | `SMP.!!` (actual reclamation in cata) |
| AnaWF.agda | `SMP.!!` (actual reclamation) |
| ParaWF.agda | `SMP.!!` (actual reclamation) |

### The Fix for PairWF

With `max-slot-eq-reclaim` available from sub-IRs, PairWF can:
1. Set `pair-max-slot = pair-reclaim` (equality, not just ≥)
2. Use sub-IR's `max-slot-eq-reclaim` to prove `max-slot-g = reclaim-g`
3. Preservation proofs like `g-preserves-fst` now work:
   - g writes in `[reclaim-f, max-slot-g)` = `[reclaim-f, reclaim-g)` (using equality)
   - fst-slot = reclaim-g is NOT in this range (strict <)
   - Therefore fst-slot is preserved ✓

## Key Insight: Two Frontiers, One Invariant

### The Problem

We now have two distinct frontiers:
1. **reclaimable-slot**: Where we can safely reset `next-slot` (result preservation)
2. **max-slot-written**: High-water mark of actual writes (trace composition)

For **recursion schemes** (Cata, Ana, Para), these can diverge:
- Layer processing writes to many slots, then reclaims
- `max-slot-written` = high-water mark > `reclaimable-slot`

For **base IRs** and **simple compositions**, they're equal:
- `max-slot-written = reclaimable-slot` by construction

### The Solution for Pair

**Pair doesn't do actual reclamation internally.** It:
1. Runs f, gets f's result at some slots
2. Runs g, gets g's result at some slots
3. Stores both in a pair at `reclaim-g + pair-slots`

If both f and g have `max = reclaim` (inductively from base cases), then:
- `max-slot-f = reclaim-f`
- `max-slot-g = reclaim-g`
- `pair-max-slot = reclaim-f ⊔ reclaim-g ⊔ (reclaim-g + ps) = reclaim-g + ps = pair-reclaim`

**So for Pair, setting `max-slot-written = reclaimable-slot` should make all proofs work as before!**

The proofs that need `fst-slot ≥ max-slot-g` become `fst-slot ≥ reclaim-g`, which is `reclaim-g ≥ reclaim-g` — trivially true.

### Stratified Approach

| IR Type | max-slot-written | Proofs |
|---------|------------------|--------|
| Base IRs | = reclaimable-slot | Work as before |
| Compose | = max(f.max, g.max) | If sub-IRs have max=reclaim, so does Compose |
| Pair | = reclaimable-slot | **Set equal** — proofs work as before |
| Cata/Ana/Para | = layer-max ⊔ alg-max | May have max > reclaim (actual reclamation) |

The key realization: **Pair doesn't need the extra generality of max > reclaim**. Only recursion schemes have actual reclamation.

## Open Problem: Cata as Sub-IR of Pair

### The Issue

For Cata, `max-slot-written ≠ reclaimable-slot` genuinely:

```
cata-max-slot = layer-max-slot ⊔ alg-max-slot
cata-reclaim = alg-reclaim
```

The layer processing has actual reclamation (Sum wrappers placed at child's reclaimable-slot), so `layer-max-slot > layer-reclaim` is possible. If `layer-max-slot > alg-max-slot`, then:

```
cata-max-slot = layer-max-slot > alg-reclaim = cata-reclaim
```

**Cata genuinely has max ≠ reclaim.** We cannot prove the equality.

### Problem for Pair

What happens when `Pair(f, g)` where `g = Cata`?

1. Pair stores f's result at `fst-slot = reclaim-g = cata-reclaim`
2. Pair runs g (Cata)
3. `g-preserves-fst` needs to prove g doesn't write to `fst-slot`

But:
- g writes in `[start, max-slot-g)` where `max-slot-g = cata-max-slot`
- `fst-slot = cata-reclaim < cata-max-slot = max-slot-g`
- So `fst-slot` is potentially in g's write range!

### Possible Solutions

1. **Detailed write analysis**: Prove Cata doesn't actually write to `reclaim` slots
   - Layer writes to `[layer-start, layer-max)`
   - Algebra writes to `[alg-start, alg-max)` where `alg-start = layer-reclaim`
   - If algebra has `max = reclaim`, then `alg-max = alg-reclaim`
   - So algebra writes to `[layer-reclaim, alg-reclaim)` — strictly less than `alg-reclaim`
   - Need to check if `layer-max > alg-reclaim` causes issues

2. **Semantic restriction**: Ensure `Pair(_, Cata)` never occurs in generated IR
   - Does the Once compiler actually generate this pattern?

3. **Different proof approach**: Find a proof strategy for Pair that doesn't need `max = reclaim`
   - Maybe use more fine-grained write bounds

4. **Restructure Cata**: Change how Cata computes its bounds
   - But can't lie about `trace-writes-below` — that would be unsound

### Questions to Resolve

- Does `Pair(_, Cata)` occur in practice in the Once compiler?
- Can we prove Cata doesn't write to its `reclaimable-slot` despite `max > reclaim`?
- Is there a more general invariant that captures both cases?

---

## Next Steps

### Tomorrow's Work

1. **Resolve the Cata question**: Determine which solution approach to take

2. **Fill `max-slot-eq-reclaim` for base IRs**: Add `; max-slot-eq-reclaim = refl` to:
   - SimpleWF.agda (Id, Fst, Snd, etc.)
   - SumRecWF.agda (Inl, Inr, Case variants)
   - CurryStackWF.agda
   - ApplyWF.agda

3. **Update ComposeWF.agda**:
   - Prove `compose-max-slot ≡ compose-reclaim` from sub-IR `max-slot-eq-reclaim`
   - Since max-slot-f = reclaim-f and max-slot-g = reclaim-g (by sub-IR equalities),
     and reclaim-g ≥ reclaim-f, we get compose-max = reclaim-g = compose-reclaim

4. **Update PairWF.agda**:
   - Set `pair-max-slot = pair-reclaim`
   - Use sub-IR `max-slot-eq-reclaim` in preservation proofs
   - Handle the Cata case based on solution chosen above

### Why This Works

Before the principled fix, we had ONE bound (`reclaimable-slot`) used for:
- Result preservation (correct use)
- Trace composition (incorrect for reclaiming cases)

After the fix, we have TWO bounds plus an equality proof:
- `reclaimable-slot` for result preservation
- `max-slot-written` for trace composition
- `max-slot-eq-reclaim` proving they're equal (for non-reclaiming IRs)

For non-reclaiming IRs, the equality proof gives us the best of both worlds:
- Trace composition works (using max-slot-written)
- Preservation proofs work (using the equality to substitute)

For reclaiming IRs (cata), the equality is postulated (SMP.!!), isolating the proof obligation to where actual reclamation occurs.

## Conclusion

The fundamental issue is that **slot reclamation** decouples two concepts:
1. Where can we safely reset the frontier? (`reclaimable-slot`)
2. Where did we actually write? (`max-slot-written`)

The clean solution is to track both explicitly, plus prove their relationship:
- `max-slot-written` represents the "physical" high-water mark
- `reclaimable-slot` represents the "logical" reclaim point
- `max-slot-eq-reclaim` proves they're equal when no reclamation occurs

For most IRs (base cases, Compose, Pair), these are equal by construction (`refl`). Only recursion schemes with layer processing have actual divergence. By making this structure explicit:
- Base IRs prove equality trivially
- Composed IRs prove equality from sub-IR equalities
- Recursion schemes have the postulate (the ONE place where the proof is hard)

This localizes the proof obligation to where actual reclamation happens, rather than spreading SMP.!! throughout the codebase.
