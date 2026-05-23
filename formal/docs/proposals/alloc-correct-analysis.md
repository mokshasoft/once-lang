# Analysis: The `alloc-correct` Field in IRResultAWF

## Current Situation

The `IRResultAWF` record contains a field:

```agda
alloc-correct : proj₂ (exec-trace trace s alloc) ≡ final-alloc
```

This claims that executing the trace produces `final-alloc`. However:

1. **Systematically unprovable**: Almost every IR module has `SMP.!!` (postulate) for this field:
   - SimpleWF.agda (6 holes)
   - ComposeWF.agda, PairWF.agda, PairStackWF.agda
   - RecCoreWF.agda (2 holes)
   - ParaWF.agda, AnaWF.agda, CurryStackWF.agda, ApplyWF.agda
   - SumRecWF.agda (10+ holes)

2. **Root cause**: There's a mismatch between:
   - `final-alloc` which is defined with `next-slot = reclaim-point` (compile-time bookkeeping)
   - `exec-trace` which mostly doesn't modify `next-slot` (runtime execution)

3. **Architectural split**: The code separates:
   - Compile-time allocation tracking (`next-slot` as frontier)
   - Runtime trace execution (stack/register operations)

   But `alloc-correct` tries to connect these, which doesn't work.

## Where Is It Used?

The field is used in RecTrace.agda for Cata proofs:

```agda
-- Line 3702
layer-runtime-eq = ProcessedLayerResult.alloc-correct layer-result

-- Line 3744
trans step4 (IRResultAWF.alloc-correct alg-result)
```

These usages chain through trace compositions to show that the final allocation state matches expectations.

## The Real Question: What Does Recursion Actually Need?

Looking at what the Cata proof actually requires:

1. **Frame preservation**: `current-frame final-alloc ≡ current-frame alloc`
2. **Slot monotonicity**: `next-slot alloc ≤ next-slot final-alloc`
3. **Heap monotonicity**: `next-heap-ref alloc ≤ next-heap-ref final-alloc`
4. **Capacity preservation**: `frame-capacity final-alloc ≡ frame-capacity alloc`

These are the **frontier invariants** - they describe how the allocation boundaries move.

The `alloc-correct` field tries to prove something stronger: that the runtime trace execution produces exactly the declared `final-alloc`. But this conflates two different concerns:

- **Semantic correctness**: The IR computes the right value
- **Allocation bookkeeping**: The frontiers move correctly

## Proposal: Remove `alloc-correct`, Keep Frontier Invariants

### Observation

The frontier invariants (`frame-preserved`, `slot-monotone`, `heap-monotone`, `capacity-preserved`) are:
1. Actually provable for all IRs
2. Sufficient for composing IRs
3. What the recursion proofs actually need

### What Recursion Needs

For Cata to work, we need to know:
1. Sub-IR doesn't escape its frame (`frame-preserved`)
2. Sub-IR's allocations are within bounds (`slot-monotone`, `heap-monotone`)
3. Capacity is preserved for nested calls (`capacity-preserved`)

We do NOT need to know that `exec-trace` produces exactly `final-alloc`. We only need the frontiers to be consistent.

### The `alloc-correct` Usages in RecTrace

Looking at the actual usages:

1. **Line 3644** - Used for `next-heap-ref` equality:
   ```agda
   trans (cong next-heap-ref (sym (ProcessedLayerResult.alloc-correct layer-result)))
         layer-runtime-heap-preserved
   ```
   This could be replaced by directly using `heap-monotone` or a dedicated heap preservation lemma.

2. **Line 3702** - Used to connect runtime alloc to declared alloc:
   ```agda
   layer-runtime-eq = ProcessedLayerResult.alloc-correct layer-result
   ```
   This is used for frame equality, which could come from `frame-preserved` directly.

3. **Line 3744** - Chaining through trace composition:
   ```agda
   trans step4 (IRResultAWF.alloc-correct alg-result)
   ```
   This could be restructured to use the actual trace execution result as the definition of `final-alloc`.

### Proposed Changes

1. **Remove `alloc-correct` from `IRResultAWF`**

2. **Redefine `final-alloc` semantically** (if needed at all):
   ```agda
   -- Option A: Remove final-alloc, use frontier fields directly
   -- Option B: Define final-alloc = proj₂ (exec-trace trace s alloc)
   ```

3. **Update RecTrace.agda** to use frontier invariants directly instead of `alloc-correct`

### Why This Is More Principled

The current `alloc-correct` tries to prove:
> "Runtime execution produces exactly this compile-time-declared allocation state"

This conflates levels. A more principled approach:
> "The frontier invariants hold between input and output allocation states"

The frontier invariants are:
- **Provable**: They follow from trace properties (writes-above, no-heap-writes, etc.)
- **Compositional**: They compose nicely for Pair, Compose, Cata
- **Sufficient**: They're all that's needed for validity preservation

## Alternative: Fix the Architecture

If we wanted to keep `alloc-correct`, we'd need to:

1. Add `instr-reclaim-to` instructions to IR traces
2. Have traces explicitly update `next-slot`
3. Define `final-alloc` to match what traces produce

But this adds complexity for no clear benefit. The frontier invariants already capture what matters.

## Recommendation

Remove `alloc-correct` and refactor RecTrace.agda to use frontier invariants directly. This:
1. Eliminates ~30 unprovable holes across the codebase
2. Makes the architecture cleaner (no conflation of compile-time/runtime)
3. Is more principled (frontiers are what matter, not exact alloc equality)

## Questions to Resolve

1. Are there any usages of `alloc-correct` that truly need exact alloc equality (not just frontier properties)?
2. Can all RecTrace usages be refactored to use `frame-preserved`, `slot-monotone`, etc.?
3. Should `final-alloc` be kept as a field, or derived from frontiers?
