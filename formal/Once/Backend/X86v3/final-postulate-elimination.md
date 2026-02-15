# Final Postulate Elimination for X86v3

This document tracks the remaining postulates in X86v3 and strategies for eliminating them.

See `proof-architecture.md` for design goals (O(1) overhead, heap fallback).

## Current Postulates

| Location | Postulate | What it needs |
|----------|-----------|---------------|
| Postulates.agda | `program-bound-cap` | `slot + ps*bound ≤ capacity` for any alloc |
| ApplyWF:333 | `slot-bounded-apply` | `final-slot ≤ slot + ir-req apply` |

The three identical `program-bound-cap-*` postulates (from ComposeWF, PairWF, ApplyWF) were consolidated into one shared postulate in `Postulates.agda`.

## Root Cause

All capacity postulates share the same issue:

```
We have:  slot + ps * bound ≤ capacity
We need:  slot₁ + ps * bound ≤ capacity   (where slot₁ > slot)
```

After running sub-IR f, the slot advances by up to `ps * ir-size f`. The capacity precondition doesn't transfer because the slot moved.

## Rejected Solution: 2x Capacity

Requiring `slot + 2 * ps * bound ≤ capacity` works mathematically but wastes O(depth) stack space, violating our O(1) overhead goal.

## Viable Approaches

### Option A: Copying Instead of Pointing

If nested values are COPIED into their parent (not pointed to):
- `curry h` copies `closure_g` into `closure_h`
- Original slots for `closure_g` can be reclaimed
- Each IR has O(1) residue
- Capacity transfers: `slot₁ ≤ slot + O(1)`

**Proof impact:** Validity transfer becomes trivial (no pointer chains to preserve).

### Option B: Frame-Based Isolation

Each sub-IR runs in its own frame:
- Results copied to parent frame on return
- Sub-IR frame fully reclaimed
- Parent pays only for copied result

**Proof impact:** Frame ordering provides automatic disjointness.

### Option C: Heap Fallback for Deep Nesting

Since heap is always available (see proof-architecture.md):
- Stack allocate up to a fixed depth
- Beyond that depth, fall back to heap
- Capacity bound becomes: `slot + ps * MAX_STACK_DEPTH ≤ capacity`

**Proof impact:** Postulates become conditional on depth check.

### Option D: Accept O(depth) for Now

Keep postulates, document that:
- They express "stack allocation is safe here"
- Heap fallback makes them optimization hints, not soundness requirements
- Future work: implement one of the above

## Next Steps

1. Decide which approach aligns with Once's goals
2. Implement chosen approach
3. Prove postulates or remove them via heap fallback
