# Final Postulate Elimination for X86v3

This document tracks the remaining postulates in X86v3 and the approach to eliminate them.

See `proof-architecture.md` for design goals (O(1) overhead).

## Current Postulates (3 total)

| Location | Postulate | What it needs |
|----------|-----------|---------------|
| Postulates.agda | `program-bound-cap` | Legacy interface, kept for gradual migration |
| ApplyWF.agda | `slot-in-working-pair` | `slot + pair-slots ≤ ps * pb` after pair allocation |
| ApplyWF.agda | `slot-bounded-apply` | `final-slot ≤ slot + ir-req apply` |

## Progress: Two Capacity Pools Implementation

The following infrastructure is now **implemented and proven** in `Postulates.agda`:

```agda
-- Core predicates
CapacityInvariant alloc = 2 * ps * pb ≤ frame-capacity alloc
SlotInWorking alloc = next-slot alloc ≤ ps * pb

-- Main lemma (PROVEN)
program-bound-cap-from-invariant :
  CapacityInvariant alloc →
  SlotInWorking alloc →
  next-slot alloc + ps * pb ≤ frame-capacity alloc

-- Preservation lemmas (PROVEN)
invariant-preserved :
  frame-capacity alloc' ≡ frame-capacity alloc →
  CapacityInvariant alloc → CapacityInvariant alloc'

slot-in-working-preserved :
  slot + ps * ir-sz ≤ ps * pb →
  slot' ≤ slot + ps * ir-sz →
  slot' ≤ ps * pb

sub-ir-in-working :
  sf < sz →
  slot + ps * sz ≤ ps * pb →
  slot + ps * sf ≤ ps * pb
```

## Threading Through the Dispatcher

The following types now take `CapacityInvariant` and `SlotInWorking` instead of `program-bound-cap`:

- `RecDispatcherWF` (ClosureWellFormed.agda)
- `BodyCorrect.execute` (ClosureWellFormed.agda)
- `run-ir-wf` (Dispatcher.agda)
- `run-wf` / `run` (Dispatcher.agda)
- `run-compose` (ComposeWF.agda)
- `run-pair` (PairWF.agda)
- `run-curry` (CurryWF.agda)
- `run-apply` (ApplyWF.agda)

## Remaining Gap: Apply's Pair Allocation

The `slot-in-working-pair` postulate identifies a gap in the current design.

**Problem:** After apply allocates `pair-slots` for the (env, arg) pair, we need:
- `slot + pair-slots ≤ ps * pb` (SlotInWorking for alloc-pair)

**Current state:**
- We have: `slot ≤ ps * pb` (SlotInWorking for alloc)
- pair-slots = 2

**Issue:** If `ps * pb = 2` (i.e., pb = 1), then slot = 0 is required.
For general pb, we need `slot ≤ ps * pb - pair-slots = ps * (pb - 1)`.

**Potential fixes:**
1. **Tighter SlotInWorking invariant:** Track `slot ≤ ps * (pb - 1)` instead
2. **Separate apply pool:** Apply gets its own small allocation pool
3. **Three pools:** Working + Apply + Reserved

For now, this is documented as a known gap with a local postulate.

## How to Use (Migration Guide)

To eliminate the legacy `program-bound-cap` postulate in a module:

1. Import the lemmas from ClosureWellFormed:
   ```agda
   open ClosureWellFormedDef {FS} program-bound
     using (CapacityInvariant; SlotInWorking;
            program-bound-cap-from-invariant;
            invariant-preserved; slot-in-working-preserved)
   ```

2. Add `CapacityInvariant alloc` and `SlotInWorking alloc` as preconditions

3. After running sub-IR, derive invariant preservation:
   ```agda
   inv₁ = invariant-preserved alloc alloc₁ cap-eq inv
   slot-in-working₁ = slot-in-working-preserved slot slot₁ sf budget slot-bound
   ```

4. Where you need `program-bound-cap`, use:
   ```agda
   pb-cap = program-bound-cap-from-invariant alloc' inv' slot-in-working'
   ```

## Implementation Steps (Remaining)

1. ~~Thread CapacityInvariant through the dispatcher~~ ✓ DONE
2. ~~Thread SlotInWorking through the dispatcher~~ ✓ DONE
3. ~~Replace program-bound-cap usage in ComposeWF, PairWF~~ ✓ DONE
4. Fix Apply gap (slot-in-working-pair postulate)
5. Fix slot-bounded-apply (requires body execution accounting)
6. Create WholeProgram module that sets up initial invariants
7. Remove legacy program-bound-cap postulate

## Alternative Approaches (Not Recommended)

### Naive 2x Capacity
Wastes O(bound) space. Rejected.

### Copying Instead of Pointing
Changes memory model significantly. Higher complexity.

### Frame-Based Isolation
More infrastructure needed. Could be future optimization.
