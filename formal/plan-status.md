# Core Invariants Refactoring - Status

**Date:** 2026-04-10
**Branch:** no-ccc-proof-obligations

## Completed Phases

### Phase 1: Add scratch-bounded (DONE - previous work)
- Added `scratch-bounded` field to IRResultAWF and ProcessedLayerResult
- Proved for all IR handlers

### Phase 2: Create Derivation Functions (DONE - previous work)
- `derive-mem-preserved` exists in SMPrimitives.agda
- Used via `exec-trace-preserves-slot-below`, `exec-trace-preserves-slot-above`, etc.

### Phase 3: Remove frame-capacity (DONE)
- Removed `frame-capacity` shim function from SMCore.agda
- Removed capacity preconditions from ALL IR handlers
- Removed all `capacity-holds` calls from Dispatcher.agda

### Phase 4: Switch to Derived Preservation (DONE)
- Removed `mem-preserved-before` field from IRResultAWF in ClosureWellFormed.agda
- Added `irresult-mem-preserved` derivation function using trace-writes-above and trace-no-heap-writes
- Updated all IR handlers to remove field assignment (12 files)
- Updated PairWF2.agda and RecTrace.agda to use `irresult-mem-preserved` instead of field access
- Fixed leftover Phase 3 issues in Helper.agda (capacity-eq, trace-preserves-capacity)
- Added missing fields in Helper.agda (max-slot-written, scratch-bounded, etc.)
- All builds pass with `timeout 300 make agda MODULE=Once/CCC/Machine/Dispatcher.agda`

### Phase 6: Enforce Perfect Scratch Reclaim (DONE)
- Changed `reclaim-bounded` type from `≤` to `≡` (perfect reclaim invariant)
- Updated all IR handlers: `reclaim-bounded = refl` instead of `reclaim-bounded = ≤-refl`
- Updated ProcessedLayerResult in RecTrace.agda with same change
- Fixed Product case: `reclaimable-slot-prod = next-slot final-alloc` (no reclaim - output persists)
- Updated ComposeWF type annotation for `compose-reclaim-bounded`
- All builds pass

## Next Phases

### Phase 5: Remove Redundant Fields (DEFERRED)
- `max-slot-usage-bound` and `slot-stays-in-budget` are actively used in compositional proofs
- Removal would require deriving these on-the-fly each time
- Consider after further simplification

### Phase 7: Remove Redundant Reclaim Fields
1. Remove `reclaimable-slot`, `reclaim-monotone`, `reclaim-bounded`
2. Remove `reclaim-preserves-result`, `reclaim-preserves-validity`
3. Remove `reclaim-size-bound`

## Build Command
```bash
timeout 120 make agda MODULE=<path>
```
If timeout occurs, refactor by extracting where-clause proofs to module level.

## Key Files
- Plan: `~/.claude/plans/resilient-crunching-clock.md`
- Design doc: `formal/stack-model-design.md`
- IRResultAWF definition: `Once/CCC/Machine/ClosureWellFormed.agda`
- Main dispatcher: `Once/CCC/Machine/Dispatcher.agda`

## Commits
1. `85dfb2ff` - Add slot-stays-in-budget field and stack model design (squashed 4 commits)
2. `431de18c` - Phase 3: Remove frame-capacity from codebase
3. `3b1cc387` - Phase 4: Remove mem-preserved-before, use derived preservation
4. `b47c74ce` - Phase 6: Enforce perfect scratch reclaim
