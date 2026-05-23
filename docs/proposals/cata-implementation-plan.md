# Cata Implementation Plan (Unoptimized)

## Goal

Implement basic catamorphism with the three-layer architecture:

```
TreeTrace (proof layer)
    ↓ treeToFlat (no optimization)
AbstractTrace (operational layer, 1-to-1 with machine)
    ↓ compile-abstract
x86-64 instructions
```

No allocation optimizations. Per-element allocation during recursion.

## Key Architectural Insight: AllocState is Compile-Time

**Critical discovery**: `AllocState` is compile-time bookkeeping, not runtime state.

Looking at `exec-abstract`:
```agda
exec-abstract (instr-alloc-stack n) s alloc =
  record s { regs = incrStackSlot (regs s) n } , alloc  -- alloc UNCHANGED!

exec-abstract (instr-push-frame cap) s alloc = s , push-frame alloc cap  -- only frame ops modify
exec-abstract instr-pop-frame s alloc = s , pop-frame alloc
```

**Implications**:
- Only `instr-push-frame` / `instr-pop-frame` (Apply IR) modify `AllocState`
- All other IRs pass `alloc` through unchanged
- `AllocState.next-slot` is compile-time tracking; instructions use literal slot numbers
- For unoptimized cata without closures: `proj₂ (exec-trace trace s alloc) ≡ alloc`

## Recent Change: Added `alloc-correct` to IRResultAWF

**Problem**: `IRResultAWF` had `trace-correct : proj₁ (exec-trace ...) ≡ final-state` but nothing for `proj₂`.

**Solution**: Added `alloc-correct : proj₂ (exec-trace trace s alloc) ≡ final-alloc` to `IRResultAWF`.

For non-Apply IRs, this is trivially `refl` since alloc passes through unchanged.
For Apply, it's provable via frame push/pop semantics.

## Current State

### Layer 3: x86-64 — COMPLETE

All AbstractInstr have x86 mappings in `AbstractToX86.agda`.

### Layer 2: AbstractTrace — COMPLETE

All instructions defined in `SMCore.agda` with complete operational semantics.

### Layer 1: TreeTrace/Proofs — PARTIAL

**10 SMP.!! markers remaining in RecTrace.agda** (updated 2026-03-31).

**Recent Progress**:
- ✓ Added `WellFormedF-irrelevant` proof to `Translate.agda`
- ✓ Filled `extract-μLayerValid` gap using proof irrelevance

## Gaps to Fill (Prioritized)

### Gap 0: Propagate alloc-correct to all IR handlers (NEW - BLOCKING)

**Problem**: Adding `alloc-correct` to `IRResultAWF` breaks all existing IR handlers.

**Files to update**:
- `SimpleWF.agda` (id, fst, snd, terminal)
- `ComposeWF.agda`
- `PairWF.agda`
- `CurryStackWF.agda`
- `ApplyWF.agda`
- `SumRecWF.agda` (inl, inr, case)
- `RecCoreWF.agda`
- `ParaWF.agda`
- `AnaWF.agda`

**Fix**: For each `IRResultAWF` construction, add:
```agda
; alloc-correct = refl  -- For non-Apply IRs (alloc unchanged)
```

For Apply:
```agda
; alloc-correct = apply-alloc-proof  -- Prove via push/pop frame semantics
```

### Gap 1: Fill alloc-correct in ProcessedLayerResult (line 762)

**Problem**: Id case converts `IRResultAWF` to `ProcessedLayerResult`.

**Fix**: Now that `IRResultAWF` has `alloc-correct`, use it:
```agda
; alloc-correct = IRResultAWF.alloc-correct rec-result
```

### Gap 2: Sum Case Validity (lines 978, 1014, 1028)

**Problem**: After processing `inj₁ x` or `inj₂ y`, need to wrap payload validity in sum validity.

**Fix**: The payload is valid at `l-result-loc`. For the unoptimized approach, return payload result directly:
```agda
; processed-valid = ProcessedLayerResult.processed-valid l-result
```

The `processed = inj₁ l-processed` wrapping is semantic, not memory layout. Memory layout stays as payload.

For line 1014 (rdi-eq for inj₂): Need `readReg (regs s) Input ≡ payload-loc`. This requires proving the setup trace establishes this.

### Gap 3: Product Case Validity (lines 1056, 1087, 1091, 1170)

**Lines 1056, 1091**: `rdi-eq` for fst/snd components. Need to prove register state after prior processing.

**Line 1087** (r-cap): Capacity arithmetic. Use:
```agda
r-cap = subst (λ c → next-slot alloc-l +ℕ ir-stack-requirement (Cata wfG alg) ≤ c)
              (ProcessedLayerResult.capacity-preserved l-result)
              (capacity-mono l-slot-mono cap)
```

**Line 1170** (processed-valid): Product validity. For unoptimized approach, return r-result's validity (sequential processing).

### Gap 4: extract-μLayerValid (line 1233)

**Problem**: Extract `μLayerValid` from `ValidAtWF` for μ-types.

**Strategy**: Pattern match on `ValidAtWF` to get `valid-μ-wf` constructor, extract the embedded `μValid`, then extract layer validity.

```agda
extract-μLayerValid wfG (valid-μ-wf .wfG x (μ-valid bf layer-valid)) = layer-valid
```

### Gap 5: Cata semantic correctness (lines 1294, 1399, 1409, 1448, 1454)

**Line 1294** (cap-alg): Capacity for algebra call.
```agda
cap-alg = capacity-after-layer layer-result cap
```

**Line 1399**: Trace independence. Use `exec-trace-same-frame` since alloc only differs in next-slot, frame is same.

**Line 1409** (result-valid-wf): Semantic equivalence. The key equation:
```
eval primSem (Cata wfG alg) x = eval primSem alg (processed-layer)
```
This follows from `sem-cata-compute`. Transport `alg-result.result-valid-wf` along this equality.

**Line 1448** (reclaim-preserves-validity): Similar transport along semantic equality.

**Line 1454** (reclaim-size-bound): Arithmetic. `ir-stack-requirement (Cata wfG alg) = ir-stack-requirement alg`.

### Gap 6: Base type validity (lines 653-654) — LOW PRIORITY

**Problem**: `valid-basetype-wf` for compound base types (Prod/Sum of base types).

**Reality**: K-layers with compound base types are rare. The K case already has `μlayer-K` which only requires `BeforeFrontier`.

**Defer**: Mark as design issue. For now, these cases likely don't occur in practice.

## Implementation Order

### Phase 1: Fix IRResultAWF breakage (Gap 0)

1. Add `; alloc-correct = refl` to all non-Apply IR handlers
2. Prove `alloc-correct` for Apply using frame push/pop
3. Verify `make agda` passes

### Phase 2: Fill ProcessedLayerResult gaps (Gaps 1-3)

1. Use `IRResultAWF.alloc-correct` for Id case
2. Fill Sum/Product validity (unoptimized: use sub-result validity directly)
3. Fill register setup proofs using exec-abstract lemmas

### Phase 3: Fill cata-dispatched gaps (Gaps 4-5)

1. Implement `extract-μLayerValid` via pattern matching
2. Fill capacity arithmetic proofs
3. Fill semantic correctness via `sem-cata-compute` transport

### Phase 4: Verify

```bash
make agda
grep -c "SMP.!!" formal/Once/CCC/Machine/IR/RecTrace.agda  # Target: 0
```

## Verification Checklist

- [ ] `alloc-correct` added to all IRResultAWF constructions
- [ ] `make agda` passes after Phase 1
- [ ] Sum inj₁/inj₂ cases: all SMP.!! filled
- [ ] Product case: all SMP.!! filled
- [ ] Id case: alloc-correct uses IRResultAWF field
- [ ] `cata-dispatched-new`: all proofs complete
- [ ] End-to-end: 0 SMP.!! in RecTrace.agda

## Non-Goals (Optimizations for Later)

- Linear in-place updates (save/restore input for sum)
- Allocation strategies (collapsing, preserving, etc.)
- Forward loops for lists
- Bulk allocation
- Parallel execution

These are Layer 2 optimizations. This plan focuses on correctness with per-element allocation.

## Detailed Blockers Analysis (Updated 2026-03-31)

### Current SMP.!! Markers (28 total after 6-trace refactoring)

The marker count increased from 10 to 28 due to Phase B restructuring. The new markers are
structural placeholders that connect the setup phases; the original blocking gaps are now
properly structured.

#### Original Gaps (preserved)
| Line | Location | Category | Status |
|------|----------|----------|--------|
| 653-654 | valid-basetype-wf | Low Priority | Unchanged |
| 1075 | Sum inj₁ processed-valid | Linear Trace | Unchanged |
| 1247 | Sum inj₂ processed-valid | Linear Trace | Unchanged |
| 1491 | Product processed-valid | Pair Validity | Unchanged |
| 1613 | cap-alg | Capacity | Unchanged |
| 1816 | reclaim-size-bound | Capacity | Unchanged |

#### Product rdi-eq Gaps (STRUCTURALLY RESOLVED)
- ~~Product left rdi-eq~~ → Now `rdi-left-setup` (line 1308, uses prod-left-setup-input)
- ~~Product right rdi-eq~~ → Now `rdi-right-setup` (line 1410, similar structure)

The rdi-eq gaps are structurally resolved: the setup traces are defined and connected
to the process-layer calls. The SMP.!! markers in the helpers (lines 732, 1410) need
to be filled with actual derivations, but the architecture is correct.

#### New Structural Placeholders (from Phase B)
| Line | Category | Description |
|------|----------|-------------|
| 732, 741, 751 | Setup helpers | prod-left-setup lemmas |
| 1325, 1334, 1340 | Left setup | layer-valid transfer, halted, capacity |
| 1384 | Transfer | r-layer-valid through left processing |
| 1410, 1414, 1419, 1422 | Right setup | rdi, halted, layer-valid, capacity |
| 1449, 1453, 1460 | Composition | trace/alloc/mem through all phases |
| 1509-1516 | Trace props | 8 trace property compositions |

### Blocker Categories

#### 1. Linear Trace for Sum (2 markers)
**Problem**: Sum processed-valid gaps (lines 1075, 1247) can't use `valid-inl-wf`/`valid-inr-wf` because:
- Current non-linear approach returns payload location as result-loc
- `valid-inl-wf` requires sum container location with pointer to payload
- Type mismatch: `ValidAtWF (inj₁ l-processed) l-result-loc` needs container structure

**Fix Required**: Implement linear trace that:
1. Saves input-loc to stack slot
2. Processes payload at payload-loc
3. Updates `sucLoc input-loc` to point to processed result
4. Returns input-loc as result (proper sum container)

#### 2. 6-Trace for Product — ✓ STRUCTURALLY COMPLETE
**Solution Applied**: Added setup traces and helpers to RecTrace.agda:
- `incr-next-slot`: Increments alloc's next-slot for slot protection
- `prod-left-setup-trace`: mov-to-output, store-at-slot, load-indirect, mov-to-input
- `prod-right-setup-trace`: load-from-slot, mov-to-input, load-indirect-suc, mov-to-input
- `prod-left-setup-input`: Proves Input = fst-loc after left setup
- Product case restructured with 4 phases: left-setup → left-process → right-setup → right-process
- Full trace: `left-setup-trace ++ l-trace ++ right-setup-trace ++ r-trace`

**Remaining work**: Fill the helper lemma bodies (straightforward derivations).

#### 3. Capacity Bounds (3 markers)
**Problem**: r-cap (line 1422), cap-alg (line 1613), reclaim-size-bound (line 1816) require:
- Proving that layer processing uses at most expected stack slots
- Now also need to account for save-slot in Product case

**Fix Required**: Add to ProcessedLayerResult:
```agda
slot-usage-bound : next-slot final-alloc ≤ next-slot alloc +ℕ layer-stack-requirement wfF
```

#### 4. WellFormedF Irrelevance — ✓ COMPLETE
**Solution Applied**: Added `WellFormedF-irrelevant` and `IsBaseType-irrelevant` proofs to
`Once/Functor/Translate.agda`. Used `subst` with irrelevance to transport layer validity
from extracted `wf` to parameter `wfG` in `extract-μLayerValid`.

#### 5. Pair Validity (1 marker)
**Problem**: Product processed-valid (line 1491) requires valid-pair-wf but:
- Need fst-loc and snd-loc for the product container
- Now have proper setup traces tracking component locations

**Depends on**: Completing the setup proof derivations.

#### 6. Low Priority (2 markers)
**Problem**: valid-basetype-wf for compound base types (lines 653-654)
- K-layers with `Prod` or `Sum` base types are rare
- Would need memory layout decomposition

**Recommendation**: Defer or mark as out of scope.

## Revised Implementation Order

### Phase A: Add WellFormedF-irrelevance (unblocks Gap 4) — ✓ COMPLETE
1. ✓ Added `IsBaseType-irrelevant` to Translate.agda
2. ✓ Added `WellFormedF-irrelevant` to Translate.agda
3. ✓ Filled extract-μLayerValid using subst

### Phase B: 6-Trace Refactoring for Product — ✓ STRUCTURALLY COMPLETE
1. ✓ Added `incr-next-slot` helper for slot protection
2. ✓ Added `prod-left-setup-trace` (4 instructions)
3. ✓ Added `prod-right-setup-trace` (4 instructions)
4. ✓ Added `prod-left-setup-input/alloc/mem-eq` helper lemmas (with SMP.!! bodies)
5. ✓ Restructured Product case with 4 phases
6. ✓ Updated full-trace to include both setup traces
7. ✓ Build compiles without OOM

**Next**: Fill helper lemma bodies with actual derivations.

### Phase C: Add slot-usage bounds (unblocks capacity proofs)
1. Define `layer-stack-requirement : WellFormedF → ℕ`
2. Add `slot-usage-bound` field to ProcessedLayerResult
3. Prove bounds for each functor case (K=0, Id=req(Cata), Sum/Prod=max of components)
4. Fill r-cap, cap-alg, reclaim-size-bound

### Phase D: Linear Trace for Sum (unblocks Sum validity)
1. Add linear trace structure to Sum cases
2. Use valid-inl-wf/valid-inr-wf with proper container locations
3. Fill processed-valid for both inj₁ and inj₂

### Phase E: Product Validity
1. Track fst-loc and snd-loc through 6-trace processing
2. Use valid-pair-wf for processed-valid

### Phase F: Cleanup
1. Address low-priority base type validity if needed
2. Final verification: `grep -c "SMP.!!" RecTrace.agda` = 0
