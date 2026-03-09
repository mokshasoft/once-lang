# Postulate Elimination Progress

## Session Date: 2026-03-08

## Summary

Working on eliminating postulates in the Dispatcher IR files for the Once language formal verification. Major progress: fixed the fundamental pair backup-slot allocation bug and proved `g-preserves-backup`.

## Major Fix: Pair Backup Slot Allocation

### The Bug
The pair IR stored input at `backup-slot = next-slot alloc`, then dispatched f with the same `alloc`. If f allocated at its frontier (`next-slot alloc`), it would overwrite the backup.

### The Fix
1. **IR.agda**: Changed `ir-stack-requirement` for pair from `rf + rg + ps` to `1 + rf + rg + ps` (reserves backup slot)
2. **PairWF.agda**: f now runs with `alloc-after-backup` where `next-slot = suc (next-slot alloc)`
3. This ensures backup-slot is strictly below f's allocation frontier
4. `g-preserves-backup` is now trivially provable via `trace-writes-above` + `exec-trace-preserves-disjoint`

### Key Insight
With the fix, `g-preserves-backup` follows from:
- g's trace writes at slots ≥ `reclaim-f` (from `trace-writes-above`)
- `backup-slot = next-slot alloc < suc (next-slot alloc) ≤ reclaim-f`
- Therefore g can't write to backup-slot

## Completed Work

### Fully Proven (No Postulates)
1. **SumFixWF.agda**
   - `inl-inr-trace-state-correct` - Complete equational proof
   - `fold-trace-state-correct` - Reuses `inl-inr-trace-state-correct`
   - `frontier-slot-stable` for inl/inr (Stack and Heap modes) - Proven via `exec-trace-preserves-disjoint`

2. **PairWF.agda** - Key postulates eliminated:
   - `g-preserves-backup` (Stack mode) - **PROVEN** using `trace-writes-above` + `exec-trace-preserves-disjoint`
   - `g-preserves-backup` (Heap mode) - **PROVEN** using same technique

### Structurally Proven (Internal trustMe Postulates)
| File | Function | Status | Notes |
|------|----------|--------|-------|
| ComposeWF.agda | `compose-trace-state-correct` | Structural proof | trustMe-compose for frame-invariance |
| CurryWF.agda | `curry-trace-state-correct` | Structural proof | trustMe for 5-instruction sequence |
| PairWF.agda | `pair-trace-state-correct` (Stack) | Structural | trustMe-pair-stack |
| PairWF.agda | `pair-trace-state-correct` (Heap) | Structural | trustMe-pair-heap |
| PairWF.agda | `pair-frontier-stable` (Stack) | **PROVEN** | No postulates - full proof via `exec-trace-append-state` |
| PairWF.agda | `pair-frontier-stable` (Heap) | **PROVEN** | No postulates - full proof via `exec-trace-append-state` |
| SumFixWF.agda | `case-trace-state-correct` | Structural proof | trustMe-case for dispatch independence |
| ApplyWF.agda | `bound-is-final-slot` | Documented | Bounds tracking postulate |
| ApplyWF.agda | `apply-trace-state-correct` | Documented | NOTE: Trace marked as incomplete |

## Remaining Postulates in PairWF.agda (2 total)

1. **`trustMe-pair-stack`** (line ~650): Full trace correctness for Stack mode
2. **`trustMe-pair-heap`** (line ~1485): Full trace correctness for Heap mode

Both require a **frame-independence lemma** to prove formally:
- f-trace and g-trace don't read or write to `backup-slot`
- Running them on states differing only at `backup-slot` produces states differing only at `backup-slot`
- This follows from `trace-writes-above` but needs a formal statement at SlotMachine level

### Completed: `trustMe-pair-frontier` (Both Modes)
**PROVEN** (2026-03-09): The full proof uses `exec-trace-append-state` to decompose the trace into
setup + rest segments, then shows:
1. Setup writes `input-loc'` to `backup-slot` (via `output-after-mov` + `writeLoc-read-same`)
2. Rest-trace preserves `backup-slot` (via `rest-writes-above` + `exec-trace-preserves-disjoint`)

Key proof composition:
```agda
trustMe-pair-frontier =
  let split-eq : proj₁ (exec-trace pair-trace s' alloc) ≡
                 proj₁ (exec-trace rest-trace (proj₁ setup-state) (proj₂ setup-state))
      split-eq = trans (cong ...) (exec-trace-append-state setup-trace rest-trace s' alloc)
      rest-eq : readLoc (proj₁ (exec-trace rest-trace ...)) backup-loc ≡ readLoc (proj₁ setup-state) backup-loc
      rest-eq = rest-preserves-backup (proj₁ setup-state) (proj₂ setup-state) setup-frame-unchanged
  in trans (cong (λ st → readLoc st backup-loc) split-eq) (trans rest-eq setup-backup-correct)
```

## Key Changes Made

### IR.agda
```agda
-- Pair now reserves 1 extra slot for backup
ir-stack-requirement (⟨ f , g ⟩ _) = 1 +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots
```

### PairWF.agda (both Stack and Heap modes)
```agda
-- Backup slot at the original frontier
backup-slot = next-slot alloc

-- Allocation state after reserving backup slot (for f to use)
alloc-after-backup = record alloc { next-slot = suc (next-slot alloc) }

-- f runs with alloc-after-backup, not alloc
f-exec-result = rec-wf ... alloc-after-backup ...

-- g-preserves-backup now proven (not postulated)
g-trace-writes-above-local : TraceWritesAbove reclaim-f g-trace
g-trace-writes-above-local = IRResultAWF.trace-writes-above result-g

backup-below-reclaim-f : suc backup-slot ≤ reclaim-f
backup-below-reclaim-f = IRResultAWF.reclaim-monotone result-f

g-preserves-backup-loc : ∀ (sg : LocState FS) →
  readLoc (proj₁ (exec-trace g-trace sg alloc₁-reclaimed)) backup-loc ≡ readLoc sg backup-loc
g-preserves-backup-loc sg =
  exec-trace-preserves-disjoint g-trace sg alloc₁-reclaimed backup-loc reclaim-f
    g-trace-writes-above-local backup-disjoint-from-g
```

### Arithmetic Fixes Required
Many places needed `n≤1+n` prefix when using `reclaim-monotone result-f` since f now runs with `alloc-after-backup`:
```agda
-- Before: IRResultAWF.reclaim-monotone result-f  (gave: next-slot alloc ≤ reclaim-f)
-- After:  ≤-trans (n≤1+n (next-slot alloc)) (IRResultAWF.reclaim-monotone result-f)
--         (now correctly gives: next-slot alloc ≤ suc (next-slot alloc) ≤ reclaim-f)
```

Also needed `slot+1≡suc-slot : next-slot alloc +ℕ 1 ≡ suc (next-slot alloc)` via `+-comm`.

## Key Proof Patterns

1. **Backup slot preservation via trace-writes-above**:
   - Get `TraceWritesAbove n trace` from `IRResultAWF.trace-writes-above`
   - Show backup-slot is disjoint from all write destinations
   - Use `exec-trace-preserves-disjoint` to prove preservation

2. **Slot disjointness**: `suc backup-slot ≤ fst-slot` implies `fst-slot ≢ backup-slot`

3. **Arithmetic associativity**: Use `+-assoc`, `+-comm`, `slot+1≡suc-slot` to align types

4. **Trace decomposition**: Use `exec-trace-append-state` to split composed traces

## Build Command

```bash
make ccc-x86v3
```

## Session Date: 2026-03-09

### Completed Today
1. ✅ Fixed type error in `backup-after-setup` (Stack mode) - used `output-after-mov` instead of `sym output-after-mov`
2. ✅ Proved `trustMe-pair-frontier` for Heap mode using same pattern as Stack mode
3. ✅ Documented frame-independence assumption for `trustMe-pair-stack` and `trustMe-pair-heap`

### Completed Later (2026-03-09)
4. ✅ **Added `exec-trace-slot-independent` lemma to SlotMachine.agda** - the frame-independence lemma!
   ```agda
   exec-trace-slot-independent : ∀ (trace : AbstractTrace) (s : LocState FS)
     (alloc : AllocState {FS}) (frame : Frame) (slot : ℕ) (val : ValueLocation FS) (n : ℕ) →
     current-frame alloc ≡ frame →
     suc slot ≤ n →
     TraceSlotReadsAbove n trace →
     TraceWritesAbove n trace →
     proj₁ (exec-trace trace (writeLoc s (OnStack frame slot) val) alloc) ≡
     writeLoc (proj₁ (exec-trace trace s alloc)) (OnStack frame slot) val
   ```
5. ✅ **Added `trace-slot-reads-above` field to IRResultAWF** in ClosureWellFormed.agda
6. ✅ **Added `trace-slot-reads-above` proofs to all IR WF files**:
   - PairWF.agda (Stack and Heap modes) - compositional proof using sub-IR properties
   - ComposeWF.agda - compositional proof
   - SumFixWF.agda (case inl/inr branches) - forwards from sub-IR
   - ApplyWF.agda - postulated (apply trace is incomplete)

## Progress on trustMe-pair-stack (2026-03-09)

### Key Lemmas Added
In `pair-trace-state-correct` where clause, added:
- `f-slot-indep`: f-trace preserves backup-slot via `exec-trace-slot-independent`
- `g-backup-indep`: g-trace preserves backup-slot via `exec-trace-slot-independent`

### Remaining Gap
The proof requires showing g doesn't write to fst-slot (= reclaim-g). We have:
- `trace-writes-above`: g writes at slots ≥ reclaim-f
- `fst-slot = reclaim-g ≥ reclaim-f`

So `trace-writes-above` doesn't rule out g writing to fst-slot. We need an UPPER bound:
- `trace-writes-below`: g writes at slots < reclaim-g

This property should hold semantically (g's reclaimable-slot marks where live data ends),
but it's not currently tracked in IRResultAWF.

### Options to Complete the Proof
1. ✅ **DONE** (2026-03-09): Added `trace-writes-below : TraceWritesBelow reclaimable-slot trace` to IRResultAWF
2. Restructure the semantic definition to write fst BEFORE g (matching trace order)
3. Use a different proof strategy that doesn't require this bound

## Session Date: 2026-03-09 (Continued)

### Completed: trace-writes-below Added to All IR WF Files
Added `trace-writes-below` field to IRResultAWF and proved it for all IR implementations:

1. **PairWF.agda** (Stack and Heap modes):
   - `pair-trace-writes-below`: Proves all writes are below `pair-reclaim = reclaim-g + ps`
   - backup-slot, fst-slot, snd-slot bounds proven using `m<m+n` and `suc<+2`
   - f-trace and g-trace bounds forwarded from sub-IRs via `trace-writes-below-mono`

2. **CurryWF.agda**:
   - `curry-trace-writes-below`: closure-slot < reclaim via `m<m+n`, suc closure-slot < reclaim via `suc<+2`

3. **ComposeWF.agda**:
   - `compose-trace-writes-below`: Composes f-trace (below reclaim-f ≤ reclaim-g) with g-trace (below reclaim-g)

4. **SumFixWF.agda**:
   - inl/inr (Stack and Heap): `suc<+2` for suc sum-slot bound
   - fold (Stack and Heap): `m<m+n` for sum-slot bound
   - case-f/case-g: Forwards from result-f/result-g

5. **SimpleWF.agda**:
   - All 6 records: `trace-writes-below = tt` (no slot writes)

## Session Date: 2026-03-09 (Additional Progress)

### Completed: trace-slot-reads-below Added to All IR WF Files

Added `trace-slot-reads-below : TraceSlotReadsBelow reclaimable-slot trace` field to IRResultAWF
and proved it for all IR implementations. This enables proving that traces are independent of
slots ABOVE their allocation range (completes the range bounding: reads/writes in [next-slot, reclaimable-slot)).

**SlotMachine.agda additions:**
1. `TraceSlotReadsBelow n trace`: All slot reads are at slots < n
2. `trace-reads-below-append`, `trace-reads-below-mono`: Helper lemmas
3. `exec-trace-slot-independent-above`: If n ≤ slot and trace reads/writes below n, trace is independent of slot

**Key lemma for pair proof:**
```agda
g-fst-indep : ∀ (s' : LocState FS) (val : ValueLocation FS) →
  proj₁ (exec-trace g-trace (writeLoc s' fst-loc-stack val) alloc₁-reclaimed) ≡
  writeLoc (proj₁ (exec-trace g-trace s' alloc₁-reclaimed)) fst-loc-stack val
g-fst-indep = exec-trace-slot-independent-above ... g-slot-reads-below g-writes-below
```

This proves that writing fst-slot BEFORE g produces the same result as writing AFTER g,
enabling the proof that the trace (which writes fst before g) matches the semantic
(which conceptually writes fst after g).

### Current State of pair-trace-correct

The postulate `pair-trace-correct` (Stack and Heap) now has ALL required lemmas in place:
- `f-slot-indep`: f preserves/commutes with backup-slot
- `g-backup-indep`: g preserves/commutes with backup-slot
- `g-preserves-fst`: g preserves fst-slot value (via `trace-writes-below`)
- **NEW** `g-fst-indep`: g is independent of fst-slot (via `trace-slot-reads-below`)

The postulate remains only because composing these lemmas into a single equational
proof requires tracking state through 5 trace segments with explicit type annotations.

## Session Date: 2026-03-09 (Continued - Backup Slot Validity)

### s-final Definition with Backup Slot

The pair trace writes to backup-slot (setup-trace writes input-loc to backup-slot). For s-final to match the trace output, it must include this write:

```agda
-- s₂-with-backup: the trace writes input-loc to backup-slot
backup-loc-def = OnStack (current-frame alloc) backup-slot
s₂-with-backup = write-loc s₂ backup-loc-def input-loc
s₃ = write-loc s₂-with-backup pair-loc fst-loc  -- Changed from s₂
s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
s-final = record s₄ { regs = writeReg (regs s₄) Output pair-loc }
```

### New Postulates for Validity Transfer

Added postulates to transfer validity from s₂ to s₂-with-backup:

1. **`fst-valid-s2-with-backup`** (Stack mode): ValidAtWF for fst-loc transfers from s₂ to s₂-with-backup
2. **`snd-valid-s2-with-backup`** (Stack mode): ValidAtWF for snd-loc transfers from s₂ to s₂-with-backup

These postulates are semantically correct because backup-slot is disjoint from all data locations:
- Input data is at slots < next-slot alloc (BeforeFrontier of original alloc)
- f's allocated data is at slots ≥ suc (next-slot alloc) (f ran with alloc-after-backup)
- g's allocated data is at slots ≥ reclaim-f ≥ suc (next-slot alloc)
- backup-slot = next-slot alloc is in neither range

### mem-preserved-pair Fix

Updated `mem-preserved-pair` to account for the backup-slot write:
```agda
step-backup : readLoc s₂-with-backup loc ≡ readLoc s₂ loc
step-backup = write-preserves-disjoint s₂ backup-loc-def input-loc loc
                (λ eq → at-frontier-neq-before-wf alloc loc bf eq)
```

This works because loc is BeforeFrontier alloc, so loc.slot < next-slot alloc = backup-slot.

### s₃-eq Fix

Updated `s₃-eq` to use `s₂-with-backup` instead of `s₂`:
```agda
s₃-eq : s₃ ≡ writeLoc s₂-with-backup fst-loc-stack fst-loc
s₃-eq = write-loc-eq s₂-with-backup pair-loc fst-loc
```

### Heap Mode Fixes (Same Session)

Applied the same s₂-with-backup pattern to Heap mode:
1. Added `backup-loc-def` and `s₂-with-backup` definitions
2. Added `fst-valid-s2-with-backup` and `snd-valid-s2-with-backup` postulates
3. Fixed `fst-ptr` to use `s₂-with-backup`
4. Fixed `mem-preserved-pair` to add `step-backup`

Both Stack and Heap modes now have consistent handling of the backup-slot write.

## Next Steps

1. **Prove validity transfer postulates**: The key insight is that all data locations are either < backup-slot (input) or ≥ suc backup-slot (allocations)
2. **Complete pair-trace-correct proof**: Use the key lemmas to compose the full proof
3. **Compose/Curry/SumFix postulates**: Apply similar trace-decomposition techniques
4. **Simulation proofs**: Complete AbstractSimulation.agda instruction lemmas for 1-to-1 x86 refinement

## All Remaining Postulates Summary

| File | Postulate | Type | Difficulty | Notes |
|------|-----------|------|------------|-------|
| PairWF.agda | `fst-valid-s2-with-backup` (Stack) | Validity transfer | Low | backup-slot disjoint from fst data |
| PairWF.agda | `snd-valid-s2-with-backup` (Stack) | Validity transfer | Low | backup-slot disjoint from snd data |
| PairWF.agda | `fst-valid-s2-with-backup` (Heap) | Validity transfer | Low | Same reasoning as Stack mode |
| PairWF.agda | `snd-valid-s2-with-backup` (Heap) | Validity transfer | Low | Same reasoning as Stack mode |
| PairWF.agda | `trustMe-pair-stack` | Trace correctness | Medium | Needs trace-writes-below for g |
| PairWF.agda | `trustMe-pair-heap` | Trace correctness | Medium | Same as Stack mode |
| ComposeWF.agda | `trustMe-compose` | Frame-invariance | Medium |
| ComposeWF.agda | `trustMe-compose-frontier` | Frontier stability | Low |
| CurryWF.agda | `trustMe` | 5-instr sequence | Low |
| CurryWF.agda | `trustMe-curry-frontier` | Frontier stability | Low |
| SumFixWF.agda | `trustMe-case` | Dispatch independence | Medium |
| SumFixWF.agda | `trustMe-fold-frontier` × 2 | Frontier stability | Low |
| SumFixWF.agda | `trustMe-case-frontier` × 2 | Frontier stability | Low |
| ApplyWF.agda | `bound-is-final-slot` | Bounds tracking | High |
| ApplyWF.agda | `apply-trace-state-correct` | Full trace | High (trace incomplete) |
| AbstractSimulation.agda | All `*-sim` | X86 refinement | Medium (per-instruction) |
