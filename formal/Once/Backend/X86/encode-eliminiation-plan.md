# Validity Migration: Encode Elimination

## Goal
Remove encode from the proof path entirely. Change function signatures in-place from encode-based to validity-based.

---

## Completed Work

### Initial Cleanup (Commit 4811019)
1. **Compose.agda** - Deleted encode-based `run-compose-star-direct` and bridge wrapper
2. **Pair.agda** - Same pattern as Compose
3. **Case.agda** - Deleted dead bridge wrappers
4. **Dispatcher.agda** - Deleted encode-based postulate
5. **MutualIR.agda** - Updated imports

### Phase A: Extend Validity Dispatcher (Commit 1e73f88)
Extended `run-ir-star-at-offset-v` to cover ALL IR constructors.

### Phase B: Convert Case to Validity (Commit bc32d43)
Added `run-case-star-v` to Case.agda with validity input/output.

### Phase C: Convert Curry/Apply to Validity (Commit 3d5b6a8)
Added `run-curry-star-v` and `run-apply-star-v` in mutual block.

### Phase D: Add Validity Propagation (Commit 45da144)
Added postulates for direct validity propagation:
- `valid-subst-addr-mem`: propagate through unchanged memory
- `valid-subst-heap-preserved`: propagate when only heap preserved

Added raw register preservation fields:
- `TransferResult.rdi2-raw`: enables direct validity chain for compose
- `PairSetupResult.rdi-setup-raw`: rdi unchanged through setup
- `PairMiddleResult.rdi2-raw`: rdi = r14 after middle

Updated Compose and Pair to use direct validity propagation instead of round-tripping through encode.

### Phase D.5a-b: Compose Validity Helpers (Commit 578afa7)
Created fully validity-based compose helpers:
- `TransferResultV`: No encode fields, uses validity chain
- `compose-transfer-star-v`: Takes IRStarResultV, produces TransferResultV
- `assemble-compose-result-v`: Takes validity inputs, produces IRStarResultV

Updated MutualIR/Compose.agda to use these helpers - **zero bridge postulates!**

### Phase D.5c-d: Pair Validity Helpers (Commit 3f99c25)
Created validity-based pair setup/middle helpers:
- `PairSetupResultV` / `pair-setup-star-v`: No encode input needed
- `PairMiddleResultV` / `pair-middle-star-v`: Takes IRStarResultV and PairSetupResultV

### Phase D.5e-f: Pair Final Helpers & Integration (Commit f371aef)
Created validity-based pair final phase helpers:
- `make-pair-final-precond-v`: Takes all validity-based records
- `assemble-pair-result-vv`: Produces IRStarResultV directly

Updated MutualIR/Pair.agda to use all validity helpers - **zero bridge postulates!**

### Phase D.5g: Case Validity (Commit 309fee6)
Eliminated bridges from MutualIR/Case.agda:
- Added sum extraction validity postulates (`valid-inl-tag-is-0`, `valid-inl-val-ptr`, etc.)
- Updated `CaseRightSetupResult` to use raw memory reads instead of encode
- Updated `run-case-star-direct` to take ValidAt input and return IRStarResultV

Updated MutualIR/Case.agda to use direct validity - **zero bridge postulates!**

### Phase D.5h: StarBase arr Validity (Commit f9818d2)
Eliminated bridges from StarBase.agda `run-arr-star-vv`:
- Inline step execution instead of calling encode-based `run-arr-star`
- Add `valid-arrow-to-eff` postulate for type index conversion (A ⇒ B → Eff A B)
- Direct validity propagation for arr

StarBase.agda now **zero bridge postulates!**

### Phase D.5k: Curry Validity Input (WIP)
Updated `run-curry-star-direct` to take validity input:
- Changed signature from `rdi-eq : ... ≡ encode x` to `ValidAt x rdi (memory s)`
- Uses `addr-from-valid` internally for encode-based `run-curry-star`
- Constructs output validity directly from `CurryMemoryResult`
- `run-curry-star-v` is now a simple passthrough

**Note:** The internal bridging is now consolidated in one place (`curry-rdi-eq`).

### Phase D.5l: Apply Validity Input & Decomposition (WIP)
Updated `run-apply-star-direct` to take validity input:
- Changed signature from encode-based to validity-based
- Uses `valid-pair-decompose` and `valid-closure-decompose` to extract memory layout
- Calls `run-apply-to-ir-result-v` directly (no more mem-layout postulate!)
- Returns `IRStarResultV` directly
- `run-apply-star-v` is now a simple passthrough

Added new postulate:
- `valid-closure-decompose`: Extract ClosureAtS from closure validity

**Note:** Internal bridging in `run-apply-to-ir-result-v` (IR/Apply.agda) still remains.

### Phase D.5m: thunk-setup-star Validity (Commit 7f1c182)
Made thunk-setup-star fully validity-based:
- Takes ValidAt for both env and arg (not encode-eq)
- Outputs ValidAt (env, arg) alongside encode equality
- Uses heap preservation to propagate input validities
- Constructs pair validity from PairAtS layout proof

Updated curry-thunk-correct-impl:
- Passes v-arg directly (eliminates addr-from-valid for arg)
- Constructs v-env via valid-from-encode (new bridge for env)

Net change: Traded addr-from-valid usage for valid-from-encode usage in curry-thunk-correct-impl.

### Phase D.5n: ClosureWellFormed env to validity (Commit 78ea301)
Changed ClosureWellFormed interface to use env value instead of env-addr:
- ClosureWellFormed now takes `{E A B : Type}` with `env : ⟦ E ⟧` instead of `env-addr : ℕ`
- thunk-correct now takes `ValidAt env r12 mem` instead of `r12 ≡ encode env`
- Eliminated valid-from-encode bridge in curry-thunk-correct-impl (v-env passed directly)

Updated supporting files:
- Apply.agda: run-apply-with-wf now takes env value and v-env validity
- StarBase.agda: ClosureWFOutput uses env value
- ClosureContext.agda: ApplyInputWF is now a record, ClosureEntry with env value
- WholeProgram.agda: ClosureMemoryOutput with env value
- MutualIR.agda: Updated both wf constructions and curry-thunk-correct-impl

**Net change:** Eliminated 1 valid-from-encode bridge in curry (now 0 bridges in curry)

### Phase D.5o: Eliminate valid-from-encode in run-apply-to-ir-result-v (WIP)
Thread validity through apply execution to eliminate `valid-from-encode` bridge:

1. Added `rax-valid` field to `ApplyWfResult` record
2. Derived `rax-valid` in `run-apply-with-wf` from `thunk-result-valid`:
   - `thunk-result-valid thunk-res : ValidAt (semantics arg) rax (memory s-thunk)`
   - Used `valid-subst-addr-mem` to propagate through pop r15 phase
3. Changed `run-apply-to-ir-result` to return `(IRStarResult × ValidAt)` pair
4. Updated `run-apply-to-ir-result-v` to use returned validity directly

**Net change:** Eliminated 1 valid-from-encode bridge in IR/Apply.agda (2 addr-from-valid remain)

---

## Current State

### Bridge Postulate Usage

| Location | Uses addr-from-valid | Uses valid-from-encode | Status |
|----------|---------------------|----------------------|--------|
| MutualIR/Compose.agda | 0 | 0 | **Fully eliminated!** |
| MutualIR/Pair.agda | 0 | 0 | **Fully eliminated!** |
| MutualIR/Case.agda | 0 | 0 | **Fully eliminated!** |
| StarBase.agda | 0 | 0 | **Fully eliminated!** |
| fst/snd in MutualIR | 0 | 0 | **Fully eliminated!** |
| curry in MutualIR | 0 | 0 | **Fully eliminated!** |
| apply in MutualIR | 0 | 0 | **Uses validity decomposition** |
| Encode dispatcher | 5 | 5 | Input/output bridging |
| IR/Apply.agda | 2 | 0 | addr-from-valid for rdi/arg-addr |
| IR/Curry.agda | 0 | 0 | Now uses ThunkExec |
| IR/ThunkExec.agda | 2 | 0 | Internal bridging |
| MemoryValid.agda | 2 (def) | 2 (def) + 1 (usage) | Definitions + helper |

**Total bridges: 14** (reduced by 1 - eliminated valid-from-encode in apply)

### Available Validity Helpers

**Compose (complete):**
- `TransferResultV`, `compose-transfer-star-v`, `assemble-compose-result-v`

**Pair (complete):**
- `PairSetupResultV`, `pair-setup-star-v` ✓
- `PairMiddleResultV`, `pair-middle-star-v` ✓
- `make-pair-final-precond-v` ✓
- `assemble-pair-result-vv` ✓

**Projections (complete):**
- `valid-pair-decompose`: Extract component validities from pair
- `run-fst-star-vv`, `run-snd-star-vv`: Validity-based fst/snd

---

## Remaining Work (Prioritized)

### Phase D.5o: Eliminate remaining bridges in IR/Apply.agda::run-apply-to-ir-result-v
**Partially done!** The `valid-from-encode` bridge has been eliminated.
Remaining bridges:
- `addr-from-valid` for rdi-eq (line 1602)
- `addr-from-valid` for arg-addr-eq (line 1606)
These are used to construct memory layout from validity - deeper restructuring needed.

### Phase D.5p: Eliminate bridges in IR/ThunkExec.agda
The thunk execution implementation uses `addr-from-valid` internally.
This is a complex change requiring validity through thunk semantics.

### Phase D.5q: Eliminate encode-based dispatcher bridges
The encode-based `run-ir-star-at-offset` uses bridges:
- Entry: `valid-from-encode` converts rdi-eq to input_valid
- Exit: `addr-from-valid` converts result validity back
Once all IR constructors use validity internally, could delete this dispatcher.

### Phase E: Delete Bridge Postulates
Once all usages eliminated:
- Delete `addr-from-valid` postulate
- Delete `valid-from-encode` postulate

---

## Build Verification

```bash
cd /home/whatever/Repo/mokshasoft/Once/once-lang3
nix develop --command bash -c "cd formal && make x86-ccc-whole"
```

### Current Status
- [x] Build completes successfully
- [x] All IR constructors have validity paths
- [x] MutualIR/Compose.agda - zero bridge postulates
- [x] MutualIR/Pair.agda - zero bridge postulates
- [x] MutualIR/Case.agda - zero bridge postulates
- [x] StarBase.agda - zero bridge postulates
- [x] fst/snd in MutualIR - zero bridges
- [x] curry in MutualIR - zero bridges (ClosureWellFormed now takes validity)
- [x] apply in MutualIR - zero bridges (uses validity decomposition)
- [ ] IR/Apply.agda internal bridges - needs deeper validity threading
- [ ] IR/ThunkExec.agda internal bridges - needs thunk validity changes
- [ ] MemoryValid helper - needs cleanup
- [ ] Encode-based dispatcher bridges - can eliminate once all constructors validity-based
- [ ] Bridge postulates deleted (blocked on above)

---

## Proof of Concept: SUCCESS

Compose, Pair, Case, arr, fst, snd all demonstrate:
1. Validity-based helpers completely replace encode-based ones
2. The proof structure is simpler without bridging
3. Direct validity propagation is cleaner than encode round-trips

---

## Commits Summary

| Commit | Description | Status |
|--------|-------------|--------|
| 4811019 | Initial cleanup | ✓ |
| 1e73f88 | Phase A: Extend dispatcher | ✓ |
| bc32d43 | Phase B: Case validity | ✓ |
| 3d5b6a8 | Phase C: Curry/Apply | ✓ |
| 45da144 | Phase D: Propagation helpers | ✓ |
| 578afa7 | Phase D.5a-b: Compose helpers | ✓ |
| 3f99c25 | Phase D.5c-d: Pair helpers | ✓ |
| f371aef | Phase D.5e-f: Pair complete | ✓ |
| 309fee6 | Phase D.5g: Case complete | ✓ |
| f9818d2 | Phase D.5h: StarBase arr | ✓ |
| 2a8b0ce | Phase D.5i-j: fst/snd | ✓ |
| 82ebc27 | Phase D.5k: Curry validity input | ✓ |
| 4c02c48 | thunk-correct interface to validity | ✓ |
| 7f1c182 | Phase D.5m: thunk-setup-star validity | ✓ |
| 78ea301 | Phase D.5n: ClosureWellFormed env to validity | ✓ |
