# Proof Architecture Migration TODO

This document tracks migration tasks to achieve the clean proof architecture.

## Priority 1: Eliminate Postulates

### [~] Replace `frame-separation` with arithmetic lemma
**File:** `MemoryValid.agda:247-250`
**Problem:** Current postulate claims ALL stack addresses differ (false!)
```agda
-- WRONG
frame-separation : InStack addr → InStack w → w ≢ addr
```
**Solution:** Create arithmetic lemma in arch-specific layer:
```agda
-- CORRECT (provable)
caller-current-disjoint : addr ≥ entry-rsp → w < entry-rsp → addr ≢ w
```
**Steps:**
1. [x] Add `caller-current-disjoint` lemma to `Arithmetic.agda`
2. [x] Add wrapper functions in `MemoryValid.agda`:
   - `caller-disjoint-from-current` - direct wrapper
   - `caller-disjoint-plus-from-current` - for addr+slot-size
3. [ ] Update call sites to use Ownership + new functions
4. [ ] Remove `frame-separation` postulate

**Call sites to migrate:**
- `MemoryValid.agda:621` - `valid-disjoint-from-stack` region-dispatch
- `MemoryValid.agda:841-903` - preservation lemmas (8 usages)
- `CaseSetup.agda:296,328,1067,1082` - 4 usages
- `ApplyInstr.agda:220,254,262,270` - 4 usages

### [ ] Eliminate `caller-stack-preserved-pair`
**File:** `IR/Pair.agda:120-122`
**Problem:** Per-IR postulate for memory preservation
**Solution:** Use `caller-input-preserved` from Ownership (pattern documented at lines 115-119)
```agda
-- OLD
valid-subst-region-preserved input-valid heap-eq caller-stack-preserved-pair

-- NEW
caller-input-preserved input-valid (rsp-in-stack cap) mem-preserved-chain
```

### [ ] Prove `stack-offset` from region bounds
**File:** `MemoryValid.agda:220-221`
**Problem:** Postulates stack region closure under `+slot-size`
**Solution:** Prove from stack region upper bound being large enough

### [ ] Prove `caller-input-owned` from call convention
**File:** `Ownership.agda:442-448`
**Problem:** Postulates that function inputs are caller-owned
**Solution:** Prove by tracking entry-rsp through IR composition

## Priority 2: Magic Numbers → Semantic Names

### [ ] Replace `+ℕ 8` with `+ℕ slot-size`
**Files affected (~30 occurrences):**
- `IR/ThunkExec.agda` - 15+ occurrences
- `IR/CaseSetup.agda` - 12+ occurrences
- `IR/ApplyInstr.agda` - 2 occurrences
- `IR/Compose.agda` - 6 occurrences
- `IR/Apply.agda` - 1 occurrence
- `ClosureContext.agda` - 2 occurrences

**Pattern:**
```agda
-- BAD
addr +ℕ 8

-- GOOD
addr +ℕ slot-size
```

## Priority 3: Encode → ValidAt Migration

### [ ] Migrate `ExecLemmas.agda` to ValidAt
**Problem:** Still has encode-based lemmas
**Solution:** Create ValidAt-based equivalents

### [ ] Complete IRStarResultV migration
**Files still using IRStarResult (encode-based):**
- [ ] `IR/Compose.agda`
- [ ] `IR/Curry.agda`
- [ ] `IR/CurryInstr.agda`
- [ ] `IR/Inl.agda`
- [ ] `IR/Inr.agda`
- [ ] `IR/PairFinal.agda`

**Reference:** `IR/Apply.agda` is fully migrated (encode-free)

## Priority 4: D041 Compliance (Abstract Arithmetic)

### [ ] Abstract arithmetic in `IR/ThunkExec.agda`
**Problem:** Heavy inline arithmetic in type signatures
**Solution:** Use abstract interface like Apply.agda does

### [ ] Abstract arithmetic in `IR/CaseSetup.agda`
**Problem:** Inline arithmetic throughout
**Solution:** Create abstract frame setup helpers

## Completed

- [x] Rename `Region` to `AllocMode` (commit 2cf08f1)
- [x] Document proof stack architecture
- [x] Add backwards-compatible aliases for migration

## Notes

### Reference Implementation
`IR/Apply.agda` demonstrates the target architecture:
- Encode-free (uses ValidAt)
- D041-compliant (abstract arithmetic interface)
- Uses `valid-in-alloc-region` for AllocMode extraction

### Portability Principle
Address arithmetic must NOT appear in portable types:
- `ValidAt` - portable (no arithmetic)
- `Ownership` - portable (no arithmetic)
- Arithmetic lemmas - architecture-specific

### Testing Migration
After each change, verify compilation:
```bash
make agda MODULE=Once/Backend/X86/Correct/<file>.agda
```
