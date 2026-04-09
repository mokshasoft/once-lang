# Slot Budget Implementation Status

**Date:** 2026-04-08
**Branch:** no-ccc-proof-obligations
**Goal:** Add `slot-stays-in-budget` field to enforce stack discipline across IR implementations

---

## Executive Summary

Successfully added the `slot-stays-in-budget` field to IRResultAWF and updated most IR implementations. The architectural change enforces that every IR execution stays within its declared stack requirement, enabling compositional capacity proofs.

**Compilation Status:** RecTrace.agda compiles past the timeout issue but has 1 remaining proof obligation in the Prod case (line ~2826).

---

## What Was Accomplished

### 1. Core Architecture (✓ Complete)

**File:** `formal/Once/CCC/Machine/ClosureWellFormed.agda`

Added field to IRResultAWF (line ~308):
```agda
-- Stack discipline: execution stays within stack requirement budget
-- Final stack frontier bounded by requirement (pointers/tags/temps)
-- Even with arbitrary-sized output (on heap), stack usage (pointers/tags) is bounded
-- Enables compositional capacity proofs: if f and g stay in bounds, so does f;g
slot-stays-in-budget : next-slot final-alloc ≤ next-slot alloc +ℕ ir-stack-requirement ir
```

**Rationale:** Stack stores pointers/tags (bounded), data lives on heap (unbounded). The requirement bounds stack usage, not output size.

### 2. Basic IR Implementations (✓ Complete)

All updated with `slot-stays-in-budget` field:

| File | Proof Strategy | Status |
|------|---------------|--------|
| **ApplyWF.agda** | `≤-refl` (allocates exactly `pair-slots`) | ✓ |
| **SimpleWF.agda** | `m≤m+n (next-slot alloc) 0` (no allocation) | ✓ |
| **ComposeWF.agda** | Compositional: `result-g.slot-stays-in-budget` composed with `reclaim-f-bound` | ✓ |
| **CurryWF.agda** | `+-monoʳ-≤ (next-slot alloc) closure-bound` | ✓ |
| **PairWF2.agda** | Reuses `pair-reclaim-size-bound` | ✓ |

### 3. Recursion Schemes (✓ Complete)

| File | Proof Strategy | Status |
|------|---------------|--------|
| **ParaWF.agda** | Reuses `reclaim-bound` | ✓ |
| **AnaWF.agda** | Reuses `reclaim-bound` | ✓ |
| **SumRecWF.agda** | Reuses `reclaim-size-bound-inl/inr` for all 6 cases | ✓ |

### 4. RecTrace.agda Refactoring (⚠️ 1 TODO Remaining)

**Motivation:** RecTrace.agda is ~78k tokens and was timing out during compilation. Extracted complex proofs to module-level helpers per `lessons-learned.md`.

#### Added Private Helper Functions (lines 150-196):

```agda
private
  sum-left-slot-budget : ∀ {FL FR G A}
    (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
    (alg : IR (⟦ G ⟧T A) A)
    (alloc : AllocState {FS})
    (l-reclaimable : ℕ)
    (alloc-after-wrapper : AllocState {FS})
    (wrapper-next-slot-eq : next-slot alloc-after-wrapper ≡ l-reclaimable +ℕ 2)
    (slot-usage-bound-inj1 : l-reclaimable ≤ next-slot alloc +ℕ layer-capacity wfL wfG alg)
    → next-slot alloc-after-wrapper ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg

  sum-right-slot-budget : ... -- Similar for right branch
```

#### ProcessedLayerResult Updates:

| Case | Strategy | Status |
|------|----------|--------|
| **K** (line ~1313) | Trivial (no allocation) | ✓ |
| **Id** (line ~1396) | `IRResultAWF.slot-stays-in-budget rec-result` | ✓ |
| **Sum inj₁** (line ~2039) | Uses `sum-left-slot-budget` helper | ✓ |
| **Sum inj₂** (line ~2650) | Uses `sum-right-slot-budget` helper | ✓ |
| **Prod** (line ~2826) | **TODO - See below** | ⚠️ |

### 5. RecCoreWF.agda Simplification (✓ Complete)

**File:** `formal/Once/CCC/Machine/IR/RecCoreWF.agda` (line ~313-318)

Simplified `run-cata-core` to pass full `ir-stack-requirement` capacity to `cata-dispatched-new`:
```agda
run-cata-core wf alg rec-wf mIn x input-loc s alloc
  input-valid-wf input-before not-halted rdi-eq combined-cap =
  -- Pass the full ir-stack-requirement capacity (cata-dispatched-new derives layer-capacity internally)
  cata-dispatched-new wf alg rec-wf x mIn input-loc s alloc
    input-valid-wf input-before not-halted rdi-eq combined-cap
```

**Impact:** `cata-dispatched-new` signature changed (line ~3522 in RecTrace.agda) to take full capacity instead of just layer-capacity.

---

## Current Status

### Compilation

```bash
cd /home/whatever/Repo/mokshasoft/Once/once-lang/formal
timeout 180 make ccc-x86-64
```

**Result:** Compiles successfully until RecTrace.agda line 2826 (Prod case).

**Error:**
```
RecTrace.agda:2826.34-55: error: [UnequalTerms]
next-slot alloc !=
next-slot (ProcessedLayerResult.final-alloc ...)
```

### Files Modified

```
 formal/Once/CCC/Machine/ClosureWellFormed.agda |   5 +
 formal/Once/CCC/Machine/IR/AnaWF.agda          |   4 +
 formal/Once/CCC/Machine/IR/ApplyWF.agda        |   4 +
 formal/Once/CCC/Machine/IR/ComposeWF.agda      |  14 ++
 formal/Once/CCC/Machine/IR/CurryWF.agda        |   4 +
 formal/Once/CCC/Machine/IR/PairWF2.agda        |   8 +
 formal/Once/CCC/Machine/IR/ParaWF.agda         |   4 +
 formal/Once/CCC/Machine/IR/RecCoreWF.agda      |   7 +-
 formal/Once/CCC/Machine/IR/RecTrace.agda       | ~150 modified
 formal/Once/CCC/Machine/IR/SimpleWF.agda       |  12 +
 formal/Once/CCC/Machine/IR/SumRecWF.agda       |   6 +
```

---

## Remaining Work

### 1. Prod Case in RecTrace.agda (Line ~2826)

**Problem:** Current proof (`slot-usage-bound-prod`) has wrong type.

**Current:**
```agda
slot-usage-bound-prod : reclaimable-slot-prod ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
slot-usage-bound-prod = m≤m+n (next-slot alloc) (layer-capacity (wf-Prod wfL wfR) wfG alg)
```
- Proves: `next-slot alloc ≤ next-slot alloc + layer-capacity`
- Uses: `reclaimable-slot-prod = next-slot alloc` (line 2868)

**Needed:**
```agda
next-slot final-alloc ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
```
- Where: `final-alloc = ProcessedLayerResult.final-alloc r-result` (line 3161)

**Key Bindings (defined in Prod case's `let` block):**
```agda
-- Line 2868
reclaimable-slot-prod = next-slot alloc

-- Line 2995
alloc-for-right = record alloc-for-left { next-slot = l-reclaimable }

-- Line 3161
final-alloc = ProcessedLayerResult.final-alloc r-result
```

**Proof Strategy:**

Need compositional proof combining both children:

1. From `l-result.slot-stays-in-budget`:
   ```agda
   next-slot (l-result.final-alloc) ≤ next-slot alloc +ℕ layer-capacity wfL wfG alg
   ```

2. After reclamation: `next-slot alloc-for-right = l-reclaimable`

3. From `r-result.slot-stays-in-budget`:
   ```agda
   next-slot final-alloc ≤ next-slot alloc-for-right +ℕ layer-capacity wfR wfG alg
   ```

4. Need to show:
   ```agda
   next-slot alloc-for-right +ℕ layer-capacity wfR ≤
   next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR)
   ```

5. Use: `layer-capacity (wf-Prod wfL wfR) = layer-capacity wfL ⊔ layer-capacity wfR`

**Recommended Approach:**

Option A: Create helper function (like Sum cases):
```agda
prod-slot-budget : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A)
  (alloc : AllocState {FS})
  (l-reclaimable : ℕ)
  (alloc-for-right : AllocState {FS})
  (final-alloc : AllocState {FS})
  (l-reclaim-eq : next-slot alloc-for-right ≡ l-reclaimable)
  (l-slot-budget : l-reclaimable ≤ next-slot alloc +ℕ layer-capacity wfL wfG alg)
  (r-slot-budget : next-slot final-alloc ≤ next-slot alloc-for-right +ℕ layer-capacity wfR wfG alg)
  → next-slot final-alloc ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
```

Option B: Inline proof using existing bindings and arithmetic lemmas.

**Files to Check:**
- Line 3160-3171: Where `final-alloc` and `slot-usage-bound-prod` are defined
- Line 2995: Where `alloc-for-right` is defined
- Line 2868: Where `reclaimable-slot-prod` is defined

### 2. Test Compilation

After fixing Prod case, verify:
```bash
cd /home/whatever/Repo/mokshasoft/Once/once-lang/formal
timeout 180 make ccc-x86-64
```

Expected: Full compilation success with only deprecation warnings.

### 3. Original Plan Postulates (If Time Permits)

From original plan (tasks #4-#5):
- Line 3799: `max-slot-usage-bound` in Cata-Core
- Line 3796: `reclaim-size-bound` in Cata-Core

**Note:** These may now be provable using the new `slot-stays-in-budget` infrastructure.

---

## Key Insights & Decisions

### 1. Stack Model Clarification

**Discovery:** Stack stores POINTERS/TAGS (bounded), not actual data (unbounded on heap).

**Impact:** `ir-stack-requirement` correctly bounds stack usage even with arbitrary-sized output.

### 2. Sequential Allocation Pattern

**Pattern:** Allocate structure pointers first, then run computations that produce arbitrary-length results.

**Example (Prod):**
```
1. Allocate pair structure (2 slots for fst/snd pointers)
2. Run fst computation → arbitrary result lives on heap, pointer stored
3. Run snd computation → arbitrary result lives on heap, pointer stored
```

### 3. Reclamation Model

**Sum cases:** Tight reclamation (reclaimable-slot = wrapper-base + 2)
**Prod case:** No reclamation (reclaimable-slot = next-slot alloc)

### 4. Compositional Capacity Proofs

**Key Property:** For `f ; g` to work compositionally:
```agda
next-slot (f's final-alloc) ≤ next-slot alloc + ir-stack-requirement f
next-slot (g's final-alloc) ≤ next-slot (f reclaimed) + ir-stack-requirement g
```

This enables proving: `next-slot (composed final-alloc) ≤ next-slot alloc + (rf + rg)`

---

## Quick Start for Tomorrow

### 1. Verify Current State
```bash
cd /home/whatever/Repo/mokshasoft/Once/once-lang/formal
git status
git diff --stat
```

### 2. Check Compilation
```bash
timeout 180 make ccc-x86-64 2>&1 | tail -50
```

Should fail at RecTrace.agda:2826 with "UnequalTerms" error.

### 3. Fix Prod Case

Navigate to RecTrace.agda line ~140 (after `sum-right-slot-budget` helper) and add:

```agda
-- Helper for Prod: compositional proof using both children's slot budgets
prod-slot-budget : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A)
  (alloc : AllocState {FS})
  (l-reclaimable : ℕ)
  (alloc-for-right : AllocState {FS})
  (final-alloc : AllocState {FS})
  -- Equations and preconditions
  (l-reclaim-eq : next-slot alloc-for-right ≡ l-reclaimable)
  (l-slot-budget : l-reclaimable ≤ next-slot alloc +ℕ layer-capacity wfL wfG alg)
  (r-slot-budget : next-slot final-alloc ≤ next-slot alloc-for-right +ℕ layer-capacity wfR wfG alg)
  → next-slot final-alloc ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
prod-slot-budget wfL wfR wfG alg alloc l-reclaimable alloc-for-right final-alloc
  l-reclaim-eq l-slot-budget r-slot-budget =
  let -- Step 1: r-slot-budget gives next-slot final-alloc ≤ next-slot alloc-for-right + capR
      -- Step 2: Substitute l-reclaim-eq: next-slot final-alloc ≤ l-reclaimable + capR
      step1 : next-slot final-alloc ≤ l-reclaimable +ℕ layer-capacity wfR wfG alg
      step1 = subst (λ n → next-slot final-alloc ≤ n +ℕ layer-capacity wfR wfG alg)
                    (sym l-reclaim-eq) r-slot-budget
      -- Step 3: From l-slot-budget: l-reclaimable ≤ next-slot alloc + capL
      -- Step 4: Monotonicity: l-reclaimable + capR ≤ (next-slot alloc + capL) + capR
      step2 : l-reclaimable +ℕ layer-capacity wfR wfG alg ≤
              (next-slot alloc +ℕ layer-capacity wfL wfG alg) +ℕ layer-capacity wfR wfG alg
      step2 = +-monoˡ-≤ (layer-capacity wfR wfG alg) l-slot-budget
      -- Step 5: Rearrange: (a + capL) + capR = a + (capL + capR)
      step3 : (next-slot alloc +ℕ layer-capacity wfL wfG alg) +ℕ layer-capacity wfR wfG alg ≡
              next-slot alloc +ℕ (layer-capacity wfL wfG alg +ℕ layer-capacity wfR wfG alg)
      step3 = +-assoc (next-slot alloc) (layer-capacity wfL wfG alg) (layer-capacity wfR wfG alg)
      -- Step 6: capL + capR ≤ capL ⊔ capR = layer-capacity (wf-Prod wfL wfR)
      step4 : layer-capacity wfL wfG alg +ℕ layer-capacity wfR wfG alg ≤
              layer-capacity (wf-Prod wfL wfR) wfG alg
      step4 = prod-capacity-sum-bound wfL wfR wfG alg  -- TODO: Check if this lemma exists
      -- Step 7: Combine
      step5 : next-slot alloc +ℕ (layer-capacity wfL wfG alg +ℕ layer-capacity wfR wfG alg) ≤
              next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
      step5 = +-monoʳ-≤ (next-slot alloc) step4
  in ≤-trans step1 (≤-trans step2 (≤-trans (≤-reflexive step3) step5))
```

**Note:** May need to find or create `prod-capacity-sum-bound` lemma. Check `Stack.agda` for how `layer-capacity (wf-Prod ...)` is defined.

### 4. Update Call Site

Navigate to line ~2826 in RecTrace.agda and replace:
```agda
; slot-stays-in-budget = slot-usage-bound-prod
```

With:
```agda
; slot-stays-in-budget = prod-slot-budget wfL wfR wfG alg alloc l-reclaimable
    alloc-for-right final-alloc l-reclaim-eq l-slot-budget r-slot-budget
```

Where you'll need to find/create the necessary bindings in the `let` block.

---

## Reference: Key File Locations

```
formal/
├── Once/CCC/Machine/
│   ├── ClosureWellFormed.agda      # IRResultAWF definition (line ~308)
│   └── IR/
│       ├── RecTrace.agda           # Main work (helpers line 150, Prod ~2826)
│       ├── RecCoreWF.agda          # Simplified (line ~313)
│       ├── ApplyWF.agda            # Complete (line ~213)
│       ├── SimpleWF.agda           # Complete (multiple)
│       ├── ComposeWF.agda          # Complete (line ~190, ~422)
│       ├── CurryWF.agda            # Complete (line ~153)
│       ├── PairWF2.agda            # Complete (line ~739)
│       ├── ParaWF.agda             # Complete (line ~213)
│       ├── AnaWF.agda              # Complete (line ~211)
│       └── SumRecWF.agda           # Complete (6 cases)
└── Once/CCC/IR/
    └── Stack.agda                  # ir-stack-requirement & layer-capacity definitions
```

---

## Questions to Resolve Tomorrow

1. Does `prod-capacity-sum-bound` lemma exist in `Stack.agda`?
   - If not, what is the exact definition of `layer-capacity (wf-Prod wfL wfR)`?
   - Is it `capL ⊔ capR` or `capL + capR`?

2. Are the bindings `l-reclaim-eq`, `l-slot-budget`, `r-slot-budget` available in the Prod case's `let` block?
   - If not, need to create them from existing bindings

3. After Prod fix, do the original plan postulates (#4-#5) still need work?

---

## Success Criteria

- [ ] RecTrace.agda compiles without errors
- [ ] `make ccc-x86-64` completes successfully (may have deprecation warnings)
- [ ] No new `SMP.!!` postulates introduced
- [ ] All `slot-stays-in-budget` fields have proofs (no holes)
- [ ] Compilation completes in <180 seconds

---

## Architectural Achievement

This work establishes **stack discipline** as an enforced invariant across the entire IR framework. Every IR must prove it stays within its declared stack requirement, enabling:

1. **Compositional reasoning:** `f ; g` capacity proof from `f` and `g` individually
2. **Frame sizing:** Child frames sized correctly using `ir-stack-requirement`
3. **No runtime checks:** All capacity violations caught at proof-time
4. **Separation:** Stack (bounded) vs heap (unbounded) made explicit

This is a significant architectural improvement to the formal verification of the Once compiler's CCC backend.
