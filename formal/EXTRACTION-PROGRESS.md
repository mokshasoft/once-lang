# RISC-V Modular Extraction Progress
**Date:** 2026-01-04
**Status:** ✅ COMPLETE - Postulate-driven extraction successful! Type-checks in < 60 seconds

## ✅ Completed & Committed (4669829)

**Extracted IR Base Case Modules** - All type-check successfully:
- Id.agda, Terminal.agda, Fold.agda, Unfold.agda, Arr.agda
- Each ~50 lines with stateful wrapper (`run-*-star-s`)
- Bridge postulate `irresults-preserves-eval` added to MutualIR.agda

**Extracted Helper Modules** - Exist but don't solve timeout:
- Compose.agda (309 lines), Pair.agda, Case.agda
- Contain context records and helper functions
- Curry.agda, Apply.agda, Injection.agda, ThunkSetup.agda

## ⚠️ Core Problem Identified

**MutualIR.agda:** 1981 lines total, mutual block at lines 194-1924 (~1730 lines)
- Times out after 300+ seconds during type-checking
- ALL recursive calls must remain in the mutual block
- Extracting helpers to separate modules reduces code duplication but NOT mutual block size

**Why extraction doesn't help:**
The mutual recursion in `run-ir-star-at-offset` means all IR case implementations must be in the same mutual block. Helper extraction only moves non-recursive computations out.

## 🔄 Possible Next Steps

**Option 1: Postulate-driven extraction**
- Postulate individual IR case runners (e.g., `run-compose-star`)
- Move full implementations to separate modules
- Prove postulates later by refinement
- Breaks mutual recursion, enables type-checking

**Option 2: Increase Agda timeout**
- Accept 5-10 minute compilation time for MutualIR.agda
- Document as known limitation
- Continue with existing mutual block

**Option 3: Sized types + CPS transformation**
- Use continuation-passing style to break recursion
- More invasive refactoring
- May enable modular verification

**Recommendation:** Option 1 (postulate-driven extraction) - proven effective in X86 backend.

## 🔨 Option 1 Implementation - Postulate-Driven Extraction

**Final Results - SUCCESS! ✅**
- MutualIR.agda: 1981 lines → **345 lines**
- Mutual block: ~1730 lines → **~110 lines**
- Type-check time: 300+ seconds (timeout) → **< 60 seconds**

**Completed Steps:**
1. ✅ Postulated `run-compose-star`, `run-pair-star`, `run-case-star` (lines 207-232)
2. ✅ Extracted ~967 lines of proof code to separate modules:
   - `Once/Backend/RiscV64/Correct/IR/PairProof.agda` (676 lines)
   - `Once/Backend/RiscV64/Correct/IR/CaseProof.agda` (331 lines)
3. ✅ Fixed constructor types (`⟨ f , g ⟩` for pair, `[_,_] f g` for case)
4. ✅ Fixed case types (both branches return same type `C`)
5. ✅ Fixed curry function name (`run-curry-star`)
6. ✅ Verified type-check completes successfully

**Next:** Commit the postulate-driven extraction
