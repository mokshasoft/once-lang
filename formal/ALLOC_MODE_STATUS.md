# AllocMode Infrastructure Implementation Status

## Overview
This document tracks the implementation of AllocMode (Stack vs Heap allocation) infrastructure in the x86-64 backend.

## Completed Work

### 1. Core IR Changes ✅
- **File**: `Once/IR.agda`
- **Changes**:
  - Added `AllocMode` data type with `Stack` and `Heap` constructors
  - Updated IR constructors: `⟨_,_⟩`, `inl`, `inr`, `curry` to include `AllocMode` parameter

### 2. Escape Analysis Module ✅
- **File**: `Once/EscapeAnalysis.agda`
- **Changes**:
  - Created conservative `analyzeAlloc` function
  - Returns `Stack` only for provably safe cases (pairs in `Consuming` context)
  - Defaults to `Heap` for all other cases

### 3. Code Generation ✅
- **File**: `Once/Backend/X86/CodeGen.agda`
- **Changes**:
  - Updated pattern matching for `⟨_,_⟩`, `inl`, `inr`, `curry` to handle both `Stack` and `Heap`
  - Currently generates identical code for both modes (Stack allocation not yet implemented)

### 4. Compile-Length Proofs ✅
- **File**: `Once/Backend/X86/Correct/CompileLength.agda`
- **Changes**:
  - Split wildcard patterns into explicit `Stack` and `Heap` cases
  - Proofs are identical for both modes since code generation is identical

### 5. Individual IR Proof Files ✅
- **Files**:
  - `Once/Backend/X86/Correct/IR/Inl.agda`
  - `Once/Backend/X86/Correct/IR/Inr.agda`
  - `Once/Backend/X86/Correct/IR/Pair.agda`
- **Changes**: Added `Heap` parameter to all constructor usages

### 6. MutualIR Support Files ✅
- **Files**:
  - `Once/Backend/X86/Correct/MutualIR/Pair.agda`
- **Changes**: Updated all pair constructor usages with `Heap` parameter

### 7. Pattern Matching in Dispatcher (Partial) ⚠️
- **File**: `Once/Backend/X86/Correct/MutualIR.agda`
- **Changes**:
  - Added `Heap` patterns for `inl`, `inr`, `⟨_,_⟩`, `curry` in `run-ir-star-at-offset`
  - Added `Stack` patterns for same constructors in `run-ir-star-at-offset`
  - **Issue**: Stack patterns call proof functions that return Heap-typed results

## Remaining Work

### Critical: Make Proof Functions AllocMode-Parametric

The core issue is that proof functions are hardcoded to work with `Heap` mode, but we need them to be parametric over `AllocMode`.

#### Files Requiring Updates:

1. **Once/Backend/X86/Correct/IR/Inl.agda**
   - Function: `run-inl-star`
   - Change: Add `AllocMode` parameter and thread it through proof
   - Current signature: `run-inl-star : ∀ {A B} (prefix suffix : Program) ...`
   - New signature: `run-inl-star : ∀ {A B} (mode : AllocMode) (prefix suffix : Program) ...`

2. **Once/Backend/X86/Correct/IR/Inr.agda**
   - Function: `run-inr-star`
   - Same changes as Inl.agda

3. **Once/Backend/X86/Correct/IR/Pair.agda**
   - Functions: `run-pair-star`, proof helpers
   - Thread AllocMode through all proof steps

4. **Once/Backend/X86/Correct/IR/Curry.agda**
   - Function: `run-curry-star`
   - Thread AllocMode parameter

5. **Once/Backend/X86/Correct/MutualIR.agda**
   - Update all call sites to pass the AllocMode from pattern matching
   - Example: `run-inl-star {A} {B} Heap prefix suffix ...` for Heap pattern
   - Example: `run-inl-star {A} {B} Stack prefix suffix ...` for Stack pattern

6. **Once/Backend/X86/Correct/MutualIR/Pair.agda**
   - Update `run-pair-star-direct` to be AllocMode-parametric
   - Update `run-pair-star-direct-s` to be AllocMode-parametric

7. **Once/Backend/X86/Correct/MutualIR/Curry.agda** (if exists)
   - Update `run-curry-star-direct` to be AllocMode-parametric

#### Implementation Pattern:

```agda
-- Before:
run-inl-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  ... →
  ∃[ s' ] IRStarResult (inl {A} {B} Heap) prog s s' x (length prefix)

-- After:
run-inl-star : ∀ {A B} (mode : AllocMode) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  ... →
  let prog = prefix ++ compile-x86 (inl {A} {B} mode) ++ suffix
  in ∃[ s' ] IRStarResult (inl {A} {B} mode) prog s s' x (length prefix)
```

The key insight is that since Stack and Heap generate identical code currently, the proofs are structurally identical - we just need to thread the AllocMode parameter through to maintain type correctness.

## Testing Strategy

Once the refactoring is complete:

1. Run `make x86` to verify all x86 backend proofs compile
2. Verify that the escape analysis correctly defaults to Heap
3. Test programs should still compile and run correctly (no runtime behavior changes yet)

## Future Work (Out of Scope for Current Implementation)

1. **Actual Stack Allocation**: Modify code generation to use stack allocation for Stack mode
2. **Advanced Escape Analysis**: Implement more sophisticated analysis for additional safe cases
3. **Other Backends**: Add AllocMode support to RISC-V and ARM backends

## Notes

- The current implementation maintains a **conservative** approach: all AllocMode defaults to Heap
- Stack and Heap currently generate **identical code** - this is intentional for this phase
- The type system now tracks allocation mode, enabling future optimization work
- The modular proof structure (separate files per IR construct) made this refactoring manageable

## Estimated Remaining Effort

- Core proof function updates: 4-6 functions need AllocMode parameter added
- Call site updates: ~20-30 call sites in MutualIR.agda and related files
- Testing and verification: Full x86 backend compilation

Total estimate: 2-3 hours of focused work for an experienced Agda developer

## Contact

For questions or issues with this implementation, refer to the formal verification documentation in `formal/README.md`.
