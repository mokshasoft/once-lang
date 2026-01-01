# Shareable Backend Proof Code Refactoring

## Executive Summary

This document outlines a plan to extract common proof infrastructure from the three backend architectures (X86-64, AArch64, RiscV64) to a shared `Once/Backend/Common/` directory. The primary focus is the Star (reflexive-transitive closure) abstraction, which is nearly identical across all backends.

**Current Status**: RiscV64 refactored ✓, X86 and AArch64 pending

**Total Potential Savings**: ~226 lines (18% reduction in Star-related code)

---

## Background

### Existing Common Code

The codebase already has a well-designed `Once/Backend/Common/` directory with shared helpers:

- **Fetch.agda** - Polymorphic instruction fetch lemmas (used by all backends)
- **Memory.agda** - Memory read/write lemmas (used by all backends)
- **ProgramLemmas.agda** - List manipulation for composition (used by all backends)
- **Exec.agda** - Fuel-based execution (used by X86, AArch64; NOT RiscV64)

### Analysis Findings

The Plan agent analyzed all three backends and found:

1. **Star.agda core is 100% identical** across all architectures (~115 lines)
2. **Helper combinators** follow same pattern but vary in count per backend
3. **Architecture-specific code** (bridge lemmas, register conventions) must remain separate
4. **RiscV64 uses the cleanest approach**: star-only, no StackInvariant, minimal complexity

---

## Detailed Analysis

### 1. Star.agda Structure

#### Common Core (100% Identical)

**Location**: Lines ~27-96 in all three Star.agda files

**Components**:

1. **Star data type** (~12 lines)
   ```agda
   data Star (prog : Program) : State → State → Set where
     refl* : ∀ {s} → Star prog s s
     step* : ∀ {s s' s''} →
             halted s ≡ false →
             step prog s ≡ just s' →
             Star prog s' s'' →
             Star prog s s''
   ```

2. **Core properties** (~15 lines)
   - `star-trans` : Transitivity lemma
   - `star-single` : Single step lifter

3. **Infix operators** (~20 lines)
   - `_◅◅_` : Prepend operator (alias for star-trans)
   - `⟨_,_⟩◅_` : Build star from step proof

4. **Helper combinators** (~45 lines)
   - `star-step2` through `star-step6` (chain N steps)

**Total extractable**: ~115 lines per backend

#### Architecture-Specific Code (Must Remain)

1. **Bridge lemmas** (~200-270 lines per backend)
   - `exec-to-star`, `star-to-exec`
   - Different implementations due to varying exec semantics
   - RiscV64: Has additional helpers for with-clause issues

2. **Register conventions** (varies)
   - X86: `rax` for result
   - AArch64: `x0` for result
   - RiscV64: `a0` for result

### 2. Helper Combinator Inventory

| Backend  | star-step2 | star-step3 | star-step4 | star-step5 | star-step6 |
|----------|------------|------------|------------|------------|------------|
| X86      | ✓          | ✓          | ✓          | ✗          | ✗          |
| AArch64  | ✓          | ✓          | ✓          | ✓          | ✓          |
| RiscV64  | ✓          | ✓          | ✓          | ✓          | ✗          |

**Maximum needed**: star-step6 (for AArch64's apply instruction sequence)

**Usage**: Rarely used directly; most code uses `⟨_,_⟩◅_` combinator

### 3. File Size Comparison

| File | Lines | Extractable | Remaining | % Reduction |
|------|-------|-------------|-----------|-------------|
| X86/Correct/Star.agda | 432 | ~112 | ~320 | 26% |
| AArch64/Correct/Star.agda | 372 | ~117 | ~255 | 31% |
| RiscV64/Correct/Star.agda | 462 | ~117 | ~345 | 25% |
| **Total** | **1266** | **~346** | **~920** | **27%** |

**New Common/Star.agda**: ~120 lines

**Net reduction**: ~226 lines (18% overall)

---

## Refactoring Plan

### Phase 1: Create Common Infrastructure ✓

**File**: `Once/Backend/Common/Star.agda` (~120 lines)

**Approach**: Module parameterization

```agda
module Once.Backend.Common.Star
  (Program : Set)
  (State : Set)
  (halted : State → Bool)
  (step : Program → State → Maybe State)
  where
```

**Content**:
- Star data type and constructors
- star-trans, star-single
- Infix operators: `_◅◅_`, `⟨_,_⟩◅_`
- Helpers: star-step2 through star-step6
- Infix notation: `_⟶*_`

**Advantages of module parameters**:
- Clean separation of concerns
- No redundant type signatures
- Agda's module system handles instantiation
- Easy to import and use

**Alternative considered (rejected)**: Record-based parameterization
- More verbose
- Extra indirection
- Not worth the complexity

### Phase 2: Refactor RiscV64 ✓

**File**: `Once/Backend/RiscV64/Correct/Star.agda`

**Changes**:
1. Remove lines ~27-139 (core infrastructure)
2. Add import: `open import Once.Backend.Common.Star Program State halted step public`
3. Keep architecture-specific code:
   - Bridge lemmas (exec-to-star, helpers for with-clause issues)
   - StarResult definitions
   - RiscV64-specific combinators

**Expected reduction**: ~117 lines

**Test**: `make riscv`

**Status**: ✓ Completed

### Phase 3: Refactor X86 (Future Work)

**File**: `Once/Backend/X86/Correct/Star.agda`

**Changes**:
1. Remove lines ~27-121 (core infrastructure)
2. Add import: `open import Once.Backend.Common.Star Program State halted step public`
3. Keep architecture-specific code:
   - Bridge lemmas (exec-to-star, star-to-exec)
   - StarResult definitions
   - X86-specific helpers

**Expected reduction**: ~112 lines

**Dependencies to update**:
- `Once/Backend/X86/Correct/StarBase.agda`
- `Once/Backend/X86/Correct/MutualIR.agda`

**Test**: `make x86` (if target exists)

**Status**: Documented, not yet executed

### Phase 4: Refactor AArch64 (Future Work)

**File**: `Once/Backend/AArch64/Correct/Star.agda`

**Changes**: Same as X86

**Expected reduction**: ~117 lines

**Dependencies to update**:
- `Once/Backend/AArch64/Correct/StarBase.agda`
- `Once/Backend/AArch64/Correct/MutualIR.agda`

**Test**: Full AArch64 backend build

**Status**: Documented, not yet executed

---

## Risk Assessment

### Overall Risk: LOW-MEDIUM

| Phase | Risk Level | Failure Impact | Rollback Difficulty |
|-------|-----------|----------------|---------------------|
| Create Common/Star | **Low** | None (new file) | Trivial (delete file) |
| Refactor RiscV64 | **Medium** | Build breaks | Easy (git revert) |
| Refactor X86 | **Medium** | Build breaks | Easy (git revert) |
| Refactor AArch64 | **Medium** | Build breaks | Easy (git revert) |

**Confidence factors**:
1. Pure extraction (no logic changes)
2. Strong type system catches errors immediately
3. Can refactor one backend at a time
4. Easy rollback at any stage
5. Existing Common/ directory proves pattern works

**Circular dependency check**: ✓ None detected

```
Common.Star
  ← depends on: Data.Bool, Data.Maybe, PropEq (stdlib only)
  → depended by: RiscV64.Star (X86.Star, AArch64.Star in future)

RiscV64.Star
  ← depends on: RiscV64.Syntax, RiscV64.Semantics, Common.Star
  → depended by: RiscV64.StarBase, RiscV64.MutualIR
```

---

## Benefits

### Code Reduction

- **Immediate (RiscV64 only)**: ~117 lines
- **Full (all backends)**: ~226 lines net reduction
- **Percentage**: 18% reduction in Star-related code

### Maintenance Improvements

1. **Single source of truth** for Star semantics
2. **Automatic uniformity** across backends
3. **Easier to extend**: Adding star-step7, star-step8 benefits all backends
4. **Reduced cognitive load** when working across backends
5. **Bug fixes propagate** automatically to all backends

### Future Extensibility

- New backends can immediately use Common.Star
- Consistent API across all backends
- Easier to document and reason about

---

## Other Analyses

### CompileLength.agda

**Line counts**:
- X86: 216 lines
- AArch64: 247 lines
- RiscV64: 220 lines

**Common pattern**: All have `length-++` helper (already in stdlib)

**Verdict**: Not worth extracting (minimal duplication, proofs are backend-specific)

### ClosureWellFormed.agda

**Line counts**:
- X86: 204 lines
- AArch64: 235 lines
- RiscV64: 266 lines

**Structure similarities**:
- Same record types: ClosureWellFormed, CurryResult, ClosuresWF
- Same abstraction: code-ptr-valid, thunk-correct

**Key differences** (cannot abstract):
- **X86**: `rdi` (arg), `r12` (env), stack-based return, needs StackInvariant
- **AArch64**: `x0` (arg), `x19` (env), `x30` (return), different ABI
- **RiscV64**: `a0` (arg), `s0` (env), `ra` register (return), no StackInvariant

**Verdict**: Architecture-specific due to calling conventions

### Foundation.agda

**Line counts**:
- X86: 157 lines (mostly re-exports)
- AArch64: 1,227 lines (includes instruction lemmas)
- RiscV64: 1,029 lines (includes instruction lemmas)

**Current state**: Already well-organized
- X86's approach is cleanest (just consolidates imports)
- AArch64 and RiscV64 include instruction execution lemmas

**Verdict**: Already optimal - Foundation is the "one-stop shop" import

### MemoryValid.agda & StackInvariant.agda

**Present in**: X86, AArch64
**Absent in**: RiscV64

**Key insight**: RiscV64's simpler approach (star-only, no stack invariants) works fine

**Recommendation**: Consider if X86/AArch64 could simplify by adopting RiscV64's approach

---

## Execution Timeline

### Completed

- ✓ Phase 1: Documentation created
- ✓ Phase 2: Common/Star.agda created
- ✓ Phase 3: RiscV64 refactored and tested

### Future Work

- Phase 4: Refactor X86 backend
- Phase 5: Refactor AArch64 backend
- Phase 6: Consider additional extractions if pattern proves successful
- Phase 7: Explore simplifying X86/AArch64 to match RiscV64's cleaner approach

---

## Lessons Learned

### What Worked Well

1. **Plan agent analysis** provided comprehensive coverage
2. **Module parameterization** is the right abstraction level
3. **Phased approach** (RiscV64 first) validates pattern before broad application
4. **Strong typing** caught any integration issues immediately

### What to Watch For

1. **Import ordering**: Ensure Common.Star is imported before arch-specific definitions
2. **Public re-exports**: Use `public` to maintain API compatibility
3. **Dependent modules**: Check StarBase.agda, MutualIR.agda for import updates
4. **Compilation time**: Monitor for any performance regressions (unlikely)

### Recommendations for Future Extractions

1. **Start with one backend** to validate approach
2. **Document the full plan** even if not executing all phases
3. **Use module parameters** for type-level abstraction
4. **Keep architecture-specific code** separate (don't over-abstract)
5. **Test incrementally** after each phase

---

## References

- Existing Common code: `Once/Backend/Common/{Fetch,Memory,ProgramLemmas,Exec}.agda`
- Plan agent analysis: Initial research for this refactoring
- proof-instructions.md: Guidelines for proof discipline
- lessons-learned.md: Star is the native abstraction for execution proofs

---

## Appendix: Exact Extraction

### Common/Star.agda Structure

```agda
module Once.Backend.Common.Star
  (Program : Set)
  (State : Set)
  (halted : State → Bool)
  (step : Program → State → Maybe State)
  where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Star data type (~12 lines)
data Star (prog : Program) : State → State → Set where
  refl* : ∀ {s} → Star prog s s
  step* : ∀ {s s' s''} →
          halted s ≡ false →
          step prog s ≡ just s' →
          Star prog s' s'' →
          Star prog s s''

-- Core properties (~20 lines)
star-trans : ...
star-single : ...

-- Infix operators (~20 lines)
_◅◅_ : ...
⟨_,_⟩◅_ : ...

-- Helper combinators (~60 lines)
star-step2 : ...
star-step3 : ...
star-step4 : ...
star-step5 : ...
star-step6 : ...

-- Notation (~5 lines)
_⟶*_ : ...
```

### Backend Instantiation Pattern

```agda
module Once.Backend.RiscV64.Correct.Star where

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State

-- Import common Star infrastructure
open import Once.Backend.Common.Star Program State halted step public

-- Architecture-specific code follows
-- (bridge lemmas, helpers, etc.)
```

---

**Document Status**: Living document, updated as refactoring progresses
**Last Updated**: 2026-01-01
**Author**: Refactoring plan based on automated Plan agent analysis
