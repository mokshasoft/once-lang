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

## Stack Analysis Extraction

### Background: The False Postulate Problem

**Date**: 2026-01-01

All three backends had a similar postulate claiming universal stack bounds:

```agda
-- RiscV64 (Foundation.agda):
postulate
  stackDepth-leq-stackBase : ∀ ir → StackDepth ir ≤ 0x7FFF0000

-- Similar postulates in X86 and AArch64
```

**Problem**: This postulate is **mathematically FALSE**. Any fixed bound can be exceeded by sufficiently deep nesting (compose chains, nested pairs, etc.). The bound `0x7FFF0000` (2GB) came from an arbitrary choice of initial stack pointer.

**Insight**: If different backends require different postulates, the postulate abstraction is wrong. The correct abstraction should be: *given sufficient stack for a specific program, execution succeeds*.

### The New Approach: Parameterized Stack Correctness

**Key Realization**: `StackDepth` is a **computable total function**. For any specific IR term, we can compute its exact stack requirements.

**Solution**:
1. Remove false universal postulate
2. Parameterize `initWithInput` by stack size
3. Make correctness theorems require explicit precondition
4. Extract stack analysis logic to Common module

### Phase 1: Common Stack Analysis Infrastructure ✓

**File**: `Once/Backend/Common/StackAnalysis.agda` (~138 lines)

**Approach**: Module parameterization by backend-specific allocation sizes

```agda
module Once.Backend.Common.StackAnalysis
  (pair-frame : ℕ)    -- Bytes allocated for pair ⟨ f , g ⟩
  (inl-frame : ℕ)     -- Bytes allocated for left injection
  (inr-frame : ℕ)     -- Bytes allocated for right injection
  (curry-frame : ℕ)   -- Bytes allocated for curry closure
  (apply-frame : ℕ)   -- Conservative bound for apply thunk
  where
```

**Content**:
- **StackDelta**: Net stack allocation after IR completes
- **StackDepth**: Maximum stack depth during execution

**Key Properties**:
- Both are total functions (computable for any IR)
- No universal bounds needed
- Backend-agnostic logic, architecture-specific sizes

**RiscV64 allocation sizes**:
```agda
open import Once.Backend.Common.StackAnalysis
  32   -- pair-frame (16 data + 8 s1 + 8 s2 frame pointer)
  16   -- inl-frame
  16   -- inr-frame
  16   -- curry-frame
  24   -- apply-frame (conservative bound)
  public
```

### Phase 2: Refactor RiscV64 Stack Analysis ✓

**Files Modified**:

1. **Once/Backend/RiscV64/CodeGen.agda**
   - Removed ~55 lines (StackDelta/StackDepth definitions)
   - Added import of Common.StackAnalysis with RiscV64 sizes
   - **Reduction**: ~55 lines

2. **Once/Backend/RiscV64/Correct/Foundation.agda**
   - Removed `stackDepth-leq-stackBase` postulate
   - Parameterized `initWithInput` by stack size:
     ```agda
     -- OLD:
     initWithInput : ∀ {A} → ⟦ A ⟧ → State

     -- NEW:
     initWithInput : (stackSize : ℕ) → ∀ {A} → ⟦ A ⟧ → State
     ```
   - Updated all helper lemmas to take `stackSize` parameter
   - Made `initWithInput-sp-sufficient` trivial (no postulate needed)

3. **Once/Backend/RiscV64/Correct.agda**
   - Updated main correctness theorem:
     ```agda
     star-codegen-correct : ∀ ir (stackSize : ℕ) x →
       StackDepth ir ≤ stackSize →  -- Explicit precondition
       ∃[ s ] (Star (compile-riscv ir) (initWithInput stackSize x) s
             × halted s ≡ true
             × readReg (regs s) a0 ≡ encode (eval ir x))
     ```
   - Removed old test theorems that would require false universal postulate
   - Kept `star-id-correct` as example with new stack-parameterized signature

4. **Once/Backend/RiscV64/Postulates.agda**
   - Updated documentation noting the removed postulate
   - Explained new approach with explicit stack parameterization

**Total reduction**: ~55 lines (StackDelta/StackDepth duplicated code)

**Status**: ✓ Completed (RiscV64)

### Benefits of the New Approach

**Correctness**:
- ✓ No false universal claims
- ✓ Provable for specific programs
- ✓ Makes stack requirements explicit and computable

**Practical Use**:
```agda
-- For a specific program, compute required stack:
let required = StackDepth myProgram  -- Computes to finite ℕ
    provided = required + 1024       -- Add safety margin
    proof : StackDepth myProgram ≤ provided
    proof = auto-prove ...
in star-codegen-correct myProgram provided x proof
```

**Runtime Model**:
1. Compiler computes `StackDepth ir` for each program
2. Compiler emits required stack size in binary metadata
3. Runtime provides sufficient stack or rejects program
4. Correctness theorem: "given ≥ N bytes, execution succeeds"

**Code Sharing**:
- ~55 lines eliminated per backend (RiscV64 done)
- X86 and AArch64 have similar StackDelta/StackDepth (pending extraction)
- Single source of truth for stack analysis logic

### Future Work: X86 and AArch64

**Expected reductions**:
- X86: ~50 lines (StackDelta/StackDepth in CodeGen.agda)
- AArch64: ~50 lines (StackDelta/StackDepth in CodeGen.agda)

**Dependencies to update**:
- X86/Correct/Foundation.agda (remove postulate, parameterize initWithInput)
- AArch64/Correct/Foundation.agda (remove postulate, parameterize initWithInput)
- X86/Correct.agda (update theorem signatures)
- AArch64/Correct.agda (update theorem signatures)
- X86/Postulates.agda (update documentation)
- AArch64/Postulates.agda (update documentation)

**Different allocation sizes** (to be verified):
- X86 uses different calling conventions (stack-based vs register-based)
- AArch64 uses different frame sizes (AArch64 ABI)

**Status**: Documented, not yet executed

---

## Frame Size Verification (Future Work)

### Background: The Hardcoded Constants Problem

**Date**: 2026-01-01

**Discovery**: While eliminating the `sp-bound-for-f-in-thunk` postulate, we discovered that `curry-frame = 16` was **incorrect** - the curry thunk actually allocates 24 bytes!

This revealed a broader issue: **all frame sizes are currently hardcoded parameters** with no verification:

```agda
open import Once.Backend.Common.StackAnalysis
  32   -- pair-frame (hardcoded!)
  16   -- inl-frame (hardcoded!)
  16   -- inr-frame (hardcoded!)
  16   -- curry-frame (WRONG! Should be 24)
  24   -- apply-frame (hardcoded!)
```

**Root Cause**: These are parameters to make StackAnalysis reusable across backends, but there's no proof they match the actual code generation.

**Risk**: If we got curry-frame wrong (16 vs 24), what else might be wrong?

### The Solution: Prove Frame Sizes from Code Generation

Instead of hardcoding, **calculate frame sizes from the actual instruction sequences**:

#### Example: curry-frame

**Current (wrong):**
```agda
16  -- curry-frame (arbitrary parameter)
```

**New (proven):**
```agda
-- Prove from actual instructions
curry-setup-allocates-16 : curry setup allocates 16-byte closure
curry-thunk-allocates-24 : curry thunk allocates 24-byte frame

curry-frame-value : ℕ
curry-frame-value = 24  -- Maximum (accounts for thunk)

curry-frame-correct :
  curry-setup-allocates-16 →
  curry-thunk-allocates-24 →
  curry-frame-value ≡ 24
```

### Implementation Plan (Future Work)

**Priority Order** (based on risk of being wrong):

1. **curry-frame** ✓ IN PROGRESS (fixing sp-bound-for-f-in-thunk postulate)
   - Prove setup allocates 16
   - Prove thunk allocates 24
   - Use proven value 24

2. **pair-frame** (High Priority)
   - Currently: 32 bytes
   - Should prove: 16 (pair data) + 8 (s1) + 8 (s2)
   - Verify from pair code generator

3. **inl-frame / inr-frame** (Medium Priority)
   - Currently: 16 bytes each
   - Should prove: tag + value layout
   - Verify from injection code generators

4. **apply-frame** (Low Priority)
   - Currently: 24 bytes
   - Actually used for thunk frame (same as curry-frame)
   - May be redundant with curry-frame

### Benefits

1. **Correctness**: Catch errors like curry-frame = 16 (should be 24)
2. **Documentation**: Code generation and stack analysis stay in sync
3. **Maintainability**: If code gen changes, proofs break (not silent bugs)
4. **Trust**: No "magic numbers" - all values proven from first principles

### Approach for Each Frame Size

For each frame size:
1. Locate code generator (in CodeGen.agda or IR/*.agda)
2. Identify allocation instructions (e.g., `addi sp sp -N`)
3. Write lemma proving allocation size
4. Replace parameter with proven value
5. Add verification that parameter matches proven value

### Status

- **curry-frame**: ✓ COMPLETED (2026-01-02) - Proven from ThunkSetup.agda instructions
- **others**: DOCUMENTED, awaiting implementation

---

## Postulate Elimination: sp-bound-for-f-in-thunk (2026-01-02)

### The Problem

**Postulate R2** in `Once/Backend/RiscV64/Postulates.agda` claimed:
```agda
postulate
  sp-bound-for-f-in-thunk : ∀ {i A B C} (f : IR i (A * B) C) (s : State) →
    StackDepth f ≤ readReg (regs s) sp
```

This was a **FALSE universal claim** - it claimed ANY IR `f` fits in ANY stack pointer `sp`.

### Root Cause

This postulate existed because:
1. curry-thunk-correct-impl needed to prove `StackDepth f ≤ sp-after-thunk-setup`
2. Thunk setup allocates 24 bytes, so `sp-after-thunk-setup = orig-sp - 24`
3. Without arithmetic, couldn't derive `StackDepth f ≤ orig-sp - 24` from preconditions
4. **Mistake**: curry-frame was hardcoded as 16 (should be 24!)

### The Solution

**Three-part fix:**

1. **Prove curry-frame = 24** (Once/Backend/RiscV64/Correct/CurryFrameProof.agda)
   - Extract allocation size from `addi sp sp -24` instruction in ThunkSetup.agda
   - Define `curry-frame-value : ℕ` with proven value 24
   - Use in CodeGen.agda instead of hardcoded parameter

2. **Add stack precondition to curry-thunk-correct-impl**
   - Require: `StackDepth (curry f) ≤ readReg (regs s) sp`
   - Expand: `curry-frame-value + StackDepth f ≤ orig-sp` (StackAnalysis definition)
   - Derive: `StackDepth f ≤ orig-sp - 24` using arithmetic helper `+-≤-to-∸`
   - Conclude: `StackDepth f ≤ sp-after-setup` (since `sp-after-setup = orig-sp - 24`)

3. **Thread precondition through proof chain**
   - Update ClosureWellFormed with stack-requirement parameter
   - Update CurryResult to specify `StackDepth (curry f)` as requirement
   - Update run-curry-star and run-curry-star-with-wf signatures
   - Pass stack bound through curry-thunk-correct-impl call

### Arithmetic Proof (MutualIR.agda lines 1621-1650)

```agda
-- Given: StackDepth (curry f) ≤ orig-sp
-- Expand: curry-frame-value + StackDepth f ≤ orig-sp
-- Given: curry-frame-value = 24
-- Therefore: 24 + StackDepth f ≤ orig-sp
-- Derive: StackDepth f ≤ orig-sp - 24 (using +-≤-to-∸)
-- Given: sp-after-setup = orig-sp - 24
-- Therefore: StackDepth f ≤ sp-after-setup ✓
```

### Files Modified

1. `Once/Backend/RiscV64/Correct/CurryFrameProof.agda` (NEW)
   - Defines curry-frame-value = 24
   - Documents derivation from ThunkSetup instructions

2. `Once/Backend/RiscV64/CodeGen.agda`
   - Import curry-frame-value from CurryFrameProof
   - Replace `16 -- curry-frame` with `curry-frame-value -- curry-frame (PROVEN!)`

3. `Once/Backend/RiscV64/Correct/MutualIR.agda`
   - Add curry-frame-value import
   - Add `+-≤-to-∸` arithmetic helper lemma
   - Add stack precondition to curry-thunk-correct-impl signature
   - Replace postulate usage with arithmetic proof (lines 1621-1650)
   - Update run-curry-star-with-wf to use `StackDepth (curry f)` instead of `16`

4. `Once/Backend/RiscV64/Correct/ClosureWellFormed.agda`
   - Add stack-requirement parameter to ClosureWellFormed record
   - Add stack precondition to thunk-correct field
   - Update CurryResult.closure-wf to pass `StackDepth (curry f)`

5. `Once/Backend/RiscV64/Correct/IR/Curry.agda`
   - Update run-curry-star to use `StackDepth (curry f)` instead of hardcoded `16`

6. `Once/Backend/RiscV64/Postulates.agda`
   - Remove sp-bound-for-f-in-thunk postulate
   - Document elimination with references to solution

### Impact

- **Postulates**: RiscV64 reduced from 4 to 3
- **Correctness**: Replaced false universal claim with explicit threading
- **Maintainability**: curry-frame now proven from code generation
- **Pattern**: Follows same approach as stack space postulate elimination

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
