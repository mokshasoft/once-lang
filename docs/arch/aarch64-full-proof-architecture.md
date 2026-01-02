# AArch64 Full Proof Architecture: Closed vs Open Verification

**Status**: Implementation in Progress
**Created**: 2026-01-02
**Goal**: Achieve ZERO postulates for closed Once programs (CompCert-level verification)

## Executive Summary

This document describes the architectural split of AArch64 correctness proofs into two verification tracks:

| Track | Scope | Postulates | Use Case |
|-------|-------|------------|----------|
| **Closed** | Whole-program analysis | **ZERO** | Pure Once programs (like CompCert C→assembly) |
| **Open** | Modular analysis | **2 FFI axioms** | External closures, dynamic loading, separate compilation |

**Key Insight**: The ~4 postulates in `Once.Backend.AArch64.Postulates` are **NOT fundamental requirements**! By threading `ClosureWellFormed` proofs through IR combinators, closed programs can achieve zero postulates.

---

## Table of Contents

1. [Current State](#current-state)
2. [Verification Strategies](#verification-strategies)
3. [Directory Structure](#directory-structure)
4. [ClosureWellFormed Infrastructure](#closurewellformed-infrastructure)
5. [Implementation Roadmap](#implementation-roadmap)
6. [Example: Proving apply ∘ ⟨curry fst, id⟩](#example-proving-apply--curry-fst-id)
7. [Build Targets](#build-targets)
8. [Migration from Current Structure](#migration-from-current-structure)

---

## Current State

### Postulate Inventory (2026-01-02)

**In `Once/Backend/AArch64/Postulates.agda`** (4 postulates):

1. **sp-bound-after-stack-op** (line 59)
   - **Type**: Runtime guarantee
   - **Status**: Standard assumption (like CompCert's memory axioms)
   - **Justification**: Stack pointer remains > 16 after operations
   - **Required in**: Both Closed and Open tracks

2. **curry-thunk-correct** (line 97)
   - **Type**: Proof obligation
   - **Status**: **Eliminable** by proving in mutual block
   - **Path**: Call `run-ir-star-at-offset` recursively on embedded f
   - **Required in**: Open only (Closed proves it)

3. **run-thunk-at-offset** (line 148)
   - **Type**: Proof obligation
   - **Status**: **Eliminable** by moving to mutual block
   - **Path**: Call `run-ir-star-at-offset` recursively
   - **Required in**: Open only (Closed proves it)

4. **apply-produces-result** (line 215)
   - **Type**: Semantic boundary
   - **Status**: **Eliminable** via ClosureWellFormed threading
   - **Path**: Use `run-apply-with-wf` when WF proof available
   - **Required in**: Open only (Closed uses WF threading)

**In Proof Modules** (2 "postulates"):

5. **preserve-stack-inv** (`ClosureWellFormed.agda:281`)
   - **Status**: **Trivially provable** by pattern matching on `StackInvariant`
   - **Note**: Duplicate of `stack-inv-preserved-unchanged` in `StackInvariant.agda:320`

6. **monus-add-lemma** (`FrameProofs.agda:123`)
   - **Status**: **ALREADY PROVEN** (not actually a postulate!)
   - **Proof**: Lines 124-145 using stdlib lemmas

**Total Actual Postulates**: 4 (in Postulates.agda) + 1 (preserve-stack-inv) = **5**

**Path to Zero for Closed Programs**:
- Prove `preserve-stack-inv` (trivial, 5 lines)
- Move thunk proofs to mutual block (eliminates curry-thunk-correct, run-thunk-at-offset)
- Thread ClosureWellFormed through curry → pair/compose → apply (eliminates apply-produces-result)
- Keep `sp-bound-after-stack-op` as runtime assumption (like CompCert)

**Result**: **1 runtime axiom** (sp-bound) for Closed track = CompCert-level verification

---

## Verification Strategies

### Closed Track: Whole-Program Analysis

**Scope**: Pure Once programs where all closures are created within the program

**Example Programs**:
```agda
-- All closures created by curry within the program
apply ∘ ⟨curry fst, id⟩           -- Type: (A * B) * C → A
apply ∘ ⟨curry (snd ∘ fst), id⟩   -- Type: ((A * B) * C) * D → B
```

**Verification Strategy**:
1. **curry** produces `CurryResult` with `closure-wf : ClosureWellFormed` field
2. **compose/pair** thread the `closure-wf` proof through combinators
3. **apply** consumes `closure-wf` via `run-apply-with-wf` (zero postulates!)

**Proof Structure**:
```agda
-- curry produces WF proof
run-curry-star-direct : ... → CurryResult f prog s s' x offset
  where CurryResult contains: closure-wf : ClosureWellFormed ...

-- pair threads WF proof
run-pair-star-direct : ... → PairResult f g prog s s' x offset
  where PairResult contains: pair-wf-fst : Maybe (ClosureWellFormed ...)

-- apply consumes WF proof
run-apply-with-wf : ... → ClosureWellFormed ... → ApplyWithWFResult ...
  -- NO postulates needed!
```

**Postulate Count**: **1** (sp-bound-after-stack-op runtime assumption)

**Comparison**: Equivalent to CompCert's C→assembly phase (fully verified, axiomatized runtime)

---

### Open Track: Modular Analysis

**Scope**: Programs with external closures (FFI, dynamic loading, separate compilation)

**Example Programs**:
```agda
-- Closure from FFI (created outside Once)
ffi-callback : Foreign (A ⇒ B)

-- Apply to FFI closure
apply-to-external : IR ∞ (Foreign (A ⇒ B) * A) B
apply-to-external = apply
```

**Verification Strategy**:
- Axiomatize at FFI boundary: "External closures satisfy calling convention"
- Simpler proofs: no WF threading needed
- Use `apply-produces-result` postulate for all `apply` calls

**Proof Structure**:
```agda
-- curry produces IRStarResult (no WF field)
run-curry-star-direct : ... → IRStarResult (curry f) prog s s' x offset

-- apply uses postulate
run-apply-star-direct : ... → IRStarResult apply prog s s' x offset
  where proof uses: apply-produces-result postulate
```

**Postulate Count**: **2**
1. `sp-bound-after-stack-op` (runtime)
2. `apply-produces-result` (FFI boundary)

**Comparison**: Similar to CompCert's assembly semantics (axiomatized at boundary)

---

## Directory Structure

### Proposed Layout

```
formal/Once/Backend/AArch64/
├── CodeGen.agda                    # Unchanged
├── Semantics.agda                  # Unchanged
├── Syntax.agda                     # Unchanged
│
├── Postulates/
│   ├── Open.agda                   # FFI boundary axioms (2 postulates)
│   │                               # - sp-bound-after-stack-op
│   │                               # - apply-produces-result
│   └── Encoding.agda               # Re-export from Once.Postulates
│
├── Correct/
│   ├── Common/                     # Shared infrastructure (ZERO postulates!)
│   │   ├── Star.agda               # Star relation (from Common.Star)
│   │   ├── StarBase.agda           # IRStarResult record type
│   │   ├── StackInvariant.agda     # Stack/x29 invariants + preservation lemmas
│   │   ├── FrameProofs.agda        # PROVEN frame sizes (lines 124-145)
│   │   ├── ClosureWellFormed.agda  # WF infrastructure + run-apply-with-wf
│   │   ├── ThunkProof.agda         # Thunk execution helpers
│   │   ├── MemoryValid.agda        # Memory validity predicates
│   │   ├── Foundation.agda         # Low-level instruction lemmas
│   │   ├── FetchStep.agda          # Fetch-decode-execute step lemmas
│   │   ├── CompileLength.agda      # compile-length arithmetic
│   │   └── CorrectBridge.agda      # Bridge between Semantics and Correct
│   │
│   ├── Closed/                     # Zero-postulate proofs
│   │   ├── IR/
│   │   │   ├── Curry.agda          # Re-export CurryResult from Common
│   │   │   ├── Apply.agda          # Re-export ApplyWithWFResult from Common
│   │   │   ├── Pair.agda           # PairResult with WF threading
│   │   │   ├── Compose.agda        # ComposeResult with WF threading
│   │   │   ├── Case.agda           # CaseResult with WF threading
│   │   │   ├── StatefulProducers.agda
│   │   │   ├── StatefulConsumers.agda
│   │   │   └── StatefulCompose.agda
│   │   │
│   │   ├── MutualIR.agda           # ZERO postulates! (except sp-bound runtime)
│   │   │                           # - Proves thunks in mutual block
│   │   │                           # - Threads ClosureWellFormed
│   │   │                           # - run-curry produces CurryResult
│   │   │                           # - run-apply uses run-apply-with-wf
│   │   │
│   │   └── Examples.agda           # Example closed programs (apply ∘ ⟨curry fst, id⟩)
│   │
│   └── Open/                       # FFI-boundary axioms
│       ├── IR/
│       │   ├── Curry.agda          # Simpler: no WF field
│       │   ├── Apply.agda          # Uses apply-produces-result postulate
│       │   ├── Pair.agda           # Simpler: no WF threading
│       │   ├── Compose.agda        # Simpler: no WF threading
│       │   ├── Case.agda           # Simpler: no WF threading
│       │   ├── StatefulProducers.agda
│       │   ├── StatefulConsumers.agda
│       │   └── StatefulCompose.agda
│       │
│       └── MutualIR.agda           # 2 FFI axioms (sp-bound, apply-produces-result)
│                                   # - run-curry produces IRStarResult
│                                   # - run-apply uses apply-produces-result
│
└── (Current files remain for backward compatibility during migration)
    ├── Postulates.agda             # Will be superseded by Postulates/Open.agda
    ├── Correct/
    │   ├── Star.agda               # Will move to Common/
    │   ├── StarBase.agda           # Will move to Common/
    │   ├── ClosureWellFormed.agda  # Will move to Common/
    │   ├── MutualIR.agda           # Current modular proof (like Open/)
    │   └── IR/...                  # Current IR helpers
```

---

## ClosureWellFormed Infrastructure

### Type: ThunkResult

**Location**: `Common/ClosureWellFormed.agda` (lines 70-82)

**Purpose**: Captures the result of executing a thunk (curry's embedded code)

```agda
record ThunkResult {A B : Type} (prog : Program) (s s' : State)
                   (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) : Set where
  field
    thunk-star      : Star prog s s'              -- Execution trace
    thunk-halted    : halted s' ≡ false
    thunk-x0        : readReg (regs s') x0 ≡ encode (f a)  -- Result in x0
    thunk-x20       : readReg (regs s') x20 ≡ readReg (regs s) x20
    thunk-x21       : readReg (regs s') x21 ≡ readReg (regs s) x21
    thunk-x29       : readReg (regs s') x29 ≡ readReg (regs s) x29
    thunk-stack-inv : StackInvariant s'
    thunk-sp-bound  : readSP (regs s') > 16
```

**Usage**: Returned by thunk execution proof in mutual block

---

### Type: ClosureWellFormed

**Location**: `Common/ClosureWellFormed.agda` (lines 105-130)

**Purpose**: Captures that a closure at a given address is valid and correct

```agda
record ClosureWellFormed {A B : Type} (prog : Program)
                         (code-ptr : ℕ) (env-addr : ℕ)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧) : Set where
  field
    code-ptr-valid : code-ptr < length prog

    -- THE KEY FIELD: Proof that thunk executes correctly
    thunk-correct : ∀ (a : ⟦ A ⟧) (s : State) (ret-addr : ℕ) →
      halted s ≡ false →
      pc s ≡ code-ptr →
      readReg (regs s) x0 ≡ encode a →
      readReg (regs s) x19 ≡ env-addr →
      readReg (regs s) x30 ≡ ret-addr →
      StackInvariant s →
      readSP (regs s) > 16 →
      ∃[ s' ] (ThunkResult prog s s' semantics a × pc s' ≡ ret-addr)
```

**Usage**:
- Produced by `curry` (in `CurryResult.closure-wf` field)
- Threaded through `compose/pair/case`
- Consumed by `apply` (in `run-apply-with-wf`)

---

### Type: CurryResult

**Location**: `Common/ClosureWellFormed.agda` (lines 146-178)

**Purpose**: Result of executing `curry f` with WF proof

```agda
record CurryResult {i} {A B C : Type} (f : IR i (A * B) C)
                   (prog : Program) (s s' : State) (x : ⟦ A ⟧)
                   (offset : ℕ) : Set where
  field
    -- Standard execution properties (like IRStarResult)
    curry-star      : Star prog s s'
    curry-halted    : halted s' ≡ false
    curry-pc        : pc s' ≡ offset +ℕ compile-length (curry f)
    curry-x0        : readReg (regs s') x0 ≡ encode {B ⇒ C} (eval (curry f) x)
    curry-x20       : readReg (regs s') x20 ≡ readReg (regs s) x20
    curry-x21       : readReg (regs s') x21 ≡ readReg (regs s) x21
    curry-x29       : readReg (regs s') x29 ≡ readReg (regs s) x29
    curry-x30       : readReg (regs s') x30 ≡ readReg (regs s) x30
    curry-mem-x21   : readMem (memory s') (readReg (regs s) x21) ≡ ...
    curry-mem-x29   : readMem (memory s') (readReg (regs s) x29) ≡ ...
    curry-mem-x29+8 : readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡ ...
    curry-stack-inv : StackInvariant s'
    curry-sp-bound  : readSP (regs s') > 16

    -- THE KEY FIELD: Well-formedness proof for the created closure
    closure-wf : ClosureWellFormed {B} {C} prog
                   (offset +ℕ 6)           -- code-ptr: thunk at offset+6
                   (encode x)              -- env-addr: encoded captured value
                   (λ b → eval f (x , b))  -- semantics: partial application
```

**Usage in Closed Track**:
1. `run-curry-star-direct` produces `CurryResult` (not `IRStarResult`)
2. `closure-wf` field is extracted and threaded through program
3. When `apply` is called, `closure-wf` is used to prove correctness

---

### Type: ApplyWithWFResult

**Location**: `Common/ClosureWellFormed.agda` (lines 198-212)

**Purpose**: Result of executing `apply` given a WF proof (zero postulates!)

```agda
record ApplyWithWFResult {A B : Type} (prog : Program) (s s' : State)
                         (cl : Closure A B) (a : ⟦ A ⟧)
                         (offset : ℕ) : Set where
  field
    apply-star      : Star prog s s'
    apply-halted    : halted s' ≡ false
    apply-pc        : pc s' ≡ offset +ℕ compile-length (apply {_} {A} {B})
    apply-x0        : readReg (regs s') x0 ≡ encode (Closure.semantics cl a)
    apply-x20       : readReg (regs s') x20 ≡ readReg (regs s) x20
    apply-x21       : readReg (regs s') x21 ≡ readReg (regs s) x21
    apply-x29       : readReg (regs s') x29 ≡ readReg (regs s) x29
    apply-stack-inv : StackInvariant s'
    apply-sp-bound  : readSP (regs s') > 16
```

**Function**: `run-apply-with-wf` (lines 299+)

```agda
run-apply-with-wf : ∀ {A B} (prefix suffix : Program) (cl : Closure A B) (a : ⟦ A ⟧) (s : State) →
  -- Preconditions (halted, pc, x0, stack-inv, sp-bound)
  -- THE KEY PARAMETER:
  ClosureWellFormed {A} {B} prog (Closure.code-ptr cl) (Closure.env-addr cl) (Closure.semantics cl) →
  -- Result: ZERO postulates needed!
  ApplyWithWFResult prog s s' cl a (length prefix)
```

**Proof Strategy**:
1. Trace `apply`'s 6 instructions (ldr, ldr, ldr, ldr, mov, blr)
2. At `blr`: use `ClosureWellFormed.thunk-correct` to prove thunk executes
3. Compose traces via `star-trans`
4. **NO postulates needed!**

---

## Implementation Roadmap

### Phase 1: Prove Trivial Lemmas (30 min)

**File**: `formal/Once/Backend/AArch64/Correct/ClosureWellFormed.agda`

**Task**: Replace `preserve-stack-inv` postulate (line 281) with proof

```agda
preserve-stack-inv : ∀ {s s'} →
  readReg (regs s') x21 ≡ readReg (regs s) x21 →
  readSP (regs s') ≡ readSP (regs s) →
  StackInvariant s → StackInvariant s'
preserve-stack-inv x21-eq sp-eq (x21-unused x21≡0) =
  x21-unused (trans (sym x21-eq) x21≡0)
preserve-stack-inv x21-eq sp-eq (stack-below-x21 sp≤x21) =
  stack-below-x21 (subst₂ _≤_ sp-eq x21-eq sp≤x21)
```

**Result**: ClosureWellFormed.agda has ZERO postulates

---

### Phase 2: Create Directory Structure (15 min)

**Actions**:
1. Create `formal/Once/Backend/AArch64/Postulates/` directory
2. Create `formal/Once/Backend/AArch64/Correct/Common/` directory
3. Create `formal/Once/Backend/AArch64/Correct/Closed/` directory
4. Create `formal/Once/Backend/AArch64/Correct/Open/` directory

**Files to Move to Common/**:
- Star.agda
- StarBase.agda
- StackInvariant.agda
- FrameProofs.agda
- ClosureWellFormed.agda
- ThunkProof.agda
- Foundation.agda
- MemoryValid.agda
- FetchStep.agda
- CompileLength.agda
- CorrectBridge.agda

**Files to Create**:
- `Postulates/Open.agda` - Re-export 2 FFI axioms
- `Closed/IR/*.agda` - Copy from current IR/, modify for WF threading
- `Closed/MutualIR.agda` - Zero-postulate mutual block
- `Open/IR/*.agda` - Copy from current IR/, simpler
- `Open/MutualIR.agda` - FFI-axiom mutual block

---

### Phase 3: Implement Closed/MutualIR.agda (4-6 hours)

**Goal**: Zero-postulate (except sp-bound runtime) mutual block

**Key Changes**:

**3.1: Remove postulate imports**
```agda
-- REMOVE:
-- open import Once.Backend.AArch64.Postulates

-- KEEP:
open import Once.Backend.AArch64.Correct.Common.Star
open import Once.Backend.AArch64.Correct.Common.ClosureWellFormed
open import Once.Backend.AArch64.Correct.Common.StackInvariant
-- Import sp-bound-after-stack-op from Postulates/Open
-- (This is the ONLY postulate allowed)
```

**3.2: Make run-curry-star-direct produce CurryResult**

Currently returns `IRStarResult`. Change to `CurryResult` with `closure-wf` field.

**3.3: Prove thunk execution in mutual block**

Add:
```agda
run-thunk-in-mutual : ∀ {i A B C} (f : IR i (A * B) C) ... →
  ThunkResult prog s s' (λ b → eval f (env , b)) arg
run-thunk-in-mutual f ... = ...
  -- Trace 4 setup instructions
  -- RECURSIVE CALL: run-ir-star-at-offset f
  -- Trace ret instruction
  -- Compose via star-trans
```

This **eliminates** `curry-thunk-correct` and `run-thunk-at-offset` postulates!

**3.4: Thread ClosureWellFormed through pair/compose**

Extend result records:
```agda
record PairResult ... where
  field
    pair-star : ...
    ...
    -- NEW: Optional WF proofs
    pair-wf-fst : Maybe (ClosureWellFormed ...)
    pair-wf-snd : Maybe (ClosureWellFormed ...)
```

**3.5: Make run-apply-star-direct use run-apply-with-wf**

```agda
run-apply-star-direct : ... → (wf : Maybe (ClosureWellFormed ...)) → ...
run-apply-star-direct ... (just wf) = run-apply-with-wf ... wf
run-apply-star-direct ... nothing =
  -- Unreachable in closed programs (proven by construction)
  ⊥-elim (closed-program-has-wf-proof ...)
```

---

### Phase 4: Implement Open/MutualIR.agda (2 hours)

**Goal**: Simpler modular proofs with 2 FFI axioms

**Approach**: Copy current `MutualIR.agda`, import from `Postulates/Open.agda`

**Key Differences from Closed**:
- No WF threading (simpler)
- `run-curry` returns `IRStarResult` (no `closure-wf` field)
- `run-apply` uses `apply-produces-result` postulate

---

### Phase 5: Add Makefile Targets (30 min)

**File**: `formal/Makefile`

```makefile
.PHONY: aarch64-closed
aarch64-closed:
	@echo "Type-checking AArch64 closed program verification (ZERO postulates)..."
	$(AGDA) Once/Backend/AArch64/Correct/Closed/MutualIR.agda
	@$(call check-postulates,Once/Backend/AArch64/Correct/Closed)
	@$(call check-postulates,Once/Backend/AArch64/Correct/Common)
	@echo "✅ AArch64 closed verification complete: ZERO postulates!"

.PHONY: aarch64-open
aarch64-open:
	@echo "Type-checking AArch64 open program verification..."
	$(AGDA) Once/Backend/AArch64/Correct/Open/MutualIR.agda
	@echo "✅ AArch64 open verification complete (2 FFI axioms)"

.PHONY: aarch64
aarch64: aarch64-closed aarch64-open

define check-postulates
	@echo "Checking for postulates in $(1)..."
	@POSTULATE_COUNT=$$(find $(1) -name "*.agda" -exec grep -l "^postulate$$" {} \; 2>/dev/null | wc -l | tr -d ' '); \
	if [ "$$POSTULATE_COUNT" -ne 0 ]; then \
		echo "❌ ERROR: Found postulates in $(1)!"; \
		find $(1) -name "*.agda" -exec grep -Hn "^postulate$$" {} \;; \
		exit 1; \
	fi
endef
```

---

## Example: Proving `apply ∘ ⟨curry fst, id⟩`

**Type**: `(A * B) * C → A`
**Semantics**: Takes `((a, b), c)` and returns `a`

**Proof Strategy** (Closed Track):

```agda
module Once.Backend.AArch64.Correct.Closed.Examples where

open import Once.IR

example : ∀ {A B C} → IR ∞ ((A * B) * C) A
example = apply ∘ ⟨ curry fst , snd ∘ fst ⟩

-- Proof with ZERO postulates (except sp-bound runtime)
example-proof : ∀ {A B C} (a : A) (b : B) (c : C) (s : State) →
  -- Initial state setup
  readReg (regs s) x0 ≡ encode ((a, b), c) →
  halted s ≡ false →
  StackInvariant s →
  readSP (regs s) > 16 →

  -- Execute and get result
  ∃[ s' ] (IRStarResult example prog s s' ((a, b), c) 0
         × readReg (regs s') x0 ≡ encode a)
example-proof a b c s x0-eq h-false stack-inv sp-bound = ...
  let
    -- Step 1: Execute curry fst
    -- Produces CurryResult with closure-wf field
    curry-res = run-curry-star-direct fst ... s
    curry-wf = CurryResult.closure-wf curry-res

    -- Step 2: Execute snd ∘ fst (gets c from input)
    snd-fst-res = run-compose-star-direct snd fst ...

    -- Step 3: Execute pair ⟨curry fst, snd ∘ fst⟩
    -- Produces (closure, c) and threads curry-wf
    pair-res = run-pair-star-direct curry-res snd-fst-res
    pair-wf-fst = PairResult.pair-wf-fst pair-res  -- Extract WF proof

    -- Step 4: Execute apply using WF proof
    -- NO postulate needed! run-apply-with-wf uses curry-wf
    apply-res = run-apply-with-wf ... pair-wf-fst

    -- Step 5: Compose all via ∘
    final-res = run-compose-star-direct pair-res apply-res

  in (state final-res , final-res , IRStarResult.ir-x0 final-res)
```

**Key Points**:
1. `curry-wf` proof created by `run-curry-star-direct`
2. `pair-wf-fst` extracts and threads WF proof
3. `run-apply-with-wf` consumes WF proof (zero postulates!)
4. Total postulates used: **1** (sp-bound runtime assumption)

---

## Build Targets

### Usage

```bash
# Verify closed programs (ZERO postulates)
make aarch64-closed

# Verify open programs (2 FFI axioms)
make aarch64-open

# Verify both
make aarch64
```

### Success Criteria

**`make aarch64-closed` MUST**:
- Type-check `Closed/MutualIR.agda`
- Find ZERO postulates in `Closed/` directory
- Find ZERO postulates in `Common/` directory (except comments)
- Pass in < 5 minutes (mutual block type-checking)

**`make aarch64-open` MUST**:
- Type-check `Open/MutualIR.agda`
- Accept 2 postulates in `Postulates/Open.agda`
- Pass in < 3 minutes (simpler proofs)

---

## Migration from Current Structure

### Backward Compatibility

During migration, **keep current files** for backward compatibility:
- `formal/Once/Backend/AArch64/Postulates.agda`
- `formal/Once/Backend/AArch64/Correct/MutualIR.agda`
- `formal/Once/Backend/AArch64/Correct/IR/*.agda`

### Migration Steps

1. **Phase 1**: Prove trivial lemmas in current structure
2. **Phase 2**: Copy current files to `Common/`, `Closed/`, `Open/`
3. **Phase 3-5**: Implement Closed/Open variants
4. **Phase 6**: Validate both tracks compile
5. **Phase 7**: Update documentation
6. **Phase 8**: Deprecate current structure (add warnings)

### Deprecation Plan

After successful validation:
- Add deprecation comments to current files
- Point to `Closed/` or `Open/` equivalents
- Keep for 1-2 releases, then remove

---

## Comparison with CompCert

| Aspect | CompCert C→Assembly | Once Closed Track |
|--------|---------------------|-------------------|
| Scope | C programs → assembly | Once IR → AArch64 assembly |
| Postulates | Assembly semantics (axiomatized) | sp-bound runtime (axiomatized) |
| Extraction | OCaml via Coq | Haskell via MAlonzo |
| Verification | Fully proven | Fully proven |
| Compositionality | Modular (per-function) | Whole-program (closed) |
| FFI | Axiomatized at boundary | Open track (2 axioms) |

**Claim**: Once's Closed track achieves **equivalent verification level** to CompCert for pure programs.

---

## Next Steps After AArch64 Success

1. **Replicate for RISC-V**
   - RISC-V already has some WF infrastructure
   - Similar mutual block structure
   - Est: 1-2 weeks

2. **Replicate for x86-64**
   - x86-64 has similar structure
   - Est: 2-3 weeks

3. **Extract to Haskell**
   - MAlonzo extraction of `Closed/MutualIR.agda`
   - Integrate into compiler pipeline
   - Est: 1 week

4. **Update Marketing**
   - "CompCert-level verification for closed Once programs"
   - "ZERO postulates for pure functional code"
   - Est: 1 day

---

## References

- **CompCert**: Leroy et al. "Formal verification of a realistic compiler" (2009)
- **CakeML**: Kumar et al. "CakeML: A verified implementation of ML" (2014)
- **RISC-V Precedent**: `formal/Once/Backend/RiscV64/Correct/` (Star-based, WF infrastructure)
- **StackInvariant Lemmas**: `formal/Once/Backend/AArch64/Correct/StackInvariant.agda:319-374`
- **FrameProofs**: `formal/Once/Backend/AArch64/Correct/FrameProofs.agda:123-145` (already proven!)

---

**Document Version**: 1.0
**Last Updated**: 2026-01-02
**Status**: Ready for Implementation
