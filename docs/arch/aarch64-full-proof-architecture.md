# AArch64 Code Generator Correctness Proof

**Status**: Implementation in Progress
**Created**: 2026-01-02
**Updated**: 2026-01-02 (Clarified scope: generator correctness, not program verification)
**Goal**: Prove AArch64 code generators correct for closed Once programs (CompCert-level verification)

## Executive Summary

This document describes proving the correctness of AArch64 code generation for pure Once IR terms.

**Fundamental Distinction**:
- **Code Generator Correctness**: Proving `∀ IR term f, compile(f) behaves like eval(f)` - This is what we're doing
- **Program Verification**: Verifying specific programs with FFI/Interpretations - Future work, separate concern

**Goal**: Prove the code generators correct with **ZERO postulates** (except runtime bounds like stack space).

| What We're Proving | Postulates | Scope |
|-------------------|------------|-------|
| **AArch64 Code Generators** | **1 runtime assumption** | Pure Once IR → AArch64 machine code |
| ~~Open/FFI Programs~~ | ~~Future~~ | ~~Interpretation interface specifications (separate)~~ |

**Key Insight**: The ~4 postulates in `Once.Backend.AArch64.Postulates` are **NOT fundamental requirements**! By threading `ClosureWellFormed` proofs through IR combinators, we can eliminate all proof obligations and prove generator correctness with only 1 runtime assumption (`sp-bound-after-stack-op`).

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

**Path to Zero Postulates** (Generator Correctness):
- ✅ Prove `preserve-stack-inv` (trivial, 5 lines) - **DONE Phase 1**
- Move thunk proofs to mutual block (eliminates curry-thunk-correct, run-thunk-at-offset)
- Thread ClosureWellFormed through curry → pair/compose → apply (eliminates apply-produces-result)
- Keep `sp-bound-after-stack-op` as runtime assumption (like CompCert's memory axioms)

**Result**: **1 runtime axiom** (sp-bound) = CompCert-level verification for code generators

---

## What We're Proving: Generator Correctness

**Goal**: For all pure Once IR terms, prove the generated AArch64 code is semantically correct.

```agda
∀ (IR term f : IR i A B) (input : ⟦ A ⟧),
  executing compile-aarch64(f) on encode(input)
  produces encode(eval f input)
```

**Scope**: Pure Once IR combinators
- id, compose (∘), fst, snd, pair ⟨_,_⟩
- inl, inr, case [_,_]
- terminal, initial
- curry, apply
- fold, unfold, arr

**Example Programs**:
```agda
-- All these are pure IR terms with proven code generation
apply ∘ ⟨curry fst, id⟩           -- Type: (A * B) * C → A
apply ∘ ⟨curry (snd ∘ fst), id⟩   -- Type: ((A * B) * C) * D → B
[ inl, inr ∘ snd ] ∘ fst          -- Type: (A + B) * C → (A + B)
```

**Not in Scope** (separate verification concern):
- Programs with FFI/Interpretations (need interface specifications)
- Specific program verification (composition of generator correctness + program properties)

---

## Proof Strategy: ClosureWellFormed Threading

**The Core Idea**: Thread well-formedness proofs through IR combinators

**Verification Strategy**:
1. **curry** produces `CurryResult` with `closure-wf : ClosureWellFormed` field
2. **compose/pair** thread the `closure-wf` proof through combinators
3. **apply** consumes `closure-wf` via `run-apply-with-wf` (zero proof obligations!)

**Proof Structure**:
```agda
-- curry produces WF proof
run-curry-star-direct : ... → CurryResult f prog s s' x offset
  where CurryResult contains: closure-wf : ClosureWellFormed ...

-- pair threads WF proof
run-pair-star-direct : ... → PairResult f g prog s s' x offset
  where PairResult contains: pair-wf-fst : Maybe (ClosureWellFormed ...)

-- apply consumes WF proof (NO POSTULATES!)
run-apply-with-wf : ... → ClosureWellFormed ... → ApplyWithWFResult ...
```

**Result**: All 3 proof obligations (curry-thunk-correct, run-thunk-at-offset, apply-produces-result) **eliminated**.

**Final Postulate Count**: **1** (sp-bound-after-stack-op runtime assumption)

**Comparison**: Equivalent to CompCert's C→assembly phase (fully verified modulo runtime axioms)

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

### Git Workflow

**IMPORTANT**: Each phase should have exactly ONE git commit.

**Commit Process**:
1. Run `git add <files>` as a separate command
2. Run `git commit -m "..."` as a separate command
3. Do NOT combine `git add` and `git commit` in a single command

**Commit Message Format**:
```
Phase N: <Brief description>

<Detailed explanation of changes>
- Bullet points for key changes
- Type-check status: ✅ Success

Part of Closed/Open verification split implementation.
```

**Example**:
```bash
git add formal/Once/Backend/AArch64/Correct/ClosureWellFormed.agda
git commit -m "Phase 1: Prove preserve-stack-inv lemma

Replace postulate with actual proof by pattern matching.
- Added _≤_ import to Data.Nat
- Case x21-unused: chain equalities via trans
- Case stack-below-x21: use subst₂

Type-check: ✅ Success"
```

---

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

### Phase 2: Eliminate Postulates in MutualIR.agda (1-2 weeks)

**Goal**: Prove all 3 proof obligations, leaving only 1 runtime assumption

**Current Postulates to Eliminate**:
1. curry-thunk-correct (line 97 of Postulates.agda)
2. run-thunk-at-offset (line 148 of Postulates.agda)
3. apply-produces-result (line 215 of Postulates.agda)

**Keep**: sp-bound-after-stack-op (runtime guarantee)

---

**Step 2.1: Make run-curry produce CurryResult (2-3 days)**

**File**: `formal/Once/Backend/AArch64/Correct/MutualIR.agda`

Currently `run-curry-star-direct` returns `IRStarResult`. Change to `CurryResult` with `closure-wf` field:

```agda
record CurryResult {i A B C} (f : IR i (A * B) C) prog s s' x offset : Set where
  field
    -- All IRStarResult fields
    ir-star : Star prog s s'
    ir-halted : halted s' ≡ false
    ir-pc : pc s' ≡ offset +ℕ compile-length (curry f)
    ir-x0 : readReg (regs s') x0 ≡ encode (eval (curry f) x)
    -- ... all register/memory preservation fields ...

    -- NEW: Well-formedness proof for created closure
    closure-wf : ClosureWellFormed prog (readReg (regs s') x0) x ...
```

---

**Step 2.2: Prove thunk execution in mutual block (3-4 days)**

Add `run-thunk-in-mutual` to the mutual block:

```agda
run-thunk-in-mutual : ∀ {i A B C} (f : IR i (A * B) C) ... →
  ThunkResult prog s s' (λ b → eval f (env , b)) arg
run-thunk-in-mutual f prefix suffix env arg s ... = ...
  -- 1. Trace 4 setup instructions (sub-sp, stp, mov-from-sp)
  -- 2. RECURSIVE CALL: run-ir-star-at-offset f
  --    (available because we're in the mutual block!)
  -- 3. Trace ret instruction
  -- 4. Compose via star-trans
```

This **eliminates** `curry-thunk-correct` and `run-thunk-at-offset` postulates!

---

**Step 2.3: Thread ClosureWellFormed through pair/compose (2-3 days)**

Extend result records to carry WF proofs:

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

---

**Step 2.4: Use run-apply-with-wf (1-2 days)**

Modify `run-ir-star-at-offset` for `apply`:

```agda
run-ir-star-at-offset apply prefix suffix x s ... with extract-wf-from-context
  -- If closure has WF proof (from threading), use it!
  ... | just closure-wf → run-apply-with-wf ... closure-wf  -- NO postulate!
  -- Otherwise: would need apply-produces-result, but shouldn't happen in pure IR
  ... | nothing → ⊥-elim (no-unproven-closures-in-pure-ir ...)
```

This **eliminates** `apply-produces-result` postulate for pure IR terms!

**Result**: Only 1 postulate remains (`sp-bound-after-stack-op` runtime assumption)

---

### Phase 3: Write Example Proofs (1-2 days)

**Goal**: Demonstrate generator correctness with concrete examples

**File**: `formal/Once/Backend/AArch64/Correct/Examples.agda`

Example programs to verify:
```agda
-- Example 1: apply ∘ ⟨curry fst, id⟩
-- Example 2: [ inl, inr ∘ snd ] ∘ fst
-- Example 3: apply ∘ ⟨curry (snd ∘ fst), snd⟩
```

Each example proves: `∀ input, compile(prog) on input produces eval(prog input)`

---

### Phase 4: Validation (1-2 hours)

**Actions**:
1. Type-check full backend: `make aarch64`
2. Count postulates: Should find only `sp-bound-after-stack-op`
3. Update documentation with final postulate count

**Success Criteria**:
- ✅ All files type-check
- ✅ Only 1 postulate in entire AArch64 backend (sp-bound)
- ✅ Examples compile and verify

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
