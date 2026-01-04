# Compilation Speed Optimization for MutualIR Modules

**Date**: 2026-01-03
**Status**: Proposals for implementation
**Problem**: MutualIR modules in backend verification take 15 minutes to over 1 hour to compile

## Context

The generator correctness proofs across all three backend architectures suffer from severe compilation performance issues:

- **RiscV64**: `Once/Backend/RiscV64/Correct/MutualIR.agda` (1,940 lines)
- **X86**: `Once/Backend/X86/Correct/MutualIR.agda` (2,150 lines)
- **AArch64**: `Once/Backend/AArch64/Correct/MutualIR.agda` (2,863 lines)

Each file contains a massive mutual block with 25+ mutually recursive functions and uses `{-# OPTIONS --sized-types #-}`.

### Root Causes Identified

1. **Sized types + mutual recursion**: Known to cause exponential constraint duplication in Agda's size solver (Agda issues [#2917](https://github.com/agda/agda/issues/2917), [#2639](https://github.com/agda/agda/issues/2639))
2. **Large mutual blocks**: 25+ functions type-checked as a single unit
3. **Massive inline proofs**: 600-800 line proof chains within mutual blocks
4. **Repeated definition unfolding**: Type checker unfolds all definitions during constraint solving

---

## Proposals (Ordered by Expected Impact)

### Proposal 1: Remove or Selectively Disable Sized Types 🔥

**Expected Speedup**: **10-100x** (from 15-60 min to under 5 min)
**Difficulty**: Low
**Risk**: Low (termination already proven by structural recursion)

#### The Problem

Sized types in combination with large mutual blocks cause superpolynomial constraint duplication. Each time the size solver fails to solve constraints, it duplicates them, leading to exponential blowup.

#### Solution Options

**Option A - Nuclear Approach** (Recommended for fastest results):
```agda
-- Remove or comment out:
-- {-# OPTIONS --sized-types #-}

-- Add to mutual block:
mutual
  {-# TERMINATING #-}
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) ...

  {-# TERMINATING #-}
  run-pair-star : ...

  -- etc for all 25 functions
```

**Option B - Surgical Approach** (Keep some type safety):
```agda
{-# OPTIONS --sized-types #-}

mutual
  -- Keep sized type for main function signature
  run-ir-star-at-offset : ∀ {i A B} (ir : IR i A B) ...

  -- But disable termination check for implementations
  {-# NO_TERMINATION_CHECK #-}
  run-ir-star-at-offset id ... = ...
  run-ir-star-at-offset (g ∘ f) ... = ...

  {-# NO_TERMINATION_CHECK #-}
  run-pair-star = ...
```

#### Why This Is Sound

- All functions terminate by structural recursion on `IR` constructors
- Size parameter `i` is purely for Agda's termination checker
- Manual inspection confirms termination (each recursive call is on a strict subterm)
- Sized types provide no runtime guarantees, only compile-time checking

#### Formal Termination Justification

**NEW**: Termination is now formally proven in a separate orthogonal module!

See `formal/Once/Backend/Termination.agda` and [`formal/docs/formal/guides/orthogonal-termination-proof.md`](../../formal/docs/formal/guides/orthogonal-termination-proof.md) for:
- Well-founded recursion proof on IR structure size
- Architecture-independent proof (shared by all backends)
- Abstract + concrete theorem (reusable for any IR processor)

This provides rigorous formal justification for the `{-# TERMINATING #-}` pragma while keeping the main correctness proofs clean and fast to compile.

#### Implementation Steps

1. Add `{-# TERMINATING #-}` pragma before mutual block
2. Add documentation comment explaining why termination is obvious
3. Test compilation time
4. If successful, remove `{-# OPTIONS --sized-types #-}` entirely

#### Trade-offs

- ✅ Massive compilation speedup (10-100x)
- ✅ No loss of correctness (termination is structurally obvious)
- ✅ Minimal code changes
- ❌ Lose automatic termination checking
- ❌ Need to manually verify termination for future changes
- ❌ Should document why TERMINATING is justified

---

### Proposal 2: Use `opaque` Definitions for Helper Functions 🚀

**Expected Speedup**: **2-5x** (can be combined with Proposal 1)
**Difficulty**: Low
**Risk**: Very Low

#### The Problem

During type checking, Agda repeatedly unfolds all function definitions in the mutual block. With 25 functions and complex proof terms, this creates massive constraint systems.

#### Solution

Mark helper functions as `opaque` to hide their implementations after definition:

```agda
mutual
  -- Main function: keep transparent for pattern matching
  run-ir-star-at-offset : ∀ {i A B} (ir : IR i A B) ...
  run-ir-star-at-offset id ... = ...
  run-ir-star-at-offset (g ∘ f) ... = ...
  run-ir-star-at-offset ⟨ f , g ⟩ ... = run-pair-star f g ...

  -- Helper functions: mark as opaque
  opaque
    run-pair-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B) ...
    run-pair-star {i} {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq sp-bound =
      -- Full implementation here, but hidden from type checker after this point
      s-final , record { ... }
      where
        -- 600 lines of proof...

  opaque
    run-case-star : ...
    run-case-star = ...

  opaque
    run-curry-star-with-wf : ...
    run-curry-star-with-wf = ...
```

#### How It Works

- `opaque` definitions are type-checked once when defined
- After definition, the implementation is hidden (replaced by abstract symbol)
- Type checker uses only the signature, not the implementation
- Can still use `opaque unfolding ... in ...` blocks when you need to unfold locally

#### Implementation Steps

1. Identify helper functions (not pattern-matched in `run-ir-star-at-offset`)
2. Wrap each in `opaque` block
3. Test that proofs still type-check
4. Measure compilation time improvement

#### Trade-offs

- ✅ Preserves all proofs and correctness
- ✅ Prevents repeated unfolding during constraint solving
- ✅ No loss of verification (unlike TERMINATING)
- ✅ Requires only Agda 2.6.3+ (we have 2.8.0)
- ❌ Slightly less convenient for interactive development
- ❌ Can't unfold opaque definitions in goal types (use `opaque unfolding` if needed)

---

### Proposal 3: Extract More Helpers with Opaque Arithmetic Lemmas 🔧

**Expected Speedup**: **1.5-3x** (can be combined with Proposals 1 & 2)
**Difficulty**: Medium
**Risk**: Low

#### The Problem

Looking at the MutualIR implementations, functions like `run-pair-star` contain 600-800 lines with massive inline arithmetic proofs:

```agda
run-pair-star f g ... =
  s-final , record { ... }
  where
    -- 50 lines of sp arithmetic
    sp-bound-for-f : StackDepth f ≤ readReg (regs s) sp
    sp-bound-for-f = ≤-trans (m≤m⊔n ...) ...

    sp-bound-for-g : StackDepth g ≤ ...
    sp-bound-for-g = cancel-+-left ...

    -- 40 lines of pc arithmetic
    pc-convert : offset +ℕ 12 +ℕ len-f +ℕ len-g ≡ ...
    pc-convert = begin
      offset +ℕ 12 +ℕ len-f +ℕ len-g
        ≡⟨ +-assoc ... ⟩
      ...

    -- 60 lines of memory preservation
    mem-preserved-final : ∀ n → readMem ... ≡ readMem ...
    mem-preserved-final n = begin
      ...
```

These inline proofs contribute to mutual block size and constraint complexity.

#### Solution

Extract proof chains into separate opaque modules:

```agda
-- Once/Backend/RiscV64/Correct/IR/PairArithmetic.agda
module PairArithmetic where
  open import Once.Backend.RiscV64.Correct.Foundation

  opaque
    derive-sp-bound-for-f : ∀ {f g sp} →
      StackDepth ⟨ f , g ⟩ ≤ sp →
      StackDepth f ≤ sp
    derive-sp-bound-for-f sp-bound =
      ≤-trans (m≤m⊔n ...) sp-bound

  opaque
    derive-sp-bound-for-g : ∀ {f g sp delta-f} →
      StackDepth ⟨ f , g ⟩ ≤ sp →
      delta-f ≤ StackDelta f →
      StackDepth g ≤ sp ∸ delta-f
    derive-sp-bound-for-g {f} {g} sp-bound delta-leq =
      cancel-+-left (StackDelta f) ...

  opaque
    pc-offset-arithmetic : ∀ offset len-f len-g →
      offset +ℕ 12 +ℕ len-f +ℕ len-g ≡
      offset +ℕ (12 +ℕ len-f +ℕ len-g)
    pc-offset-arithmetic offset len-f len-g = ...

  opaque
    memory-preservation-chain : ...

-- Once/Backend/RiscV64/Correct/MutualIR.agda
open import Once.Backend.RiscV64.Correct.IR.PairArithmetic

mutual
  run-pair-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound =
    s-final , record { ... }
    where
      -- Just call the opaque lemmas
      sp-bound-for-f = derive-sp-bound-for-f sp-bound
      sp-bound-for-g = derive-sp-bound-for-g sp-bound (ir-sp-delta-leq rf)
      pc-final = pc-offset-arithmetic offset len-f len-g
      mem-preserved-final = memory-preservation-chain ...
```

#### Benefits

- Smaller mutual block (less constraint solving)
- Better error localization (failures point to specific lemma)
- Reusable lemmas across similar proofs
- Opaque arithmetic prevents redundant constraint generation

#### Implementation Steps

1. Identify common proof patterns (sp arithmetic, pc conversion, memory chains)
2. Create `IR/PairArithmetic.agda`, `IR/CaseArithmetic.agda`, etc.
3. Extract lemmas and mark as `opaque`
4. Replace inline proofs with lemma calls
5. Test compilation (should be faster and cleaner)

#### Trade-offs

- ✅ Cleaner, more maintainable code
- ✅ Better error messages
- ✅ Faster compilation (less work in mutual block)
- ✅ Can be done incrementally
- ❌ More files to manage
- ❌ Need to design good lemma APIs

---

### Proposal 4: Upgrade to Agda 2.9.0 ⬆️

**Expected Speedup**: **1.2-1.5x** (cumulative improvements)
**Difficulty**: Low
**Risk**: Low-Medium (potential compatibility issues)

#### The Problem

Currently using Agda 2.8.0 (from nixpkgs). The latest Agda 2.9.0 (released December 2025) includes performance improvements.

#### Solution

Update `flake.nix` to use Agda 2.9.0:

```nix
# In flake.nix, agda shell:
agda = pkgs.mkShell {
  buildInputs = [
    # Pin to specific version if needed
    (pkgs.agda.overrideAttrs (old: {
      version = "2.9.0";
      # May need to specify source if not in nixpkgs yet
    }))
    pkgs.agdaPackages.standard-library
    pkgs.git
  ];
  # ...
};
```

Or wait for nixpkgs-unstable to include Agda 2.9.0 and update flake inputs.

#### Expected Improvements

- General type-checker optimizations
- Better constraint solver heuristics
- Improved caching mechanisms
- Bug fixes for edge cases

#### Implementation Steps

1. Update Agda version in `flake.nix`
2. Run `nix flake update` if needed
3. Test that all proofs still type-check
4. Check for deprecation warnings
5. Fix any compatibility issues

#### Trade-offs

- ✅ Free performance improvement
- ✅ Access to latest features and bug fixes
- ✅ Better tooling support
- ❌ May introduce new bugs (though 2.9.0 is stable)
- ❌ Requires Nix rebuild (time investment)
- ❌ Potential compatibility issues with proof code

---

### Proposal 5: Split MutualIR into Signature + Implementation Modules 📦

**Expected Speedup**: **2-3x** (better for incremental recompilation)
**Difficulty**: High
**Risk**: Medium

#### The Problem

Each MutualIR file is 1940-2863 lines. Even with extracted helpers, the core mutual block is huge and recompiles entirely on any change.

#### Solution

Create abstract interface module separate from implementation:

```agda
-- Once/Backend/RiscV64/Correct/MutualIR/Interface.agda
module Once.Backend.RiscV64.Correct.MutualIR.Interface where

open import Once.IR
open import Once.Backend.RiscV64.Correct.StarBase

-- Just signatures, no implementations
mutual
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B)
    (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ir ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  run-pair-star : ∀ {A B C} (f : IR C A) (g : IR C B)
    (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ⟨ f , g ⟩ ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)

  run-case-star : ...

  -- All other helper signatures


-- Once/Backend/RiscV64/Correct/MutualIR.agda
{-# OPTIONS --no-termination-check #-}
module Once.Backend.RiscV64.Correct.MutualIR where

import Once.Backend.RiscV64.Correct.MutualIR.Interface as I

-- Import all the extraction modules
open import Once.Backend.RiscV64.Correct.IR.Compose
open import Once.Backend.RiscV64.Correct.IR.Pair
-- etc

-- Implementations (Agda trusts they match interface)
mutual
  run-ir-star-at-offset : I.run-ir-star-at-offset
  run-ir-star-at-offset id prefix suffix x s h-false pc-eq a0-eq _ =
    run-id-star prefix suffix x s h-false pc-eq a0-eq
  -- Full implementation...

  run-pair-star : I.run-pair-star
  run-pair-star = ... -- Full implementation

  run-case-star : I.run-case-star
  run-case-star = ... -- Full implementation
```

#### Benefits

- Smaller mutual blocks (signature module is tiny)
- Better incremental compilation (changing implementation doesn't recheck interface)
- Clearer API (interface is documentation)
- Modular development (work on implementations separately)

#### Challenges

- Need to keep interface and implementation in sync
- More boilerplate
- `--no-termination-check` required (or prove termination externally)

#### Trade-offs

- ✅ Better code organization and documentation
- ✅ Faster incremental recompilation
- ✅ Clearer separation of concerns
- ❌ Significant refactoring effort
- ❌ More files to maintain
- ❌ Synchronization overhead (keep signatures updated)
- ❌ Requires `--no-termination-check` or external termination proof

---

## Recommended Implementation Strategy

### Phase 1: Quick Wins (Expected: 20-100x speedup)

1. **Apply Proposal 1A** (Remove sized types + add TERMINATING)
   - Minimal code changes
   - Document why termination is obvious
   - Test compilation time on RiscV64 first
   - If successful, apply to X86 and AArch64

2. **Apply Proposal 2** (Add opaque to helpers)
   - Mark all `run-*-star` helpers (except main `run-ir-star-at-offset`) as opaque
   - Should stack with Proposal 1

**Expected Result**: Compilation time drops from 15-60 minutes to **under 2 minutes**

### Phase 2: Code Quality (Expected: Additional 2-4x speedup)

3. **Apply Proposal 3** (Extract arithmetic lemmas)
   - Create `IR/*Arithmetic.agda` modules
   - Extract common proof patterns
   - Mark lemmas as opaque
   - Cleaner code + faster compilation

**Expected Result**: Compilation time drops to **under 1 minute**

### Phase 3: Infrastructure (Expected: Additional 1.2-1.5x speedup)

4. **Apply Proposal 4** (Upgrade Agda)
   - Update to 2.9.0 in `flake.nix`
   - Test and fix compatibility issues

**Final Expected Result**: Compilation time **30-60 seconds** per backend

### Optional: Long-term Refactoring

5. **Consider Proposal 5** (Module splitting) for future work
   - Better for very large codebases
   - Good for multi-developer teams
   - Can defer until other optimizations are done

---

## Measurement and Validation

Before and after each proposal, measure compilation time:

```bash
cd formal
/usr/bin/time -l nix develop '.#agda' --command \
  sh -c 'agda --library-file=<(find /nix/store -name "standard-library.agda-lib" | head -1; echo "Once.agda-lib") \
  Once/Backend/RiscV64/Correct/MutualIR.agda'
```

Track metrics:
- Real time (wall clock)
- User time (CPU time)
- Maximum resident memory
- Number of constraint solver iterations (if possible with `--profile=internal`)

---

## References

- Agda Issue #2917: [Very slow due to unsolved size?](https://github.com/agda/agda/issues/2917)
- Agda Issue #2639: [Performance regression, possibly related to the size solver](https://github.com/agda/agda/issues/2639)
- Agda Documentation: [Performance debugging](https://agda.readthedocs.io/en/latest/tools/performance.html)
- Agda Documentation: [Mutual Recursion](https://agda.readthedocs.io/en/latest/language/mutual-recursion.html)

---

## Questions and Discussion

This document captures proposals for discussion. Key questions to consider:

1. **Termination checking**: Are we comfortable using `TERMINATING` given that termination is structurally obvious?
2. **Opaque aggressiveness**: Should we mark even more definitions as opaque?
3. **Code organization**: Is the current extraction of Compose/Pair/Case helpers sufficient, or should we go further?
4. **Verification strength**: Are we trading too much verification for compilation speed?

Please add your thoughts and preferences to guide implementation priorities.
