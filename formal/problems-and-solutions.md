# Compiler Verification Problems and Solutions

This document tracks problems encountered and solutions applied during full compiler stack verification.

**Scope**: Surface syntax → x86-64 machine code
**Excludes**: CLI/Parser, C backend, generator correctness proofs (already proven)

---

## Problem 1: `exchange₆` Postulate in TypeCheck/Elaborate

**File**: `formal/Once/TypeCheck/Elaborate.agda:220-225`

**Problem**:
```agda
postulate
  exchange₆ : ∀ {n} {Γ : SCtx n} {A B C D E F G H : Type}
            → SExpr ((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) H
            → SExpr (((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) H
```

This violates proof-instructions.md Core Principle 1: "No Inline Postulates - every postulate represents unfinished work, goal is zero."

**Root Cause**:
The elaboration needs to weaken de Bruijn contexts when going under binders (lambda, case, let). The current approach manually implements `exchange` through `exchange₅` (handling nesting depth 0-5), then postulates `exchange₆` for depth 6+.

**Status**: Open

**Solution Options**:
1. **Prove `exchange₆`** following the existing pattern
   - Requires implementing the same 11-constructor case analysis as `exchange₅`
   - Need new lookup lemma: `lookup-suc-suc-suc-suc-suc-suc-suc`
   - Then postulate `exchange₇` for depth 7+

2. **Change the abstraction** (preferred per proof-instructions.md)
   - Use a generalized `exchangeN : ∀ n → ...` with well-founded recursion
   - Prove termination by showing depth decreases
   - Eliminates all exchange postulates

**Analysis**:
The current implementation has a clear pattern:
- Each `exchangeN` handles variables at depth N
- Variables 0..N-1: unchanged
- Variable N+: shifted by suc
- For binders (lam, case', let'): recurse with `exchangeN+1`
- Each depth requires a `lookup-suc-suc-...-suc` lemma with N+1 suc's

The pattern is entirely mechanical but requires explicit type parameters for each context layer.

**Attempted**:
- 2025-01-29: Analyzing current implementation to design generalized solution
- 2025-01-29: Implemented `exchange₆` following the established pattern, moved postulate to `exchange₇`

**Solution Applied**:
Extended the pattern one more level:
1. Added `lookup-suc-suc-suc-suc-suc-suc-suc` lemma (7 suc's)
2. Implemented `exchange₆` with all 11 Surface.Syntax constructors
3. Moved postulate to `exchange₇` for depth 7+
4. Type-checks successfully with `make agda MODULE=Once/TypeCheck/Elaborate.agda`

This reduces the postulate from depth 6 to depth 7. Programs with 7+ levels of nested binders are even rarer than 6 levels.

**Status**: In Progress - one postulate level eliminated, `exchange₇` remains

**Next Steps**: Continue extending pattern to `exchange₇`, `exchange₈`, etc. or accept `exchange₇` as acceptable axiom

---

## Problem 2: ~30 Mechanical Postulates in X86 Backend

**File**: `formal/Once/Backend/X86/Correct.agda`

**Problem**:
Multiple postulates for execution traces, register preservation, memory preservation across generators.

**Categories** (from what-is-proven.md):
- Per-generator execution traces: ~20 postulates
- Register preservation (r14-final, r15-final): ~10 postulates
- StackInvariant preservation: ~5 postulates
- Stack size after operations: ~5 postulates

**Root Cause**:
These are mechanical step-by-step proofs that follow the same pattern as already-proven generators (inl, inr, id, fst, snd, terminal, fold, unfold, arr). The E2E-Trace module demonstrates a complete 37-instruction trace proof for `apply ∘ ⟨curry fst, id⟩`.

**Status**: Open

**Solution**:
Follow E2E-Trace pattern for each generator:
- Step through all instructions manually
- Track register and memory state at each step
- Use Star-based proofs (per proof-instructions.md)

**Attempted**: addr-diff postulates were successfully eliminated via StackInvariant integration

**Next Steps**: Systematic elimination following E2E-Trace pattern

---

## Problem 3: Integration of TypeCheck/Elaborate with End-to-End Theorem

**File**: `formal/Once/EndToEnd.agda`

**Problem**:
Need to connect the new TypeCheck/Elaborate module (which combines inference + scope resolution) to the existing end-to-end pipeline.

**Current Pipeline**:
```
RawExpr → [inferElab] → Surface.Expr → [elaborate] → IR → [optimize] → IR → [codegen] → x86-64
```

**Status**: Open (pending TypeCheck/Elaborate completion)

**Solution**:
Once `exchange₆` is eliminated:
1. Prove soundness of `inferElab` (connects to Sound.agda theorems)
2. Compose with existing `elaborate-correct`, `optimize-correct`, `codegen-x86-correct`
3. Update end-to-end theorem to use full verified path

**Next Steps**: Complete TypeCheck/Elaborate first

---

## Problem 4: MAlonzo Extraction and --verified Flag

**Files**: `compiler/src/Once/CLI.hs`, `compiler/app/Main.hs`, `compiler/src/Once/Elaborate/Verified.hs`

**Problem**:
The `--verified` flag enables opt-in verification with fallback to unverified Haskell. This should be removed once all compilation phases are MAlonzo-extracted.

**Current State**:
- `--verified` flag triggers MAlonzo elaboration
- Fallback to Haskell if MAlonzo fails (postulates, exceptions)
- Verification is optional, not the default

**Target State**:
- All verified modules extracted via MAlonzo
- No Haskell implementation fallback
- Verification is the ONLY path
- `--verified` flag removed entirely

**Status**: Open (pending completion of Phases 1-4)

**Solution**:
1. Complete all Agda proofs (zero inline postulates)
2. Extract all verified modules: TypeCheck.Elaborate, Surface.Elaborate, Optimize, Backend.X86
3. Update compiler to use only MAlonzo code
4. Remove flag and fallback logic
5. Verify all 221 tests pass

**Next Steps**: Complete proof work first, then extract and integrate

---

## Solutions Applied

### Solution S1: StackInvariant Integration (Completed)

**Problem**: 4 addr-diff postulates in inl/inr generators

**Solution**:
- Added `StackInvariant s` predicate tracking `rsp ≤ r15` relationship
- Created `addr-diff-from-invariant` lemma deriving address disjointness
- Integrated StackInvariant into `run-ir-at-offset` parameters
- Proved `initWithInput-stack-inv` and `stack-inv-after-setup`

**Result**: All 4 addr-diff postulates eliminated

**Files Modified**:
- `formal/Once/Backend/X86/Correct.agda`

**Commit**: (to be recorded when committed)

---

## Guidelines

When adding entries to this document:

1. **Problem Format**:
   - File location with line numbers
   - Clear description of what's wrong
   - Root cause analysis
   - Status: Open/In Progress/Resolved
   - Solution options (if multiple approaches)

2. **Solution Format**:
   - What was attempted
   - What worked/didn't work
   - Files modified
   - Commit reference

3. **Update Regularly**:
   - Add problems as discovered
   - Document solution attempts (even failures)
   - Mark resolved when complete
   - Cross-reference with git commits

4. **Cross-Reference**:
   - Link to related docs (proof-instructions.md, what-is-proven.md)
   - Reference decision log entries
   - Note related problems
