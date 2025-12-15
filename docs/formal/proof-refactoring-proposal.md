# Proof Refactoring Proposal: Consolidating Backend Lemmas

## Executive Summary

This document proposes a refactoring of the formal proof file structure to:
1. Eliminate ~215 lines of duplicated lemmas across backends
2. Create shared infrastructure for common proof patterns
3. Group generators by proof complexity for easier maintenance
4. Parameterize architecture-specific patterns where possible

**Current State:**
- 12,138 total lines in Correct.agda files (AArch64: 2,454 | RiscV64: 2,072 | x86-64: 7,612)
- ~20 exact duplicate lemma pairs across backends
- No Backend/Common/ directory - all sharing is at formal/Once/ level

**Proposed Result:**
- New Backend/Common/ directory with ~300 lines of shared lemmas
- ~15-20% reduction in per-backend Correct.agda size
- Clearer separation of concerns

---

## Current Directory Structure

```
formal/Once/
├── Type.agda              # Core type system
├── IR.agda                # IR generators (shared)
├── Semantics.agda         # Denotational semantics
├── Postulates.agda        # Encoding axioms (shared)
├── Compile.agda           # Compilation entry point
├── Optimize.agda          # IR optimization
├── EndToEnd.agda          # End-to-end correctness
├── Category/
│   └── Laws.agda          # Categorical laws
├── Surface/               # High-level syntax
├── Primitive/             # Effect primitives
├── TypeSystem/            # Typing rules
└── Backend/
    ├── AArch64/
    │   ├── Syntax.agda
    │   ├── Semantics.agda
    │   ├── CodeGen.agda
    │   └── Correct.agda   # 2,454 lines, 12 postulates
    ├── RiscV64/
    │   ├── Syntax.agda
    │   ├── Semantics.agda
    │   ├── CodeGen.agda
    │   └── Correct.agda   # 2,072 lines, 3 postulates
    └── X86/
        ├── Syntax.agda
        ├── Semantics.agda
        ├── CodeGen.agda
        └── Correct.agda   # 7,612 lines, 15 postulates
```

---

## Proposed Directory Structure

```
formal/Once/
├── ... (existing shared modules unchanged)
└── Backend/
    ├── Common/                         # NEW: Shared backend lemmas
    │   ├── Fetch.agda                  # List indexing lemmas
    │   ├── Exec.agda                   # N-step execution lemmas
    │   ├── Memory.agda                 # Memory read/write lemmas
    │   └── StateHelpers.agda           # Generic state manipulation
    ├── AArch64/
    │   ├── ... (existing)
    │   └── Correct/                    # Split Correct.agda into parts
    │       ├── Main.agda               # Re-exports all
    │       ├── Trivial.agda            # id, fold, unfold, arr, terminal, initial
    │       ├── Projection.agda         # fst, snd
    │       ├── Injection.agda          # inl, inr
    │       ├── Compound.agda           # compose, pair, case
    │       └── Exponential.agda        # curry, apply
    ├── RiscV64/
    │   └── ... (similar split)
    └── X86/
        └── ... (similar split)
```

---

## Table 1: Duplicated Lemmas to Consolidate

### High Priority: Exact Duplicates (Move to Common/)

| Lemma | AArch64 | RiscV64 | X86 | Lines | Target Module |
|-------|---------|---------|-----|-------|---------------|
| `fetch-0` | 330 | 391 | 454 | 2 | Common/Fetch.agda |
| `fetch-1` | - | 395 | 458 | 2 | Common/Fetch.agda |
| `fetch-2` | - | 399 | 462 | 2 | Common/Fetch.agda |
| `fetch-3` | - | 403 | 466 | 2 | Common/Fetch.agda |
| `fetch-4` | - | 407 | 540 | 2 | Common/Fetch.agda |
| `fetch-5` | - | 411 | 544 | 2 | Common/Fetch.agda |
| `fetch-append-left` | 343 | 431 | 490 | 5 | Common/Fetch.agda |
| `fetch-append-right` | 351 | 438 | 484 | 4 | Common/Fetch.agda |
| `exec-two-steps` | - | 544 | 1956 | 8 | Common/Exec.agda |
| `exec-three-steps` | - | 553 | 1967 | 9 | Common/Exec.agda |
| `exec-four-steps` | - | 563 | 1977 | 9 | Common/Exec.agda |
| `exec-five-steps` | - | 574 | 1988 | 10 | Common/Exec.agda |
| `step-exec-0..5` | - | 466-510 | 508-786 | 30 | Common/Exec.agda |

**Total: ~87 lines → Common/Fetch.agda + Common/Exec.agda**

### Medium Priority: Similar Patterns (Abstract Interface)

| Lemma Pattern | AArch64 | RiscV64 | X86 | Pattern |
|---------------|---------|---------|-----|---------|
| `readMem-writeMem-same` | 293 | 362 | 425 | Same semantics, different proofs |
| `readMem-writeMem-diff` | 298 | 379 | 442 | Same semantics, different proofs |
| `exec-chain` | 474 | - | 1034 | Complex recursion |
| `exec-one-step` | 365 | 528 | 897 | Varies by ISA |

**Recommendation:** Create a shared interface/record in Common/Memory.agda with architecture-specific instantiation.

### Low Priority: Architecture-Specific (Keep Separate)

| Lemma | Location | Reason |
|-------|----------|--------|
| `readReg-writeReg-same` | AArch64:137 | 31 cases specific to x0-x30 |
| `readSP-*` | AArch64:212 | SP handling varies by ISA |
| `execInstr-*` | All | Instruction semantics differ |

---

## Table 2: Generator Groupings by Proof Complexity

### Trivial Generators (can share proof template)

| Generator | Proof Pattern | Lines per Backend |
|-----------|---------------|-------------------|
| id | `refl` | 5-10 |
| fold | `refl` with Fix wrapper | 10-15 |
| unfold | `refl` with Fix unwrap | 10-15 |
| arr | `refl` | 5-10 |
| terminal | Single mov/li | 15-20 |
| initial | trap/brk/ebreak | 10-15 |

**Recommendation:** Create `Correct/Trivial.agda` with shared structure.

### Projection Generators (single load pattern)

| Generator | Proof Pattern | Lines per Backend |
|-----------|---------------|-------------------|
| fst | Load from offset 0 | 30-50 |
| snd | Load from offset 8 | 30-50 |

**Recommendation:** Create `Correct/Projection.agda` - pattern match limitation makes these harder to share.

### Injection Generators (tag + value store)

| Generator | Proof Pattern | Lines per Backend |
|-----------|---------------|-------------------|
| inl | Store tag=0, value | 50-70 |
| inr | Store tag=1, value | 50-70 |

**Recommendation:** Create `Correct/Injection.agda` - similar structure.

### Compound Generators (recursive, hardest)

| Generator | Proof Difficulty | Lines per Backend | Key Challenge |
|-----------|-----------------|-------------------|---------------|
| compose | Medium | 80-150 | exec-concat lemma |
| pair | High | 150-250 | Nested IH, register preservation |
| case | High | 150-250 | Branch reasoning, nested IH |

**Recommendation:** Create `Correct/Compound.agda` - these benefit most from consolidation.

### Exponential Generators (closure handling)

| Generator | Proof Status | Lines per Backend | Key Challenge |
|-----------|-------------|-------------------|---------------|
| curry | Partial | 100-200 | Jump over thunk |
| apply | Postulated | N/A | Fundamental model limitation |

**Recommendation:** Create `Correct/Exponential.agda` - document apply limitation.

---

## Table 3: Common/Fetch.agda Specification

```agda
------------------------------------------------------------------------
-- Backend.Common.Fetch
-- Generic list indexing lemmas for instruction fetching
------------------------------------------------------------------------

module Once.Backend.Common.Fetch where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Generic fetch function (list indexing)
fetch : ∀ {A} → List A → ℕ → Maybe A
fetch [] _ = nothing
fetch (x ∷ xs) zero = just x
fetch (x ∷ xs) (suc n) = fetch xs n

-- Immediate indexing lemmas
fetch-0 : ∀ {A} (i : A) (is : List A) → fetch (i ∷ is) 0 ≡ just i
fetch-0 i is = refl

fetch-1 : ∀ {A} (i₀ i₁ : A) (is : List A) → fetch (i₀ ∷ i₁ ∷ is) 1 ≡ just i₁
fetch-1 _ _ _ = refl

-- ... fetch-2 through fetch-N ...

-- Append lemmas
fetch-append-left : ∀ {A} (xs ys : List A) (n : ℕ) → n < length xs →
  fetch (xs ++ ys) n ≡ fetch xs n
fetch-append-left (x ∷ xs) ys zero _ = refl
fetch-append-left (x ∷ xs) ys (suc n) (s≤s p) = fetch-append-left xs ys n p

fetch-append-right : ∀ {A} (xs ys : List A) (n : ℕ) →
  fetch (xs ++ ys) (length xs + n) ≡ fetch ys n
fetch-append-right [] ys n = refl
fetch-append-right (x ∷ xs) ys n = fetch-append-right xs ys n

-- Past-end returns nothing
fetch-past-end : ∀ {A} (xs : List A) (n : ℕ) → n ≥ length xs →
  fetch xs n ≡ nothing
-- ...
```

**Estimated size:** 80-100 lines
**Used by:** All three backends

---

## Table 4: Common/Exec.agda Specification

```agda
------------------------------------------------------------------------
-- Backend.Common.Exec
-- Generic N-step execution lemmas (parameterized by step function)
------------------------------------------------------------------------

module Once.Backend.Common.Exec
  {State : Set}
  (halted : State → Bool)
  (step : State → Maybe State)
  where

-- N-step execution
exec : ℕ → State → Maybe State
exec zero s = just s
exec (suc n) s with halted s
... | true = just s
... | false with step s
...   | nothing = nothing
...   | just s' = exec n s'

-- Two-step execution pattern
exec-two-steps : ∀ (s s₁ s₂ : State) →
  halted s ≡ false → step s ≡ just s₁ →
  halted s₁ ≡ false → step s₁ ≡ just s₂ →
  halted s₂ ≡ true →
  exec 2 s ≡ just s₂
-- ...

-- Three-step, four-step, ... patterns
-- These are mechanical extensions of the two-step pattern
```

**Issue:** This requires parameterizing over State, halted, step - each backend has different types.

**Alternative:** Use a type class or record to abstract the interface:

```agda
record ExecutionSemantics : Set₁ where
  field
    State : Set
    halted : State → Bool
    step : State → Maybe State
```

**Estimated size:** 150-200 lines
**Complexity:** Medium - requires careful parameterization

---

## Table 5: Refactoring Order

| Phase | Task | Effort | Benefit | Dependencies |
|-------|------|--------|---------|--------------|
| 1 | Create Common/Fetch.agda | Low | 87 lines saved | None |
| 2 | Update backends to import Fetch | Low | Cleaner code | Phase 1 |
| 3 | Create Common/Exec.agda skeleton | Medium | Interface clarity | None |
| 4 | Split Correct.agda by generator group | Medium | Easier navigation | None |
| 5 | Parameterize exec lemmas | High | 100+ lines saved | Phase 3 |
| 6 | Abstract memory interface | High | Proof consistency | None |

### Phase 1: Common/Fetch.agda (Immediate Win)

**Create:** `formal/Once/Backend/Common/Fetch.agda`

**Content:** Generic fetch-0 through fetch-N, fetch-append-left/right

**Impact:**
- Removes ~15 lines from each backend
- Total savings: ~45 lines
- Very low risk - these are trivial refl proofs

### Phase 2: Import Fetch in Backends

**Modify:**
- `AArch64/Correct.agda`: Add `open import Once.Backend.Common.Fetch`
- `RiscV64/Correct.agda`: Same
- `X86/Correct.agda`: Same

**Remove:** Local fetch-* lemmas from each file

### Phase 3: Split Correct.agda

For each backend, split the monolithic Correct.agda:

```
Correct/
├── Main.agda              # Re-exports all, maintains compatibility
├── Trivial.agda           # id, fold, unfold, arr, terminal, initial
├── Projection.agda        # fst, snd
├── Injection.agda         # inl, inr
├── Compound.agda          # compose, pair, case
└── Exponential.agda       # curry, apply
```

**Benefits:**
- Faster type-checking (only recheck changed module)
- Easier navigation
- Parallel development on different generators

---

## Table 6: Code Sharing Blockers

| Pattern | Blocker | Workaround |
|---------|---------|------------|
| `readReg-writeReg-same` | 31 cases for AArch64 registers | Keep architecture-specific |
| `readMem-writeMem-*` | Equality decidability differs | Abstract interface |
| `execInstr` | Instruction sets differ completely | No sharing possible |
| `exec-concat-left` | PC tracking is ISA-specific | Share structure only |
| `run-*-seq` postulates | ISA-specific instruction patterns | Keep separate |

---

## Table 7: Line Count Projections

### Before Refactoring

| Backend | Correct.agda | Other Files | Total |
|---------|-------------|-------------|-------|
| AArch64 | 2,454 | ~500 | ~2,954 |
| RiscV64 | 2,072 | ~400 | ~2,472 |
| X86 | 7,612 | ~600 | ~8,212 |
| **Total** | **12,138** | **~1,500** | **~13,638** |

### After Refactoring (Estimated)

| Location | Lines | Change |
|----------|-------|--------|
| Common/Fetch.agda | 100 | New |
| Common/Exec.agda | 200 | New |
| Common/Memory.agda | 100 | New |
| AArch64/Correct/* | 2,100 | -354 (-14%) |
| RiscV64/Correct/* | 1,800 | -272 (-13%) |
| X86/Correct/* | 6,800 | -812 (-11%) |
| **Total** | **11,100** | **-1,038 (-8%)** |

**Note:** The savings are modest in percentage terms but significant in maintainability:
- Common changes to fetch/exec lemmas now happen in one place
- Generator groupings make proofs easier to find and understand
- Clearer separation enables parallel work

---

## Immediate Actions (Can Start Now)

### Action 1: Create Common/Fetch.agda

```bash
mkdir -p formal/Once/Backend/Common
# Create Fetch.agda with generic list lemmas
```

### Action 2: Create Generator Grouping Template

For each backend, add section markers in existing Correct.agda:

```agda
------------------------------------------------------------------------
-- TRIVIAL GENERATORS: id, fold, unfold, arr, terminal, initial
------------------------------------------------------------------------

-- ... existing code ...

------------------------------------------------------------------------
-- PROJECTION GENERATORS: fst, snd
------------------------------------------------------------------------

-- ... existing code ...
```

This makes future splitting easier without breaking anything.

### Action 3: Document Sharing Decisions

Add to CLAUDE.md:

```markdown
## Proof File Structure

- `Backend/Common/`: Shared lemmas (fetch, exec patterns)
- `Backend/*/Correct/`: Generator proofs split by category
- Keep ISA-specific lemmas in backend directories
```

---

## Conclusion

The main value of refactoring is not raw line count reduction (~8%) but:

1. **Single source of truth** for generic lemmas (fetch, exec patterns)
2. **Easier navigation** with generator-based file organization
3. **Faster iteration** - type-check only affected modules
4. **Parallel development** - different people can work on different generator groups
5. **Consistent patterns** - Common/ modules establish canonical proof strategies

The recommended approach is incremental: start with Common/Fetch.agda (low risk, immediate benefit), then expand as patterns become clearer.
