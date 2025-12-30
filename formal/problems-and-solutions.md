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
Extended the pattern from depth 5 to depth 7:
1. Added `lookup-suc-suc-suc-suc-suc-suc-suc` lemma (7 suc's)
2. Implemented `exchange₆` with all 11 Surface.Syntax constructors
3. Added `lookup-suc-suc-suc-suc-suc-suc-suc-suc` lemma (8 suc's)
4. Implemented `exchange₇` with all 11 Surface.Syntax constructors
5. Moved postulate to `exchange₈` for depth 8+ nesting
6. Type-checks successfully with `make agda MODULE=Once/TypeCheck/Elaborate.agda`

This reduces the postulate from depth 6 to depth 8. Programs requiring 8+ levels of nested binders are extremely rare (requires nesting 8 lambdas/cases/lets deep).

**Status**: In Progress - two postulate levels eliminated, `exchange₈` remains at depth 8

**Decision Point**:
Three options for completing this:

**Option A: Accept exchange₈ as axiom**
- Depth 8+ nesting is extremely rare (would need 8 nested lambdas/cases/lets)
- Pragmatic: covers virtually all real programs
- Violates proof-instructions.md Principle 1 (no inline postulates)
- Not aligned with goal of "full end-to-end verification of arbitrary Once programs"

**Option B: Continue mechanical pattern to depth 10-12**
- Extend pattern: exchange₈, exchange₉, exchange₁₀, etc.
- Each level adds ~30 lines of boilerplate
- Eventually still hits a postulate limit
- Doesn't address root cause

**Option C: Change abstraction (RECOMMENDED)**
- Generalized approach with parameterized depth
- Use **dependent types** with depth as type-level index
- Define type-level function to construct nested contexts
- Well-founded recursion on ℕ for termination
- Eliminates ALL exchange postulates
- Aligned with proof-instructions.md "change the abstraction" principle
- Aligned with goal of arbitrary program verification

**Design Approach**:
1. Define `extendCtx : ℕ → SCtx n → Vec Type m → SCtx (n + m)` to build nested contexts
2. Define generalized `lookup-suc^n` with depth parameter
3. Define `exchangeN : (depth : ℕ) → ...` parameterized by depth
4. Prove termination using well-founded recursion on depth

**Recommendation**: Pursue Option C with dependent types (depth-indexed approach)

**Implementation Progress** (2025-01-29):
- Extended mechanical pattern from depth 6 → 8 (exchange₇ implemented, postulate at exchange₈)
- Explored three generalization approaches:

**Attempt 1: Vec with type-level arithmetic `n + m`**
- Defined `extendMany : SCtx n → Vec Type m → SCtx (n + m)`
- Issue: `subst SCtx (sym (+-identityʳ n)) Γ` creates complex types
- Rewrites don't eliminate subst, blocking pattern matching
- Status: Blocked on subst complexity

**Attempt 2: Rewrite-based simplification**
- Used `rewrite +-identityʳ n | +-suc n m` to eliminate arithmetic
- Base case works: `exchangeN [] e rewrite ... = weaken e`
- Issue: Subst from extendMany persists even after rewrite
- Recursive cases still blocked on arithmetic
- Status: Blocked by interaction of rewrite + subst

**Attempt 3: Existential with List (avoiding arithmetic)**
- Defined `extendWithList : SCtx n → List Type → ∃[k] SCtx k`
- Signature: `exchangeN : (types : List Type) → (let _ , Γ' = extendWithList Γ types in SExpr Γ' Result) → ...`
- Base case works cleanly
- Issue: Variable pattern matching requires exact size exposed for `Fin k`, but existential hides it
- Unification error: `suc n ≟ extendWithList Γ (B ∷ types) .proj₁`
- Status: **Blocked - fundamental issue with existential approach**

**Key Insight**:
Variable indices (`Fin`) require exact context sizes at the type level. The existential `∃[k] SCtx k` hides the size, breaking pattern matching on variables. Any working solution must expose sizes explicitly.

**Implementation Progress** (2025-12-29):

**✅ Completed Infrastructure**:
```agda
-- Build nested context from Vec of types
extendMany : ∀ {n} → SCtx n → (m : ℕ) → Vec Type m → SCtx (n Nat.+ m)
extendMany {n} Γ zero [] rewrite +-identityʳ n = Γ
extendMany {n} Γ (suc m) (A ∷ As) rewrite +-suc n m = extendMany (Γ S, A) m As

-- Lookup lemma: variables from base context get shifted
lookup-extendMany : ∀ {n} (Γ : SCtx n) (depth : ℕ) (types : Vec Type depth) (i : Fin n)
                  → ∃[ j ] (lookup Γ i ≡ lookup (extendMany Γ depth types) j)
lookup-extendMany {n} Γ zero [] i rewrite +-identityʳ n = i , refl
lookup-extendMany {n} Γ (suc depth) (A ∷ As) i
  rewrite +-suc n depth
  with lookup-extendMany (Γ S, A) depth As (suc i)
... | j , prf = j , trans (lookup-suc i) prf

-- Generalized exchange signature
exchangeN : ∀ {n} {Γ : SCtx n} {A Result : Type} (depth : ℕ) (types : Vec Type depth)
          → SExpr (extendMany Γ depth types) Result
          → SExpr (extendMany (Γ S, A) depth types) Result
```

**✅ Depth 0 Case Working**:
```agda
exchangeN {n} {Γ} zero [] e
  rewrite +-identityʳ n | +-identityʳ (suc n)
  = weaken e
```

**❌ BLOCKED: Depths 1+ Implementation**

**Root Cause - Agda Type System Limitation**:

When attempting to implement depth 1:
```agda
exchangeN {n} {Γ} {A} {Result} (suc zero) (B ∷ []) e
  rewrite +-identityʳ (suc n)
  rewrite +-suc n zero
  rewrite +-identityʳ (suc (suc n))
  rewrite +-suc (suc n) zero
  = exchange e
```

**Error from Agda**:
```
suc (n Nat.+ 0) != lhs of type ℕ
when checking that the type of the generated with function is well-formed
```

**Technical Analysis**:

The `rewrite` mechanism in Agda:
1. Transforms the goal type by substituting equal terms
2. Creates a "with-abstraction" to expose the equality
3. This abstraction introduces fresh variables (like `lhs`)

When combining:
- **Type-level arithmetic**: `SCtx (n Nat.+ m)` with indexed types
- **Multiple rewrites**: `+-identityʳ`, `+-suc` transforming sizes
- **GADT pattern matching**: Need to match on `SExpr` constructors

The rewritten types become "opaque" to the pattern matcher. Agda cannot unify the transformed index `suc (n Nat.+ 0)` with the fresh variable `lhs` introduced by the with-abstraction, even though they're provably equal.

**Why This Is Fundamental**:

1. **Intrinsically-typed representation**: `SExpr (Γ : SCtx n) (A : Type)` embeds sizes in types
2. **Pattern matching on Fin requires exact sizes**: `var zero : SExpr (Γ S, A) A` only type-checks when context size is exactly `suc n`
3. **Rewrite hides structure**: After rewrite, Agda sees `SExpr (Γ | lhs | proof)` instead of `SExpr (Γ S, A)`
4. **Ill-typed with-abstraction**: The generated with-function has types that don't align after transformation

**Attempted Solutions** (All Failed):

1. **Vec with helper function** (lines 322-341, first attempt):
   - Used `where` clause to separate rewrite from pattern matching
   - Result: Helper function still sees rewritten types, same error

2. **Direct pattern matching** (lines 317-374, second attempt):
   - Pattern match on each constructor before applying rewrites
   - Result: Can't pattern match before rewrite - index mismatch error

3. **Delegation with arithmetic alignment** (lines 320-326, third attempt):
   - Apply all necessary rewrites, then delegate to existing `exchange`
   - Result: Ill-typed with-abstraction - rewrites create incompatible types

4. **Previous: Existential types** (documented earlier):
   - Hide sizes with `∃[k] SCtx k`
   - Result: Can't pattern match on `Fin k` when `k` is hidden

**Current Status** (2025-12-29):
- File: `formal/Once/TypeCheck/Elaborate.agda` lines 304-332
- Infrastructure: Complete and correct (extendMany, lookup-extendMany proven)
- Depth 0: Working (delegates to weaken)
- Depths 1-8+: Holes (compilation succeeds with holes, type-checks as incomplete)
- Manual exchange₀-₇: Still present and working

**Theoretical Options**:

1. **Proof-by-Reflection**: Use Agda's reflection mechanism to normalize arithmetic at compile-time
2. **Inspect Idiom**: Use Agda's `inspect` to preserve equality information through pattern matching
3. **View Patterns**: Define custom view to expose structure after arithmetic rewrites
4. **Extrinsic Typing**: Transform untyped terms, prove typing separately (abandons intrinsic approach)
5. **Sized Types**: Use Agda's sized types instead of arithmetic on ℕ (may not help with context extension)
6. **Manual Proofs**: Transport terms through equality proofs instead of rewrite (complex, unclear if better)

**Status**: **BLOCKED** - Requires either:
- Advanced Agda technique we haven't discovered
- External expertise (Agda mailing list, experts)
- Fundamental change in approach (extrinsic types, abandoning generalization)

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
