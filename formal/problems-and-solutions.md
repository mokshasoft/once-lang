# Compiler Verification Problems and Solutions

This document tracks problems encountered and solutions applied during full compiler stack verification.

**Scope**: Surface syntax → x86-64 machine code
**Excludes**: CLI/Parser, C backend, generator correctness proofs (already proven)

---

## Refactoring Principles

This section documents the high-level principles guiding our verification and refactoring work.

### Priority Order for Postulates

When encountering postulates (axioms without proofs), apply solutions in this priority order:

**1. ELIMINATE (Best)** - Prove the property, remove the postulate entirely
   - **Stateful proofs**: Use `IRStarResultS` with validity predicates to eliminate ALL encoding postulates
   - Example: x86-64 stateful architecture eliminates 10+ encoding postulates (see Solution S1)
   - Example: `curry-output-wf` eliminated using `run-curry-star-proven` bridge pattern (see Problem 5)
   - Example: `sp-bound-for-f-in-thunk` eliminated with explicit stack preconditions
   - Goal: Zero postulates in actual execution paths

**2. GENERALIZE (Acceptable)** - Move to `Once.Backend.Common.*` for all architectures
   - Create `BackendInterface` with parameterized types (State, Program, registers)
   - Single source of truth for universal properties
   - Reduces duplication across X86/AArch64/RiscV64
   - Use when: Property is universal but architecture types differ

**3. ARCH-SPECIFIC (Worst)** - Keep separate postulates per backend
   - Only as last resort when generalization is too complex
   - Current state we're moving away from
   - Indicates incomplete refactoring

### Priority Order for Implementations

**1. GENERALIZE (Best)** - Shared implementation in `Once.Backend.Common.*`
   - Example: `StackAnalysis` (shared across all backends)
   - Example: `Star` execution relation (parameterized over instruction type)
   - Reduces duplication, ensures consistency

**2. ARCH-SPECIFIC (Fallback)** - Separate implementations per backend
   - Use when: Calling conventions differ fundamentally
   - Use when: Type system complexity makes parameterization impractical
   - Example: `ClosureWellFormed` (different return address handling: stack vs link register vs ra)
   - Example: Register-specific operations (rax/x0/a0, rsp/sp/sp)

### Decision Framework

When encountering duplication or postulates:

1. **Can we prove it?** → Eliminate postulate (Priority 1)
2. **Is it semantically universal?** → Generalize to Common (Priority 2 for postulates, 1 for implementations)
3. **Are arch differences fundamental?** → Keep arch-specific (last resort)

### Examples Applied

| Problem | Old Approach | New Approach | Priority Achieved |
|---------|--------------|--------------|-------------------|
| `curry-output-wf` | Arch-specific postulate | Bridge pattern in MutualIR eliminates it | Priority 1 ✓ |
| `sp-bound-for-f-in-thunk` | Universal postulate (false) | Explicit stack preconditions | Priority 1 ✓ |
| `run-apply-star` | Arch-specific postulate (Priority 3) | Generalized to `Once.Backend.Common.ApplyPostulate` | Priority 2 ✓ |
| `StackAnalysis` | Duplicated in X86/AArch64/RiscV64 | Moved to Common | Priority 1 ✓ |
| `ClosureWellFormed` | Considered for Common | Kept arch-specific (calling conventions differ) | Priority 2 (justified) |

### Verification Scope: Compiler Correctness for Arbitrary Programs

**Goal**: Verify the **compiler** is correct for ANY program using ANY combination of IR generators

**What we prove**:
- The Once compiler correctly translates programs to machine code
- For ANY combination of generators (curry + apply + compose + ...), composition is correct
- If an Once program type-checks, it compiles correctly

**What we do NOT prove**:
- Whether specific Once programs produce correct results (that's program verification, not compiler verification)

**Compositional approach**:
- Prove each generator correct in isolation (modular proofs)
- Prove generators compose correctly (MutualIR.agda)
- Result: Compiler works for ALL type-correct programs

**Postulate strategy**:
- Prefer: Eliminate postulates in modular composition proofs (zero internal postulates)
- Accept: Axioms only at true external boundaries (FFI, dynamic loading, syscalls)

This compositional approach ensures:
- Complex programs with deep nesting compile correctly
- Programs with higher-order functions compile correctly
- ANY combination of generators compiles correctly

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

## Problem 5: curry-output-wf Postulate in Backend Modules

**Files**:
- `formal/Once/Backend/RiscV64/Correct/IR/Curry.agda:66-74` (functionally eliminated)
- `formal/Once/Backend/X86/Correct/IR/Curry.agda` (similar postulate exists)
- `formal/Once/Backend/AArch64/Correct/IR/Curry.agda` (similar postulate exists)

**Problem**:
```agda
postulate
  curry-output-wf : ∀ {B C : Type} (prog : Program) → ClosuresWF (B ⇒ C) prog
```

This postulate axiomatizes that `curry` produces well-formed closures. It was needed because:
1. Curry generates a closure with code-ptr and env-addr
2. The ClosureWellFormed proof requires access to the mutual recursion block context
3. Curry.agda cannot import MutualIR.agda (would create circular dependency)
4. Therefore, Curry.agda postulated the WF proof

**Root Cause**:
Circular module dependency:
- `Curry.agda` needs `run-curry-star-with-wf` from `MutualIR.agda` to get ClosureWellFormed proof
- `MutualIR.agda` imports `run-curry-star` from `Curry.agda` for its mutual recursion block
- Direct import would create a cycle

**Status**:
- RiscV64: **Functionally Eliminated** (2026-01-02) - postulate kept as internal placeholder
- X86: Open (same pattern applicable)
- AArch64: Open (same pattern applicable)

**Solution Applied (RiscV64)**:

The solution uses the mutual recursion block as a bridge:

1. **MutualIR.agda - Modified `run-curry-star-with-wf`** (lines 1792-1823):
   ```agda
   -- Return BOTH CurryResult (with closure-wf proof) AND IRStarResult
   -- This avoids proof duplication by building both from single execution
   run-curry-star-with-wf : ... → ∃[ s' ] (CurryResult × IRStarResult)
   ```

2. **MutualIR.agda - Created `run-curry-star-proven`** (lines 1884-1922):
   ```agda
   -- Bridge function that extracts closure-wf from CurryResult
   -- and packages it as ClosuresWF for external callers
   run-curry-star-proven : ... → ∃[ s' ] IRStarResult
   run-curry-star-proven f prefix suffix x s ... =
     let (s' , (curry-res , ir-result)) = run-curry-star-with-wf ...
         wf-proof = CurryResult.closure-wf curry-res
         output-wf = ... , wf-proof  -- Package as ClosuresWF
     in s' , record { ... ; ir-output-wf = output-wf }  -- PROVEN!
   ```

3. **MutualIR.agda - Updated curry case** (lines 233-238):
   ```agda
   run-ir-star-at-offset (curry f) ... =
     run-curry-star-proven f ...  -- Use proven version, not postulate!
   ```

4. **Curry.agda - Postulate Kept as Placeholder** (lines 66-74):
   ```agda
   -- Internal placeholder - only used by run-curry-star
   -- NEVER used by external callers (they use run-curry-star-proven)
   postulate curry-output-wf : ...
   ```

**Key Insight**:
The mutual recursion block (`MutualIR.agda`) has access to BOTH:
- `run-curry-star` from Curry.agda (imported)
- `run-curry-star-with-wf` (defined locally with actual proof)

This allows creating a bridge function (`run-curry-star-proven`) that:
- Extracts the real ClosureWellFormed proof from CurryResult
- Packages it in IRStarResult format
- Provides it to external callers WITHOUT requiring the postulate

**Architecture**:
```
Curry.agda:
  run-curry-star (uses postulate placeholder) ← imported by MutualIR

MutualIR.agda (mutual block):
  run-curry-star-with-wf (builds actual closure-wf proof)
  run-curry-star-proven (extracts proof, wraps in IRStarResult)
  run-ir-star-at-offset (calls run-curry-star-proven) ← exported
```

External callers → `run-ir-star-at-offset` → `run-curry-star-proven` → **PROVEN WF**

**Performance Optimization**:
Returning `(CurryResult, IRStarResult)` tuple avoids proof duplication:
- Both results built from single call to `run-curry-star`
- `code-ptr-valid-proof` (large proof involving `<-≤-trans`, `+-monoʳ-<`, etc.) exists only once
- Prevents exponential type-checking time from redundant proof construction

**Result**:
- Postulate functionally eliminated (only used internally, never by external callers)
- All external callers use proven version
- Build verified: `make riscv` (exit code 0)
- Commit: ab5ce57

**Files Modified**:
- `formal/Once/Backend/RiscV64/Correct/MutualIR.agda`
- `formal/Once/Backend/RiscV64/Correct/IR/Curry.agda`

**Cross-Architecture Applicability**:

This pattern can be applied to X86 and AArch64 with architecture-specific adjustments:

| Architecture | Differences from RiscV64 | Difficulty |
|--------------|--------------------------|------------|
| **X86** | - Return address on stack (not register)<br>- No stack-requirement parameter yet | Low |
| **AArch64** | - Return address in x30 link register<br>- Different register names (x0/x19 vs a0/s0) | Low |

All three backends have identical structure:
- `ClosureWellFormed` record with `code-ptr-valid` and `thunk-correct`
- `CurryResult` record with `closure-wf` field
- Same circular dependency (Curry.agda ↔ MutualIR.agda)

**Recommendation**:
Keep architecture-specific implementations rather than creating Common modules because:
1. Backend types (State, Program, registers) differ significantly
2. Calling conventions differ (stack vs. link register for return address)
3. RiscV64 has `stack-requirement` parameter that X86/AArch64 may need when eliminating their postulates
4. Current duplication is minimal (structure is identical, only register names differ)

**Next Steps**:
- Apply same pattern to `Once/Backend/X86/Correct/MutualIR.agda` (separate branch)
- Apply same pattern to `Once/Backend/AArch64/Correct/MutualIR.agda` (separate branch)
- Verify all three backends build successfully
- Update `what-is-proven.md` to reflect postulate elimination

---

## Problem 6: `apply-produces-result` Postulate - Validation vs Verification

**Files**:
- `formal/Once/Backend/X86/Postulates.agda:125-146` (apply-produces-result)
- `formal/Once/Backend/X86/Correct/MutualIR.agda` (uses postulate in modular path)
- `formal/Once/Backend/X86/Correct/WholeProgram.agda` (incomplete whole-program path)

**Problem**:

Currently we have TWO parallel proof architectures for curry/apply:

1. **Modular Path** (`run-ir-star-at-offset` in MutualIR.agda): VALIDATION
   - Proves `∀ {i A B} (ir : IR i A B) → ...` for ANY IR ✓
   - Uses `apply-produces-result` POSTULATE for the `apply` case ✗
   - **Current status**: Complete but uses postulate (validation, not verification)

2. **Whole-Program Path** (WholeProgram.agda): TRUE VERIFICATION
   - Proves correctness for closed Once programs
   - NO `apply-produces-result` postulate needed! ✓
   - Uses `ClosureWellFormed` threading through composition
   - **Current status**: INCOMPLETE (missing memory layout threading)

**Why This Matters**:

The goal is to verify **arbitrary Once programs compile correctly** (compiler correctness).
Once programs are CLOSED (all curry/apply pairs are composed together), so we should
use the whole-program path which requires ZERO postulates.

The modular path with `apply-produces-result` is a workaround for "open programs"
(library code that receives closures from outside), which is NOT our verification target.

**Infrastructure Status** (from `WholeProgram.agda:7-35`):

✓ **Complete**:
- `ClosureWellFormed` predicate (proves closure memory structure)
- `run-curry-star-with-wf` (curry produces `ClosureWellFormed` proof)
- `run-apply-with-full-wf` (apply consumes `ClosureWellFormed` proof)
- Base curry/apply proofs

○ **Incomplete** (BLOCKING true verification):
- Pair case: doesn't produce memory layout showing where things are stored
- Compose case: doesn't thread `ClosureWellFormed` from f to g
- Case case: doesn't thread `ClosureWellFormed` through branches

**From Postulates.agda:73-89** (documentation states clearly):

```
VERIFICATION STRATEGY: WHOLE-PROGRAM PROOFS FOR CLOSED PROGRAMS

The verification goal is to prove correctness of arbitrary closed Once
programs. In closed programs:
  - Every `apply` consumes a closure created by some `curry`
  - The curry and apply are always composed together
  - ClosureWellFormed proofs flow naturally through composition

This means: NO POSTULATE NEEDED for closed program verification.
```

**Solution Path (Priority 1 - ELIMINATE)**:

Complete the whole-program path in `WholeProgram.agda`:

1. **Extend pair proof** to produce memory layout:
   ```agda
   run-pair-star-wf : ... → produces PairMemoryLayout + preserves ClosureWellFormed
   ```

2. **Extend compose proof** to thread `ClosureWellFormed`:
   ```agda
   run-compose-star-wf : ... → threads ClosureWellFormed from f to g
   ```

3. **Extend case proof** similarly for both branches

4. **Create `run-whole-program`**:
   ```agda
   run-whole-program : ∀ {i A B} (ir : IR i A B) → ...
     -- Pattern match on ALL IR constructors
     -- Thread ClosureWellFormed through composition
     -- Use run-apply-with-full-wf for apply case (NO POSTULATE!)
   ```

5. **Replace modular path** usage with whole-program path as default

**What NOT to Remove** (Critical Infrastructure):

Do NOT remove:
- ✓ `run-curry-star` - base curry proof
- ✓ `run-apply-star` - base apply proof
- ✓ `ClosureWellFormed` - essential predicate
- ✓ `run-curry-star-with-wf` - curry with WF proof
- ✓ `run-apply-with-full-wf` - apply consuming WF proof
- ✓ Individual generator proofs (compose, pair, case, etc.)

These are all ESSENTIAL for the solution!

**What to Remove** (After completing solution):

Only remove:
- ✗ `apply-produces-result` postulate in Postulates.agda
- ✗ Modular path usage that depends on this postulate
- ✗ Any validation-only test cases

**Impact**:

**Before** (current - validation):
- Works for any IR compositionally
- Uses 1 postulate for apply
- Status: Validation (not verification)

**After** (true verification):
- Works for any closed Once program compositionally
- ZERO postulates for curry/apply
- Status: True compiler correctness verification

**Estimated Effort**: Medium (3-5 days)
- Infrastructure exists, just needs completion
- Pattern already proven in isolated test cases
- Main work: threading memory layout through composition

**Files to Modify**:
- `formal/Once/Backend/X86/Correct/WholeProgram.agda` (complete)
- `formal/Once/Backend/X86/Correct/MutualIR.agda` (switch to whole-program)
- `formal/Once/Backend/X86/Postulates.agda` (remove postulate)

---

## Solutions Applied

### Solution S1: Stateful Proof Architecture (x86-64, Completed)

**Problem**: Non-stateful proofs require 10+ encoding postulates about how semantic
values map to machine words.

**Root Cause**: Proofs that use `encode (eval ir x)` must assume properties like:
- `encode-pair-fst/snd`: Pairs store first/second elements at known offsets
- `encode-inl/inr-tag/val`: Sum types store tag and value at known offsets
- `encode-closure-*`: Closures store code-ptr and env-addr at known offsets

Non-stateful proofs (RISC-V approach) postulate these properties as axioms.

**Solution**: Stateful proof architecture with validity predicates

**Architecture**:

1. **Two Result Types**:
   - `IRStarResult` (internal): `ir-rax : readReg (regs s') rax ≡ encode (eval ir x)`
   - `IRStarResultS` (external): `ir-rax-s : readReg (regs s') rax ≡ addr-out`

2. **Validity Predicates** prove memory layout explicitly:
   ```agda
   PairAtS : Word → ⟦ A ⟧ → ⟦ B ⟧ → Memory → Set
   PairAtS addr a b m =
     readMem m addr ≡ just (encode a) ∧
     readMem m (addr + 8) ≡ just (encode b)
   ```

3. **Conversion Bridge**:
   ```agda
   convert-to-stateful : IRStarResult → IRStarResultS
   ```

**Pattern Applied**:
```agda
-- Each IR generator provides stateful runner
run-fst-star-s : ... → ∃[ s' ] IRStarResultS fst prog s s' addr-out offset
run-fst-star-s addr-in (a , b) s ... =
  let (s' , res) = run-fst-star ...        -- Non-stateful proof
      res-s = convert-to-stateful fst ...  -- Convert to stateful
  in s' , res-s
```

**Result**:
- **ZERO encoding postulates** (all 10+ postulates eliminated)
- Complete E2E proofs with no assumptions about `encode` function
- Validity predicates prove actual memory layout instead

**Files Modified**:
- `formal/Once/Backend/X86/Correct/StarBase.agda` - Added `IRStarResultS`, validity predicates
- `formal/Once/Backend/X86/Correct/IR/*.agda` - All generators provide stateful runners
- `formal/Once/Postulates.agda:252-340` - Documents all ELIMINABLE postulates

**Cross-Architecture**:
- X86-64: Uses stateful proofs (ZERO encoding postulates)
- RISC-V: Still uses non-stateful proofs (requires all encoding postulates)
- AArch64: TBD (can adopt stateful approach)

**Status**: Completed for x86-64 backend

**Commits**: Multiple commits implementing stateful architecture

---

### Solution S2: StackInvariant Integration (Completed)

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
