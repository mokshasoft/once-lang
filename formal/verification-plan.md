# Full Compiler Stack Verification Plan

## Scope

Verify the complete compilation pipeline from **RawExpr (parser output) to x86-64 machine code** for arbitrary Once programs.

**In Scope**:
- TypeCheck/Elaborate - Type checking and elaboration to Surface.Expr
- Surface/Elaborate - Surface syntax to Core IR (already proven)
- Optimization - Categorical rewrites (already proven)
- Arithmetic compiler integration - OCP-0001 (already proven, verify integration)
- End-to-end composition - Complete pipeline theorem from RawExpr to x86-64

**Out of Scope**:
- CLI/Parser (Haskell, unverified by design)
- C backend (IR → C generation)
- **Generator correctness proofs** (id, compose, pair, fst, snd, inl, inr, case, curry, apply, etc.) - **ALREADY PROVEN**, do NOT modify Backend/X86/Correct.agda generator proofs
- Backend mechanical postulates - generator-level implementation details, out of scope

**Important**: Work on layers ABOVE generators. Types between arithmetic IR and generators remain separate (not unified).

## Current Status

| Component | Status | Postulates |
|-----------|--------|-----------|
| Core IR semantics | ✓ Proven | 0 |
| Categorical laws (18) | ✓ Proven | 0 |
| Type soundness | ✓ Proven | 0 |
| Surface elaboration | ✓ Proven | 0 |
| Desugar | ✓ Proven | 0 |
| Optimization | ✓ Proven | 0 |
| Arithmetic compiler (OCP-0001) | ✓ Proven | 0 |
| **TypeCheck/Elaborate** | **In Progress** | **1** (exchange₆) |
| x86-64 generators | ✓ Proven | N/A (out of scope) |
| End-to-end (SurfaceIR→x86) | ✓ Proven | 0 |
| **End-to-end (RawExpr→x86)** | **TODO** | Needs TypeCheck integration |

## Problems

### Problem 1: `exchange₆` Postulate

**File**: `formal/Once/TypeCheck/Elaborate.agda:220-225`

**Violation**: proof-instructions.md Principle 1 (No Inline Postulates)

```agda
postulate
  exchange₆ : ∀ {n} {Γ : SCtx n} {A B C D E F G H : Type}
            → SExpr ((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) H
            → SExpr (((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) H
```

**Solution**: Change the abstraction - implement generalized `exchangeN` with well-founded recursion

### Problem 2: TypeCheck Integration

**File**: `formal/Once/EndToEnd.agda`

**Issue**: Current end-to-end theorem starts from `SurfaceIR`, not `RawExpr`

**Solution**: Extend theorem to compose TypeCheck/Elaborate correctness

### Problem 3: MAlonzo Extraction

**Files**: `compiler/src/Once/CLI.hs`, `compiler/app/Main.hs`

**Issue**: `--verified` flag enables opt-in verification with fallback

**Solution**: Complete proofs, extract all modules, remove flag (verification becomes default)

## Implementation Plan

### Phase 1: Eliminate Exchange Postulate via Dependent Types (1-2 weeks)

**Goal**: Zero inline postulates in TypeCheck/Elaborate using generalized `exchangeN`

**Decision: Dependent Types Approach (Option C)**

After extending the mechanical pattern from depth 6 → 8, we determined that **only a fully generalized solution enables verification of arbitrary Once programs**:

- ❌ **Option A** (Accept exchange₈ as axiom): Violates proof-instructions.md Principle 1, fails for programs with 8+ nested binders
- ❌ **Option B** (Continue pattern to depth 10-12): Eventually hits limit, doesn't address root cause
- ✅ **Option C** (Generalized exchangeN): Handles **any** nesting depth, zero postulates, truly arbitrary

**Why This is Essential:**

Programs with deep nesting are legitimate and can occur via:
- Nested pattern matching + closures
- Infix operators creating multiple curried parameters
- Complex combinator-based code

The goal of "full end-to-end verification of arbitrary Once programs" requires handling **unbounded** nesting depth.

**Implementation Approach:**

Type-level infrastructure:
```agda
extendMany : ∀ {n} (m : ℕ) → SCtx n → Vec Type m → SCtx (m Nat.+ n)
exchangeN : ∀ {n} (depth : ℕ) {Γ : SCtx n} {A Result : Type} (types : Vec Type depth)
          → SExpr (extendMany depth Γ types) Result
          → SExpr (extendMany depth (Γ S, A) types) Result
```

Breakthrough: `extendMany` builds nested contexts at the type level, enabling arbitrary-depth manipulation without explicit nesting levels.

**Tasks**:

1. **✅ Design type-level infrastructure** (DONE)
   - `extendMany` to build nested contexts from Vec
   - `exchangeN` signature with dependent types
   - Integrated into mutual block with weaken/exchange

2. **🔄 Fix operator ambiguities** (IN PROGRESS)
   - ~50 instances of `Data.Nat._+_/_*_` vs `Once.Type._+_/_*_` conflicts
   - Systematic disambiguation with qualified names

3. **Complete exchangeN implementation**
   - Fill holes: variable shifting (needs lookup-extendMany)
   - Binder cases: lam, case, let (extend types vector)
   - Prove lookup-extendMany lemma

4. **Replace exchange₀ through exchange₇**
   - Use `exchangeN` throughout weaken/exchange functions
   - Remove manual exchange implementations

5. **Remove postulate and comments**
   - Delete exchange₈ postulate
   - Remove TERMINATING pragma once termination proven
   - Clean up meta-comments

6. **Type-check**
   ```bash
   cd formal
   timeout 300 make agda MODULE=Once/TypeCheck/Elaborate
   ```

**Files**: `formal/Once/TypeCheck/Elaborate.agda`

**Success**: Zero postulates, handles arbitrary nesting depth, type-checks without timeout

---

### Phase 2: TypeCheck Soundness (1 week)

**Goal**: Prove type checking produces well-typed terms

**Tasks**:

1. **Prove inferElab soundness**
   - Prove: `inferElab ctx e = just (A , se) → ⊢ e : A`
   - Show intrinsically-typed `se` corresponds to `e`

2. **Update Sound.agda**
   - Complete soundness theorems
   - Remove any postulates

**Files**:
- `formal/Once/TypeCheck/Sound.agda`
- `formal/Once/TypeCheck/Elaborate.agda`

**Success**: TypeCheck soundness fully proven, no postulates

---

### Phase 3: End-to-End Integration (1 week)

**Goal**: Prove correctness for arbitrary Once programs (RawExpr → x86-64)

**Tasks**:

1. **Extend EndToEnd.agda**
   - Import TypeCheck/Elaborate soundness
   - Compose: `inferElab-sound ∘ elaborate-correct ∘ optimize-correct ∘ codegen-x86-correct`
   - State theorem:
   ```agda
   compiler-correct : ∀ rawExpr input.
     inferElab rawExpr ≡ just (A , sExpr)
     → ∃[ s ] (Star (compile-x86 (compile (elaborate sExpr))) init s
             ∧ halted s ≡ true
             ∧ rax = encode (eval-raw rawExpr input))
   ```

2. **Verify composition**
   - Check proof type-checks
   - Ensure no gaps in chain

**Files**: `formal/Once/EndToEnd.agda`

**Success**: Complete RawExpr→x86-64 theorem proven

---

### Phase 4: MAlonzo Extraction (1 week)

**Goal**: Replace Haskell with MAlonzo-extracted verified code, remove `--verified` flag

**Tasks**:

1. **Extract verified modules**
   - Update `formal/Makefile` for extraction
   - Generate: TypeCheck.Elaborate, Surface.Elaborate, Optimize, Backend.X86
   - Output to `compiler/src/MAlonzo/Code/`

2. **Update compiler**
   - Replace Haskell elaboration with MAlonzo
   - Replace Haskell optimization with MAlonzo
   - Replace Haskell codegen with MAlonzo
   - Update `Once.CLI` and `Main.hs`

3. **Remove `--verified` flag**
   - Delete flag from CLI parser
   - Remove fallback logic
   - Verification is now the ONLY path

4. **Test**
   - All 221 tests pass with MAlonzo code
   - No fallback to Haskell

**Files**:
- `formal/Makefile`
- `compiler/src/Once/CLI.hs`
- `compiler/app/Main.hs`
- `compiler/src/Once/Elaborate/Verified.hs`
- `compiler/once.cabal`

**Success**: Flag removed, all tests pass, verification is default

---

### Phase 5: Documentation (1-2 days)

**Goal**: Update documentation, remove meta-comments

**Tasks**:

1. **Update proof-instructions.md** (if needed)
   - Document new proof patterns

2. **Update what-is-proven.md**
   - Mark all phases ✓ Proven
   - Update postulate counts to zero
   - Note verification is default

3. **Update problems-and-solutions.md**
   - Mark all Resolved
   - Document solutions
   - Add commit refs

4. **Remove meta-comments**
   - Delete "no postulates!", "PROVEN", etc.
   - Code speaks for itself (Principle 4)

**Files**:
- `formal/problems-and-solutions.md`
- `docs/formal/what-is-proven.md`
- Various Agda files

---

## Critical Files

### TypeCheck
- `formal/Once/TypeCheck/Elaborate.agda` - Contains exchange₆ postulate
- `formal/Once/TypeCheck/Sound.agda` - Soundness theorems
- `formal/Once/TypeCheck.agda` - Public API

### End-to-End
- `formal/Once/EndToEnd.agda` - Full pipeline theorem
- `formal/Once/Surface/Correct.agda` - Elaboration correctness
- `formal/Once/Optimize/Correct.agda` - Optimization correctness

### Documentation
- `formal/proof-instructions.md` - **MANDATORY RULES**
- `formal/problems-and-solutions.md` - Problem tracking
- `docs/formal/what-is-proven.md` - Status

## Proof Guidelines (MANDATORY)

### From proof-instructions.md

1. **No Inline Postulates** (Principle 1)
   - Every postulate = unfinished work
   - Goal: ZERO inline postulates
   - Can't prove? **Change the abstraction**, do NOT add postulates

2. **Star-Based Proofs** (Principle 3)
   - ALL proofs use Star relation
   - No fuel-based proofs, no step counting
   - Combinators: `star-single`, `star-trans`, `star-stepN`

3. **No Meta-Comments** (Principle 4)
   - Don't write "no postulates!", "postulate-free", "PROVEN"
   - Code speaks for itself

4. **Semantic Axioms Only** (Principle 2)
   - Only acceptable postulates: `Once/Postulates.agda`
   - Encoding axioms, memory model
   - Clearly identified and auditable

### Build Commands

```bash
# Single file (300s timeout)
timeout 300 make agda MODULE=Once/TypeCheck/Elaborate

# Full x86 backend (900s timeout)
timeout 900 make x86

# If timeout: refactor to simplify
```

## Success Criteria

1. ✓ **Zero inline postulates** - Only semantic axioms in Postulates.agda
2. ✓ **Zero meta-comments** - No justifications
3. ✓ **All phases type-check** - No timeouts
4. ✓ **End-to-end theorem** - RawExpr → x86-64 for arbitrary programs
5. ✓ **MAlonzo extraction** - All verified code extracted
6. ✓ **`--verified` flag removed** - Verification is default
7. ✓ **All tests pass** - 221 compiler tests
8. ✓ **Documentation updated** - Reflects completion

## Timeline

- **Phase 1** (exchange₆): 1-2 weeks
- **Phase 2** (TypeCheck soundness): 1 week
- **Phase 3** (End-to-End): 1 week
- **Phase 4** (MAlonzo): 1 week
- **Phase 5** (Documentation): 1-2 days

**Total**: 4-5 weeks

## Notes

- **Generator proofs OUT OF SCOPE** - Already proven, do NOT modify
- **Work ABOVE generators** - TypeCheck, Surface, optimization layers
- **Arithmetic compiler IN SCOPE** - Integration with main pipeline
- **Keep types separate** - Do not unify arithmetic IR and generator IR
- C backend out of scope
- CLI/Parser unverified by design
- **Follow proof-instructions.md strictly**
