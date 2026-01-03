# AArch64 Backend Verification Architecture

## Executive Summary

The AArch64 backend is **in active development**, with core infrastructure in place but several generators still requiring proofs. It follows the X86 patterns in structure but has specific areas needing improvement.

**Status**: 8/15 generators proven (53% complete)
**Total Code**: 19 files, 11,006 lines
**Postulate Discipline**: ❌ Needs improvement (5 files with postulates)
**ABI Compliance**: ✅ AAPCS64 with custom closure protocol

## The Prime Directive: No Shortcuts

**The goal is complete end-to-end verification with zero unjustified postulates.**

Every shortcut, workaround, or "temporary" postulate is technical debt. When a proof fails, there are only two valid responses:

1. **The implementation is wrong** → Fix the code generator
2. **The specification is wrong** → Fix the specification

There is NO third option of "add a postulate and move on." (See `formal/proof-instructions.md`)

## Architecture Characteristics

### Register Model (AAPCS64)

**Standard ABI Registers:**
- **x0**: Input argument AND return value (simpler than X86!)
- **sp**: Stack pointer (must be 16-byte aligned)
- **x29**: Frame pointer (callee-saved)
- **x30**: Link register / return address (callee-saved)
- **x20, x21**: Callee-saved (used for pair construction)

**Closure Protocol (Custom):**
- **x19**: Environment pointer for closures (NOT preserved across IR nodes)
  - Set by `apply` before jumping to curry thunk
  - Used by curry thunk to access captured environment
  - Part of closed-world curry/apply contract

**Preservation Requirements:**
```agda
record IRStarResult where
  field
    ir-x20  : readReg (regs s') x20 ≡ readReg (regs s) x20  -- ✅ Saved in pair
    ir-x21  : readReg (regs s') x21 ≡ readReg (regs s) x21  -- ✅ Saved in pair
    ir-x29  : readReg (regs s') x29 ≡ readReg (regs s) x29  -- ✅ Frame pointer
    ir-x30  : readReg (regs s') x30 ≡ readReg (regs s) x30  -- ✅ Link register
    -- x19 NOT here - part of closure protocol, not preserved
```

### Transfer Instruction Overhead

**Compose structure:**
```
compile-aarch64 (g ∘ f) = compile-aarch64 f ++ [nop] ++ compile-aarch64 g
```

- **Why nop?**: ⚠️ UNCLEAR - x0 is both input and output, should be like RISC-V!
- **Cost**: 1 instruction per compose
- **Status**: ❌ Investigate removal (see RISC-V which has NO transfer)

**RECOMMENDATION**: Investigate whether nop can be eliminated. RISC-V proves it's not needed when input = output register.

### Stack Alignment

All stack operations maintain 16-byte alignment per AAPCS64:
- **pair**: Allocates 32 bytes (16 for saved x20/x21, 16 for data)
- **inl/inr**: Allocates 16 bytes (tag + value)
- **curry**: Allocates 16 bytes + thunk code

## Key Architectural Pattern: Star-Based Execution

**THE most important decision** (from `lessons-learned.md` lines 7-106):

```agda
-- Star is the right abstraction for execution proofs
data Star (prog : Program) : State → State → Set where
  refl* : ∀ {s} → Star prog s s
  step* : ∀ {s s' s''} →
          halted s ≡ false →
          step prog s ≡ just s' →
          Star prog s' s'' →
          Star prog s s''
```

**Why Star over fuel-based exec:**
1. **Composition is trivial**: `star-trans` is just structural recursion
2. **No fuel arithmetic**: No step counting or fuel management
3. **No case_of_ blocking**: Works with abstract scrutinees

**Pattern: "Compose high, convert at boundaries"**
- Build proofs using Star internally
- Convert to `exec` only at final theorem boundaries
- Follows the X86 proven pattern

## Proof Organization

### File Structure (19 files total)

**Core Foundation:**
- `Foundation.agda` - Common imports, State, encode
- `Postulates.agda` - Centralized semantic axioms
- `StarBase.agda` - IRStarResult definition, trivial generators

**Complex Generators:**
- `IR/Compose.agda` - ComposeContext, helper records
- `IR/Pair.agda` - PairContext, setup/middle/final phases
- `IR/Case.agda` - Case dispatch logic
- `IR/Curry.agda` - Closure creation
- `IR/Apply.agda` - Closure invocation
- `IR/StatefulProducers.agda` - Stateful pair/inl/inr proofs
- `IR/StatefulConsumers.agda` - Stateful fst/snd proofs
- `IR/StatefulCompose.agda` - Stateful compose

**Mutual Block:**
- `MutualIR.agda` - Central run-ir-star-at-offset mutual recursion (1,700+ lines)

**Support Files:**
- `StackInvariant.agda` - Stack discipline tracking
- `ThunkProof.agda` - Curry thunk correctness (postulated)
- `ClosureWellFormed.agda` - Closure validity predicates

### ❌ CRITICAL ISSUE: Inline Record Construction

**BAD pattern found in compose proof** (`MutualIR.agda:1333-1347`):

```agda
run-compose-star-direct f g prefix suffix x s ... =
  s-final , record
    { ir-star = star-full
    ; ir-halted = ir-halted res-g
    ; ir-pc = pc-final
    ; ir-x0 = ir-x0 res-g
    ; ir-x20 = trans (ir-x20 res-g) (trans (ir-x20 res-f) refl)
    ; ir-x21 = trans (ir-x21 res-g) (trans (ir-x21 res-f) refl)
    ; ... 10 more fields constructed inline ...
```

**Why this is bad:**
- Bloats the mutual block (1,700+ lines total)
- Harder to type-check (longer compilation times)
- Not modular (can't reuse logic)
- Violates the X86 pattern

**SHOULD BE** (like X86/RISC-V):
```agda
run-compose-star-direct f g prefix suffix x s ... =
  s-g , assemble-compose-result f g prefix suffix x s s-f s-nop s-g res-f res-g
  -- ^ helper in IR/Compose.agda, extracted from mutual block
```

**ACTION REQUIRED**: Extract `assemble-compose-result` helper to `IR/Compose.agda`

## Generator Status and Complexity

### Tier 1: Trivial (5-20 lines, ✅ Complete)
- **id, fold, unfold, arr, terminal**: Single instruction or identity
- **Pattern**: `star-single h-false step-eq`
- **Status**: ✅ Proven

### Tier 2: Projections (30-50 lines, ⚠️ Partial)
- **fst, snd**: Single load from pair
- **Pattern**: `star-single` + memory read
- **Status**: ⚠️ Partial proofs exist, integration pending

### Tier 3: Injections (50-70 lines, ⚠️ Partial)
- **inl, inr**: Stack allocation + tag write
- **Pattern**: `star-step4` (4 instructions)
- **Status**: ⚠️ Stateful versions proven, encoding integration pending

### Tier 4: Compound (80-250 lines, ❌ Postulated)
- **compose**: Recursive f, nop, recursive g
- **pair**: Setup (save regs), recursive f, recursive g, final (restore)
- **case**: Dispatch on tag, branch to f or g
- **Pattern**: Recursive IH + star-trans composition
- **Status**: ❌ Structure exists but proofs use postulates

**BLOCKERS**: Need exec-concat infrastructure for compose/pair/case to complete proofs

### Tier 5: Exponential (100-200+ lines, ❌ Postulated)
- **curry**: Create closure with embedded thunk code
- **apply**: Load environment, indirect call to thunk
- **Pattern**: Closure protocol, indirect jumps
- **Status**: ❌ ThunkProof.agda has postulated curry-thunk-correct

## Current Postulate Inventory

| Category | Count | Status | Location |
|----------|-------|--------|----------|
| **Semantic axioms** | 1 | Intentional | Postulates.agda |
| **Encoding axioms** | 10 | Same as X86 | Postulates.agda |
| **Practical bounds** | 1 | Assumption | Postulates.agda |
| **Thunk proofs** | 1 | ❌ Should be proven | ThunkProof.agda |
| **Closure well-formedness** | 1 | ❌ Should be proven | ClosureWellFormed.agda |
| **Apply execution** | 2 | ❌ Should be proven | IR/Apply.agda |

### ❌ CRITICAL: Scattered Postulates

**Postulates found in 5 files** (violates proof-instructions.md):
1. `Postulates.agda` - ✅ OK (semantic axioms)
2. `Foundation.agda` - ✅ OK (encodedMemory)
3. `ThunkProof.agda` - ❌ BAD (curry-thunk-correct)
4. `IR/Apply.agda` - ❌ BAD (closure-code-ptr, run-thunk-at-offset, run-ir-at-offset-apply)
5. `ClosureWellFormed.agda` - ❌ BAD (run-apply-with-wf)

**ACTION REQUIRED**: Move or eliminate postulates 3-5. Only semantic axioms should remain in Postulates.agda.

## Proof Patterns: Good vs Bad

### ✅ GOOD Patterns (Replicate These)

1. **Star-based execution** - Adopted from X86 ✅
   ```agda
   ir-star = star-single h-false step-eq  -- Trivial generators
   ir-star = star-trans star-f star-nop star-g  -- Compound generators
   ```

2. **IRStarResult standard contract** - Uniform postconditions ✅
   ```agda
   record IRStarResult where
     field
       ir-star   : Star prog s s'
       ir-halted : halted s' ≡ false
       ir-pc     : pc s' ≡ offset +ℕ compile-length ir
       ir-x0     : readReg (regs s') x0 ≡ encode (eval ir x)
       ir-x20, ir-x21, ir-x29, ir-x30 : ... preservation ...
       ir-mem-*  : ... memory preservation ...
   ```

3. **Context records** - Partially adopted ✅
   - ComposeContext exists
   - PairContext exists

### ❌ BAD Patterns (Must Fix)

1. **Inline record construction** - Major issue ❌
   - compose builds IRStarResult manually inline
   - Should extract to helper like X86
   - Bloats MutualIR.agda to 1,700+ lines

2. **Scattered postulates** - Violates discipline ❌
   - 5 files have postulates
   - Should only be in Postulates.agda
   - Hard to track assumptions

3. **Unexplained nop in compose** - Architecture smell ❌
   ```
   compile-aarch64 (g ∘ f) = compile-aarch64 f ++ nop ∷ compile-aarch64 g
   ```
   - x0 is input AND output (like RISC-V)
   - RISC-V has NO transfer instruction
   - Why does AArch64 need nop?
   - **Investigate and likely remove**

## Migration to Fuel-Free Star-Based Proofs

**Status**: 🔵 PLANNED (2026-01-02)
**Based on**: RISC-V successful modernization (2026-01-01)
**Timeline**: 3-4 weeks core, 6-9 weeks complete

### Executive Summary: The RISC-V Blueprint

RISC-V completed a comprehensive modernization on 2026-01-01, eliminating fuel-based proofs and adopting Common.Star and Common.StackAnalysis infrastructure. Key discoveries:

1. **curry-frame = 16 was WRONG** - Should be 24! (Found via frame size verification)
2. **Universal stack bounds are FALSE** - Replaced with explicit preconditions
3. **Common infrastructure saves ~165 lines** - Star (~115) + StackAnalysis (~50)
4. **Star is mandatory** - Fuel-based proofs inevitably fail

**AArch64 will follow this proven blueprint.**

### Phase 0: Update Architecture Documentation ✅

**Status**: This section
**Timeline**: 1 day

Document the complete migration plan with lessons learned, comparison tables, and success criteria.

### Phase 1: Import Common.Star Infrastructure

**Timeline**: 1-2 days
**Risk**: LOW (RISC-V validates this works)
**Expected Reduction**: ~115 lines

**Files to modify**:
- `formal/Once/Backend/AArch64/Correct/Star.agda`
- Dependent files: `StarBase.agda`, `MutualIR.agda`, `ClosureWellFormed.agda`

**Changes**:
```agda
-- REMOVE: Lines defining Star data type, core properties
-- ADD:
open import Once.Backend.Common.Star Program State halted step public

-- KEEP: Architecture-specific bridge lemmas
exec-to-star : ...
star-to-exec : ...
```

**Validation**: `timeout 300 make agda MODULE=Once/Backend/AArch64/Correct/Star.agda`

### Phase 2: Integrate Common.StackAnalysis & Prove Frame Sizes

**Timeline**: 2-3 days
**Risk**: MEDIUM (may discover curry-frame is wrong like RISC-V)
**Expected Reduction**: ~50 lines
**Critical Discovery Expected**: curry-frame verification

**Files to create**:
- `formal/Once/Backend/AArch64/Correct/AArch64FrameProof.agda` (NEW)

**Changes**:

1. **Create AArch64FrameProof.agda** - Prove allocation sizes from instruction sequences:
```agda
-- Prove from instruction: sub sp sp #32
pair-frame-value : ℕ
pair-frame-value = 32

-- CRITICAL: Verify if 16 or 24 (RISC-V found 16 was WRONG!)
curry-frame-value : ℕ
curry-frame-value = ? -- Prove from actual curry thunk setup

inl-frame-value : ℕ
inl-frame-value = 16
```

2. **Update CodeGen.agda**:
```agda
open import Once.Backend.AArch64.Correct.AArch64FrameProof
open import Once.Backend.Common.StackAnalysis
  pair-frame-value   -- 32 (PROVEN!)
  inl-frame-value    -- 16 (PROVEN!)
  inl-frame-value    -- 16 (same as inl)
  curry-frame-value  -- ?? (PROVEN! - verify actual value)
  24                 -- apply-frame (TODO: prove later)
  public
```

3. **Update Foundation.agda** - Stack space explicit parameterization:
```agda
-- OLD (FALSE universal claim):
-- postulate stackDepth-leq-stackBase : ∀ ir → StackDepth ir ≤ N

-- NEW (explicit precondition):
initWithInput : (stackSize : ℕ) → ⟦ A ⟧ → State

star-codegen-correct : ∀ ir (stackSize : ℕ) x →
  StackDepth ir ≤ stackSize →  -- Explicit precondition
  ∃[ s ] (Star (compile-aarch64 ir) (initWithInput stackSize x) s × ...)
```

**Validation**: `timeout 300 make aarch64`

**Why This Matters**: RISC-V discovered `curry-frame = 16` was wrong (should be 24). Proving from code generation catches these bugs instead of computing wrong stack bounds silently.

### Phase 3: Convert Fuel-Based Proofs to Star

**Timeline**: 1-2 weeks
**Risk**: MEDIUM (requires restructuring ~4,779 lines of proof code)
**Status**: IN PROGRESS (migration guide created)

**📖 See detailed guide**: [`docs/arch/aarch64-phase3-migration-guide.md`](../../arch/aarch64-phase3-migration-guide.md)

**Files to Convert** (8 modules total):
1. `formal/Once/Backend/AArch64/Correct/IR/StatefulCompose.agda` (170 lines) - Start here!
2. `formal/Once/Backend/AArch64/Correct/IR/Apply.agda` (268 lines)
3. `formal/Once/Backend/AArch64/Correct/IR/Compose.agda` (306 lines) - Core pattern
4. `formal/Once/Backend/AArch64/Correct/IR/Curry.agda` (309 lines)
5. `formal/Once/Backend/AArch64/Correct/IR/Case.agda` (510 lines)
6. `formal/Once/Backend/AArch64/Correct/IR/StatefulProducers.agda` (630 lines)
7. `formal/Once/Backend/AArch64/Correct/IR/Pair.agda` (913 lines)
8. `formal/Once/Backend/AArch64/Correct/IR/StatefulConsumers.agda` (1673 lines)
9. `formal/Once/Backend/AArch64/Correct/Foundation.agda` (cleanup fuel-based lemmas)

**Pattern for conversion**:
```agda
-- OLD (fuel-based - FAILS on complex proofs):
helper : ∀ n → exec n prog s ≡ just s' → ...
helper n exec-eq = ... complex fuel arithmetic ...

-- NEW (Star-based - ALWAYS WORKS):
helper : ∀ → Star prog s s' → ...
helper star-proof = ... use star-trans (trivial!) ...
```

**Star combinators**:
- `star-step2-6` for fixed instruction sequences
- `⟨ h , step-eq ⟩◅ rest` to build step chains
- `star-trans` to compose (replaces ALL fuel arithmetic)

**Validation after each file**: `timeout 300 make agda MODULE=Once/Backend/AArch64/Correct/IR/[File].agda`

### Phase 4: Centralize Postulates

**Timeline**: 2-3 days
**Risk**: LOW (mostly moving code)
**Target**: Only Postulates.agda and Foundation.agda have postulates

**Current violations** (5 files):
1. `Postulates.agda` - ✅ OK (semantic axioms)
2. `Foundation.agda` - ✅ OK (encodedMemory)
3. `ThunkProof.agda` - ❌ BAD (curry-thunk-correct)
4. `IR/Apply.agda` - ❌ BAD (3 postulates)
5. `ClosureWellFormed.agda` - ❌ BAD (5+ postulates)

**Actions**:
1. **Audit**: `grep -r "^postulate$" formal/Once/Backend/AArch64/Correct/`
2. **For each scattered postulate**:
   - If semantic axiom → Move to Postulates.agda with documentation
   - If provable → Prove using mutual block IH
   - If cyclic dependency → Restructure to eliminate cycle
3. **Specific moves**:
   - `curry-thunk-correct` → Move to mutual block (RISC-V pattern)
   - IR/Apply postulates → Move to mutual block where run-ir-star-at-offset available
   - ClosureWellFormed arithmetic helpers → Keep (trivially provable, OK)

**Validation**: `grep -r "^postulate$" formal/Once/Backend/AArch64/Correct/ | wc -l` should be ≤2

**Principle** (from proof-instructions.md): NO inline postulates in proof files. Only semantic axioms in Postulates.agda.

### Phase 5: Complete Frame Size Proofs

**Timeline**: 1 week
**Risk**: MEDIUM (may discover wrong values)

**Priority order**:

1. **pair-frame** (HIGH PRIORITY)
   - Currently: 32 bytes
   - Prove from: `sub sp sp #32`

2. **curry-frame** (CRITICAL - May Reveal Bug!)
   - Currently: Unknown (hardcoded 16?)
   - RISC-V: Was 16, SHOULD BE 24
   - Prove from curry thunk setup instructions
   - **This may reveal AArch64 has same bug**

3. **inl-frame / inr-frame** (MEDIUM PRIORITY)
   - Currently: 16 bytes each
   - Prove from injection code generators

4. **apply-frame** (LOW PRIORITY)
   - Currently: Unknown
   - May be redundant with curry-frame
   - Prove from thunk invocation

**Pattern** (from RISC-V CurryFrameProof.agda):
```agda
curry-frame-correct : curry-setup-reduces-sp-by curry-frame-value
curry-frame-correct = prove-from-instruction (sub sp sp #curry-frame-value)
```

**Validation**: `timeout 300 make agda MODULE=Once/Backend/AArch64/Correct/AArch64FrameProof.agda`

### Phase 6: Investigate nop Removal (OPTIONAL)

**Timeline**: 3-5 days
**Risk**: LOW-MEDIUM (might discover constraint)
**Architectural Investigation**: Why nop when x0 = x0?

**Current**:
```agda
compile-aarch64 (g ∘ f) = compile-aarch64 f ++ [nop] ++ compile-aarch64 g
```

**Question**: x0 is both input and output (like RISC-V a0). Why nop?

**Investigation**:
1. Review RISC-V compose: `compile-riscv (g ∘ f) = f ++ g` (NO transfer!)
2. Verify AArch64 register convention (x0 input = x0 output)
3. If nop unnecessary:
   - Update CodeGen: `compile-aarch64 (g ∘ f) = f ++ g`
   - Simplify proofs (2 program equalities instead of 3)
4. If necessary, document architectural reason

**Benefits**:
- 1 fewer instruction per compose (performance)
- Simpler proofs
- Aligns with RISC-V cleaner architecture

### Phase 7: Prove Curry/Apply (OPTIONAL, ADVANCED)

**Timeline**: 2-4 weeks
**Risk**: HIGH (complex closure protocol)
**Note**: May remain as semantic axioms (acceptable)

**Approach** (following RISC-V pattern):

1. **curry-thunk-correct** - Move proof into mutual block:
   - Trace 4 thunk setup instructions using Star
   - Call run-ir-star-at-offset on f (the IH)
   - Trace ret instruction
   - Compose via star-trans

2. **run-thunk-at-offset** - Same pattern

3. **apply-produces-result** - Two paths:
   - **PATH 1** (Modular): Keep as semantic axiom (X86/RISC-V also have this)
   - **PATH 2** (Whole-program): Thread ClosureWellFormed through compose/pair

### Key Insights from RISC-V Migration

#### 1. False Universal Claims are Mathematically Wrong

**WRONG** (RISC-V eliminated this):
```agda
postulate stackDepth-leq-stackBase : ∀ ir → StackDepth ir ≤ 0x7FFF0000
-- FALSE: Arbitrary deep nesting can exceed ANY fixed bound
```

**RIGHT** (RISC-V's solution):
```agda
star-codegen-correct : ∀ ir (stackSize : ℕ) x →
  StackDepth ir ≤ stackSize →  -- Specific precondition for THIS program
  ...
-- TRUE: StackDepth is computable for any specific IR
```

**Insight**: Replace false universal claims with provable specific claims.

#### 2. Proven Constants Catch Bugs

**RISC-V Discovery** (2026-01-01):
- Hardcoded `curry-frame = 16` was WRONG
- Actual value from code generation: 24
- Silent bug would compute incorrect stack bounds

**Solution**: Prove from code generation
```agda
curry-frame-value : ℕ
curry-frame-value = 24  -- Derived from: addi sp sp neg24
```

**Benefit**: If code gen changes, proofs break (compile error) instead of silent bugs.

#### 3. Star is Mandatory

**From proof-instructions.md**:
- ALL proofs MUST use Star
- Fuel-based proofs inevitably lead to unprovable lemmas
- Star eliminates fuel arithmetic entirely

**Pattern**: "Compose high, convert at boundaries"
- Build proofs using Star internally
- Compose using `star-trans` (trivial!)
- Convert to `exec` only at final theorem boundaries

#### 4. Postulate Discipline is Critical

**From proof-instructions.md**:
- ONLY semantic axioms in `Once/Postulates.agda`
- NO inline postulates in proof files
- All assumptions centralized and auditable

**RISC-V Violation** (still being fixed):
- `run-apply-star` postulate in MutualIR.agda (line 184)
- Violates discipline

**AArch64 Current**: 5 files with postulates (❌ WORSE than RISC-V)

### Current State vs Target State

| Component | Current AArch64 | Target (Post-Migration) | RISC-V Status |
|-----------|-----------------|-------------------------|---------------|
| **Star** | Own 371-line implementation | Import Common.Star + ~250 lines bridge | ✓ Using Common.Star |
| **StackAnalysis** | Duplicate definitions? | Import Common.StackAnalysis | ✓ Using Common.StackAnalysis |
| **Frame sizes** | Hardcoded parameters | Proven from code gen | ✓ curry-frame proven (24) |
| **Stack space** | Runtime bound postulate | Explicit stackSize param | ✓ Explicit parameterization |
| **Postulate files** | 5 files | 1-2 files | 4 files (still being fixed) |
| **Execution proofs** | Mix of Star + fuel | 100% Star-based | 100% Star-based |
| **Compose transfer** | nop (unclear why) | Investigate removal | None (a0 = a0) |

**Code Reduction**: ~165 lines of duplicate code eliminated

### Generator Completeness

| Generator | AArch64 Current | AArch64 Target | RISC-V |
|-----------|-----------------|----------------|--------|
| **id, fold, unfold, arr, terminal** | ✅ Proven | ✅ Proven | ✅ Proven |
| **fst, snd** | ⚠️ Partial | ✅ Proven | ✅ Proven |
| **inl, inr** | ⚠️ Partial | ✅ Proven | ✅ Proven |
| **compose** | ❌ Postulated | ✅ Proven | ✅ Proven |
| **pair** | ❌ Postulated | ✅ Proven | ✅ Proven (1420 lines!) |
| **case** | ❌ Postulated | ✅ Proven | ❌ Postulated |
| **curry** | ❌ Postulated | ⚠️ Semantic axiom | ❌ Postulated |
| **apply** | ❌ Postulated | ⚠️ Semantic axiom | ❌ Postulated |

**Target**: 11/15 generators proven (73%), matching RISC-V with better postulate discipline

### Success Criteria

**Completion Checklist**:
1. ✅ AArch64 imports Common.Star and Common.StackAnalysis
2. ✅ All postulates in Postulates.agda (except Foundation encodedMemory)
3. ✅ Frame sizes proven from code generation (pair, inl, inr, curry)
4. ✅ Stack space uses explicit stackSize parameter (no false universal bounds)
5. ✅ All proofs use Star (zero fuel-based exec in IR/*)
6. ✅ Postulate count ≤ 4 semantic axioms (matching/exceeding RISC-V)
7. ✅ `timeout 300 make aarch64` passes
8. ✅ This architecture document updated with "Migration Complete"

**Timeline Summary**:
- **Core modernization** (Phases 0-5): 3-4 weeks
- **With optional phases** (Phases 6-7): 6-9 weeks
- **Expected state**: Clean architecture, proven frame sizes, ~165 lines saved

### Lessons Learned to Apply

1. **Arithmetic Proofs Eliminate Postulates**: Use standard library lemmas (`+-≤-to-∸`) to derive stack bounds
2. **Parameterization Over Postulation**: Explicit preconditions are provable; universal claims can be false
3. **Code Generation Verification**: Prove constants from actual instructions to catch bugs
4. **Star Transitivity is Free**: No fuel arithmetic, just structural recursion
5. **Centralization Enables Auditing**: Scattered postulates hide assumptions

### References

**RISC-V Migration** (Validated Blueprint):
- `docs/formal/shareable-proof-refactor.md` - Stack space elimination, frame verification
- `docs/formal/riscv64-full-proof-architecture.md` - Current state

**Common Infrastructure** (Production Ready):
- `formal/Once/Backend/Common/Star.agda` (~174 lines)
- `formal/Once/Backend/Common/StackAnalysis.agda` (~143 lines)

**Proof Principles** (Mandatory Reading):
- `formal/proof-instructions.md` - Prime Directive, Star mandatory, postulate discipline

---

## Roadmap to Completion (SUPERSEDED - See Migration Plan Above)

**Note**: The migration plan above supersedes this roadmap. Priorities are now:
1. Phase 1: Import Common.Star (1-2 days)
2. Phase 2: StackAnalysis + frame proofs (2-3 days)
3. Phase 3: Convert to Star (1 week)
4. Phase 4: Centralize postulates (2-3 days)
5. Phase 5: Complete frame proofs (1 week)

The old priorities below remain valid but are now integrated into the phases above.

### Priority 1: 🔴 Fix Postulate Discipline (NOW IN PHASE 4)

**Target**: Move all non-semantic postulates to proper locations or prove them

**Actions**:
1. **curry-thunk-correct** (ThunkProof.agda:117) → Prove using mutual block IH (Phase 7)
2. **closure-code-ptr** (IR/Apply.agda:121) → Derive from encode-closure-construct (Phase 4)
3. **run-thunk-at-offset** (IR/Apply.agda:251) → Prove using recursive IH (Phase 7)
4. **run-ir-at-offset-apply** (IR/Apply.agda:279) → Prove or move to Postulates.agda (Phase 4)
5. **run-apply-with-wf** (ClosureWellFormed.agda:221) → Prove using well-formedness invariants (Phase 7)

**Timeline**: High priority - violates proof-instructions.md principles

### Priority 2: 🟠 Extract Helper Functions (STILL VALID)

**Target**: Extract inline record construction to helpers (like X86)

**Actions**:
1. **compose** → Extract `assemble-compose-result` to IR/Compose.agda
2. **pair** → Verify helpers are properly extracted (already partially done)
3. **case** → Extract assembly helpers

**Benefits**:
- Faster type-checking (smaller MutualIR mutual block)
- Clearer proof structure
- Reusable across similar backends

**Timeline**: Medium priority - improves maintainability

### Priority 3: 🟡 Investigate nop Removal (NOW IN PHASE 6)

**Target**: Determine if nop in compose can be eliminated

**Actions**:
1. Review RISC-V compose implementation (no transfer needed)
2. Verify x0 register model allows direct composition
3. If possible, update CodeGen.agda to remove nop
4. Update proofs accordingly

**Benefits**:
- 1 fewer instruction per compose (performance)
- Simpler proofs (2 program equalities instead of 3)
- Cleaner architecture

**Timeline**: Low priority - optimization

### Priority 4: 🟢 Complete Remaining Generators (ONGOING)

**Target**: Prove all 15 generators

**Actions**:
1. **fst, snd**: Integrate stateful versions from StatefulConsumers.agda
2. **inl, inr**: Integrate stateful versions from StatefulProducers.agda
3. **compose, pair, case**: Complete proofs (currently postulated)
4. **curry, apply**: Complete thunk proofs (ThunkProof.agda)

**Blockers**: May need exec-concat lemmas (similar to X86 development path)

**Timeline**: Ongoing - follow X86 proven patterns

## Verification Commands

```bash
cd formal

# Single file (300s timeout guideline)
timeout 300 make agda MODULE=Once/Backend/AArch64/Correct/StarBase.agda

# Per-module type checking
make aarch64-star       # Star.agda only
make aarch64-correct    # Correct.agda and MutualIR.agda

# Full backend (900s timeout guideline)
timeout 900 make aarch64
```

## Success Criteria

### ✅ Completed
- [x] Star-based execution infrastructure (adopted from X86)
- [x] IRStarResult definition
- [x] 8/15 generators proven (trivial ones)
- [x] Context records for complex generators
- [x] Stateful proof infrastructure (StatefulProducers, StatefulConsumers)

### 🔴 Critical (Priority 1)
- [ ] Centralize postulates (only Postulates.agda should have them)
- [ ] Prove curry-thunk-correct
- [ ] Prove apply execution

### 🟠 Important (Priority 2)
- [ ] Extract assemble-compose-result helper
- [ ] Extract other inline record constructions
- [ ] Reduce MutualIR.agda size

### 🟡 Optimization (Priority 3)
- [ ] Investigate nop removal in compose
- [ ] Align with RISC-V cleaner architecture

### 🟢 Completion (Priority 4)
- [ ] Complete all 15 generators
- [ ] Prove exec-concat lemmas
- [ ] **`make aarch64` passes with zero unjustified postulates**

## Comparison with Other Backends

| Aspect | X86 | **AArch64** | RISC-V |
|--------|-----|-------------|--------|
| **Files** | 25 | **19** | 13 |
| **Lines** | 16,486 | **11,006** | 10,092 |
| **Maturity** | Reference | **In progress** | In progress |
| **Generators** | 14/15 (93%) | **8/15 (53%)** | 11/15 (73%) |
| **Postulate Discipline** | ✅ Excellent (2 files) | **❌ Poor (5 files)** | ⚠️ Moderate (4 files) |
| **Helper Extraction** | ✅ Yes | **❌ Partial** | ✅ Yes |
| **Transfer Overhead** | mov rdi,rax (unavoidable) | **nop (investigate!)** | None! |
| **Register Model** | Complex (rdi≠rax) | **Simple (x0=x0)** | Simplest (a0=a0) |

**AArch64 should be more like RISC-V** - simpler register model (x0 for input/output), but needs better postulate discipline and helper extraction.

## Key Actions for AArch64

### Immediate (This Session)
1. ❌ Move curry-thunk-correct to Postulates.agda or prove it
2. ❌ Move Apply postulates to Postulates.agda or prove them
3. ❌ Extract assemble-compose-result to IR/Compose.agda

### Short Term (Next Sessions)
4. Complete fst/snd/inl/inr integration
5. Prove compose/pair/case (may need exec-concat)
6. Investigate nop removal

### Long Term (Future)
7. Complete curry/apply proofs
8. Eliminate all mechanical postulates
9. Achieve zero unjustified postulates

## Architectural Philosophy

### Arbitrary Programs, Not Toy Examples

The goal is to prove **arbitrary Once programs** compile correctly, not just specific examples.

**What this means:**
- ✓ Prove each IR generator in isolation (modular proofs in MutualIR.agda)
- ✓ Prove generators compose correctly (run-ir-star-at-offset)
- ✓ Enable verification of ANY program via compositional reasoning
- ✗ Do NOT only prove specific whole-program examples

### Learn from X86, Optimize Like RISC-V

- **Follow X86 structure**: Proven patterns (Star, helper extraction, centralization)
- **Adopt RISC-V optimizations**: No transfer instruction (x0=x0), clean architecture
- **Fix unique issues**: Scattered postulates, inline record construction

## References

- **Proof Instructions**: `formal/proof-instructions.md` - Prime directive
- **Lessons Learned**: `docs/formal/lessons-learned.md` - Star pattern (lines 7-106)
- **X86 Architecture**: `docs/formal/x86-full-proof-architecture.md` - Reference implementation
- **RISC-V Architecture**: `docs/formal/riscv64-full-proof-architecture.md` - Clean register model
- **Decision Log**: `docs/compiler/decision-log.md` (D022: Agda, D032: Arrow effects)

---

# FINALIZATION PLAN SUMMARY

## Executive Summary

**Goal**: Complete AArch64 backend using X86-64's stateful proof architecture, following existing migration plan (Phases 1-7 above)

**Current State**: 8/15 generators proven (53%), migration plan documented, needs execution

**Only Acceptable Postulate**: `sp-bound-after-stack-op` (stack pointer bounds - runtime property)

**Status**: Migration plan complete (see above), ready for execution following X86-64/RISC-V proven patterns

## CRITICAL: The Wrong Path to Avoid

### ❌ DO NOT Use `apply-produces-result` or Modular Reasoning

**Why this is the WRONG PATH**:

1. **Not needed for closed programs**: Our verification goal is arbitrary **closed Once programs** (RawExpr → machine code), NOT open program fragments

2. **Modular reasoning is a rabbit hole**: This postulate exists for hypothetical modular reasoning about open program fragments where closures come from unknown sources. We do NOT verify open fragments.

3. **ClosureWellFormed eliminates the need**: Whole-program proofs of closed Once programs use the `ClosureWellFormed` infrastructure which tracks closure creation and application through compose/pair.

4. **X86-64 already documented why**: From `X86.Postulates.agda` lines 107-122 - apply postulate NOT needed for closed programs

**The RIGHT path**: Follow existing migration plan (Phases 1-7 above) which adopts X86-64's stateful proof architecture with `ClosureWellFormed` for whole-program proofs.

## Current Status

### Generators: 8/15 Proven (53%)

**✅ PROVEN**: Trivial generators (id, fold, unfold, arr, terminal)

**⚠️ PARTIAL**: fst, snd, inl, inr (stateful versions exist, integration pending)

**❌ REMAINING**: compose, pair, case (postulated), curry, apply

### Critical Issues

1. **Scattered postulates** - 5 files (ThunkProof, IR/Apply, ClosureWellFormed) - VIOLATES proof-instructions.md
2. **Inline record construction** - MutualIR.agda bloated (1,700+ lines)
3. **Mysterious nop in compose** - x0 is input AND output (like RISC-V), why nop?

## Execution Order (Following Migration Plan Above)

### Phase 0: ✅ COMPLETE
Migration plan documented above (Phases 1-7)

### Phase 1: Import Common.Star (1-2 days) - NEXT
Follow RISC-V proven pattern, ~115 lines reduction

### Phase 2: StackAnalysis + Frame Proofs (2-3 days)
**CRITICAL**: May discover curry-frame is wrong (like RISC-V found 16→24)

### Phase 3: Convert to 100% Star (1-2 weeks)
Convert 8 modules (~4,779 lines) from fuel-based to Star-based proofs

### Phase 4: Centralize Postulates (2-3 days) - CRITICAL
Move all postulates to Postulates.agda, fix violations

### Phase 5: Complete Frame Proofs (1 week)
Prove pair-frame, curry-frame, inl-frame, inr-frame from code generation

### Phase 6: Investigate nop Removal (OPTIONAL, 3-5 days)
x0=x0 like RISC-V, nop likely unnecessary

### Phase 7: Prove Curry/Apply (OPTIONAL, 2-4 weeks)
Use ClosureWellFormed, may remain as semantic axioms

## Final Postulate Count Target

| Category | Count | Status |
|----------|-------|--------|
| Runtime Properties | 1 | `sp-bound-after-stack-op` (PERMANENT) |
| Encoding Postulates | 0 | ✅ ELIMINATED via stateful proofs (X86 pattern) |
| Modular Reasoning | 0 | ✅ NOT NEEDED for closed programs |
| Standard Math Axioms | 2 | funext + closure-eq (PERMANENT) |
| **TOTAL FOR CLOSED PROGRAMS** | **3** | **Minimal trusted base** |

## Build Commands

```bash
cd formal

# Parallel builds (RECOMMENDED)
make -j4 aarch64              # Full backend
make -j4 aarch64-correct      # Correctness proofs only

# Individual modules
timeout 300 make agda MODULE=Once/Backend/AArch64/Correct/MutualIR.agda
timeout 300 make agda MODULE=Once/Backend/AArch64/Correct/StarBase.agda

# Quick validation
make -j4 aarch64-star         # Star.agda only

# Full validation
make -j4 aarch64 && echo "SUCCESS: AArch64 backend fully proven"
```

## Timeline

Following the detailed migration plan (Phases 1-7 above):

- **Core modernization** (Phases 1-5): 3-4 weeks
- **With optional phases** (Phases 6-7): 6-9 weeks
- **Expected state**: Clean architecture, proven frame sizes, ~165 lines saved, ZERO encoding postulates

## Success Criteria

**Completion Checklist** (matching migration plan above):
1. ✅ AArch64 imports Common.Star and Common.StackAnalysis
2. ✅ All postulates in Postulates.agda (except Foundation encodedMemory)
3. ✅ Frame sizes proven from code generation (pair, inl, inr, curry)
4. ✅ Stack space uses explicit stackSize parameter (no false universal bounds)
5. ✅ All proofs use Star (zero fuel-based exec in IR/*)
6. ✅ Postulate count ≤ 4 semantic axioms (matching/exceeding RISC-V)
7. ✅ 15/15 generators proven or documented as semantic axioms
8. ✅ ZERO encoding postulates (following X86 pattern)
9. ✅ `make -j4 aarch64` passes
10. ✅ Documentation updated
11. ✅ ONLY `sp-bound-after-stack-op` runtime postulate remains

**Final State**: AArch64 backend with ZERO encoding postulates, following proven X86-64/RISC-V patterns.

## Key References

- **Detailed Migration Plan**: See Phases 1-7 above (lines 259-628 of this file)
- **X86 Stateful Infrastructure** (Proven pattern to follow):
  - `Once.Backend.X86.Correct.MemoryValid.agda` - Validity predicates
  - `Once.Backend.X86.Correct.StarBase.agda` - E2E stateful tests (lines 1453-1763)
- **X86 Apply Discussion**: `Once.Backend.X86.Postulates.agda` (lines 107-122) - Why apply postulate NOT needed
- **RISC-V Migration Success**: `docs/formal/architecture/riscv64-backend-verification-plan.md` - Proven blueprint
- **Proof Instructions**: `formal/proof-instructions.md` - Principle 1 (No Inline Postulates), Star mandatory

## Action Items for Parallel Work

Since you requested plans for parallel work across all three backends, the priorities are:

**IMMEDIATE (this week)**:
- **X86-64**: Begin Phase 1 of stateful migration (IRStarResultS threading)
- **RISC-V**: Fix MutualIR.agda postulate violation (Priority 1, 2-3 days)
- **AArch64**: Begin Phase 1 (Import Common.Star, 1-2 days)

**SHORT TERM (next 2 weeks)**:
- **X86-64**: Complete Phase 1, start Phase 2 (E2E update)
- **RISC-V**: Begin Phase 2a (Create stateful infrastructure)
- **AArch64**: Complete Phases 1-2 (Common.Star + StackAnalysis)

**MEDIUM TERM (weeks 3-6)**:
- **X86-64**: Complete all 4 phases, achieve ZERO encoding postulates
- **RISC-V**: Complete Phases 2b-2c, Priority 3 (generators)
- **AArch64**: Execute Phase 3 (convert to Star), Phase 4 (centralize postulates)

All three backends converge on the same target: ZERO encoding postulates, ONLY `sp-bound-after-stack-op` runtime postulate, using stateful proof architecture.
