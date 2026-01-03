# RISC-V 64-bit Backend Verification Architecture

## Executive Summary

The RISC-V backend represents the **cleanest architectural design** of the three backends, with the simplest register model and no transfer instruction overhead. It achieves 73% completion (11/15 generators) with good postulate discipline and excellent code organization.

**Status**: 11/15 generators proven (73% complete)
**Total Code**: 13 files, 10,092 lines (most concise!)
**Postulate Discipline**: ⚠️ Moderate (4 files with postulates, 1 in MutualIR - needs cleanup)
**ABI Compliance**: ✅ RISC-V LP64 ABI with custom closure protocol
**Architecture Quality**: ⭐⭐⭐⭐⭐ **BEST** - Should be the model for future backends

## The Prime Directive: No Shortcuts

**The goal is complete end-to-end verification with zero unjustified postulates.**

Every shortcut, workaround, or "temporary" postulate is technical debt. When a proof fails, there are only two valid responses:

1. **The implementation is wrong** → Fix the code generator
2. **The specification is wrong** → Fix the specification

There is NO third option of "add a postulate and move on." (See `formal/proof-instructions.md`)

## Architecture Characteristics

### Register Model (RISC-V LP64 ABI) - THE CLEANEST!

**Standard ABI Registers:**
- **a0**: Input argument AND return value (same register!)
- **sp**: Stack pointer (must be 16-byte aligned)
- **ra**: Return address (saved when making calls)
- **s1, s2**: Callee-saved (used for pair construction)

**Closure Protocol (Custom):**
- **s0**: Environment pointer for closures (NOT preserved across IR nodes)
  - Set by `apply` before jumping to curry thunk
  - Used by curry thunk to access captured environment
  - Part of closed-world curry/apply contract

**Preservation Requirements:**
```agda
record IRStarResult where
  field
    ir-s1  : readReg (regs s') s1 ≡ readReg (regs s) s1  -- ✅ Saved in pair
    ir-s2  : readReg (regs s') s2 ≡ readReg (regs s) s2  -- ✅ Saved in pair (frame ptr)
    ir-ra  : readReg (regs s') ra ≡ readReg (regs s) ra  -- ✅ Return address
    -- s0 NOT here - part of closure protocol, not preserved
```

### ⭐ NO Transfer Instruction Overhead!

**Compose structure** (RISC-V `CodeGen.agda` line 8-10):
```
-- a0 is BOTH input and output, so NO transfer instruction needed!
compile-riscv (g ∘ f) = compile-riscv f ++ compile-riscv g
```

**Why this is THE BEST:**
- **a0** serves as both input AND output register
- **No mov/nop needed** between f and g
- **Simplest possible codegen**: just concatenate
- **Simpler proofs**: Only 2 program equalities instead of 3
- **Better performance**: 1 fewer instruction per compose

**Comparison:**
| Backend | Transfer | Overhead | Reason |
|---------|----------|----------|---------|
| X86 | `mov rdi, rax` | ❌ 1 inst | rdi (input) ≠ rax (output) |
| AArch64 | `nop` | ❌ 1 inst | Unclear why (x0 = x0!) |
| **RISC-V** | **NONE** | ✅ 0 inst | **a0 = a0** |

### Advanced Stack Delta Tracking

RISC-V has the **most sophisticated stack tracking** among all backends:

```agda
record IRStarResult where
  field
    ir-sp-delta : ℕ  -- Stack bytes allocated (0, 16, or 24)
    ir-sp-delta-leq : ir-sp-delta ≤ StackDelta ir  -- Bounded by static analysis
    ir-sp : readReg (regs s') sp +ℕ ir-sp-delta ≡ readReg (regs s) sp
    ir-mem-preserved : ∀ n → readMem (memory s') (readReg (regs s) sp +ℕ n)
                           ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
```

**Benefits:**
- Tracks **exact stack allocation** per generator
- Proves **static bounds** via StackDelta computation
- **Universal memory preservation** (quantified over all caller frame offsets)
- Handles **arbitrary nesting** (pair, case, curry)

**X86/AArch64 don't have this** - they use simpler boolean stack invariants.

### Stack Alignment

All stack operations maintain 16-byte alignment per RISC-V LP64 ABI:
- **pair**: Allocates 24 bytes (8 for saved s2 + 16 for data)
- **inl/inr**: Allocates 16 bytes (tag + value)
- **curry**: Allocates 24 bytes (thunk frame: saved s2 + pair)

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
- Proven successful in X86, adopted in RISC-V

## Proof Organization

### File Structure (13 files total - MOST CONCISE!)

**Core Foundation:**
- `Foundation.agda` - Common imports, State
- `StarBase.agda` - IRStarResult definition, trivial generators
- `Star.agda` - Star relation and combinators

**Complex Generators (Extracted Helpers):**
- `IR/Compose.agda` - ComposeContext (simpler than X86 - no transfer!)
- `IR/Pair.agda` - PairContext, phase helpers (1,420 lines, no postulates!)
- `IR/Case.agda` - Case dispatch logic
- `IR/Curry.agda` - Closure creation (has curry-output-wf postulate)
- `IR/Apply.agda` - Closure invocation
- `IR/Injection.agda` - Combined inl/inr proofs
- `IR/ThunkSetup.agda` - Curry thunk setup

**Mutual Block:**
- `MutualIR.agda` - Central run-ir-star-at-offset (⚠️ has run-apply-star postulate)

**Support Files:**
- `CompileLength.agda` - Length computation proofs
- `ClosureWellFormed.agda` - Closure validity (has dummy-wf-for-arrow postulate)

### ✅ EXCELLENT: Helper Extraction Pattern

RISC-V follows the X86 proven pattern of extracting helpers:

```agda
-- From IR/Compose.agda (lines 79-100)
record ComposeContext where
  field
    code-f code-g : Program
    -- NO transfer field! (unlike X86)
    suffix-f prefix-g : Program
    len-f len-g : ℕ
    prog-eq-f prog-eq-g : ... program equalities ...  -- Only 2! (X86 has 3)

-- From MutualIR.agda (lines 261-301)
run-ir-star-at-offset (g ∘ f) prefix suffix x s ... =
  sg , assemble-compose-result f g prefix suffix x s sf sg rf' rg'  -- ✅ Uses helper!
  where
    ctx = make-compose-context f g prefix suffix
    step-f = run-ir-star-at-offset f prefix suffix-f x s ...  -- RECURSIVE
    rf' = transform-f-result f g prefix suffix x s sf rf      -- helper
    step-g = run-ir-star-at-offset g prefix-g suffix-g x s-mid ...  -- RECURSIVE
    rg' = transform-g-result ...                               -- helper
    -- ^ All helpers extracted to IR/Compose.agda - clean mutual block!
```

**Benefits** (demonstrated in RISC-V):
- MutualIR.agda is concise and focused
- Helpers are reusable and testable
- Faster type-checking
- Clear separation of concerns

## Generator Status and Complexity

### Tier 1: Trivial (5-20 lines, ✅ Complete)
- **id, fold, unfold, arr, terminal**: Single instruction or identity
- **Pattern**: `star-single h-false step-eq`
- **Status**: ✅ Proven

### Tier 2: Projections (30-50 lines, ✅ Complete)
- **fst, snd**: Single load from pair
- **Pattern**: `star-single` + memory read
- **Status**: ✅ Proven

### Tier 3: Injections (50-70 lines, ✅ Complete)
- **inl, inr**: Stack allocation + tag write
- **Pattern**: `star-step4` (4 instructions)
- **Status**: ✅ Proven (in IR/Injection.agda, no postulates!)
- **Note**: Combined in single file (unlike X86's separate Inl/Inr)

### Tier 4: Compound (80-250 lines, ⚠️ Partial)
- **compose**: ✅ Proven! Uses transform helpers, no transfer needed
- **pair**: ✅ Proven! 1,420 lines in IR/Pair.agda, **zero postulates**!
- **case**: ❌ Postulated (needs exec-concat or Star infrastructure)
- **Pattern**: Recursive IH + star-trans composition
- **Status**: 2/3 proven

**Pair is FULLY PROVEN** (unlike X86/AArch64) - this is a major achievement!

### Tier 5: Exponential (100-200+ lines, ❌ Postulated)
- **curry**: Create closure with embedded thunk code
- **apply**: Load environment, indirect call to thunk
- **Pattern**: Closure protocol, indirect jumps
- **Status**: ❌ curry-output-wf, run-apply-star postulated

## Current Postulate Inventory

| Category | Count | Status | Location |
|----------|-------|--------|----------|
| **Semantic axioms** | 0 | N/A | (uses Once/Postulates.agda) |
| **Practical bounds** | 1 | Assumption | Foundation.agda |
| **Mutual block** | 1 | ❌ Should move | MutualIR.agda:184 |
| **Curry output WF** | 1 | ❌ Should prove | IR/Curry.agda:70 |
| **Closure dummy** | 1 | ❌ Should prove | ClosureWellFormed.agda:204 |

### ⚠️ ISSUE: Postulate in MutualIR

**`run-apply-star`** (MutualIR.agda:184):
```agda
postulate
  run-apply-star : ∀ {i A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    -- Apply produces correct result
```

**Why this is bad:**
- Violates proof-instructions.md principle
- Should be in Backend/RiscV64/Postulates.agda if intentional
- Or should be proven (following X86 pattern)

**ACTION REQUIRED**: Move to Postulates.agda or prove it

### Other Postulates

1. **stackDepth-leq-stackBase** (Foundation.agda:86) - ✅ OK (practical bound)
2. **curry-output-wf** (IR/Curry.agda:70) - ❌ Prove using closure construction
3. **dummy-wf-for-arrow** (ClosureWellFormed.agda:204) - ❌ Prove or remove

## Proof Patterns: Good vs Bad

### ✅ GOOD Patterns (RISC-V Excels Here!)

1. **No transfer overhead** - ⭐ BEST PATTERN
   ```agda
   -- From IR/Compose.agda lines 7-11
   -- a0 is BOTH input and output, so NO transfer instruction needed!
   -- compile-riscv (g ∘ f) = compile-riscv f ++ compile-riscv g
   ```

2. **Helper extraction** - ✅ Follows X86 proven pattern
   ```agda
   assemble-compose-result f g prefix suffix x s sf sg rf' rg'  -- Extracted!
   transform-f-result, transform-g-result  -- Transform helpers
   ```

3. **SP-delta tracking** - ⭐ MOST SOPHISTICATED
   ```agda
   ir-sp-delta : ℕ  -- Exact bytes allocated
   ir-sp-delta-leq : ir-sp-delta ≤ StackDelta ir  -- Provably bounded
   ir-mem-preserved : ∀ n → ...  -- Universal preservation
   ```

4. **Pair proof completeness** - ⭐ ONLY BACKEND WITH ZERO POSTULATES IN PAIR
   ```agda
   -- IR/Pair.agda: 1,420 lines, fully proven!
   ```

5. **Combined Injection file** - ✅ Good organization
   - `IR/Injection.agda` has both inl and inr
   - Reduces file count, shares common patterns

### ❌ BAD Patterns (Must Fix)

1. **Postulate in MutualIR** - ❌ CRITICAL VIOLATION
   ```agda
   -- MutualIR.agda:184
   postulate run-apply-star : ...  -- ❌ Should be in Postulates.agda
   ```

2. **Curry/Apply incomplete** - ⚠️ Expected (same as all backends)
   - curry-output-wf postulated
   - run-apply-star postulated
   - Matches X86/AArch64 state

## Roadmap to Completion

### Priority 1: 🔴 Fix Postulate Discipline (CRITICAL)

**Target**: Move run-apply-star out of MutualIR.agda

**Actions**:
1. Move `run-apply-star` to `Backend/RiscV64/Postulates.agda` (if semantic axiom)
2. OR prove it using closure well-formedness (if provable)
3. Document why it's a semantic boundary (if moving to Postulates)

**Timeline**: Immediate - violates proof-instructions.md principles

### Priority 2: 🟠 Complete Case Generator

**Target**: Prove case dispatch

**Blockers**: May need exec-concat lemmas (see X86 development path)

**Actions**:
1. Study X86 case proof pattern
2. Adapt to RISC-V's cleaner register model
3. Leverage sp-delta tracking for precision

**Timeline**: Short term - following X86 proven patterns

### Priority 3: 🟡 Complete Curry/Apply

**Target**: Eliminate curry-output-wf and closure dummy postulates

**Actions**:
1. **curry-output-wf** → Prove closure is well-formed after curry
2. **dummy-wf-for-arrow** → Derive from closure construction or remove
3. **run-apply-star** → Already in Priority 1

**Timeline**: Medium term - complex but follows X86 pattern

### Priority 4: 🟢 Cleanup and Optimization

**Target**: Achieve zero unjustified postulates

**Actions**:
1. Verify all remaining postulates are semantic or practical bounds
2. Document assumption rationale
3. Extract any remaining inline helpers

**Timeline**: Long term - polish and documentation

## Verification Commands

```bash
cd formal

# Single file (300s timeout guideline)
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/StarBase.agda

# Per-module type checking
make riscv-star      # Star.agda only
make riscv-correct   # Correct.agda and MutualIR.agda

# Full backend (900s timeout guideline)
timeout 900 make riscv64
```

## Success Criteria

### ✅ Completed
- [x] Star-based execution infrastructure
- [x] IRStarResult with sp-delta tracking (most sophisticated!)
- [x] 11/15 generators proven (73%)
- [x] Helper extraction pattern (follows X86)
- [x] **NO transfer overhead** (best in class!)
- [x] **Pair fully proven** (1,420 lines, zero postulates!)
- [x] Centralized StackDelta computation

### 🔴 Critical (Priority 1)
- [ ] Move run-apply-star out of MutualIR.agda
- [ ] Centralize all postulates properly

### 🟠 Important (Priority 2)
- [ ] Complete case generator proof
- [ ] Prove curry-output-wf

### 🟡 Future (Priority 3)
- [ ] Complete curry/apply (semantic or proven)
- [ ] **`make riscv64` passes with zero unjustified postulates**

## Comparison with Other Backends

| Aspect | X86 | AArch64 | **RISC-V** |
|--------|-----|---------|------------|
| **Files** | 25 | 19 | **13** ⭐ Smallest |
| **Lines** | 16,486 | 11,006 | **10,092** ⭐ Most concise |
| **Maturity** | Reference | In progress | **In progress** |
| **Generators** | 14/15 (93%) | 8/15 (53%) | **11/15 (73%)** |
| **Postulate Discipline** | ✅ Excellent (2 files) | ❌ Poor (5 files) | **⚠️ Moderate (4 files, 1 bad)** |
| **Helper Extraction** | ✅ Yes | ❌ Some inline | **✅ Yes** ⭐ |
| **Transfer Overhead** | mov rdi,rax (1 inst) | nop (1 inst) | **None!** ⭐⭐⭐ |
| **Register Model** | Complex (rdi≠rax) | Simple (x0=x0) | **Simplest (a0=a0)** ⭐ |
| **Stack Tracking** | Boolean invariant | Boolean invariant | **SP-delta with bounds** ⭐ |
| **Pair Proof** | Has postulates | Has postulates | **ZERO postulates!** ⭐⭐⭐ |

**RISC-V is the cleanest architecture** - future backends should follow this model!

## Why RISC-V is THE BEST Architecture

### 1. ⭐ No Transfer Overhead
```
compile-riscv (g ∘ f) = compile-riscv f ++ compile-riscv g  -- Just concatenate!
```
- Simplest possible codegen
- 1 fewer instruction per compose
- 2 program equalities instead of 3

### 2. ⭐ Most Sophisticated Stack Tracking
```agda
ir-sp-delta : ℕ  -- Exact allocation
ir-sp-delta-leq : ir-sp-delta ≤ StackDelta ir  -- Provably bounded
ir-mem-preserved : ∀ n → ...  -- Universal preservation
```
- Precise resource tracking
- Static bounds verification
- Universal memory preservation

### 3. ⭐ Pair Fully Proven
- 1,420 lines of proof
- **ZERO postulates** in IR/Pair.agda
- Only backend to achieve this

### 4. ⭐ Excellent Code Organization
- 13 files (smallest codebase)
- 10,092 lines (most concise)
- Good helper extraction
- Clear module structure

### 5. ⭐ Simplest Register Model
- a0 for input AND output
- Only s1, s2 need preservation (vs X86's r14, r15, rbp)
- ra for return address
- s0 for closures (custom protocol)

## Key Actions for RISC-V

### Immediate (This Session)
1. ❌ **CRITICAL**: Move `run-apply-star` out of MutualIR.agda to Postulates.agda

### Short Term (Next Sessions)
2. Complete case generator proof
3. Prove curry-output-wf
4. Prove or document dummy-wf-for-arrow

### Long Term (Future)
5. Complete curry/apply (following X86 pattern)
6. Achieve zero unjustified postulates
7. **Serve as reference for future backends**

## Architectural Philosophy

### Arbitrary Programs, Not Toy Examples

The goal is to prove **arbitrary Once programs** compile correctly, not just specific examples.

**What this means:**
- ✓ Prove each IR generator in isolation (modular proofs in MutualIR.agda)
- ✓ Prove generators compose correctly (run-ir-star-at-offset)
- ✓ Enable verification of ANY program via compositional reasoning
- ✗ Do NOT only prove specific whole-program examples

### RISC-V as the Reference Architecture

RISC-V demonstrates that **simpler is better**:
- Simplest register model → Simplest proofs
- No transfer overhead → Faster code + simpler theorems
- SP-delta tracking → More precise specifications
- Helper extraction → Maintainable codebase

**Recommendation**: Future backends (e.g., WebAssembly, LLVM IR) should follow the RISC-V pattern, not X86.

## Lessons for Other Backends

### From RISC-V to AArch64
- **Remove the nop!** - x0 is input/output like a0, no transfer needed
- **Add sp-delta tracking** - More precise than boolean stack invariant
- **Extract helpers** - Don't build records inline

### From RISC-V to Future Backends
- **Choose simple register model** - Input = output register if possible
- **Precise resource tracking** - SP-delta with static bounds
- **Extract helpers early** - Smaller mutual blocks = faster type-checking
- **Prove pair completely** - RISC-V shows it's possible

## References

- **Proof Instructions**: `formal/proof-instructions.md` - Prime directive
- **Lessons Learned**: `docs/formal/lessons-learned.md` - Star pattern (lines 7-106)
- **X86 Architecture**: `docs/formal/x86-full-proof-architecture.md` - Reference implementation
- **AArch64 Architecture**: `docs/formal/aarch64-full-proof-architecture.md` - Similar register model
- **Decision Log**: `docs/compiler/decision-log.md` (D022: Agda, D032: Arrow effects)

---

# FINALIZATION PLAN: Stateful Proofs + Postulate Cleanup

## Executive Summary

**Goal**: Complete RISC-V backend generator proofs using X86-64's stateful proof architecture, eliminate encoding postulates, fix postulate discipline violations.

**Current State**: 11/15 generators proven (73%), excellent architecture (cleanest register model, no transfer overhead), but has encoding postulates and postulate discipline violations

**Only Acceptable Postulate**: `sp-bound-after-stack-op` (stack pointer bounds - runtime property, RISC-V equivalent of X86's `rsp-bound-after-stack-op`)

**Status**: Excellent foundation with best-in-class architecture, ready for migration to stateful proofs following X86-64 proven pattern

## CRITICAL: The Wrong Path to Avoid

### ❌ DO NOT Use `apply-produces-result` or Modular Reasoning

**Why this is the WRONG PATH**:

1. **Not needed for closed programs**: Our verification goal is arbitrary **closed Once programs** (RawExpr → machine code), NOT open program fragments

2. **Modular reasoning is a rabbit hole**: This postulate exists for hypothetical modular reasoning about open program fragments where closures come from unknown sources. We do NOT verify open fragments.

3. **ClosureWellFormed eliminates the need**: Whole-program proofs of closed Once programs use the `ClosureWellFormed` infrastructure which tracks closure creation and application through compose/pair. Every `apply` in a closed program consumes a closure created by some `curry`, and the proofs flow naturally through composition.

4. **X86-64 already documented why**: From `X86.Postulates.agda` lines 107-122:
   ```agda
   -- VERIFICATION STRATEGY: WHOLE-PROGRAM PROOFS FOR CLOSED PROGRAMS
   -- The verification goal is to prove correctness of arbitrary closed Once
   -- programs. In closed programs:
   --   - Every `apply` consumes a closure created by some `curry`
   --   - The curry and apply are always composed together
   --   - ClosureWellFormed proofs flow naturally through composition
   --
   -- This means: NO POSTULATE NEEDED for closed program verification.
   ```

**What happens if we go down this path**:
- We accept postulates we don't need
- We abandon the whole-program verification strategy
- We violate proof-instructions.md Principle 1 (No Inline Postulates)
- We fail to achieve true compiler correctness for arbitrary Once programs

**The RIGHT path**: Follow X86-64's stateful proof architecture with `ClosureWellFormed` infrastructure for whole-program proofs.

## Current Status (Detailed)

### Generators: 11/15 Proven (73%)

**✅ PROVEN (11 generators)**:
- Trivial (5): id, fold, unfold, arr, terminal
- Projections (2): fst, snd
- Injections (2): inl, inr (combined in IR/Injection.agda - excellent!)
- Compound (2): compose (NO transfer instruction!), pair (1,420 lines, ZERO postulates!)

**❌ REMAINING (4 generators)**:
- case (needs Star infrastructure, following X86 pattern)
- curry (has curry-output-wf postulate)
- apply (has run-apply-star postulate in MutualIR - CRITICAL VIOLATION)

### Architecture Strengths (Best in Class!)

**⭐ RISC-V has the CLEANEST architecture**:
1. **No transfer overhead**: `compile-riscv (g ∘ f) = f ++ g` (just concatenate!)
2. **Simplest register model**: a0 for input AND output
3. **Sophisticated stack tracking**: SP-delta with provable static bounds
4. **Pair fully proven**: 1,420 lines, ZERO postulates (only backend to achieve this!)
5. **Most concise**: 13 files, 10,092 lines (smallest codebase)

**Future backends should follow RISC-V patterns, not X86!**

### Postulates: Current Inventory and Violations

**Category 1: Runtime Properties (ACCEPTABLE)**:
- ✅ `stackDepth-leq-stackBase` (Foundation.agda:86) - Stack space assumption
  - **Note**: Should be renamed to `sp-bound-after-stack-op` to match X86 naming
  - **Status**: Permanent - runtime property

**Category 2: CRITICAL VIOLATIONS (Must Fix Immediately)**:
- ❌ `run-apply-star` (MutualIR.agda:184) - **SEVERE VIOLATION**
  - **Problem**: Postulate in mutual recursion block violates proof-instructions.md
  - **Should be**: In Backend/RiscV64/Postulates.agda if semantic axiom, OR proven using IH
  - **Priority**: CRITICAL - fix immediately

**Category 3: Closure Well-Formedness (Should Prove)**:
- ❌ `curry-output-wf` (IR/Curry.agda:70) - Prove closure is well-formed after curry
- ❌ `dummy-wf-for-arrow` (ClosureWellFormed.agda:204) - Prove or remove

**Category 4: Encoding Postulates (ELIMINABLE with stateful proofs)**:
- RISC-V currently uses non-stateful approach with encoding postulates
- **Solution**: Migrate to X86-64's stateful proof architecture (IRStarResultS)
- **Evidence**: X86 has ZERO encoding postulates using this approach

**Current Total**: ~4-5 files with postulates (VIOLATION - should be 1-2 max)

## Finalization Strategy: Multi-Phase Approach

### Priority 1: Fix Postulate Discipline (IMMEDIATE - 2-3 days)

**CRITICAL**: Move `run-apply-star` out of MutualIR.agda

**Problem**: Violates proof-instructions.md Principle 1 (No Inline Postulates)

**Options**:

**Option A (If semantic axiom)**:
1. Create `formal/Once/Backend/RiscV64/Correct/Postulates.agda`
2. Move `run-apply-star` there with full documentation
3. Document why it's a semantic boundary (like X86's apply-produces-result)
4. **BUT NOTE**: Even X86's apply-produces-result is NOT needed for closed programs!

**Option B (If provable - RECOMMENDED)**:
1. Prove using mutual recursion IH (like curry)
2. Use ClosureWellFormed infrastructure
3. Pattern from X86: curry proves closure creation, apply uses well-formedness

**Validation**:
```bash
cd formal
grep -r "^postulate$" Once/Backend/RiscV64/Correct/MutualIR.agda  # Should find 0
make -j4 riscv64
```

**Success**: ZERO postulates in MutualIR.agda, all postulates in Postulates.agda

### Priority 2: Migrate to Stateful Proof Architecture (2-3 weeks)

**Goal**: Follow X86-64's proven pattern to eliminate encoding postulates

**Pattern**: Use IRStarResultS with validity predicates instead of abstract encode

**Phase 2a: Create Stateful Infrastructure (1 week)**

**Files to create**:
- `formal/Once/Backend/RiscV64/Correct/MemoryValid.agda` - Validity predicates
- `formal/Once/Backend/RiscV64/Correct/Postulates.agda` - Centralized postulates

**Pattern (from X86)**:
```agda
-- MemoryValid.agda: Explicit addresses instead of abstract encode
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ 8) ≡ just addr-b

record InlAtS (tag addr-val addr-sum : Word) (m : Memory) : Set where
  field
    tag-valid : readMem m addr-sum ≡ just tag
    val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val
```

**Validation**:
```bash
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/MemoryValid.agda
```

**Phase 2b: Define IRStarResultS (1 week)**

**File to modify**: `formal/Once/Backend/RiscV64/Correct/StarBase.agda`

**Pattern**:
```agda
record IRStarResultS where
  field
    -- Standard Star execution
    ir-star : Star prog s s'
    ir-halted : halted s' ≡ false
    ir-pc : pc s' ≡ offset +ℕ compile-length ir

    -- Register preservation (RISC-V specific)
    ir-s1, ir-s2, ir-ra : ... preservation ...

    -- SP-delta tracking (RISC-V's sophisticated approach - KEEP THIS!)
    ir-sp-delta : ℕ
    ir-sp-delta-leq : ir-sp-delta ≤ StackDelta ir
    ir-sp : readReg (regs s') sp +ℕ ir-sp-delta ≡ readReg (regs s) sp

    -- NEW: Validity predicates instead of encode
    ir-output-valid : PairAtS addr-a addr-b a0 (memory s')
                    ∨ InlAtS tag addr a0 (memory s')
                    ∨ InrAtS tag addr a0 (memory s')
                    ∨ a0 ≡ encode-primitive val

    -- Memory preservation (RISC-V's universal quantification - KEEP THIS!)
    ir-mem-preserved : ∀ n → readMem (memory s') (readReg (regs s) sp +ℕ n)
                           ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
```

**Key insight**: Keep RISC-V's superior SP-delta and universal memory preservation!

**Phase 2c: Thread Through MutualIR (1 week)**

**Files to modify**:
- `formal/Once/Backend/RiscV64/Correct/MutualIR.agda`
- `formal/Once/Backend/RiscV64/Correct/IR/*.agda`

**Pattern (internal interface)**:
```agda
run-ir-star-at-offset : ∀ ir prefix suffix x s ... →
  IRStarResultS ir prefix suffix x s  -- Now stateful

-- Generators build validity proofs from memory operations
run-pair-star-direct : ... →
  let (addr-a, s-a) = allocate-pair-fst ...
      (addr-b, s-b) = allocate-pair-snd ...
      fst-valid = prove-from-write ...
      snd-valid = prove-from-write ...
  in record { ir-output-valid = pair-at-s fst-valid snd-valid ; ... }
```

**External interface (convert-to-stateful bridge)**:
```agda
-- External: uses encode for compatibility
run-ir-star : ∀ ir x s → IRStarResult
run-ir-star ir x s =
  let res-s = run-ir-star-at-offset ir [] [] x s ...
  in convert-to-encode res-s

convert-to-encode : IRStarResultS → IRStarResult
-- Derive encode from validity predicates
```

**Validation**:
```bash
cd formal

# Individual generators (parallel)
make -j4 agda MODULE=Once/Backend/RiscV64/Correct/IR/Pair.agda
make -j4 agda MODULE=Once/Backend/RiscV64/Correct/IR/Compose.agda

# Mutual block
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/MutualIR.agda

# Full backend
make -j4 riscv64
```

### Priority 3: Complete Remaining Generators (1-2 weeks)

**case generator** (Following X86 pattern):
- Study X86 case proof (IR/Case.agda)
- Adapt to RISC-V's cleaner architecture (no transfer!)
- Use Star composition (star-trans)

**curry generator**:
- Prove curry-output-wf using closure construction
- Pattern from X86: track closure structure through memory operations

**apply generator** (After fixing MutualIR postulate):
- If semantic axiom: Document in Postulates.agda with clear scope
- If provable: Use ClosureWellFormed infrastructure

**Validation for each**:
```bash
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/IR/Case.agda
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/IR/Curry.agda
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/IR/Apply.agda
```

### Priority 4: Eliminate Encoding Postulates (1 day)

**After stateful migration complete**:

1. Verify encoding postulates unused:
   ```bash
   cd formal
   grep -r "encode-pair-fst" Once/Backend/RiscV64/  # Should find 0
   # ... check all encoding postulates
   ```

2. Remove from dependency on Once.Postulates encoding axioms

3. Document ZERO encoding postulates achievement

**Validation**:
```bash
make -j4 riscv64 && echo "SUCCESS: RISC-V with ZERO encoding postulates"
```

## Timeline

- **Priority 1** (Postulate discipline): 2-3 days (IMMEDIATE)
- **Priority 2** (Stateful migration): 2-3 weeks
  - Phase 2a (Infrastructure): 1 week
  - Phase 2b (IRStarResultS): 1 week
  - Phase 2c (Thread through): 1 week
- **Priority 3** (Complete generators): 1-2 weeks
- **Priority 4** (Eliminate encoding postulates): 1 day

**Total**: 4-6 weeks for complete finalization

## Final Postulate Count

After completing this finalization plan:

| Category | Count | Status |
|----------|-------|--------|
| Runtime Properties | 1 | `sp-bound-after-stack-op` (PERMANENT) |
| Encoding Postulates | 0 | ✅ ELIMINATED via stateful proofs |
| Modular Reasoning | 0 | ✅ NOT NEEDED for closed programs |
| Standard Math Axioms | 2 | funext + closure-eq (PERMANENT) |
| **TOTAL FOR CLOSED PROGRAMS** | **3** | **Minimal trusted base** |

**Key point**: Same minimal trusted base as X86-64 with superior architecture!

## Build Commands

```bash
cd formal

# Parallel builds (RECOMMENDED - RISC-V is fastest backend!)
make -j4 riscv64                # Full backend
make -j4 riscv-correct          # Correctness proofs only

# Individual modules (for debugging)
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/MutualIR.agda
timeout 300 make agda MODULE=Once/Backend/RiscV64/Correct/StarBase.agda

# Quick validation
make -j4 riscv-star             # Star.agda only

# Full validation
make -j4 riscv64 && echo "SUCCESS: RISC-V backend fully proven"
```

## Success Criteria

**Completion Checklist**:
1. ✅ ZERO postulates in MutualIR.agda (moved to Postulates.agda or proven)
2. ✅ All postulates centralized in Backend/RiscV64/Correct/Postulates.agda
3. ✅ IRStarResultS with validity predicates defined
4. ✅ All generators use stateful proofs internally
5. ✅ External interface maintains encode compatibility via convert-to-stateful
6. ✅ 15/15 generators proven (case, curry, apply completed)
7. ✅ ZERO encoding postulates (following X86 pattern)
8. ✅ SP-delta tracking preserved (RISC-V's superior approach)
9. ✅ `make -j4 riscv64` passes
10. ✅ Documentation updated
11. ✅ ONLY `sp-bound-after-stack-op` runtime postulate remains

**Final State**: RISC-V backend with ZERO encoding postulates, cleanest architecture, serving as the model for future backends.

## Why RISC-V Will Be The Reference After Finalization

**Current**: X86-64 is reference (most mature, proven patterns)

**After finalization**: RISC-V should become reference because:

1. ⭐ **No transfer overhead**: Simplest possible codegen
2. ⭐ **Cleanest register model**: a0 = input = output
3. ⭐ **Superior stack tracking**: SP-delta with static bounds
4. ⭐ **Most concise**: Smallest codebase (10,092 lines vs X86's 16,486)
5. ⭐ **Pair fully proven**: Only backend with ZERO postulates in pair proof
6. ⭐ **Combined injection**: Better organization (Injection.agda vs separate Inl/Inr)

**Recommendation**: After finalization, new backends (WebAssembly, LLVM IR) should follow RISC-V patterns, not X86.

## References

- **X86 Stateful Infrastructure** (Proven pattern to follow):
  - `Once.Backend.X86.Correct.MemoryValid.agda` - Validity predicates
  - `Once.Backend.X86.Correct.StarBase.agda` - E2E stateful tests (lines 1453-1763)
- **X86 Apply Discussion**: `Once.Backend.X86.Postulates.agda` (lines 107-122) - Why apply postulate NOT needed
- **Proof Instructions**: `formal/proof-instructions.md` - Principle 1 (No Inline Postulates), Star mandatory
- **Current RISC-V Files**:
  - `formal/Once/Backend/RiscV64/Correct/MutualIR.agda` - FIX run-apply-star postulate (line 184)
  - `formal/Once/Backend/RiscV64/Correct/IR/Pair.agda` - EXCELLENT example (1420 lines, zero postulates)
