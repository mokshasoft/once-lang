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
