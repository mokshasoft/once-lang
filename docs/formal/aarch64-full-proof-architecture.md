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

## Roadmap to Completion

### Priority 1: 🔴 Fix Postulate Discipline

**Target**: Move all non-semantic postulates to proper locations or prove them

**Actions**:
1. **curry-thunk-correct** (ThunkProof.agda:117) → Prove using X86 pattern
2. **closure-code-ptr** (IR/Apply.agda:121) → Derive from encode-closure-construct
3. **run-thunk-at-offset** (IR/Apply.agda:251) → Prove using recursive IH
4. **run-ir-at-offset-apply** (IR/Apply.agda:279) → Prove or move to Postulates.agda
5. **run-apply-with-wf** (ClosureWellFormed.agda:221) → Prove using well-formedness invariants

**Timeline**: High priority - violates proof-instructions.md principles

### Priority 2: 🟠 Extract Helper Functions

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

### Priority 3: 🟡 Investigate nop Removal

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

### Priority 4: 🟢 Complete Remaining Generators

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
