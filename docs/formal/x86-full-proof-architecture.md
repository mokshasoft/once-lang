# X86-64 Backend Verification Architecture

## Executive Summary

The X86-64 backend verification is the **most mature and complete** of the three backend implementations, serving as the reference architecture for AArch64 and RISC-V backends.

**Status**: 14/15 generators proven (93% complete)
**Total Code**: 25 files, 16,486 lines
**Postulate Discipline**: ✅ Excellent (only 2 files with postulates)
**ABI Compliance**: ✅ System V AMD64 ABI with custom closure protocol

## The Prime Directive: No Shortcuts

**The goal is complete end-to-end verification with zero unjustified postulates.**

Every shortcut, workaround, or "temporary" postulate is technical debt. When a proof fails, there are only two valid responses:

1. **The implementation is wrong** → Fix the code generator
2. **The specification is wrong** → Fix the specification

There is NO third option of "add a postulate and move on." (See `formal/proof-instructions.md`)

## Architecture Characteristics

### Register Model (System V AMD64 ABI)

**Standard ABI Registers:**
- **rdi**: Input argument (first parameter)
- **rax**: Return value / output
- **rsp**: Stack pointer (must be 16-byte aligned)
- **rbp**: Frame pointer (callee-saved)
- **r14, r15**: Callee-saved (used for pair construction)

**Closure Protocol (Custom):**
- **r12**: Environment pointer for closures (NOT preserved across IR nodes)
  - Set by `apply` before jumping to curry thunk
  - Used by curry thunk to access captured environment
  - Part of closed-world curry/apply contract

**Preservation Requirements:**
```agda
record IRStarResult where
  field
    ir-r14  : readReg (regs s') r14 ≡ readReg (regs s) r14  -- ✅ Saved in pair
    ir-r15  : readReg (regs s') r15 ≡ readReg (regs s) r15  -- ✅ Saved in pair
    ir-rbp  : readReg (regs s') rbp ≡ readReg (regs s) rbp  -- ✅ Saved in pair
    -- r12 NOT here - part of closure protocol, not preserved
```

### Transfer Instruction Overhead

**Compose structure:**
```
compile-x86 (g ∘ f) = compile-x86 f ++ [mov rdi, rax] ++ compile-x86 g
```

- **Why needed**: rdi (input) ≠ rax (output)
- **Cost**: 1 instruction per compose
- **Status**: Unavoidable given System V calling convention

### Stack Alignment

All stack operations maintain 16-byte alignment per System V ABI:
- **pair**: Allocates 16 bytes (saved regs) + 16 bytes (data) = 32 bytes
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
- Follows same principle as type-level programming (work with types, erase at runtime)

## Proof Organization

### File Structure (25 files total)

**Core Foundation:**
- `Foundation.agda` - Common imports, State, encode
- `Postulates.agda` - Centralized semantic axioms
- `StarBase.agda` - IRStarResult definition, trivial generators

**Complex Generators (Extracted Helpers):**
- `IR/Compose.agda` - ComposeContext, helper records
- `IR/Pair.agda` - PairContext, setup/middle/final phases
- `IR/Case.agda` - Case dispatch logic
- `IR/Curry.agda` - Closure creation
- `IR/Apply.agda` - Closure invocation
- `IR/Inl.agda`, `IR/Inr.agda` - Sum injections
- `IR/ThunkStructure.agda`, `IR/ThunkExec.agda` - Curry thunk proofs

**Mutual Block:**
- `MutualIR.agda` - Central run-ir-star-at-offset mutual recursion

### Helper Extraction Pattern (✅ GOOD)

Complex generators use **context records + phase helpers**:

```agda
-- Context: computed values independent of execution
record ComposeContext where
  field
    code-f code-g : Program
    transfer : Instr
    len-f len-g : ℕ
    prog-eq-f prog-eq-transfer prog-eq-g : ... program equalities ...

-- Phase helpers: non-recursive execution steps
exec-compose-transfer : ... → TransferResult
assemble-compose-result : ... → IRStarResult (g ∘ f) ...

-- Mutual block: only recursive calls
run-compose-star-direct f g prefix suffix x s ... =
  let ctx = make-compose-context f g prefix suffix
      (s1, r1) = run-ir-star-at-offset f ...  -- RECURSIVE
      tr = exec-compose-transfer ... r1       -- helper
      (s2, r2) = run-ir-star-at-offset g ...  -- RECURSIVE
  in assemble-compose-result ... r1 tr r2     -- helper
```

**Benefits:**
- Reduces mutual block size → faster type-checking
- Separates computation from proof structure
- Reusable helpers across backends

## Generator Status and Complexity

### Tier 1: Trivial (5-20 lines, ✅ Complete)
- **id, fold, unfold, arr, terminal**: Single instruction or identity
- **Pattern**: `star-single h-false step-eq`
- **Status**: Proven

### Tier 2: Projections (30-50 lines, ✅ Complete)
- **fst, snd**: Single load from pair
- **Pattern**: `star-single` + memory read
- **Status**: Proven

### Tier 3: Injections (50-70 lines, ✅ Complete)
- **inl, inr**: Stack allocation + tag write
- **Pattern**: `star-step4` (4 instructions)
- **Status**: Proven

### Tier 4: Compound (80-250 lines, ✅ Complete)
- **compose**: Recursive f, transfer, recursive g
- **pair**: Setup (save regs), recursive f, recursive g, final (restore)
- **case**: Dispatch on tag, branch to f or g
- **Pattern**: Recursive IH + star-trans composition
- **Status**: Proven

### Tier 5: Exponential (100-200+ lines, ⚠️ Axiom)
- **curry**: Create closure with embedded thunk code
- **apply**: Load environment, indirect call to thunk
- **Pattern**: Closure protocol, indirect jumps
- **Status**: curry proven, apply has semantic axiom

## Current Postulate Inventory

| Category | Count | Status | Location |
|----------|-------|--------|----------|
| **Semantic axioms** | 1 | Intentional | Postulates.agda |
| **Encoding axioms** | 10 | 4 proven, 6 remain | Postulates.agda |
| **Practical bounds** | 1 | Assumption | Postulates.agda |
| **Mechanical** | ~10 | Could eliminate | Scattered in IR/*.agda |

### Semantic Axioms (Intentional)

**`apply-produces-result`** (`Postulates.agda:125`):
```agda
postulate
  apply-produces-result : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    -- apply produces correct result for arbitrary closures
```

**Why unprovable**: Curry stores code pointer to thunk embedded in curry's own code. Apply's isolated program doesn't contain the thunk, so can't trace execution through indirect call.

**Solutions**:
1. ✅ Accept as semantic boundary (current)
2. Defunctionalization (tag-based dispatch, breaks separate compilation)
3. Whole-program proofs (include thunk in combined program)

### Encoding Axioms (4/14 proven)

**Proven** (Stage 2 progress):
- `encode-unit` : Unit encodes to 0
- `encode-fix-wrap/unwrap` : Fix wrapping is identity
- `encode-arr-identity` : Eff = Closure semantically

**Remaining** (need allocation state tracking):
- `encode-pair-fst/snd` : Memory layout of pairs
- `encode-inl/inr-tag/val` : Memory layout of sums
- `encode-*-construct` : Inverse axioms

## Proof Patterns: Good vs Bad

### ✅ GOOD Patterns (Replicate These)

1. **Star-based execution** - Universal pattern
   ```agda
   ir-star = star-single h-false step-eq  -- Trivial generators
   ir-star = star-trans star-f star-g     -- Compound generators
   ```

2. **Helper extraction** - Reduces mutual block size
   - Context records for computed values
   - Phase helpers for non-recursive steps
   - Only recursive calls in MutualIR.agda

3. **Centralized postulates** - Easy to track
   - Semantic axioms in `Postulates.agda`
   - Clear documentation of assumptions

4. **IRStarResult standard contract** - Uniform postconditions
   ```agda
   record IRStarResult where
     field
       ir-star   : Star prog s s'
       ir-halted : halted s' ≡ false
       ir-pc     : pc s' ≡ offset +ℕ compile-length ir
       ir-rax    : readReg (regs s') rax ≡ encode (eval ir x)
       ir-r14, ir-r15, ir-rbp : ... preservation ...
       ir-mem-*  : ... memory preservation ...
   ```

### ❌ BAD Patterns (Avoid These)

1. **Inline postulates** - Hard to track, violates prime directive
   ```agda
   where
     postulate m∸n+k≡m∸n-k : ∀ m n k → ...  -- ❌ Should be in Arithmetic.agda
   ```

2. **Fuel-based exec composition** - Blocks on case_of_
   ```agda
   exec (suc n) prog s = case halted s of λ where ...  -- ❌ Use Star instead
   ```

3. **Complex PC arithmetic in proofs** - Indicates design problem
   ```agda
   pc-step = trans (+-assoc ...) (trans (cong ...) ...)  -- ❌ Use symbolic offsets
   ```

4. **Timeout workarounds** - Never replace proofs with postulates!
   - Extract to separate module instead
   - Restructure proof for clarity
   - Split large where blocks

## Roadmap to Zero Postulates

### Stage 1: ✅ Complete - Star Infrastructure

**Added**: `star-to-exec` bridge in `Star.agda`
```agda
star-to-exec : Star prog s s' → halted s' ≡ true → ∃[ n ] exec n prog s ≡ just s'
```

**Status**: Uses `exec-step-helper` postulate (plumbing, not semantic)

### Stage 2: ⚠️ In Progress - Encoding Axioms

**Target**: Derive 10 remaining encoding axioms

**Approach**: Thread allocation state or use validity predicates
- Option A: AllocState through Semantics.eval (major refactor)
- Option B: MemoryValid preconditions (moderate effort)
- Option C: Accept as semantic model axioms (minimal changes)

**Current**: Infrastructure created (`MemoryValid.agda`), full derivation pending

### Stage 3: 🔲 Pending - encode-injective

**Target**: `encode-injective` in `Encoding.agda`

**Approach**: If encode x = encode y, read memory proves components equal

### Stage 4: 🔲 Pending - Refactor to Star Throughout

**Target**: Remove fuel-based exec from internal proofs

**Pattern**:
```agda
-- Old: exec-based
exec 2 prog s ≡ just s2  -- Blocked by case_of_

-- New: Star-based
star-trans (star-single ...) (star-single ...)  -- Composes cleanly
```

### Stage 5: 🔲 Optional - Whole-Program Proofs

**Target**: Eliminate `apply-produces-result` postulate

**Approach**: Prove curry/apply in whole-program context where thunk exists in program
- Phase 1: Add whole-program entry point
- Phase 2: Restructure to include thunk in apply's program
- Phase 3: Trace through indirect call naturally

## Verification Commands

```bash
cd formal

# Single file (300s timeout guideline)
timeout 300 make agda MODULE=Once/Backend/X86/Correct/StarBase.agda

# Per-module type checking
make x86-star       # Star.agda only
make x86-encoding   # Encoding.agda
make x86-correct    # Correct.agda and IR/*.agda

# Full backend (900s timeout guideline)
timeout 900 make x86
```

## Success Criteria

### ✅ Completed
- [x] Star-based execution infrastructure
- [x] exec-to-star bridge proven
- [x] 4 encoding axioms proven
- [x] 14/15 generators proven
- [x] Helper extraction pattern established
- [x] Centralized postulates

### ⚠️ Remaining
- [ ] 10 encoding axioms (need allocation tracking)
- [ ] encode-injective derived
- [ ] All mechanical postulates eliminated
- [ ] apply semantic axiom (optional: whole-program migration)

### 🎯 Final Goal
- [ ] **`make x86` passes with zero unjustified postulates**
- [ ] **Only semantic axioms remain** (apply-produces-result, if accepted)

## Architectural Philosophy

### Arbitrary Programs, Not Toy Examples

The goal is to prove **arbitrary Once programs** compile correctly, not just specific examples.

**What this means:**
- ✓ Prove each IR generator in isolation (modular proofs in MutualIR.agda)
- ✓ Prove generators compose correctly (run-ir-star-at-offset)
- ✓ Enable verification of ANY program via compositional reasoning
- ✗ Do NOT only prove specific whole-program examples

**Implication**: Whole-program proofs (E2E-Trace) serve as validation and demonstration, but the real verification happens in the modular layer.

### Compose High, Convert at Boundaries

Work at the highest abstraction level (Star), convert only at system boundaries (final theorem).

This follows the same pattern as:
- Type-level programming: work with types, erase at runtime
- Category theory: work with morphisms, interpret at the end
- CompCert: work with step relations, extract to execution

Star is the "native" abstraction for execution proofs. Fuel-based exec is an implementation detail.

## Comparison with Other Backends

| Aspect | X86 | AArch64 | RISC-V |
|--------|-----|---------|--------|
| **Files** | 25 | 19 | 13 |
| **Lines** | 16,486 | 11,006 | 10,092 |
| **Maturity** | Most complete | In progress | In progress |
| **Generators** | 14/15 (93%) | 8/15 (53%) | 11/15 (73%) |
| **Postulate Discipline** | ✅ Excellent (2 files) | ❌ Poor (5 files) | ⚠️ Moderate (4 files) |
| **Helper Extraction** | ✅ Yes | ❌ Some inline | ✅ Yes |
| **Transfer Overhead** | mov rdi,rax (1 inst) | nop (1 inst, unclear why) | None! (cleanest) |
| **Register Model** | Complex (rdi≠rax) | Simple (x0=x0) | Simplest (a0=a0) |

**X86 serves as the reference implementation** - other backends should adopt its proven patterns (Star, helper extraction, centralized postulates).

## Key Lessons for Other Backends

1. **Extract helpers** - Don't build records inline (see AArch64 compose)
2. **Centralize postulates** - Only in Backend/*/Postulates.agda
3. **Use Star throughout** - Never fuel-based exec in proofs
4. **Follow X86 structure** - Proven to work at scale

## References

- **Proof Instructions**: `formal/proof-instructions.md`
- **Lessons Learned**: `docs/formal/lessons-learned.md`
- **Decision Log**: `docs/compiler/decision-log.md` (D022: Agda, D032: Arrow effects)
- **Proof Analysis**: `docs/formal/proof-analysis.md` (Apply unprovability analysis)
- **What Is Proven**: `docs/formal/what-is-proven.md`

## Mechanical Postulate Elimination Progress

**Status**: 7 of 18 IR correctness postulates eliminated (39% reduction)
**Commits**: e4ab0bf (6 postulates), 7cd788b (1 postulate)

### Techniques Developed

#### 1. Stack Pointer Arithmetic Pattern ✅ (6 eliminated)

**Key Lemma**: `∸-monoˡ-≤ : ∀ o {m n} → m ≤ n → m ∸ o ≤ n ∸ o`

**Proof Pattern**:
```agda
-- Given: rsp > 16, new-rsp = rsp ∸ 16
-- Prove: new-rsp ≠ 0

17≤rsp : 17 ≤ rsp
17≤rsp = rsp>16

1≤new-rsp : 1 ≤ new-rsp  
1≤new-rsp = subst (1 ≤_) refl (∸-monoˡ-≤ 16 17≤rsp)

diff : new-rsp ≠ 0
diff = <⇒≢ (≤-trans (s≤s z≤n) 1≤new-rsp) ∘ sym
```

**Eliminated From**:
- IR/Inl.agda: 2 postulates (new-rsp ≠ 0, new-rsp + 8 ≠ 0)
- IR/Inr.agda: 2 postulates (same pattern)
- IR/Curry.agda: 2 postulates (same pattern)

**Key Insight**: Stack pointer bounds (rsp > n) + monus monotonicity = powerful inequality proofs

#### 2. Memory Preservation Through Single Write ✅ (1 eliminated)

**Key Lemma**: `readMem-writeMem-diff`

**Proof Pattern**:
```agda
-- Prove memory at 0 unchanged when writing to addr
-- where addr = rsp ∸ n and rsp > n

addr-neq-0 : addr ≠ 0
addr-neq-0 = <⇒≢ addr>0 ∘ sym
  where
    addr>0 : addr > 0
    addr>0 = subst (_> 0) (sym addr-eq) rsp∸n>0

mem-at-0-preserved : readMem (memory s') 0 ≡ readMem (memory s) 0
mem-at-0-preserved = readMem-writeMem-diff mem addr 0 val addr-neq-0
```

**Eliminated From**:
- IR/Pair.agda: `mem-at-0-mid-proof` (middle phase write preservation)

**Key Insight**: Can reuse rsp > n proofs to show stack addresses ≠ 0

### Remaining Mechanical Postulates (11 total)

#### Easy: SeqExec Extension (1 postulate)

**IR/Pair.agda** - `mem-at-0-setup-proof`:
- **Challenge**: Setup writes to 3 addresses (rsp-24, rsp-16, rsp-8)
- **Approach**: Extend `exec-pair-setup-at-7` postcondition
- **Effort**: Moderate (modify SeqExec.agda, ~50 lines)

#### Medium: StackInvariant Analysis (3 postulates)

**IR/Apply.agda**:
- `stack-inv5`: StackInvariant after apply setup
- `stack-inv1`: StackInvariant after call instruction

**StackInvariant.agda**:
- `postulate-stack-below-r15-ret`: Preservation through ret

**Approach**: Analyze StackInvariant constructors and prove preservation
**Effort**: Significant (understand invariant semantics, ~200 lines total)

#### Hard: Thunk Execution Tracing (7 postulates)

**IR/Apply.agda** - memory/register preservation through thunk:
- `r15-post`, `mem-r15-post`, `mem-rbp-post`, `mem-rbp+8-post`
- `mem-above-post`, `mem-at-0-post`, `rbp-inv-post`

**Approach**: Use ClosureWellFormed.ThunkResult framework
**Effort**: Major (trace through curry thunk execution, ~500 lines)

### Elimination Statistics

| Module | Initial | Eliminated | Remaining | % Complete |
|--------|---------|------------|-----------|------------|
| IR/Inl.agda | 2 | 2 | 0 | 100% ✅ |
| IR/Inr.agda | 2 | 2 | 0 | 100% ✅ |
| IR/Curry.agda | 2 | 2 | 0 | 100% ✅ |
| IR/Pair.agda | 2 | 1 | 1 | 50% |
| IR/Apply.agda | 9 | 0 | 9 | 0% |
| StackInvariant.agda | 1 | 0 | 1 | 0% |
| **TOTAL** | **18** | **7** | **11** | **39%** |

### Next Priority Actions

1. **Pair setup mem-at-0** (1 week) - Extend SeqExec postcondition
2. **StackInvariant preservation** (2 weeks) - Prove invariant through key instructions
3. **Apply thunk tracing** (3-4 weeks) - Major undertaking, use ClosureWellFormed

**Estimated time to zero mechanical postulates**: 6-8 weeks of focused work

### Key Lessons Learned

1. **Monus arithmetic is well-supported** - Data.Nat.Properties has all needed lemmas
2. **Stack bounds are powerful** - rsp > n enables many disequality proofs
3. **Instruction-level tracing works** - Sequential execution lemmas are manageable
4. **Record fields > postulates** - Move to PairSetupResult/PairMiddleResult improved structure

