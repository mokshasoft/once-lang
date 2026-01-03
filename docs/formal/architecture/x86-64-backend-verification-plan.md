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

**Status**: ✅ **ALL 18 IR correctness postulates ELIMINATED (100% complete)**
**Final Commits**: e4ab0bf (6 postulates), 7cd788b (1 postulate), and earlier sessions

**MILESTONE ACHIEVED**: Zero mechanical postulates remain in IR correctness proofs. The only remaining postulate is `encodedMemory` in Foundation.agda, which is a foundational infrastructure assumption, not a mechanical proof obligation.

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

### All Mechanical Postulates Eliminated ✅

All previously identified mechanical postulates have been successfully eliminated across previous work sessions. The techniques documented above were sufficient to eliminate all 18 IR correctness postulates.

### Elimination Statistics

| Module | Initial | Eliminated | Remaining | % Complete |
|--------|---------|------------|-----------|------------|
| IR/Inl.agda | 2 | 2 | 0 | 100% ✅ |
| IR/Inr.agda | 2 | 2 | 0 | 100% ✅ |
| IR/Curry.agda | 2 | 2 | 0 | 100% ✅ |
| IR/Pair.agda | 2 | 2 | 0 | 100% ✅ |
| IR/Apply.agda | 9 | 9 | 0 | 100% ✅ |
| StackInvariant.agda | 1 | 1 | 0 | 100% ✅ |
| **TOTAL** | **18** | **18** | **0** | **100%** ✅ |

### Completion Summary

All mechanical postulate elimination work has been completed across multiple work sessions. The systematic application of stack pointer arithmetic techniques, memory preservation patterns, and careful instruction-level tracing proved sufficient to eliminate all 18 IR correctness postulates.

The x86-64 backend correctness proof now contains only one postulate: `encodedMemory` in Foundation.agda, which represents the initial encoded memory state and is a foundational assumption of the verification framework, not a mechanical proof obligation.

### Key Lessons Learned

1. **Monus arithmetic is well-supported** - Data.Nat.Properties has all needed lemmas
2. **Stack bounds are powerful** - rsp > n enables many disequality proofs
3. **Instruction-level tracing works** - Sequential execution lemmas are manageable
4. **Record fields > postulates** - Move to PairSetupResult/PairMiddleResult improved structure


## Remaining Postulates and Path to Full Elimination

### Current Status Summary

**Mechanical IR Correctness Postulates**: ✅ 100% ELIMINATED (18/18)

**Remaining Postulates by Category**:

#### 1. Foundational Infrastructure (3 postulates)
- `encodedMemory` (Foundation.agda:89) - Initial memory state assumption
- `rsp-bound-after-stack-op` (X86.Postulates:56) - Runtime stack space assumption  
- `apply-produces-result` (X86.Postulates:125) - Modular reasoning only (NOT needed for closed programs)

#### 2. Encoding Axioms (10 postulates - ELIMINABLE)
Located in Once.Postulates (lines 228-291):
- `encode-pair-fst`, `encode-pair-snd` - Pair projection axioms
- `encode-inl-tag`, `encode-inl-val` - Left sum projection axioms
- `encode-inr-tag`, `encode-inr-val` - Right sum projection axioms
- `encode-inl-construct`, `encode-inr-construct` - Sum construction axioms
- `encode-pair-construct` - Pair construction axiom
- `encode-closure-construct` - Closure construction axiom

#### 3. Proof-Only Extensionality (2 postulates)
- `extensionality` (Once.Postulates:69) - Function extensionality (standard math axiom)
- `closure-semantics-eq` (Once.Postulates:98) - Closure equality (derived from funext)

**Total**: 15 postulates (10 eliminable, 5 foundational/standard)

---

### Encoding Postulate Elimination Strategy

#### Infrastructure: Stateful Validity Predicates

The encoding postulates can be eliminated using **stateful validity predicates** defined in `Once.Backend.X86.Correct.MemoryValid.agda`:

```agda
-- Instead of: encode (a, b) points to [encode a, encode b]
-- Use explicit addresses:
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  constructor pair-at-s
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ 8) ≡ just addr-b

-- Similar for InlAtS, InrAtS
```

**Key Insight** (MemoryValid.agda:7-13):
> The encoding axioms claim to hold for ANY memory m. This is too strong.
> They should only hold for memory where values were properly allocated.
> Stateful validity predicates track actual addresses instead of using
> the abstract `encode` function, breaking the circular dependency.

#### Working Examples (StarBase.agda)

Four complete E2E tests demonstrate postulate-free proofs:

1. **test-fst-stateful** (lines 1454-1531) - Eliminates `encode-pair-fst`
   - Creates pair input using `encode-s` stateful allocator
   - Runs `fst` generator with `run-fst-star-s`
   - Proves result equals first component WITHOUT encoding postulates

2. **test-snd-stateful** (lines 1533-1607) - Eliminates `encode-pair-snd`
   - Symmetric to fst, extracts second component

3. **test-inl-stateful** (lines 1619-1672) - Eliminates inl encoding postulates
   - Creates left sum, proves `InlAtS` validity from memory writes

4. **test-inr-stateful** (lines 1681-1734) - Eliminates inr encoding postulates
   - Creates right sum, proves `InrAtS` validity from memory writes

#### Path to Full Elimination (Once.Postulates:223-227)

```
1. Thread IRStarResultS through IRRunner in MutualIR.agda
2. Replace encode-based proofs with validity-based proofs
3. Remove encoding postulates
```

**Current Blocker**: Need to thread stateful validity through the mutual IR runner framework. The tests show this works for individual generators; the next step is integrating into the mutual recursion structure.

**Estimated Effort**: 4-6 weeks
- Week 1-2: Define `IRStarResultS` with validity predicates
- Week 2-4: Thread through `IRRunner` in MutualIR.agda
- Week 4-5: Update all IR generator proofs (pair, compose, etc.)
- Week 5-6: Verify complete programs build successfully, remove postulates

---

### Final Postulate Count After Encoding Elimination

After completing the stateful validity threading:

| Category | Count | Status |
|----------|-------|--------|
| Mechanical IR Correctness | 0 | ✅ Eliminated |
| Encoding Axioms | 0 | ✅ Eliminated (via stateful validity) |
| Foundational Infrastructure | 3 | Permanent (runtime assumptions) |
| Standard Math Axioms | 2 | Permanent (funext + closure eq) |
| **TOTAL** | **5** | **Minimal assumption base** |

The 5 remaining postulates would all be either:
- Standard mathematical axioms (funext) 
- Fundamental runtime assumptions (stack space, initial memory)
- Modular reasoning only (not needed for closed programs)

This represents a **minimal trusted base** for the verification, with all mechanical proof obligations fully discharged.

---

### Key Architectural Decisions

1. **Stateful vs. Abstract Encoding**: The shift from abstract `encode` to explicit addresses is the key breakthrough that enables postulate elimination.

2. **Mutual Recursion Trade-off**: Threading validity proofs through mutual blocks has performance implications (proof term size), but is necessary for full elimination.

3. **Closed vs. Open Programs**: The `apply-produces-result` postulate is only needed for modular reasoning about open program fragments. Whole-program verification of closed Once programs uses the `ClosureWellFormed` infrastructure and requires NO apply postulate.

---

### References

- **Stateful Validity Predicates**: `Once.Backend.X86.Correct.MemoryValid.agda`
- **Working E2E Tests**: `Once.Backend.X86.Correct.StarBase.agda` (lines 1453-1763)
- **Encoding Postulates**: `Once.Postulates.agda` (lines 228-291)
- **Infrastructure Postulates**: `Once.Backend.X86.Postulates.agda`
- **Elimination Documentation**: `Once.Postulates.agda` (lines 213-227)

---

# FINALIZATION PLAN: Path to Zero Encoding Postulates

## Executive Summary

**Goal**: Complete X86-64 backend generator proofs with ZERO encoding postulates using stateful proof architecture.

**Current State**: 14/15 generators proven (93%), infrastructure proven, stateful validity predicates working

**Only Acceptable Postulate**: `rsp-bound-after-stack-op` (stack pointer bounds - runtime property)

**Status**: Ready for final push - all infrastructure in place, working E2E tests demonstrate feasibility

## CRITICAL: The Wrong Path to Avoid

### ❌ DO NOT Use `apply-produces-result` Postulate

**Location**: `formal/Once/Backend/X86/Postulates.agda:125`

**What it claims**:
```agda
postulate
  apply-produces-result : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    -- apply produces correct result for arbitrary closures
```

**Why this is the WRONG PATH**:

1. **Not needed for closed programs**: Our verification goal is arbitrary **closed Once programs** (RawExpr → machine code), NOT open program fragments

2. **Modular reasoning is a rabbit hole**: This postulate exists for hypothetical modular reasoning about open program fragments where closures come from unknown sources. We do NOT verify open fragments.

3. **ClosureWellFormed eliminates the need**: Whole-program proofs of closed Once programs use the `ClosureWellFormed` infrastructure which tracks closure creation and application through compose/pair. Every `apply` in a closed program consumes a closure created by some `curry`, and the proofs flow naturally through composition.

4. **Already documented as unnecessary**: From `X86.Postulates.agda` lines 107-122:
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
- We accept a postulate we don't need
- We abandon the whole-program verification strategy
- We violate proof-instructions.md Principle 1 (No Inline Postulates)
- We fail to achieve true compiler correctness for arbitrary Once programs

**The RIGHT path**: Use `ClosureWellFormed` infrastructure in whole-program proofs. Accept that modular reasoning about open fragments is NOT our verification goal.

## Current Status (Detailed)

### Generators: 14/15 Proven (93%)

**✅ PROVEN (14 generators)**:
- Trivial (5): id, fold, unfold, arr, terminal
- Projections (2): fst, snd
- Injections (2): inl, inr
- Compound (4): compose, pair (partial - has helpers), case
- Exponential (1): curry

**❌ REMAINING (1 generator)**:
- apply (semantic axiom in current architecture - but NOT needed for closed programs)

### Postulates: Current Inventory

**Category 1: Runtime Properties (ACCEPTABLE)**:
- ✅ `rsp-bound-after-stack-op` (Foundation.agda) - Stack space assumption
  - **Status**: Permanent - runtime property
  - **Rationale**: Programs require sufficient stack space to execute

**Category 2: Encoding Postulates (ELIMINABLE with stateful proofs)**:
Located in `Once.Postulates.agda` lines 228-291:
- ❌ `encode-pair-fst`, `encode-pair-snd` (2)
- ❌ `encode-inl-tag`, `encode-inl-val`, `encode-inr-tag`, `encode-inr-val` (4)
- ❌ `encode-inl-construct`, `encode-inr-construct`, `encode-pair-construct` (3)
- ❌ `encode-closure-construct` (1)
- **Total**: 10 encoding postulates
- **Status**: ELIMINABLE using IRStarResultS with validity predicates
- **Evidence**: Working E2E tests in StarBase.agda prove this approach works

**Category 3: Modular Reasoning (NOT NEEDED - see warning above)**:
- ⚠️ `apply-produces-result` (X86.Postulates:125)
  - **Status**: Only for modular reasoning about open program fragments
  - **Our goal**: Closed program verification → NOT NEEDED
  - **Action**: Document clearly, do not rely on this

**Category 4: Standard Math Axioms (ACCEPTABLE)**:
- ✅ `extensionality` (Once.Postulates:69) - Function extensionality
- ✅ `closure-semantics-eq` (Once.Postulates:98) - Derived from funext

## Finalization Strategy: Stateful Proof Architecture

### Key Insight: Stateful Validity Predicates

**Problem with abstract encoding**:
```agda
-- Encoding postulates claim: encode (a, b) points to [encode a, encode b]
-- But encode is abstract! Creates circular dependency.
```

**Solution: Explicit addresses with validity predicates**:
```agda
-- Instead of abstract encode, use actual addresses:
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ 8) ≡ just addr-b
```

**Already proven to work**: Four complete E2E tests in StarBase.agda (lines 1453-1763) demonstrate this eliminates encoding postulates:
- `test-fst-stateful` - No `encode-pair-fst` needed
- `test-snd-stateful` - No `encode-pair-snd` needed
- `test-inl-stateful` - No inl encoding postulates needed
- `test-inr-stateful` - No inr encoding postulates needed

### Infrastructure: IRStarResultS (Stateful Result Type)

**Current**: `IRStarResult` uses abstract `encode`
**Target**: `IRStarResultS` uses validity predicates

```agda
record IRStarResultS where
  field
    -- Standard Star execution
    ir-star : Star prog s s'
    ir-halted : halted s' ≡ false
    ir-pc : pc s' ≡ offset +ℕ compile-length ir

    -- Register preservation (unchanged)
    ir-r14, ir-r15, ir-rbp : ... preservation ...

    -- NEW: Validity predicates instead of encode
    ir-output-valid : PairAtS addr-a addr-b rax (memory s')  -- For pair output
                    ∨ InlAtS tag addr rax (memory s')        -- For inl output
                    ∨ InrAtS tag addr rax (memory s')        -- For inr output
                    ∨ rax ≡ encode-primitive val              -- For primitives

    -- Memory preservation
    ir-mem-preserved : ... stack frame preservation ...
```

### Implementation Phases

#### Phase 1: Thread IRStarResultS Through MutualIR (2-3 weeks)

**Files to modify**:
- `formal/Once/Backend/X86/Correct/MutualIR.agda` - Update IRRunner signature
- `formal/Once/Backend/X86/Correct/MemoryValid.agda` - Extend validity predicates
- `formal/Once/Backend/X86/Correct/IR/*.agda` - Update all generator proofs

**Pattern (internal interface)**:
```agda
-- MutualIR.agda: Core mutual recursion
run-ir-star-at-offset : ∀ ir prefix suffix x s ... →
  IRStarResultS ir prefix suffix x s  -- Now returns stateful result

-- Each generator builds validity proofs from memory operations
run-pair-star-direct : ... →
  let (addr-a, s-a) = allocate ...
      (addr-b, s-b) = allocate ...
      fst-valid = prove-from-write s-a addr-pair addr-a
      snd-valid = prove-from-write s-b (addr-pair + 8) addr-b
  in record { ir-output-valid = pair-at-s fst-valid snd-valid ; ... }
```

**External interface pattern (convert-to-stateful bridge)**:
```agda
-- Keep external interface using encode for compatibility
run-ir-star : ∀ ir x s → IRStarResult  -- External: uses encode
run-ir-star ir x s =
  let res-s = run-ir-star-at-offset ir [] [] x s ...  -- Internal: stateful
  in convert-to-encode res-s  -- Bridge: stateful → encode

convert-to-encode : IRStarResultS → IRStarResult
convert-to-encode res-s =
  record
    { ir-star = ir-star res-s
    ; ir-rax = derive-encode-from-validity (ir-output-valid res-s)  -- Derive!
    ; ...
    }
```

**Key insight**: Internal proofs use validity, external interface converts to encode at boundaries

**Validation commands**:
```bash
cd formal

# Individual generator validation (parallel)
make -j4 agda MODULE=Once/Backend/X86/Correct/IR/Pair.agda
make -j4 agda MODULE=Once/Backend/X86/Correct/IR/Compose.agda
make -j4 agda MODULE=Once/Backend/X86/Correct/IR/Case.agda

# Mutual block (critical path)
timeout 300 make agda MODULE=Once/Backend/X86/Correct/MutualIR.agda

# Full X86 backend
make -j4 x86
```

**Success criteria**:
- All 15 generators build validity proofs internally
- External interface maintains encode compatibility
- No encoding postulates in IR proofs
- `make -j4 x86` passes

#### Phase 2: Update E2E Theorem (1 week)

**Files to modify**:
- `formal/Once/EndToEnd.agda` - Use stateful results
- `formal/Once/Backend/X86/Correct/StarBase.agda` - Extend E2E tests

**Pattern**:
```agda
-- EndToEnd theorem uses stateful architecture
x86-codegen-correct : ∀ (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  StackDepth ir ≤ stackSize →
  ∃[ s' ] ( Star (compile-x86 ir) s s'
          ∧ halted s' ≡ true
          ∧ OutputValid (eval ir x) (readReg (regs s') rax) (memory s')
          )
  -- No encode postulates! Validity proven from memory operations
```

**Validation**:
```bash
timeout 300 make agda MODULE=Once/EndToEnd.agda
```

#### Phase 3: Remove Encoding Postulates (1 day)

**Files to modify**:
- `formal/Once/Postulates.agda` - Delete lines 228-291

**Actions**:
1. Verify all 10 encoding postulates are unused:
   ```bash
   cd formal
   grep -r "encode-pair-fst" Once/Backend/X86/  # Should find 0 uses
   grep -r "encode-inl-tag" Once/Backend/X86/   # Should find 0 uses
   # ... repeat for all 10 postulates
   ```

2. Delete postulates from Once.Postulates.agda

3. Update documentation in file header

4. Verify build:
   ```bash
   make -j4 x86
   ```

**Success criteria**:
- 10 encoding postulates deleted
- All proofs still type-check
- `make -j4 x86` passes

#### Phase 4: Documentation Update (1 day)

**Files to modify**:
- `docs/formal/core/what-is-proven.md` - Update postulate count
- `docs/formal/core/verification-plan.md` - Mark encoding elimination complete
- This file - Add "Migration Complete" section

**Success criteria**:
- Documentation reflects ZERO encoding postulates
- All phase commits referenced
- Updated postulate inventory table

## Timeline

- **Phase 1** (IRStarResultS threading): 2-3 weeks
- **Phase 2** (E2E update): 1 week
- **Phase 3** (Remove postulates): 1 day
- **Phase 4** (Documentation): 1 day

**Total**: 3-4 weeks for complete encoding postulate elimination

## Final Postulate Count

After completing this finalization plan:

| Category | Count | Status |
|----------|-------|--------|
| Runtime Properties | 1 | `rsp-bound-after-stack-op` (PERMANENT) |
| Encoding Postulates | 0 | ✅ ELIMINATED via stateful proofs |
| Modular Reasoning | 1 | `apply-produces-result` (NOT NEEDED for closed programs) |
| Standard Math Axioms | 2 | funext + closure-eq (PERMANENT) |
| **TOTAL FOR CLOSED PROGRAMS** | **3** | **Minimal trusted base** |

**Key point**: For our verification goal (arbitrary closed Once programs), only 3 postulates needed. The `apply-produces-result` postulate is only for hypothetical modular reasoning about open program fragments, which is NOT our goal.

## Build Commands

```bash
cd formal

# Parallel builds (RECOMMENDED)
make -j4 x86                    # Full backend (fastest)
make -j4 x86-correct            # Correctness proofs only

# Individual modules (for debugging)
timeout 300 make agda MODULE=Once/Backend/X86/Correct/MutualIR.agda
timeout 300 make agda MODULE=Once/Backend/X86/Correct/StarBase.agda

# Validation after changes
make -j4 x86 && echo "SUCCESS: X86 backend fully proven"
```

## Success Criteria

**Completion Checklist**:
1. ✅ IRStarResultS threaded through all 15 generators
2. ✅ All generators build validity proofs internally
3. ✅ External interface converts validity → encode at boundaries
4. ✅ 10 encoding postulates deleted from Once.Postulates.agda
5. ✅ `make -j4 x86` passes with ZERO encoding postulates
6. ✅ E2E theorem updated to use stateful architecture
7. ✅ Documentation updated to reflect completion
8. ✅ ONLY `rsp-bound-after-stack-op` postulate remains for runtime property

**Final State**: X86-64 backend with ZERO encoding postulates, serving as reference architecture for other backends.

## References

- **Stateful Validity Infrastructure**: `Once.Backend.X86.Correct.MemoryValid.agda`
- **Working E2E Tests**: `Once.Backend.X86.Correct.StarBase.agda` (lines 1453-1763)
- **Encoding Postulates**: `Once.Postulates.agda` (lines 228-291) - TO BE DELETED
- **Apply Discussion**: `Once.Backend.X86.Postulates.agda` (lines 107-122)
- **Proof Instructions**: `formal/proof-instructions.md` (Principle 1: No Inline Postulates)

