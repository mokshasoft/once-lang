# Proof Instructions for Once Formal Verification

## The Prime Directive: No Shortcuts

**The goal is complete end-to-end verification with zero unjustified postulates.**

Every shortcut, workaround, or "temporary" postulate is technical debt that
compounds. What seems like a small compromise inevitably leads to more
postulates, spec gaps, and eventually an unverifiable system.

### The Fundamental Principle

> **If the specification cannot be proven, fix the implementation.**

When a proof fails, there are only two valid responses:
1. **The implementation is wrong** → Fix the code generator
2. **The specification is wrong** → Fix the specification

There is NO third option of "add a postulate and move on."

### Example: Register Preservation

If IRStarResult requires x20/x21 preservation but pair/curry/case modify them:

❌ **WRONG approach (shortcut):**
- Add postulates claiming preservation (they're false)
- Remove preservation from IRStarResult (hides the problem)
- Add "preconditions" that make false claims trivially true

✅ **RIGHT approach (principled):**
- Recognize the code generator violates the ARM64 ABI
- Fix CodeGen.agda to save/restore x20/x21 properly
- The proofs then work because the claims are TRUE

### Why This Matters

Shortcuts accumulate:
1. One postulate leads to another to work around its limitations
2. Proof complexity grows as workarounds interact
3. Eventually the system becomes unverifiable
4. The original "small" shortcut caused systemic failure

The principled approach pays off:
1. Each proof is solid because it proves true facts
2. Proofs compose cleanly
3. The system remains verifiable as it grows
4. Full E2E verification becomes achievable

## The Axiom Hierarchy: Only CPU Semantics Are Axioms

The ONLY true axioms in the system are about CPU instruction semantics — how
each x86 instruction modifies State (registers, memory, flags). Everything
else is a theorem to be proven.

**Layer 1: CPU Instruction Semantics (AXIOMS)**
- How `mov`, `push`, `call`, `ret`, `sub`, `add` modify State
- These define the machine model and cannot be simplified further

**Layer 2: Allocator Semantics (THEOREMS from Layer 1)**
- `encode-injective`: different values get different addresses
- `encode-in-heap-sem`: allocated values are in the heap region
- `valid-from-encode`: encode establishes validity
- `valid-addr-is-encode`: validity implies encode address
- These are properties of the allocator IMPLEMENTATION, provable from how
  allocation instructions (sub rsp, mov) modify memory

**Layer 3: Compiler Correctness (THEOREMS from Layers 1+2)**
- All IR generator proofs (curry, apply, compose, pair, case, etc.)
- All capacity, memory preservation, and register preservation lemmas
- Zero postulates — everything follows from the instruction semantics

**Absurd Reasoning (NEVER acceptable):**
Claiming that any Layer 2 or Layer 3 property is an "axiom" or "must stay
as a postulate" is absurd reasoning. If the generators are mathematically
sound and the implementation is correct, a proof MUST exist. Any gap
indicates incomplete proof machinery, not a fundamental limitation.

Current status: Layer 2 postulates in MemoryValid.agda are placeholders
for AllocatorSemantics proofs. They will be eliminated when the allocator
module is implemented. They are NOT axioms — they are unfinished theorems.

## Core Principles

### 1. No Inline Postulates
Every `postulate` block in proof files (Correct.agda, MutualIR.agda, etc.)
represents unfinished work. The goal is zero inline postulates.

If you cannot prove something:
- **Change the implementation** - make the code do what the spec says
- **Change the abstraction** - add preconditions, strengthen invariants
- **Do not add postulates** - postulates hide bugs and block verification

### 2. Semantic Axioms in Postulates.agda
The only acceptable postulates are semantic axioms in `Once/Postulates.agda`:
- `encode` function and its properties
- Memory model axioms (if any remain unproven)

These are clearly identified, centralized, and auditable.

### 3. Star-Based Proofs (Mandatory)
**All proofs must use the Star relation.** Refactor any fuel-based proofs to Star.

Fuel-based proofs (exec, exec-chain, step counting) inevitably lead to
unprovable lemmas and postulates. Star-based proofs compose cleanly and
the stars always align.

Use these combinators:
- `star-single` - lift a single step to Star
- `star-trans` - compose two Star proofs
- `star-stepN` - chain N steps directly
- `⟨ h , step ⟩◅ rest` - build step chains

Star eliminates fuel arithmetic entirely. No step counting, no fuel
management, just transitivity.

### 4. No Meta-Comments
Do not write comments like:
- "no postulates!"
- "postulate-free"
- "PROVEN (not postulated!)"

The code speaks for itself. If there are no postulates, that's visible.

## Verification Philosophy

### What We're Proving: Compiler Correctness for Arbitrary Programs

Once verification proves **compiler correctness**, not program correctness.

**The Goal:**
> For ANY Once program that type-checks, prove the compiled machine code faithfully
> implements the IR semantics.

**Compiler Correctness** (What we prove):
- The Once compiler correctly translates programs to machine code
- For ANY combination of IR generators, the composition is correct
- If your Once program type-checks, it compiles correctly

**Program Correctness** (NOT our job):
- Whether a specific Once program produces the right answer
- Example: "This sorting algorithm actually sorts"
- That's about the program's logic, not the compiler

### Compositional Verification: Prove Once, Use Everywhere

**What this means:**
- ✓ Prove EACH IR generator correct in isolation (id, compose, curry, apply, etc.)
- ✓ Prove generators COMPOSE correctly (run-ir-star-at-offset in MutualIR.agda)
- ✓ Result: ANY program using ANY COMBINATION of generators compiles correctly

**Why this works:**
```
Prove: curry is correct
Prove: apply is correct
Prove: compose is correct
Prove: They compose correctly
→ ANY program using ANY combination of curry, apply, compose, etc. compiles correctly
```

This is the difference between:
- Verifying "hello world compiles" vs "the compiler works for all programs"
- Proving "2+2=4" vs "addition is commutative"
- Testing one example vs verifying the general case

**Whole-program proofs are validation:**
End-to-end proofs like `test-curry-apply` demonstrate the system works,
but they don't prove compiler correctness for arbitrary programs.
Only modular proofs with composition do that.

**Implication for postulate elimination:**
When eliminating postulates (like apply-produces-result), we must eliminate them from
the MODULAR mutual block (run-ir-star-at-offset), not just from example programs.
The modular layer is where we prove arbitrary program correctness.

## Layered Proof Architecture: Generator Proofs vs Edge Proofs

**Critical Principle**: The Once compiler proves generators correct for Once-generated code.
External code interactions (FFI) require programmer proofs at the boundary.

### What This Means

1. **Generator Correctness (Our Job)**:
   - Prove curry produces valid closures
   - Prove apply correctly invokes closures produced by curry
   - Prove compose/pair/case preserve closure validity
   - Result: ANY closed Once program compiles correctly

2. **FFI Boundary Proofs (Programmer's Job)**:
   - If calling external C functions that return closures
   - If exposing Once closures to external code
   - The programmer provides ClosureWellFormed proofs at the boundary

### Why Postulates Are Elimination Targets

When you see postulates like `apply-produces-result`:
- ❌ WRONG: "This is a justified model axiom because closures could come from anywhere"
- ✅ RIGHT: "This should be eliminated for closed programs via ClosureEntry tracking"

The infrastructure exists (ClosureEntry, ClosureWellFormed, run-apply-with-wf) to eliminate
these postulates. Comments suggesting they're permanent axioms lead us down wrong paths.

### Common Misunderstanding Pattern

This mistake has occurred 10+ times in our codebase:

1. Someone sees apply can't prove closure validity modularly
2. They write "this postulate is justified because closures could be external"
3. This framing makes it seem like the postulate is permanent
4. We stop working on elimination and add more postulates
5. Eventually we rediscover the layered architecture and fix it

**The fix**: Comments should always emphasize the ELIMINATION PATH, not justify permanence.

## Proof Patterns

### Single-Instruction IR (id, terminal, fold, unfold, arr)
Use `star-single`:
```agda
ir-star = star-single h-false step-eq
```

### Multi-Instruction IR (inl, inr, fst, snd)
Use `star-stepN`:
```agda
star-proof = star-step4 h-false step1 h1 step2 h2 step3 h3 step4
```

### Composite IR (compose, pair, case, curry)
Use recursive calls + `star-trans`:
```agda
let (s1 , res-f) = run-ir-star-at-offset f ...
    (s2 , res-g) = run-ir-star-at-offset g ...
in star-trans (ir-star res-f) (ir-star res-g)
```

## Git Workflow

Run git commands separately:
```bash
git add <files>
git commit -m "message"
git push origin master
```

**Commit often.** Small, focused commits are easier to review and bisect.

## Architecture

Follow the patterns established for x86-64. When adding new backends or proof
modules, study the x86-64 structure first and maintain consistency.

### Backend Proof Architecture: Stateful Proofs for Zero Postulates

The x86-64 backend uses **stateful proofs** to eliminate ALL encoding postulates.
This is the RECOMMENDED approach for all backend verification.

**Two Result Types**:

1. **IRStarResult** (non-stateful, used internally):
   ```agda
   record IRStarResult where
     field
       ir-rax : readReg (regs s') rax ≡ encode (eval ir x)  -- Depends on encode!
   ```

2. **IRStarResultS** (stateful, used by external callers):
   ```agda
   record IRStarResultS where
     field
       ir-rax-s : readReg (regs s') rax ≡ addr-out  -- Explicit address, NO encode!
   ```

**Why Stateful Proofs Win**:

- **Zero encoding postulates**: Non-stateful proofs require 10+ postulates about
  `encode` behavior (encode-pair-fst/snd, encode-inl/inr-*, encode-closure-*)
- **Explicit memory layout**: Validity predicates (`PairAtS`, `InlAtS`, `InrAtS`,
  `ClosureAtS`) prove actual memory structure instead of assuming it
- **Clean composition**: Use `convert-to-stateful` to bridge internal (non-stateful)
  to external (stateful) interfaces

**Pattern**:
```agda
run-ir-star-s : ... → ∃[ s' ] IRStarResultS ir prog s s' addr-out offset
run-ir-star-s ... =
  let (s' , res) = run-ir-star ...  -- Non-stateful proof
      res-s = convert-to-stateful ir prog s s' x offset res  -- Convert
  in s' , subst (λ addr → IRStarResultS ...) enc-eq res-s
```

**Result**: Complete E2E proofs with ZERO encoding postulates.

**Reference**: See `Once/Backend/X86/Correct/StarBase.agda` for implementation,
`Once/Postulates.agda:252-340` for documentation of eliminated postulates.

**Historical Note**: x86-64 evolved from RISC-V's non-stateful approach specifically
to eliminate encoding postulates. RISC-V backend still uses non-stateful proofs
and requires all encoding postulates.

## Type Checking

For single file type checks:
```bash
timeout 300 make agda MODULE=Once/Backend/X86/Correct/IR/Pair.agda
```

For full type checks:
```bash
timeout 900 make x86
```

**If type checking times out, refactor.** Long compile times indicate the
proof structure needs simplification. Split large modules, reduce dependencies,
or restructure proofs to compile faster.

## MAlonzo Extraction

The verified compiler components are extracted to Haskell via Agda's MAlonzo backend:

```bash
cd formal

# Extract entire compiler (IR, Surface, Optimizer, Type system)
make malonzo

# Extract specific components:
make malonzo-core        # Type, IR, Semantics, Memory
make malonzo-typecheck   # Verified type checker
make malonzo-codegen     # Backend code generators (X86, AArch64, RiscV64)
```

### What Gets Extracted

The `make malonzo` target extracts and copies to `../compiler/src/MAlonzo/Code/Once/`:
- **Core IR**: All 13 generators (id, compose, fst, snd, pair, inl, inr, case, terminal, initial, curry, apply, fold, unfold, arr)
- **Surface IR**: Surface language with Let/Prim constructs
- **Desugar**: Surface → Core IR transformation
- **Optimizer**: Pattern-based optimizations (~190KB of optimization rules)
- **Type System**: QTT-based type definitions
- **Semantics**: Denotational semantics and encoding

### Entry Point

```haskell
-- Main compilation function in MAlonzo.Code.Once.Compile
compile :: SurfaceIR A B → IR ∞ A B
compile = optimize . desugar
```

### Workflow

1. **Develop in Agda**: Write verified code in `formal/Once/*.agda`
2. **Type-check**: `make x86` or `make riscv` to verify proofs
3. **Extract**: `make malonzo` to generate Haskell modules
4. **Integrate**: Extracted modules are automatically copied to `compiler/src/MAlonzo/`

The extracted Haskell code is the **single source of truth** for the compiler's core logic.
All IR generators, optimizations, and transformations come from verified Agda code.

## When Stuck

If a proof seems impossible:
1. Check preconditions - do you need stronger invariants?
2. Check the abstraction - is the type signature correct?
3. Check the semantics - does the code actually do what you're proving?
4. Ask: "Am I proving this for arbitrary programs, or just this example?"
   - If just an example, extend to modular proof
   - Examples are good for validation, but insufficient for verification

Never add a postulate to "get past" a difficult proof.

## Handling Timeouts

**If type checking times out, the solution is NEVER to replace proofs with postulates.**

Proofs can be restructured, improved, or extracted to separate modules.
But they must never be deleted and replaced with postulates - that moves us
away from the goal, not toward it.

When a module times out:

1. **Identify the bottleneck** - usually complex arithmetic or deeply nested terms
2. **Extract to a separate module** - move the slow-compiling code to its own file
3. **Restructure the proof** - find a cleaner approach that avoids the complexity
4. **Split large where blocks** - Agda type-checks where clauses together

### Arithmetic Does Not Belong in Star Proofs

Complex arithmetic lemmas like:
```agda
pc-step n = trans (+-assoc ...) (trans (cong ...) (trans ...))
```

These indicate a design problem, not a proof problem. Star-based proofs
should compose cleanly without arithmetic gymnastics. If you need complex
PC arithmetic, consider:

- Defining PC offsets as compile-time constants
- Using helper records that track PC symbolically
- Restructuring the proof to avoid manual arithmetic

### What you must NEVER do:
- Delete proven step executions and replace with postulates
- Delete proven preservation lemmas and replace with postulates
- Remove working proofs to "simplify" - that's not simplification, that's regression

### What you CAN do:
- Rewrite proofs to be cleaner or faster to compile
- Extract proofs to separate modules
- Restructure proof architecture for better composition
- Replace complex arithmetic with cleaner abstractions

The goal is zero unjustified postulates. Every proof deletion moves us
further from that goal. Every proof improvement or restructuring that
maintains correctness moves us closer.
