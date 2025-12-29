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

### Arbitrary Programs, Not Toy Examples

The goal of Once verification is to prove that **arbitrary Once programs** compile correctly,
not just specific example programs.

**What this means:**
- ✓ Prove each IR generator correct in ISOLATION (modular proofs)
- ✓ Prove generators COMPOSE correctly (run-ir-star-at-offset in MutualIR.agda)
- ✓ Enable verification of ANY program via compositional reasoning
- ✗ Do NOT only prove specific whole-program examples (E2E-Trace style)

**Why this matters:**
Whole-program proofs like `test-curry-apply` only verify that one specific expression
works. They do not prove that curry and apply compose correctly in general.

Modular proofs prove that no matter how you combine IR generators, the result is correct.
This is the difference between:
- Verifying "hello world works" vs "all C programs work"
- Proving "2+2=4" vs "addition is commutative"

**Implication for postulate elimination:**
When eliminating postulates (like apply-produces-result), we must eliminate them from
the MODULAR mutual block (run-ir-star-at-offset), not just from example programs.

Whole-program proofs serve as validation and demonstration, but the real verification
happens in the modular layer.

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

Follow the patterns established for x86. When adding new backends or proof
modules, study the x86 structure first and maintain consistency.

## Type Checking

For single file type checks:
```bash
timeout 300 make agda MODULE=Once/Backend/X86/Correct/IR/Pair
```

For full type checks:
```bash
timeout 900 make x86
```

**If type checking times out, refactor.** Long compile times indicate the
proof structure needs simplification. Split large modules, reduce dependencies,
or restructure proofs to compile faster.

## When Stuck

If a proof seems impossible:
1. Check preconditions - do you need stronger invariants?
2. Check the abstraction - is the type signature correct?
3. Check the semantics - does the code actually do what you're proving?
4. Ask: "Am I proving this for arbitrary programs, or just this example?"
   - If just an example, extend to modular proof
   - Examples are good for validation, but insufficient for verification

Never add a postulate to "get past" a difficult proof.
