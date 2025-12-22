# Proof Instructions for Once X86 Backend

## Core Principles

### 1. No Inline Postulates
Every `postulate` block in proof files (Correct.agda, MutualIR.agda, etc.)
represents unfinished work. The goal is zero inline postulates.

If you cannot prove something:
- **Change the abstraction** - add preconditions, strengthen invariants
- **Do not add postulates** - postulates hide bugs

### 2. Semantic Axioms in Postulates.agda
The only acceptable postulates are semantic axioms in `Once/Postulates.agda`:
- `encode` function and its properties
- Memory model axioms (if any remain unproven)

These are clearly identified, centralized, and auditable.

### 3. Star-Based Proofs
Use the Star relation for execution proofs:
- `star-single` - lift a single step to Star
- `star-trans` - compose two Star proofs
- `star-stepN` - chain N steps directly
- `⟨ h , step ⟩◅ rest` - build step chains

Star eliminates fuel arithmetic entirely.

### 4. No Meta-Comments
Do not write comments like:
- "no postulates!"
- "postulate-free"
- "PROVEN (not postulated!)"

The code speaks for itself. If there are no postulates, that's visible.

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

## When Stuck

If a proof seems impossible:
1. Check preconditions - do you need stronger invariants?
2. Check the abstraction - is the type signature correct?
3. Check the semantics - does the code actually do what you're proving?

Never add a postulate to "get past" a difficult proof.
