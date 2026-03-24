# OCP-0004: Minimal-Trust Verification via Categorical Foundations

**Author:** [TBD]
**Status:** Draft
**Created:** 2026-03-10
**Depends-On:** OCP-0003 (Layered IR)

---

## Summary

Establish that Once programs can be formally verified with a **minimal trusted computing base (TCB)**: mathematics, hardware, and a tiny bootstrap normalizer (~50-100 lines). This is achieved by recognizing that the CCC IR (from OCP-0003) **is** category theory, not an implementation of it. Verification becomes checking conformance to mathematical definitions, reducing the software TCB from ~50,000 lines (typical proof assistant) to ~50-100 lines (bootstrap normalizer).

---

## The Bootstrap Tower (Overview)

The path from "trust only mathematics" to "fully verified Once" is a **bootstrap tower** where each level builds on the previous:

```
┌─────────────────────────────────────────────────────────────────┐
│                    THE BOOTSTRAP TOWER                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Level 0: Minimal CCC                                            │
│    IR: id, ∘, fst, snd, ⟨_,_⟩, inl, inr, [_,_], terminal, In, cata │
│    Verified by: Fixpoint property + mathematical theorems        │
│    TCB: Mathematics only (~0 lines of code)                      │
│                        ↓                                         │
│  Level 1: + Exponentials                                         │
│    IR: + curry, apply                                            │
│    Verified by: Level 0 normalizer                               │
│                        ↓                                         │
│  Level 2: + Full Recursion Schemes (= OCP-0003 IR)               │
│    IR: + ana, ν, guardedness checking                            │
│    Verified by: Level 1 normalizer                               │
│                        ↓                                         │
│  Level 3: Once Compiler                                          │
│    Full compiler: parser, type checker, elaborator, optimizer    │
│    Verified by: Level 2 normalizer (totality + consistency)      │
│                        ↓                                         │
│  Level 4: + Dependent Types                                      │
│    Proofs as programs, specifications as types                   │
│    Verified by: Extended normalizer (proof checking)             │
│                        ↓                                         │
│  Level 5: Fully Verified Once                                    │
│    Compiler with correctness proofs, self-hosting                │
│    Verified by: Itself (all proofs checked by normalizer)        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**Key insight**: Each level doesn't need to TRUST the previous level's normalizer — it is VERIFIED by it. Trust flows only from mathematics through the fixpoint property at Level 0.

**The end state**: Once + Dependent Types + TCB0 Normalizer = Fully verified language with trust only in math.

---

## The Bootstrap Tower (Detailed)

### How Lower Levels Verify Higher Levels

A crucial question: How can a Level 0 normalizer (which lacks curry/apply) verify a Level 1 normalizer (which uses curry/apply)?

**Answer**: Lower levels don't need higher-level OPERATIONS — they have them as DATA.

```
Level 0 has:                    Level 0 handles curry/apply as:
─────────────────               ─────────────────────────────────
id, ∘, fst, snd, ⟨_,_⟩          DATA tags in the term encoding
inl, inr, [_,_], terminal       Pattern matching via cata + [_,_]
In, cata                        Reduction rules as data transformations
```

The Level 1 normalizer is ENCODED as Level 0 data:

```
Level 1 term: curry f           Level 0 encoding:
                                In ∘ inr ∘ ... ∘ inl ∘ encode(f)
                                     ↑
                                     tag for "curry"
```

The Level 0 normalizer recognizes patterns in this encoded data:

```
Pattern: apply ∘ ⟨curry f, x⟩   (as encoded tags)
Action:  Return encoding of f ∘ ⟨id, x⟩
```

This is like writing a Python interpreter in C: C doesn't have Python features, but can simulate them by manipulating data.

### Level 0: Minimal CCC

**IR Operations:**
- Category: `id`, `_∘_`
- Products: `fst`, `snd`, `⟨_,_⟩`
- Coproducts: `inl`, `inr`, `[_,_]`
- Terminal: `terminal`
- Initial Algebras: `In`, `cata`

**Verification method**: Fixpoint property

```
Theorem (from MainTheorem.agda):
  In a simple system (confluent + terminating):

  fixpoint-implies-nf:
    If N(t) ⟶* t  (N achieves fixpoint on t)
    Then t is in normal form

  Proof:
    1. N produces normal forms (by construction of normalize-step)
    2. N(t) ⟶* t (given fixpoint)
    3. But normal forms can't reduce (nf-stable)
    4. Therefore t ≡ N(t), so t is normal

  nf-unique (via confluence):
    Normal forms are unique per equivalence class

  Combined insight:
    Fixpoint ⟹ normal form ⟹ unique ⟹ correct

Why the fixpoint matters:
  1. Running N on ⟦N⟧ and reaching fixpoint proves ⟦N⟧ is normal
  2. The encoding is verified by being normalized
  3. This is empirically testable (RunTest.agda)
```

**TCB**: Mathematics (categorical laws, Lambek's Lemma) + ~50-100 lines bootstrap code (or less with traces)

**Current status**: In development (`bootstrap-normalizer` branch)

### Level 1: CCC + Exponentials

**Additional IR Operations:**
- `curry : Term (A × B) C → Term A (B ⇒ C)`
- `apply : Term ((A ⇒ B) × A) B`

**Additional reduction rules:**
- `apply ∘ ⟨curry f, x⟩ ⟶ f ∘ ⟨id, x⟩` (β)
- `curry (apply ∘ ⟨f ∘ fst, snd⟩) ⟶ f` (η)

**Verification method**: Level 0 normalizer

```
1. Write Level 1 normalizer N₁ (uses curry/apply)
2. Encode N₁ as Level 0 data
3. Level 0 normalizer verifies N₁'s encoding is well-formed
4. N₁ achieves fixpoint on its own encoding
5. N₁ is verified
```

**TCB**: Level 0 (already verified)

### Level 2: Full Recursion Schemes (OCP-0003 IR)

**Additional IR Operations:**
- `ν F` (greatest fixpoint / coinductive types)
- `Out : νF → F(νF)` (coalgebra structure)
- `ana : (A → F A) → A → νF` (anamorphism)
- Guardedness checking for productivity

**This IS the OCP-0003 IR**: The complete Once intermediate representation.

**Verification method**: Level 1 normalizer

```
1. Write Level 2 normalizer N₂ (uses ana, guardedness)
2. Encode N₂ as Level 1 data
3. Level 1 normalizer verifies N₂'s encoding
4. N₂ achieves fixpoint
5. N₂ is verified
```

**TCB**: Levels 0-1 (already verified)

### Level 3: Once Compiler

**Components:**
- Parser: `String → Maybe AST`
- Type Checker: `AST → Maybe TypedAST`
- Elaborator: `TypedAST → IR`
- Optimizer: `IR → IR`
- Code Generator: `IR → TargetCode`

**Verification method**: Level 2 normalizer

```
What the normalizer verifies:

1. TOTALITY
   - Compile Once compiler to IR
   - Normalizer checks IR is well-formed
   - Well-formed IR terminates (by Lambek's Lemma)
   → The compiler doesn't crash or loop

2. CONSISTENCY (Fixpoint)
   - Run compiler on its own source
   - Check: normalize(output) = normalize(compiler)
   → The compiler is self-consistent

3. OPTIMIZER CORRECTNESS
   - For each optimization: check normalize(opt(t)) = normalize(t)
   → Optimizations preserve semantics
```

**What's NOT yet verified**: Semantic correctness (does the compiler implement the language correctly?)

**TCB**: Levels 0-2 (already verified)

### Level 4: Once + Dependent Types

**Additional capabilities:**
- Types can depend on values: `Vec : Nat → Type → Type`
- Propositions as types: `IsEven : Nat → Type`
- Proofs as programs: `proof : IsEven 4`

**Verification method**: Extended normalizer (proof checking)

```
With dependent types, we can write SPECIFICATIONS:

compile-correct : ∀ s → ⟦compile s⟧ ≡ ⟦s⟧
--                      ↑ compiled semantics = source semantics

parse-inverse : ∀ ast → parse (pretty ast) ≡ Just ast
--                      ↑ parser inverts pretty-printer

The proof terms compile to IR.
The normalizer checks: does the proof normalize to refl?
If yes, the specification is satisfied.
```

**TCB**: Levels 0-3 (already verified)

### Level 5: Fully Verified Once

**The end state:**
- Once compiler written in Once
- Correctness proofs written in Once
- Both compile to IR
- Normalizer verifies both code and proofs
- System is self-hosting and self-verifying

```
┌─────────────────────────────────────────────────────────────────┐
│                         TCB (TRUSTED)                            │
├─────────────────────────────────────────────────────────────────┤
│  Mathematics (category theory, logic)                            │
│  Hardware (CPU, memory)                                          │
│  Bootstrap normalizer (~50-100 lines, or less)                   │
├─────────────────────────────────────────────────────────────────┤
│                      VERIFIED (NOT TRUSTED)                      │
├─────────────────────────────────────────────────────────────────┤
│  Once compiler (parser, type checker, elaborator, optimizer)     │
│  Correctness proofs for the compiler                             │
│  Once standard library                                           │
│  All Once programs and their proofs                              │
│  The normalizer itself (after bootstrap)                         │
└─────────────────────────────────────────────────────────────────┘
```

### Summary: Trust Flow

```
Mathematics (trusted, peer-reviewed since 1960s)
    ↓ proves
"Fixpoint ⟹ Normal Form" theorem (in simple systems)
    + confluence (unique normal forms)
    + termination (normal forms exist)
    ↓ applied to
Bootstrap normalizer (~50-100 lines, human-verifiable)
    ↓ verifies (via fixpoint)
Level 0 normalizer
    ↓ verifies
Level 1 normalizer
    ↓ verifies
Level 2 normalizer (OCP-0003 IR)
    ↓ verifies
Once compiler (totality, consistency)
    ↓ with dependent types, verifies
Once compiler proofs (semantic correctness)
    ↓ verifies
All Once programs + proofs
```

The entire verification chain rests on:
1. Mathematical theorems (published, peer-reviewed)
2. A tiny bootstrap (~50-100 lines, or pen-and-paper)
3. Hardware (unavoidable)

---

## Motivation

### The Traditional Trust Problem

Every verified system has a Trusted Computing Base (TCB):

```
Traditional Verification Stack:
─────────────────────────────────────────
Hardware                    (trusted)
    ↓
Operating System            (trusted)
    ↓
Proof Assistant (Agda/Coq)  (trusted)  ← Problem!
    ↓
Verified Compiler
    ↓
Generated Code
```

We trust Agda/Coq because "their type checkers are obviously correct" — but they're 50,000+ lines of complex code. Bugs have been found in proof assistants.

### The Goal

```
Minimal-Trust Verification Stack:
─────────────────────────────────────────
Hardware                    (trusted - unavoidable)
    ↓
Mathematics                 (trusted - it's math)
    ↓
Bootstrap Normalizer        (trusted - ~50-100 lines, verifiable)
    ↓
Once IR = Math              (verified by bootstrap)
    ↓
Verified Code
```

**Minimal software TCB.** Trust in mathematical definitions, hardware, and a tiny verifiable bootstrap normalizer — NOT a 50,000 line proof assistant.

### Why This Is Possible for Once

The CCC IR from OCP-0003 is not a programming language *based on* category theory. It **is** category theory:

- The 12 generators ARE categorical morphisms
- The typing rules ARE categorical laws
- Verification IS checking categorical validity

There's no gap between "specification" and "implementation" to trust.

---

## The Foundation: CCC IR = Category Theory

### The 12 Generators ARE Categorical Morphisms

```
┌─────────────────────────────────────────────────────────────┐
│     Once CCC IR          │     Category Theory             │
├──────────────────────────┼──────────────────────────────────┤
│ Id A                     │ id_A : A → A                    │
│ Compose g f              │ g ∘ f                           │
│ Fst A B                  │ π₁ : A × B → A                  │
│ Snd A B                  │ π₂ : A × B → B                  │
│ Pair f g                 │ ⟨f, g⟩ : C → A × B             │
│ Inl A B                  │ ι₁ : A → A + B                  │
│ Inr A B                  │ ι₂ : B → A + B                  │
│ Case f g                 │ [f, g] : A + B → C              │
│ Terminal A               │ !_A : A → 1                     │
│ Initial A                │ ¡_A : 0 → A                     │
│ Curry f                  │ λ(f) : A → (B → C)              │
│ Apply A B                │ eval : (A → B) × A → B          │
└──────────────────────────┴──────────────────────────────────┘
```

These aren't representations of categorical concepts — they ARE the concepts.

### The Categorical Laws ARE Definitional

The equations that govern CCC IR are not theorems to prove. They are the **definition** of what "Cartesian Closed Category" means:

```
Identity Laws (definition of identity morphism):
    compose f id = f
    compose id f = f

Associativity (definition of composition):
    compose (compose f g) h = compose f (compose g h)

Product Laws (definition of categorical product):
    fst ∘ pair f g = f                    -- β₁
    snd ∘ pair f g = g                    -- β₂
    pair (fst ∘ h) (snd ∘ h) = h          -- η (when h : C → A × B)
    pair fst snd = id                      -- η (special case)

Coproduct Laws (definition of categorical coproduct):
    case f g ∘ inl = f                    -- β₁
    case f g ∘ inr = g                    -- β₂
    case (h ∘ inl) (h ∘ inr) = h          -- η
    case inl inr = id                      -- η (special case)

Terminal Object Laws (definition of terminal object):
    terminal = terminal                    -- uniqueness (any two are equal)

Initial Object Laws (definition of initial object):
    initial = initial                      -- uniqueness

Exponential Laws (definition of exponential/closed structure):
    apply ∘ pair (curry f) id = f          -- β
    curry (apply ∘ pair (g ∘ fst) snd) = g -- η
```

A structure satisfying these laws IS a CCC. The laws don't describe CCCs — they DEFINE them.

### RecursionIR = Initial Algebras + Final Coalgebras

```
┌─────────────────────────────────────────────────────────────┐
│     Once RecursionIR     │     Category Theory             │
├──────────────────────────┼──────────────────────────────────┤
│ μF                       │ Initial F-algebra               │
│ In : F(μF) → μF          │ Algebra structure map           │
│ Cata alg                 │ Unique F-algebra morphism       │
│                          │   from initial algebra          │
├──────────────────────────┼──────────────────────────────────┤
│ νF                       │ Final F-coalgebra               │
│ Out : νF → F(νF)         │ Coalgebra structure map         │
│ Ana coalg                │ Unique F-coalgebra morphism     │
│                          │   to final coalgebra            │
└──────────────────────────┴──────────────────────────────────┘
```

The key properties are definitional:

```
Initial Algebra (definition):
    For any F-algebra (A, alg : F(A) → A),
    there exists a UNIQUE morphism cata alg : μF → A
    such that: cata alg ∘ In = alg ∘ F(cata alg)

    ┌────────┐    In     ┌────────┐
    │ F(μF)  │ ────────→ │   μF   │
    └────────┘           └────────┘
         │                    │
    F(cata alg)          cata alg
         │                    │
         ↓                    ↓
    ┌────────┐    alg    ┌────────┐
    │  F(A)  │ ────────→ │   A    │
    └────────┘           └────────┘

    This diagram commutes BY DEFINITION of initial algebra.

Final Coalgebra (definition):
    For any F-coalgebra (A, coalg : A → F(A)),
    there exists a UNIQUE morphism ana coalg : A → νF
    such that: Out ∘ ana coalg = F(ana coalg) ∘ coalg

    ┌────────┐  coalg   ┌────────┐
    │   A    │ ───────→ │  F(A)  │
    └────────┘          └────────┘
         │                   │
     ana coalg          F(ana coalg)
         │                   │
         ↓                   ↓
    ┌────────┐   Out    ┌────────┐
    │   νF   │ ───────→ │ F(νF)  │
    └────────┘          └────────┘

    This diagram commutes BY DEFINITION of final coalgebra.
```

### Totality and Productivity ARE Definitional

```
Lambek's Lemma (1968):
    The structure map In : F(μF) → μF is an isomorphism.

    This means μF ≅ F(μF).

    Consequence: μF is well-founded (no infinite descent).
    Therefore: cata always terminates.

    This is not a theorem about our IR — it's a theorem about
    initial algebras, proven in 1968, part of mathematics.

Dual (Final Coalgebras):
    The structure map Out : νF → F(νF) is an isomorphism.

    This means νF ≅ F(νF).

    Consequence: νF is productive (always has next element).
    Therefore: ana always makes progress (with guardedness).

    Also a mathematical theorem, not specific to Once.
```

---

## Verification = Categorical Validity

### What "Verification" Means

```
Traditional:
    "Verify this program is correct"
    = Run verification algorithm
    = Trust verification algorithm is correct
    = Trust: ~50,000 lines of proof assistant

Minimal-Trust:
    "Verify this program is correct"
    = Check it's a valid CCC morphism
    = Check it satisfies the categorical definitions
    = Trust: ~50-100 lines bootstrap normalizer
```

### The Verification Predicate

```
A Once program P is valid iff:

1. P is a well-formed morphism in a CCC
   (follows from the generators and composition rules)

2. All eliminations of μF are via cata
   (definition: cata is THE way to use initial algebras)

3. All introductions of νF are via guarded ana
   (definition: ana is THE way to produce final coalgebras)

This is not an algorithm. It's the MEANING of validity.
```

### The "Verifier" IS the Definitions

```
-- This is not code. This is mathematics written in executable notation.

valid : IR → Bool

-- CCC morphisms are valid by categorical definitions
valid (Id A)         = true                      -- identity exists
valid (Compose g f)  = target f ≡ source g      -- composition defined
valid (Fst A B)      = true                      -- product projection
valid (Snd A B)      = true                      -- product projection
valid (Pair f g)     = source f ≡ source g      -- universal property
valid (Inl A B)      = true                      -- coproduct injection
valid (Inr A B)      = true                      -- coproduct injection
valid (Case f g)     = target f ≡ target g      -- universal property
valid (Terminal A)   = true                      -- terminal morphism
valid (Initial A)    = true                      -- initial morphism
valid (Curry f)      = isProduct (source f)     -- exponential transpose
valid (Apply A B)    = true                      -- evaluation morphism

-- Initial algebra: cata is the unique eliminator
valid (Cata F alg x) = validAlg F alg ∧ hasType x (μ F)

-- Final coalgebra: ana is the unique introducer (with guardedness)
valid (Ana F coalg s) = validCoalg F coalg ∧ guarded coalg

-- Guardedness: coalgebra result is under a constructor
guarded : CCC_IR → Bool
guarded (Pair _ _) = true      -- product constructor guards
guarded (Inl _ _)  = true      -- sum constructor guards
guarded (Inr _ _)  = true      -- sum constructor guards
guarded _          = false
```

This isn't an algorithm we trust. It's the categorical definitions, expressed in a form that can be mechanically checked.

---

## The Minimal-Trust Argument

### What We're Claiming

```
Claim: Verifying Once programs requires trust ONLY in:
       1. Mathematics (category theory, logic)
       2. Hardware (physical computation)
       3. Bootstrap normalizer (~50-100 lines)

       No trust required in:
       - Any proof assistant (50,000+ lines)
       - Any compiler (verified output, not compiler itself)
       - Any complex software implementation
       - Any "obviously correct" human judgment
```

### The Argument

```
Step 1: Once IR = Category Theory
        ─────────────────────────
        The CCC IR generators ARE categorical morphisms.
        The RecursionIR constructs ARE initial/final (co)algebras.
        There is no "implementation" separate from "specification".

Step 2: Validity = Categorical Laws
        ────────────────────────────
        A program is valid iff it satisfies the categorical laws.
        The categorical laws are DEFINITIONS, not theorems.
        Checking definitions is mechanical symbol manipulation.

Step 3: Totality/Productivity = Mathematical Theorems
        ──────────────────────────────────────────────
        Lambek's Lemma (1968): cata on initial algebras terminates.
        Dual theorem: guarded ana on final coalgebras is productive.
        These are mathematical facts, independent of Once.

Step 4: Verification = Checking Categorical Structure
        ──────────────────────────────────────────────
        To verify a program:
        - Check it's a valid CCC morphism (syntactic)
        - Check recursion uses cata/ana (syntactic)
        - Check ana is guarded (syntactic)
        All checks are: "does this match the definition?"

Step 5: Matching Definitions = Symbol Manipulation
        ──────────────────────────────────────────
        Checking if something matches a definition is:
        - Pattern matching
        - Equality comparison
        - No complex reasoning
        Hardware can do this directly.

Conclusion: Trust Chain
        ───────────────
        Valid program
            ↑ follows from
        Matches categorical definitions
            ↑ checked by
        Symbol manipulation
            ↑ performed by
        Hardware

        Plus: Totality/Productivity
            ↑ follows from
        Lambek's Lemma + coalgebra theorems
            ↑ which are
        Mathematical facts (since 1968)
```

### What We Trust and Why

```
┌─────────────────────────────────────────────────────────────┐
│                    TRUSTED                                  │
├─────────────────────────────────────────────────────────────┤
│ Mathematics                                                 │
│ ├── Category theory is consistent                          │
│ ├── CCCs exist and have the stated properties              │
│ ├── Initial algebras have the initiality property          │
│ ├── Final coalgebras have the finality property            │
│ └── Lambek's Lemma is correct (proven 1968)                │
│                                                             │
│ Hardware                                                    │
│ ├── CPU executes instructions correctly                    │
│ ├── Memory stores and retrieves correctly                  │
│ └── Symbol manipulation works as intended                  │
│                                                             │
│ Bootstrap Normalizer (~50-100 lines)                        │
│ ├── Written outside Once ecosystem                         │
│ ├── Applies categorical reduction rules                    │
│ ├── Small enough for human verification                    │
│ └── Breaks the bootstrapping circular dependency           │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│                    NOT TRUSTED                              │
├─────────────────────────────────────────────────────────────┤
│ Software                                                    │
│ ├── Once compiler (can have bugs - we verify its output)   │
│ ├── Proof assistants (not needed)                          │
│ ├── Operating system (just runs hardware)                  │
│ └── Complex verification tools (not needed)                │
│                                                             │
│ Humans                                                      │
│ ├── Code review of large codebases (not needed)            │
│ ├── Trust in "obviously correct" (not needed)              │
│ └── Faith in proof assistants (not needed)                 │
└─────────────────────────────────────────────────────────────┘
```

### The Bootstrapping Problem

A fundamental challenge exists: how do we verify the verifier?

```
The Circular Dependency:
─────────────────────────
Once Compiler → needs verification
    ↓
Verifier (in Once) → needs compilation
    ↓
Once Compiler → needs verification
    ↓
... infinite regress
```

**Solution: Bootstrap Normalizer**

We break the cycle with a tiny external normalizer:

```
Bootstrap Normalizer (~50-100 lines):
─────────────────────────────────────
Input:  CCC/RecursionIR expressions
Output: Normalized form

Implementation:
- Written in any trusted language (C, assembly, hand-executed)
- Implements ONLY categorical reduction rules:
  * compose f id → f
  * compose id f → f
  * fst ∘ pair f g → f
  * snd ∘ pair f g → g
  * case f g ∘ inl → f
  * case f g ∘ inr → g
  * apply ∘ pair (curry f) id → f
  * cata alg ∘ In → alg ∘ F(cata alg)  [for recursion]

Why ~50-100 lines suffices:
- ~12 CCC reduction rules
- ~4 recursion scheme rules
- Pattern matching + substitution
- No complex algorithms
```

**Note**: The approach below still trusts this code. See "The Assembly Gap and Its Resolution" for how to eliminate even this trust by verifying the normalizer's traces directly.

---

## The Verification Process

### For Any Once Program

```
Input: Once source code

Step 1: Parse to IR
        (Parser may have bugs - we verify the output, not the parser)

Step 2: Check IR validity
        For each IR node:
        - Is it a valid CCC generator? (match against 12 cases)
        - Is composition well-typed? (source = target check)
        - Is recursion via cata/ana? (match against Cata/Ana)
        - Is ana guarded? (constructor at top of coalgebra)

Step 3: If all checks pass → program is total + productive
        This follows from:
        - Categorical definitions (what CCC means)
        - Lambek's Lemma (initiality → termination)
        - Coalgebra theorem (finality + guard → productivity)

Output: Verified program (or rejection with reason)
```

### The Checker Implementation

The checker can be implemented in any language. Its correctness follows from:

1. Does it correctly identify the 12 CCC generators? (12 pattern matches)
2. Does it correctly check source/target equality? (type equality)
3. Does it correctly identify cata/ana usage? (2 pattern matches)
4. Does it correctly check guardedness? (constructor at top)

All of these are **mechanical** checks that directly correspond to definitions.

### Multiple Implementations (Development Aid)

During development, multiple implementations can help catch bugs:

```
Checker in C      ──┐
Checker in Rust    │
Checker in Python  ├──→ Disagreement reveals bugs
Checker in OCaml   │
Checker in Haskell─┘
```

However, this is **not** the basis for trust. See "The Assembly Gap and Its Resolution" for how trust is established through human-verifiable traces, not through implementation diversity.

---

## Self-Verification

### The Checker as a Once Program

The checker itself can be written in Once:

```
check : IR → Bool
check = cata checkAlgebra

checkAlgebra : IRF Bool → Bool
checkAlgebra (IdF A)        = true
checkAlgebra (ComposeF g f) = g ∧ f ∧ typesMatch
checkAlgebra (PairF f g)    = f ∧ g ∧ sameSource
checkAlgebra (CataF F a x)  = a ∧ x ∧ validFunctor F
checkAlgebra (AnaF F c s)   = c ∧ s ∧ validFunctor F ∧ guarded c
-- ... etc
```

Since the checker:
- Uses only cata (structural recursion)
- On IR (a polynomial functor / μF)
- With a total algebra

The checker is itself total + productive.

### The Self-Verification Loop

```
┌─────────────────────────────────────────────────────────────┐
│     Checker source (Once)                                   │
└─────────────────────────────────────────────────────────────┘
                         │
                         │ compile to IR
                         ↓
┌─────────────────────────────────────────────────────────────┐
│     Checker IR: ⟦check⟧                                     │
└─────────────────────────────────────────────────────────────┘
                         │
                         │ run checker on itself
                         ↓
┌─────────────────────────────────────────────────────────────┐
│     check(⟦check⟧) = true                                   │
│                                                             │
│     The checker verifies its own IR is valid!               │
└─────────────────────────────────────────────────────────────┘
```

This is not circular reasoning. It's a **fixpoint** with mathematical teeth:

- In a simple system (confluent + terminating), fixpoints are normal forms
- The checker's own IR achieves fixpoint under normalization
- Therefore the checker's IR is in normal form (proven, not assumed)
- Normal forms are unique, so the encoding is THE canonical form
- This is mathematically forced, not self-justifying

### The Bootstrap

```
Phase 1: Write checker by hand (in any language)
         Correctness: follows from categorical definitions

Phase 2: Write checker in Once

Phase 3: Compile Once checker to IR using any compiler
         (Compiler may have bugs - we'll verify the output)

Phase 4: Run hand-written checker on IR of Once checker
         Result: valid (or find the compiler bug)

Phase 5: Run Once checker on its own IR
         Result: valid (self-verification)

Phase 6: Now use Once checker for everything
         Its correctness is grounded in:
         - Categorical definitions (math)
         - Self-verification (fixpoint)
         - Hardware (performs the checks)
```

---

## Formal Statement

### Theorem: Minimal-Trust Verification

```
Let P be a Once program.

Claim: P is total + productive
       iff
       P is a valid morphism in a CCC with initial algebras
       and final coalgebras (with guarded corecursion)

Proof:

(→) If P is total + productive, then by the semantics of Once,
    P denotes a morphism in a CCC with the required structure.

(←) If P is a valid morphism in such a category, then:

    For termination:
    - All elimination of μF is via cata (by IR structure)
    - cata terminates by Lambek's Lemma (1968)
    - Lambek: In : F(μF) → μF is an isomorphism
    - Therefore μF is well-founded
    - Therefore structural recursion terminates

    For productivity:
    - All introduction of νF is via guarded ana (by IR structure)
    - ana is productive by final coalgebra property
    - Guardedness ensures each step produces a constructor
    - Therefore progress is always made

The verification:
- Checks P has the required IR structure (syntactic)
- Applies to mathematical theorems (Lambek, coalgebra)
- Requires trust only in math + hardware                     □
```

### Corollary: Minimal TCB

```
The software TCB for Once verification is ~50-100 lines.

Proof:
- Verification = checking categorical structure
- Categorical structure = mathematical definitions
- Checking = symbol manipulation (hardware)
- Bootstrap normalizer = categorical laws as code (~50-100 lines)
- Bootstrap required to break circular dependency
- After bootstrap, trust chain is: math → bootstrap → Once      □
```

This is a dramatic reduction from ~50,000 lines (typical proof assistant) to ~50-100 lines (bootstrap normalizer).

**Update**: See "The Assembly Gap and Its Resolution" for how to eliminate even this ~50-100 line TCB by verifying traces instead of trusting code.

---

## Implementation Strategy

### Phase 1: Formal Specification

Write the categorical foundations as pure mathematics:

```
Definition (CCC): A category C is cartesian closed iff ...
Definition (Initial Algebra): An initial F-algebra is ...
Definition (Once IR): An Once IR term is ...
Definition (Validity): An IR term is valid iff ...
Theorem (Totality): Valid IR terms denote total functions.
Theorem (Productivity): Valid IR terms with νF are productive.
```

### Phase 2: Minimal Checker

Implement the validity check in the simplest possible form:

```
valid : IR → Bool
valid = cata validAlgebra
-- ~50 lines of pattern matching
```

This is not "implementing" the specification. It IS the specification, in executable notation.

### Phase 3: Development Testing

During development, test implementations against each other to catch bugs. This is a development aid, not the trust basis.

### Phase 4: Self-Hosting

```
1. Compile valid.once to IR using Once compiler
2. Run valid.once on its own IR, producing trace
3. Human verifies trace (one time, ~2 hours)
4. Trust established through human-verified math
```

### Phase 5: Full Deployment

```
All Once compilation:
1. Compiler produces IR
2. valid.once checks IR
3. If valid → totality + productivity guaranteed
4. Trust: math + hardware only
```

---

## Comparison with Existing Approaches

| Approach | TCB | Trust Basis |
|----------|-----|-------------|
| Testing | Large | "Tests passed" |
| Code review | Large | Human judgment |
| Agda/Coq | 50,000+ LOC | Proof assistant correct |
| Metamath | ~300 LOC | Small verifier correct |
| **Once (basic)** | **~50-100 LOC** | **Categorical laws as code** |
| **Once (trace verifier)** | **~15-20 LOC** | **Trace verification** |
| **Once (pen-and-paper)** | **~0 LOC** | **Manual trace check** |

The Once approach has a minimal TCB because:
1. The bootstrap normalizer IS the categorical laws (not an implementation of them)
2. After bootstrap, Once self-verifies with no additional trust
3. With proof-carrying normalization, only the trace verifier needs trust
4. The trace verifier can be verified by hand (pen-and-paper) for ultimate minimization

---

## Further TCB Minimization

The ~50-100 line bootstrap normalizer is already small, but can we go smaller? This section explores approaches to reduce the TCB even further.

### The Problem with the Current Approach

The bootstrap normalizer (~50-100 lines) must:
1. Represent CCC terms (~10 lines)
2. Pattern match reduction rules (~30 lines)
3. Apply substitution (~20 lines)
4. Iterate until normal form (~10 lines)

We trust ALL of this code. Can we reduce what we trust?

### Approach 1: Proof-Carrying Normalization

**Key insight**: Don't trust the normalizer's computation — only trust a trace verifier.

Instead of:
```
normalize : CCC → CCC
```

Use:
```
normalize : CCC → (CCC, Trace)

where Trace = [(RuleName, Before, After), ...]
```

Example trace:
```
Input: compose (compose f id) g

Step 1: compose (compose f [id]) g
        Rule: id-right
        Before: compose f id
        After: f

Step 2: compose f g
        (normal form)

Output: compose f g
Trace: [(id-right, "compose f id", "f")]
```

The trace verifier is trivial (~15-20 lines):

```
verify : Trace → Bool
verify [] = true
verify ((rule, before, after) :: rest) =
  matches rule before &&        -- pattern matches?
  apply rule before == after && -- correct application?
  chainedCorrectly rest after &&-- next step starts here?
  verify rest                   -- rest valid?
```

**TCB reduction**: ~50-100 lines → ~15-20 lines

The normalizer can be buggy — bugs are caught by the trace verifier, not trusted.

### Approach 2: String Rewriting Systems

CCC reduction rules ARE string rewriting rules:

```
┌────────────────────────────────────────────────────────────┐
│                 CCC as String Rewriting                    │
├────────────────────────────────────────────────────────────┤
│ compose f id           →  f                                │
│ compose id f           →  f                                │
│ fst (pair f g)         →  f                                │
│ snd (pair f g)         →  g                                │
│ case f g (inl x)       →  f x                              │
│ case f g (inr x)       →  g x                              │
│ apply (pair (curry f) x) →  f x                            │
│ pair (fst ∘ h) (snd ∘ h) →  h    (when h : A → B × C)     │
└────────────────────────────────────────────────────────────┘
```

A string rewriting engine is ~10-15 lines:

```
rewrite : [Rule] → Term → Maybe Term
rewrite rules term =
  case findFirstMatch rules term of
    Nothing → Nothing
    Just (rule, subst) → Just (applySubst subst (rhs rule))

normalize : [Rule] → Term → Term
normalize rules term =
  case rewrite rules term of
    Nothing → term
    Just term' → normalize rules term'
```

The rules themselves ARE the specification — the rewriter just does mechanical pattern matching.

### Approach 3: Self-Evident Traces

Make the trace format so clear that verification is visual:

```
═══════════════════════════════════════════════════════════
REDUCTION TRACE
═══════════════════════════════════════════════════════════

Input: compose (compose f id) g

Step 1:
  Term:    compose (compose f id) g
  Pattern: compose _ id
  Match:   compose f id
                   ├─ _ = f
                   └─ id = id ✓
  Rule:    id-right: compose X id → X
  Result:  compose f g

Step 2:
  Term:    compose f g
  No patterns match.
  NORMAL FORM REACHED.

Output: compose f g
═══════════════════════════════════════════════════════════
```

A human can verify this by:
1. Checking highlighted pattern matches the rule's LHS
2. Checking substitution is applied correctly
3. Checking result matches

For the bootstrap case (normalizer verifying itself), this could be done **by hand** once.

### Approach 4: Generate Code and Proof Simultaneously

**Deep insight**: In Curry-Howard, programs ARE proofs.

For CCC normalization:
- A reduction step IS a proof that `before ≡ after`
- The complete trace IS a proof that `input ≡ result`

```
normalize : (t : CCC) → Σ (r : CCC) × (t ≡ r)
--          input        result      proof that input equals result
```

If we write the normalizer in CCC itself using `cata`:

```
normalize : CCC → CCC
normalize = cata normalizeAlgebra
```

Then:
- `cata` guarantees termination (Lambek's Lemma)
- The algebra structure IS the correctness argument
- The code IS the proof — they're the same object

### Approach 5: Layered TCB Architecture

Separate concerns into layers with decreasing trust requirements:

```
┌─────────────────────────────────────────────────────────────┐
│ Layer 0: Mathematical Definitions        (~0 lines of code)│
│ ─────────────────────────────────────────────────────────── │
│ The CCC laws written on paper:                              │
│   compose f id = f                                          │
│   compose id f = f                                          │
│   fst (pair f g) = f                                        │
│   ...                                                       │
│                                                             │
│ Trust basis: Mathematics (peer-reviewed since 1960s)        │
├─────────────────────────────────────────────────────────────┤
│ Layer 1: Trace Verifier                  (~15-20 lines)     │
│ ─────────────────────────────────────────────────────────── │
│ Checks: does each step correctly apply a rule?              │
│                                                             │
│ - Pattern match check (tree comparison)                     │
│ - Substitution check (variable replacement)                 │
│ - Chain check (each step follows previous)                  │
│                                                             │
│ Trust basis: Small enough to verify BY HAND                 │
├─────────────────────────────────────────────────────────────┤
│ Layer 2: Normalizer                      (~50-100 lines)    │
│ ─────────────────────────────────────────────────────────── │
│ Produces reduction traces                                   │
│                                                             │
│ Trust basis: NONE — verified by Layer 1                     │
│ (Bugs are caught, not trusted)                              │
├─────────────────────────────────────────────────────────────┤
│ Layer 3: Once Verifier                   (in Once)          │
│ ─────────────────────────────────────────────────────────── │
│ Full verification system                                    │
│                                                             │
│ Trust basis: NONE — verified by Layer 2, then self-verifies │
└─────────────────────────────────────────────────────────────┘

True TCB = Layer 0 (math) + Layer 1 (trace verifier) = ~15-20 lines
```

### Approach 6: The Pen-and-Paper Bootstrap

The ultimate minimal TCB:

```
For the ONE-TIME bootstrap verification:

1. Run normalizer on its own IR
2. Get reduction trace (printed output)
3. Verify trace BY HAND with pen and paper:
   - For each step, check pattern matches
   - For each step, check substitution correct
   - Confirm final result

This is feasible because:
- The bootstrap is done ONCE
- The trace is finite
- Each step is mechanical (pattern matching)
- A mathematician can do this in a few hours

After this ONE manual verification:
- The normalizer is trusted
- It can verify the Once verifier
- Once self-verifies everything else

TCB: Literally just mathematics + human pattern matching
```

### Comparison of Approaches

| Approach | TCB Size | Verification Method |
|----------|----------|---------------------|
| Current bootstrap | ~50-100 lines | Code inspection |
| Proof-carrying + trace verifier | ~15-20 lines | Verify verifier code |
| Verifier with fixpoint (new) | 0 lines | Human verifies verifier's trace |

### Recommended Path

```
Phase 1: Current approach (~50-100 lines)
         Good enough to start, enables self-hosting

Phase 2: Add trace generation
         Normalizer outputs reduction traces
         Enables manual verification of bootstrap

Phase 3: Implement trace verifier as CCC term (~25 primitives)
         Verifier has fixpoint property like normalizer
         Verifier's meta-trace is human-verifiable

Phase 4: Human verification of verifier's meta-trace
         One-time ~2 hour verification
         Grounds entire system in human-checked math

Final state:
┌─────────────────────────────────────────────────────────────┐
│  Trusted: Mathematics only                                   │
│  Verified by human-checked traces: Verifier, then everything│
└─────────────────────────────────────────────────────────────┘
```

See "The Assembly Gap and Its Resolution" below for the complete solution.

### The Theoretical Minimum

The absolute minimum TCB is:

1. **Mathematics**: CCC reduction rules (definitions, not code)
2. **Hardware**: Must render traces faithfully (unavoidable)
3. **Human**: Must verify ~200-400 pattern matches once (bootstrap)

No software trust required. This is the theoretical minimum for any verification system.

---

## The Assembly Gap and Its Resolution

### The Problem: Mathematical Proofs Don't Apply to Binaries

The previous sections establish that if a normalizer N is built from CCC primitives and achieves a fixpoint, then N is correct. But there's a critical gap:

```
Mathematical Normalizer N          Assembly/Binary B
(CCC primitives, proven correct)   (running on hardware)
            ↑                              ↑
      Theorems apply here           Theorems say nothing here
```

**The gap**: How do we know the actual binary B faithfully implements the mathematical N?

This matters because:
1. **Malicious tampering**: Someone could modify the assembly while preserving the fixpoint on self-test
2. **Compiler bugs**: The compiler translating N to assembly could have bugs
3. **"Trusting Trust"**: The entire toolchain could be compromised

The fixpoint property proves N (the abstract CCC term) is correct, but says nothing about whether B corresponds to N.

### Why Trace Verification Alone Doesn't Solve It

One might think: "Run B, get a trace, verify the trace by hand."

But this has a flaw: **B produces the trace**. A malicious B could:
- Internally compute something wrong
- Output a perfectly valid trace
- Humans verify the printed trace, not what actually happened

The trace is just bytes that B chose to output. There's no guarantee they reflect B's actual computation.

### The Solution: Traces as Self-Certifying Mathematical Objects

The key insight is to change our perspective on what traces are:

**Old view**: Trace = record of what the software did (requires trusting software)
**New view**: Trace = mathematical proof that stands on its own (requires no trust)

A valid CCC reduction trace is a **mathematical object**. Each step either is or isn't a valid CCC reduction — this is a mathematical fact independent of what produced the trace.

If a binary produces an **invalid** trace, verification catches it.
If a binary produces a **valid** trace, the **result is correct by math**, regardless of what the binary does internally.

### The Minimal Verifier with Fixpoint Property

The verifier V only needs to check: "Is this single step a valid CCC reduction?"

```
V : Step → Bool
V (before, rule, after) =
  case rule of
    IdRight  → before matches (f ∘ id) ∧ after ≡ f
    IdLeft   → before matches (id ∘ f) ∧ after ≡ f
    FstPair  → before matches (fst ∘ ⟨f,g⟩) ∧ after ≡ f
    SndPair  → before matches (snd ∘ ⟨f,g⟩) ∧ after ≡ g
    CaseInl  → before matches ([f,g] ∘ inl) ∧ after ≡ f
    CaseInr  → before matches ([f,g] ∘ inr) ∧ after ≡ g
    ... (12-15 rules total)
```

**Crucially, V itself is a CCC term**. Written as `cata TermF verifyAlgebra` where `verifyAlgebra` is NoRedex, V has the **same fixpoint property** as the normalizer:

```
normalize(encode(V)) ⟶* encode(V)
```

But V is **much smaller** than the normalizer:
- Normalizer N: ~100-150 CCC primitives
- Verifier V: ~20-30 CCC primitives

### Size Estimates for Human Verification

```
V ≈ 25 CCC primitives
encode(V) ≈ 30-40 nodes
Trace of normalizing encode(V) ≈ 40-60 steps
V verifying that trace ≈ 40-60 verification steps
Meta-trace ≈ 200-400 primitive operations
```

At 10 seconds per operation: **~1-2 hours of human work**.

### Decomposition for Even Smaller Verification

V can be split into micro-verifiers:

```
V_id   : checks id-left, id-right           (~5 primitives)  ~15 min
V_pair : checks fst-pair, snd-pair, η-pair  (~8 primitives)  ~20 min
V_case : checks case-inl, case-inr, η-case  (~8 primitives)  ~20 min
V_exp  : checks β-curry, η-curry            (~6 primitives)  ~15 min
V_cata : checks cata-β                      (~5 primitives)  ~15 min
```

Each micro-verifier has its own fixpoint, and each can be verified independently in ~15-20 minutes.

### The Complete Bootstrap Protocol

```
┌─────────────────────────────────────────────────────────────┐
│              PHASE 1: VERIFY THE VERIFIER                    │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  For each micro-verifier V_x:                                │
│                                                              │
│  1. Run ANY implementation of V_x on encode(V_x)             │
│     → Produces trace T_x                                     │
│                                                              │
│  2. V verifies T_x, producing meta-trace M_x                │
│                                                              │
│  3. Format M_x in human-readable form:                       │
│                                                              │
│     ═══════════════════════════════════════════════════════  │
│     VERIFICATION OF T_id, STEP 3                             │
│     ═══════════════════════════════════════════════════════  │
│                                                              │
│     Claim: (compose f id) ──[id-right]──▶ f                  │
│                                                              │
│     Check 1: Does "compose f id" match pattern "_ ∘ id"?     │
│              compose  f   id                                 │
│              [_____] [_] [id]                                │
│              ✓ Match with _ = f                              │
│                                                              │
│     Check 2: Does result "f" equal the extracted _?          │
│              Result: f                                       │
│              Extracted: f                                    │
│              ✓ Equal                                         │
│                                                              │
│     Step 3 VALID ✓                                           │
│     ═══════════════════════════════════════════════════════  │
│                                                              │
│  4. Human verifies M_x by reading (one time, ~15-20 min)    │
│                                                              │
│  After Phase 1: V is PROVEN correct, not trusted             │
│                                                              │
├─────────────────────────────────────────────────────────────┤
│              PHASE 2: VERIFY THE NORMALIZER                  │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. Run normalizer N on encode(N)                            │
│     → Produces trace T_N                                     │
│                                                              │
│  2. V verifies T_N (V is now trusted from Phase 1)          │
│     → If valid, N is PROVEN correct                          │
│                                                              │
├─────────────────────────────────────────────────────────────┤
│              PHASE 3: ONGOING VERIFICATION                   │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  All computation produces traces                             │
│  V verifies all traces                                       │
│  V's correctness is grounded in human-verified proof         │
│                                                              │
│  SOFTWARE TRUST: ZERO                                        │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### Why This Eliminates All Software Trust

The key properties:

1. **Traces are mathematical proofs**: A valid trace proves the computation is correct, regardless of what produced it. An invalid trace is caught by verification.

2. **V has a fixpoint**: V is itself a CCC term with the fixpoint property, so V's correctness can be verified the same way as N's.

3. **V is small enough for human verification**: The meta-trace M_V is ~200-400 operations, verifiable in 1-2 hours.

4. **Human verification is one-time**: After the bootstrap, V is proven correct and can verify everything else.

5. **No code inspection needed**: We don't verify source code or assembly. We verify mathematical traces.

```
Trust chain:

Mathematics (CCC reduction rules)
    ↓ defines
What counts as a valid trace
    ↓ verified by
Human reading meta-traces (one time, ~2 hours)
    ↓ proves
V (verifier) is correct
    ↓ proves via traces
N (normalizer) is correct
    ↓ proves via traces
All Once programs are correct

SOFTWARE TRUST AT EACH STEP: ZERO
```

---

## Limitations and Caveats

### What We Still Trust

1. **Mathematics**: Category theory is consistent and the CCC reduction rules are correct. If mathematics itself is inconsistent, all bets are off. (But then so is everything else in formal verification.)

2. **Hardware**: The hardware correctly outputs the trace to a human-readable medium (paper, screen). This is unavoidable for any computation, but the trust is minimal: we only need the trace to be faithfully rendered, not that any computation was performed correctly.

3. **Human Verification** (one-time): A human correctly verifies the bootstrap meta-traces (~200-400 operations, ~2 hours). The trace format is designed to make each step self-evident — pattern matching that a mathematician can verify by inspection.

4. **Encoding Faithfulness**: The IR representation faithfully captures the program.

   The normalizer works on ENCODINGS of terms, not terms directly:
   ```
   encode : Term A B → Term Unit TermCode
   ```

   For verification to be meaningful, `encode` must be:

   - **Injective**: Different terms produce different codes
     ```
     encode (f ∘ g) ≠ encode (g ∘ f)
     ```
     (Proven formally in Encoding.agda)

   - **Structure-preserving**: All relevant information is captured
     (Constructor tags, type information, subterms)

   - **Faithful to intent**: The Agda definitions match mathematical concepts
     (Verified by human inspection of ~50 lines of definitions)

   This is a weak assumption:
   - Injectivity is formally proven
   - Structure preservation is by construction
   - Faithfulness is checkable by reading the encoding function

### What This Doesn't Cover

1. **Functional Correctness**: We verify totality + productivity, not "does this program compute what you want."

2. **Performance**: A total program may still be slow.

3. **Resource Bounds**: Termination doesn't mean termination in reasonable time/space.

### Extending to Functional Correctness

Functional correctness could be added:

```
-- Specification: what the program should compute
spec : A → B

-- Implementation: the actual program
impl : A → B

-- Proof: impl computes the same as spec
correct : ∀ x → impl x ≡ spec x
```

This would require dependent types (per Once's roadmap) but the same minimal-trust principle applies: correctness proofs are mathematical objects verified by categorical structure.

---

## Summary

```
┌─────────────────────────────────────────────────────────────┐
│                     THE CLAIM                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Once programs can be verified with ZERO SOFTWARE TRUST:    │
│                                                             │
│  Trust only:                                                │
│  1. Mathematics (CCC reduction rules, since 1960s)          │
│  2. Hardware (to render traces faithfully)                  │
│  3. Human verification (one-time, ~2 hours)                 │
│                                                             │
│  NO trust in: compilers, proof assistants, or any code      │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│                     THE MECHANISM                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Once IR = CCC morphisms (not representation — identity)    │
│  Validity = categorical laws (definitions, not theorems)    │
│  Totality = Lambek's Lemma (math theorem, 1968)            │
│  Productivity = coalgebra theorems (math)                   │
│                                                             │
│  KEY INSIGHT: Traces are mathematical proofs                │
│  - A valid trace proves correctness BY MATH                 │
│  - Invalid traces are caught by verification                │
│  - We verify traces, not software                           │
│                                                             │
│  THE VERIFIER HAS A FIXPOINT:                               │
│  - V (verifier) is a CCC term (~25 primitives)              │
│  - normalize(encode(V)) ⟶* encode(V)                        │
│  - V's correctness is proven the same way as N's            │
│  - But V is small enough for human trace verification       │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│                     THE BOOTSTRAP                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Phase 1: Verify the Verifier (~2 hours, one time)          │
│  - Run V on encode(V), get trace                            │
│  - Format trace in human-readable form                      │
│  - Human verifies ~200-400 pattern matches                  │
│  - V is now PROVEN correct                                  │
│                                                             │
│  Phase 2: Verify Everything Else (automatic)                │
│  - V verifies normalizer, compiler, all programs            │
│  - V's correctness is grounded in Phase 1                   │
│  - No further human verification needed                     │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│                     THE RESULT                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Software TCB: ZERO LINES                                   │
│                                                             │
│  We don't trust any software. We verify mathematical        │
│  traces that prove correctness regardless of what           │
│  software produced them.                                    │
│                                                             │
│  Compare to other systems:                                  │
│  - Typical proof assistant: ~50,000 lines trusted           │
│  - Metamath verifier: ~300 lines trusted                    │
│  - Once: 0 lines trusted (only math + traces)               │
│                                                             │
│  This is the theoretical minimum for any verification       │
│  system: trust only mathematics and human reasoning.        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## References

- Lambek, J. (1968). "A fixpoint theorem for complete categories." *Mathematische Zeitschrift*.
- Lawvere, F.W. (1963). "Functorial Semantics of Algebraic Theories."
- Mac Lane, S. (1971). *Categories for the Working Mathematician.*
- OCP-0003: Total and Productive IR via Layered Architecture.
- Rutten, J. (2000). "Universal coalgebra: a theory of systems."
- Thompson, K. (1984). "Reflections on Trusting Trust." *Turing Award Lecture*. (The problem this proposal solves.)

---

## Discussion

[Comments, concerns, and resolutions will be added here as discussion proceeds.]
