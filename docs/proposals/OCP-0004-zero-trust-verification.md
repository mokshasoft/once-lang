# OCP-0004: Minimal-Trust Verification via Categorical Foundations

**Author:** [TBD]
**Status:** Draft
**Created:** 2026-03-10
**Depends-On:** OCP-0003 (Layered IR)

---

## Summary

Establish that Once programs can be formally verified with a **minimal trusted computing base (TCB)**: mathematics, hardware, and a tiny bootstrap normalizer (~50-100 lines). This is achieved by recognizing that the CCC IR (from OCP-0003) **is** category theory, not an implementation of it. Verification becomes checking conformance to mathematical definitions, reducing the software TCB from ~50,000 lines (typical proof assistant) to ~50-100 lines (bootstrap normalizer).

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

The bootstrap normalizer can be:
1. Hand-verified by mathematicians (it IS the math)
2. Implemented multiple times independently
3. Cross-checked against hand calculations
4. Run on paper for small examples

Once the bootstrap normalizer verifies the Once verifier, the Once verifier can self-verify and verify everything else.

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

### Multiple Independent Implementations

```
Checker in C      ──┐
Checker in Rust    │
Checker in Python  ├──→ All must agree on all inputs
Checker in OCaml   │
Checker in Haskell─┘

If 5 independent implementations agree:
- Either all are correct
- Or all have the same bug (virtually impossible)
```

The implementations don't trust each other. They just check against the categorical definitions, which are the same for everyone.

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

This is not circular reasoning. It's a **fixpoint**:

- The checker checks that IR conforms to categorical definitions
- The checker's own IR conforms to categorical definitions
- Therefore the checker accepts itself
- This is mathematically consistent, not self-justifying

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

This is a dramatic reduction from ~50,000 lines (typical proof assistant) to ~50-100 lines (bootstrap normalizer). The bootstrap normalizer is small enough to be:
- Hand-verified against the mathematical definitions
- Implemented multiple times for cross-checking
- Tested exhaustively on small examples

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

### Phase 3: Multiple Implementations

Create independent implementations:

```
valid.c      -- C implementation (~100 lines)
valid.rs     -- Rust implementation (~80 lines)
valid.py     -- Python implementation (~60 lines)
valid.ml     -- OCaml implementation (~70 lines)
valid.once   -- Once implementation (~50 lines)
```

Cross-check on large corpus of programs.

### Phase 4: Self-Hosting

```
1. Compile valid.once to IR using Once compiler
2. Run valid.c on this IR → true
3. Run valid.once on its own IR → true
4. Self-verification achieved
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
| Proof-carrying + trace verifier | ~15-20 lines | Verify verifier |
| String rewriting | ~10-15 lines | Rules ARE specification |
| Pen-and-paper bootstrap | ~0 lines code | Manual trace check |

### Recommended Path

```
Phase 1: Current approach (~50-100 lines)
         Good enough to start, enables self-hosting

Phase 2: Add trace generation
         Normalizer outputs reduction traces
         Enables manual verification of bootstrap

Phase 3: Implement trace verifier (~15-20 lines)
         Multiple independent implementations
         Cross-check on all inputs

Phase 4: Pen-and-paper bootstrap verification
         One-time manual verification of trace verifier
         Reduces "opaque" TCB to mathematics itself

Final state:
┌─────────────────────────────────────────────────────────────┐
│  Trusted: Mathematics + ~15-20 line trace verifier          │
│  Verified by traces: Everything else                        │
└─────────────────────────────────────────────────────────────┘
```

### The Theoretical Minimum

The absolute minimum TCB would be:

1. **~0 lines of code**: Define rules on paper, verify traces by hand
2. **Hardware**: Must execute something (unavoidable)
3. **Human**: Must check something once (unavoidable for bootstrap)

This is as close to "trust only mathematics" as computationally possible.

---

## Limitations and Caveats

### What We Still Trust

1. **Mathematics**: Category theory is consistent. If mathematics itself is inconsistent, all bets are off. (But then so is everything else.)

2. **Hardware**: CPU executes correctly. A hardware bug could cause incorrect verification. (Unavoidable for any computation.)

3. **Bootstrap Code** (choose your level):

   **Level 1 (~50-100 lines)**: Full bootstrap normalizer
   - Direct correspondence to mathematical definitions
   - Multiple independent implementations possible
   - Small enough for careful code review

   **Level 2 (~15-20 lines)**: Trace verifier only
   - Normalizer produces proof traces
   - Only the trace verifier is trusted
   - Even smaller, even easier to verify

   **Level 3 (~0 lines)**: Pen-and-paper verification
   - One-time manual check of bootstrap trace
   - Trust only human pattern matching ability
   - Theoretical minimum for any computational system

4. **Encoding**: The IR representation faithfully captures the program. (Can be verified by inspection or multiple encoders.)

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
│  Once programs can be verified with trust only in:          │
│                                                             │
│  1. Mathematics (category theory, since 1960s)              │
│  2. Hardware (physical computation)                         │
│  3. Minimal bootstrap code (see levels below)               │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│                     THE MECHANISM                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Once IR = CCC morphisms (not representation — identity)    │
│  Validity = categorical laws (definitions, not theorems)    │
│  Totality = Lambek's Lemma (math theorem, 1968)            │
│  Productivity = coalgebra theorems (math)                   │
│  Verification = checking categorical structure (syntactic)  │
│  Bootstrap = breaks circular dependency with tiny verifier  │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│                     THE RESULT                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Software TCB options (choose your trust level):            │
│                                                             │
│  Level 1: ~50-100 lines (bootstrap normalizer)              │
│           - Standard approach, code inspection              │
│           - 500x smaller than proof assistants              │
│                                                             │
│  Level 2: ~15-20 lines (trace verifier only)                │
│           - Proof-carrying normalization                    │
│           - Normalizer verified by traces, not trusted      │
│                                                             │
│  Level 3: ~0 lines (pen-and-paper bootstrap)                │
│           - One-time manual trace verification              │
│           - Trust only math + human pattern matching        │
│                                                             │
│  Compare to other systems:                                  │
│  - Typical proof assistant: ~50,000 lines                   │
│  - Metamath verifier: ~300 lines                            │
│  - Once (Level 1): ~50-100 lines                            │
│  - Once (Level 2): ~15-20 lines                             │
│  - Once (Level 3): ~0 lines code                            │
│                                                             │
│  After bootstrap, Once self-verifies with zero additional   │
│  trust: the verified Once verifier checks everything else.  │
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

---

## Discussion

[Comments, concerns, and resolutions will be added here as discussion proceeds.]
