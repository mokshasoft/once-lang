# Formal Verification in Once

## Two Levels of Verification

This document covers two distinct concerns:

1. **Part I: Verifying the Compiler** - Proving the Once compiler itself is correct
2. **Part II: Verifying Programs** - Using external tools to prove properties of Once programs

These are separate problems with different approaches.

---

# Part I: Verifying the Compiler

## Why It's Tractable

Once is built on **graded natural transformations** (QTT + category theory). The compiler is verifiable because:

1. **Small core** - ~12 generators, not a sprawling language
2. **Equational specification** - Categorical laws ARE the spec
3. **Well-studied foundations** - QTT and CT both formalized in proof assistants
4. **Denotational semantics** - Morphisms, not operational soup

## The Specification: Graded Categorical Laws

The compiler is correct if it preserves these equations:

### Category Laws

```
compose f id = f                           -- right identity
compose id f = f                           -- left identity
compose f (compose g h) = compose (compose f g) h  -- associativity
```

### Functor Laws

```
fmap id = id                               -- identity
fmap (compose f g) = compose (fmap f) (fmap g)     -- composition
```

### Quantity Laws (QTT)

```
-- Semiring structure
0 + r = r                    -- zero is additive identity
1 · r = r                    -- one is multiplicative identity
0 · r = 0                    -- zero annihilates

-- Composition respects quantities
compose (f : B →ᵣ C) (g : A →ₛ B) : A →ᵣₛ C   -- quantities multiply
```

### Graded Naturality

```
fmap f ∘ αₐ = αᵦ ∘ fmap f    -- naturality square commutes with quantities
```

These laws have been proven since the 1940s (categories) and 2010s (QTT). We're not inventing new math.

## Compiler Pipeline

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   Source    │ → │  Categorical│ → │  Optimized  │ → │   Target    │
│   Once      │    │     IR      │    │     IR      │    │   Code      │
└─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘
     Parse           Type Check          Rewrite           Generate
                    + Quantity
                     Inference
```

Each stage needs verification.

## Stage 1: Parser

```
Syntax → AST
```

Standard parser verification. Not category-specific.

**Proof obligation:**
```coq
Theorem parse_sound :
  ∀ s ast, parse s = Some ast → valid_syntax ast.

Theorem parse_complete :
  ∀ s, valid_source s → ∃ ast, parse s = Some ast.
```

**Estimated effort:** ~500 lines of Coq. Standard techniques.

## Stage 2: Type Checker + Quantity Inference

```
AST → Typed Categorical IR (with quantities)
```

This is the interesting part. Must verify:
- Morphisms have correct source/target types
- Composition types match
- Quantities are inferred correctly
- Linearity constraints are satisfied

**Proof obligations:**

```coq
(* Well-typed programs denote graded morphisms *)
Theorem typing_sound :
  ∀ Γ e τ r, Γ ⊢ e : τ @ r →
  ∃ f : ⟦Γ⟧ →ᵣ ⟦τ⟧, ⟦e⟧ = f.

(* Type preservation under evaluation *)
Theorem preservation :
  Γ ⊢ e : τ @ r → e ⟶ e' → Γ ⊢ e' : τ @ r.

(* Progress: well-typed terms can step or are values *)
Theorem progress :
  ∅ ⊢ e : τ @ r → value e ∨ ∃ e', e ⟶ e'.

(* Quantity soundness: linear means no copying *)
Theorem linear_no_copy :
  Γ ⊢ e : τ @ 1 → ¬(copies e).

(* Quantity inference is sound *)
Theorem infer_sound :
  infer e = Some (τ, r) → ∅ ⊢ e : τ @ r.
```

**Estimated effort:** ~3000 lines of Coq. Based on existing QTT formalizations.

## Stage 3: Optimizer

```
Categorical IR → Optimized Categorical IR
```

Every optimization is a **graded categorical law**:

| Optimization | Law |
|--------------|-----|
| Identity elimination | `compose f id = f` |
| Associative reordering | `compose f (compose g h) = compose (compose f g) h` |
| Functor fusion | `compose (fmap f) (fmap g) = fmap (compose f g)` |
| Naturality | `compose (fmap f) η = compose η f` |
| Product fusion | `compose (bimap f g) diagonal = pair f g` |
| Dead code (terminal) | `compose terminal f = terminal` |

**Proof obligation:**

```coq
(* Each rewrite preserves denotation *)
Theorem rewrite_sound :
  ∀ e e', e ⟶ e' → ⟦e⟧ = ⟦e'⟧.

(* Each rewrite preserves quantities *)
Theorem rewrite_quantity :
  ∀ e e' r, e ⟶ e' → quantity e = r → quantity e' = r.
```

**Estimated effort:** ~500 lines of Coq. Proofs follow directly from categorical laws.

## Stage 4: Code Generator

```
Categorical IR → Target Code
```

Must verify the ~12 generators compile correctly for each target:

| Generator | Semantics | Must Preserve |
|-----------|-----------|---------------|
| `id` | Identity | Value unchanged |
| `compose f g` | Composition | `f(g(x))` |
| `fst` | First projection | Extract first |
| `snd` | Second projection | Extract second |
| `pair f g` | Pairing | `(f(x), g(x))` |
| `inl` | Left injection | Tag + value |
| `inr` | Right injection | Tag + value |
| `case f g` | Case analysis | Branch on tag |
| `terminal` | Discard | Produce unit |
| `initial` | Absurd | Unreachable |
| `curry` | Currying | Closure |
| `apply` | Application | Call |

**Proof obligations:**

```coq
(* Identity compiles to no-op *)
Theorem compile_id :
  ∀ v s, exec (compile id) (v, s) = (v, s).

(* Composition compiles to sequential execution *)
Theorem compile_compose :
  ∀ f g v s, exec (compile (compose f g)) (v, s) =
             exec (compile f) (exec (compile g) (v, s)).

(* Fst extracts first component *)
Theorem compile_fst :
  ∀ a b s, exec (compile fst) ((a, b), s) = (a, s).

(* Case branches correctly *)
Theorem compile_case :
  ∀ f g v s,
    exec (compile (case f g)) (inl v, s) = exec (compile f) (v, s) ∧
    exec (compile (case f g)) (inr v, s) = exec (compile g) (v, s).

(* Linear code doesn't duplicate values *)
Theorem compile_linear :
  ∀ e, quantity e = 1 → no_dup (compile e).
```

**Estimated effort:** ~500 lines of Coq per target.

## The Full Verification Stack

```
┌─────────────────────────────────────────────┐
│  Graded Category Theory                     │
│  - Semiring of quantities (0, 1, ω)         │
│  - Graded CCC structure                     │
│  (Builds on UniMath, agda-categories, etc.) │
└─────────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────┐
│  QTT Type System                            │
│  - Soundness (preservation + progress)      │
│  - Quantity inference correctness           │
│  (Based on Atkey, Idris 2 formalization)    │
└─────────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────┐
│  Optimizer Correctness                      │
│  - Each rewrite = graded categorical law    │
│  - Denotation preserved                     │
└─────────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────┐
│  Codegen Correctness                        │
│  - 12 generators → target semantics         │
│  - Quantities respected                     │
└─────────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────┐
│  Target Semantics                           │
│  - C: CompCert memory model                 │
│  - LLVM: Vellvm                             │
│  - WASM: Wasm formalization                 │
│  (Existing formalizations)                  │
└─────────────────────────────────────────────┘
```

## Existing Foundations to Build On

### Category Theory

| Library | Proof Assistant | Notes |
|---------|-----------------|-------|
| UniMath | Coq | Very mature |
| agda-categories | Agda | Mature |
| mathlib4 | Lean 4 | Mature |

### QTT

| Resource | Notes |
|----------|-------|
| Atkey's QTT paper | Foundational theory |
| Idris 2 | Working implementation |
| GraD (Granule) | Another QTT language |

### Verified Compilers

| Project | Relevant For |
|---------|--------------|
| CompCert | C backend semantics |
| CakeML | Full-stack compiler verification |
| Vellvm | LLVM semantics |

## Total Estimated Effort

| Component | Lines of Coq |
|-----------|--------------|
| Semiring + graded CCC | ~1000 |
| QTT type system | ~3000 |
| Quantity inference | ~1000 |
| Optimizer | ~500 |
| Codegen (one target) | ~500 |
| **Total** | **~5000-8000** |

Compare to CompCert: ~100,000 lines.

The math does the heavy lifting. Once is designed to be verifiable.

---

# Part II: Verifying Programs

## Design Principle

> The compiler compiles. External tools verify domain properties.

Once follows a **separation of concerns**:

- **Compiler** - Guarantees structural properties (types, quantities, effects)
- **External tools** - Prove domain-specific properties (sorted, secure, correct)

This keeps the compiler simple and verified, while enabling arbitrary verification when needed.

## What the Compiler Already Guarantees

If a program compiles, these hold **by construction**:

| Property | Enforced By |
|----------|-------------|
| Type correctness | Type checker |
| Quantity correctness | QTT inference |
| Linearity (^1) | Quantity = 1 |
| No hidden effects | Functor in type |
| Naturality | Parametricity |
| Categorical laws | Definitional |

No external proof needed for these. The compiler guarantees them.

## What External Tools Can Prove

Domain-specific properties require external verification:

| Property | Example | Tool |
|----------|---------|------|
| Sortedness | `Sorted (sort xs)` | Coq, Agda, Lean |
| Permutation | `Permutation xs (sort xs)` | Coq, Agda, Lean |
| Complexity | `O(n log n)` | Manual / Coq |
| Security | Constant-time | Specialized tools |
| Refinements | `x > 0` | SMT (Z3) |

## The Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     External Tools                              │
│                                                                 │
│   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐          │
│   │  Coq    │  │  Agda   │  │  Lean   │  │   Z3    │          │
│   │         │  │         │  │         │  │  (SMT)  │          │
│   └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘          │
│        └────────────┴─────┬──────┴────────────┘                │
│                           │                                     │
├───────────────────────────┼─────────────────────────────────────┤
│                    Categorical IR                               │
│                   (exchange format)                             │
├───────────────────────────┼─────────────────────────────────────┤
│                    Once Compiler                                │
│               QTT + NT → IR → Target                           │
└─────────────────────────────────────────────────────────────────┘
```

The Categorical IR is the interface between Once and external tools.

## Workflow 1: Compiler Only (Most Code)

For most code, compiler guarantees are sufficient:

```
-- Write Once
parseJson : String^1 → (Json + ParseError)^1
parseJson = ...

-- Compile
> once build

-- Done. Guaranteed:
--   ✓ Type correct
--   ✓ Linear (quantity 1)
--   ✓ No hidden effects
--   ✓ Compiles to any target
```

No external tools needed.

## Workflow 2: Proof Export (Critical Code)

For critical code, export to a proof assistant:

```
-- Write Once
sort : List Int → List Int
sort = ...

-- Export
> once export --coq sort.once -o Sort.v
```

Generated Coq:

```coq
(* Auto-generated from sort.once *)

Require Import Once.Prelude.

Definition sort : list Z -> list Z :=
  (* ... translated from IR ... *).

(* Proof obligations - user completes *)
Theorem sort_sorted : forall xs, Sorted (sort xs).
Proof.
  (* YOUR PROOF HERE *)
Admitted.

Theorem sort_permutation : forall xs, Permutation xs (sort xs).
Proof.
  (* YOUR PROOF HERE *)
Admitted.
```

User completes proofs. Coq verifies. Mathematical certainty achieved.

## Workflow 3: SMT Checking (Decidable Properties)

For decidable properties, SMT solvers verify automatically:

```
-- Refinement specification
-- @require: all (> 0) xs
-- @ensure: result > 0
sum_positive : List Int → Int
sum_positive = ...

-- Check
> once check --smt sum_positive.once

  Translating to SMT-LIB...
  Calling Z3...
  ✓ All refinements verified
```

No manual proof. SMT solver handles it.

### SMT Limitations

SMT works for:
- Linear arithmetic
- Uninterpreted functions
- Arrays, bitvectors
- Simple inductive facts

SMT does NOT work for:
- Complex recursion
- Higher-order properties
- Undecidable theories

For those, use proof assistants.

## Workflow 4: Property Testing (Fast Feedback)

For development, property testing gives quick feedback:

```
> once test sort \
    --property "sorted (sort xs)" \
    --property "length (sort xs) == length xs" \
    --samples 10000

  ✓ sorted (sort xs): 10000/10000 passed
  ✓ length (sort xs) == length xs: 10000/10000 passed
```

Not a proof, but fast and catches bugs.

## The Verification Spectrum

```
Weaker ◄─────────────────────────────────────────────► Stronger
(faster)                                               (slower)

Property        SMT              Proof
Testing         Solving          Assistants

"Probably       "Definitely      "Mathematically
 correct"        correct          certain"
                (decidable
                 fragment)"
```

Choose based on needs:
- Development: property testing
- Production: SMT for decidable, proofs for critical
- Safety-critical: full proofs

## Summary

| Concern | Approach |
|---------|----------|
| **Compiler verification** | ~5-8K Coq, graded categorical laws |
| **Program verification** | External tools via Categorical IR |
| **Structural properties** | Compiler guarantees by construction |
| **Domain properties** | Coq/Agda/Lean/SMT as needed |
| **Philosophy** | Simple verified core + composable tools |

The Once compiler is **small and verified**. Domain verification uses **external tools** through **clean interfaces**. Each part does one thing well.
