# CCC Compiler Theory: Fixpoint, Correctness, and Uniqueness

This document develops the theoretical foundations for building a self-hosting compiler based on Cartesian Closed Categories (CCC), connecting the fixpoint property to compiler correctness and bootstrapping.

## 1. The Setup

### 1.1 CCC Terms as a Universal Language

We work with terms in a Cartesian Closed Category with 12 generators:

```
Term A B ::= id                    -- identity
           | f ∘ g                 -- composition
           | fst | snd             -- projections
           | ⟨f, g⟩                -- pairing
           | inl | inr             -- injections
           | [f, g]                -- case analysis
           | terminal              -- unit introduction
           | initial               -- void elimination
           | curry f | apply       -- exponentials
           | In | Out              -- fixed points (μ)
           | cata F alg            -- catamorphism
```

This is a complete internal language for computation - anything computable can be expressed as a CCC term.

### 1.2 Self-Representation via Encoding

The crucial insight is that CCC terms can encode themselves:

```agda
encode : Term A B → Term Unit TermCode'
```

Where `TermCode' = μ TermF` is the fixed point of the term functor:

```agda
TermF = K TyCode                           -- id (position 0)
      ⊕ (Id ⊗ Id)                          -- ∘  (position 1)
      ⊕ (K TyCode ⊗ K TyCode)              -- fst, snd, inl, inr, etc.
      ⊕ ...                                -- remaining constructors
```

This encoding is:
- **Injective**: Different terms have different encodings
- **Computable**: `encode` is itself a CCC term
- **Universal**: Every term can represent any other term as data

### 1.3 Catamorphisms as Interpreters

A catamorphism `cata F alg` folds over a recursive structure using an algebra:

```agda
cata F alg : Term (μ F) A
alg : Term (⟦ F ⟧F A) A
```

The β-rule for catamorphisms:
```
cata F alg ∘ In ⟶ alg ∘ fmap F (cata F alg)
```

This says: to process a recursive structure, first recursively process all subterms, then apply the algebra.

## 2. The Identity Algebra and Refold

### 2.1 The Refold Operation

The simplest algebra is the identity algebra `In`:

```agda
N-refold : Term TermCode' TermCode'
N-refold = cata TermF In
```

This "refolds" an encoded term back into an identical encoding. It's the identity function on encoded terms, but crucially it *processes* the entire structure.

### 2.2 The Refold Fixpoint Theorem

**Theorem (Refold Idempotent):**
```agda
refold-idempotent : ∀ t → (N-refold ∘ encode t) ⟶* encode t
```

**Proof structure:**
- By structural induction on `t`
- For each constructor, show that `fmap TermF N-refold` applied to the encoded subterms reduces back to those subterms
- The `In` algebra then rebuilds the original encoding

**Corollary (Self-Application Fixpoint):**
```agda
N-refold-fixpoint : (N-refold ∘ encode N-refold) ⟶* encode N-refold
```

This is the specialization to `t = N-refold` itself.

### 2.3 What We Proved

The normalizer codebase establishes:

| Property | Statement | Status |
|----------|-----------|--------|
| Encoding correctness | `encode` produces valid `TermCode'` | ✓ Proven |
| Beta normal form | Encoded terms have no redexes | ✓ Proven |
| Refold idempotent | `N ∘ encode(t) ⟶* encode(t)` | ✓ Proven |
| Self-application | `N ∘ encode(N) ⟶* encode(N)` | ✓ Proven |

## 3. From Normalizer to Compiler

### 3.1 The Compiler Structure

A compiler is a catamorphism with a non-trivial algebra:

```agda
compile-algebra : Term (⟦ TermF ⟧F TargetCode) TargetCode
C : Term TermCode' TargetCode
C = cata TermF compile-algebra
```

The algebra specifies how to compile each term constructor given compiled subterms.

### 3.2 Compiler Correctness

**Definition (Semantic Preservation):**
A compiler `C` is correct if for all terms `t`:
```
⟦ C ∘ encode(t) ⟧ = ⟦ t ⟧
```

Where `⟦_⟧` denotes denotational semantics.

**Operational formulation:**
```agda
compile-correct : ∀ t → (C ∘ encode t) ⟶* encode (compile t)
  where compile t ≈ t  -- semantic equivalence
```

### 3.3 Optimizing Compiler

For an optimizing compiler, `compile t` is a *simpler* but equivalent term:

```agda
optimize : Term A B → Term A B
optimize-sound : ∀ t → optimize t ≈ t
optimize-simpler : ∀ t → complexity (optimize t) ≤ complexity t
```

The compiler correctness becomes:
```agda
C-correct : ∀ t → (C ∘ encode t) ⟶* encode (optimize t)
```

## 4. Self-Hosting and Bootstrapping

### 4.1 Self-Hosting Property

**Definition:** A compiler `C` is self-hosting if:
```agda
C ∘ encode(C) ⟶* encode(C')
```
where `C'` is a valid compiler (behaviorally equivalent to `C`).

### 4.2 The Bootstrapping Tower

Starting from an externally-verified compiler `C₀`:

```
C₀ : Term TermCode' TargetCode     -- initial compiler (trusted)
C₁ = C₀(encode(C₀))                -- first self-compilation
C₂ = C₁(encode(C₁))                -- second self-compilation
...
```

**Fixpoint Theorem:**
If the compiler correctly implements itself, then:
```
Cₙ₊₁ = Cₙ  for all n ≥ 1
```

The tower stabilizes after one self-compilation.

### 4.3 Why Fixpoint Matters

The fixpoint property provides:

1. **Trust amplification**: Once `C₁ = C₀(encode(C₀))` is verified equivalent to `C₀`, we trust the self-hosted compiler.

2. **Bootstrapping correctness**: The compiler doesn't "drift" with repeated self-application.

3. **Compiler verification**: To verify `C`, we only need to verify `C₀` and prove the fixpoint property.

## 5. Uniqueness and Canonicity

### 5.1 Canonical Forms

**Definition:** A term is in canonical form if it has no redexes and is maximally simplified.

**Theorem (Canonicity):**
For a normalizing compiler `N`:
```agda
canonical : ∀ t → IsCanonical (normalize t)
idempotent : ∀ t → N ∘ encode(N ∘ encode(t)) ⟶* N ∘ encode(t)
```

### 5.2 Uniqueness of Normal Forms

If the reduction system is confluent:
```agda
confluence : t ⟶* u → t ⟶* v → ∃ w. u ⟶* w × v ⟶* w
```

Then normal forms are unique:
```agda
unique-nf : IsNF u → IsNF v → t ⟶* u → t ⟶* v → u ≡ v
```

### 5.3 Compiler Determinism

For a deterministic compiler:
```agda
C-deterministic : (C ∘ encode t) ⟶* u → (C ∘ encode t) ⟶* v → u ≡ v
```

This follows from confluence of the underlying reduction system.

## 6. The Full Picture

### 6.1 What We Have (Normalizer)

```
┌─────────────────────────────────────────────────────────┐
│  Term A B                                               │
│     │                                                   │
│     │ encode                                            │
│     ▼                                                   │
│  Term Unit TermCode'  ─────────────────────────────────│
│     │                         │                         │
│     │ N = cata TermF In       │ (identity)             │
│     ▼                         ▼                         │
│  Term Unit TermCode'  ═══════════════════              │
│                       (same encoding)                   │
│                                                         │
│  Fixpoint: N ∘ encode(N) ⟶* encode(N)                  │
└─────────────────────────────────────────────────────────┘
```

### 6.2 What We Want (Compiler)

```
┌─────────────────────────────────────────────────────────┐
│  Term A B                                               │
│     │                                                   │
│     │ encode                                            │
│     ▼                                                   │
│  Term Unit TermCode'  ─────────────────────────────────│
│     │                         │                         │
│     │ C = cata TermF alg      │ (compile)              │
│     ▼                         ▼                         │
│  Term Unit TargetCode ═══════════════════              │
│                       (optimized/compiled)              │
│                                                         │
│  Correctness: ⟦ C ∘ encode(t) ⟧ = ⟦ t ⟧               │
│  Fixpoint: C ∘ encode(C) ⟶* encode(C')                 │
│            where C' ≈ C                                 │
└─────────────────────────────────────────────────────────┘
```

### 6.3 The Path Forward

1. **Define the target**: What is `TargetCode`? Options:
   - Same as `TermCode'` (normalizer/optimizer)
   - Different CCC (target machine model)
   - External representation (bytecode, machine code)

2. **Design the algebra**: `compile-algebra` must:
   - Handle each term constructor
   - Preserve semantics
   - Produce simpler/faster code

3. **Prove correctness**: By structural induction, show:
   ```agda
   compile-correct : ∀ t → (C ∘ encode t) ⟶* encode (compile t)
   ```

4. **Prove fixpoint**: Specialize to `t = C`:
   ```agda
   C-fixpoint : (C ∘ encode C) ⟶* encode C'
   ```

5. **Prove equivalence**: Show `C' ≈ C`:
   ```agda
   C-self-hosting : ∀ t → (C' ∘ encode t) ⟶* (C ∘ encode t)
   ```

## 7. Connection to Classical Results

### 7.1 Kleene's Recursion Theorem

The fixpoint property is an instance of Kleene's recursion theorem:

> For any computable function `f`, there exists a program `e` such that `φₑ = φ_{f(e)}`.

In our setting:
- `f` = the compiler transformation
- `e` = `encode(C)`
- `φₑ = C` (the compiler's behavior)
- The fixpoint says `C` compiled by `C` yields equivalent `C`

### 7.2 Futamura Projections

The three Futamura projections describe specialization:

1. `specialize(interpreter, program) = compiled_program`
2. `specialize(specializer, interpreter) = compiler`
3. `specialize(specializer, specializer) = compiler_generator`

Our framework naturally supports these:
- The interpreter is `eval = cata TermF eval-algebra`
- Specialization is partial evaluation via a specialized algebra
- Self-application yields the compiler generator

### 7.3 Quines and Self-Reference

A quine is a program that outputs its own source. Our fixpoint:

```
N ∘ encode(N) ⟶* encode(N)
```

is a "computational quine" - the normalizer applied to itself yields itself.

## 8. Summary

| Concept | Normalizer (done) | Compiler (goal) |
|---------|-------------------|-----------------|
| Operation | `cata TermF In` | `cata TermF compile-alg` |
| Fixpoint | `N ∘ enc(N) ⟶* enc(N)` | `C ∘ enc(C) ⟶* enc(C')` |
| Correctness | Identity | Semantic preservation |
| Self-hosting | Trivial (identity) | C' ≈ C |
| Uniqueness | Via confluence | Via determinism |

The normalizer work establishes the *structural* foundation. The compiler extends this with *semantic* content - the algebra does real work while preserving meaning.

The fixpoint property is not just a curiosity; it's the mathematical foundation for:
- Compiler correctness
- Bootstrapping trust
- Self-hosting verification
- Stable compiler towers
