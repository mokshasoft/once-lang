# Optimization Strategies for Once

This document describes Once's optimization architecture, implemented optimizations, and future directions including fusion/deforestation.

## Table of Contents

1. [Optimization Architecture](#optimization-architecture)
2. [Implemented Optimizations](#implemented-optimizations)
3. [Escape Analysis](#escape-analysis)
4. [Fusion and Deforestation](#fusion-and-deforestation)
5. [Future Directions](#future-directions)
6. [References](#references)

## Optimization Architecture

### Rule-Based Rewriting

Once uses **rule-based rewriting** where each optimization rule is:
1. A pattern match on IR terms
2. A rewrite to an equivalent (but faster) IR term
3. A machine-checked proof of correctness in Agda

The architecture follows the categorical structure of the IR:

```agda
-- Optimize at composition points
optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C

-- Recursive descent through IR
optimize-once : ∀ {A B} → IR A B → IR A B

-- Bounded iteration to fixed point
optimize : ∀ {A B} → IR A B → IR A B
```

### Why Composition-Based Rules Work

The IR is built from categorical combinators where composition (`_∘_`) is the fundamental way to combine operations. Most optimization opportunities appear at composition points:

```agda
-- Identity laws
id ∘ f = f
f ∘ id = f

-- Beta laws (computation)
fst ∘ ⟨ f , g ⟩ = f
snd ∘ ⟨ f , g ⟩ = g
[ f , g ] ∘ inl = f
[ f , g ] ∘ inr = g
apply ∘ ⟨ curry f , g ⟩ = f ∘ ⟨ id , g ⟩

-- Eta laws (uniqueness)
⟨ fst , snd ⟩ = id
[ inl , inr ] = id

-- Fixed point isomorphism
fold ∘ unfold = id
unfold ∘ fold = id
```

### Proof Strategy

All proofs follow a uniform pattern:

1. **Pattern correctness**: Show `eval (optimized-pattern) x ≡ eval (original-pattern) x`
2. **Recursive correctness**: Show `eval (optimize-once f) x ≡ eval f x`
3. **Iteration correctness**: Show `eval (optimize f) x ≡ eval f x`

Most proofs are `refl` (definitional equality) because the semantics are defined to make the laws hold:

```agda
-- From Once/Semantics.agda
eval fst (a , b) = a
eval (⟨ f , g ⟩ _) x = (eval f x , eval g x)

-- Therefore: eval (fst ∘ ⟨ f , g ⟩) x = eval f x  by definition!
```

## Implemented Optimizations

### Category Laws

**Identity elimination:**
```agda
id ∘ f  →  f
f ∘ id  →  f
```

These eliminate redundant identity morphisms from generated code.

### Product Laws (Beta)

**Projection fusion:**
```agda
fst ∘ ⟨ f , g ⟩  →  f
snd ∘ ⟨ f , g ⟩  →  g
```

Eliminates pair allocation when only one component is used.

**Pairing distribution:**
```agda
⟨ f , g ⟩ ∘ h  →  ⟨ f ∘ h , g ∘ h ⟩
```

Exposes further optimization opportunities.

### Product Laws (Eta)

**Pair reconstruction:**
```agda
⟨ fst , snd ⟩  →  id
⟨ fst ∘ h , snd ∘ h ⟩  →  h
```

Eliminates redundant pair deconstruction/reconstruction.

### Coproduct Laws (Beta)

**Case elimination:**
```agda
[ f , g ] ∘ inl  →  f
[ f , g ] ∘ inr  →  g
```

Eliminates sum allocation when the branch is statically known.

**Case distribution:**
```agda
h ∘ [ f , g ]  →  [ h ∘ f , h ∘ g ]
```

Pushes computation into branches.

### Coproduct Laws (Eta)

**Case reconstruction:**
```agda
[ inl , inr ]  →  id
[ h ∘ inl , h ∘ inr ]  →  h
```

Eliminates redundant case analysis.

### Exponential Beta Law

**Closure elimination:**
```agda
apply ∘ ⟨ curry f , g ⟩  →  f ∘ ⟨ id , g ⟩
```

This is a **high-impact optimization**. When a curried function is immediately applied, the closure allocation is eliminated entirely. The function body `f` is directly composed with the argument, avoiding:
- Closure heap allocation
- Environment capture
- Indirect function call

Example impact:
```
-- Before: allocates closure, then calls it
let f = λx. x + 1 in f 5

-- After: direct computation, no closure
5 + 1
```

### Terminal/Initial Absorption

**Dead code elimination:**
```agda
terminal ∘ f  →  terminal    -- Result discarded
f ∘ initial  →  initial       -- Input is impossible
```

Eliminates unreachable code.

### Fixed Point Laws

**Wrap/unwrap elimination:**
```agda
fold ∘ unfold  →  id
unfold ∘ fold  →  id
```

Eliminates redundant recursive type wrapping.

## Escape Analysis

### Purpose

Escape analysis identifies allocations that don't "escape" their immediate context and can be stack-allocated instead of heap-allocated.

### AllocMode Annotation

The IR includes allocation mode annotations:

```agda
data AllocMode : Set where
  Stack : AllocMode  -- Safe for stack allocation
  Heap  : AllocMode  -- Must use heap allocation

-- Allocating constructors carry AllocMode
⟨_,_⟩ : IR C A → IR C B → AllocMode → IR C (A * B)
inl   : AllocMode → IR A (A + B)
inr   : AllocMode → IR B (A + B)
curry : IR (A * B) C → AllocMode → IR A (B ⇒ C)
```

### Key Insight: Semantic Transparency

AllocMode is **ignored in the semantics**:

```agda
eval (⟨ f , g ⟩ _) x = (eval f x , eval g x)  -- _ ignores mode
```

This means all escape analysis rewrites are trivially correct by `refl`.

### Escape Analysis Rules

Rules identify patterns where allocations are immediately consumed:

| Rule | Pattern | Rewrite | Rationale |
|------|---------|---------|-----------|
| 1 | `fst ∘ ⟨ f , g ⟩ m` | `fst ∘ ⟨ f , g ⟩ Stack` | Pair consumed by fst |
| 2 | `snd ∘ ⟨ f , g ⟩ m` | `snd ∘ ⟨ f , g ⟩ Stack` | Pair consumed by snd |
| 3 | `[ f , g ] ∘ inl m` | `[ f , g ] ∘ inl Stack` | Injection consumed by case |
| 4 | `[ f , g ] ∘ inr m` | `[ f , g ] ∘ inr Stack` | Injection consumed by case |
| 5 | `apply ∘ ⟨ curry f _ , x ⟩ _` | `apply ∘ ⟨ curry f Stack , x ⟩ Stack` | Closure + pair immediately applied |
| 6 | `fold ∘ inl/inr m` | `fold ∘ inl/inr Stack` | Injection consumed by fold |
| 7 | `terminal ∘ ⟨ f , g ⟩ m` | `terminal ∘ ⟨ f , g ⟩ Stack` | Pair discarded |
| 8 | `(f ∘ fst/snd) ∘ ⟨ g , h ⟩ m` | `(f ∘ fst/snd) ∘ ⟨ g , h ⟩ Stack` | Pair consumed by projection |

### Let Binding Optimization

Rule 8 is particularly impactful for let bindings. The desugaring:

```
let x = e in body   →   (body[x := snd] ∘ snd) ∘ ⟨ id , e ⟩
```

With escape analysis, the pair created for the let binding is stack-allocated.

### Interaction with Unboxing

For maximum benefit, escape analysis should combine with unboxed representation:

| Boxing | Escape | Benefit |
|--------|--------|---------|
| Boxed | Stack | Saves pointer pair allocation (~16 bytes) |
| Unboxed | Stack | Saves entire data structure (significant!) |

See `allocation-strategies-and-escape-analysis.md` for details.

## Fusion and Deforestation

### The Problem: Intermediate Data Structures

Functional programs often create intermediate data structures that are immediately consumed:

```haskell
-- Creates two intermediate lists
sum (map (+1) (filter even xs))
```

**Deforestation** (or **fusion**) eliminates these intermediates by fusing producer-consumer pairs.

### Once's Fix Type

Once represents recursive types using `Fix F`:

```agda
Fix F ≅ F (Fix F)    -- Isomorphism via fold/unfold

fold   : F (Fix F) → Fix F    -- Constructor (wrap)
unfold : Fix F → F (Fix F)    -- Destructor (unwrap)
```

For example, lists are:
```agda
List A = Fix (Unit + (A × _))
-- Unfolded: Unit + (A × List A)
--           nil  | cons
```

### Recursion Schemes

**Catamorphism** (fold): Consumes a recursive structure
```agda
cata : (F A → A) → Fix F → A
cata alg = alg ∘ fmap (cata alg) ∘ unfold
```

**Anamorphism** (unfold): Produces a recursive structure
```agda
ana : (A → F A) → A → Fix F
ana coalg = fold ∘ fmap (ana coalg) ∘ coalg
```

**Hylomorphism**: Unfold then fold (the fusion target)
```agda
hylo : (F B → B) → (A → F A) → A → B
hylo alg coalg = cata alg ∘ ana coalg
```

### Fusion Law

The key fusion law eliminates intermediate `Fix F`:

```agda
cata alg ∘ ana coalg = hylo alg coalg
```

In terms of fold/unfold patterns:
```agda
fold ∘ ... ∘ unfold ∘ fold ∘ ... ∘ unfold
      ↓ fusion
fold ∘ ... ∘ unfold
```

### Implemented Fusion Rules

**Basic fold/unfold cancellation:**
```agda
fold ∘ unfold  →  id
unfold ∘ fold  →  id
```

**Composition through fold/unfold:**
```agda
fold ∘ (unfold ∘ f)  →  f
unfold ∘ (fold ∘ f)  →  f
```

**Coproduct functor fusion** (deforestation for sum types):
```agda
-- Right functor fusion: fmap h ∘ fmap k = fmap (h ∘ k)
[ inl, inr ∘ h ] ∘ [ inl, inr ∘ k ]  →  [ inl, inr ∘ (h ∘ k) ]

-- Left functor fusion
[ inl ∘ f, inr ] ∘ [ inl ∘ g, inr ]  →  [ inl ∘ (f ∘ g), inr ]

-- Bimap fusion: bimap f g ∘ bimap h k = bimap (f ∘ h) (g ∘ k)
[ inl ∘ f, inr ∘ g ] ∘ [ inl ∘ h, inr ∘ k ]  →  [ inl ∘ (f ∘ h), inr ∘ (g ∘ k) ]

-- Mixed fusion (4 additional rules for combinations)
```

These rules eliminate intermediate sum allocations when composing coproduct maps.

### Short-Cut Fusion

The GHC-style short-cut fusion uses `build/foldr`:

```haskell
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []

foldr :: (a -> b -> b) -> b -> [a] -> b

-- Fusion law:
foldr c n (build g) = g c n
```

In Once's categorical setting:
```agda
-- If: producer = fold ∘ k  for some k
-- And: consumer = alg ∘ unfold
-- Then: consumer ∘ producer = alg ∘ k
```

### Why Fusion is Safe in Once

Fusion preserves semantics because:
1. `fold` and `unfold` form an isomorphism
2. Composition is associative
3. The semantics are defined to make these laws hold

Proofs follow the standard pattern:
```agda
fusion-correct : ∀ f x → eval (fused f) x ≡ eval f x
fusion-correct f x = refl  -- or simple equational reasoning
```

## Future Directions

### Product Functor Fusion

Symmetric to coproduct fusion, we could add product functor fusion:

```agda
-- Product bimap fusion: bimap f g ∘ bimap h k = bimap (f ∘ h) (g ∘ k)
⟨ f ∘ fst, g ∘ snd ⟩ ∘ ⟨ h ∘ fst, k ∘ snd ⟩  →  ⟨ (f ∘ h) ∘ fst, (g ∘ k) ∘ snd ⟩
```

This would require detecting the "bimap" pattern and fusing compositions.

### Product Associativity Normalization

Normalize nested products to a canonical form:

```agda
-- Type isomorphism (not equality)
(A × B) × C  ≅  A × (B × C)
```

This requires working with type isomorphisms rather than simple rewrites, since the types differ. Could be useful for optimizing tuple-heavy code.

### Stream Fusion

Instead of fusing list operations directly, convert to a stream representation that fuses naturally:

```agda
data Stream a = ∃s. Stream (s → Step a s) s
data Step a s = Done | Skip s | Yield a s
```

Stream operations compose without intermediate allocation, then a final `unstream` produces the result.

### Supercompilation

Supercompilation performs aggressive program transformation:
1. Driving: Unfold function calls
2. Generalization: Abstract common patterns
3. Folding: Recognize recursive patterns

This can discover optimizations that simple rewriting misses.

### Partial Evaluation

Specialize programs based on known static inputs:

```agda
-- Generic power function
power : Nat → Int → Int
power 0 x = 1
power (n+1) x = x * power n x

-- Specialized for n=3
power3 : Int → Int
power3 x = x * x * x
```

### Call Pattern Specialization

Create specialized versions of functions for common call patterns:

```agda
-- Generic map
map : (A → B) → List A → List B

-- Specialized when f is known
map_f : List A → List B
map_f = map f
```

This eliminates closure allocation for the function argument.

### Verified Rewriting Engines

Use Agda's reflection capabilities to automate proof generation:

```agda
-- Automatically derive:
-- optimize-correct : eval (optimize f) ≡ eval f
-- from the rewrite rules
```

## References

### Files

- `formal/Once/Optimize.agda` - Main optimizer
- `formal/Once/Optimize/Correct.agda` - Correctness proofs
- `formal/Once/Escape.agda` - Escape analysis
- `formal/Once/Escape/Correct.agda` - Escape analysis proofs
- `formal/Once/IR.agda` - IR definition with AllocMode
- `formal/Once/Semantics.agda` - Denotational semantics

### Papers

**Deforestation:**
- Wadler, P. (1988). "Deforestation: Transforming programs to eliminate trees"
- Gill, A., Launchbury, J., & Peyton Jones, S. (1993). "A short cut to deforestation"

**Fusion:**
- Coutts, D., Leshchinskiy, R., & Stewart, D. (2007). "Stream Fusion: From Lists to Streams to Nothing at All"
- Farmer, A. et al. (2014). "The HERMIT in the Machine"

**Recursion Schemes:**
- Meijer, E., Fokkinga, M., & Paterson, R. (1991). "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire"

**Modern Approaches:**
- Graf, S. et al. (2024). "Lumberhack: Deforestation using Graph Rewriting" (ICFP 2024)

### Category Theory Background

The optimization laws derive from the structure of a **Cartesian Closed Category**:

- Products have universal property (pair eta/beta)
- Coproducts have universal property (case eta/beta)
- Exponentials satisfy the adjunction (curry/apply)
- Initial algebras give recursion (fold/unfold)

Understanding these structures helps identify which laws are available for optimization.
