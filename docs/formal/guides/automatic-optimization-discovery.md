# Automatic Discovery of Optimization Rules

This document explores how the simplicity of Once's CCC-based IR enables automatic discovery of deforestation and fusion rules.

## Table of Contents

1. [Why CCC Makes This Tractable](#why-ccc-makes-this-tractable)
2. [Enumerate and Test](#enumerate-and-test)
3. [E-Graph Saturation](#e-graph-saturation)
4. [Cost-Directed Search](#cost-directed-search)
5. [Implementation Sketch](#implementation-sketch)
6. [Related Work](#related-work)

## Why CCC Makes This Tractable

The Once IR is built from a small set of categorical generators:

```agda
-- Category
id      : A → A
_∘_     : (B → C) → (A → B) → (A → C)

-- Products
fst     : A × B → A
snd     : A × B → B
⟨_,_⟩   : (C → A) → (C → B) → (C → A × B)

-- Coproducts
inl     : A → A + B
inr     : B → A + B
[_,_]   : (A → C) → (B → C) → (A + B → C)

-- Exponentials
curry   : (A × B → C) → (A → B ⇒ C)
apply   : (A ⇒ B) × A → B

-- Terminal/Initial
terminal : A → Unit
initial  : Void → A

-- Fixed Points
fold    : F (Fix F) → Fix F
unfold  : Fix F → F (Fix F)
```

**Key properties enabling automation:**

1. **Small generator set** (~15 constructors)
2. **Types constrain composition** - can't compose arbitrary terms
3. **Clear denotational semantics** - equivalence is well-defined
4. **Proofs often trivial** - many equalities are definitional (`refl`)

Compare to general-purpose IRs with hundreds of instructions and complex semantics - the CCC is orders of magnitude simpler.

## Enumerate and Test

The most direct approach: generate terms and test for equivalence.

### Algorithm

```
1. Fix a type signature (e.g., (A + B) × C → D)
2. Enumerate all well-typed IR terms up to depth N
3. For each pair of distinct terms:
   a. Test on random/exhaustive inputs
   b. If outputs always match, flag as candidate equivalence
4. Review candidates, attempt proofs
```

### Why This Works

For small types and bounded depth, the search space is manageable:

| Type | Depth 3 | Depth 4 | Depth 5 |
|------|---------|---------|---------|
| A × B → A | ~5 | ~20 | ~100 |
| (A + B) → C | ~10 | ~50 | ~300 |
| A × B → C × D | ~20 | ~200 | ~2000 |

Types heavily prune the space - most random compositions don't type-check.

### Testing Strategy

For ground types (Unit, Void, Int), use concrete values:

```haskell
testEquiv :: IR a b -> IR a b -> [a] -> Bool
testEquiv f g inputs = all (\x -> eval f x == eval g x) inputs
```

For polymorphic types, instantiate with small concrete types and test.

## E-Graph Saturation

E-graphs represent equivalence classes of terms efficiently.

### Approach

```
1. Start with known equalities as bidirectional rewrite rules:
   - fst ∘ ⟨f, g⟩  ↔  f
   - [f, g] ∘ inl  ↔  f
   - fold ∘ unfold  ↔  id
   - etc.

2. Add terms of interest to the e-graph

3. Saturate: apply all rules in all directions until fixed point

4. Extract: for each equivalence class, find the "cheapest" term
```

### Cost Model for Deforestation

Define allocation cost:

```
cost(id) = 0
cost(fst) = 0
cost(snd) = 0
cost(⟨f, g⟩) = 1 + cost(f) + cost(g)   -- pair allocation
cost(inl) = 1                            -- sum allocation
cost(inr) = 1
cost([f, g]) = cost(f) + cost(g)
cost(curry f) = 1 + cost(f)              -- closure allocation
cost(fold) = 1                           -- recursive structure
...
```

Terms with lower cost allocate fewer intermediate structures.

### Discovery Process

```
1. For a term T with cost C
2. Find all equivalent terms via e-graph
3. If any equivalent term T' has cost C' < C
4. Then T → T' is a deforestation rule
```

### Tools

- **egg** (Rust): Fast e-graph library with extraction
- **hegg** (Haskell): Haskell port of egg
- Could implement in Agda with reflection

## Cost-Directed Search

Directly search for cheaper equivalents.

### Algorithm

```
1. Given term T of type A → B with cost C
2. Enumerate all terms of type A → B with cost < C
3. For each candidate T':
   a. Test equivalence T ≡ T'
   b. If equivalent, found optimization: T → T'
```

### Guided Search

Use the structure of T to guide search:

```
-- If T contains ⟨f, g⟩ followed by fst/snd
-- Search for equivalent without the pair

-- If T contains [f, g] with inl/inr
-- Search for equivalent without the case

-- If T contains fold ... unfold
-- Search for equivalent without building Fix F
```

### Example Discovery

```
Input term:  fst ∘ ⟨ f ∘ g , h ⟩
Cost:        1 (one pair allocation)

Search terms of type A → B with cost 0:
  - f ∘ g  (no allocation)

Test: eval (fst ∘ ⟨ f ∘ g , h ⟩) x  ==  eval (f ∘ g) x
Result: Equal!

Discovered rule: fst ∘ ⟨ f ∘ g , h ⟩  →  f ∘ g
(This is just the beta law, but discovered automatically)
```

## Implementation Sketch

### Term Generator (Agda)

```agda
-- Generate all terms of a type up to depth n
generate : (A B : Type) → ℕ → List (IR A B)
generate A .A zero = [ id ]
generate A B (suc n) =
  -- Compositions
  concat [ [ g ∘ f | f ← generate A C n , g ← generate C B n ]
         | C ← allTypes ]
  ++
  -- Products (if B = B₁ × B₂)
  (case B of
    B₁ * B₂ → [ ⟨ f , g ⟩ | f ← generate A B₁ n , g ← generate A B₂ n ]
    _ → [])
  ++
  -- ... other constructors
```

### Equivalence Tester (Haskell)

```haskell
-- Test equivalence on random inputs
testEquiv :: IR a b -> IR a b -> Gen Bool
testEquiv f g = do
  inputs <- vectorOf 100 arbitrary
  return $ all (\x -> eval f x == eval g x) inputs

-- Find equivalent terms with lower cost
findCheaper :: IR a b -> [IR a b] -> [(IR a b, IR a b)]
findCheaper term candidates =
  [ (term, cand)
  | cand <- candidates
  , cost cand < cost term
  , runTests (testEquiv term cand)
  ]
```

### E-Graph Integration

```haskell
-- Using hegg or similar
import Data.EGraph

-- Add known equalities
rules :: [Rewrite IR]
rules =
  [ "beta-fst" :  fst :. pair f g  :=>  f
  , "beta-snd" :  snd :. pair f g  :=>  g
  , "eta-pair" :  pair fst snd    :=>  id
  , "fold-unfold" : fold :. unfold :=> id
  -- ... all known laws
  ]

-- Saturate and extract cheapest
optimize :: IR a b -> IR a b
optimize term =
  let egraph = saturate rules (addTerm emptyEGraph term)
  in extractCheapest costFn egraph (classOf term)
```

## Related Work

### Equality Saturation

- Tate et al. "Equality Saturation: A New Approach to Optimization" (2009)
- Willsey et al. "egg: Fast and Extensible Equality Saturation" (2021)

E-graphs efficiently represent and explore equivalence classes. The `egg` library has been used to discover optimizations in various domains.

### Supercompilation

- Turchin "The concept of a supercompiler" (1986)
- Mitchell "Rethinking Supercompilation" (2010)

Supercompilation drives programs symbolically, generalizes, and folds back. Can discover optimizations that local rewriting misses.

### Term Rewriting and Completion

- Knuth-Bendix completion algorithm
- Automated discovery of confluent rewrite systems

Given equations, automatically derive a terminating, confluent rewrite system.

### Property-Based Testing for Laws

- QuickSpec: Automatically discovers algebraic laws by testing
- Speculate: Similar approach in Haskell

Generate candidate laws, test exhaustively, filter to minimal set.

### CCC-Specific

The categorical structure provides:
- Well-defined universal properties (uniqueness of mediating morphisms)
- Coherence theorems (all diagrams commute)
- Clear cost model (allocating constructors)

This makes automatic discovery more feasible than in ad-hoc IRs.

## Practical Next Steps

1. **Quick win**: Implement term generator for small types, test pairs exhaustively
2. **Medium effort**: Integrate with e-graph library for saturation
3. **Research project**: Full supercompilation over CCC terms

The CCC's simplicity makes this a tractable research direction. Even a simple enumerate-and-test approach could discover rules we missed.
