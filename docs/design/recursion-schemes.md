# Recursion Schemes

## Overview

Recursion schemes provide structured patterns for working with recursive data types. In Once, they live in the Initial library alongside the data types they operate on (`List`, `Maybe`, `Result`, etc.).

The key insight: recursive data types are **fixed points of functors**, and operations on them follow universal patterns called catamorphisms (folds) and anamorphisms (unfolds).

## Fixed Points and Functors

A recursive data type can be viewed as a fixed point:

```
-- List is the fixed point of this functor
ListF A X = Unit + (A * X)

-- Meaning: a list is either empty (Unit) or a head (A) and a tail (X)
-- The recursion comes from X referring back to the whole structure

List A = Fix (ListF A)
```

The `Fix` type ties the recursive knot:

```
Fix : (Type -> Type) -> Type
Fix F = F (Fix F)
```

## Catamorphism: Structured Folding

A catamorphism (from Greek "downward") collapses a recursive structure:

```
cata : (F A -> A) -> Fix F -> A
```

The function `F A -> A` is called an **algebra**. It specifies how to combine one layer of structure into a result.

### List Example

For lists, the algebra handles two cases:

```
-- The functor
ListF A X = Unit + (A * X)

-- An algebra to sum a list of integers
sumAlg : ListF Int Int -> Int
sumAlg = case (const 0) (\(head, tailSum) -> add head tailSum)
--            ^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--            empty case    cons case: head + recursive result

-- Usage
sum : List Int -> Int
sum = cata sumAlg
```

The catamorphism handles the recursion; the algebra handles one layer.

### Standard List Operations as Catamorphisms

| Operation | Algebra |
|-----------|---------|
| `sum` | `case (const 0) (uncurry add)` |
| `length` | `case (const 0) (\(_, n) -> n + 1)` |
| `foldr f z` | `case (const z) (uncurry f)` |
| `map f` | `case (const nil) (\(a, as) -> cons (f a) as)` |

## Anamorphism: Structured Unfolding

An anamorphism (from Greek "upward") builds a recursive structure from a seed:

```
ana : (A -> F A) -> A -> Fix F
```

The function `A -> F A` is called a **coalgebra**. It produces one layer of structure.

### Stream Example

Streams are infinite, so they use coalgebras:

```
-- Stream functor (always has a head and tail)
StreamF A X = A * X

-- Coalgebra to generate natural numbers
natsCoalg : Int -> StreamF Int Int
natsCoalg n = (n, n + 1)
--            ^^  ^^^^^
--            head  seed for next iteration

-- Usage
nats : Stream Int
nats = ana natsCoalg 0
-- Produces: 0, 1, 2, 3, ...
```

### Finite Unfolding

For finite structures, the coalgebra can signal termination:

```
-- List coalgebra returns Unit (done) or continues
rangeCoalg : Int * Int -> ListF Int (Int * Int)
rangeCoalg (lo, hi) =
  if lo >= hi
    then inl unit              -- empty, done
    else inr (lo, (lo + 1, hi)) -- emit lo, continue

-- Usage
range : Int -> Int -> List Int
range lo hi = ana rangeCoalg (lo, hi)
-- range 1 4 produces: [1, 2, 3]
```

## Hylomorphism: Unfold Then Fold

A hylomorphism combines an anamorphism and catamorphism:

```
hylo : (F B -> B) -> (A -> F A) -> A -> B
hylo alg coalg = cata alg . ana coalg
```

This pattern appears constantly: build a structure, then immediately consume it.

### Factorial Example

```
-- Build a list of numbers to multiply, then multiply them
factorial : Int -> Int
factorial = hylo productAlg countdownCoalg

-- Coalgebra: generate [n, n-1, ..., 1]
countdownCoalg : Int -> ListF Int Int
countdownCoalg n =
  if n <= 0
    then inl unit
    else inr (n, n - 1)

-- Algebra: multiply the list
productAlg : ListF Int Int -> Int
productAlg = case (const 1) (uncurry multiply)
```

### The Optimization Opportunity

The naive implementation allocates an intermediate list:

```
factorial n = product (countdown n)  -- allocates list
```

But a hylomorphism can **fuse** the operations:

```
factorial n = hylo productAlg countdownCoalg n  -- no intermediate list
```

The compiler can recognize `cata alg . ana coalg` and transform it to `hylo alg coalg`, eliminating the intermediate structure entirely.

## Paramorphism: Folding with Context

A paramorphism gives the algebra access to the original subtree, not just the recursive result:

```
para : (F (Fix F * A) -> A) -> Fix F -> A
```

Useful when you need to inspect the original structure during folding.

### Example: Safe Tail

```
-- Get tail, returning empty list if input is empty
safeTail : List A -> List A
safeTail = para tailAlg

tailAlg : ListF A (List A * List A) -> List A
tailAlg = case (const nil) (\(_, (originalTail, _)) -> originalTail)
--                          ^^^^^^^^^^^^^^^^^^^^
--                          access to original subtree
```

## Implementation in Once

These schemes are derived from the generators:

```
-- Catamorphism uses case and recursion
cata : (F A -> A) -> Fix F -> A
cata alg (Fix fa) = alg (fmap (cata alg) fa)

-- Anamorphism uses pair and recursion
ana : (A -> F A) -> A -> Fix F
ana coalg seed = Fix (fmap (ana coalg) (coalg seed))

-- Hylomorphism composes them (or fuses directly)
hylo : (F B -> B) -> (A -> F A) -> A -> B
hylo alg coalg seed = alg (fmap (hylo alg coalg) (coalg seed))
```

All built from:
- `fmap` (functor mapping)
- `case` (sum elimination)
- `pair` (product introduction)
- `compose` (function composition)

## Optimizer Integration

The Once optimizer can apply hylomorphism fusion:

```
-- Before (allocates intermediate structure)
compose (cata alg) (ana coalg)

-- After (fused, no intermediate)
hylo alg coalg
```

This is a straightforward rewrite rule added to the existing categorical law rewrites.

## Initial Library Placement

Recursion schemes belong in the Initial library alongside the data types:

```
Initial/
├── Bool.once
├── Maybe.once
├── Result.once
├── List.once
├── Fix.once          -- Fixed point type
└── Recursion.once    -- cata, ana, hylo, para
```

They're pure derived code - no new generators needed.

## Summary

| Scheme | Type | Pattern |
|--------|------|---------|
| `cata` | `(F A -> A) -> Fix F -> A` | Fold structure |
| `ana` | `(A -> F A) -> A -> Fix F` | Build structure |
| `hylo` | `(F B -> B) -> (A -> F A) -> A -> B` | Build then fold |
| `para` | `(F (Fix F * A) -> A) -> Fix F -> A` | Fold with context |

Recursion schemes separate:
- **What** to compute (the algebra/coalgebra)
- **How** to recurse (the scheme itself)

This separation enables:
- Clearer code (non-recursive algebras are simpler)
- Optimization (fusion eliminates intermediate structures)
- Verification (schemes have known laws)
