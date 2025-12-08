# Alternative Categorical Foundations

## Beyond Natural Transformations

Once is built on natural transformations in a cartesian closed category. This is a powerful and well-understood foundation, but category theory offers many other abstractions that could complement or extend Once's design.

This document explores alternative categorical structures and their potential roles in a programming language with Once's design principles.

## Why Consider Alternatives?

Natural transformations in a CCC give us:
- Functions (morphisms)
- Products and coproducts (data structures)
- Higher-order functions (exponentials)
- Polymorphism (naturality)

But some computational patterns don't fit naturally:
- Bidirectional transformations (lenses, parsing/printing)
- Resource-aware computation (linear/affine types)
- Concurrent and distributed systems
- Incremental computation
- Reversible computation

## Optics: Bidirectional Access

### What Are Optics?

Optics generalize the idea of "focusing" on part of a data structure:

```
Lens s t a b     -- focus on one part
Prism s t a b    -- focus on one variant
Traversal s t a b -- focus on many parts
Iso s t a b      -- bidirectional isomorphism
```

### Categorical Foundation

Optics arise from **profunctor** theory:

```
type Optic p s t a b = p a b -> p s t
```

Different constraints on `p` give different optics:
- `Strong p => Lens`
- `Choice p => Prism`
- `Wander p => Traversal`

### Relevance to Once

Once already has the building blocks:
- `fst`, `snd` are weak lenses
- `inl`, `inr`, `case` are prisms

Optics could be a **derived** abstraction:

```
-- Lens as pair of get/set
type Lens S A = (S -> A) * (S * A -> S)

-- Van Laarhoven encoding (more composable)
type Lens S A = forall F. Functor F => (A -> F A) -> S -> F S

-- Usage
view : Lens S A -> S -> A
set  : Lens S A -> A -> S -> S
over : Lens S A -> (A -> A) -> S -> S
```

### Benefits

| Benefit | Description |
|---------|-------------|
| **Composable access** | `lens1 . lens2` focuses deeper |
| **Bidirectional** | Get and set in one abstraction |
| **Lawful** | Lens laws ensure consistency |
| **Efficient** | Can compile to direct field access |

## Profunctors: Generalized Functions

### What Are Profunctors?

A profunctor is a functor of two arguments, contravariant in the first:

```
class Profunctor p where
  dimap : (a' -> a) -> (b -> b') -> p a b -> p a' b'
```

Functions are profunctors:
```
dimap f g h = g . h . f
```

### Beyond Functions

Other profunctors capture different computational patterns:

| Profunctor | Meaning |
|------------|---------|
| `(->)` | Pure functions |
| `Kleisli m` | Effectful functions: `a -> m b` |
| `Star f` | Computations producing `f`: `a -> f b` |
| `Costar f` | Computations consuming `f`: `f a -> b` |
| `UpStar`, `DownStar` | Categorical lifting |

### Relevance to Once

Profunctors could unify:
- Pure transformations
- Parser/printer pairs
- Bidirectional codecs
- Protocol definitions

```
-- A codec is a profunctor
type Codec a b = (a -> Bytes) * (Bytes -> b + Error)

-- Composition works naturally
composeCodec : Codec b c -> Codec a b -> Codec a c
```

## Arrows: Generalized Computation

### What Are Arrows?

Arrows generalize functions with additional structure:

```
class Arrow a where
  arr    : (b -> c) -> a b c           -- lift function
  (>>>) : a b c -> a c d -> a b d     -- sequence
  first : a b c -> a (b * d) (c * d)  -- parallel
```

### Why Arrows?

Arrows capture computations that:
- Have static structure (circuits, dataflow)
- Need explicit sequencing
- Carry additional information

```
-- Signal functions (FRP)
type SF a b  -- continuous transformation

-- Circuits
type Circuit a b  -- with internal state

-- Parsers with static analysis
type StaticParser a b  -- can inspect without running
```

### Relevance to Once

Arrows could model:
- Hardware description (circuits)
- Dataflow programming
- Stream processing with static optimization

```
-- Arrow-based signal processing
lowpass  : Arrow a => Frequency -> a Signal Signal
highpass : Arrow a => Frequency -> a Signal Signal

-- Compose statically
bandpass : Arrow a => Frequency -> Frequency -> a Signal Signal
bandpass lo hi = lowpass hi >>> highpass lo
```

## Linear and Affine Categories

### The Resource Problem

Standard category theory allows:
- `diagonal : A -> A * A` (copying)
- `terminal : A -> Unit` (discarding)

But some resources can't be copied or discarded:
- File handles
- Network connections
- Unique tokens
- Linear memory

### Linear Categories

A **linear** category lacks diagonal and terminal:

```
-- NOT available in linear category:
diagonal : A -> A * A   -- no copying
terminal : A -> Unit    -- no discarding

-- Every value used exactly once
```

### Affine Categories

An **affine** category has terminal but not diagonal:

```
-- Available:
terminal : A -> Unit    -- can discard

-- NOT available:
diagonal : A -> A * A   -- no copying
```

### Relevance to Once

Once already mentions linearity as an **observable property**. This could be strengthened:

```
-- Types could carry linearity
Linear A    -- must use exactly once
Affine A    -- must use at most once
Relevant A  -- must use at least once
Unlimited A -- standard (can copy/discard)

-- Transformations respect linearity
linearMap : (Linear A -> Linear B) -> Linear (List A) -> Linear (List B)
```

See the [Memory](memory.md) document for detailed treatment of linear resources.

## Monoidal Categories and String Diagrams

### Beyond Cartesian Products

Cartesian categories have `diagonal` (copying) built in. **Monoidal** categories are more general:

```
-- Monoidal structure
tensor : A * B          -- combine (not necessarily cartesian product)
unit   : I              -- identity for tensor

-- Associativity and unit laws
assoc : (A * B) * C <-> A * (B * C)
leftUnit  : I * A <-> A
rightUnit : A * I <-> A
```

### String Diagrams

Monoidal categories have a **graphical** representation:

```
     A ─────┐     ┌───── C
            │ f   │
     B ─────┴─────┴───── D

-- f : A * B -> C * D
```

Composition is vertical stacking. Tensor is horizontal.

### Symmetric Monoidal Categories

Add `swap : A * B -> B * A`:

```
     A ───╲  ╱─── B
          ╲╱
          ╱╲
     B ───╱  ╲─── A
```

### Relevance to Once

String diagrams could provide:
- Visual programming interface
- Circuit design
- Dataflow visualization
- Quantum computing representation

```
-- Quantum circuit as string diagram
hadamard : Qubit -> Qubit
cnot     : Qubit * Qubit -> Qubit * Qubit

-- Bell state preparation
bell : Unit -> Qubit * Qubit
bell = (hadamard * id) >>> cnot >>> ...
```

## Polynomial Functors

### What Are Polynomials?

Polynomial functors are built from:
- Constants: `K_c(X) = c`
- Identity: `Id(X) = X`
- Sums: `(F + G)(X) = F(X) + G(X)`
- Products: `(F * G)(X) = F(X) * G(X)`

### Representing Data Types

Every algebraic data type is a polynomial functor:

```
-- Maybe A = 1 + A
Maybe = K_1 + Id

-- List A = 1 + A * List A  (fixed point)
ListF = K_1 + (Id * X)
List = Fix ListF

-- Binary tree
TreeF A = K_1 + (Id * A * Id)
Tree A = Fix (TreeF A)
```

### Derivatives and Zippers

The **derivative** of a polynomial functor gives its one-hole contexts:

```
∂(K_c) = K_0           -- constant has no holes
∂(Id) = K_1            -- identity has one hole
∂(F + G) = ∂F + ∂G     -- sum rule
∂(F * G) = ∂F * G + F * ∂G  -- product rule
```

This gives **zippers** for free:

```
-- Zipper = value at focus + context (derivative)
Zipper F A = A * ∂F(A)

-- List zipper
∂(ListF) = List * List  -- elements before and after
ListZipper A = A * (List A * List A)
```

### Relevance to Once

Polynomial functors could:
- Generate efficient data structure operations
- Derive zippers automatically
- Enable generic programming
- Support differentiation for optimization

```
-- Automatic zipper derivation
zipper : DataType -> ZipperType
zipper t = (t, derivative t)

-- Generic traversal
traverse : Polynomial F => (A -> B) -> F A -> F B
```

## Coalgebras and Codata

### Algebras vs Coalgebras

| Algebra | Coalgebra |
|---------|-----------|
| `F A -> A` | `A -> F A` |
| Fold (catamorphism) | Unfold (anamorphism) |
| Finite data | Potentially infinite codata |
| Inductive | Coinductive |
| Lists, trees | Streams, processes |

### Codata in Once

Once mentions coalgebraic streams for time. This could be expanded:

```
-- Stream as coalgebra
type Stream A = A * Stream A  -- coinductive!

-- Unfold
unfold : (S -> A * S) -> S -> Stream A

-- Process (with input)
type Process I O = I -> O * Process I O

-- Mealy machine
type Mealy S I O = S -> I -> O * S
```

### Bisimulation

Coalgebras have **bisimulation** as their notion of equality:

```
-- Two streams are bisimilar if:
-- 1. Their heads are equal
-- 2. Their tails are bisimilar

bisimilar : Stream A -> Stream A -> Bool
bisimilar s1 s2 = (head s1 == head s2) && bisimilar (tail s1) (tail s2)
```

### Relevance to Once

Coalgebras naturally model:
- Infinite data structures
- Reactive systems
- State machines
- Concurrent processes

## Operads and Multicategories

### Beyond Binary Operations

Categories have morphisms with **one input**. Multicategories allow **multiple inputs**:

```
-- Multicategory morphism
f : A1, A2, ..., An -> B
```

Operads are multicategories with one object (operations on a single type).

### Relevance to Once

Multicategories could model:
- N-ary operations directly
- Database queries (multiple tables -> result)
- API combinators

```
-- Database join as multicategory morphism
join : Table A, Table B, (A * B -> Bool) -> Table (A * B)

-- Composition of multi-ary operations
```

## Double Categories and 2-Categories

### Higher Structure

A **2-category** has:
- Objects (0-cells)
- Morphisms between objects (1-cells)
- Morphisms between morphisms (2-cells)

```
      f
  A -----> B
  |   α    |
  |   ⇓    |
  A -----> B
      g
```

### Relevance to Once

2-categories could represent:
- Refactorings (2-cells transform between equivalent programs)
- Natural transformations as first-class
- Module morphisms

## Comparison Summary

| Foundation | Strengths | Best For |
|------------|-----------|----------|
| **CCCs (Once current)** | Simple, well-understood | General pure FP |
| **Linear categories** | Resource safety | Systems, embedded |
| **Profunctors** | Bidirectionality | Codecs, optics |
| **Arrows** | Static analysis | Circuits, FRP |
| **Monoidal** | Visual, quantum | Hardware, physics |
| **Polynomial** | Generic programming | Data structure ops |
| **Coalgebras** | Infinite, reactive | Streams, processes |

## Recommendation for Once

Once's current foundation (natural transformations in CCCs) is excellent for the core language. The extensions that seem most valuable:

### Immediate Value

1. **Optics** - Already derivable, make them first-class
2. **Linear resources** - Critical for low-level targets
3. **Coalgebras** - Already mentioned for time, expand for processes

### Future Exploration

4. **Profunctors** - For bidirectional programming
5. **String diagrams** - Visual representation
6. **Polynomial functors** - Generic programming

### Probably Not Core

7. **Full 2-categories** - Too complex for core language
8. **Operads** - Niche use cases

## Conclusion

Natural transformations provide an excellent foundation, but Once need not stop there. The categorical world offers many abstractions that could extend Once's expressiveness while maintaining its core principles:

- **Substrate independence** - Most categorical structures compile to any target
- **Formal verifiability** - All have well-understood laws
- **Composability** - Category theory is fundamentally about composition

The key is choosing which abstractions earn their place in the language versus remaining in the "interesting but not essential" category.
