# Once Design Philosophy

## Natural Transformations as Foundation

Once is built on a simple idea: **natural transformations are the right abstraction for computation**.

A natural transformation is a structure-preserving map between functors. In programming terms: it's a polymorphic function that respects the structure of data. This property - **naturality** - is what makes Once programs portable across targets.

## Why Natural Transformations?

### The Universal Language

Every programming language has:
- Functions (morphisms)
- Pairs/structs (products)
- Variants/unions (coproducts)
- Composition

Natural transformations describe computation in terms of these universals. They don't mention:
- Memory layout
- Garbage collection
- Calling conventions
- Runtime systems

This is why the same Once program compiles to C, Rust, JavaScript, or bare metal.

### The Naturality Law

The central equation:

```
fmap f . component = component . fmap f
```

This says: applying a function before or after a natural transformation gives the same result. The transformation commutes with mapping.

This law:
- Enables safe refactoring
- Allows compiler optimizations
- Makes formal verification tractable
- Guarantees structure preservation across targets

## Comparison with Monads

In Haskell, effects are typically handled with monads. Monads are built from natural transformations:

| Component | Type | Role |
|-----------|------|------|
| Functor | `T` | The effect type |
| Unit | `η : Identity -> T` | Inject pure value |
| Join | `μ : T (T A) -> T A` | Flatten nested effects |

Once says: **work with the natural transformations directly**, not the composite monad structure.

### Benefits

| Aspect | Monadic Approach | Natural Transformation Approach |
|--------|------------------|--------------------------------|
| Composition | Kleisli composition | Direct categorical composition |
| Performance | O(n) transformer stacks | O(1) composition |
| Expressiveness | Limited to monads | Full categorical structure |
| Cross-language | Tied to host language | Substrate-independent |

## Effects Without Monads

In Once, effects emerge from **functor choice**, not special syntax:

```
-- Pure function
parse : String -> AST

-- May fail
parse : String -> Maybe AST

-- May fail with error
parse : String -> AST + ParseError

-- Uses external IO
readFile : Path -> External String

-- Has state
counter : Unit -> State Int Int
```

The type tells you the effect. No effect system, no special keywords - just functors.

### The External Functor

IO isn't special. `External` is just a functor marking "this needs the outside world":

```
External : Type -> Type

fmap : (A -> B) -> External A -> External B
```

Primitives in the Interpretations layer produce `External` values. Everything else is pure.

## Error Handling Without Exceptions

Once deliberately omits exceptions. Errors are handled through **sum types**:

```
-- May fail with error
parseJson : String -> Json + ParseError

-- Chain operations that may fail
parseAndValidate : String -> ValidJson + ParseError + ValidationError
```

### Why No Exceptions?

**1. Not expressible with generators**

The 12 generators form a cartesian closed category. Exceptions require non-local control flow - `throw` jumps past multiple stack frames to a distant `catch`. This violates the compositional structure:

```
-- With exceptions (NOT Once):
f : A -> B        -- might throw, but type doesn't say
g : B -> C        -- might throw, but type doesn't say
compose g f : A -> C    -- where does the exception go?

-- With sum types (Once):
f : A -> B + E₁
g : B -> C + E₂
-- must explicitly handle E₁ before calling g
```

**2. Verifiability**

Exceptions break compositional reasoning. When verifying `compose f g`, you cannot reason locally - either function might throw, transferring control elsewhere. Sum types preserve compositionality:

```
-- Categorical law still holds:
compose (case f g) inl = f

-- No hidden control flow paths to track
```

**3. Explicit is better than implicit**

With exceptions, `A -> B` hides potential failures. With sum types, `A -> B + Error` makes failure explicit. You cannot accidentally ignore an error:

```
-- Must handle both cases
result : Json + ParseError
result = parseJson input

-- case forces you to handle the error
output = case handleJson handleError result
```

### Composing Fallible Operations

For chaining operations that may fail, use standard categorical combinators:

```
-- Map over success case
mapRight : (B -> C) -> (A + B) -> (A + C)

-- Chain fallible operations
bindRight : (B -> A + C) -> (A + B) -> (A + C)

-- Example: parse then validate
parseAndValidate : String -> ValidJson + Error
parseAndValidate = bindRight validate . mapRight normalize . parseJson
```

These are derivable from the 12 generators - no special error-handling syntax needed.

### Comparison

| Aspect | Exceptions | Sum Types (Once) |
|--------|------------|------------------|
| In type signature | No | Yes |
| Can ignore | Yes (accidentally) | No (must handle) |
| Compositional | No (non-local jumps) | Yes |
| Formally verifiable | Difficult | Standard CCC |
| Control flow | Implicit | Explicit |

Sum types make Once programs easier to verify, easier to reason about, and impossible to accidentally mishandle. See decision [D023](../compiler/decision-log.md#d023-no-exceptions) for the full rationale.

## The Three-Layer Architecture

Once organizes code by **purity**, not by module:

```
┌─────────────────────────────────────────────────────┐
│              Interpretations (Impure)               │
│   Platform primitives, OS calls, hardware access    │
├─────────────────────────────────────────────────────┤
│              Derived (Pure)                         │
│   All computation: parsers, algorithms, libraries   │
├─────────────────────────────────────────────────────┤
│              Generators (Pure)                      │
│   The 12 primitive morphisms                        │
└─────────────────────────────────────────────────────┘
```

- **Generators**: Universal primitives every language has
- **Derived**: Pure code, portable to any target
- **Interpretations**: Where Once meets the real world

## Quantitative Types

Once uses **Quantitative Type Theory (QTT)** to track resource usage. Every binding has a quantity:

| Quantity | Meaning | Memory Implication |
|----------|---------|-------------------|
| `0` | Erased (compile-time only) | No runtime representation |
| `1` | Linear (exactly once) | Stack allocation, no GC |
| `ω` | Unrestricted (any number) | May need GC or refcounting |

This is integrated with natural transformations via **graded categories**. The categorical laws still hold, but morphisms carry quantity information.

### Why Quantities?

Quantities are **semantic**, not implementation details:

```
f : A^1 → B    -- "f uses its input exactly once"
```

This statement is substrate-independent. Every target can implement it:
- C: value consumed, stack allocation
- Rust: ownership transfer
- JavaScript: used once (GC still handles it)
- Bare metal: stack slot, no free needed

### Inference by Default

Programmers write normal code. The compiler infers quantities:

```
-- You write
swap : A * B → B * A
swap = pair snd fst

-- Compiler infers
swap : (A * B)^1 → (B * A)^1
-- "This is linear"
```

### Optional Annotations

When you need guarantees (API boundaries, verification):

```
-- Explicit annotation
export swap : (A * B)^1 → (B * A)^1
swap = pair snd fst

-- Compiler VERIFIES your claim
-- If code isn't actually linear, compile error
```

This gives both expressiveness (inference) and guarantees (annotations) without restricting the language. See [Memory](memory.md) for details.

## Types Without Ceremony

Morphisms have types - that's mathematical fact:

```
f : A -> B
```

But type **annotations** are optional. Types can be inferred. The philosophy:
- Types exist (they're part of the math)
- Type annotations are documentation
- Inference handles the common case

## Substrate Independence

The key insight: natural transformations describe **what**, not **how**.

```
compose f g   -- means "do g then f"
pair f g      -- means "compute both"
case f g      -- means "branch"
```

Every language can express these concepts. The Once compiler translates:

| Generator | C | Rust | JavaScript |
|-----------|---|------|------------|
| `compose f g` | `f(g(x))` | `f(g(x))` | `f(g(x))` |
| `pair f g` | `{f(x), g(x)}` | `(f(x), g(x))` | `[f(x), g(x)]` |
| `case f g` | `if(tag) f else g` | `match { ... }` | `tag ? f : g` |

The structure is preserved. The implementation varies by target.

## Formal Correctness

Category theory provides **equational laws**:

```
compose f id = f
compose id f = f
compose f (compose g h) = compose (compose f g) h
```

These laws are the specification. A compiler is correct if it preserves them.

This makes verification tractable:
- Laws are well-known (proven in the 1940s)
- Only ~12 generators to verify
- Each optimization is a law application

## Summary

| Principle | Once Approach |
|-----------|---------------|
| Foundation | Graded natural transformations (QTT + category theory) |
| Effects | Functor choice (no special syntax) |
| Purity | Derived = pure, Interpretations = impure |
| Types | Inherent but annotations optional |
| Quantities | 0 (erased), 1 (linear), ω (unrestricted) |
| Resource tracking | QTT inference, optional annotations |
| Targets | Any (substrate-independent) |
| Correctness | Graded categorical laws as spec |

Once is not about adding features. It's about using the right mathematical foundation - one that's universal, verifiable, and works everywhere.
