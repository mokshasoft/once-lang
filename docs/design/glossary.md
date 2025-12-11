# Glossary

Reference for Once terminology, types, and categorical concepts.

## The 12 Generators

| Generator | Type | Meaning |
|-----------|------|---------|
| `id` | `A -> A` | Do nothing, return input |
| `compose` | `(B -> C) -> (A -> B) -> (A -> C)` | Chain two functions |
| `fst` | `A * B -> A` | Extract first component |
| `snd` | `A * B -> B` | Extract second component |
| `pair` | `(C -> A) -> (C -> B) -> (C -> A * B)` | Apply two functions, combine results |
| `inl` | `A -> A + B` | Inject into left branch |
| `inr` | `B -> A + B` | Inject into right branch |
| `case` | `(A -> C) -> (B -> C) -> (A + B -> C)` | Handle both branches |
| `terminal` | `A -> Unit` | Discard value |
| `initial` | `Void -> A` | Impossible case |
| `curry` | `(A * B -> C) -> (A -> (B -> C))` | Convert to curried form |
| `apply` | `(A -> B) * A -> B` | Apply function to argument |

## Type Syntax

| Syntax | Name | Description |
|--------|------|-------------|
| `A -> B` | Function | Morphism from A to B |
| `A * B` | Product | Both A and B |
| `A + B` | Coproduct | Either A or B |
| `Unit` | Terminal | Single value, no information |
| `Void` | Initial | No values, impossible |
| `A^1` | Linear | Used exactly once |
| `A^0` | Erased | Compile-time only |
| `A^ω` | Unrestricted | Used any number of times |

## Standard Types

### Initial Library Types

| Type | Definition | Purpose |
|------|------------|---------|
| `Bool` | `Unit + Unit` | True or false |
| `Maybe A` | `Unit + A` | Optional value |
| `Result A E` | `A + E` | Success (left) or error (right) |
| `List A` | `Unit + (A * List A)` | Sequence of values |

### Result Conventions (D025)

```
ok  : A -> Result A E    -- ok = inl (success on left)
err : E -> Result A E    -- err = inr (error on right)
```

## Canonical Library

Derived morphisms from universal properties:

| Name | Type | Definition |
|------|------|------------|
| `swap` | `A * B -> B * A` | `pair snd fst` |
| `diagonal` | `A -> A * A` | `pair id id` |
| `assocL` | `A * (B * C) -> (A * B) * C` | Reassociate left |
| `assocR` | `(A * B) * C -> A * (B * C)` | Reassociate right |
| `distrib` | `A * (B + C) -> (A * B) + (A * C)` | Distribute product over sum |

## IO Monad (D026)

Three composition levels:

| Level | Operation | Type |
|-------|-----------|------|
| Functor | `fmap` | `(A -> B) -> IO A -> IO B` |
| Applicative | `pure` | `A -> IO A` |
| Applicative | `both` | `IO A -> IO B -> IO (A * B)` |
| Monad | `bind` | `IO A -> (A -> IO B) -> IO B` |

Choose the weakest level that works:
- `fmap` when transforming results
- `both` when combining independent operations (can parallelize)
- `bind` when second operation depends on first (must sequence)

## Three Strata

| Stratum | Purity | Contents |
|---------|--------|----------|
| Generators | Pure | The 12 primitives |
| Derived | Pure | All library code built from generators |
| Interpretations | Impure | Platform-specific IO primitives |

## Recursion Schemes

| Scheme | Type | Meaning |
|--------|------|---------|
| `cata` | `(F A -> A) -> Fix F -> A` | Fold recursive structure |
| `ana` | `(A -> F A) -> A -> Fix F` | Unfold into recursive structure |
| `hylo` | `(F B -> B) -> (A -> F A) -> A -> B` | Combined unfold then fold |
| `para` | `(F (Fix F * A) -> A) -> Fix F -> A` | Fold with original subtree access |

See [Recursion Schemes](recursion-schemes.md) for details.

## Category Theory Terms

| Term | Once Meaning |
|------|--------------|
| Morphism | Function between types |
| Functor | Type constructor with `fmap` |
| Natural transformation | Polymorphic function between functors |
| Product | `A * B` with projections |
| Coproduct | `A + B` with injections |
| Terminal object | `Unit` |
| Initial object | `Void` |
| Cartesian closed | Has products, exponentials (functions), terminal |

## QTT Quantities

| Quantity | Usage |
|----------|-------|
| `0` | Type-level only, erased at runtime |
| `1` | Must use exactly once (linear) |
| `ω` | May use any number of times |

Linear types (`^1`) enable:
- No garbage collection needed
- Predictable memory usage
- Safe resource management

## Syntax Quick Reference

```
-- Type signature
name : Type

-- Definition
name = expression

-- Lambda
\x -> body

-- Application
f x y

-- Composition
f . g       -- right-to-left
x |> f      -- left-to-right

-- Let binding
let x = e in body

-- Type alias
type Name = Definition

-- Primitive (Interpretations)
primitive name : Type
```
