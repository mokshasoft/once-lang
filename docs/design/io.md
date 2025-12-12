# Input/Output in Once

## IO is an Arrow

Once uses arrows for effect tracking. This is more general than monads and aligns perfectly with Once's categorical foundation.

```
Categories ⊃ Arrows ⊃ Monads
```

If you know Haskell's `IO` monad, you'll feel at home - `IO A` works as expected. Under the hood, it's sugar for the more general arrow type `Eff Unit A`.

## The Core Type: Eff

`Eff A B` represents an effectful morphism from `A` to `B`:

```once
type Eff : Type -> Type -> Type

-- Effectful primitives
println : Eff String Unit       -- takes String, produces Unit (with IO effect)
readLine : Eff Unit String      -- takes Unit, produces String (with IO effect)
readFile : Eff String (Result String Error)  -- may fail
```

## IO as Sugar

For Haskell users, `IO A` is syntactic sugar for `Eff Unit A`:

```once
type IO A = Eff Unit A

main : IO Unit                  -- familiar syntax
-- equivalent to:
main : Eff Unit Unit            -- explicit arrow form
```

## Arrow Composition

### Sequential Composition (>>>)

Chain effectful operations:

```once
(>>>) : Eff A B -> Eff B C -> Eff A C

-- Example: read input, then print it
echo : Eff Unit Unit
echo = readLine >>> println
```

### Lifting Pure Functions (arr)

Embed pure functions into the effectful world:

```once
arr : (A -> B) -> Eff A B

-- Example: greet with pure transformation
greet : Eff Unit Unit
greet = readLine >>> arr (\name -> "Hello, " ++ name) >>> println
```

### Parallel Composition

Work with multiple values:

```once
first  : Eff A B -> Eff (A * C) (B * C)
second : Eff A B -> Eff (C * A) (C * B)
(***)  : Eff A B -> Eff C D -> Eff (A * C) (B * D)
(&&&)  : Eff A B -> Eff A C -> Eff A (B * C)
```

## Why Arrows over Monads?

Once's 12 generators are already arrow-like:

| Generator | Arrow Operation |
|-----------|-----------------|
| `compose` | `(>>>)` |
| `pair` | `(&&&)` |
| `case` | `(\|\|\|)` |
| `curry`/`apply` | ArrowApply |

Benefits:
1. **Uniform composition** - everything uses `(>>>)`
2. **Natural embedding** - pure functions use `arr`
3. **Simpler verification** - one category, not two
4. **More expressive** - arrows can represent things monads cannot

## Comparison: Monad vs Arrow Style

**Monad style** (what Haskell users know):
```once
main : IO Unit
main = readLine >>= \name ->
       println ("Hello, " ++ name)
```

**Arrow style** (Once's native approach):
```once
main : IO Unit
main = readLine >>> arr (\name -> "Hello, " ++ name) >>> println
```

Both work in Once! ArrowApply (curry/apply) gives us monadic `>>=`.

## Eff vs Result

These are different concepts (see D025, D032):

| Type | What It Is | Example |
|------|------------|---------|
| `Result A E` | A value: success or error | `A + E` (sum type) |
| `Eff A B` | A morphism: effectful function | From A to B |
| `IO A` | A computation: effectful, no input | `Eff Unit A` |

They work together:
```once
readFile : Eff String (Result String Error)
-- An effectful operation (Eff) that may fail (Result)
```

## Primitives

IO operations come from **primitives** in the Interpretations layer:

```once
-- File operations
primitive readFile  : Eff String (Result String Error)
primitive writeFile : Eff (String * String) (Result Unit Error)

-- Console
primitive readLine : Eff Unit String
primitive println  : Eff String Unit

-- Network
primitive httpGet : Eff String (Result String Error)
```

Primitives are opaque - they have no implementation in Once, only a type signature. The interpretation (Linux, bare metal, WASM) provides the implementation.

## Complete Example

```once
-- Import primitives
primitive readLine : Eff Unit String
primitive println : Eff String Unit
primitive readFile : Eff String (Result String Error)

-- Pure helpers
greetMessage : String -> String
greetMessage name = "Hello, " ++ name ++ "!"

-- Effectful pipeline
main : IO Unit
main = arr (\_ -> "What is your name?")
   >>> println
   >>> readLine
   >>> arr greetMessage
   >>> println
```

## The Arrow Laws

`Eff` satisfies the arrow laws:

```
-- Identity
arr id >>> f        = f
f >>> arr id        = f

-- Associativity
(f >>> g) >>> h     = f >>> (g >>> h)

-- arr preserves composition
arr (g . f)         = arr f >>> arr g
```

## Purity Tracking

The type tells you everything:

```once
-- Pure: no Eff in the type
process : String -> String

-- Effectful: Eff in the type
load : Eff String String
```

You cannot accidentally do IO. If a function doesn't have `Eff` or `IO` in its type, it cannot perform effects. This is enforced by the type system.

## Summary

| Concept | Once Approach |
|---------|---------------|
| Effect type | `Eff A B` (arrow) or `IO A` (sugar) |
| Sequential | `(>>>) : Eff A B -> Eff B C -> Eff A C` |
| Lift pure | `arr : (A -> B) -> Eff A B` |
| Parallel | `(***), (&&&), first, second` |
| Effect only | `Eff A Unit` or `IO Unit` |
| IO operations | Primitives in Interpretations layer |
| Purity tracking | Eff/IO in type = effectful, none = pure |

## See Also

- D032: Arrow-Based Effect System
- D025: Result Type Convention
- docs/design/effects-proposal.md
