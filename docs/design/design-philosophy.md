# Design Philosophy

## The Foundation: Natural Transformations

Once programs are **natural transformations** - structure-preserving maps from category theory. This isn't an implementation detail; it's the defining characteristic of the language.

A natural transformation preserves structure across contexts. In programming terms: the same transformation works regardless of what container or effect wraps your data. This property - naturality - enables cross-platform compilation.

## Why This Foundation?

### Universal Operations

All programming languages share certain operations:

- Compose functions
- Create and access pairs
- Branch on variants
- Call functions

These correspond exactly to the categorical generators Once uses. By building programs from these universal operations, Once code translates to any target language.

### No Implementation Details

Natural transformations don't mention:

- How memory is laid out
- Whether there's a garbage collector
- What calling convention to use
- What runtime system exists

They describe *what* to compute, not *how*. The backend chooses the how.

## Three Strata

Once separates code by purity:

| Stratum | Purity | Purpose |
|---------|--------|---------|
| Generators | Pure | The 12 primitives |
| Derived | Pure | All library code |
| Interpretations | Impure | Platform IO |

The insight: most code belongs in Derived. Only the thin Interpretations layer touches the external world. Everything else is portable.

## Effects Through Types

Once represents effects in the type system:

```
-- Pure
compute : Int -> Int

-- May fail
parse : String -> Result Json Error

-- Performs IO
readFile : Path -> IO String
```

The type signature tells you everything about what a function does. No hidden effects.

### IO is a Monad

IO in Once is honestly a monad (see D026). Three composition levels:

```
fmap : (A -> B) -> IO A -> IO B           -- Transform result
both : IO A -> IO B -> IO (A * B)         -- Combine independent
bind : IO A -> (A -> IO B) -> IO B        -- Sequence dependent
```

Use the weakest level that works. `both` can parallelize; `bind` cannot.

## No Exceptions

Once uses sum types for errors (D023):

```
type Result A E = A + E

parseJson : String -> Result Json ParseError
```

Rationale:

1. **Expressible with generators** - Exceptions require non-local jumps. Sum types compose naturally.

2. **Verifiable** - You can prove properties about `case f g` locally. Exceptions break compositional reasoning.

3. **Explicit** - The type shows failure is possible. You must handle both cases.

## Quantitative Types

Once tracks resource usage with quantities:

| Quantity | Meaning |
|----------|---------|
| `0` | Compile-time only |
| `1` | Used exactly once |
| `ω` | Used any number |

Linear types (`^1`) enable:
- No garbage collector needed
- Predictable memory behavior
- Safe resource handling

Quantities are inferred by default. Annotations are optional but provide guarantees:

```
-- Compiler verifies this is actually linear
processBuffer : Buffer^1 -> Result^1
```

## Type Inference

Types exist - morphisms have types by mathematical definition. But annotations are optional:

```
-- Explicit
swap : A * B -> B * A
swap = pair snd fst

-- Inferred (same result)
swap = pair snd fst
```

Write annotations for documentation and API boundaries. Skip them for local code.

## Minimal Core

The language has ~12 generators. Everything else is derived:

- `swap = pair snd fst`
- `diagonal = pair id id`
- `const a = curry fst`

No special forms. No compiler magic. If you can write it with generators, it's derivable.

## Formal Verification

Categorical laws provide the specification:

```
compose f id = f
compose id f = f
compose f (compose g h) = compose (compose f g) h
```

A compiler is correct if it preserves these equalities. This makes verification tractable:

- Only ~12 generators
- Laws proven since the 1940s
- Rewrites are law applications

## Comparison with Other Approaches

| Aspect | Traditional FP | Once |
|--------|---------------|------|
| Effects | Monad transformers | Functor choice |
| Errors | Exceptions or Either | Sum types |
| Resources | GC | QTT quantities |
| Portability | Single target | Any target |
| Verification | Difficult | Tractable |

## Design Decisions Summary

| Decision | Choice |
|----------|--------|
| D021 | Canonical library for derived morphisms |
| D023 | No exceptions |
| D024 | Initial library for data types |
| D025 | Result type, success-left |
| D026 | IO is a monad |

See [decision log](../compiler/decision-log.md) for full rationale.

## The Goal

Write logic once. Compile anywhere. Verify correctness.

Natural transformations make this possible because they describe structure - and structure is universal.
