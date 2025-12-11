# Once Quickstart

## The One-Sentence Summary

**Once** = Write programs as natural transformations, compile to any language.

## The Core Idea (30 seconds)

```
Once program:     parseJson : String -> Json + Error
                        ↓
Categorical IR:   composition of ~12 primitive morphisms
                        ↓
Any target:       C, Rust, JavaScript, WASM, Haskell, bare metal
```

Natural transformations describe **structure**, not implementation. Every language can implement structure. Therefore: write once, compile anywhere.

## The 12 Generators (1 minute)

Everything reduces to these:

```
-- Composition
id      : A -> A
compose : (B -> C) -> (A -> B) -> (A -> C)

-- Products (pairs)
fst     : A * B -> A
snd     : A * B -> B
pair    : (C -> A) -> (C -> B) -> (C -> A * B)

-- Coproducts (either/or)
inl     : A -> A + B
inr     : B -> A + B
case    : (A -> C) -> (B -> C) -> (A + B -> C)

-- Terminal/Initial
terminal : A -> Unit
initial  : Void -> A

-- Functions
curry   : (A * B -> C) -> (A -> (B -> C))
apply   : (A -> B) * A -> B
```

That's it. JSON parsers, crypto, compression - all reduce to these.

## The Three Layers (1 minute)

```
┌────────────────────────────────────────┐
│         Interpretations                │  ← Impure (OS, hardware)
├────────────────────────────────────────┤
│         Derived                        │  ← Pure (your code)
├────────────────────────────────────────┤
│         Generators                     │  ← The 12 primitives
└────────────────────────────────────────┘
```

- **Generators**: Universal primitives
- **Derived**: All pure code (portable to any target)
- **Interpretations**: Platform bindings (POSIX, bare metal, WASM)

**Rule**: If it doesn't touch the external world, it's Derived. If it does, it's Interpretations.

## Effects = Functor Choice (30 seconds)

No special effect syntax. The type tells you:

| Type | Effect |
|------|--------|
| `A -> B` | Pure |
| `A -> Maybe B` | Might fail |
| `A -> List B` | Multiple results |
| `A -> E + B` | Error E possible |
| `A -> IO B` | Needs outside world (IO monad) |

## Why It Works (1 minute)

**Categorical laws** are universal:

```
compose f id = f           -- works in every language
compose id f = f           -- works in every language
fmap id = id               -- works in every language
```

The compiler translates structure, not implementation:

| Generator | C | Rust | JavaScript |
|-----------|---|------|------------|
| `compose f g` | `f(g(x))` | `f(g(x))` | `f(g(x))` |
| `pair f g` | `{f(x), g(x)}` | `(f(x), g(x))` | `[f(x), g(x)]` |
| `case f g` | `if/else` | `match` | `? :` |

Same meaning, different syntax.

## Key Properties

| Property | Why |
|----------|-----|
| **No GC needed** | Linear code (quantity 1) compiles without allocation |
| **Quantitative types** | Track usage: 0 (erased), 1 (linear), ω (unrestricted) |
| **Formally verifiable** | ~12 generators, graded categorical laws |
| **Bare metal ready** | No runtime required |
| **FFI both ways** | Call C, be called by C |

## Quick Example

```
-- Pure parser (Derived layer, portable)
parseNumber : String -> Int + ParseError
parseNumber = compose digitsToInt (many1 digit)

-- With IO (Interpretations layer, platform-specific)
readConfig : Path -> IO (Config + Error)
readConfig = compose parseConfig readFile
```

Same `parseNumber` compiles to C, Rust, JS, WASM. The `readConfig` needs a platform.

## Document Map

| Want to... | Read... |
|------------|---------|
| Understand the philosophy | [Design Philosophy](design-philosophy.md) |
| See all primitives | [Glossary](glossary.md) |
| Learn about compilation | [Transformation](transformation.md) |
| Understand IO | [IO](io.md) |
| Target bare metal | [Bare Metal](bare-metal.md) |
| See library structure | [Libraries](libraries.md) |
| Understand verification | [Formal Verification](formal-verification.md) |

## The Value Proposition

```
Traditional:                Once:
├─ JSON parser (C)          ├─ JSON parser (Once)
├─ JSON parser (Rust)       │     ↓ compile
├─ JSON parser (JS)         ├─ C
├─ JSON parser (Python)     ├─ Rust
├─ JSON parser (Go)         ├─ JS
└─ ... (N implementations)  ├─ Python
                            └─ ... (1 source, N targets)

N bugs → 1 bug
N maintenance → 1 maintenance
```

## Next Steps

1. Read [Overview](overview.md) for comprehensive introduction
2. Read [Design Philosophy](design-philosophy.md) for the "why"
3. Read [Prelude](prelude.md) for available functions
4. Read [Compiler](compiler.md) for how it works

## TL;DR

- Programs = natural transformations
- ~12 generators = universal substrate
- Pure code compiles anywhere
- Types show effects
- Category theory = the spec
- Write once, run everywhere (for real this time)
