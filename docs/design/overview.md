# Once Language Overview

## What is Once?

Once is a programming language where programs are **natural transformations** - structure-preserving maps from category theory. This mathematical foundation enables a key property: code written in Once compiles to multiple target languages (C, Rust, JavaScript, WebAssembly, bare metal) from a single source.

## The Central Idea

Natural transformations describe **structure**, not implementation details. They don't mention memory layout, garbage collection, or calling conventions - just how to compose operations. Since every programming language can implement basic operations like composition, products, and sums, Once code translates naturally to any target.

```
Once source → Categorical IR → C / Rust / JS / WASM / ...
```

## The 12 Generators

All Once programs reduce to compositions of these primitives:

```
id       : A -> A                              -- identity
compose  : (B -> C) -> (A -> B) -> (A -> C)    -- composition
fst      : A * B -> A                          -- first projection
snd      : A * B -> B                          -- second projection
pair     : (C -> A) -> (C -> B) -> (C -> A * B) -- pairing
inl      : A -> A + B                          -- left injection
inr      : B -> A + B                          -- right injection
case     : (A -> C) -> (B -> C) -> (A + B -> C) -- case analysis
terminal : A -> Unit                           -- discard value
initial  : Void -> A                           -- impossible case
curry    : (A * B -> C) -> (A -> (B -> C))     -- currying
apply    : (A -> B) * A -> B                   -- application
```

These operations exist in every language. That's why compilation works.

## The Three Strata

Once organizes code into three layers:

| Stratum | Purity | Contents |
|---------|--------|----------|
| **Generators** | Pure | The 12 primitives |
| **Derived** | Pure | All library code (JSON, crypto, algorithms) |
| **Interpretations** | Impure | Platform-specific IO (file, network, GPIO) |

Only Interpretations touches the external world. Code in Generators and Derived is portable to any target.

## Type System

### Basic Types

```
A -> B      -- Function from A to B
A * B       -- Product: both A and B
A + B       -- Coproduct: either A or B
Unit        -- Single value (terminal object)
Void        -- No values (initial object)
```

### Quantitative Type Theory (QTT)

Once tracks how many times values are used:

| Quantity | Notation | Meaning |
|----------|----------|---------|
| 0 | `A^0` | Compile-time only, erased |
| 1 | `A^1` | Used exactly once (linear) |
| ω | `A^ω` | Used any number of times |

Linear types (`^1`) enable:
- No garbage collector required
- Predictable memory usage
- Safe resource management

Quantities are inferred by default; annotations are optional.

## IO and Effects

Once uses the IO monad for effects (see D026):

```
pure : A -> IO A
fmap : (A -> B) -> IO A -> IO B
both : IO A -> IO B -> IO (A * B)
bind : IO A -> (A -> IO B) -> IO B
```

Effects are visible in types - a function returning `IO A` performs IO, a function returning just `A` is pure.

## Error Handling

Once uses sum types instead of exceptions (see D023):

```
type Result A E = A + E

ok  : A -> Result A E    -- ok = inl
err : E -> Result A E    -- err = inr
```

Success is on the left by convention (D025). Errors are values, not control flow.

## Code Example

```
-- Pure JSON parser (Derived stratum)
parseJson : String -> Result Json ParseError
parseJson = compose validate (compose structure tokenize)

-- IO wrapper (Interpretations stratum)
readConfig : Path -> IO (Result Config Error)
readConfig path = fmap parseJson (readFile path)
```

The parser compiles to any target. The IO wrapper requires platform-specific file primitives.

## Compilation Targets

| Target | Status | Use Case |
|--------|--------|----------|
| C | Implemented | Maximum portability |
| Rust | Planned | Memory safety |
| JavaScript | Planned | Browser, Node.js |
| WebAssembly | Planned | Portable binary |
| Bare metal | Planned | Embedded, firmware |

## Formal Verification

The categorical foundation enables tractable formal verification:

- Only ~12 generators to verify
- Rewrites are applications of categorical laws
- Laws have been proven correct since the 1940s

The compiler itself can be generated from verified Agda code using MAlonzo, ensuring the optimizer provably preserves program semantics.

See [What Is Proven](../formal/what-is-proven.md) for current verification status.
See [MAlonzo Compilation](malonzo-compilation.md) for the verified compiler architecture.

## Optimization

The natural transformation foundation enables principled optimization:

- **Parametricity** gives "free theorems" - equations that hold by construction
- **Functor laws** enable map fusion: `map f . map g = map (f . g)`
- **Recursion schemes** enable deforestation: eliminate intermediate data structures
- **Linearity** enables in-place updates without aliasing concerns

The optimizer applies categorical laws as rewrite rules, preserving semantics by construction.

See [Optimization](optimization.md) for theory, laws, and programming guidelines.

## Documentation Structure

| Section | Contents |
|---------|----------|
| [Quickstart](quickstart.md) | 5-minute introduction |
| [Design Philosophy](design-philosophy.md) | Why natural transformations |
| [Compiler](compiler.md) | Compiler architecture |
| [MAlonzo Compilation](malonzo-compilation.md) | Generating compiler from Agda |
| [Optimization](optimization.md) | NT-based optimization theory and guidelines |
| [Libraries](libraries.md) | The three strata |
| [IO](io.md) | The IO monad |
| [Memory](memory.md) | QTT and resource management |
| [FFI](ffi.md) | Foreign function interface |
| [Bare Metal](bare-metal.md) | Embedded compilation |
| [Glossary](glossary.md) | Quick reference |

## Getting Started

```bash
# Build with Nix
nix build
./result/bin/once build example.once -o example

# Or with Stack
cd compiler
stack build
stack exec -- once build example.once -o example
```

See [Quickstart](quickstart.md) for more details.
