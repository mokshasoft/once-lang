# Once

**Write once, compile anywhere.** A programming language founded on natural transformations.

## What is Once?

Once is a programming language where programs are **natural transformations** from category theory. This mathematical foundation provides:

- **Substrate independence** - Same code compiles to C, Rust, JavaScript, WASM, bare metal
- **No garbage collector required** - Linear code (quantity 1) needs no GC
- **Formal verification** - ~12 generators, graded categorical laws, tractable proofs
- **Memory safety** - Quantitative types (QTT) track resource usage at compile time

```
Once program:     parseJson : String^1 → (Json + Error)^1
                        ↓
Categorical IR:   composition of ~12 primitive morphisms
                        ↓
Any target:       C, Rust, JavaScript, WASM, Haskell, bare metal
```

## The Core Idea

Natural transformations describe **structure**, not implementation. Every programming language can implement structure. Therefore: write once, compile anywhere.

### The 12 Generators

Everything in Once reduces to these primitives:

```
id       : A → A                              -- identity
compose  : (B → C) → (A → B) → (A → C)        -- composition
fst      : A × B → A                          -- first projection
snd      : A × B → B                          -- second projection
pair     : (C → A) → (C → B) → (C → A × B)    -- pairing
inl      : A → A + B                          -- left injection
inr      : B → A + B                          -- right injection
case     : (A → C) → (B → C) → (A + B → C)    -- case analysis
terminal : A → Unit                           -- discard
initial  : Void → A                           -- absurd
curry    : (A × B → C) → (A → (B → C))        -- currying
apply    : (A → B) × A → B                    -- application
```

### Quantitative Types (QTT)

Once tracks resource usage via quantities:

| Quantity | Meaning | Memory Implication |
|----------|---------|-------------------|
| `0` | Erased (compile-time only) | No runtime representation |
| `1` | Linear (exactly once) | Stack allocation, no GC |
| `ω` | Unrestricted (any number) | May need GC |

Quantities are **inferred by default**, with optional annotations for guarantees.

### Three Layers

```
┌─────────────────────────────────────────────────────┐
│              Interpretations                        │  ← Impure (OS, hardware)
├─────────────────────────────────────────────────────┤
│              Derived                                │  ← Pure (your code)
├─────────────────────────────────────────────────────┤
│              Generators                             │  ← The 12 primitives
└─────────────────────────────────────────────────────┘
```

- **Generators**: Universal primitives every language has
- **Derived**: All pure code - portable to any target
- **Interpretations**: Platform bindings (POSIX, bare metal, WASM)

## Documentation

### Quick Start
- [Quickstart](docs/design/quickstart.md) - 5-minute introduction

### Design
- [Overview](docs/design/overview.md) - Comprehensive introduction
- [Design Philosophy](docs/design/design-philosophy.md) - Why natural transformations
- [Memory](docs/design/memory.md) - QTT, linearity, and resource management
- [Glossary](docs/design/glossary.md) - Reference for types and operations

### Architecture
- [Libraries](docs/design/libraries.md) - The three-layer structure
- [IO](docs/design/io.md) - Effects as functor choice
- [FFI](docs/design/ffi.md) - Foreign function interface
- [Prelude](docs/design/prelude.md) - Standard library structure

### Compilation
- [Transformation](docs/design/transformation.md) - Write-once, compile anywhere
- [Compiler](docs/design/compiler.md) - Compiler architecture
- [Formal Verification](docs/design/formal-verification.md) - Proving correctness

### Targets
- [Bare Metal](docs/design/bare-metal.md) - No OS, no runtime
- [Unikernels](docs/design/unikernels.md) - Minimal secure images

### Advanced
- [Categorical Foundations](docs/design/categorical-foundations.md) - Alternative abstractions
- [Parallelism](docs/design/parallelism.md) - Products and Day convolution
- [Time](docs/design/time.md) - Streams and coalgebraic time

## Project Structure

```
once-lang/
├── compiler/          # Haskell implementation of the Once compiler
├── docs/
│   └── design/        # Language design documentation
└── examples/          # Example Once programs
```

## Status

**Early design phase.** The language design is documented but the compiler is not yet implemented.

## The Vision

> No more reimplementing the same logic in every language.
> No more memory bugs from manual management.
> No more "it works on my machine."

One source of truth. Mathematical guarantees. Runs everywhere.

## License

GPL-2.0
