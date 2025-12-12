# Once

**Capture essence, write Once, compile everywhere.** A programming language founded on natural transformations.

## What is Once?

Once is a programming language where programs are **natural transformations** from category theory. This mathematical foundation provides:

- **Substrate independence** - Same code compiles to C, Rust, JavaScript, WASM, bare metal
- **No garbage collector required** - Linear code (quantity 1) needs no GC
- **Formal verification** - ~12 generators, graded categorical laws, [partially verified in Agda](docs/formal/what-is-proven.md)
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

### The Three Strata

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
- **Derived**: All pure code - portable to any target. Includes the **Canonical** library of standard morphisms derived from universal properties.
- **Interpretations**: Platform bindings (POSIX, bare metal, WASM)

## Quick Start

### Prerequisites

- **Nix** (recommended) or **Stack** for building
- **GCC** for compiling generated C code

### Build with Nix

```bash
nix build
./result/bin/once build --help
```

### Build with Stack

```bash
cd compiler
stack build
stack exec -- once build --help
```

### Hello World

```bash
# Create hello.once
cat > hello.once << 'EOF'
primitive puts : String Utf8 -> Unit

main : Unit -> Unit
main = puts "Hello for Once"
EOF

# Compile (using Nix)
./result/bin/once build --exe --interp Strata/Interpretations/Linux hello.once -o hello

# Or with Stack
stack exec -- once build --exe --interp ../Strata/Interpretations/Linux hello.once -o hello

# Compile the generated C and run
gcc -o hello hello.c
./hello
# Output: Hello for Once
```

### Library Example

Once compiles to C libraries that can be called from any language:

```bash
# swap.once - pure natural transformation, no primitives
cat > swap.once << 'EOF'
swap : A * B -> B * A
swap = pair snd fst
EOF

# Generate C library
./result/bin/once build swap.once -o swap

# Creates: swap.h, swap.c
# Use from C, Rust, Python, etc. via FFI
```

## Documentation

### Design
- [Quickstart](docs/design/quickstart.md) - 5-minute introduction
- [Overview](docs/design/overview.md) - Comprehensive introduction
- [Design Philosophy](docs/design/design-philosophy.md) - Why natural transformations
- [Memory](docs/design/memory.md) - QTT, linearity, and resource management
- [Glossary](docs/design/glossary.md) - Reference for types and operations

### Architecture
- [Libraries](docs/design/libraries.md) - The three strata
- [IO](docs/design/io.md) - Effects as functor choice
- [FFI](docs/design/ffi.md) - Foreign function interface
- [Prelude](docs/design/prelude.md) - Standard library structure

### Compilation
- [Transformation](docs/design/transformation.md) - Write-once, compile anywhere
- [Compiler](docs/design/compiler.md) - Compiler architecture
- [Formal Verification](docs/design/formal-verification.md) - Proving correctness
- [What Is Proven](docs/formal/what-is-proven.md) - Current verification status

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
├── Strata/            # The three strata (see D016)
│   ├── Derived/       # Pure library code (Canonical, Initial)
│   └── Interpretations/  # Platform-specific bindings (Linux, etc.)
├── docs/
│   └── design/        # Language design documentation
└── examples/          # Example Once programs
```

## Status

**Working compiler.** The Once compiler generates C code from `.once` source files.

Currently supported:
- Products (`A * B`), sums (`A + B`), functions (`A -> B`)
- The 12 categorical generators
- String literals and `Buffer`/`String` types
- Library mode (generates `.h` + `.c`)
- Executable mode with interpretations (linux)
- Composition operator (`.`) and ML-style application

Coming soon:
- QTT quantity enforcement
- More interpretations (WASM, bare metal)
- Additional backends beyond C

## The Vision

> No more reimplementing the same logic in every language.
> No more memory bugs from manual management.
> No more "it works on my machine."

One source of truth. Mathematical guarantees. Runs everywhere.

## Acknowledgements

The design of Once was influenced by [Ya](https://github.com/iokasimov/ya), a categorical programming language by Murat Kasimov. His exploration of natural transformations as a programming foundation and writings on categorical semantics helped shape Once's approach.

## License

GPL-2.0
