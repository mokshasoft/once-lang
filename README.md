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

- **Nix** (required) for building the compiler
- **binutils** (`as`, `ld`, `objcopy`): the compiler assembles and links its output itself (the Nix
  package brings them)

### Build the Compiler

The Once compiler is built using Nix:

```bash
nix build
./result/bin/once build --help
```

**Note:** While the project includes `stack.yaml` for Stack users, building with Stack may encounter toolchain conflicts in Nix environments (especially on macOS). The recommended and tested build method is `nix build`, which handles all dependencies and toolchain configuration automatically.

### Hello World

Once has no strings yet; a program is observed by its exit code. This one computes 6 · 7 and exits
with it (`examples/hello.once`):

```bash
cat > hello.once << 'EOF'
import I.Linux.Syscalls as S

answer : Int -> Int
answer x = x * (x + 1)

main : Act Unit Void
main = exit@S (answer 6)
EOF

./result/bin/once build hello.once -o hello
./hello; echo $?
# Output: 42
```

The target defaults to the host's architecture, and a module with a `main` builds to an executable.
`--target x86_32` works the same way on an x86-64 host; `--target riscv64` needs a cross `as`/`ld`
(set `AS`, `LD`, `OBJCOPY`) and qemu to run.

### Library Example

A module without `main` is a library: the build emits assembly and stops.

```bash
cat > swap.once << 'EOF'
swap : a * b -> b * a
swap = pair snd fst

swapInts : Int * Int -> Int * Int
swapInts = swap
EOF

./result/bin/once build swap.once -o swap
# Creates: swap.s
```

Type variables are lowercase (`a`, `b`); uppercase names are concrete types. A polymorphic definition
has no code of its own; it is compiled where it is used at a concrete type, here `swapInts`.

### More Examples

[`examples/`](examples/) has small programs (arithmetic, `let`, a fold over the naturals, quantities).
`make -C examples ONCE=$PWD/result/bin/once` builds each one and checks its exit code on x86-64 and
x86-32; adding `riscv64` does the same under qemu.

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

**Working compiler.** The Once compiler compiles `.once` source to native assembly and links it into
a static executable itself (no C compiler involved).

Currently supported:
- Native backends: x86-64, x86-32 and RISC-V 64 (Linux)
- Products (`A * B`), sums (`A + B`), functions (`A -> B`), `Int` arithmetic and comparisons
- The 12 categorical generators
- Folds over initial algebras (`Mu`, `cata`)
- QTT quantities, inferred and enforced (`A^1` linear, `A^0` erased)
- Library mode (assembly, no entry point) and executable mode with interpretations (Linux)
- Composition operator (`.`) and ML-style application

Not yet:
- Strings and buffers: a program is observed by its exit code
- An ARM64 backend
- More interpretations (WASM, bare metal)

## The Vision

> No more reimplementing the same logic in every language.
> No more memory bugs from manual management.
> No more "it works on my machine."

One source of truth. Mathematical guarantees. Runs everywhere.

## Acknowledgements

The design of Once was influenced by [Ya](https://github.com/iokasimov/ya), a categorical programming language by Murat Kasimov. His exploration of natural transformations as a programming foundation and writings on categorical semantics helped shape Once's approach.

## License

AGPL-3.0-or-later

### Compiler Output Licensing

**Programs compiled with Once are derivative works under AGPL-3.0.**

Compilation is translation, not pass-through. The compiler's implementation
choices are structurally present in every compiled binary:

- **Slot machine model** for stack frame management
- **Catamorphism strategies** for recursive type compilation
- **Memory layouts** for products, sums, and recursive structures

Every major compiler either adds a runtime exception (GCC, GNAT) or uses a
permissive license (LLVM, Rust, Go) to permit proprietary compilation.
Once does neither. AGPL-3.0 applies to compiled output.

See [NOTICE](NOTICE) for full legal basis and details.
