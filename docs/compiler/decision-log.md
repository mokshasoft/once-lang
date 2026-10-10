# Decision Log

Design decisions made during the implementation of the Once compiler.

---

## D001: Generators as Reserved Words

**Date**: 2025-12-08
**Status**: **SUPERSEDED by D136 (2026-09-01)** — generators are identified by a
reserved NAMESPACE (`Generators.*`), not by reserved bare names, and a user MAY
define `fst`. The reservation below was never enforced at the parser; what it
produced instead was a collision in which the builtin silently won. Read D136
for what replaced it and why.

### Context
The 12 categorical generators (`id`, `compose`, `fst`, `snd`, `pair`, `inl`, `inr`, `case`, `terminal`, `initial`, `curry`, `apply`) need to be represented in the surface syntax. Two approaches were considered:

1. **Prelude functions**: Generators are ordinary identifiers that can be shadowed (like Haskell's `fst`)
2. **Reserved words**: Generators cannot be used as variable names

### Decision
Generators are **reserved words**.

### Rationale
- Generators are not ordinary functions - they're the categorical primitives that define the language's semantics
- They're more like operators (`+`, `=`) than library functions (`map`)
- Allowing shadowing would:
  - Create confusion about meaning
  - Complicate tooling and verification
  - Undermine Once's philosophical foundation (12 generators as universal substrate)
- The restriction is minor (12 names) and actually beneficial:
  - If you want the first element, `fst` is the right name
  - If you want something else, a more descriptive name is better

### Consequences
- Users cannot define variables named `fst`, `snd`, `pair`, etc.
- The parser can assume these names always refer to generators
- Elaboration is simpler (no need to check for shadowing)

---

## D002: Surface Syntax AST Design

**Date**: 2025-12-08
**Status**: Accepted

### Context
The surface syntax AST (`Syntax.hs`) represents parsed Once code before elaboration to IR. We needed to decide how to represent generator applications.

### Decision
Generators are represented as `EVar` nodes with reserved names. There are no special AST constructors like `EFst`, `ESnd`, etc.

### Rationale
- Keeps the AST simple - only structural forms (application, lambda, pair, case)
- The parser recognizes generator names and produces `EVar "fst"`, etc.
- The elaborator maps these to IR constructors (`Fst`, `Snd`, etc.)
- Clean separation: parser handles syntax, elaborator handles semantics

### Consequences
- `Syntax.hs` has fewer constructors
- Generator recognition happens in the parser (reserved words) and elaborator (IR mapping)
- AST is more uniform - everything is variables and applications

---

## D003: Quantity Type as Semiring

**Date**: 2025-12-08
**Status**: Superseded by D276 (2026-10-06): the semiring stands; `One` means AT MOST once
(affine), and the order `Zero ⊑ One ⊑ Omega` is part of the structure.

### Context
QTT (Quantitative Type Theory) requires tracking resource usage with quantities.

### Decision
Quantities form a semiring with three elements: `Zero`, `One`, `Omega`.

```haskell
data Quantity = Zero | One | Omega

qAdd :: Quantity -> Quantity -> Quantity  -- semiring addition
qMul :: Quantity -> Quantity -> Quantity  -- semiring multiplication
```

### Rationale
- `Zero`: Erased at runtime (compile-time only)
- `One`: Linear (used exactly once) - enables GC-free execution
- `Omega`: Unrestricted (used any number of times)
- Semiring laws ensure quantities compose correctly
- Property tests verify the laws hold

### Consequences
- All variable usage is tracked with quantities
- Linear code (`One`) can be compiled without garbage collection
- Quantities are inferred by default, with optional annotations

---

## D004: Property Tests as Specification

**Date**: 2025-12-08
**Status**: Accepted

### Context
The implementation plan calls for "verification-ready" code. We needed a practical approach that enables future proofs.

### Decision
QuickCheck property tests serve as the executable specification.

### Rationale
- Properties are written to be "theorem-shaped" - each can become a Coq lemma
- Immediate feedback during development
- Properties document invariants clearly
- Example: `prop_id_right f x = eval (Compose f (Id t)) x === eval f x`
- Later this becomes: `Theorem id_right : forall f x, eval (Compose f (Id _)) x = eval f x.`

### Consequences
- All categorical laws are tested (identity, associativity, product/coproduct laws)
- Semiring laws for quantities are tested
- Tests serve as living documentation
- Path to formal verification is clear

---

## D005: Single Backend (C)

**Date**: 2025-12-08
**Status**: Accepted (from implementation plan)

### Context
Once's value proposition is "write once, compile anywhere." We needed to choose initial backend targets.

### Decision
Start with C as the only backend. Other languages call Once code via C FFI.

### Rationale
- C is the universal FFI language
- Every major language can call C
- Simpler than maintaining multiple backends initially
- Proves the concept before expanding

### Consequences
- Once libraries compile to `.h` + `.c` files
- Other languages (Rust, Python, JS) can use Once via C bindings
- Future backends (WASM, etc.) can be added later

---

## D006: Fourmolu Defaults

**Date**: 2025-12-08
**Status**: Accepted

### Context
The implementation plan specified fourmolu for consistent formatting.

### Decision
Use fourmolu's default settings (no custom `fourmolu.yaml`).

### Rationale
- Defaults are well-chosen
- Less configuration to maintain
- Matches community conventions

### Consequences
- No `fourmolu.yaml` file in the repo
- Run `fourmolu --mode inplace` with no extra flags

---

## D007: Structural Type Matching for Signatures

**Date**: 2025-12-08
**Status**: Accepted

### Context
When type-checking a function definition against its signature, we need to verify that the inferred type matches the declared type. Two approaches were considered:

1. **Rigid/skolem variables** (ML-family approach): Signature type variables are treated as "rigid" - they cannot be unified with arbitrary types, only with other type variables. This ensures parametricity.

2. **Structural matching**: The signature and inferred type must have the same structure, with consistent variable mappings.

### Decision
Use **strict structural matching** for signature checking. Signatures must exactly match the inferred type (modulo variable renaming).

### Rationale

**Why not rigid/skolem variables (ML approach)?**

In ML-family languages, signatures are sometimes *necessary* for type inference:
- Polymorphic recursion requires annotation
- Higher-rank types need explicit `forall` placement
- Type class ambiguity needs resolution
- Monomorphism restriction affects unannotated bindings

In Once, **none of these apply**:
- No recursion (programs are finite compositions of generators)
- No higher-rank types (everything is first-order categorical morphisms)
- No type classes
- No monomorphism restriction

The generators have fixed, known types. The type of any expression is **fully determined** by how generators compose - there's no ambiguity, no choice for the compiler to make.

**Why not allow signature specialization?**

We considered allowing signatures to be more specific than the inferred type. For example:
```
foo : Unit -> Unit
foo = id          -- id infers to A -> A
```

This was rejected because it would make signatures **semantically meaningful** - the signature would restrict the type rather than just document it. This has problematic implications:
- Two different signatures for the same body would produce different functions
- Signatures become "load-bearing" rather than purely declarative
- The type of `foo` when used elsewhere would be `Unit -> Unit`, not `A -> A`

**The Once approach: signatures as assertions**

Signatures in Once serve a different purpose than in ML:
- **Documentation** for human readers
- **Assertions** that the programmer understands the composition correctly

The expression alone determines the type. The signature is the programmer saying "I believe this has type X" and the compiler verifying that belief. This keeps the language simple and predictable.

### Consequences
- Simpler type checker implementation (no rigid variable tracking, no subsumption)
- Clear error messages: "signature says X, inferred Y"
- Signatures are optional - the compiler can always infer the type
- Signatures cannot change the meaning of a program, only verify it
- `foo : Unit -> Unit` with `foo = id` is rejected (signature doesn't match `A -> A`)

---

## D008: Library vs Executable Output Modes

**Date**: 2025-12-08
**Status**: Accepted

### Context
Once programs can serve two purposes:
1. **Libraries**: Reusable components called from other languages via FFI
2. **Executables**: Standalone programs (for bare-metal, unikernels, OS binaries)

The initial compiler only generated library output (`.h` + `.c` files). We needed to support standalone executables.

### Decision
Add `--lib` and `--exe` flags to the CLI:
- `--lib` (default): Generates a C header and source file for FFI integration
- `--exe`: Generates a standalone C file with `main()` entry point

### Rationale
- **Separation of concerns**: Libraries are for composition, executables are for deployment
- **Different output structure**:
  - Libraries need headers for consumers
  - Executables need `main()` and primitive implementations
- **Primitives differ**:
  - In library mode, primitives are declared `extern` (provided by the host)
  - In executable mode, known primitives (like `exit0`) are implemented inline
- **Minimal viable example**: The "hi world" program (`main = exit0`) demonstrates a complete executable

### Implementation Details
- Executable mode generates a single `.c` file (no header needed)
- The `main()` function calls `once_main(NULL)` and returns 0
- Unknown primitives are declared `extern` (must be linked separately)

### Built-in Primitives

Currently supported primitives in executable mode:

| Primitive | Type | C Implementation |
|-----------|------|------------------|
| `exit0` | `Unit -> Unit` | `exit(0)` |

These are hardcoded in `CLI.hs`. Future work could:
- Add more primitives (e.g., `exit : Int -> Unit`, `putchar : Int -> Unit`)
- Allow primitive definitions in a separate file
- Generate extern declarations for unknown primitives

### Consequences
- Users can now compile complete programs, not just libraries
- Path to bare-metal/unikernel compilation is opened
- Adding new primitives requires modifying `CLI.hs` (temporary limitation)

---

## D009: Interpretations Live Outside the Compiler

**Date**: 2025-12-08
**Status**: Accepted

### Context
Primitives are opaque operations at the boundary between Once and the external world. We needed to decide where primitive implementations live.

### Options Considered

1. **Hardcoded in compiler** - Primitive C code embedded in Haskell
2. **Once file + implementation file** - `.once` declares types, `.c` provides C implementation
3. **Pure Once files** - Interpretations as Once modules only
4. **FFI syntax in Once** - `foreign import c "exit" ...`

### Decision
Option 2: **Interpretations are `.once` + `.c` file pairs, living outside the compiler**.

```
Strata/
  Interpretations/
    Linux/
      syscalls.once     -- type declarations
      syscalls.c        -- C implementation
    Browser/
      syscalls.once
      syscalls.js       -- JS implementation
    BareMetal/
      ...
  Derived/
    Canonical/          -- morphisms from universal properties
    Initial/            -- data types as initial algebras
```

### Rationale

- **Generators only in compiler**: The 12 categorical generators are the language. Primitives are external.
- **No FFI foot-gun**: Once is "write once, compile anywhere." No need to call other languages directly.
- **Platform-native implementations**: Each interpretation uses its native language (C for linux, JS for browser).
- **Extensible**: Users can create their own interpretations without modifying the compiler.
- **Clean separation**: Pure Once (generators + composition) vs impure boundary (interpretations).

### File Naming

- `syscalls.once` - primitive type declarations
- `syscalls.c` / `syscalls.js` - native implementation for that platform
- Future: `drivers/gpio.once` etc. for device-specific primitives

### Consequences
- `Strata/Interpretations/` directory at repo root, not in `compiler/`
- Compiler only knows about generators
- Linking interpretations is a separate concern (future work)
- Each platform interpretation is self-contained

### Amendment (2026-10-06, plan 0.107 step 5): assembly, not C
The implementation half is the interpretation's hand-written per-arch ASSEMBLY,
`Strata/Interpretations/<…>/<M>.<arch>` (`x86_64`, `x86_32`, `riscv64`, `arm64`; plan 0.11),
not a `.c` file. The `.c` files beside them are leftovers of the dropped C backend. The CLI
(`assembleImplFiles`) assembles that file with `as` and renames each operation's plain symbol to
`onceSymbolPath (path ++ [op])` (`objcopy --redefine-sym`), and `ld` links it. The program emits
no body for an FFI declaration (D274): the declaration extends Σ, its call sites name the resolved
`CanonicalName`'s symbol, and the file lists that symbol as `.extern`. The interpretation's
contracts stay its author's to discharge (D061); the rename is trusted Haskell on that boundary.

---

## D010: Buffer as Primitive Type

**Date**: 2025-12-09
**Status**: Accepted

### Context
Once needs a way to handle strings and byte sequences efficiently. We needed to decide how to represent contiguous byte data.

### Options Considered

1. **Derived from generators** - `type Buffer = List Byte`
2. **Primitive type** - `Buffer` as a built-in type like `Int`

### Decision
Buffer is a **primitive type**, not derivable from generators.

### Rationale
- The 12 generators describe structure (products, sums, functions), not memory layout
- "Contiguous bytes" is inherently about physical representation
- `List Byte` would be a linked list - O(n) indexing, poor cache locality
- Every target platform has efficient contiguous byte representation:
  - C: `struct { uint8_t* data; size_t len; }`
  - JavaScript: `Uint8Array`
  - Bare metal: pointer + length

### Consequences
- Buffer is added to `Type.hs` alongside `TInt`, `TUnit`, etc.
- Buffer operations (`concat`, `length`, `slice`) are primitives in IR
- C backend generates efficient struct-based representation
- This is the single primitive for byte storage - no fragmentation like Haskell

---

## D011: String as Parameterized Type with Encoding

**Date**: 2025-12-09
**Status**: Accepted

### Context
Once needs string handling. We needed to decide how to represent text and whether encoding should be part of the type.

### Options Considered

1. **Type alias** - `type String = Buffer` (encoding by convention)
2. **Newtype** - `newtype String = String Buffer` (distinct type, no encoding info)
3. **Type parameter** - `String : Encoding -> Type` (encoding in type)

### Decision
String is a **parameterized type** with encoding as type parameter: `String : Encoding -> Type`.

### Rationale
- Encoding is **semantic** - it affects how operations work (e.g., `charAt` for UTF-8 vs ASCII)
- Allocation is **implementation** - it doesn't affect what the function computes
- Semantic concerns belong in the type; implementation concerns don't
- Type parameter provides compile-time safety (can't mix UTF-8 and UTF-16 accidentally)
- Encoding is erased at runtime (zero cost) - just like other type parameters

Built-in encodings: `Utf8`, `Utf16`, `Ascii`. Users can add more.

### Consequences
- `String Utf8`, `String Ascii`, etc. are distinct types
- Explicit conversion between encodings: `toUtf8 : String Ascii -> String Utf8`
- Under the hood, `String e` wraps `Buffer` with erased encoding tag
- Encoding-agnostic operations work on any `String e`
- Encoding-specific operations (like `charAt`) require specific encoding

---

## D012: Allocation Annotation in Implementation

**Date**: 2025-12-09
**Status**: Superseded by D142 (2026-09; allocation is mechanical — no surface annotation, no IR mode, no flag). Status updated 2026-10-09 (plan 0.113 E).

### Context
Buffer allocation strategy (stack, heap, pool, arena) needs to be expressible. We needed to decide where this annotation goes.

### Options Considered

1. **Inline in type** - `concat : Buffer @heap * Buffer @heap -> Buffer @heap`
2. **Separate line above signature** - `@alloc heap` then `concat : Buffer * Buffer -> Buffer`
3. **Separate line with @returns** - `@returns heap` then `concat : ...`
4. **In implementation** - `concat @heap a b = ...`

### Decision
Allocation annotation goes in the **implementation**, not the type signature.

```
concat : Buffer * Buffer -> Buffer
concat @heap a b = ...
```

For lambdas: `(@stack \x -> concat x x)`

### Rationale
- **Type signatures should be purely semantic** - they describe categorical meaning
- **Allocation doesn't change meaning** - `f @heap` and `f @stack` compute the same function
- **Allocation is implementation detail** - belongs with implementation, not type
- Option 1 rejected: `@heap` looks like type parameter, suggests it could be used on inputs
- Option 2/3 rejected: Adds extra line, still near type signature

This aligns with D007: signatures verify but don't change meaning.

### Consequences
- Type signatures remain clean and categorical
- Allocation is visibly an implementation choice
- Lambdas can have allocation annotations
- No annotation = inferred from context or compiler flag

---

## D013: Allocation Only Applies to Outputs

**Date**: 2025-12-09
**Status**: Superseded by D142 (2026-09; allocation is mechanical — no surface annotation, no IR mode, no flag). Status updated 2026-10-09 (plan 0.113 E).

### Context
When annotating allocation, should it apply to inputs, outputs, or both?

### Decision
Allocation annotation only applies to **outputs** (return values).

### Rationale
- **Inputs**: Function accepts data from wherever the caller provides it - allocation already decided
- **Outputs**: Function must decide where to allocate the result
- For linear in-place operations (`^1 -> ^1`): output uses same memory as input, allocation inherited

A function reading a buffer doesn't care where it came from. A function producing a buffer needs to know where to put it.

### Consequences
- `concat @heap a b = ...` means output goes to heap
- Input buffers can come from any allocation strategy
- Mixing strategies requires explicit conversion at call site
- Linear transforms inherit allocation from input

---

## D014: Allocation Strategy Compiler Flag

**Date**: 2025-12-09
**Status**: Superseded by D142 (2026-09; allocation is mechanical — no surface annotation, no IR mode, no flag). Status updated 2026-10-09 (plan 0.113 E).

### Context
Not every function needs explicit allocation annotation. We needed a way to set defaults.

### Decision
Add `--alloc` compiler flag to set default allocation strategy.

```bash
once build myfile.once                  # platform default
once build --alloc=stack myfile.once    # default to stack
once build --alloc=arena myfile.once    # default to arena
```

### Rationale
- Same source code can compile with different strategies
- Bare metal projects can default to `--alloc=stack`
- Server applications can default to `--alloc=arena`
- No code changes needed for different deployment targets

### Precedence
1. Explicit `@stack` in implementation - always wins
2. Compiler flag `--alloc=X` - default for unannotated
3. Platform default - fallback (typically `heap` for Linux)

### Consequences
- CLI gains `--alloc` flag
- Codegen tracks current default strategy
- Most code needs no allocation annotations

---

## D015: Three Allocator Interface Classes

**Date**: 2025-12-09
**Status**: Accepted

### Context
Different allocation strategies have different interfaces. Users may want to add custom allocators. We needed to decide how to enable extensibility.

### Decision
Define three allocator interface classes that the compiler knows about:

**MallocLike** (heap, custom allocators):
```
alloc : Size -> Ptr
free : Ptr -> Unit
realloc : Ptr -> Size -> Ptr
```

**PoolLike** (fixed-size block allocators):
```
createPool : BlockSize -> BlockCount -> Pool
allocBlock : Pool -> Ptr
freeBlock : Pool -> Ptr -> Unit
destroyPool : Pool -> Unit
```

**ArenaLike** (bump allocators):
```
createArena : Size -> Arena
allocArena : Arena -> Size -> Ptr
resetArena : Arena -> Unit
destroyArena : Arena -> Unit
```

Built-in strategies (`stack`, `const`) are compiler-managed, not user-extensible.

### Rationale
- Different strategies have fundamentally different interfaces (arena has no individual free)
- Users can add custom allocators by implementing one of these interfaces
- Compiler doesn't need updating for new allocators - just needs to know the interface class
- Property test can verify all allocators produce same results

### Consequences
- Users can define custom allocators in Interpretations
- Custom allocator picks an interface class and implements it
- Compiler generates appropriate code based on interface class
- `stack` and `const` remain special (compiler-managed)

---

## D016: Naming the Three Layers "Strata"

**Date**: 2025-12-09
**Status**: Accepted

### Context
Once has three conceptual layers: Generators, Derived, and Interpretations. We needed a collective name for these layers.

### Options Considered
- Layers (generic)
- Stack (overloaded term)
- Hierarchy (generic)
- Strata (Latin for layers)

### Decision
The three layers are collectively called **Strata**.

### Rationale
- "Strata" is specific and technical-sounding
- Captures the idea of distinct levels with different properties
- Not overloaded with other meanings in programming
- Each stratum has clear boundaries and rules

### Consequences
- Documentation refers to "the three strata" or "Once strata"
- Individual layers: Generators Stratum, Derived Stratum, Interpretations Stratum

---

## D017: Refinement Types as Future Extension Path

**Date**: 2025-12-09
**Status**: Deferred

### Context
Sized buffers (`Buffer { size <= 1024 }`) would be useful for safety. We needed to decide whether to add dependent types or a simpler alternative.

### Options Considered

1. **Full dependent types** - Types depend on values, type-level computation
2. **Refinement types** - Properties on types, always erased, SMT-checked
3. **No extension** - Keep simple types only

### Decision
**Defer implementation**, but plan for **refinement types** (not full dependent types) using **comprehension categories** as the theoretical foundation.

### Rationale
- Refinement types cover practical cases (sizes, bounds, non-null)
- Always erased at runtime (zero cost) - aligns with "types don't change meaning"
- Simpler than full dependent types (often decidable with SMT)
- Comprehension categories allow incremental extension:
  1. Simple types (current)
  2. Refinement types (future)
  3. Full dependent types (if ever needed)
- Simple users remain unaffected - refinements are opt-in

### Consequences
- Current type system unchanged
- Path to sized buffers is clear when needed
- Comprehension categories guide future extension
- See `type-system.md` for detailed discussion

---

## D018: Values with Implicit Lifting to Morphisms

**Date**: 2025-12-09
**Status**: Accepted

### Context
Once has a categorical core where everything is a morphism (natural transformation). However, writing purely point-free code can be verbose and hard to read. We needed to decide how the surface syntax handles "values" like string literals.

### Options Considered

1. **Pure point-free**: String literals are morphisms `Unit -> String Utf8`. Users must use explicit composition: `compose puts "hello"`.

2. **Values with implicit lifting**: String literals are values `String Utf8`. The compiler lifts them to constant morphisms when needed.

### Decision
**Values with implicit lifting**. The surface syntax allows ML-style values and application. The compiler inserts the categorical machinery.

```
-- Surface syntax (what users write)
main : Unit -> Unit
main = puts "Hello"

-- Categorical core (what compiler sees)
-- "Hello" is lifted to a constant morphism Unit -> String Utf8
-- puts "Hello" becomes compose puts "Hello" in IR
```

### Rationale
- **Readability**: `puts "hello"` is immediately clear vs `compose puts "hello"`
- **Familiarity**: Most programmers think in terms of values and function application
- **Categorical core preserved**: The IR remains purely morphisms; elaborator handles translation
- **Point-free still possible**: Users can write `f . g . h` when they want explicit composition
- **Precedent**: Even Haskell, which supports point-free, lets you write `f x` not `f . const x`

The key insight: The categorical foundation provides formal guarantees, but the surface language should be practical and readable.

### Lifting Rules

1. **String literals**: `"hello" : String Utf8` (value in surface syntax)
2. **Application**: `puts "hello" : Unit` (standard function application)
3. **Binding check**: When signature is `A -> B` but expression has type `B`, compiler accepts it
4. **IR generation**: Values become constant morphisms (compose with terminal)

### Consequences
- Surface syntax feels like ML (values, application)
- Type checker allows binding value to morphism type (with implicit lift)
- Elaborator generates categorical IR from value-based surface syntax
- Pure point-free style remains available via `.` operator and explicit `compose`

---

## D019: Composition Operator (.)

**Date**: 2025-12-09
**Status**: Accepted

### Context
With values and application as the default, we needed a way to write explicit composition when desired.

### Decision
Add `.` as an infix operator for composition, desugaring to `compose`.

```
f . g        -- desugars to: compose f g
f . g . h    -- desugars to: compose f (compose g h)  (right-associative)
f x . g y    -- desugars to: compose (f x) (g y)  (application binds tighter)
```

### Rationale
- **Familiar syntax**: Matches Haskell's composition operator
- **Explicit when needed**: For point-free style or when composition is clearer
- **Clean precedence**: Application binds tighter than composition (like Haskell)
- **Right-associative**: `f . g . h` means `f . (g . h)` (like Haskell)

### Examples

```
-- Point-free style (pure categorical)
swap : A * B -> B * A
swap = pair snd fst

-- Alternative with explicit composition
doubleFirst : A * B -> A * A
doubleFirst = pair fst fst

-- Mixed style
process : String Utf8 -> Unit
process = puts . toUpper    -- composition of two morphisms
```

### Consequences
- Parser recognizes `.` as composition operator
- Desugars to `compose` before elaboration
- Both styles (value-based and point-free) work naturally
- Users can choose based on readability for each situation

---

## D020: Point-Free Code Remains Fully Supported

**Date**: 2025-12-09
**Status**: Accepted

### Context
With the introduction of values and implicit lifting (D018), we needed to clarify that pure categorical (point-free) code is still fully supported.

### Decision
Pure point-free code continues to work unchanged. The implicit lifting only applies when types require it.

### Examples of Pure Point-Free Code

```
-- These work exactly as before, no lifting involved
swap : A * B -> B * A
swap = pair snd fst

dup : A -> A * A
dup = pair id id

first : (A -> B) -> A * C -> B * C
first f = pair (f . fst) snd

-- Composition chain
pipeline : A -> D
pipeline = h . g . f
```

### Rationale
- **Generators are morphisms**: `fst`, `snd`, `pair` etc. have morphism types
- **Composition of morphisms**: `pair snd fst` composes morphisms, no values involved
- **No lifting needed**: When types already match as morphisms, no transformation occurs
- **Best of both worlds**: Use point-free for transformations, values for I/O and literals

### When Lifting Occurs

Lifting only happens when:
1. A value (like `"hello"`) appears where a morphism is expected
2. A binding has morphism type (`A -> B`) but expression has value type (`B`)

For pure generator compositions, no lifting is involved.

### Consequences
- Existing point-free code works unchanged
- Performance: no overhead for pure categorical code
- Clear mental model: "values lift, morphisms compose"
- Users can mix styles freely within a program

---

## D021: Canonical as the Standard Derived Library

**Date**: 2025-12-10
**Status**: Accepted

### Context
Once needs a curated set of derived combinators that users can rely on. These are morphisms that arise naturally from universal properties - the "obvious" constructions that every category theorist would recognize. We needed to decide what to call this collection and where it lives.

### Options Considered

1. **Prelude** - Familiar from Haskell, but borrowed terminology
2. **Core** - Generic, not mathematical
3. **Standard** - Generic
4. **Universal** - Emphasizes universal properties
5. **Canonical** - Emphasizes these are "the" natural choices

### Decision
The standard derived library is called **Canonical**. It lives within the Derived stratum as a distinguished, curated collection.

### Rationale

**Why "Canonical":**
- In mathematics, a **canonical morphism** is one that arises uniquely from a universal property
- Products have a canonical `swap : A * B -> B * A`
- Every object has a canonical diagonal `diagonal : A -> A * A`
- These aren't arbitrary choices - they're determined by the structure
- The name signals: "these are the morphisms you'd expect"

**Why not other names:**
- "Prelude" is Haskell jargon without mathematical meaning
- "Core" and "Standard" are generic and don't convey the mathematical nature
- "Universal" is close but refers more to the properties than the morphisms themselves

**What belongs in Canonical:**
Morphisms that arise from universal properties of the categorical structures:

| Structure | Canonical Morphisms |
|-----------|---------------------|
| Products | `swap`, `assocL`, `assocR`, `first`, `second`, `bimap`, `diagonal` |
| Coproducts | `mirror`, `mapLeft`, `mapRight`, `bicase` |
| Terminal | `unit` (alias for `terminal`) |
| Initial | `absurd` (alias for `initial`) |
| Exponential | `flip`, `const`, `(&)` (flip apply) |
| Composition | `(.)`, `(|>)` (pipeline) |

**What does NOT belong in Canonical:**
- Data type definitions (Bool, Maybe, List, Result) - these go in `Initial/` (see D024)
- Domain-specific libraries (JSON, crypto) - these go in `Derived/`
- Anything requiring primitives - that's Interpretations

### Directory Structure

```
Strata/
├── Derived/
│   ├── Canonical.once        -- morphisms from universal properties
│   └── Initial.once          -- data types as initial algebras (see D024)
└── Interpretations/
    └── Linux/
        ├── syscalls.once
        └── memory.once
```

### Note on Imports
The `import` syntax is not yet implemented in the compiler. This decision establishes the naming and organization; the import mechanism will be added in a future phase (see implementation plan).

### Consequences
- `Canonical/` is a curated, stable collection - additions are carefully considered
- Each file in `Canonical/` corresponds to a categorical structure
- The name communicates mathematical intent to users familiar with category theory
- Users unfamiliar with the term will learn it means "standard" or "natural"
- Requires implementing an import/module system (future work)

---

## D022: Agda for Formal Verification

**Date**: 2025-12-10
**Status**: Accepted

### Context
Once is designed to be formally verifiable. We needed to choose a proof assistant for mechanizing the verification of the compiler. The choice affects both the verification effort and how verified code integrates with the existing Haskell codebase.

### Options Considered

1. **HOL4** - Used by CakeML, mature, classical logic
2. **Coq** - Used by CompCert, largest community, good automation
3. **Lean 4** - Modern, fast, excellent tooling, growing community
4. **Agda** - Haskell extraction, category theory libraries, PL community
5. **Idris 2** - Native QTT support, but too immature

### Decision
Use **Agda** for formal verification, with extraction to Haskell.

### Rationale

**Why Agda:**

1. **Haskell extraction**: Once's compiler is Haskell. Agda extracts directly to Haskell via MAlonzo, enabling incremental replacement of unverified code with verified code.

2. **agda-categories**: A mature category theory library that models cartesian closed categories - exactly what Once's 12 generators are.

3. **PL community alignment**: QTT research and type theory papers often use Agda. The community that cares about linear types uses Agda.

4. **Proofs are programs**: Agda's philosophy matches Once's - both emphasize that the code IS the specification.

**Why not HOL4:**
- Small community, SML-centric
- Once is Haskell, not SML

**Why not Coq:**
- Haskell extraction is awkward compared to Agda
- More automation, but Once's proofs are simple enough not to need it

**Why not Lean 4:**
- No Haskell extraction (compiles to C)
- Would require either rewriting Once in Lean or maintaining parallel implementations

**Why not Idris 2:**
- Native QTT is attractive, but ecosystem too immature
- Smaller community, less tooling

### Architecture

```
┌─────────────────────────────────────────┐
│          Verified Core (Agda)           │
│  - IR, semantics, type checker, codegen │
│  - Proofs of correctness                │
└────────────────┬────────────────────────┘
                 │ MAlonzo extraction
                 ▼
┌─────────────────────────────────────────┐
│         Unverified Shell (Haskell)      │
│  - Parser, CLI, File IO                 │
└─────────────────────────────────────────┘
```

The security-critical core is verified. The plumbing (parser, CLI) is not - those aren't where the important bugs are.

### Trusted Computing Base

- Agda's type checker
- MAlonzo extraction
- GHC
- The C compiler (for generated code)
- OS and hardware

This is comparable to CakeML (HOL4 + PolyML + OS) and CompCert (Coq + OCaml + OS).

### Estimated Effort

| Component | Lines of Agda | Time |
|-----------|---------------|------|
| Core IR + Semantics | ~300 | 1-2 weeks |
| Categorical laws | ~400 | 2-3 weeks |
| Type system + soundness | ~500 | 3-4 weeks |
| QTT properties | ~400 | 2-3 weeks |
| C backend correctness | ~1000 | 6-8 weeks |
| **Total** | **~2600** | **~4 months** |

Compare to CakeML (~100,000 lines) and CompCert (~100,000 lines). Once is ~40x simpler due to its minimal design.

### Consequences
- Agda becomes a project dependency for verification work
- Verified code can incrementally replace unverified Haskell
- QuickCheck properties are "theorem-shaped" - each corresponds to an Agda theorem
- The PL community will accept Agda proofs
- See `docs/design/formal/verification-strategy.md` for full details

---

## D023: No Exceptions

**Date**: 2025-12-11
**Status**: Accepted

### Context
Many programming languages provide exceptions as an error-handling mechanism. We needed to decide whether Once should support exceptions.

### Decision
**Exceptions will never be implemented in Once.**

### Rationale

**1. Not expressible with generators**

The 12 generators form a cartesian closed category (CCC). Exceptions require **non-local control flow** - the ability to "jump" out of a computation at any point, bypassing intermediate stack frames. This is fundamentally incompatible with the compositional structure of morphisms:

- `case` is local: `case f g : A + B -> C` handles both branches at the point of consumption
- Exceptions are non-local: `throw` jumps past multiple stack frames to a distant `catch`

To express exceptions categorically would require something like continuations, effect handlers, or monads - none of which are part of the CCC structure.

**2. Difficult to formally verify**

Exceptions break compositionality. When verifying `compose f g`, you cannot reason locally about `f` and `g` because either might throw, transferring control elsewhere. This makes proofs significantly harder:

- Must track all possible exception paths
- Compositional reasoning breaks down
- Denotational semantics becomes complex

**3. Difficult to reason about**

The same property that makes exceptions hard to verify makes them hard to think about:

- A function's type `A -> B` doesn't reveal it might throw
- Control flow is implicit and non-local
- Exception safety requires careful manual reasoning

**4. Sum types are the right solution**

Once already has explicit error handling via sum types:

```
parseJson : String -> Json + ParseError
readFile : Path -> IO (Buffer + IOError)
```

Benefits:
- Errors are visible in the type - you cannot ignore them
- Local handling - errors are handled where they occur
- Compositional - `case` composes normally
- Verifiable - standard CCC reasoning applies

### Consequences
- No `throw`, `catch`, `try`, or similar constructs
- All error cases must be represented in types (typically as sum types)
- Code is more explicit about failure modes
- Formal verification remains tractable
- Once programs are easier to reason about

### See Also
- [Design Philosophy](../design/design-philosophy.md) - Error handling section
- [IO](../design/io.md) - Effects as functor choice

---

## D024: Initial as the Standard Data Type Library

**Date**: 2025-12-11
**Status**: Accepted

### Context
Once needs a curated set of standard data types. In D021, we established `Canonical/` for morphisms arising from universal properties. We needed a parallel concept for data types.

### Options Considered

1. **Data/** - Generic name
2. **Algebra/** - Mathematical, refers to algebraic data types
3. **Initial/** - Category theory term for how these types are constructed
4. **Base/** - Haskell convention
5. **Data.Initial/** - Nested under Data

### Decision
The standard data type library is called **Initial**. It lives parallel to `Canonical/` within the Derived stratum.

### Rationale

**Why "Initial":**
In category theory, these data types are **initial algebras**:

| Type | Initial Algebra Of |
|------|-------------------|
| `Bool` | `1 + 1` (two-element set) |
| `Maybe A` | `1 + A` (optional value) |
| `List A` | `1 + A × X` (recursive list) |
| `Result A E` | `A + E` (success or error) |

The initiality property gives these types their universal character - they are "the" canonical representations of these patterns, just as `Canonical/` morphisms are "the" canonical transformations.

**Why parallel to Canonical:**
- `Canonical`: morphisms from universal properties
- `Initial`: data types from initial algebras
- Both are mathematical terms at the same level
- Clean symmetry in the library structure

**What belongs in Initial:**
- `Bool` - the two-element type
- `Maybe` - optional values
- `List` - sequences
- `Result` - success/error handling (see D025)
- Other initial algebra constructions

**What does NOT belong in Initial:**
- Terminal coalgebras (streams, infinite structures) - future `Terminal/` library
- Domain-specific types (Json, HttpRequest) - go in `Derived/`
- Types requiring primitives - that's Interpretations

### Directory Structure

```
Strata/
├── Derived/
│   ├── Canonical.once    -- morphisms from universal properties
│   └── Initial.once      -- data types as initial algebras
└── Interpretations/      -- platform-specific IO
```

### Consequences
- `Initial.once` is a curated, stable collection parallel to `Canonical.once`
- The name communicates mathematical intent
- Future: `Terminal/` for coalgebraic types (streams, etc.)
- Requires implementing an import/module system (future work)

---

## D025: Result Type Convention (Success-Left)

**Date**: 2025-12-11
**Status**: Accepted

### Context
Error handling in Once uses sum types (see D023). We needed to decide on a convention for the `Result` type - which side represents success and which represents error.

### Options Considered

1. **Haskell convention** - `Either E A` where Left = error, Right = success
2. **Success-left** - `Result A E = A + E` where Left = success, Right = error
3. **No convention** - Just use `A + E` with `inl`/`inr` directly

### Decision
Adopt **success-left** convention: `Result A E = A + E` where `ok = inl` (success) and `err = inr` (error).

### Rationale

**Why not Haskell's convention:**
- "Left = error" is arbitrary and counterintuitive to many
- No categorical basis for this choice
- Just historical accident in Haskell

**Why success-left:**
- Success is the primary/expected case - put it first
- Reading left-to-right, you see the happy path first
- `inl` = "in left" = "in success" feels natural
- Still arbitrary, but more intuitive than Haskell

**Why in Initial/, not Canonical/:**
- `Result` is a type alias with semantic conventions (`ok`/`err`)
- `Canonical/` is for morphisms from universal properties
- `ok` and `err` are convenient names, not categorical necessities
- This is a data type definition, belongs with `Bool`, `Maybe`, `List`

### Definition

```
-- In Initial/Result.once

type Result A E = A + E

ok : A -> Result A E
ok = inl

err : E -> Result A E
err = inr

-- Combinators
mapResult : (A -> B) -> Result A E -> Result B E
mapResult f = case (ok . f) err

bindResult : (A -> Result B E) -> Result A E -> Result B E
bindResult f = case f err
```

### Usage Example

```
parseNumber : String -> Result Int ParseError
parseNumber s = ...

validatePositive : Int -> Result Int ValidationError
validatePositive n = case (n > 0) of
  true  -> ok n
  false -> err ValidationError.NotPositive

-- Chaining
parseAndValidate : String -> Result Int Error
parseAndValidate = bindResult validatePositive . parseNumber
```

### Consequences
- Consistent error handling convention across Once code
- `ok`/`err` are semantic aliases for `inl`/`inr`
- Success-left is the standard, documented convention
- Users can still use raw `A + E` with `inl`/`inr` if preferred

---

## D026: IO is a Monad

**Date**: 2025-12-11
**Status**: Superseded by D032 (effects are ARROWS `Eff A B`; the monad lives in the semantics — `T`, D257 — not in the surface language). Status updated 2026-10-09 (plan 0.113 E).

### Context
Once needs a way to handle input/output and other effects. We needed to decide how to represent IO and whether to be explicit about its mathematical nature.

### Options Considered

1. **Call it `External`** - A functor marking "needs external world", avoid monad terminology
2. **Call it `IO`** - Standard name, be honest that it's a monad
3. **Use effect handlers** - More complex, different abstraction
4. **World-passing style** - Make state explicit in types

### Decision
**IO is a monad, and we call it that.**

Once uses `IO` as the standard name for effectful computations. We are honest that it's a monad, providing all three levels of composition:

```
-- Functor
fmap : (A -> B) -> IO A -> IO B

-- Applicative
pure : A -> IO A
both : IO A -> IO B -> IO (A * B)

-- Monad
bind : IO A -> (A -> IO B) -> IO B
```

### Rationale

**Why be honest about monads:**
- If it has `bind` with the monad laws, it's a monad - calling it something else is misleading
- Programmers familiar with monads immediately understand Once's IO
- Mathematical honesty is a Once principle

**Why `IO` not `External`:**
- `IO` is the standard name in the PL community (Haskell, Scala, etc.)
- `External` requires explanation; `IO` is self-documenting
- Being different for the sake of being different doesn't help users

**Why all three levels:**
- Functor: transform results without changing effects
- Applicative: combine independent effects (can parallelize)
- Monad: sequence dependent effects (inherently sequential)

Users should prefer the weakest level that works - this isn't just style, it affects what optimizations are possible.

### Definition

```
-- IO is an opaque type provided by the runtime
IO : Type -> Type

-- Functor
fmap : (A -> B) -> IO A -> IO B

-- Applicative
pure : A -> IO A
both : IO A -> IO B -> IO (A * B)

-- Monad
bind : IO A -> (A -> IO B) -> IO B
join : IO (IO A) -> IO A

-- Laws: standard monad laws hold
```

### IO Primitives

IO operations come from primitives in the Interpretations layer:

```
primitive readFile  : Path -> IO (String + Error)
primitive writeFile : Path * String -> IO (Unit + Error)
primitive getLine   : Unit -> IO String
primitive putLine   : String -> IO Unit
```

### Consequences
- `IO` is the standard name for effectful computations
- Documentation is honest about IO being a monad
- All three composition levels available (functor, applicative, monad)
- Familiar to programmers from Haskell, Scala, etc.
- Renamed from `External` in earlier documentation

### See Also
- [IO Documentation](../design/io.md) - Full IO documentation with examples

---

## D027: No Implicit Imports

**Date**: 2025-12-12
**Status**: Accepted

### Context
Many languages provide a "prelude" that is implicitly imported. We needed to decide whether Once should have implicit imports.

### Decision
**No implicit imports except generators.** All imports must be explicit. The 12 generators are always available as they are the language primitives.

### Rationale
- Implicit dependencies like a "prelude" often include OS dependencies
- Even if those are compilable on Windows/Mac/Linux, they're not compilable on all bare-metal platforms
- Users would have to actively remove the prelude and include their own
- Better to be explicit from the start
- Aligns with Once's philosophy of transparency and portability
- Generators are different: they ARE the language, not imported functionality

### Consequences
- Generators (id, compose, fst, snd, pair, inl, inr, case, terminal, initial, curry, apply) are always available
- Everything else requires explicit import
- No hidden dependencies that break on new platforms
- Slightly more verbose, but completely predictable
- Easier to port to new targets

---

## D028: Use Nix for Project Configuration

**Date**: 2025-12-12
**Status**: Accepted

### Context
The implementation plan mentioned adding a project configuration file for Once projects. We needed to decide whether to create a custom format or use existing tooling.

### Decision
**Use Nix for project configuration.** No custom project file format.

### Rationale
- Nix already handles dependency management, build configuration, and reproducibility
- Creating a custom project file would reinvent the wheel
- Nix is already a project dependency (used for building the compiler)
- Nix flakes provide standardized project structure

### Mitigating Nix Learning Curve
- Provide library functions that make Nix integration easy
- Goal: using Nix should be as simple as maintaining a custom YAML format
- Templates and examples in documentation

### Consequences
- Once projects use `flake.nix` for configuration
- No `once.yaml`, `once.toml`, or similar custom format
- Leverages existing Nix ecosystem and tooling
- Library functions reduce friction for users unfamiliar with Nix

---

## D029: Let Bindings with Desugaring

**Date**: 2025-12-12
**Status**: Accepted

### Context
Adding let bindings to Once for local variable introduction. Multiple design options exist:

1. **Single binding only**: `let x = e in body`
2. **Multiple bindings with comma**: `let x = e1, y = e2 in body`
3. **Multiple bindings with semicolon**: `let x = e1; y = e2 in body`
4. **Multiple bindings with newline/layout**: Like Haskell's layout rule

### Decision
**Semicolon-separated multiple bindings** that **desugar to nested lets**.

```once
let x = e1; y = e2; z = e3 in body
```

Desugars to:
```once
let x = e1 in let y = e2 in let z = e3 in body
```

### Rationale
- **Desugaring over special AST node**: Keeps the core AST simple (single `ELet Name Expr Expr` node). This simplifies verification since we only need to verify single let semantics.
- **Semicolon over comma**: Semicolons are visually distinct from commas in expressions, making parsing unambiguous without complex lookahead.
- **Semicolon over layout**: Layout-sensitive parsing (like Haskell) is complex to implement correctly and can be confusing. Explicit delimiters are more predictable.
- **Later bindings can reference earlier ones**: The desugaring to nested lets naturally provides this - `y` is in scope when evaluating `z`.

### Consequences
- Simple parser implementation using `sepBy1`
- Single `ELet` AST node handles all cases after desugaring
- No layout sensitivity required
- Users can write `let x = a; y = b; z = c in body` on one line or split across lines

### Verification Status

Let bindings are **covered by existing Agda proofs** without requiring new theorems. The key insight is that `let` is syntactic sugar:

```
let x = e1 in e2   ≡   (λx. e2) e1
```

The elaborator translates `ELet x e1 e2` to IR using this equivalence. Since `lam` and `app` are already proven correct in `Once/Surface/Correct.agda` (via `elaborate-correct`), let bindings inherit correctness automatically.

No changes to the Agda formalization are required because:
1. `let` doesn't add new expressive power - it's pure convenience
2. The desugared form (`app (lam e2) e1`) is already covered
3. The `elaborate-correct` theorem proves the elaboration preserves semantics

---

## D030: Function References (FunRef) and Threading

**Date**: 2025-12-12
**Status**: Accepted

### Context
To pass functions as arguments to primitives like `thread_spawn`, we needed a way to generate function pointers in C rather than function calls. The expression `thread_spawn worker` should pass `worker` as a value, not call it.

### Decision
Add `FunRef` IR node for function references.

**IR change**:
```haskell
| FunRef Name  -- Function reference (pointer, not call)
```

**Elaboration heuristic**: When a variable is passed as an argument and it's not a generator or local binding, use `FunRef` instead of `Var`.

**C codegen**:
- `Var "f"` → `once_f(x)` (function call)
- `FunRef "f"` → `(void*)once_f` (function pointer)

### Verification Status

**FunRef does NOT require changes to the Agda formalization** because:

1. The Agda IR only models the pure categorical generators (id, compose, fst, snd, pair, inl, inr, case, terminal, initial, curry, apply, fold, unfold)

2. `Var`, `LocalVar`, `FunRef`, `Prim`, `StringLit`, and `Let` are **implementation-level constructs** in the Haskell IR that don't appear in the formal model

3. These nodes handle name resolution, primitives, and syntactic sugar - concerns outside the pure categorical semantics

The formal guarantees apply to the categorical core. Implementation mechanisms like `FunRef` are in the "interpretation layer" - trusted but not formally verified.

### Consequences
- Functions can be passed to primitives like `thread_spawn worker`
- Clear separation: Agda proves categorical core, C codegen is trusted
- Simple heuristic-based elaboration (may need refinement for complex cases)

---

## D031: Raw Syscall Threading (x86_64)

**Date**: 2025-12-12
**Status**: Accepted

### Context
The Thread.c implementation needed to spawn threads using the `clone` syscall. The naive approach (using raw `syscall(SYS_clone, ...)`) failed because clone returns in both parent and child at the same instruction, causing stack corruption when both try to execute.

### Options Considered

1. **Use glibc clone() wrapper** - Works but adds glibc dependency
2. **Use pthread** - Works but adds pthread dependency
3. **Raw syscall with inline assembly** - Pure syscall interface, x86_64 specific

### Decision
**Raw syscall with inline assembly** (option 3).

The key insight is that glibc's `clone()` wrapper:
1. Pushes function pointer and argument onto the NEW stack before clone
2. After clone returns 0 (in child), pops and calls the function
3. Child exits via syscall, never returns to C code

We implement this directly:

```c
static pid_t raw_clone_with_fn(void (*fn)(void*), void* stack_top, int flags, void* arg) {
    pid_t ret;
    void** sp = (void**)stack_top;
    *--sp = arg;        /* Push arg */
    *--sp = (void*)fn;  /* Push fn */

    __asm__ volatile(
        "syscall\n\t"
        "test %%rax, %%rax\n\t"
        "jnz 1f\n\t"
        /* Child: pop fn, pop arg, call fn(arg), exit */
        "pop %%rax\n\t"
        "pop %%rdi\n\t"
        "call *%%rax\n\t"
        "mov $60, %%eax\n\t"
        "xor %%edi, %%edi\n\t"
        "syscall\n\t"
        "1:\n\t"
        : "=a"(ret)
        : "a"(SYS_clone), "D"(flags), "S"(sp), ...
    );
    return ret;
}
```

### Rationale
- **Keeps impure code at the edge** - Only Thread.c has assembly, rest is pure C
- **No library dependencies** - Just Linux syscalls
- **Educational** - Shows how threading actually works

### Limitations

1. **x86_64 only** - The inline assembly is architecture-specific. Other architectures (ARM, RISC-V) would need their own implementations.

2. **No thread pool** - Each spawn allocates a fresh 4MB stack. For many short-lived threads, this is inefficient.

3. **Simplified interface** - Current API:
   ```once
   thread_spawn : (Unit -> Unit) -> Buffer
   thread_join : Buffer -> Unit
   ```

   Limitations:
   - Threads can only return Unit (no return values)
   - Buffer is untyped (should be `Thread` type)
   - No error handling for spawn failures

### Future Improvements

A richer threading abstraction could use categorical structure:

```once
-- Typed thread handles
Thread : Type -> Type

-- Fork returns result
thread_spawn : (Unit -> A) -> Thread A
thread_join : Thread A -> A

-- Categorical combinators
parallel : Thread A -> Thread B -> Thread (A * B)  -- product
race : Thread A -> Thread A -> Thread A            -- coproduct
```

This would require:
- Type aliases or higher-kinded types
- More sophisticated codegen for Thread type

### Performance

Current implementation is comparable to pthread:
- **Stack**: 4MB mmap (same as pthread default)
- **Clone**: Single syscall + assembly trampoline
- **Sync**: Futex-based (kernel-assisted, efficient)

The main overhead is stack allocation per thread. A thread pool would amortize this.

### Consequences
- Threading works on x86_64 Linux
- Other architectures need separate implementations
- Simple but limited API (Unit -> Unit functions only)
- Clear path to richer abstractions when needed

---

## D032: Arrow-Based Effect System (Eff)

**Date**: 2025-12-12
**Status**: Accepted

### Context

Once has an implicit lifting bug in the type checker (TypeCheck.hs lines 437-440) where expressions of type `B` are silently lifted when `A -> B` is expected. This allows effectful code to masquerade as pure functions:

```once
println "hello" : Unit
-- Gets implicitly lifted to Unit -> Unit
-- Can be used where a pure function is expected!
```

This breaks equational reasoning - we cannot distinguish pure from effectful code by looking at types.

### Options Considered

1. **IO Monad** (Haskell-style)
   - `type IO : Type -> Type`
   - `println : String -> IO Unit`
   - Composition via `bind : IO A -> (A -> IO B) -> IO B`

2. **Arrow-based Eff**
   - `type Eff : Type -> Type -> Type`
   - `println : Eff String Unit`
   - Composition via `(>>>) : Eff A B -> Eff B C -> Eff A C`

3. **No explicit effects**
   - Keep current model, fix lifting bug only
   - Effects remain implicit in semantics

### Decision

Adopt **arrow-based effect system** with `Eff A B` for effectful morphisms:

```once
-- Effectful morphism type
type Eff : Type -> Type -> Type

-- Lift pure functions to effectful
arr : (A -> B) -> Eff A B

-- Effectful primitives
println : Eff String Unit
readLine : Eff Unit String

-- IO as sugar for nullary effects (familiar to Haskell users)
type IO A = Eff Unit A

-- Main is effectful
main : IO Unit  -- or equivalently: main : Eff Unit Unit
```

### Rationale

**Why Arrows over Monads:**

1. **Once's generators are already arrow-like**:
   - `compose` = `(>>>)` (sequential composition)
   - `pair` = `(&&&)` (parallel composition)
   - `case` = `(|||)` (choice)
   - `curry`/`apply` = ArrowApply

2. **Uniform composition**: Everything uses `(>>>)`, no need for two operators (`.` and `>>=`)

3. **Natural embedding**: Pure functions embed via `arr`, no explicit lifting needed

4. **Simpler verification**: One unified category instead of tracking pure vs Kleisli categories

5. **More general**: Every monad gives rise to an arrow, but not vice versa (Arrows ⊃ Monads)

**Why IO sugar:**
- Familiar to Haskell users (`IO ()` vs `Eff Unit Unit`)
- `IO A = Eff Unit A` (effectful computation with no input)
- No semantic difference, purely ergonomic

**Why remove implicit lifting:**
- The lifting bug was introduced for convenience but breaks reasoning
- Effectful code MUST be explicitly typed
- Pure functions require `arr` to be used in effectful context

### Implementation

**Type-level only**: `Eff A B` compiles to the same C code as `A -> B`. The distinction exists purely for type checking.

**New type constructor**:
```haskell
-- In Type.hs
data Type = ... | TEff Type Type

-- In Syntax.hs
data SType = ... | STEff SType SType
```

**Parser recognizes**:
- `Eff A B` → `STEff A B`
- `IO A` → `STEff STUnit A` (sugar)

**Unification**:
- `TEff` unifies with `TEff`
- `TEff` does NOT unify with `TArrow` (core of effect system)

**New generator**:
- `arr : (A -> B) -> Eff A B` (lifts pure to effectful)

### Eff vs Result (see D025)

These are orthogonal concepts:
- `Result A E = A + E` is a **value** (sum type)
- `Eff A B` is a **morphism** (effectful function)

They work together:
```once
readFile : Eff String (Result String Error)
-- Effectful operation that may fail
```

### Migration

**Before** (broken):
```once
primitive println : String -> Unit
main : Unit -> Unit
main = compose println (compose (\_ -> "hello") terminal)
```

**After**:
```once
primitive println : Eff String Unit
main : IO Unit
main = compose println (compose (arr (\_ -> "hello")) terminal)
```

### Arrow Laws (for verification)

```
arr id >>> f           = f                    -- left identity
f >>> arr id           = f                    -- right identity
(f >>> g) >>> h        = f >>> (g >>> h)      -- associativity
arr (f . g)            = arr g >>> arr f      -- arr preserves composition
```

### Consequences

- **Breaking change**: All effectful code must use `Eff`/`IO` types
- Pure functions (A -> B) are guaranteed side-effect free
- Effect tracking enables verification of purity
- Fixes the implicit lifting bug permanently
- Users can use familiar `IO` notation
- Foundation for future effect indexing (e.g., `Eff [Console, File] A B`)

### See Also

- D025: Result Type Convention (Success-Left)
- D023: Error Handling via Sum Types
- docs/design/effects-proposal.md (detailed comparison)

---

## D033: Module Import System with Path Abbreviations

**Date**: 2025-12-13
**Status**: Accepted

### Context

Once programs need to import definitions from the Strata directory structure:
- `Strata/Derived/` - Pure library code (morphisms, utilities)
- `Strata/Interpretations/` - Platform-specific I/O implementations

The import syntax was already parsed (D027) but module resolution was not implemented.

### Decision

Implement module resolution with **hardcoded path abbreviations**:
- `I.` expands to `Interpretations.` (e.g., `import I.Linux.Syscalls`)
- `D.` expands to `Derived.` (e.g., `import D.Simple`)

### Rationale

**Why abbreviations:**
- The three strata (Generators, Derived, Interpretations) are fundamental to Once's architecture
- Full paths like `Interpretations.Linux.Syscalls` are verbose
- Single-letter abbreviations match the conceptual structure (I for Interpretation, D for Derived)
- Generators don't need imports (they're reserved words per D001)

**Why hardcoded:**
- The strata structure is fixed by design
- Configurability would add complexity without benefit
- Matches Once's philosophy of minimal, principled design

### Implementation

**New module**: `Once/Module.hs`
- `expandAbbreviations` - Expands I./D. to full paths
- `loadModuleFile` - Parses module from Strata directory
- `resolveImports` - Loads all imported modules with cycle detection
- `lookupQualified` - Resolves `name@Module.Path` expressions

**CLI changes**:
- `--strata PATH` flag to specify Strata directory location
- Auto-detection of Strata/ relative to input file

**Type checking/Elaboration**:
- `checkModuleWithEnv` / `inferTypeWithEnv` - Module-aware type inference
- `elaborateWithEnv` - Resolves qualified names to actual definitions

### Usage

```once
import D.Simple as S

mySwap : A * B -> B * A
mySwap = swap@S
```

### Cycle Detection

Cyclic imports are **errors** (not allowed):
```
Module error: Cyclic import detected: A -> B -> C -> A
```

### Consequences

- Qualified names (`swap@S`) resolve to imported definitions
- Type checking verifies imported types match usage
- Elaboration inlines imported definitions
- C files from Interpretations are automatically included
- V1 limitations: no re-exports, no unqualified imports, no wildcards

### See Also

- D009: Interpretations Outside Compiler
- D027: No Implicit Imports

---

## D034: Target Architecture Flag

**Date**: 2025-12-13
**Status**: Accepted

### Context

Once aims to support multiple target architectures:
- C backend (current, via gcc)
- x86-64 assembly (future)
- ARM64 assembly (future)
- RISC-V 64-bit (future)

Each target requires different interpretation files alongside the `.once` declarations.

### Decision

Add `--target <arch>` CLI flag with target-specific file extensions:

| Target | Extension | Description |
|--------|-----------|-------------|
| `c` | `.c` | C backend (default) |
| `x86_64` | `.x86_64` | x86-64 assembly |
| `arm64` | `.arm64` | ARM64 assembly |
| `riscv64` | `.riscv64` | RISC-V 64-bit |

### Directory Structure

```
Strata/Interpretations/Linux/
├── syscalls.once       # Type declarations (shared)
├── syscalls.c          # C implementation
├── syscalls.x86_64     # x86-64 assembly (future)
└── syscalls.arm64      # ARM64 assembly (future)
```

### Implementation

**Types** (`Once/CLI.hs`):
```haskell
data Target = TargetC | TargetX86_64 | TargetArm64 | TargetRiscV64

targetExtension :: Target -> String
targetExtension TargetC = ".c"
targetExtension TargetX86_64 = ".x86_64"
-- etc.
```

**Module environment** (`Once/Module.hs`):
- `meTargetExt` field stores target extension
- `loadModuleFile` finds target-specific files
- `lmTargetPath` (renamed from `lmCPath`) stores path

### Usage

```bash
# Default (C backend)
once build --exe hello.once -o hello

# Explicit target
once build --exe --target c hello.once -o hello

# Future targets (graceful error)
once build --exe --target x86_64 hello.once
# Error: Target 'TargetX86_64' not yet implemented
# Hint: Use --target c for C backend
```

### Consequences

- One `.once` file pairs with multiple target implementations
- Module loading automatically finds correct target file
- Future assembly backends can be added incrementally
- V1: Only `TargetC` is implemented

### See Also

- D009: Interpretations Outside Compiler
- D033: Module Import System

---

## D035: Two-Stage IR and MAlonzo Compilation

**Date**: 2025-12-13
**Status**: Accepted

### Context

The Once compiler has two IR definitions:
- **Agda IR** (`formal/Once/IR.agda`): 13 pure categorical constructors + fold/unfold + arr
- **Haskell IR** (`compiler/src/Once/IR.hs`): Same plus Let, LocalVar, Var, FunRef, Prim, StringLit

The goal is to generate the optimizer (and eventually entire compiler) from verified Agda code using MAlonzo (Agda's Haskell backend).

### Problem

The IR mismatch creates integration challenges:
1. **Extend Agda IR?** Adding Let, Var, etc. means every proof needs extra cases, complicating verification
2. **Wrapper approach?** Keeping Agda pure with Haskell wrapper means two IRs to maintain
3. **Replace Haskell IR?** Requires major refactor, may lose useful constructs

### Decision

**Two-stage IR architecture in Agda**:

```
Surface IR (Agda)     -- has Let, Prim, ConstStr
      ↓
  desugar (Agda)      -- expand to categorical form
      ↓
Core IR (Agda)        -- pure categorical (current Once.IR)
      ↓
  optimize (Agda)     -- verified optimizer (current Once.Optimize)
      ↓
  codegen (Agda)      -- generate assembly (current Once.Backend.X86)
```

### Surface IR Design

```agda
data SurfaceIR : Type → Type → Set where
  -- All Core IR constructors embedded
  id, _∘_, fst, snd, ⟨_,_⟩, inl, inr, [_,_],
  terminal, initial, curry, apply, fold, unfold, arr

  -- Surface-only constructs
  Let      : ∀ {A B C} → SurfaceIR A B → SurfaceIR (A * B) C → SurfaceIR A C
  Prim     : ∀ {A B} → String → SurfaceIR A B
  ConstStr : String → SurfaceIR Unit StringType
```

**Key insight**: `Let` uses De Bruijn style - the body receives `(original-input, bound-value)` via `fst`/`snd`. No named `LocalVar` needed!

### Desugar Transformation

```agda
desugar : ∀ {A B} → SurfaceIR A B → CoreIR A B
desugar (Let e1 e2) = desugar e2 ∘ ⟨ id , desugar e1 ⟩
desugar (Prim name) = prim name
desugar (ConstStr s) = constStr s ∘ terminal
desugar (f ∘ g) = desugar f ∘ desugar g
-- ... structural recursion ...
```

The categorical translation of `let`:
```
let x = e1 in e2   ≡   e2 ∘ ⟨id, e1⟩
```
where `e2` uses `fst` for original input and `snd` for bound value.

### Rationale

1. **Core IR stays minimal**: Optimizer proofs don't need Let cases
2. **Desugar is trivial**: Structural recursion with one interesting case
3. **Existing proofs unchanged**: Once.Optimize.Correct works as-is
4. **MAlonzo generates everything**: Full pipeline from verified Agda
5. **Clear separation**: Naming/binding is Surface concern, computation is Core

### Consequences

- Agda formalization grows but stays modular
- Haskell compiler becomes thin wrapper calling MAlonzo-generated functions
- Path to fully verified compiler (desugar → optimize → codegen all in Agda)
- D029 (Let Bindings) still applies to surface syntax; this decision covers IR representation

### See Also

- D029: Let Bindings with Desugaring (surface syntax)
- [MAlonzo Compilation](../design/malonzo-compilation.md) (detailed design)

---

## D036: Generate Compiler from Agda via MAlonzo

**Date**: 2025-12-13
**Status**: Accepted

### Context

Once has two parallel implementations:
- **Agda formalization** (`formal/`): Verified IR, optimizer, semantics
- **Haskell compiler** (`compiler/`): Unverified but complete

The Haskell optimizer implements the same categorical laws as the Agda version, but isn't formally verified. We needed to decide whether to:

1. **Implement directly**: Keep separate Haskell implementation, use QuickCheck for testing
2. **Generate from Agda**: Use MAlonzo to generate Haskell from verified Agda code

### Decision

**Generate the compiler from Agda via MAlonzo.**

The verified Agda code is compiled to Haskell using Agda's MAlonzo backend:
```bash
cd formal && make malonzo
```

This generates:
- `MAlonzo.Code.Once.Compile` - Main entry point
- `MAlonzo.Code.Once.Optimize` - Verified optimizer (~77KB)
- `MAlonzo.Code.Once.Surface.{IR,Desugar}` - Surface IR handling
- ~222 supporting modules (stdlib, data types)

The Haskell compiler becomes a thin wrapper that:
1. Parses `.once` files (not verified)
2. Type-checks (not verified)
3. Elaborates to Surface IR (not verified)
4. Calls MAlonzo-generated `d_compile_8` (**verified**)
5. Code-generates to C/assembly (partially verified via x86 backend)

### Rationale

**Why generate:**

1. **Single source of truth**: The Agda code IS the specification AND implementation. No drift possible.

2. **Verified by construction**: The optimizer is proven correct in Agda. MAlonzo extraction is part of the TCB, but much smaller than trusting a hand-written Haskell optimizer.

3. **Incremental adoption**: We can replace one component at a time:
   - Phase 1: optimizer (done - generates 77KB Haskell)
   - Phase 2: desugar (done)
   - Phase 3: x86 codegen (in progress)
   - Phase 4: parser/type-checker (future, if ever)

4. **MAlonzo is mature**: Used in production by other verified compilers. Trusted by the Agda community.

**Why not implement directly:**

1. **Duplication**: Maintaining two implementations (Agda for proofs, Haskell for execution) means bugs in Haskell version aren't caught by proofs.

2. **Drift risk**: Even with careful discipline, Haskell and Agda can diverge over time.

3. **Wasted effort**: If we're already writing the Agda code, why write it again in Haskell?

### Technical Details

**MAlonzo compilation command:**
```bash
agda -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Compile.agda
```

**Generated entry point:**
```haskell
-- MAlonzo.Code.Once.Compile
d_compile_8 :: T_Type_4 -> T_Type_4 -> T_SurfaceIR_6 -> T_IR_4
d_compile_8 v0 v1 v2 = coe
    MAlonzo.Code.Once.Optimize.d_optimize_612 v0 v1
    (MAlonzo.Code.Once.Surface.Desugar.d_desugar_16 v0 v1 v2)
```

**Integration point:**
The Haskell compiler will import and call these generated functions, converting between Haskell IR and MAlonzo types.

### Trusted Computing Base (TCB)

With MAlonzo generation, the TCB is:
1. **Agda type checker** - Verifies proofs
2. **MAlonzo extraction** - Translates Agda to Haskell
3. **GHC** - Compiles generated Haskell
4. **Haskell wrapper** - Parser, type-checker, elaborator (unverified)
5. **OS/hardware** - Execution platform

The verified optimizer is NOT in the TCB - it's proven correct.

### Consequences

- Compiler depends on MAlonzo-generated code
- Build process runs `make malonzo` to regenerate after Agda changes
- ~222 Haskell files generated (stdlib support, data types, etc.)
- Generated code is readable but not intended for manual editing
- Postulates require FFI bindings (e.g., `Prim` evaluation)

### See Also

- D035: Two-Stage IR and MAlonzo Compilation
- [MAlonzo Compilation Design](../design/malonzo-compilation.md)

---

## D037: Polynomial Functors for Recursive Type Semantics

**Date**: 2025-12-14
**Status**: Accepted

### Context

The formal semantics had a known limitation (S1 in `what-is-proven.md`): the `Fix F` type used a trivial newtype wrapper rather than true recursive semantics. This meant `fold`/`unfold` proofs were trivially `refl` instead of proving the actual fixed point isomorphism `μF ≅ F(μF)`.

Four options were analyzed in `docs/formal/fix-semantics-options.md`:
1. **Polynomial Functors** - Universe of strictly positive type expressions
2. **Sized Types** - Agda's sized types for termination
3. **Well-Founded Recursion** - Explicit termination proofs
4. **QIITs** - Quotient inductive-inductive types

### Decision

Use **Polynomial Functors** (Option 1) implemented in `formal/Once/SPF.agda`.

### Implementation

The SPF module provides:

```agda
-- Functor codes (strictly positive type expressions)
data Functor : Set₁ where
  K    : Type → Functor           -- Constant
  Id   : Functor                  -- Recursive position
  _⊕_  : Functor → Functor → Functor  -- Sum
  _⊗_  : Functor → Functor → Functor  -- Product

-- Functor interpretation
⟦_⟧F : Functor → Set → Set

-- Proper fixed point (initial algebra)
data μ (F : Functor) : Set where
  ⟨_⟩ : ⟦ F ⟧F (μ F) → μ F

-- Destructor
out : ∀ (F : Functor) → μ F → ⟦ F ⟧F (μ F)

-- Catamorphism with termination proof
cata : ∀ {F} {A : Set} → (⟦ F ⟧F A → A) → μ F → A

-- Functor laws
fmap-id : ∀ F {X} (x : ⟦ F ⟧F X) → fmap F id x ≡ x
fmap-comp : ∀ F f g x → fmap F (g ∘ f) x ≡ fmap F g (fmap F f x)

-- Fixed point isomorphism
fold-unfold : ∀ F x → out F ⟨ x ⟩ ≡ x
unfold-fold : ∀ F x → ⟨ out F x ⟩ ≡ x

-- Induction principle
ind : ∀ {F} (P : μ F → Set) → ... → (x : μ F) → P x
```

### Rationale

| Criterion | Polynomial Functors | Other Options |
|-----------|:------------------:|:-------------:|
| Implementation effort | **~340 lines** | 200-500+ lines |
| Ongoing proof burden | **Lowest** | Medium-High |
| Once compatibility | **Excellent** | Good |
| User syntax change | **None** | None |
| QTT/Linearity fit | **Best** | Varies |
| CCC alignment | **Perfect** | Good |

**Why Polynomial Functors win:**

1. **Zero user impact**: Surface syntax unchanged (`Fix (Unit + X)` still works)
2. **Lowest proof burden**: One-time setup, then automatic induction principles
3. **Best QTT fit**: No functions in recursive positions means clean linearity
4. **CCC alignment**: Polynomial functors = free cartesian category on one generator
5. **Sufficient expressiveness**: Covers all Once recursive types (Nat, List, Tree)

**What it cannot express** (and Once doesn't need):
- `Fix (X -> A)` - X in negative position (rarely needed)
- Church/Scott encodings - higher-order (native Fix is better)
- PHOAS - negative occurrence (use de Bruijn)

### Mathematical Foundation

Polynomial functors form the **free cartesian category** on one generator. This aligns perfectly with Once's CCC foundation. Initial algebras of polynomial functors always exist in Set, giving us proper inductive types with sound semantics.

### Integration Status

The SPF module is **standalone** and type-checks successfully. Full integration into `Type.agda` and `Semantics.agda` is deferred as future work because:

1. Would require updating many existing proofs
2. SPF can be used directly for new verified programs
3. Existing proofs remain valid for their current scope

### Future Work

To fully integrate SPF:
1. Change `Fix : Type → Type` to `Fix : Functor → Type` in `Type.agda`
2. Change `⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧` to `⟦ Fix F ⟧ = μ F` in `Semantics.agda`
3. Update dependent proofs in `Laws.agda`, `Correct.agda`, etc.

### Consequences

- S1 semantic gap is **addressable** (foundation now exists)
- New verified programs can use SPF directly
- Existing formalization unchanged (no breaking changes)
- Clear path to full integration when needed

### See Also

- `docs/formal/fix-semantics-options.md` - Detailed comparison of all options
- `formal/Once/SPF.agda` - Implementation
- `docs/formal/what-is-proven.md` - S1 limitation documentation

---

## D038: Multiple Generator Implementation Profiles

**Date**: 2025-12-15
**Status**: Accepted

### Context

The formal verification analysis (see `docs/formal/proof-analysis.md`) revealed that:

1. **apply is fundamentally unprovable** with the current isolated-program execution model due to code addressing issues (thunk code lives in curry's program space, not apply's)

2. **Some generators are difficult to prove** due to program concatenation reasoning (compose, pair, case)

3. **Different use cases have different priorities**: cryptographic code needs constant-time execution, safety-critical systems need formal verification, general applications need performance

4. **Branchless implementations** offer both easier proofs (no control flow reasoning) and side-channel resistance (constant-time)

### Decision

Support **multiple implementation profiles** for generators, allowing the same Once program to be compiled with different code generation strategies based on the target use case.

### Implementation Profiles

| Profile | Primary Goal | Trade-offs |
|---------|--------------|------------|
| **Crypto** | Constant-time execution | Slower (2x+ for case due to speculation) |
| **Verified** | Provable correctness | May be slower, uses defunctionalization |
| **Fast** | Maximum performance | Complex proofs or postulates |
| **Small** | Minimal code size | May be slower |
| **Debug** | Observable execution | Slowest, includes tracing |

### Per-Generator Implementation Matrix

| Generator | Crypto | Verified | Fast | Small |
|-----------|--------|----------|------|-------|
| id | nop | nop | nop | nop |
| compose | f;g | f;nop;g | f;g | f;g |
| fst | load | load | load | load |
| snd | load | load | load | load |
| pair | stack-only | stack-only | register | stack-only |
| inl | standard | standard | standard | standard |
| inr | standard | standard | standard | standard |
| case | **branchless** | stack-only | branching | branching |
| terminal | mov | mov | mov | mov |
| initial | trap | trap | trap | trap |
| curry | **defunc** | defunc | thunk+jump | defunc |
| apply | **branchless-defunc** | defunc-case | indirect-call | defunc-case |
| fold | nop | nop | nop | nop |
| unfold | nop | nop | nop | nop |
| arr | nop | nop | nop | nop |

### Rationale

**Why multiple implementations:**

1. **No single optimal choice**: Constant-time code is slower but essential for crypto. Fast code has branches that complicate proofs. The right choice depends on the application.

2. **Proof strategy**: Simpler implementations (stack-only, branchless) can be proven correct, then equivalence to faster implementations can be established.

3. **apply becomes provable**: With defunctionalization, apply becomes a case dispatch rather than an indirect jump, making it fully provable for the Verified profile.

4. **Side-channel resistance**: The Crypto profile eliminates data-dependent branches, providing constant-time execution for cryptographic operations.

**Profile selection algorithm:**
```
select_profile(program):
  if program.handles_secrets:
    return Crypto
  elif program.requires_certification:
    return Verified
  elif program.memory_constrained:
    return Small
  else:
    return Fast
```

### Branchless Execution (Crypto Profile)

The Crypto profile uses branchless code to prevent timing side channels:

**Branchless case:**
```asm
; Execute BOTH branches, select result with cmov/csel
ldr     x9, [x0]            ; tag
ldr     x0, [x0, #8]        ; value
mov     x20, x0             ; save value
; --- compile f ---
mov     x21, x0             ; save f result
mov     x0, x20             ; restore value
; --- compile g ---
cmp     x9, #0
csel    x0, x21, x0, eq     ; branchless select
```

**Branchless apply (via defunctionalization):**
- curry stores `(env, tag)` instead of `(env, code_ptr)`
- apply executes ALL possible functions and selects result based on tag
- No indirect jumps, constant instruction count

### Cycle Cost Comparison

| Profile | case cycles | apply cycles | Predictable? |
|---------|-------------|--------------|--------------|
| Fast | 8 + \|one branch\| | 25-40 (indirect) | No |
| Crypto | 8 + \|both branches\| + 3 | 10 + \|all funcs\| + 3n | **Yes** |
| Verified | 10 + \|one branch\| | depends on defunc | Partially |

### Proof Strategy by Profile

| Profile | Proof Approach |
|---------|----------------|
| Crypto | Prove constant-time property + correctness |
| Verified | Full correctness proof via stack-machine equivalence |
| Fast | Equivalence to Verified, or accept postulates |
| Small | Equivalence to Verified |

### Future CLI Integration

```bash
# Default (Fast)
once build --exe hello.once -o hello

# Crypto profile for constant-time
once build --exe --profile crypto hello.once -o hello

# Verified profile for formally proven code
once build --exe --profile verified hello.once -o hello

# Mix profiles (future)
once build --exe --crypto-functions "deriveKey,encrypt" hello.once -o hello
```

### Consequences

- Same Once source can compile to different implementations
- Crypto-critical code gets side-channel resistance
- Safety-critical code gets formal verification
- General code gets maximum performance
- Path to proving apply via defunctionalization
- Branchless implementations simplify proofs (no control flow)

### See Also

- `docs/formal/proof-analysis.md` - Full analysis of proof status and branchless implementations
- D022: Agda for Formal Verification
- D032: Arrow-Based Effect System

---

## D039: Lambda Elaboration and Named Parameters

**Date**: 2025-12-23
**Status**: Accepted

### Context

Once programs often need to express operations that take arguments and use them in complex ways. The categorical style requires verbose point-free composition:

```once
-- Without lambdas (verbose point-free)
findUntyped = compose ... fst ... snd ...

-- With lambdas (readable)
findUntyped bootinfo sizeBits idx = ...
```

### Decision

Add **lambda elaboration** as syntactic sugar for `curry`, plus **named function parameters** as parser sugar for nested lambdas.

**Lambda elaboration** (`\x -> e` → `Curry x e'`):
- The bound variable `x` becomes a `LocalVar` in the body
- The `Curry Name IR` constructor carries the variable name for code generation
- The C backend handles `LocalVar` inside `Curry` appropriately

**Named parameters** (`f x y = e` → `f = \x -> \y -> e`):
- Pure parser-level desugaring via `foldr ELam e params`
- No IR changes needed beyond lambda support

### Implementation

**Parser** (`Parser.hs`):
```haskell
funDef = do
  name <- lowerIdent
  params <- many lowerIdent  -- zero or more parameters
  alloc <- optional allocAnnotation
  void $ symbol "="
  e <- parseExpr
  pure $ FunDef name alloc (foldr ELam e params)
```

**IR** (`IR.hs`):
```haskell
| Curry Name IR  -- curry f : A -> (B -> C) (with lambda var name for codegen)
```

**Elaboration** (`Elaborate.hs`):
```haskell
ELam x body -> do
  body' <- elaborateExpr' (Set.insert x locals) body
  Right $ Curry x body'
```

### Rationale

1. **No new expressive power**: `curry` already exists as a generator; lambdas are purely syntactic
2. **Categorical soundness**: The translation is the standard categorical encoding of lambda calculus
3. **Readability**: Complex operations become much more readable
4. **Proofs preserved**: The IR remains morphism-based; elaborator handles translation

### Consequences

- Users can write `f x y = e` (familiar style)
- Users can write `\x -> e` (explicit lambdas)
- Point-free style still works: `f = g . h`
- Case expressions work: `case x of { Left a -> e1; Right b -> e2 }`
- C backend generates appropriate code for `Curry` with `LocalVar`

### See Also

- D029: Let Bindings with Desugaring (similar approach)
- D032: Arrow-Based Effect System

---

## D040: Orthogonal Arithmetic Compiler (Separate ArithIR)

**Date**: 2025-12-26
**Status**: Accepted

### Context

OCP-0001 proposes an arithmetic compiler for efficient numeric computation. The goal is baremetal arithmetic performance with control flow using natural transformations.

Two approaches were considered:
1. **Embedded in IR**: Add arithmetic (Add, Mul, etc.) as generators
2. **Separate ArithIR**: Two parallel IRs with natural transformation interface

### Decision

Use **Separate ArithIR** — two orthogonal IRs with a natural transformation boundary.

```
Source → Parse → Elaborate → IR
                              ↓
                    ┌─────────┴─────────┐
                    ↓                   ↓
            Arithmetic IR         Control Flow IR
            (expressions)         (generators)
                    ↓                   ↓
            Register alloc        Current codegen
                    ↓                   ↓
                    └─────────┬─────────┘
                              ↓
                          Assembly
```

### Rationale

**1. Categorical purity**

The 12 generators capture CCC structure (products, coproducts, exponentials). Arithmetic is operations on base types — conceptually orthogonal to structural operations.

**2. Performance**

Embedded approach forces stack allocation for intermediate values through `pair`. For `a*b + c*d`:
- **Embedded**: ~40+ instructions with memory traffic (pair allocates 16 bytes per intermediate, compose moves values through stack)
- **Separate ArithIR**: ~5 register-only instructions (direct register allocation across the expression)

Example with embedded generators:
```
a + b  →  compose add (pair (prim "a") (prim "b"))
```
This generates: stack allocation for pair, two stores, load pair ptr, load both elements, add.

Example with separate ArithIR:
```asm
mov  eax, [a]
add  eax, [b]    ; 2 instructions, register-only
```

**3. Linearity (QTT)**

Arithmetic linearity reduces to counting variable occurrences. Separate ArithIR uses context splitting:

```agda
data ArithIR : Ctx → NumType → Set where
  Add : ArithIR Γ τ → ArithIR Δ τ → ArithIR (Γ ⊕ Δ) τ
```

The context split (Γ ⊕ Δ) enforces linearity: a variable can only appear in one subexpression unless it's ω. This is cleaner than tracking through generator composition.

**4. Proof modularity**

Arithmetic has no closures, no branches, no stack frames. Isolated proofs are simpler:
- Arithmetic correctness: standard expression compilation (well-understood)
- Generator correctness: existing proofs unchanged
- Boundary: simple composition proof

MutualIR.agda (3152 lines) stays focused on generator mutual recursion.

**5. Natural transformation interface**

The boundary between control flow and arithmetic IS a natural transformation — aligns perfectly with project philosophy. The `arith` constructor embeds arithmetic expressions in the generator IR:

```agda
arith : ∀ {Γ τ} → ArithIR Γ τ → IR (Env Γ) (NumToType τ)
```

### Scope

**Included:**
- Integer types: i8, i16, i32, i64 (full range)
- Float types: f32, f64
- Operations: Add, Sub, Mul, Div, Mod, Neg, comparisons (Lt, Eq)
- Register allocation for expressions
- Formal correctness proofs in Agda
- x86-64 backend (GPRs for integers, SSE/XMM for floats)

**Deferred:**
- SIMD/vectorization
- Complex optimizations (CSE, strength reduction)
- AArch64/RISC-V backends (follow same pattern)

### Trade-offs

| Aspect | Pro | Con |
|--------|-----|-----|
| Performance | Baremetal for arithmetic | - |
| Proof complexity | Simpler isolated proofs | Boundary proof required |
| Code organization | Clear separation of concerns | Two IRs to maintain |
| Linearity tracking | Clean context splitting | Must define arithmetic context |
| Categorical structure | Generators stay pure CCC | Arithmetic outside CCC |

### Consequences

- New `formal/Once/Arith/` directory with Type, IR, Semantics, Backend
- `arith` constructor added to `IR.agda`
- Register allocation within arithmetic expressions
- Boundary proof: `eval (arith e ∘ f) x ≡ eval-arith e (eval f x)`
- Haskell compiler gains ArithIR recognition and codegen

### See Also

- OCP-0001: Orthogonal Arithmetic Compiler (proposal)
- D022: Agda for Formal Verification
- D038: Multiple Generator Implementation Profiles

---

## D041: Abstract Memory Regions Model

**Date**: 2026-01-09
**Status**: Accepted

### Context

The x86 backend proofs use concrete stack addresses (`stackBase = 0x7FFF0000`) and specific postulates like `heap-stack-disjoint`. While working on eliminating postulates in the apply proof, we encountered fundamental issues:

1. **StackInvariant requires ordering**: `rsp ≤ r15` when r15 holds a heap address
2. **code-ptr is not a heap address**: During apply, r15 holds a code pointer (low program address ~0-1MB) while rsp is high (~2GB), so `rsp ≤ code-ptr` is FALSE
3. **Concrete addresses are false precision**: We already postulate "enough stack space" - the concrete stackBase value doesn't add real guarantees

The discussion revealed that `heap-stack-disjoint` is justified by the memory layout assumption that regions don't overlap. The same reasoning applies to code addresses, but code-stack disjointness shouldn't need a separate postulate - it follows from the same memory model.

### Decision

Adopt an **abstract memory regions model** where:

1. Memory is partitioned into **three disjoint regions**: Stack, Heap, Code
2. Stack operations use **tight allocation** (delta equals size, no waste)
3. Stack is **LIFO** (push/pop are inverses - exact recovery)
4. Concrete addresses (like `stackBase = 0x7FFF0000`) are replaced with abstract region membership

### The Pure Stack Model

```agda
record PureStackModel : Set₁ where
  field
    -- Stack pointer type (abstract, not concrete ℕ)
    SP : Set

    -- Allocation advances SP by exactly the requested size (tight, no waste)
    alloc : SP → ℕ → SP
    alloc-tight : ∀ sp n → distance sp (alloc sp n) ≡ n

    -- Deallocation retreats SP by exactly the same amount (LIFO, exact recovery)
    dealloc : SP → ℕ → SP
    dealloc-inverse : ∀ sp n → dealloc (alloc sp n) n ≡ sp

    -- Convert SP + offset to address
    slot-addr : SP → ℕ → Addr

    -- Different SPs give different addresses (freshness)
    sp-distinct : sp₁ ≢ sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k

    -- Different offsets give different addresses
    offset-distinct : k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂

    -- All stack addresses are in stack region
    in-region : ∀ sp k → StackRegion (slot-addr sp k)
```

### Region Disjointness (Single Postulate)

```agda
-- Memory is partitioned into regions
data Region : Set where stack heap code : Region

-- Single postulate: regions are pairwise disjoint
postulate
  regions-disjoint : ∀ {r₁ r₂} → r₁ ≢ r₂ →
    ∀ a₁ a₂ → region-of a₁ ≡ r₁ → region-of a₂ ≡ r₂ → a₁ ≢ a₂

-- Region membership (definitional, not postulated)
stack-addr-region : ∀ sp k → region-of (slot-addr sp k) ≡ stack
heap-addr-region : ∀ {A} (x : ⟦ A ⟧) k → region-of (encode x + k) ≡ heap
code-addr-region : ∀ offset → offset < prog-length → region-of offset ≡ code
```

### Rationale

**Why abstract over concrete:**

| Concrete Model | Abstract Model |
|----------------|----------------|
| `rsp = 0x7FFF0000` | `rsp ∈ StackRegion` |
| `rsp > 16` | `HasStackSpace sp n` |
| `heap-stack-disjoint` (postulate) | `regions-disjoint` (single postulate) |
| `code-stack-disjoint` (needs new postulate) | Follows from `regions-disjoint` |
| Direction matters (grows down) | Direction abstracted away |

**Why "tight allocation" matters:**

Pure freshness ("allocations don't overlap") allows wasteful implementations:
```
Frame 1: [addr 0-7]
Frame 2: [addr 1000-1007]  -- wasted 992 bytes!
```

Tight allocation (`delta ≡ size`) ensures no waste - the stack pointer moves exactly by the frame size. Combined with LIFO (`dealloc ∘ alloc = id`), this captures the essential stack discipline without assuming direction.

**Why not assume "grows down":**

- Not all architectures grow down (PA-RISC grew up)
- The proofs don't actually need direction
- "Tight + LIFO" captures the essential properties
- More general = more reusable proofs

**Generalizing "enough stack space":**

We already postulate sufficient stack space. The abstract model generalizes this:
- Stack: "enough space" = allocations succeed and are tight
- Heap: "enough space" = encode allocations succeed and are fresh
- Code: fixed at compile time, no runtime allocation

This is the same assumption applied uniformly across all regions.

### What Changes in Proofs

**StackInvariant simplifies:**
```agda
-- Old: track rsp ≤ r15 ordering (fails when r15 = code-ptr)
-- New: just track which region r15 points to

data R15Status (s : State) : Set where
  r15-zero   : readReg (regs s) r15 ≡ 0 → R15Status s
  r15-heap   : HeapRegion (readReg (regs s) r15) → R15Status s
  r15-code   : CodeRegion (readReg (regs s) r15) → R15Status s

-- Stack writes are safe regardless of which case!
-- Because regions-disjoint covers all cases
```

**Memory preservation becomes trivial:**
```agda
-- To prove: stack write at sp doesn't affect heap addr h
mem-preserved : StackRegion sp → HeapRegion h →
                writeMem mem sp v → readMem (result) h ≡ readMem mem h

-- Proof: regions-disjoint gives sp ≢ h, so write doesn't affect read. QED.
```

**Concrete bounds disappear:**
- No more `rsp > 16`
- No more `stackBase = 0x7FFF0000`
- Just `HasStackSpace sp n` for operations needing n bytes

### Consequences

- **Single region disjointness postulate** replaces multiple specific postulates
- **code-stack disjointness** falls out for free (no new postulate)
- **StackInvariant** simplifies to region membership tracking
- **Proofs don't assume stack direction** - more general and reusable
- **Tight allocation + LIFO** captures stack discipline abstractly
- **Requires refactoring** existing concrete `rsp` usage (future work)

### Migration Path

1. Define abstract `PureStackModel` in new module
2. Define `regions-disjoint` postulate
3. Refactor `StackInvariant` to use region membership
4. Update memory preservation proofs to use region disjointness
5. Remove concrete `stackBase`, `rsp > 16` bounds
6. Remove `heap-stack-disjoint` (subsumed by `regions-disjoint`)

### See Also

- D022: Agda for Formal Verification
- D038: Multiple Generator Implementation Profiles
- `formal/Once/Backend/X86/Correct/StackInvariant.agda` - Current concrete model
- `formal/Once/Postulates.agda` - Current `heap-stack-disjoint` postulate

---

## D042: Case Generator vs Destruct Syntax

**Date**: 2026-01-22
**Status**: Accepted

### Context

Per D001, `case` is one of the 12 categorical generators - the coproduct eliminator (copairing). However, the parser had overloaded `case` to mean two different things:

1. **Generator**: The categorical operation `(A → C) → (B → C) → (A + B → C)`
2. **Syntax**: Pattern matching `case e of { Left x -> e1; Right y -> e2 }`

This conflation caused problems:
- `mirror = case inr inl` didn't parse (case expected pattern-matching syntax)
- Inconsistent with D027 (generators should be implicitly available as reserved words)
- Conflates a categorical operation with binding/naming concerns

### Decision

**Separate the concerns:**

1. **`case` is a pure generator** - coproduct eliminator/copairing
   - Type: `(A → C) → (B → C) → (A + B → C)`
   - Available as reserved word per D001/D027
   - Usage: `case f g` applies f to Left, g to Right

2. **`destruct` is the pattern-matching syntax** - sum elimination with variable binding
   - Syntax: `destruct e | x -> e1 | y -> e2`
   - First branch handles `inl` (Left), second handles `inr` (Right)
   - Positional - no `Left`/`Right` keywords needed

### Syntax Design (Bar-separated patterns)

```once
destruct e
  | x -> e1
  | y -> e2
```

The first branch handles `inl` (Left), second handles `inr` (Right).

**Examples:**

```once
-- Bool (if/then/else is just destruct on Unit + Unit)
destruct b
  | _ -> trueCase
  | _ -> falseCase

-- Maybe A = Unit + A
destruct m
  | _ -> default
  | x -> f x

-- Mirror: A + B -> B + A
mirror x = destruct x
  | a -> inr a
  | b -> inl b

-- Nested destruction
assocR x = destruct x
  | ab -> destruct ab
      | a -> inl a
      | b -> inr (inl b)
  | c -> inr (inr c)
```

### Rationale

**Why not just `case`:**
- `case` as a generator is `(A → C) → (B → C) → (A + B → C)` - takes functions
- Pattern matching with binding is different - introduces names
- The generator `case` composes; the syntax `destruct` binds

**Why not `if-then-else`:**
- `if-then-else` is just `destruct` on `Bool = Unit + Unit`
- One universal syntax handles all sum types
- No special case for Bool needed

**Why bar-separated syntax:**
- Clean visual structure for pattern branches
- Good for programmer overview of code
- Similar to Haskell's guards/case arms
- No verbose braces or keywords

**Why positional (no Left/Right keywords):**
- Consistent with `inl`/`inr` (first/second injection)
- Less visual noise
- Two branches always - sum types are binary

### Consequences

- `case` works as a generator: `mirror = case inr inl`
- Pattern matching uses `destruct` with bar-separated patterns
- No `if-then-else` needed - use `destruct` on Bool
- Parser changes: rename `case` syntax to `destruct`
- All examples using old `case ... of { ... }` syntax need migration

### See Also

- D001: Generators as Reserved Words
- D027: No Implicit Imports (generators are implicitly available)

---

## D043: Applied-NT Desugaring via Universal Property (Parser) vs Classifier Extension (Typechecker)

**Date**: 2026-04-21
**Status**: Accepted for pair/compose/curry/apply; **flagged for migration after C.5-arr lands classifier machinery** (see Re-evaluation below)

### Context

Plan 0.6 Phase C needed to make multi-arg categorical NTs (`pair`,
`compose`, `curry`, `apply`) typecheck at call sites in point-free
user code — both in ground-typed definitions like
`mkSwap : Int*Int → Int*Int; mkSwap = pair snd fst` and in
polymorphic user defs like `swap : a*b → b*a; swap = pair snd fst`
composed with ground-type use sites.

Two implementation routes were considered, both producing equivalent
typed IR:

1. **Classifier extension (typechecker).** Add per-NT entries to
   `AppHeadView` / `classifyAppHead` in
   `Once.TypeCheck.Elaborate`, plus a `t-pair-app` / `t-compose-app`
   / … judgment rule per NT in `Judgment.agda`, plus Soundness +
   Completeness + ErrorProofs cases. Emits the direct IR
   constructor (`IR.pair`, `IR.compose`, …) at elaboration time.

2. **Surface-level desugaring (parser).** Rewrite applied NT forms
   at the RawExpr level to explicit lambda+pair+app using the
   universal property of each morphism:
   - `pair f g`    → `λx → (f x, g x)`
   - `compose f g` → `λx → f (g x)`
   - `curry f`     → `λx → λy → f (x, y)`
   - `apply p`     → `let $p = p in fst $p (snd $p)`
   The desugared form is handled by existing RLam + RPair + RApp
   typechecker machinery — no new rules, no new proofs.

### Decision

**Surface-level desugaring** for all NTs whose universal property
*has* a lambda form. `arr : (A ⇒ B) ⇒ Eff A B` is excluded because
`Eff` is a distinct IR type constructor with no lambda reduction;
it will use the classifier route when added (plan 0.6 Phase C.5-arr).

### Rationale

- **Proof-surface cost.** Classifier extension = 5 NTs × per-NT
  judgment rule + Soundness + Completeness + ErrorProofs +
  classifier-view updates = substantial multi-file proof work per
  addition. Desugaring = one pattern in `expandBuiltins` per NT.
  Proof surface doesn't grow with each NT added.
- **Semantic equivalence by construction.** `specPair`'s lambda body
  in the elaborator is *literally* the desugaring target. Both
  routes produce the same Surface IR term after elaboration, so the
  desugaring is not an approximation — it's another path to the
  same IR.
- **Beta-reduction pass (`betaReduceApps`) recovers structural
  shape** when nested desugarings produce `RApp (RLam …) _` in
  inference position (e.g. `compose fst (pair h k)`). Without this,
  the applied lambda can't be inferred.
- **Fresh names (`$pair_x`, `$compose_x`, …).** `$` is illegal in
  user identifiers (see `Once.Parser.Lexer.isIdentStart` /
  `isIdentContinue`), so capture with user variables is impossible
  by construction.

### Consequences (future costs)

- **Error messages reference desugared names.** A type error in
  `pair f g` may surface a reference to `$pair_x`, a variable the
  user never wrote. Cost: diagnostic quality degrades for these
  builtins. Not yet mitigated.
- **Optimizer-dependent IR equivalence.** The desugared form is
  lambda+pair+app. Runtime equivalence to `IR.pair` relies on the
  optimizer's beta/eta laws to fuse the lambda back. If optimization
  is disabled or weakened (e.g. `-O0`), output IR is larger. The
  classifier route would emit `IR.pair` directly.
- **No user-source path to raw `IR.pair`.** Any future proof
  targeting the `IR.pair` constructor is, transitively, a proof
  about "lambda-fused-to-`IR.pair`." We've exchanged per-builtin
  soundness proofs for one optimizer-correctness obligation.
- **NT identity is erased.** After desugaring, `pair f g` is
  indistinguishable from an arbitrary user lambda of the same
  shape. Any future feature that keys off NT identity (specialized
  codegen, rewrite rules, usage analysis keyed on NT name) loses
  that hook.
- **`arr` still needs the classifier.** Once classifier machinery
  exists for `arr`, the argument "we already have it, just extend
  it" becomes available. Stance: keep desugaring for lambda-form
  NTs; classifier only for non-lambda-form NTs.

### Consequences (future savings)

- **New lambda-form NTs cost one pattern** in `expandBuiltins`.
  No proof work.
- **Uniform pipeline.** User polymorphic defs (plan 0.6 Phase C.0
  + C.1) and NT builtins both flow through the same
  inline → desugar → betaReduce → typecheck path. No bifurcation.
- **One optimizer law generalises.** A general proof "lambda+pair+app
  fuses to `IR.pair`" covers every occurrence. The classifier route
  requires per-builtin soundness independently.

### Re-evaluation (2026-04-21, same day)

A subsequent review flagged that the "zero proof-side delta" framing
was misleading:

1. **The classifier machinery has to be built anyway.** `arr` cannot
   be lambda-desugared (`Eff` is a distinct IR type constructor with
   no lambda reduction), so plan 0.6 Phase C.5-arr must land
   `AppHeadView` / `classifyAppHead` / judgment rule / Soundness /
   Completeness extensions for at least one NT. Once that machinery
   exists, the marginal proof cost of extending it to
   pair/compose/curry/apply is small — template-following, not
   novel work.

2. **Error-message quality is a permanent user-facing cost.** Every
   compile error in `pair f g` surfaces `$pair_x` — a variable the
   user never wrote. This is paid at every failing compile,
   indefinitely, not as a one-time proof setup. A mitigation would
   require reverse-mapping desugared names to user-level
   expressions at diagnostic time, which is itself non-trivial.

3. **IR-reachability and NT-identity costs** (see Consequences
   above) are permanent. The classifier route preserves NT names in
   IR and diagnostics.

**Honest reassessment.** The savings realised in C.2-C.5 came from
avoiding classifier machinery setup *in this session*, not from
durable lifecycle savings. Once C.5-arr pays the setup cost, the
per-NT marginal cost of classifier coverage is comparable to the
desugaring's per-NT cost — and the classifier route wins on
diagnostics, on avoiding the optimizer dependency, and on preserving
NT identity for future features.

**Forward plan.** Land C.5-arr with full classifier machinery. After
that machinery exists, migrate pair/compose/curry/apply off the
desugaring path onto the classifier. At that point this decision is
superseded by a D044 recording the migration. D043 remains in the
log as the record of the intermediate step and the lesson about
front-loaded vs lifecycle cost framing.

### Migration attempt (2026-04-21, same day): blocked on bare-builtin check-mode

Attempted the migration of pair/compose/curry/apply off the desugaring
path. C.5-arr worked cleanly because `arr`'s typical argument is a
user-defined function. The multi-arg NTs hit a different blocker:

Canonical point-free usage `swap = pair snd fst` needs the classifier
to check `snd` at expected function type `(A * B) ⇒[Many] B`. But
**bare polymorphic builtins in check mode were explicitly removed in
plan 0.3 G2** — a deliberate earlier decision that `id`/`fst`/`snd`/...
must appear applied (as RApp heads) or via imports, never as bare
RVars. The removal was load-bearing for proof simplification.

The desugaring route sidesteps this because `pair snd fst ↦ λx → (snd
x, fst x)` wraps `snd`/`fst` in RApps inside the lambda body, where
the classifier's infer-mode path handles them.

Three paths forward, each with real cost:

1. **Re-introduce bare-builtin check-mode clauses.** Reverses the G2
   decision. Requires updating the removed clauses' proofs across
   Elaborate / Judgment / Soundness / Completeness / ErrorProofs.
   Substantial proof work re-done.

2. **Eta-expand inside `checkPair`/`checkCompose`/`checkCurry`.** When
   an arg is a bare polymorphic builtin RVar, wrap it in `RLam x (RApp
   builtin (RVar x))` before recursing. Works around the gap locally.
   Partial duplication of desugaring logic inside classifier helpers
   — loses the "clean classifier vs desugaring" separation.

3. **Keep the hybrid.** Classifier for `arr`; desugaring for
   pair/compose/curry/apply. Accepts permanently worse diagnostics
   for the lambda-reducible NTs in exchange for not taking on (1)
   or (2). This is the **currently-landed state** (commits
   `092d70d6`/`b32f8d0e`/`272e2fab`/`e7b984e5`).

**Current status: parked at hybrid.** The full migration is deferred
until either path (1) or (2) is specifically chosen and scheduled.
D043 stays the governing decision for now.

### Deeper blocker (2026-04-21, second migration attempt): Ψ-mismatch

A second, more determined migration attempt surfaced the actual
architectural cost. Re-introducing specialised bare-builtin
check-mode clauses — even with a clean "fall through on guard
failure" design — breaks completeness via a **usage (Ψ) mismatch**:

- Specialised clause for `RVar "id"` at `A ⇒[Many] A` emits
  `specId A` with `Ψ = zeroUsage` (the specialised term is a closed
  λ-abstraction, used zero times in the enclosing context).
- Judgment derivation via `t-embed (t-var-local {x="id"} …)`
  produces a non-zero Ψ reflecting the variable's single-use.

The existing completeness helper `checkElab-fallback-RVar`
(`Completeness.agda:490`) asserts that the inferred Ψ is *preserved*
through to the check-mode result. The specialised path returns a
different Ψ, so the lemma as stated fails.

Two real fixes, both substantial:

1. **Per-builtin check-mode judgment rules.** Add 12 new rules
   (`t-id-check`, `t-fst-check`, …), each with conclusion
   `ctx ⊢ᶜ RVar x ∶ T ⨾ zeroUsage`. Completeness then splits:
   specialised Ψ matches the new rule; lookup Ψ matches the existing
   `t-embed (t-var-local …)`. ≈12 new judgment rules + ≈24 new
   soundness / completeness cases + ErrorProofs paths. Scope: 300–500
   lines of proof. Principled.

2. **Parser reservation + shadow-impossibility lemma.** Enforce D001
   at parse time so reserved names can never appear in local/import
   scope; prove the shadow-impossibility lemma globally; use it to
   absurd-out the non-zero-Ψ case in completeness. Medium proof work
   + parser change that ripples into existing fixtures / tests.
   Less repetitive than (1) but coupling the proof to a parser
   invariant is new territory.

Neither path is a "small" lift. The hybrid remains in place.

**Takeaway for future planning.** The proof architecture carries more
weight than surface-level tooling in this codebase. When considering
reversing a decision like G2, cost isn't just "re-add the clauses" —
it's "re-align the Ψ-invariant across the elaborator / judgment /
completeness triangle." D043's desugaring route avoided this cost
entirely at the price of diagnostic quality. That trade, once made
visible, turns out to be genuinely load-bearing.

### See Also

- D001: Generators as Reserved Words
- D007: Structural Type Matching for Signatures (frames why
  user-polymorphic schemas do not need a separate specialisation
  mechanism — call-site specialisation for user NTs is subsumed by
  builtin specialisation after inlining)
- D021: Canonical.once (morphisms from universal properties —
  D043's desugaring IS the universal property in surface syntax)
- Plan 0.6.1: Phase C Design (drives this decision)
- **D044** (below) — partial supersession: reversal of G2 with
  disjoint judgment rules

---

## D044: G2 Reversed — Classifier Route via Disjoint Judgment Rules

**Date**: 2026-04-21
**Status**: Accepted

### Context

D043's re-evaluation identified two costs of the desugaring approach:
(1) diagnostics — `pair f g` errors surface `$pair_x`; (2) optimizer
dependency — runtime equivalence to `IR.pair` requires the β/η
laws to fuse. The forward plan committed to reversing G2 when the
classifier machinery landed for `arr`.

An initial attempt at simple G2 reversal (re-introducing specialised
bare-builtin check-mode clauses that fell through to lookup on guard
failure) surfaced a **Ψ-mismatch**: specialised clauses emit
`zeroUsage`, while lookup-based derivations via `t-embed (t-var-local
…)` produce non-zero Ψ. The existing `checkElab-fallback-RVar`
completeness lemma asserts Ψ-preservation, which the specialised
path broke.

### Decision

Resolve via **disjoint per-builtin check-mode judgment rules** with
lookup-failure premises:

```
t-id-check : ∀ {ctx T}
           → lookupLocal ctx "id" ≡ nothing
           → lookupImport (NamedCtx.imports ctx) "id" ≡ nothing
           → ctx ⊢ᶜ RVar "id" ∶ (T ⇒[Many] T) ⨾ zeroUsage
```

The lookup-failure premises make this rule **disjoint by
construction** from `t-embed (t-var-local/import …)` — each
derivation uniquely identifies which elab path fires, so the
Ψ-mismatch evaporates. No global shadow-impossibility lemma
required.

For applied multi-arg NTs (`pair`, `compose`, `curry`, `apply`),
disjointness with `t-embed (t-app …)` comes for free from the
existing `classifyAppHead f ≡ nothing` premise on `t-app` — extending
`classifyAppHead` to return `just pba-*-applied` for these shapes
makes `t-app` inapplicable.

### Architecture (landed commits)

| Component | Commit |
|---|---|
| POC-1: bare `id` (validate pattern) | `bc1171f6` |
| POC-2: applied `pair f g` (validate multi-arg + sub-derivation) | `77e24986` |
| Bare fst/snd/terminal/initial/inl/inr/arr (`BareBuiltinClass` view) | `32b13467` |
| Applied compose/curry/apply classifiers + judgment rules | `cdbfcdf5` |

Key components:

- **`BareBuiltinClass` view** (`Once.TypeCheck.Elaborate`): dispatches
  `checkElab-RVar` by indexed view, scales cleanly to 8 bare
  builtins without nested `with` explosion. Same idiom as
  `classifyAppHeadView`.
- **Per-builtin judgment rules** (`t-X-check` in
  `Once.TypeCheck.Judgment`): 8 bare + 4 applied = 12 new rules.
  All carry disjointness premises (lookup-failure for bare, or
  classifier-derived for applied).
- **Per-builtin completeness helpers**
  (`checkElab-fallback-RVar-X` / `checkElab-fallback-RApp-X` in
  `Elaborate.agda`): thread lookup-failure or sub-derivation
  equations through `rewrite` to close `check-complete (t-X-check
  …)`. Uniform proof structure; ~10 lines each.

### Consequences

**Gains (user-visible):**

- Errors reference NT names directly (e.g. "pair: expected type
  mismatch") instead of `$pair_x`. Diagnostic quality improves.
- Direct `IR.pair` / `IR.compose` emission via `spec*`; no optimizer
  β/η dependency for runtime equivalence.
- Bare polymorphic builtins in check mode at their canonical types
  now typecheck (e.g. `x : A → A; x = id` is legal).

**Proof-side cost (realized):**

- 12 judgment rules, 12 completeness helpers, ~1200 LoC added
  (including mechanical repetition across builtins). In line with
  the 300–500 LoC estimate's upper end. No soundness cases required
  — following the architectural pattern of `ahv-inl`/`ahv-inr`/etc.
  where elab coverage doesn't force per-builtin Soundness theorems.

**Partial migration:**

The classifier is the primary path but the desugarings in
`Once.Parser.Inline.expandBuiltins` remain as a parallel fallback
for complex nested cases (`compose f (pair g h)` where the
classifier's per-NT infer-mode fails because `pair g h` has no
inferable form). Both paths produce equivalent Surface IR; the
desugaring fires first in the pipeline. Full desugaring removal
awaits either a `pair`-infer-mode extension (requires inferable
bare-builtin args) or a nested-RApp classifier extension. Scoped
as future work.

### See Also

- **D043** — original decision, now superseded in part by D044
- **G2 decision** (plan 0.3, 2026-04-17) — the specialised
  bare-builtin check-mode removal that D044 reverses
- Plan 0.6.1 Phase C.7 — migration implementation track
- **D045** (below) — fully supersedes D043's desugaring-fallback
  story via typecheck-time polymorphic schema instantiation

---

## D045: Polymorphic Schema Instantiation, Supersedes D043/D044's Fallback

**Date**: 2026-04-21
**Status**: Accepted

### Context

D043 introduced desugaring of multi-arg NTs at parser level; D044
added classifier machinery for the same but kept the desugaring as
a fallback for cases the classifier's per-NT infer-mode couldn't
handle (e.g. `compose f (pair …)` — pair has no infer-mode because
its polymorphic schema's result has no canonical ground shape).

The desugaring fallback was honest but kept two sources of truth in
the compiler: parser-level rewrites + classifier entries. Error
messages referenced desugar-fresh variables like `$pair_x`. Runtime
equivalence to `IR.pair` etc. depended on the optimiser's β/η laws
to collapse the lambda+pair+app shapes.

### Decision

Replace the inlining pipeline with **typecheck-time polymorphic
schema instantiation**. A user-declared `PolyFunInfo` is threaded
through `NamedCtx.polys` (a new field), and each call site
instantiates the schema against the call-site expected type,
recursively typechecking the body at the resulting ground type.

For cases where only one side of a poly arrow is known (e.g. `g` in
`compose f g` at check `A → C` — only `A` is known), a new helper
`composeArgB : NamedCtx → RawExpr → Type → Maybe Type` structurally
derives the codomain from the poly schema's domain, bare-builtin
canonical types (fst/snd/id/terminal), or nothing. The derived type
then drives `checkElab` on the poly body.

### Architecture (landed commits, plan 0.6.2)

| Phase | Commit | Scope |
|---|---|---|
| 1 | `723397a9` | `instantiate` / `applySubst` / `schemaArrowCodomain` primitives in `Once.Type` |
| 2 | `c6fa984d` | `PolyCtx` field on `NamedCtx`, plumbing |
| 3a | `eceb23d2` | `checkElab-RVar` poly-lookup fallback |
| 3b | `b854daf2` | `checkCompose` poly fallback via `composeArgB` |
| 5 | `3dac99a8` | Remove inlining pipeline (-891 LoC) |

### Consequences

**User-facing gains:**

- Errors for polymorphic code reference user-written names
  (`swap`, `pair`, etc.) — no more `$pair_x` / `$compose_x`
  leakage from desugar-fresh variables.
- Direct `IR.pair` / `IR.compose` emission — no β/η-fusion
  dependency for runtime equivalence.
- `swap = pair snd fst` at any ground instantiation compiles once
  per unique instantiation (schema-driven, cache-friendly).

**Architectural:**

- Single source of truth for poly-to-ground resolution: the
  `PolyCtx` field threaded through typecheck.
- `Once.Parser.Inline` empty; parser is pure syntactic
  transformation, no semantic rewrites.
- D007-compatible: `instantiate` is structural template matching,
  not unification. No meta-variables.

**Proof-side cost (FINAL, 2026-04-22):**

Initial Phase 4 estimate flagged termination as "pragma + semantic
guard" due to projected WF-refactor blast radius (116+ proof-file
call sites). That estimate assumed preserving the interleaved
typecheck-and-resolve architecture. A session pivot (2026-04-22)
lifted to a **two-phase architecture** that flipped the cost:

- **Phase 1 — structural typechecker.** `checkElab-RVar`'s poly
  fallback now emits a `Surface.poly x T` placeholder constructor
  (added to `Once.Surface.Syntax.Expr`) rather than recursing into
  the body. The mutual block becomes purely structural on
  `RawExpr`; **no TERMINATING pragma needed** on `checkElab` /
  `inferElab` / `checkElab-RVar` or any mutual member. All 151+
  internal sites and all downstream proof files reduce through a
  machine-verified terminating function.

- **Phase 2 — well-founded resolver.** A new `resolveExpr`
  tree-walk (in `Once.TypeCheck.Elaborate`) substitutes each
  `Surface.poly x T` placeholder with the specialised body's
  elaboration. Written with explicit `Acc _<_ (length polys)` as
  a direct argument, so Agda's lex termination checker accepts
  it without a pragma. Localised to one non-mutual function
  (split into `resolveExprWF` + `resolvePolyCase` helpers);
  downstream proofs untouched.

- **Encoding choice (Option A).** An intermediate design used a
  string-encoded `prim ("poly:" ++ x)` placeholder (reusing the
  existing `prim` constructor). It worked but overloaded `prim`'s
  semantics, left cycles silently miscompiled (unresolved prims
  became external function calls at codegen), and required
  string-concatenation cancellation lemmas for proofs. Upgraded
  to a proper `poly` constructor (~6 file touches, ~1 hour):
  cycle safety via Agda's coverage checker, no string encoding,
  direct constructor pattern-match in the resolver.

- **Judgment rule `t-var-poly-instantiate`:** premises and
  conclusion unchanged from the earlier design. Disjointness
  premises (`classifyBareBuiltin x ≡ bbc-other`, `¬ (x ≡ "unit")`,
  `lookupLocal ≡ nothing`, `lookupImport ≡ nothing`,
  `lookupPoly ≡ just (schema, body)`) still make the rule
  disjoint from all other `RVar x` derivations by construction.
  The body-derivation premise is retained for semantic
  soundness but — architecturally important — is no longer used
  by the typechecker-completeness proof.

- **Completeness:** `checkElab-fallback-RVar-poly` in
  `Elaborate.agda` is now a **proven lemma**, no longer a
  postulate. The existential-quantification trick: the signature
  requires `∃ eE`, and `Surface.poly x T` is a valid witness
  under Phase 1 — body's elaboration is the resolver's job, not
  the typechecker's. The `bodyE` premise remains in the signature
  for caller compatibility but is unused in the proof.

- **Soundness:** not added for the poly case; follows the
  `ahv-inl` / `ahv-inr` / `ahv-initial` precedent (elab coverage
  without a forced Soundness theorem).

**Final state (typecheck verification layer):**

- Zero `{-# TERMINATING #-}` pragmas
- Zero postulates
- Zero downstream proof files modified (beyond the one `check-complete`
  case that was already threading the body derivation through)
- `tests/poly-defs.once` passes end-to-end via the new pipeline

**Relationship to D043 / D044:**

- **D043** (desugaring approach): *superseded in full*. The
  desugarings removed from `Parser.Inline` were the final piece.
- **D044** (classifier approach): *compatible and coexisting*.
  The classifier entries (pair/compose/curry/apply) are still
  the check-mode elaboration path. D045 adds the `PolyCtx` layer
  underneath so the classifier entries can recurse into poly
  sub-expressions without desugaring fallback.

### See Also

- D043 / D044 — the two-step migration that D045 finalises
- Plan 0.6.2 — implementation plan with 6 phases (all complete)
- Plan 0.6.1 — overarching Phase C implementation track
- Memory `feedback_load_bearing_lemma_poc.md` — the two-gate POC
  discipline that surfaced the lift-to-nested insight before the
  full refactor was committed

---

## D046: Kind-Unified Arrow — Eff and `_⇒[_]_` Merged

**Date**: 2026-04-23
**Status**: Accepted
**Plan**: 0.5.1 (kind-unified arrow), supersedes the Phase C close-out in plan 0.5

### Context

Before this decision:

- `Type` had two distinct arrow constructors: `_⇒[_]_ : Type → Quantity → Type → Type` for pure arrows and `Eff : Type → Type → Type` for effectful arrows.
- `CCC.IR` had an `applyEff` constructor in addition to `apply`, even though the two behaved identically at runtime (`eval ps applyEff (closure, arg) = closure arg`).
- The x86-64 dispatcher had an `applyEff-placeholder` postulate — the runtime was wired (codegen emitted the same instructions as `apply`), but the correctness proof for the effectful branch was stubbed, since mirroring the full `IRResultAWF` record meant ~30 fields of duplication.

Plan 0.5 Phase C asked the principled question: is `Eff` pulling its weight as a distinct constructor, or is it redundant with the arrow?

### Decision

Unify `Eff` and `_⇒[_]_` via a kind-parameterised arrow:

```agda
record ArrowKind : Set where
  constructor mk-kind
  field
    quantity : Quantity
    purity   : Purity   -- pure | eff

data Type : Set where
  _⇒[_]_ : Type → ArrowKind → Type → Type
  -- ... other constructors
```

`Eff A B` becomes `A ⇒[ mk-kind Many eff ] B`; a pure linear arrow becomes `A ⇒[ mk-kind One pure ] B`.

Consequences at the IR layer:

- `applyEff` removed; `apply {k = mk-kind Many eff}` handles effectful application uniformly via the same runtime path.
- `applyEff-placeholder` postulate eliminated. The dispatcher's `run-apply` is kind-polymorphic by construction.
- `valid-eff-wf` constructor (converted pure-arrow validity to Eff validity) replaced by `valid-coerce-kind-wf`, which names what it does.

Consequences at the frontend:

- Parser keeps `Eff A B` / `IO A` as surface keywords — surface language unchanged. `Once.Parser.Type` produces `A ⇒[ mk-kind Many eff ] B` directly.
- Grammar-layer `GType.TEff` unchanged (grammar AST is a separate layer and outlives this refactor).

### Rationale

Quantity and purity are categorically independent dimensions of an arrow. Forcing them into separate constructors duplicated every proof that pattern-matched on the arrow shape. Once we accepted that `Eff` carried no extra runtime structure — only a type-level tag — the single-constructor form follows.

The orthogonal-record design (`ArrowKind`) was the principled choice over a sum-typed `Purity = pure-p Quantity | eff-p`: there is no "linear effect" in Once, but nor is there anything in the category theory forcing quantity and purity to be dependent. Keep them independent and prove the restrictions at the use sites that need them.

### Consequences

**Eliminated:**
- `applyEff : IR ((Eff A B) * A) B` — IR constructor
- `Eff : Type → Type → Type` — synonym; surface type and `A ⇒[ mk-kind Many eff ] B` are now the same
- `_⇒q[_]_` — synonym; use `A ⇒[ mk-kind q pure ] B` directly
- `applyEff-placeholder` — dispatcher postulate
- `valid-eff-wf` — ValidAtWF constructor, replaced by kind-polymorphic `valid-closure-wf` plus `valid-coerce-kind-wf` for rewrapping

**Made kind-polymorphic (was pure-only):**
- `curry : IR (A * B) C → AllocMode → IR A (B ⇒[ k ] C)`
- `apply : IR ((A ⇒[ k ] B) * A) B`
- `ty-curry`, `ty-apply` in `TypeSystem.Typing`
- `decomposeClosureWF`, `closure-mode-is-heap-proof` in `ClosureWellFormed`
- `run-apply` in the x86-64 dispatcher

**Added:**
- `ArrowKind`, `Purity`, `_≟p_`, `_≟k_`, `pureK`, `effK` vocabulary in `Once.Type`
- `arr : IR (A ⇒[ mk-kind q pure ] B) (A ⇒[ mk-kind Many eff ] B)` — still lifts pure to eff (D032 direction unchanged), just phrased in the unified vocabulary

**Proof-count delta:**
- −1 postulate (`applyEff-placeholder`)
- 46 files touched across the refactor
- 5 unreachable `Eff`-success clauses in `TypeCheck.Soundness` became unreachable-with-warning, now removed
- Zero new postulates; zero new `TERMINATING` pragmas

### Surface-language impact

None. `main : Eff Unit Unit` parses and typechecks as before. The surface keyword `Eff` is now sugar for `A ⇒[ mk-kind Many eff ] B` at the internal-type layer, and round-trips through the grammar printer unchanged.

### Relationship to earlier decisions

- **D032** (arrow-based effects): unchanged. `arr` still tags a pure function as effectful; what changes is the internal representation of the target type.
- **Plan 0.5 Phase C** (close `applyEff-placeholder`): this decision is the principled resolution. The three options considered in Phase C (prove the placeholder, delete `applyEff`, unify at the type level) collapse to one once you admit that `Eff` is redundant — option 3 is the root cause fix, and it closes the postulate as a side effect.

### Alternative considered: keep synonyms as RHS sugar

After landing the refactor, `_⇒q[_]_` and `Eff` briefly remained as RHS-only synonyms (same definitionally-equal form). The argument to keep them was brevity in signatures; the argument to remove them was that two spellings of the same constructor is cognitive load with no proof benefit. The synonyms were removed (this decision); all RHS sites now write `⇒[ mk-kind q pure ]` / `⇒[ mk-kind Many eff ]` explicitly.

### See Also

- Plan 0.5 (IR extension hygiene), Phase C
- Plan 0.5.1 (kind-unified arrow)
- D032 (arrow-based effects)

---

## D047: Rename `Prim` to `SigOp` (Signature Operation)

**Date**: 2026-04-23
**Status**: Accepted

### Context

The IR escape-hatch constructor was named `Prim` (short for "primitive"):

```agda
data IR : Type → Type → Set where
  ...
  Prim : ∀ {A B} → String → IR A B   -- opaque external morphism
```

Two problems with the name:

1. **Categorical confusion.** "Primitive" in programming often means "built-in scalar type" (Int, Float, …). The name nudges readers to believe `Prim : IR A B` requires `A` and `B` to be primitive types. That's **wrong**: `Prim` is an opaque arrow that obeys the CCC's calling convention, and its types can be μ-types (lists, trees), products, coproducts — anything. The constraint is *protocol compliance at the target*, not type shape.

   The actual "primitive types" predicate `IsPrimitive : Type → Set` already exists and is correctly named — it classifies register-representable types for layout purposes. It is *unrelated* to the `Prim` IR constructor. Two completely different axes, same misleading prefix.

2. **Greppability.** Short generic names like `Prim` (or the alternative `Op`) collide with many unrelated occurrences in a codebase — documentation prose, user identifiers, stdlib names. A unique token is trivially auditable.

### Decision

Rename the IR escape-hatch constructor to **`SigOp`** (signature operation), matching the universal-algebra / operad-theory term for a basic operation in a signature. Rename surface vocabulary and all dependent machinery consistently.

### Rationale

The correct categorical framing: the IR is the **free cartesian closed category generated over a signature Σ**. The CCC's structural morphisms (id, ∘, fst, snd, pair, inl, inr, case, terminal, initial, curry, apply — the 12 generators of D001) are the axioms of CCC structure; the rest of Σ consists of "signature operations" — axiomatic arrows that are *given* rather than *derived*. `SigOp` is the inclusion of Σ into the free CCC.

Why `SigOp` over alternatives:

- **`Op`**: correct universal-algebra term but collides with every "operation" / "operator" / `_+_` in the tree. Loses the pragmatic grep win.
- **`Foreign`** / **`Extern`**: programmer-intuitive (FFI) but not categorical. Once's naming policy is to follow established math vocabulary rather than invent per-language terms.
- **`Generator`**: already used in D001 for the 12 structural CCC morphisms. Conflating the two kinds of generator would defeat the purpose of the rename.
- **`Axiom`**: logic-flavored; less common in CT proper.

### Surface keyword

The corresponding surface-language declaration form renamed from `primitive` to `signature`:

```once
-- before:
primitive exit : Eff Int Unit

-- after:
signature exit : Eff Int Unit
```

Reads as "declare `exit` as a signature operation of type …" — the intent is explicit.

### Scope of the rename

- `Prim` → `SigOp` (IR constructor, all case analyses, all WF proofs)
- `prim` → `sigOp` (Surface expr constructor)
- `DPrimitive` → `DSignature` (parser Decl constructor)
- `parsePrimitive` → `parseSignature`
- `primitivesWithOwner` → `signaturesWithOwner`
- `PrimSem` → `SigOpSem`; `primSem` → `sigOpSem`
- `evalPrim` → `evalSigOp`; `defaultEvalPrim` → `defaultEvalSigOp`; `defaultPrimSem` → `defaultSigOpSem`
- `PrimContract` → `SigOpContract`; `prim-proof` → `sigOp-proof`
- `prim-desugar` → `sigOp-desugar`; `desugar-correct-prim` → `desugar-correct-sigOp`
- `ty-prim` → `ty-sigOp`
- `run-prim` → `run-sigOp`; `normal-prim` → `normal-sigOp`
- `h-Prim` → `h-SigOp`
- `evalSurfacePrim` → `evalSurfaceSigOp`
- `resolveExpr-prim` → `resolveExpr-sigOp`
- `"primitive"` → `"signature"` (parser keyword token)
- Directories: `formal/Once/Arith/Prim/` → `formal/Once/Arith/SigOp/`; `formal/Once/CCC/Prim/` → `formal/Once/CCC/SigOp/`
- `.once` files: every `primitive NAME : TY` → `signature NAME : TY`

### Explicitly NOT renamed

- **`IsPrimitive`** and its constructors (`is-unit`, `is-int`, `is-float`, `is-str`, `is-buffer`). This predicate classifies register-representable Types and is correctly named. It is orthogonal to `SigOp` — the rename clarifies that the two concepts were never meant to be related.
- **`is-prim`** (local parameter names referring to IsPrimitive evidence) — these are talking about primitive types, not signature ops.
- **`primCharEquality`, `primCharToNat`, etc.** — Agda stdlib builtins using Agda's own `primitive` keyword. Unrelated.

### Semantic equivalence

The rename is purely syntactic. Every type-check, every extracted MAlonzo module, every generated x86 binary produces byte-identical output. Verified by re-running `make compiler` + MAlonzo extraction + cabal rebuild + the layer-0 smoke test: all produce the same results as before the rename.

### Consequences

- **Greppability.** `grep SigOp` gives exactly the signature operations. No false positives from stdlib or user code.
- **Documentation.** Comments and error messages now distinguish "signature operation" (opaque CCC escape hatch) from "primitive type" (register-representable shape). These were conflated only by name coincidence.
- **Future layering.** When platform-specific providers (Linux syscalls, seL4 syscalls, GPU kernels) register their signatures, the vocabulary is uniform: "provider X contributes these `SigOp`s to the signature."

### See Also

- D001 (Generators as Reserved Words) — the 12 *structural* generators of the CCC; distinct from signature operations.
- Universal algebra: an "operation" in a multi-sorted signature is exactly what this constructor encodes.

## D049: `--exact-split` for Bug-Hiding Catch-All Class

**Date:** 2026-04-26
**Plan:** 0.9 (Exhaustive Semantic Case-Splits)
**Status:** Adopted with scoped enforcement; full project-wide error
promotion deferred.

### Decision

Enable Agda's `--exact-split` option project-wide via
`formal/Once.agda-lib`'s `flags:` field. The flag emits a
`CoverageNoExactSplit` warning whenever a clause's case-tree
compilation can't preserve definitional equalities — i.e. whenever
a clause sits as a catch-all relative to a more specific sibling.

For the bug-hiding subset of catch-alls (those whose return type
matches a state value and that silently absorb unmodeled cases as
identity / zero / no-op), refactor to either:
- explicit per-constructor enumeration, or
- a named postulate the clause delegates to.

For the safe subset of catch-alls (Bool predicates, `Maybe`-
returning parsers, typed `failure`-returning checkers, ⊤/⊥
inductive predicates, view-tag-returning classifiers), leave the
warnings in place as a **discipline backlog** until they're
addressed file-by-file. Each refactor must verify that downstream
proofs still build — some catch-alls preserve definitional
reductions that proofs depend on (see `Once/Type.agda`'s `_≤q_`
and `Once/Grammar/Convert.agda`'s round-trip lemmas).

`-W error=CoverageNoExactSplit` is **not** flipped on globally yet.
It will be flipped once the discipline backlog is cleared. At that
point, every `{-# CATCHALL #-}` pragma becomes a finite, greppable
audit surface (analogous to `make postulates`), and every new
catch-all without a pragma becomes a compile error.

### Why

The `lea r9 (rip+disp 4)` codegen bug (plan 0.2.4.1 Phase D, fixed
in commit f00e8126) was hidden by a single line in
`Once.CCC.Target.X86-64.DirectSimulation.exec-x86`:

```agda
exec-x86 _ xs _ = xs    -- catch-all: unmodeled instrs = identity
```

The function had explicit clauses for ~15 instructions; everything
else fell through to the no-op catch-all. The abstract semantics
therefore didn't constrain what `r9` held after `lea r9 …`, and
no downstream proof could contradict the wrong byte offset. The
bug was real, the type checker accepted it, `make postulates`
found nothing, every proof in the `compile-correct` chain
succeeded.

This was a class of silent under-specification. The mechanism was
already in the Agda compiler: the `--exact-split` option flags
exactly these catch-alls. Combined with `{-# CATCHALL #-}` for
deliberate exceptions, the catch-all surface becomes finite and
greppable on par with the postulate surface.

### What Was Done

**Phase B (DirectSimulation, 3 targets — X86-64, X86-32, RiscV64).**
The single `exec-x86 _ xs _ = xs` catch-all was split into per-Instr-
constructor explicit clauses. Operand-shape catch-alls within
`mov`/`lea`/`add`/`sub`/`push`/`pop` (which can't be enumerated —
unbounded `imm n` operand) route to **named postulates**
(`exec-x86-mov-other`, `exec-x86-lea-other`, etc.) visible in
`make postulates-grep`. The `lea r9 (rip+disp …)` site that hid
the original bug now produces an opaque postulated term — not
silent identity.

The CATCHALL pragma stays on those dispatch clauses (the case-tree
overlap with explicit clauses is unavoidable given the unbounded
operand product), but the body is no longer silent identity. 17
CATCHALLs remain in DirectSim, all routing to postulates.

**Phase C (Optimize.agda).** Zero CATCHALL, zero
`CoverageNoExactSplit`. `_≟Type_` / `_≟Functor_` / `≟IRH-diag` with-
blocks extracted to top-level helpers; predicates rewritten via
`ir-head + dec-to-bool + _≟IRHead_`; views enumerate all 24 IR
constructors.

**Phase D (per-file sweep).**

| File | Sites before | After | Notes |
|---|---|---|---|
| Once/Type.agda | 19 | 0 | Quantity ops keep `Zero op _` to preserve definitional reductions |
| SMPrimitives | 6 | 0 | All AbstractInstr enumerated |
| SMCore | 4 | 0 | `writeStackMem-aux` order chosen for proof reduction |
| WriteOps | 1 | 0 | `(yes refl)` patterns for case-tree exactness |
| RecTrace | 1 | 0 | Mechanical |
| TypeCheck/Raw | 2 | 0 | BinOp enumeration |
| TypeCheck/Elaborate | 33 | 23 | `≟T`/`≟F` and `classifyAppHead` done; deeper `inferElab` Type-shape and `checkElab-RVar` failure-propagation deferred |
| Grammar/Convert | 8 | 8 | Reverted — round-trip proofs depend on the catch-all reducing definitionally |
| X86-64/Syntax | 2 | 0 | **`instr-consumed-slots` was the last remaining bug-hiding catch-all** — silently returned 0 stack-slot consumption for unmodeled instructions, same class as the lea-offset bug |
| Parser modules + ExprBridge | ~46 | ~46 | Mechanical Token-enumeration backlog |

**Phase E (this entry).** Added `make catchalls` Makefile target —
greps every `{-# CATCHALL #-}` pragma with file:line. Parallels
`make postulates-grep`. Did NOT flip
`-W error=CoverageNoExactSplit` to error globally — would block the
build until the ~85-site discipline backlog is finished.

**Phase F.** This decision log entry plus
`docs/formal/guides/exhaustive-semantics.md`.

### Bug-Hiding Class: Closed

The motivating bug class — "function returns the same type as some
state value, and the catch-all silently absorbs unmodeled cases as
identity/zero/no-op" — is **fully closed across the codebase** as
of this plan. The two known sites:

1. `exec-x86` in three target simulators (Phase B).
2. `instr-consumed-slots` in `X86-64/Syntax` (Phase D).

both now require per-constructor explicit clauses. Adding a new
`Instr` (or `AbstractInstr`) constructor that allocates stack /
mutates state forces these functions to be updated — compile
error, not silent under-modeling.

### Discipline Backlog (Safe Catch-Alls)

The remaining ~85 warnings are in safe shape:

- **Bool predicates** with explicit "no" semantics (`isComparisonOp`,
  parser `Not*` predicates).
- **Maybe-returning parsers** with explicit "couldn't parse"
  fallbacks (`parseAllocB`, `parseSignatureB`, view classifiers).
- **Typed `failure`-returning checkers** (`checkCompose`,
  `inferElab` shape mismatches).
- **⊤/⊥ inductive predicates** (already enumerated for `InstrPreservesFrame`-
  style; `NotDot`/`NotAdd`/etc. are the same shape and just need
  Token enumeration).
- **Proof completeness with-blocks** (`complete-cmpWFraw`).
- **View `*-other` tags** (already done in `Optimize`; same pattern
  in `Parser/Expr` views).

None of these silently absorb state mutations. Refactoring them is
hygiene; refactoring them carelessly can break downstream proofs
(see Convert.agda revert). They should be addressed file-by-file
with `make compiler` re-run between commits.

### Tooling

- `formal/Once.agda-lib`: `flags: --exact-split`.
- `make catchalls`: lists every `{-# CATCHALL #-}` pragma.
- `make postulates-grep`: lists every `postulate`.
- `make exact-split-census` (new): rebuilds and prints the unique
  warning sites.

### Lessons

1. **Catch-alls preserve reductions.** `Zero ≤q _ = true` reduces
   `Zero ≤q q ≡ true` for any variable `q`; fully enumerating the
   9 cases breaks proofs relying on that reduction. Structure
   refactors so the special-case branch stays single-clause.

2. **`(yes refl)` patterns.** When `Dec X` is decomposed in a
   helper, use `(yes refl)` consistently rather than mixing
   `(yes refl)` with `(yes _)`. The case-tree compiler can't
   preserve overlap between the two.

3. **`with`-block proofs are brittle.** The Convert.agda revert
   showed that a function's catch-all and a downstream proof's
   `with`-block reduction can be tightly coupled — refactoring
   one without the other breaks the proof. Treat such pairs as a
   single unit.

4. **Postulate-bodied dispatch.** When operand-shape enumeration
   is impossible (unbounded `imm n` operand space), routing the
   catch-all to a named postulate is more honest than silent
   identity. The CATCHALL pragma stays but the audit surface
   shifts to `make postulates`.

### See Also

- Plan 0.9 (`plans/0.9-exhaustive-semantics.md`) — the gap-class
  catalogue. This decision closes class **Catch-all in semantic
  pattern**; classes A–H remain.
- D047 (Rename `Prim` to `SigOp`) — vocabulary discipline.
- The lea-offset bug commit (f00e8126) — the discovery that
  motivated the plan.
- `docs/formal/guides/exhaustive-semantics.md` — usage guide for
  `{-# CATCHALL #-}` and the audit-surface conventions.

## D053: Layer-0 Closure Calling Convention (`%r12` + (env, arg) Pair)

**Plan:** 0.2.4.2 (Closure Codegen Fix), Phase D follow-up.

**Decision.** A closure on x86-64 is a 2-word record laid out as
`[env, code-addr]`. Calling a closure with argument `arg` is a
two-step operation:

1. **Closure register** — `%r12` holds the closure pointer for the
   duration of the call. The call site does `call *0x8(%r12)`.
2. **Argument convention** — `%rdi` points to a freshly-built
   `(env, arg)` pair on the caller's stack frame. The closure body
   reads its captured environment via `fst` and its argument via
   `snd`, both relative to `%rdi`.

**Why two pieces of state?** Pure-SysV would put the argument in
`%rdi` directly, but Once closures capture an environment that the
body also needs. Passing the pair by pointer is the natural shape;
`%r12` is callee-saved in SysV, so a long body can use scratch
registers without spilling the closure pointer.

**Consequence: a new `AbstractInstr`.** The `apply` IR primitive
needed to put the closure pointer into `%r12` somewhere between
"load it from the input pair" and "build the new (env, arg) pair
in `%rdi`". That's now `instr-save-closure-reg`, abstractly an
identity (we don't track `%r12` at the abstract level), per-arch
lowering `movq %rdi, %r12` on x86-64 (and `ud2`/`unimp` stubs on
the other backends until layer-0 reaches them).

**Consequence: `_start` must build the pair.** When `_start` calls
the top-level `main` closure with `()` as the argument, it has to
construct an `(env, ())` pair on the stack and set `%rdi` to point
at it — same as `apply` would. Failing to do this segfaults on the
body's first instruction (`fst` dereferences `%rdi`).

**Verified by:** `Layer0/id returns input (exit 42)` regression
test in `compiler/test/Layer0Spec.hs` — `main = exit@S (id 42)`
compiles and the resulting binary exits with code 42.

**Known limitation (separate from D053):** The default optimizer
currently elides effApp closure bodies when it shouldn't, so the
Layer-0 regression tests pass `--no-optimize` for now. Tracked
separately.

---

## D054: `Int` Means the CPU's `add` (Modular `Word`); Mathematical Integers Are a Separate Future `BigInt`

**Date:** 2026-05-27, revised 2026-05-28.
**Status:** Accepted.

> Revised 2026-05-28: this decision originally framed the choice as a
> proof-mechanism question. That was solving a symptom. The underlying
> question is *what Once's arithmetic means* — the numeric model below.
> The earlier ℤ-vs-ℕ-vs-`Fin` framing and "programmer-managed overflow"
> are superseded by it.

### Context

Once's arithmetic needs a denotation. The codebase reflexively used
Agda's `ℤ` as the meaning of `Int` (`eval-arith`, `semI` are all ℤ)
while compiling to fixed-width CPU registers, then tried to prove the
two equal. That straddle is the *root* of the no-overflow side
conditions, the ℕ-with-monus placeholder, and the
ℤ↔Word encode/decode mess — not bad luck in the proofs.

The governing fact (arithmetic, not effort): **representation follows
the promise.**

- Mathematical `+` (unbounded) ⟺ a *growable* representation (bignum).
- A *fixed-width* representation ⟹ *modular* semantics, `(x+y) mod 2ⁿ`.

There is no third option. You cannot prove fixed-width `add` equals
unbounded ℤ `+`, because they are different functions (`255 + 1 = 0`
in a byte, `= 256` in ℤ). The no-overflow precondition is exactly the
narrow regime where the impossible accidentally holds.

What real verified compilers do — each type's representation matches
its promise:

- **C / CompCert:** `unsigned` is *defined* modular by the C standard;
  the runtime value type **is** the modular word. ℤ appears only as
  scaffolding inside the definition of the modular op (`repr (x+y)`),
  never as a promise to the programmer.
- **CakeML:** SML `int` is arbitrary-precision, implemented as
  **bignums** and proven against that growable representation — not
  against a single `add`. CakeML *also* has `Word64`/`Word8`, which
  are modular. Two promises, two representations.

### Decision

**Once's `Int` means exactly "whatever the target CPU's `add` / `sub`
/ `mul` computes" — modular arithmetic on an n-bit `Word`, where n is
the target word size. Its denotation is `Word`, not ℤ.**

Wraparound (`255 + 1 = 0`) is *correct, defined* Once semantics — not
a bug, not undefined behaviour, and not something the programmer or
the compiler must prove absent. This is the fixed-width-modular camp
(C, Go, Rust, WASM), as opposed to arbitrary-precision.

**`Int` is signed.** `add` / `sub` / `mul` are bit-identical for
signed and unsigned under two's complement, so the choice only bites
at the sign-sensitive ops — and there `Int` takes the **signed**
instruction: division/remainder → `idiv`, comparison/branch → `jl` /
`jg` (signed), right-shift → `sar` (arithmetic). Rationale: signed
matches the `a < b` intuition and avoids unsigned's foot-guns (the
cliff at zero, `0 - 1` = huge; silent signed↔unsigned comparison
flips). Java made the same call deliberately.

**Other number types are separate, opt-in, deferred types over the
same `Word`** — added later, if a real need appears, by the same
staged discussion this decision came from:

- **`UInt`** — unsigned. Shares `Word` and the `add`/`sub`/`mul`
  opcodes; differs only by emitting `div` / `jb` / `shr` at the
  sign-sensitive ops. No new representation work.
- **`BigInt`** — mathematical (unbounded) integers, with a ℤ
  denotation over a growable bignum representation (CakeML's road).
  Real runtime machinery; most programs never need it.

The hard rule for any future type: **no implicit conversion between
them.** That is what neutralises the actual harm in mixing signed /
unsigned (and in silently widening to bignum).

**Crucial staging constraint — separate the two number-worlds *by
type* from day one.** ℤ must stop being the meaning of the fixed `Int`
*now*, even though `BigInt` does not exist yet. The tempting middle —
"leave ℤ as `Int`'s meaning for now, add bignum later" — does **not**
stage cleanly: it keeps the impossible promise on the fixed type and
preserves every no-overflow hole. The existing ℤ-based `eval-arith` /
`semI` are not thrown away; they become the *parked spec* of the
future `BigInt` type.

### Rationale

- **It makes correctness statable and near-trivial.** Source `+` and
  machine `add` become the *same* operation by definition, so the arith
  refinement obligations collapse toward `refl` instead of carrying
  no-overflow preconditions. There is nothing to assume away.
- **The semantics becomes unconditionally faithful to silicon.**
  Modeling wraparound means `execInstr (add ...)` is just true,
  including on overflow — no trusted "within the no-overflow regime"
  caveat hiding in a header comment.
- **It is the mainstream, validated choice.** C/CompCert, Go, Rust,
  WASM all define fixed-width `+` as modular. CakeML shows the other
  fork (math `+` ⇒ bignum). We are picking a fork deliberately, per
  type, not straddling.
- **It defers cost where cost is rare.** Arbitrary-precision integers
  carry real runtime machinery (heap-allocated, growing). Few Once
  programs need them; pay for them only when `BigInt` ships.

### Consequences

- `Int`'s machine-path denotation (`eval-arith` / `semI`) is
  redefined over `Word` (modular). The ℤ versions move *out* of the
  fixed path and are retained as the seed spec for a future `BigInt`.
- The no-overflow side conditions, the ℕ-with-monus placeholder, and
  the ℤ↔Word encode/decode bridge all **disappear** from the fixed
  path.
- The earlier ℤ-vs-ℕ-vs-`Fin` question and the "programmer-managed
  overflow" framing are superseded: the answer is "neither — `Word`,
  defined identically at source and machine."
- **Language-spec obligation:** document that Once `Int` arithmetic
  wraps (modular), so it is a stated promise, not a surprise.
- `BigInt` is future work: new type, ℤ denotation, bignum runtime
  representation, proven against the growable representation (not
  against a CPU `add`).

### Open questions

None. (Division by zero / signed-overflow behaviour is settled in
D055.)

(Forward pointers, not open questions of this decision: when `UInt`
and `BigInt` land, and what user-facing types select them over the
default signed `Int`.)

## D055: Division and Remainder Are Total — RISC-V Semantics (No Trap)

**Date:** 2026-05-28.
**Status:** Accepted.

### Context

D054 fixed `Int` as a signed, modular `Word`, with `+` / `-` / `*`
**total** (wraparound is a defined value, never a fault). Division is
the one arithmetic op where the target silicon *disagrees*, so it
can't simply "be the CPU":

- **x86:** `idiv` **traps** (`#DE` → SIGFPE) on both `a / 0` *and*
  signed overflow `INT_MIN / -1`. No result value — a control-flow
  fault.
- **RISC-V:** by design has **no arithmetic traps**. Division is total
  and returns defined sentinel values (below). The check is left to
  software, where it's a single elidable branch.
- **ARM:** also returns a defined value (no trap).

RISC-V is the modern clean-slate design and the one consistent with
D054's philosophy: arithmetic ops are pure, value-returning, with no
control-flow side effects.

### Decision

**Once's `/` and `%` are total functions over `Word`, following
RISC-V's defined results. No trap, no fault, no partiality.**

For signed `Int`:

- `a / 0` = `-1` (all-ones); `a % 0` = `a`. This keeps the division
  identity `a = (a / b) * b + (a % b)` true even at `b = 0`
  (`(-1)*0 + a = a`).
- `INT_MIN / -1` = `INT_MIN`; `INT_MIN % -1` = `0`. (The quotient
  wraps, matching the `*` wraparound convention.)

Division therefore has the *same shape* as `+`/`-`/`*`: a defined
value for every input. Code that wants to *detect* a zero divisor does
so explicitly (test the divisor, or recognise the sentinel), exactly
as RISC-V software does.

### Backend obligation

- **RISC-V:** native — emit `div` / `rem` directly; behaviour matches
  by spec.
- **x86 / ARM (trapping `idiv`):** emit a guard (compare divisor /
  detect the overflow case, branch) that *produces the RISC-V-defined
  value* instead of executing the trapping instruction. The guard may
  be elided wherever the compiler can prove the divisor is nonzero and
  the operands aren't the `INT_MIN / -1` case.

No Once-compiled program ever raises `#DE` / SIGFPE.

### Rationale

- **Consistency with D054.** `+`/`-`/`*` are total value-returning
  ops; division becomes one too. *All* Once arithmetic is then pure —
  no instruction has a control-flow side effect. That is precisely the
  RISC-V principle.
- **Portability.** One uniform semantics across every target, instead
  of "traps on x86, returns a value on RISC-V." The meaning of `a / 0`
  doesn't depend on which backend you compiled with.
- **Principled source.** RISC-V's choice preserves the div/rem
  identity, uses detectable sentinels, and keeps the cost (a branch)
  in software and elidable.
- **Cost lands only where the hardware forces it.** Trapping targets
  pay for a guard; RISC-V pays nothing; everyone gets the same answer.

### Consequences

- The `/` and `%` denotations are total over `Word` — no partial
  function, no `SigOp` fault event for division.
- x86 / ARM backends gain a small div-guard codegen step; RISC-V emits
  the bare instruction.
- When `UInt` lands (D054), unsigned `/` `%` follow RISC-V's unsigned
  definitions by the same rule (`a / 0` = all-ones = `2ⁿ-1`,
  `a % 0` = `a`; no signed-overflow special case).

---

## D056: One Realm — Morphism-Realm Composition for the Effectful Path and Values

**Date**: 2026-06-09
**Status**: Accepted (design); implementation in Plan 0.40
**Supersedes**: the closure-fallback / `effCompose` framing in `docs/design/effect-composition.md`
**Completes**: D044 + D045 for the effectful path and for value injection

### Context

D044/D045 moved composition onto the **morphism-realm classifier**: `compose`/
`case`/`pair` elaborate to direct `IR.compose`/`IR.case`/`IR.pair` (via `spec*`),
the parser-level desugaring was removed (`Parser.Inline` empty, −891 LoC), and
`composeArgB` + `PolyCtx` recover middle types without a desugaring fallback.
"Direct IR emission, no optimizer β/η dependency" was the explicit win.

Two residuals remained, and both block Plan 0.36's effectful cata:

1. The **effectful** `compose`/`case` were never folded into that path — they
   are a separate elaborator clause that only fuses (`extract-morph-eff`), with
   no fallback, duplicating the pure path.
2. `composeArgB` recovers the middle type from poly schemas, bare-builtin
   canonical types, and arrow-typed imports — but **returns `nothing` for a
   value-typed name**. So `compose emitAll xs` with `xs : Mu` (a value) fails,
   even though the cata algebra itself fuses.

Plan 0.39 separately found the optimizer **unsound** (it dropped effectful
SigOps), which retroactively confirms D044/D045's "no optimizer dependency" as
a *soundness* requirement, not a convenience.

### Decision

One realm — **morphism** — for composition **and** values:

1. **Unify pure and effectful `compose`/`case` into one grade-polymorphic
   classifier path.** The IR is grade-erased (`eff ∘` *is* `pure ∘`), so per
   D046 this is one mechanism, not two. Delete the bespoke eff clauses.
2. **`composeArgB` and the point-free check-mode use D018's value-lift.** A
   value `v : B` used where a morphism is expected is the constant morphism
   `const v : Unit → B` (codomain `B`). Value-typed defs inject like any morphism.
3. **`curry`/`apply` stay as exponentials** (higher-order, partial application;
   D053 calling convention). They are *not* a parallel composition realm.
   First-order functions are morphisms; a first-order lambda should not become a
   `curry`-closure.
4. **No `effCompose`** (D032: one category, one `compose`). The closure-realm
   *as a composition path* is retired; what remains of "closures" is exponentials.

### Rationale

D032 (one unified category), D046 (don't duplicate a mechanism identical at the
grade-erased IR), D044/D045 (the morphism/classifier route was already the
chosen direction), D018 (values are constant morphisms), and Plan 0.39 (optimizer-
independence is now required for soundness). The effectful path being a
fallback-less copy of the pure path is exactly the D046 anti-pattern at the
elaborator level.

### Consequences

- Delete the bespoke effectful `compose`/`case` elaborator clauses; route eff
  through the grade-poly classifier path.
- Extend `composeArgB` (and the consuming check-mode path) with the value-lift.
- Unblocks Plan 0.36's eff cata `main` with no closure fallback and no second
  structure.
- **Proof obligation:** effectful `∘` sequences effects in source order
  (run `g`, then `f`) — discharged against the trace semantics, not assumed.

### See Also

- D018 (value lift), D032 (arrow effects), D043/D044/D045 (the migration this
  completes), D046 (kind-unified arrow), D053 (closure calling convention)
- Plan 0.36 (the eff cata this unblocks), Plan 0.39 (trace-correct optimizer),
  Plan 0.40 (implementation)

## D057: Correctness Is Anchored at a Source-Level Reference Semantics (Not the IR)

**Date**: 2026-06-13
**Status**: Accepted; Plan 0.45 (Part A landed; Part B = the discharge)
**Supersedes**: the IR-pivot meaning `⟦ src ⟧ := obs (elaborate src)` (Plan 0.24 Phase C, `Once.Verified.SourceTrace`)

### Context

A Once program returns nothing; its only observable is the ordered sequence of
SigOp calls it makes (Plan 0.44: `Behavior = ℕ → List SigOpEvent`). Plan 0.44
fixed the observable *type* and the apex statement (`exec arch bytes ≈ ⟦ src ⟧`),
but the *meaning* stayed `⟦ src ⟧ := obs (elaborate src)` — defining the source's
meaning **as the elaborator's output**. That anchors the spec at the IR: the
~2400-line elaborator is baked into the spec, so a meaning-changing elaboration
moves *both* sides of `correct` together and cannot be caught. The typechecker
was **not load-bearing** — which is why its proof-structure problems never showed
up as a constraint.

CCC+SR is a fine denotational semantics *of the IR*, but the surface→CCC
translation (the elaborator) is non-trivial and could map a program to a morphism
that doesn't mean what the program says. Trusting it as the spec is an
*assumption*, not a *theorem*.

### Decision

Anchor `⟦ src ⟧` at a small **source-level reference semantics**, computed
independently of the elaborator. `sourceTrace : Source → Behavior`
(`Once.Verified.SourceSemantics`, **154 code lines**) is a direct fuel-bounded
interpreter over `RawExpr` that emits the SigOp trace. The full `compile`
(typechecker included) is then *proven* to preserve it (`elaborate-preserves-
trace`, inside `Compile.module-to-asm-correct`) — making the elaborator
**load-bearing**.

Reference design:
- Untyped `Value` with **defunctionalised** closures — a HOAS `Vfun : (Value →
  Value) → Value` is not strictly positive. **Fuel** for termination — an
  *internal* device only. (~~the fuel is `Behavior`'s step index~~ **CORRECTED by
  D058**: `Behavior`'s index is the effectful-EVENT count, not a step count; the
  fuel never appears in the observable.)
- **SigOp application is the sole emitter** (mirrors `obs`); **arith is pure**
  (the arith→SigOp lowering is internal optimisation only); events in eval order.
- `cata` folds via `In`-position detection (recursive positions are exactly
  `Vin`-wrapped) — no functor witness needed at runtime.

### Rationale

The reference must be *much* smaller than the elaborator (154 vs ~2400 lines,
~16×) and structurally unlike it (no type inference / closure records / codegen),
or it just moves the trust. Anchoring below the parser, above the elaborator
(`Source = GModule`; text→`GModule` stays trusted) verifies the typechecker while
keeping a trustworthy reference.

### Consequences

- The IR pivot is gone; `module-to-asm-correct` now spans the elaborator. **Part
  B** is `elaborate-preserves-trace` — an untyped-source ↔ typed-IR bridge
  (CompCert-style), and the place the frontend's proof-structure issues (value-
  lift clause overlap, `with`-opacity) surface *inside the grand theorem* and get
  resolved, rather than as an isolated `ErrorProofs` island.
- The typed layers (`evalSurface` on `Expr`, `obs` on IR) keep their typed/HOAS
  semantics; the untyped defunctionalised reference is local to `sourceTrace` and
  forecloses nothing about future dependent types.
- Faithfulness obligations (Part B): `divℤ`/`modℤ` agree with the value
  semantics'; multi-argument SigOps (the reference treats SigOps as 1-arg).

### See Also

- Plan 0.44 (Behavior = the SigOp trace), Plan 0.45 (this), Plan 0.24 (`obs` and
  the superseded IR pivot)
- D054 (`Int` semantics), D055 (div/mod totality)

## D058: Correctness Is the Effectful-SigOp Trace, EVENT-Count-Indexed (Not Step-Indexed)

**Date**: 2026-06-14
**Status**: Accepted; **corrects the index framing** of D057, Plan 0.24, Plan 0.44
**Supersedes**: "the fuel is `Behavior`'s step index" (D057); "`Behavior n` = the
prefix observed within `n` steps" (`Once.Verified.Behavior`, Plan 0.24/0.44)

### Context — the misunderstanding this exists to prevent

`Behavior = ℕ → List SigOpEvent` has **two independent dimensions**, and they
were repeatedly conflated:

1. **The list ELEMENTS** — *which* events are observable. Settled: **EFFECTFUL
   SigOps only** (`linux.exit`, `print`, …). Pure SigOps (the arith→SigOp
   lowering) are an *internal optimisation* and emit **nothing**. *(the content)*
2. **The INDEX `n`** — what "the prefix at `n`" *means*. **The type
   `ℕ → List SigOpEvent` says nothing about what `n` counts** — "first `n`
   events" and "events within `n` execution steps" have the *identical type*.
   *(the index)*

The **content** was always specified correctly (effectful SigOps). But the
**index** silently drifted to **step-count** — an early *productivity-avoidance*
compromise (`Behavior`'s doc: *"prefix within `n` steps … plain induction on `n`,
no co-data, no productive bind"*), chosen because event-count indexing of a
possibly-infinite (productive) trace *seems* to need co-data while step-count is
finite-by-fiat. The drift was **invisible** (the type masks it) and **harmless
for terminating Layer-0 programs** (a single `exit`: step-prefix = event-prefix
for large `n`), so no test or proof ever distinguished the two indices — until an
*operational* interpreter made step-fuel load-bearing for `apply`, and the
step-vs-event conflict surfaced as bogus "completion / `take` / fuel"
reconciliation. Nothing slipped past the *stated* spec; an unlabelled `ℕ` quietly
meant a different thing from day one.

### Decision — the correctness meaning, crystal clear

> **`Behavior n` = the first `n` EFFECTFUL SigOp events, in order.**
>
> **`correct : ∀ n → exec arch bytes n ≡ ⟦ src ⟧ n`** — the compiled binary
> invokes *exactly* the same effectful SigOps, in the same order, as the
> source reference, at every observation depth `n`.

Non-negotiables:

- **INDEX = effectful-EVENT count.** `n` counts effectful SigOps emitted. It is
  **never** execution steps.
- **CONTENT = effectful SigOps only.** Pure SigOps contribute `[]`.
- **The trace is a finite-prefix FAMILY indexed by events — NOT co-data.** A
  possibly-infinite effectful trace is represented as `Behavior = ℕ → List
  SigOpEvent`, where `Behavior n` = the first `n` effectful events. "Same trace" =
  `∀ n, Behavior n` agree — the inductive form of trace-equality (≡ Colist
  bisimilarity *as observed through its finite prefixes*). **Nothing is assumed
  finite.** *Why not an actual `Colist`/stream:* sequencing effects in a
  coinductive trace needs a **productive monadic bind**, which is not definable
  under plain `--guardedness` and would force `--sized-types` (rejected — has
  bitten this project; Plan 0.24/0.44). The finite-prefix family avoids co-data,
  bind, and funext entirely. *(CORRECTION TRAIL, 2026-06-14: an even-earlier draft
  said "no co-data required"; I then over-corrected to "the trace IS co-data" —
  **both framings were noise.** The settled position: no co-data (bind problem,
  Plan 0.24), finite-prefix family, and the index counts EVENTS not steps. What
  the original "no co-data" draft got wrong was only the steps-vs-events index —
  NOT the absence of co-data. OCP-0003's `ana` "Stream of events" is the
  *intuition*; the formal observable is its event-indexed prefix family.)*
- **NO completion / NO "run halts".** `Behavior n` is well-defined because the
  system is **productive**: the first `n` effectful events fire after finitely
  much work. A terminating program's trace stabilises (`take n` of `k<n` events =
  the `k`); a productive one keeps emitting. "Enough work to emit `n` events" is a
  **productivity** fact — never a completion/termination one.
- **STEP-FUEL is an internal termination device, never the observable index.**
  Any interpreter (the source reference, `otrace`, the machine) may carry fuel to
  satisfy Agda's totality checker *for its pure part*; that fuel must not appear
  in `Behavior`/`correct` and must not be read as a completion assumption. The
  **event count** bounds the effectful/productive part; the **pure part
  terminates structurally** (totality of CCC+SR — e.g. `Cata` via `sem-cata`,
  closures via a structural/Kleisli representation, not a fuel crutch).

### Rationale

Splitting the two dimensions makes the invisible visible: the type can only carry
the content honestly, so the index meaning must be stated *in words* and pinned
top-down. Event-count is the only index that is calibration-free (no machine-step
↔ source-step lockstep) and faithful for productive programs. Productivity — not
co-data avoidance, not termination — is the correct justification for "first `n`
events exists"; embracing it removes the step-index hack at its root.

### Consequences

- The index is fixed **top-down**: `Behavior` → `⟦src⟧`/source reference →
  `exec` → `⟦_⟧IR`/`otrace` → `flat-events` **all index by effectful-event
  count**. Nothing below may redefine the index.
- The source reference (D057) and `otrace` must *deliver* "first `n` effectful
  events"; their internal step-fuel is not the index.
- Pure-part termination (e.g. `apply` of a closure) is **structural** (Kleisli /
  build-at-`curry`, apply-by-application), not a fuel crutch. A fuel index that
  leaks into the observable is **forbidden**.
- **D057 correction:** its "Fuel for termination; the fuel is `Behavior`'s step
  index" is wrong on the second clause — the fuel is an *internal* termination
  device; `Behavior`'s index is the **effectful-event count**.

### See Also

- D057 (source-level reference; **step-index framing corrected here**)
- Plan 0.44 (Behavior type), 0.45 (source meaning), 0.46 (denotational layer)
- `Once.Verified.Behavior` doc comment — to be updated from "within `n` steps" to
  "first `n` effectful events"

## D059: Source Meaning Is the Denotational `evalᴰ`; `SS.eval` Is the Load-Bearing Cross-Check

**Date**: 2026-06-14
**Status**: Accepted; **updates D057** (which set `⟦src⟧ := SS.eval`)
**Implements**: Plan 0.46 (the role-inverted rewrite)

### Context — the meter, rooted in `apply`

Two source-level trace semantics now exist:
- **`evalᴰ`** (`Once.Verified.DenotTrace`) — the *compositional, monadic,
  denotational* trace. Indexed by **observation depth** (Cata emits its full
  finite trace; only `Ana` consumes the depth). `apply` is **fuel-free**:
  `⟦apply⟧(clo,a) = clo a`, the monadic arrow carries the trace.
- **`SS.eval`** (`Once.Verified.SourceSemantics`) — the *untyped, operational*
  reference (D057). Indexed by **step-fuel**, *because* untyped-λ `apply` (running
  a closure body) is non-structural and needs fuel for Agda totality.

So the depth-vs-step meter mismatch is rooted in **`apply`**: `evalᴰ` pays no fuel
for it, `SS.eval` must. The two are incommensurable as a same-`n` equality.

### Decision

- **`⟦src⟧ := evalᴰ`** — the apex source meaning is the denotational, depth-indexed
  `evalᴰ`. This makes the apex `exec n ≡ ⟦src⟧ n` **commensurable** (both at the
  machine's/source's shared observation depth, via `traces-agree`), and it is the
  **compositional** meaning needed to *reason about Once programs* (`⟦g∘f⟧ᴰ =
  ⟦g⟧ᴰ ∘ₖ ⟦f⟧ᴰ`; equational theory, Plan 0.46 M6). `SS.eval`, being an operational
  interpreter, is *not* compositional and cannot serve program reasoning.
- **`SS.eval` is a SEPARATELY-REQUIRED cross-check** (`#10`/`elaborate-preserves-
  trace`: `SS.eval ≡ evalᴰ`), **not** the apex's definitional meaning.

### Why load-bearing is preserved (the invariant)

D057's purpose — keep the elaborator load-bearing by anchoring at a reference
*independent of `elaborate`* — is preserved: `evalᴰ` is elaborator-dependent (it
is the IR's meaning), but a meaning-changing elaborator bug moves `evalᴰ` *and*
the machine together (so `exec ≡ evalᴰ` survives) while **breaking
`SS.eval ≡ evalᴰ`** (`SS.eval` is independent, untyped, pre-elaborate). So the bug
is caught — **provided `#10` remains a REQUIRED component of the grand theorem.**
That is the standing invariant: dropping `#10` from the required set silently
loses load-bearing. (`SS.eval` thus keeps its D057 role as the independent anchor;
only its *position* changes — cross-check, not apex meaning.)

### Consequences

- `Once.Verified.SourceTrace.⟦_⟧`/`sourceTrace` flips from `SS.runTrace` to
  `evalᴰ`-based (`⟦ moduleToIR m ⟧IR`); the apex `correct : exec n ≡ evalᴰ n`
  reaches `⟦src⟧ = evalᴰ` directly (commensurable; no `#10` in the *meter* chain).
- **`#10` is NOT a standalone/floating lemma — it is a REQUIRED CONJUNCT of the
  grand theorem.** The claimed correctness is `correct × elaborate-faithful`
  (`exec ≡ evalᴰ` AND `evalᴰ ≡ SS.eval`), which together yield `exec ≡ SS.eval`
  (the truly-independent claim). Dropping `#10` must break the stated correctness
  — otherwise load-bearing is silently lost (the D057 failure mode). It is
  separate from the *meter chain* only to confine the cross-meter awkwardness to
  `#10`; it is structurally required.
- `#10` is a **cross-meter** statement (`evalᴰ`-depth ↔ `SS.eval`-step), proven as
  a source-side simulation — structurally like the machine `traces-agree`/`flat-sim`,
  but implementation-independent (no codegen). The meter on each side is an
  internal totality device; the observable is the effectful-SigOp event sequence.

### See Also

- D057 (independent source reference — role updated), D058 (event/observation-depth
  observable), Plan 0.46 (denotational `evalᴰ` as the observable + reasoning layer)

## D060: One Denotational Meaning (Surface + IR); `SS.eval` Retired; Value Model at the Machine `Word`

**Date**: 2026-06-17
**Status**: Accepted
**Supersedes**: D059 (retires the `SS.eval` cross-check; keeps its denotational-meaning core)
**Updates**: D057 (the source reference is no longer `SS.eval`); D058 (observation-depth observable retained)
**Implements**: Plan 0.46 / OCP-0006.2 (branch `clean-semantics`)

### Context

Once *is* CCC + structured recursion with an effect-carrying arrow, so a program *is* a
morphism and has exactly **one** mathematical meaning. The tree had accumulated ~10
overlapping semantics joined by drift-prone bridges; D059 codified one — keeping `SS.eval`
(untyped, fuel-bounded) as a "load-bearing cross-check" against `evalᴰ` via `#10`
(`SS.eval ≡ evalᴰ`). That coexistence **is** the island problem: two semantics that can
drift, joined by a bridge that papers over the drift — and `SS.eval`'s fuel re-admits the
general recursion OCP-0003 removed.

### Decision

The semantics is **five objects and one theorem**:
1. **Model** — `Semantics.Core : CCC+SR → Set`, instantiated at the **machine `Word`**
   (signed modular per D054; total division per D055; width threaded from the architecture,
   never hard-coded — reuse `Once.Word`/`Width bits`). Not ℤ, not unbounded ℕ.
2. **Meaning** — `⟦_⟧ : CCC+SR → T` (observation monad, D058); value from the Model, trace
   from `emit`. ONE meaning, two presentations: `⟦_⟧ˢ` over the typed surface `Expr` (the
   programmer's meaning) and `⟦_⟧ᴰ` over IR (the compiler's), proven equal by
   `faithful : ⟦elab e⟧ᴰ ≡ ⟦e⟧ˢ`.
3. **Machine** — `exec` (abstract machine → targets).
4. **Adequacy** — the apex: `machine-trace (compile src) ≡ projTrace ⟦src⟧ˢ`.

**`SS.eval` is deleted**, not repositioned. The `CompSim`/`ProdSim`/`prod-bridge`/`AnaTrace`
scaffolding and the **ℤ value model** (`Semantics.IR` / `eval′` / `SigOpInfo.semI`) go with it.

### Why load-bearing survives without `SS.eval` (the crux — answers D059's worry)

D059 kept `SS.eval` to catch a buggy elaborator via an *independent, pre-`elaborate`*
reference. That job is done by two properties, **neither a trace cross-check**:
- **Soundness (output well-typed):** intrinsic typing. `checkElab : RawExpr → Maybe (typed
  Expr Γ Ψ A)` *cannot* emit an ill-typed term — Agda rejects it by construction.
- **Faithfulness (output is the *right* term for the source):** the **syntactic `erase`
  round-trip** `erase (checkElab raw) ≡ raw`. A well-typed-but-wrong elaboration breaks it.
  Syntactic, fuel-free, trace-independent.

And surface→IR `elaborate` stays load-bearing by **`faithful`** (`⟦elaborate e⟧ᴰ ≡ ⟦e⟧ˢ`),
because `⟦_⟧ˢ` is defined *directly* on the surface, independent of `elaborate` — so a
meaning-changing elaboration breaks `faithful`. `SS.eval` was a redundant *third* mechanism;
removing it loses no coverage.

### Consequences

- D059's standing invariant ("`#10` is a required conjunct or load-bearing is silently
  lost") is **void** — there is no `#10` and no `SS.eval`. Load-bearing = intrinsic typing +
  `erase` round-trip + `faithful`.
- Value model migrates ℤ → `Word`. **A rule true in ℤ but false under wrap is unsound on
  hardware** — surface it as an explicit `postulate` tagged *unsound + the precise wrap case*
  (a visible bug backlog), never hidden behind the ℤ instantiation. (The D054 straddle,
  closed.)
- Process (branch `clean-semantics`, Plan 0.46): top-down, layer by layer (Model → Meaning →
  Machine → Adequacy); **delete conflicts, don't bridge them**; scaffold downstream breaks as
  downward-pointing postulates to bound the red; never descend a layer until it is
  postulate-free among itself.

### See Also

- D059 (superseded — `SS.eval` cross-check retired), D057/D058 (source-reference role
  updated; observation depth retained), D054 (`Int` = signed modular `Word`), D055 (total
  division), Plan 0.46 + `plans/0.46-HANDOFF.md`.

## D061: A SigOp's Contract Comes From Its Interpretation (Off-Line, All Equal); the Core Is Interpretation-Agnostic

**Date**: 2026-06-17
**Status**: Accepted
**Implements**: Plan 0.38 (`0.38-core`) + Plan 0.11 (the SigOp slice); branch `clean-semantics`
**Triggered by**: D060's `faithful` proof — its last obligation `build-pure` is false while a
SigOp's effect is guessed by a hardcoded `classify-name` string-match.

### Context

A `SigOp` is just a morphism `A → B` that escapes CCC structure but **not soundness**: it
carries a contract (machine semantics `semM` + observable `EffectShape` + `impl ⊨ semM`) its
producer must discharge. Today the external contract is laundered: `classify-name {Unit}
"linux.exit" = Halts` (effect from a **string**, decoupled from the type) plus a
`generic-semM : String → …` postulate materialise a `SigOpInfo` for *any* name at *any* type.
This (a) bakes a specific interpretation (Linux) into the compiler core, (b) lets a contractless
SigOp be minted (the Plan 0.36 effectful-cata bug), and (c) makes `build-pure` false — a
non-arrow `sigOp {Unit} "linux.exit"` "emits" at build (the third mask of the parallel-truth
disease, after the ℤ-model and the parallel `eval` value-model).

### Decision

**A SigOp's contract is supplied by its *interpretation*, and the verified core is parameterized
over an abstract interpretation — no concrete interpretation is baked in.**

1. **Two compile times.** (i) *Once program-compile-time* — the extracted `once` binary; **no
   Agda in it**; it does not know which interpretation will be linked; it sees only declared
   signatures + effects and **cannot check contract proofs**. (ii) *Interpretation-verification-
   time* — **off-line**, in Agda, where each SigOp's contract is discharged.
2. **All interpretations are equal — none is special, NOT Linux.** There is no "built-in
   interpretation verified when we build Once." Linux, seL4, and a user's own interpretation are
   all verified off-line by their authors, identically.
3. **Discharge is proof-OR-postulate, per (SigOp × target)** — NOT "external ⟹ axiom". An
   unverified kernel (Linux) **postulates** its contracts; a verified one (seL4) can **prove**
   them, connected to its refinement theorems; internal producers (the arith compiler) prove
   theirs. The `TrustedBase` shrinks automatically as targets become verified.
4. **The core (`elaborate`/`⟦_⟧ˢ`/`⟦_⟧ᴰ`/`faithful`/compile-correctness) is parameterized over an
   abstract `Interpretation`** (per-name `SigOpInfo` + a well-formedness condition: a non-arrow /
   bare-value op is `Pure`, since effects are deferred onto arrows). `classify-name` /
   `generic-info` / `generic-semM` are deleted — they were a hardcoded stand-in for that
   parameter. This is the SigOp slice of Plan 0.11's `TrustedBase` parameterization.

### Consequences

> **Update 2026-06-20:** `build-pure` has since been **retired** — the clean-semantics
> `cata`/`ana` closure-bridge (`cata-body`/`ana-body`) removed the need for it, so `faithful`
> is already total and postulate-free *without* the abstract-interpretation WF. The decision
> below stands, but its *forcing function* is gone: M0 now proceeds for **honesty** (deleting
> the `String → SigOpInfo` catch-all so a SigOp's effect/value come from a contract), not to
> unblock `build-pure`. Also clarified: the **compiler never reads `semM`** — only `name` +
> `effect` (the optimizer's pure-vs-eff, ≈ `π`); `semM` is consumed solely by `eval` and the
> off-line proofs, so sourcing it from the contract is a meaning-layer (not compiler) fix.

- `build-pure` (and a postulate-free meaning layer / `faithful`) is provable **relative to a
  well-formed abstract interpretation** — nothing emits at build, so the IR's per-fold-layer
  algebra rebuild matches the denotational build-once.
- A contractless or mis-typed external SigOp becomes **unconstructible** (no `String → SigOpInfo`
  catch-all) — closing the Plan 0.36 laundering class, not just making it visible.
- Concrete interpretation instances (Linux, seL4) and **dog-fooding** a user-proven interpretation
  (the acceptance test that a third party can author + verify one) are off-line, equal, and
  **deferred** — the core must not import any of them.

### See Also

- Plan 0.38 (per-producer SigOp contracts; `0.38-core` = M0), Plan 0.11 (parameterized
  `TrustedBase` / `--safe`), D060 (the `faithful` proof that triggered this), D025-era
  `EffectShape` contract, D047 (`SigOp` rename). Decision-log D-entry on primitives-are-external
  (2025-12-08) is the original "interpretations live outside the compiler".

## D062: Total+Productive by Construction — No Unwitnessed Recursion; the Recursive-Coalgebra Certificate

**Date**: 2026-06-18
**Status**: Accepted
**Implements**: branch `clean-semantics` (the meaning-layer TP cleanup); supersedes the
OCP-0003 "input is `μG` ⟹ well-founded" assumption.
**Triggered by**: trying to *prove* termination while retiring the `TERMINATING` pragmas — the
attempt exposed that the meaning's `Hylo`/`Fuse` assert totality by fiat for coalgebras that can
diverge.

### Context

Once is meant to be **total + productive (TP)**: every `μ`-recursion terminates, every
`ν`-production is productive, no `⊥`. The denotational layer (`⟦_⟧ˢ`/`⟦_⟧ᴰ`/`faithful`) is
postulate-free *except* for `TERMINATING` pragmas it inherits from `fuseW` (used by
`sem-fuse`/`sem-hylo`) and the coinductive `sem-ana`. A `TERMINATING` pragma is a
**postulate-in-disguise**: it asserts termination the checker can't see. The key finding: a
hylomorphism `hylo = cata ∘ ana` is total **iff its coalgebra is a recursive (well-founded)
coalgebra**; `cata` (consumes finite `μ`) and `ana` (productive into `ν`) being individually TP
does **not** transfer through the composition, because it crosses the `μ`/`ν` boundary via a
coercion that is only total when the unfold bottoms out. OCP-0003 anchored `Hylo`/`Fuse` at a
`μG` *input* believing that ensured termination — **false**: a coalgebra that synthesizes new
`μG` via `In` at a recursive position grows without bound despite the `μG` input. That false
assumption is the source of the dishonest pragma.

### Decision

**TP is a type-level invariant carried by the recursion combinators; there is no
unwitnessed-recursion escape hatch. The `TERMINATING` pragma is removed and replaced by an
explicit recursive-coalgebra certificate.**

1. **The schemes, by role.** `cata`/`para` consume `μ` (structural, total-free); `ana` produces
   `ν` (productive corecursion, total-free); `hylo` generates-then-consumes. `para` is a derived
   `cata`; `fuse ≡ hylo` (Lambek's `In`/`out-μ` iso — same scheme, coalgebra-packaging difference
   only, **not** two principles). So the meaning has **one** generate-then-consume scheme; `fuse`
   is its destructed-layer face.
2. **The certificate ladder.** Totality of `hylo` requires a *recursive (well-founded) coalgebra*
   (Capretta–Uustalu–Vene; Adámek–Milius–Moss — for our polynomial functors *recursive* =
   *well-founded*). Three rungs by how the certificate is discharged: `cata`/`para`/`ana` — free;
   `hyloS` — trivial/structural certificate, auto-derived (the deforestation/natural case);
   `hyloW` — a programmer-supplied **measure + descent** witness (the measured case, e.g.
   quicksort). `cata` = `hylo` at `out-μ` with the always-derivable certificate.
3. **`μG`-anchoring is NOT a termination certificate** (corrects OCP-0003). The real certificate
   is *subterm-preservation* (natural ⟹ structural ⟹ `hyloS`) or a *measure* (`hyloW`). `In` at a
   recursive position is the unique well-foundedness breaker, and `In` is the algebra structure
   map — **not** a natural transformation — so the natural fragment excludes exactly it.
4. **`hylo`'s type carries the certificate as an inferred argument:**
   `hylo alg c {{Recursive c}} → X → A`, where `Recursive c` = a measure into a well-founded order
   + a per-recursive-position descent proof (or the `Acc` form). Auto-resolved when structural,
   supplied as a measure when measured.

### Consequences

- **Surface vocabulary** is `cata`/`ana`/`para`/`hylo` — **one** `hylo` keyword; the
  structural/well-founded (S/W) grading lives entirely internally (`hyloS`/`hyloW`). The Once
  programmer sees `hylo`, and supplies a measure only for genuine divide-and-conquer.
- **The elaborator fills the certificate** via a *syntactic* natural-fragment check (the coalgebra
  IR is `In`-free at recursive positions) — a decidable structural traversal, **not** a general
  termination prover — whose soundness (natural ⟹ recursive ⟹ total) is proven once, so it adds
  **no postulate**. A non-structural coalgebra is rejected ("needs a measure") until Phase 2.
- **Once syntax is unchanged now:** `hylo`/`fuse` are elaborator/optimizer-produced, so the
  certificate is internal; a measure annotation is a Phase-2 addition only when a real program
  needs measured recursion.
- **Deforestation stays an optimization:** a verified pass *transports* the source's certificate
  (never invents one); `fuse` is re-added to the IR only as a refinement proven equal to `hylo`
  (denotation = `hylo`, codegen = fused loop, correctness = the deforestation law).
- **`para`/`fuse` are derived, not primitive**, so the IR's five-scheme zoo collapses toward
  `cata`/`ana`/`hylo`. Internal `fuseS`/`fuseW` (SFunctor/Writer *carrier* axis) are renamed so the
  S/W letters mean *structural/well-founded* (certificate axis) consistently.
- **TP becomes a theorem, not a checker pass:** once the `TERMINATING`s are gone and every
  recursion justifies itself in its type, "the denotational layer is postulate-free" *is* a proof
  that Once is total+productive (an OCP-6-class invariant).

### Phasing

- **Phase 1 (now):** structural-only. Remove the `TERMINATING`s; route `Hylo`/`Fuse` through the
  certificate-graded `hylo` (natural fragment ⟹ `cata`-derived `hyloS`); elaborator auto-fills the
  structural certificate and rejects non-structural coalgebras. Zero programmer burden.
- **Phase 2 (deferred):** measured `hyloW` — surface measure annotation + descent verification —
  added only when a program needs divide-and-conquer that rebuilds (quicksort/mergesort).

### See Also

- D060 (one denotational meaning; the postulate-free target this completes), D058 (productivity,
  not termination — `ana` is the reactive loop), the recursion-scheme reify work
  (`reify-recursion-for-foetus-perf`). Literature: Capretta–Uustalu–Vene *Recursive coalgebras
  from comonads*; Adámek–Milius–Moss–Sousa *On Well-Founded and Recursive Coalgebras* (FoSSaCS
  2020); Bove–Capretta (well-founded recursion); Meijer–Fokkinga–Paterson (the morphism zoo).

## D063: The Morphism Realm `⊢ᵐ` — the CCC Trichotomy in the Typing Judgment

**Date**: 2026-06-24
**Status**: Accepted (design); implementation in Plan 0.49 Phase 2 (route 2)
**Completes**: D056 (one morphism realm for composition) at the level of the *declarative
judgment* and the *denotation*, not just the elaborator algorithm.

### Context

Plan 0.49's `realize` (the elaborator-free reference elaboration `⊢ᶜ → SExpr`, whose
denotation `SD.⟦realize D⟧ˢ` is the source meaning) must be a **total** function over the
typing judgment. Writing it exposed a latent inconsistency that predates the plan:

- The judgment's `t-case-copair-check` / `t-compose-check` are **grade-polymorphic** and take
  **arbitrary check derivations** as arms (they model the *closure-realm* form: their `Ψ` is
  `(0 +ᵘ Many*Ψ₁) +ᵘ Many*Ψ₂`).
- But `checkElab` for the **eff** grade *only fuses* (`extract-morph-eff`) and **fails** with no
  fallback (`Elaborate.agda:1301`, `:1354`) when an arm is not point-free.
- So the **spec (judgment) is strictly more permissive than the elaborator**, and the proof layer
  bridges the gap with two postulates (`case-copair-eff-complete`, `compose-eff-complete`,
  `Completeness.agda:911`) labelled "PROVABLE" that are in fact **false** (counterexample: an arm
  that is a bound variable of eff-arrow type — derivable via `t-embed (t-var-local …)`, rejected
  by `checkElab`).

`realize` cannot be both total and elaborator-free on these rules as the judgment stands, *and*
the inconsistency cannot be fixed on the proof side: there is no eff-closure surface term to fall
back to (eff exponential elements you compose are not a coherent thing), and adding one is exactly
the `effCompose` parallel-structure anti-pattern D056/D046 forbid. **The spec must move.**

### Decision

Reflect the **CCC trichotomy** directly in the judgment. A source expression denotes one of three
things, and each gets its own family + a lift into `⊢ᶜ`:

| realm | categorical meaning | judgment | lift into `⊢ᶜ` |
|---|---|---|---|
| **value** | global element `1 → A` | `⊢ᵍ` (exists) | `t-value-lift` (exists) |
| **morphism** | arrow `A → B` | **`⊢ᵐ` (new)** | **`t-morph-lift` (new)** |
| **closure** | exponential element `Γ → Bᴬ` | `t-lam` (exists) | — (it *is* a `⊢ᶜ` rule) |

`⊢ᵐ` (grade-free — the IR is grade-erased per D046; closed ⇒ no usage index, like `⊢ᵍ`) is
**structural over the categorical combinators** (`m-compose`/`m-case`/`m-pair`/`m-curry`/`m-cata`,
recursing on `⊢ᵐ`) with **extensional leaves** (`m-id`/`m-fst`/… point-free primitives; `m-const`
reusing `⊢ᵍ`; `m-named` a plain morphism ref; `m-lam` a *closed* lambda read as its body in the
one-variable context). `realize-morph : ⊢ᵐ e ∶ A ⇒ B → IR A B` is total by structural recursion,
each clause the **direct** categorical IR (`IR.∘`, `IR.case`, `IR.⟨_,_⟩`, `IR.Cata`, …).
`t-morph-lift : ⊢ᵐ e ∶ A ⇒ B → ⊢ᶜ e ∶ (A ⇒[Many π] B) ⨾ 0` collapses the whole combinator zoo
(`t-id-check`…`t-compose-check`…`t-cata-check`) into one bridge, the mirror of `t-value-lift`.

The categorical combinators take `⊢ᵐ` arms **uniformly across purity**. A *closure* (`t-lam`,
context-capturing) is structurally **not** a `⊢ᵐ`, so it can never be a `compose`/`case` arm — the
eff problem evaporates at its root, and the two false completeness postulates become provable
(arms are now morphisms by construction) and are deleted.

### Rationale

- **Categorical, not bottom-up.** `elaborate : Expr Γ Ψ A → IR ⟦Γ⟧ᶜ A` already says every in-context
  term is a morphism `⟦Γ⟧ → A`; the morphism realm is exactly its **closed** sub-fragment
  (`1 → Bᴬ ≅ A → B`). Composition is the category's `∘` acting on morphisms; the closure-realm
  `λx.f(g x)` is the *internal-hom* composition masquerading as it (the D043 original sin, made a
  soundness issue by Plan 0.39). `curry`/`apply` remain the exponential structure for genuine
  higher-order values — not a parallel composition realm.
- **Forces the correct proof obligations.** The meaning routes through `realize-morph`'s direct
  categorical IR, so `correct`'s soundness conjunct forces *codegen* to implement `∘` as
  composition, and `realize-agrees` forces *`checkElab`* to denote the same `IR.∘` — one clause per
  combinator, each literally the categorical law, with no closure escape hatch to make it
  tautological. (An extensional `⊢ᵐ := closed ⊢ᶜ` + uncurry would type-check but route compose back
  through the closure form, making the obligation say nothing about `∘` — rejected for that reason.)
- **Mirror of `⊢ᵍ`** (D018/D041): the value realm already did exactly this ("extractable by
  construction"). `⊢ᵐ` is the dual; `realize-morph` is the dual of `realize-global`.

### Consequences

- New `⊢ᵐ` family + `realize-morph`; `t-morph-lift` added to `⊢ᶜ`; the combinator check rules
  (`t-id-check`…`t-compose-check`/`t-case-copair-check`/`t-pair-check`/`t-cata-check`/the bare
  `t-{inl,inr,initial,arr}-check`) are subsumed and removed. Blast radius: `Judgment.agda`,
  `Soundness.agda`, `Completeness.agda` (the two false postulates **deleted**, now provable),
  `Elaborate.agda` (the eff `compose`/`case` clauses route through one grade-poly path), and the
  saturated `t-{inl,inr}-app-check` likely collapse into `⊢ᵍ` (`g-inl`/`g-inr`) — confirm
  separately.
- The Once *programmer* loses nothing buildable today: the only programs leaving the spec are eff
  `compose`/`case` with capturing-closure arms, which already do not compile. The principled
  restriction (categorically honest): a capturing closure is not a `compose`/`case` arm — reference
  a named morphism or use `apply`.
- **Honest residue:** `m-lam`/`m-named`/`m-const` are forced extensionally (no law exists for an
  opaque function); the combinators are forced as laws. First-order *and* higher-order closed
  lambdas are handled uniformly by `m-lam` (body-in-one-variable-context); the higher-order case's
  internal exponential use lives inside the body's IR, not in a special constructor.
- Supersedes Plan 0.49's "fallback `app (app spec*) f g`" instruction for `realize`'s
  compose/case/pair clauses.

### See Also

- D056 (one morphism realm — this completes it in the judgment+denotation), D046 (grade-erased
  arrow), D018/D041 (`⊢ᵍ` value realm — the mirror), D044/D045 (classifier route), D053 (closures =
  exponentials, calling convention is downstream), Plan 0.49 (route 2, the implementation),
  Plan 0.40 (the elaborator-side one-realm migration this aligns with).

## D064: Named Definitions Are Morphisms — Direct-Call ABI

**Date**: 2026-06-24
**Status**: Accepted (design); implementation DEFERRED (own milestone, sequenced after the D063 collapse)
**Corrects**: D019 (sigop/closure split) + D053 (closure calling convention) — the *universal*
closure-returner ABI for user-defined functions.

### Context

A top-level definition `f : A → B` (`f x = body`) compiles to `once_f` under a
**closure-returning** ABI (D019/D053): `once_f()` returns a closure pointer (an element of the
exponential object `Bᴬ`), and call sites go through `apply (closure "f") arg`. This represents
*every* definition as an exponential element `1 → Bᴬ`, never as the morphism `A → B`.

### Decision (from principle)

- A top-level definition `f : A → B` **is a morphism `A → B`** — always, even when `B` is itself
  an exponential (`f : A → (C ⇒ D)` is a morphism *into* an exponential object). A definition is
  *never* inherently an exponential element.
- An **exponential element** (a value of type `Bᴬ`, i.e. `1 → Bᴬ`) arises **only when a morphism
  is used as data** — that is `curry`, a property of the **use site** (passing/storing the
  function), not the definition.
- Therefore: **a definition compiles to a morphism** (a direct symbol / `IR.SigOp`-style arrow,
  `once_f(a : A) : B`, direct call). `curry`/closure is emitted **explicitly and only** at genuine
  value-introduction sites.

### Rationale

The universal closure-returner conflates `Hom(A,B)` with `Hom(1, Bᴬ)`. These are isomorphic (the
exponential adjunction), so the current ABI is **not unsound** — but it is the **wrong primitive**:
it forces every function into the exponential realm by default. This is the *same* morphism/
exponential conflation already removed elsewhere —
- **D056**: `compose` is `∘` on morphisms, not internal-hom composition on closures;
- **D063**: the typing judgment splits `⊢ᵐ` (morphisms) from `t-lam` (closures);
— left standing at the **codegen/ABI** level. It was justified only by *implementation uniformity*
of `apply` (one path for "apply a closure value" and "call a named function"), which is a
convenience, not a language principle. D063 is the **enabler**: with the type system now
distinguishing morphisms from closures, a call site can tell "call a named morphism" from "apply a
closure value," so the direct-morphism ABI is well-defined where it previously was not.

### Consequences

- **NOT a short change.** It touches: the elaborator (`sigOp`/`closure` at arrow type → direct
  `IR.SigOp` morphism instead of `curry(SigOp ∘ snd)`; `curry` only at value-use), the calling
  convention / codegen backends (D053 — `once_f` becomes the arrow, call sites become direct
  calls), use-site desugaring (`f arg` → direct call, not `apply (closure "f") arg`), the MAlonzo
  bridge NameIds, and crucially the **closure/apply verification machinery** (the `Apply*`/`Curry*`
  WF proofs, closure-location/`valid-closure-wf`, DirectSimulation/Corresponds) — a verified-
  codegen milestone in its own right, comparable to the `Apply`/`Curry` work.
- **Separable from Plan 0.49.** The *spec* (`realize-morph`) already uses the principled morphism
  form `m-named ↦ IR.SigOp`; while the closure ABI still stands, the difference is absorbed by
  `realize-agrees` (morphism ≡ uncurried-closure, true by the β/uncurry law). So the spec is
  principled regardless of the ABI; the ABI change just turns that bridge lemma trivial.
- Subsumes Plan 0.40 residual-3 ("a first-order function should not become a `curry`-closure") —
  that residual is this decision at the lambda level.

### Sequencing

Recorded now; **implemented as its own milestone after the D063 collapse + the Plan 0.49 `realize`
work land** (a dedicated plan, e.g. `0.50-named-defs-are-morphisms`). It is not a blocker for
`realize`/`realize-agrees`, so it does not interrupt the current work.

### See Also

- D063 (the `⊢ᵐ`/`t-lam` distinction that enables this), D056 (one morphism realm), D019/D053 (the
  decisions this corrects), Plan 0.40 residual-3 (first-order-lambda-as-morphism, subsumed),
  Plan 0.49 (the `realize` work this is kept separable from).

## D065: Bare Morphisms Are Grade-Free — `checkElab` Accepts Any Purity; `arr` Is Optional

**Date**: 2026-06-24
**Status**: Accepted; implementation in Plan 0.49 (morph-complete discharge)
**Completes**: D056/D063 (grade-free morphism realm) at the *elaborator* level.

### Context

D063's `⊢ᵐ` morphism realm is grade-free (the IR is grade-erased, D046), and `t-morph-lift`
wraps a morphism into `⊢ᶜ` at ANY purity `π`. But `checkElab`'s bare point-free builtins
(`id`/`fst`/`snd`/`terminal`/`initial`/`inl`/`inr`/bare `arr`) are accepted only at **pure**
arrows (`Elaborate.agda` `bbc-*-failure-aux` matched `mk-kind Many pure`, with `mk-kind _ eff →
failure`). So `t-morph-lift {eff} (m-id …)` is a valid `⊢ᶜ` derivation that `checkElab` rejects —
making `morph-complete` (completeness) **false** at `π = eff` for bare builtins. (Caught by
*attempting* the `morph-complete` discharge — the value of discharging vs. postulating.)

### Decision

A bare morphism is usable at **any** grade without an explicit lift. Broaden `checkElab`'s
bare-builtin clauses from `mk-kind Many pure` to `mk-kind Many π` (any purity), emitting the same
grade-polymorphic `lift-morphism IR.X`. `checkElab` thus agrees with the grade-free `⊢ᵐ`;
`morph-complete` becomes provable.

`arr : (A → B) → Eff A B` (Hughes' arrow; runtime identity) is **retained but OPTIONAL** — it
still lifts a *pure function value* to eff, but bare point-free morphisms no longer *need* it
(`id` is directly usable at `T ⇒[eff] T`). The pure→eff boundary is no longer required to be
syntactically marked for morphisms (it is grade-erased anyway).

### Rationale

Grade-free morphisms (D046/D056) — a morphism is the same arrow at any grade; the IR is
grade-erased. Requiring `arr` on a bare morphism was an artifact of the pure-only `checkElab`
clauses, not a semantic necessity. The alternative (restrict `t-morph-lift`'s grade per-leaf)
re-fragments the eff `compose`/`case` D056 just unified, so it's rejected.

### Consequences

- `checkElab` accepts `id`/`fst`/… (and bare `arr`) at eff-arrows (small language broadening —
  strictly more programs accepted, all semantically valid). Touches the `bbc-*` clauses + re-verify.
- `morph-complete` (Completeness) becomes a TRUE, dischargeable theorem (was false at eff).
- Effect visibility: pure→eff for a *morphism* is no longer syntactically marked. (Genuine
  effects still come from SigOps; `arr` stays available for lifting pure *function values*.)
- **`arr` is redundant *as a morphism* — bare unapplied `arr` is dropped.** Reasoning: `arr`'s
  only job is the grade flip `pure → eff`, which is free for morphisms (grade-erased IR, D046 +
  grade-free D065) — so for a morphism there is nothing to lift (`id : T ⇒[eff] T` directly).
  `arr` *is* genuine for **closures** (capturing pure function *values*, introduced by `t-lam`
  at a pure arrow): `arr f` lifts those to eff. So the morphism-realm leaf `m-arr-bare` (and the
  bare-`arr` `checkElab` clause + `checkElab-fallback-RVar-arr`) are removed — bare unapplied
  `arr` becomes a type error — while applied `arr f` (the closure lift, `t-arr-app-check`) is
  retained. Surface-only, no expressiveness loss (you write `arr f`, or a bare morphism directly
  at eff). Trajectory: D032 (`arr` lifts; effects a separate type) → D046 (effects = arrow grade)
  → D065 (`arr`-on-morphisms redundant).

### See Also

- D063 (`⊢ᵐ`), D056 (one morphism realm), D046 (grade-erased arrow), D032 (`arr`),
  Plan 0.49 (`morph-complete`).

## D066: The Morphism Realm Is Grade-Indexed (Pure Grade-Poly, Effectful Grade-Fixed)

**Date**: 2026-06-24
**Status**: Accepted; implementation in Plan 0.49 (`morph-complete` discharge)
**Refines**: D065 — "bare morphisms are grade-free" holds **only for pure morphisms**.

### Context

Proving `morph-complete` revealed that a *grade-free* `⊢ᵐ` with a `∀π` `t-morph-lift` is both
**incomplete and unsound** for the grade-fixed leaves:
- `m-named` carries an import's fixed kind `A ⇒[k] B`, but `t-morph-lift {π}` wraps at any `π`. A
  **pure import at eff** is `checkElab`-rejected (completeness gap); an **eff import at pure** is
  **unsound** — it tags an effectful SigOp as pure, which the meaning/optimizer treat as
  effect-free (Plan 0.39: the optimizer drops effectful SigOps). `eff → pure` drops effects.
- Same for `m-const` (values; `t-value-lift` is pure-only), `m-lam`, `m-pair`, `m-curry`
  (`checkElab` paths are pure-fixed).

D065 is right for *pure* morphisms (the point-free builtins have no effect → usable at any grade),
but the morphism realm has a **grade structure**: pure morphisms are grade-poly, effectful ones are
grade-fixed (D046 masquerade + Plan 0.39 soundness).

### Decision

`⊢ᵐ` is **grade-indexed**: `_⊢ᵐ_∶_⇨[ π ]_` (purity `π` on the morphism). `t-morph-lift` lifts to
`A ⇒[mk-kind Many π] B` using `⊢ᵐ`'s own `π` (NOT `∀π`). Per-constructor grade:
- **grade-poly** (`π` free): `m-id`/`m-fst`/`m-snd`/`m-terminal`/`m-initial`/`m-inl`/`m-inr`
  (pure point-free builtins — usable at any grade, D065).
- **grade-poly via arms** (single shared `π`): `m-compose`, `m-case`, `m-cata`.
- **pure-fixed** (`π = pure`): `m-pair`, `m-curry`, `m-const`, `m-lam` (`checkElab` paths pure-only).
- **import-grade** (`π` from the import's kind): `m-named`.

The IR stays grade-erased (`realize-morph` ignores `π`); `π` lives only in the surface type, so this
matches D046. `morph-complete` becomes provable (each morphism elaborates at exactly its grade) and
the eff→pure unsoundness is excluded by construction.

### Consequences

- `⊢ᵐ`, `t-morph-lift`, the `m-*` constructors, `extractMorphWitness`, `realize-morph`'s signature,
  and the Elaborate witnesses thread the `π` index. The pure point-free builtins stay grade-poly
  (D065's broadening = the free `π`).
- Effectful morphisms can no longer be silently used at pure (soundness restored).

### See Also

- D065 (grade-free — refined here to pure-only), D046 (grade-erased IR / masquerade), D056 (one
  realm), D063 (`⊢ᵐ`), Plan 0.39 (optimizer drops eff SigOps), Plan 0.49 (`morph-complete`).

## D067: `morph-complete` Discharged — 12/15 by Induction; 3 Scoped Postulates

### Context

D063–D066 made `morph-complete` (Plan 0.49 row-3 forcing) a TRUE, grade-correct postulate. This
discharges it: `Once.TypeCheck.MorphComplete.morph-elab : ⊢ᵐ e ∶ A⇨[π]B → StrongElab` proves the
strong form (`checkElabV` reduces to a success whose result expr `E` and witness `W` both extract —
`extract-morph-eff E ≡ just (m,refl)`, `extractMorphWitness W ≡ just mᵐ`), and `morph-complete` is
its `cong proj₁`. Completeness imports it; the blanket postulate is removed.

### Decision

**12/15 cases PROVEN**: 7 bare builtins (mirror `checkElab-fallback-RVar-*` lifted to `checkElabV`),
`m-pair`/`m-case`/`m-compose`/`m-curry`/`m-arr` (recurse on arms, rewrite their `checkElabV` +
extraction equations, `refl`). **3 SCOPED postulates** remain in `MorphComplete`:
- `m-const` — needs a STRONG `gd-complete` (the Completeness one is `checkElab`-weak, not the
  `checkElabV`-with-witness form). Mutual-with-Completeness.
- `m-cata` — needs a STRONG `check-complete` on the (`⊢ᶜ`) algebra. Mutual-with-Completeness.
- `m-named` — a **bare import elaborates to a CLOSURE** pre-Plan-0.50 (`sigOp x` → resolver →
  `curry(SigOp∘snd)`; `extract-morph-eff` rightly refuses `sigOp`, soundness). Only QUALIFIED
  externals (`RQualified` → `t-var-qualified` → `lift-morphism (IR.SigOp …)`) are morphisms today.
  **Discharged by Plan 0.50 milestone 1** (named refs become direct `IR.SigOp` morphisms).

Required refactors (feedback_with_abstraction — fight the definition, not the proof):
- `composeMid` → plain `composeMid-pick` (was a `with` blocking `rewrite`/`with` abstraction).
- `checkCompose` → `checkComposeGo` (explicit result + eq; drops `with … in`, which threaded
  `composeMid` into a non-abstractable position).
- `checkPair`/`checkCurry` → `extract-morph-eff` (they used the lift-morphism-only `extract-morph`,
  so they REJECTED `cata` arms — a genuine completeness fix, not just convenience).
- `extractMorphWitness`'s `t-arr-app-check` clause → plain `extractMorph-arr`.

### Consequences

- Frontend green through `Adequacy.ModuleComplete`. The CCC codegen apex (`EntryPointCCC`) has a
  PRE-EXISTING break (`RecCoreWF`: `NatTr G F` vs `IR …`, unrelated — imports no `TypeCheck`).
- Next (Plan 0.49 piece 3): `main-realize-agrees` ← `realize-agrees` (RealizeBridge, a denotational
  induction relating `checkElab`'s `se` to `realize` of its soundness witness) + `resolveExpr`-
  faithfulness. Then Plan 0.50, then prove `m-named`.

### See Also

- D063 (`⊢ᵐ`), D066 (grade-indexed), D064/Plan 0.50 (named-defs ABI — unblocks `m-named`), Plan 0.49
  (`realize` spec, the row-3 forcing).

## D068: Grade Is a Checked, Erased Refinement — pure→eff Is Subsumption, `arr` Retired

**Date**: 2026-06-30
**Status**: Accepted; implementation in Plan 0.52 (not started)
**Completes**: D065/D066 — the grade discipline taken to its endpoint, enabling OCP-0007.

### Context

`evalᴰ apply` is kind-polymorphic and `evalᴰ arr f = returnT f` (identity): the
grade is a PHANTOM IR index — present in the type, ignored by codegen (grade-erased
IR, D046; `realize-morph` ignores `π`, D066). D065 already dropped BARE `arr` (type
error) and made bare morphisms grade-free. What remains is APPLIED `arr f` — a pure
function VALUE lifted to an eff arrow (`t-arr-app-check`), a no-op coercion
(`⟦arr f⟧ = ⟦f⟧`). The question (raised while closing the `check-agreeV` RVar gap):
should the pure→eff boundary be a COERCION term (`arr`) or a SUBSUMPTION check?

### Decision

The grade (purity, later capabilities) is a **checked, runtime-erased typing
refinement**. pure→eff is **monotone subsumption** (`pure ⊑ eff`, a check on the
grade lattice), never a coercion term. `arr` is retired entirely (bare already gone
per D065; applied `arr f` replaced by subsumption in `checkElabV`). The grade stays
in the surface type (load-bearing for the effect/capability analysis), but is
adjusted by checking, not by inserting terms.

Subsumption is ONE-DIRECTIONAL: `pure ⊑ eff` sound; `eff ⊑ pure` UNSOUND (D066 — the
optimizer drops pure SigOps, so tagging an eff SigOp pure drops effects). That is
exactly OCP-0007 attenuation: authority only relaxes downward.

### Rationale

- **OCP-0007**: its core rule is "annotation is a CHECK, never a coercion"; effects
  compose with the same operators as pure code and the grade "rides along
  silently." A pure→eff coercion term (`arr`) contradicts this; monotone subsumption
  IS it. Retiring `arr` is a prerequisite for the capability-lattice generalization.
- **QTT / dependent types**: the kinds already carry `Zero/One/Many` — the `{0,1,ω}`
  semiring of Quantitative Type Theory (Idris 2 / Agda `--erasure`). QTT tracks
  resource/usage annotations in typing, adjusts them by CHECKING, and ERASES them at
  runtime — and QTT is a dependent type theory, the cleanest on-ramp to a dependent
  future. The purity/capability grade is another such annotation (a lattice). `arr`
  is the pure/eff analogue of an explicit `0→ω` coercion term, which QTT
  specifically avoids. So "check, not coercion" is the dependent-types-aligned path;
  keeping `arr` is the one move that fights it.
- **No expressiveness change**: `arr` is denotationally the identity, so retiring it
  removes zero behavior; subsumption expresses everything it did, with less ceremony.

### Consequences

- Deletes the `arr` IR constructor + codegen, the `arr'`/`ahv-arr` coercion-identity
  lemma, `m-arr`, and the bbc-`arr` machinery. New obligation — `pure ⊑ eff`
  subsumption is denotation-preserving — is trivial (`⟦_⟧` is grade-blind).
- Correctness spec stays grade-free (already is); grade soundness becomes a separate,
  smaller static-analysis property — the healthiest proof end-state.
- Optional follow-on (Plan 0.52 M2): erase the `mk-kind q π` index from the IR
  exponential OBJECT (codegen already ignores it), collapsing every
  `mk-kind Many/One/Zero × pure/eff` case-split across the agree/codegen proofs —
  PENDING verification that optimizer purity rides on SigOp contracts (D061), not
  arrow grades.
- Surface programs drop `arr f` (rare); re-extract MAlonzo.

### See Also

- D065 (bare `arr` dropped), D066 (grade-indexed `⊢ᵐ`; eff→pure unsound), D046
  (grade-erased IR), D032 (`arr` lifts), D061 (SigOp contract from interpretation),
  Plan 0.52 (implementation), Plan 0.39 (optimizer drops pure SigOps), OCP-0007
  (capability-graded effects), QTT (McBride/Atkey — quantity semiring, erasure).

## D069: Effect-Free Value Intros Are Grade-Poly — the Grade Is Real Only Where Effects Are Introduced

**Date**: 2026-06-30
**Status**: Accepted; implementation in Plan 0.52 M1
**Refines**: D066 (which fixed value-lift / `m-pair` / `m-curry` to pure).

### Context

D068's general `t-subsume` (`⊢ᶜ e ∶ A⇒[pure]B → ⊢ᶜ e ∶ A⇒[eff]B`) makes
`⊢ᶜ 42 ∶ (X⇒[eff]Int)` derivable (a constant used as an effectful function). But
`t-value-lift` (and `m-pair`/`m-curry`) were PURE-FIXED (D066), so `checkElab`
could not find that eff typing — a completeness gap. The same hits every
effect-free value intro (RInt-vlift, RPair-vlift, closed values via `checkG`).

### Decision

The grade is a FREE INDEX wherever no effect is introduced. Make the effect-free
value intros **grade-poly** (π free): a closed value / point-free combinator
inhabits `A ⇒[mk-kind Many π] B` at ANY π directly. `t-value-lift` (and the
pure-fixed `m-pair`/`m-curry`) gain a free `π`, extending the SAME pattern D065
gave the bare point-free morphisms. `t-subsume` then survives ONLY for the
genuinely-graded constructs: **lambdas** (grade determined by the body — a
pure-bodied lambda subsumes up; an eff-bodied one cannot be pure) and
**infer-embed** (a variable/application has a fixed inferred type).

### Meaning-preserving (does NOT change Once)

- **Denotations unchanged**: the grade is denotationally inert
  (`⟦arr' f⟧=⟦f⟧`, `evalᴰ`/`realize-morph` ignore the kind). `42 : X⇒[pure]Int`
  and `42 : X⇒[eff]Int` denote the same function.
- **Same programs well-typed**: `t-subsume` already admits `42 : eff`; this only
  changes which DERIVATION the elaborator finds (a grade-poly `t-value-lift`
  vs `t-subsume (t-value-lift …)`).
- **D066's load-bearing content intact**: the soundness barrier is **eff→pure
  forbidden** (an effectful SigOp must not masquerade as pure — the optimizer
  drops pure SigOps, Plan 0.39). D069 only grade-polys EFFECT-FREE intros for the
  **pure→eff** direction; it never makes an effectful construct grade-poly and
  never permits eff→pure. The invariant — the actual semantic guarantee — stays.

### Consequences

- Cleaner, smaller proofs: `subsume-complete`'s value cases become trivial (the
  eff value-lift succeeds directly), leaving `t-subsume` completeness to RLam +
  infer-embed only. The principle "the grade is real only where effects are
  introduced" makes the split obvious.
- `t-value-lift`/`m-pair`/`m-curry` gain a free `π`; `isRIntVliftTarget?` / the
  vlift elaborator sites / `checkG` accept any grade; realize/soundness/agree
  thread `π` (grade-erased, so denotation unchanged).

### See Also

- D066 (refined here — value intros pure-fixed → grade-poly), D065 (bare
  morphisms grade-poly), D068 (`t-subsume`), D032 (compose/case/cata grade-poly),
  Plan 0.39 (optimizer drops pure SigOps), Plan 0.52 M1.

## D070: Lambdas ARE Morphisms — Bracket-Abstract Them (the ⊢ᶜ/⊢ᵐ Split for Lambdas Is a Presentation Artifact)

### Context

Discharging `cata-morph-strong` (the last apex-reachable morphism-completeness
leaf, after `const-morph-strong` landed) requires `StrongElab`'s faithfulness
field `m ≡ realize-morph mᵐ` — a **syntactic** IR equality. Investigation
showed this holds cheaply for EVERYTHING point-free:

- **Leaves / combinators** (`m-id`/`m-compose`/`m-pair`/`m-case`/`m-curry`):
  `realize-morph` builds the categorical IR DIRECTLY from sub-morphism IRs and
  the elaborator builds the same — syntactically equal by structural recursion
  (`morph-realize`).
- **Values** (`⊢ᵍ`): a closed value is a global element (point-free constant
  morphism); `checkG-realize` gives syntactic equality (`const-morph-strong`
  discharged this way).

It breaks in EXACTLY ONE place: a **lambda** cata algebra. `cata`'s algebra slot
is typed `⊢ᶜ`, which admits `t-lam`. `realize-morph (m-cata _ dalg)` embeds the
algebra via `elaborate Heap (realize dalg)` — a round-trip `⊢ᶜ → realize →
Surface → elaborate → IR` — while the elaborator embeds `elaborate Heap algE`.
For a lambda the two surface terms (`algE` vs `realize dalg`) come from different
producers, so they are meaning-equal but **not syntactically** equal. A lambda is
the ONLY non-point-free thing that can reach a morphism IR node (compose/case
arms are `⊢ᵐ`, so they can never be lambdas). `ana` (IR-only today) would have
the identical issue via its `⊢ᶜ` coalgebra.

The mathematical question — lambda vs morphism — has a definitive answer:
**Curry–Howard–Lambek.** A CCC and the typed λ-calculus are equivalent; a closed
lambda `A → B` **IS** a morphism `A → B`; lambda abstraction is the exponential
adjunction (`curry`/`apply`); **bracket abstraction is the isomorphism**. So the
`⊢ᶜ`/`⊢ᵐ` distinction for lambdas is a **syntactic presentation artifact**, not a
categorical one.

### Decision

**Elaborate closed lambdas to point-free `⊢ᵐ` morphisms via bracket abstraction**,
rather than leaving them as `⊢ᶜ` `t-lam`. Then cata/ana algebras are always
morphisms, `realize-morph` stays in IR-land, and `cata-morph-strong` (like the
other combinators) is provable with the cheap structural `morph-realize` — no
denotational reorg of the agree theorem.

The IR is NOT changed — it is ALREADY point-free. This decision lives at the
TYPING/derivation level only: it aligns the derivation (`⊢ᵐ`) with the IR's
already-point-free reality. It is the mathematically honest fix: the point-free
IR is the correct categorical home, and lambdas already belong in it. The
alternative (make `morph-realize` denotational, `⟦m⟧ ≡ ⟦realize-morph mᵐ⟧`,
mutual with `agree`) merely PATCHES a presentation mismatch — working around the
fact that two syntaxes for the same morphism aren't the same term.

### Refines D066 (m-lam drop) — the two reasons no longer bind

D066 dropped `m-lam` (a closed lambda AS a morphism). Neither reason blocks
bracket abstraction:

1. *"`extractMorphWitness` can't recover a closed lambda's outer-ctx-emptiness"* —
   a NON-issue. Bracket abstraction produces a GENUINE composite morphism
   (`curry`/`apply`/`compose`/…), not a lambda-shaped `m-lam`, so
   `extractMorphWitness` recovers a real `⊢ᵐ`. Nobody needs to recover a lambda.
2. *"lambdas-as-`t-lam` keep compose/case arms lambda-free ⇒ `*-eff-complete`
   provable"* — PRESERVED. The lambda becomes a morphism BEFORE it can occupy an
   arm position, so arms stay morphism-shaped; the eff-complete proofs keep their
   guarantee.

### Meaning-preserving (does NOT change Once)

- **Runtime / IR unchanged.** `Once.Surface.Elaborate` ALREADY lowers surface
  lambdas to point-free IR (`curry`/`apply`) — codegen is already point-free.
  This moves the SAME categorical translation to the TYPING level so the morphism
  realm captures it; denotations are unchanged (bracket abstraction is meaning-
  preserving by the CCC isomorphism).
- **Same programs well-typed.** Lambda sugar stays in the surface; only the
  DERIVATION changes (a lambda gets a `⊢ᵐ` bracket-abstraction derivation instead
  of `t-lam`).

### Consequences

- `cata-morph-strong` (and future `ana`) discharge as cheap structural
  `morph-realize` cases; no agree-theorem reorg; `StrongElab`'s syntactic
  faithfulness field stays intact.
- New elaborator content: the bracket-abstraction translation + a `⊢ᵐ`
  derivation for lambdas + its `realize-morph` clause. Real work, but well-
  trodden (the CAM/categorical-combinator translation) and it removes the only
  non-point-free thing in the pipeline.
- `t-lam` in `⊢ᶜ` may become vestigial for closed lambdas (retain for any
  open/context-carrying use if such arises).

### See Also

- D066 (m-lam drop — reasons refined/dissolved here), D063 (CCC trichotomy
  `⊢ᵍ`/`⊢ᵐ`/`⊢ᶜ`), D032 (compose/case/cata grade-poly), Curry–Howard–Lambek
  correspondence (CCC ≅ typed λ-calculus), Plan 0.52 M1 (`const-morph-strong`
  discharged; `cata-morph-strong` the remaining leaf this enables).

## D071: Internal Definition References Are Context Projections, Not SigOps (DTT-Aligned)

> **Heading corrected 2026-09-29 (D245).** This entry was headed "SigOp Is FFI-Only". That
> overstated it: D061 names two producers of SigOps, interpretations (FFI) AND the compiler
> itself (the pure `arith.block.<digest>` SigOps). The body's actual decision is that
> *definition references* are not SigOps. See D245.

**Date**: 2026-07-12
**Status**: Accepted; **implemented + certified green** (Plan 0.58, 2026-07-12)
**Implements**: Plan 0.58 (`0.58-once-spec-language-definition.md`), branch `ocp-0006-once-spec`
**Corrects**: the Plan-0.58 SigOp-concreteness migration (2026-07-11), which made `poly`/`closure`
references ride the FFI `SigOp` placeholder
**Relates to**: D047 (Prim→SigOp), D061 (SigOp contract = its interpretation; core is
interpretation-agnostic), D064 (named definitions are morphisms — direct-call ABI), D045
(polymorphic schema instantiation), D030 (FunRef — function references as pointers),
D057 (correctness anchored at a source-level *reference* semantics)

### Context

The 2026-07-11 concreteness migration (Plan 0.58) required a SigOp's types to be `IsConcrete`
(an FFI/register-ABI boundary genuinely only passes concrete values — a legitimate spec
constraint, per D047/D061: a SigOp is an *interpretation* boundary). But it also baked
`IsConcrete` into the surface `poly` (same-module polymorphic-def reference) and `closure`
(user-fn-as-value reference) nodes, which elaborate to `SigOp (value-info …)`. That made
**internal definition references masquerade as FFI values** — so `cata`/closure programs at
non-concrete types (`μNat → Int`) became untypable/rejected (13 exit-tests failed).

The root confusion: `poly`/`closure` are **references to internal definitions** (D064: named
defs are morphisms with a direct-call ABI), NOT FFI operations. Forcing them through the
concrete `SigOp` placeholder hit a totality wall — a reference of *arbitrary* type needs a total
value (impossible for `Void`), which SigOp faked with an opaque postulated value. Two
elaboration attempts (inline δ-reduction with well-founded `Acc` threading) foundered on an
all-or-nothing ~25-member termination cascade.

Stepping back to the mathematics: this is ordinary **parametric polymorphism** with two standard
solutions — monomorphization (Rust/C++/MLton; inline per use) vs. **polymorphic values in a
context + type application** (Haskell Core/System F, Idris2). Only the latter aligns with
**dependent types** (Agda/Idris/Coq/Lean): definitions live in a context Γ, a reference is a
NAME that **δ-reduces to its body on demand**, `⟦x⟧Γ = Γ(x)`. Monomorphization cannot align
with DTT (types depend on terms ⇒ can't pre-instantiate; instantiations may be unbounded;
conversion needs shared references, not copies).

### Decision

**SigOp stays exactly for what it is — an FFI/interpretation boundary (D061), with its
`IsConcrete` constraint intact.** Internal definition references (`poly`, `closure`) STOP riding
SigOp. Instead, adopt **Option C**: a reference is a **projection from the definition-context Γ**.

- **Γ = the definition-context** — the ordered telescope of top-level defs AS MEANINGS (the DTT
  global signature). Its *syntax* is the acyclic telescope already landed (commit `5b4c25ac`,
  which made acyclicity manifest); D071 adds its *semantics*.
- **A reference is a NAME/index into Γ** — no `IsConcrete`, no carried body. `poly` = a value
  reference; `closure` = a first-class-function reference (D064's named-def morphism), refined
  from D030's `FunRef` to be a context projection rather than a bare pointer.
- **The meaning carries Γ** — `⟦_⟧ᵈ`/`SD.⟦_⟧ˢ`/`evalᴰ` become Γ-aware (cleanest as an Agda module
  parameter, threaded once per module); `⟦ ref x ⟧Γ = Γ(x)` IS δ-reduction. Totality comes from
  Γ being well-formed (no `Void` wall); references are O(1) projections (no termination threading).
- **Codegen** compiles `ref x` to internal-linkage call/load of the def's symbol (D064 direct-call
  ABI) — never an FFI SigOp; no concreteness gate.

### Consequences

- The 13 non-concrete `cata`/closure exit-tests become typable/compilable.
- Both blockers of the inline approach dissolve (no totality wall, no `Acc` threading).
- The source-level reference semantics (D057) becomes the DTT global-context/δ-reduction model,
  so **OCP-9 (dependent types) inherits the right structure and need not redo it**.
- Cost: the largest structural change in 0.58 — Γ threads through the meaning functions and the
  adequacy relates the machine's *linked* def-code to Γ. Executed top-down (C is the authority;
  SD/evalᴰ/adequacy are rewritten to conform, not preserved).

### Implementation (2026-07-12, certified green)

The semantic side of Option C was already realized by commit `5b4c25ac` (the acyclic telescope):
the `t-var-poly-instantiate` rule embeds the body's derivation `bodyD` as a premise (that IS Γ(x)
materialized in the derivation tree), and `⟦ t-var-poly-instantiate … bodyD ⟧ᶜ = ⟦ bodyD ⟧ᶜ tt`,
`realize` inlines to `morph-app (elaborate (realize bodyD)) unit`, and `bridge-c` recurses on
`bodyD`. So the concreteness premise was **unused** on the spec side — its removal there is a
mechanical drop.

The remaining wall was structural, not semantic: the IR's named-op carrier `SigOpInfo A B`
*required* an `IsConcrete B` field, so `poly`/`closure` could not build a `SigOp` at a non-concrete
result type. Since that field is **write-only** (no proof ever reads `conB`/`baseA`), the fix was to
relax it to a `Linkage B` tag — `ffi-concrete (IsConcrete B) | internal-ref` — recording the
FFI-vs-internal distinction structurally instead of adding a whole new IR node:
- FFI builders (`value-info`/`arrow-info`/`mk-info`/`ext-*-info`) still take `IsConcrete B` and wrap
  it as `ffi-concrete` — the D061 concreteness discipline for real syscalls/intrinsics is intact.
- A new `internal-info : CanonicalName → SigOpInfo Unit A` builds an `internal-ref` at ANY result
  type (same `Pure`/`generic-semM` shape, so `faithful` stays `refl`). `elaborate`/`SD` of
  `poly`/`closure` now emit `internal-info (bare name)`; codegen's `SigOp → once_<name>` call IS the
  D064 internal-linkage ABI.
- The Surface `poly`/`closure` nodes and the `t-var-poly-instantiate` rule drop their `IsConcrete`
  field/premise; `checkElab-RVar`'s `NonConcreteSigOpType` gate for poly refs is deleted (a poly ref
  is emitted at any `T`); `resolveExprWF`/`resolvePolyCase`/`applySplice` and the Canon transports
  drop the now-absent witness; the dead `poly-ref-bridge` leaf is removed.

`make certified` is exit 0 with these changes.

### Implementation, part 2 (2026-07-12/13, certified green, 13 cata/closure exit tests fixed)

The Linkage relaxation above unblocked the *carrier*; making the 13 regressed same-module tests
pass needed the *routing* and a missing *infer rule*:

- **Telescope routing**: ground-non-concrete own-module defs stop being resolved to `RResolved`
  (the FFI path) and become telescope entries like poly defs. `Parser.agda`
  `extractFunctions-go` and `Resolve.agda` `polyDefNames` split ground defs by
  `isConcrete? (extractGround ty g)`: concrete → the old `RResolved`/SigOp path (FFI discipline
  intact), non-concrete → `PolyFunInfo`/keep-bare (telescope). The three mirror proofs
  (`CanonExtract`, `CanonReflectExtract`, `CanonPolyNames`) replicate the nested
  `with isGround`/`with isConcrete?` clause structure verbatim (the clause trees must match).
- **New infer rule `t-var-poly-instantiate-infer`** (⊢ᵢ): a *ground* telescope def infers at its
  declared type. Same lookup premises as the check rule plus `isGround schema ≡ inj₁ g`, with the
  generic-codomain trick (conclusion at generic `T` + premise `T ≡ extractGround schema g` — a
  direct `extractGround` index makes downstream splits UnificationStuck). This rule is what makes
  *applied* uses (`toInt three`) typable — the earlier "inline-resolution deadlock" was just this
  rule missing. The CHECK rule `t-var-poly-instantiate` gains the complementary premise
  `isGround schema ≡ inj₂ tt` (non-ground only), keeping the system syntax-directed and
  completeness two-sided: check-mode uses of ground telescope defs go infer → `embedOrSubsume`,
  exactly the pre-migration mono behavior.
- **Semantics/adequacy**: `⟦ t-var-poly-instantiate-infer … bodyD ⟧ᵢ dγ = ⟦ bodyD ⟧ᶜ tt`
  (Meaning); `realize-infer` inlines the body (Realize); `bridge-i` mirrors `bridge-c`'s poly
  case (MeaningBridge); the Canon transports gain the mirrored -ᵢ cases (schema is
  canon-invariant, so `ig`/`Teq` carry verbatim).
- **Elaborator**: `inferElabV-RVar`'s nothing/nothing fallback now succeeds for ground poly names
  (de-withed helper chain `inferElabV-RVar-poly-aux` → `-lookup-aux` → `-ground-aux`, enumerating
  all `bbc` constructors — no catch-all); `Completeness` gains the `infer-complete` case and
  threads `eqG`; `ErrorProofs`' `var-unbound-is-UnboundVariable` re-proved now that the fallback
  can succeed (every *failure* leaf is still UnboundVariable).
- **Residuals** (established Phase-2-gap pattern, dischargeable via the real rules): two
  premise-erased witness postulates (`bbc-other-poly-witness`, `bbc-other-poly-infer-witness`)
  and two RealizeAgrees agreement postulates (`check-agreeV-RVar-poly-todo`,
  `infer-agreeV-RVar-poly-todo`). Cross-module (unaliased import) non-concrete defs still take
  `RResolved` → still gated; the fixed tests are all same-module.

Post-change: `make certified` exit 0, re-extraction + capped cabal build clean,
`tests/run-exit-tests.sh` **50 pass / 0 fail / 2 skip** (the 13 layer5 cata/closure regressions
are green again).

---

## D072: Sig-less Definition Types via an Untrusted Principal-Type Oracle (Kernel Stays Bidirectional)

**Date**: 2026-07-13
**Status**: Accepted (design); implementation staged (Plan 0.58 D072 phase)
**Completes**: D007 ("signatures are optional — the compiler can always infer the type")
**Relates**: D063 (morphism realm), D071 (telescope references), the no-unification kernel
discipline (`Classify.agda`: "the typing rule must be locally decidable in a no-unification
bidirectional system")

### Context

D007 (2025-12-08) promises complete type inference: *"the expression alone determines the
type"*, *"signatures are optional"* — and even works `foo = id` inferring `A -> A`. That promise
is mathematically sound: Once's term language is first-order with fixed generator schemas, no
higher-rank types, no type classes, and finite annotation lattices (purity, quantity) — exactly
the hypotheses of Hindley's **principal type property**. Every typeable expression has a most
general type, unique up to renaming, computable by first-order unification. (D007's rejection of
signature specialization is only coherent *because* principal types exist.)

The formal spec under-delivers on D007: the kernel judgment (`⊢ᵢ/⊢ᶜ/⊢ᵐ/⊢ᵍ`) is bidirectional and
deliberately unification-free, so information flows only up (synthesis) or down (checking) the
syntax tree. Any type determined only by a *system* of constraints spanning siblings — the
`cod g = dom f` of a composition, a bare polymorphic name with no application, a sig-less lambda
— is out of reach. Witnesses: the PENDING exit tests `infer-id.once` (`myId = id`) and
`infer-compose.once` (`run = compose exit@S id`), and generally every sig-less def whose body is
an introduction form. The classifier family (`composeMid`/`composeArgB`/`domainOfHead`) is a
per-shape hand-computation of fragments of the most general unifier; the frontier never closes
(per-shape witnesses aren't a theorem).

### Options

- **A — re-scope D007**: make "introduction-form defs require signatures" the official contract.
  Retracts a mathematically valid documented promise to fit the proof technique. Rejected.
- **B — untrusted principal-type oracle + verified kernel check**: the proof-assistant
  architecture (Agda/Coq/Lean): an untrusted elaborator/unifier proposes, a small syntax-directed
  kernel disposes. **Accepted.**
- **C — keep accreting classifiers**: re-deriving Robinson's algorithm one syntax shape at a
  time, three mirror proofs per shape, frontier never closes. Rejected as strategy (existing
  classifiers stay — they serve check-mode rules).

### Decision

For **sig-less definitions only**, compute the body's principal type with an **oracle** — a
fuel-bounded first-order unification (metavariables, occurs check) over the schema grammar, with
generalization at the definition boundary — and then proceed exactly as if the user had written
that type as a signature:

- principal type **ground** → the existing `FunInfo` path: `resolveFunType`'s `nothing` branch
  falls back to the oracle when `inferElab` fails; `compileFun` re-checks the body at the
  oracle's answer with the verified `checkElab` (check-after-infer).
- principal type **a schema** → the def routes to the telescope (`PolyFunInfo`) with the
  computed schema, exactly like a signed poly def; uses instantiate through
  `t-var-poly-instantiate(-infer)` as today.

**The kernel judgment is unchanged**: no metavariables, no new rules, no new `Type` constructors.
The oracle's output is **untrusted** — a wrong answer fails the kernel check and the program is
rejected; nothing ill-typed can pass. Soundness of acceptance ("accepted ⇒ derivation ⇒
meaning") is therefore preserved *by construction*, with zero growth of the trusted base.

### The trust/proof structure

- **Soundness**: free. `AllFunsTyped.tcons` keeps its two-premise shape — `resolveFunType ≡
  inj₂ ty` (provenance now signature | inference | oracle) and `⊢ᶜ body ∶ ty` (from
  `compileFun`'s verified check). `AcceptSound` does not care where `ty` came from.
- **Completeness**: the genuinely new obligation, stated ONCE about the oracle — *if any type
  (ground or schema, up to renaming) exists at which the body kernel-checks, the oracle returns
  the principal one and the kernel check at it succeeds*. One theorem about one algorithm,
  instead of a theorem per syntax shape. Staged: v1 ships with the oracle unverified (soundness
  unconditional regardless); the completeness theorem is tracked as an explicit open obligation,
  NOT hidden behind acceptance postulates.
- **Failure = signature request**: since a correct oracle fails only on genuinely untypeable
  bodies (unification clash), the error is principled; an incomplete v1 corner degrades to
  "cannot infer — add a signature", never to unsoundness.

### Design rules for the implementation

1. **Fuel-bounded unification**: Agda totality via a fuel measure (problem size bound); fuel
   exhaustion = inference failure (ask for a signature), never wrong output.
2. **Canon-invariance by construction**: the oracle dispatches `RVar x` and `RResolved cn`
   through the same `showCanonical`-keyed lookups (the `composeArgB-lookup` pattern) so the
   canon transport proofs stay definitional.
3. **Least-commitment annotations**: v1 emits `Many` quantities and infers purity structurally
   (`PEff` where forced); the kernel check is the arbiter (t-subsume / q-ordering absorb slack).
   Purity-polymorphic leftovers → failure (signature required) in v1.
4. **Generalization only at the def boundary** (matching the telescope): leftover metas in a
   def's principal type become schema `PTVar`s; no generalization inside terms (terms stay
   simply typed — the kernel's ground-`Type` invariant is untouched).
5. **OCP-9 continuity**: this is the kernel/elaborator split of the proof assistants; under
   dependent types the oracle becomes partial (pattern unification) and the kernel keeps its
   shape. Nothing built here is redone.

### Consequences

- `infer-id.once` and `infer-compose.once` flip (52-test suite); D007's contract becomes true.
- New module `Once/TypeCheck/Principal.agda` (oracle; unverified v1); `inferType` fallback wiring
  (`Compile.agda`); sig-less schema routing in `Parser`/`Resolve` + the 3 Canon mirror proofs.
- Open obligation ledger gains: oracle completeness theorem (principality), replacing the
  open-ended classifier frontier.

### Implementation (2026-07-13, certified green, 55-test suite)

Landed in four milestones, all `make certified` exit 0, zero new postulates:

- **M1 — the oracle** (`Once/TypeCheck/Principal.agda`): `PTVar "?n"` metavariables,
  occurs-checked fuel-bounded unification over `PolyType`/`PolyFunctor`, ground-`Type`
  embedding, builtin schema table (`compose` special-cased — grade-polymorphic), schema
  freshening for user poly defs, W-style structural traversal (`_>>=R_` chains, with-free
  spine), def-boundary generalization. The traversal context is `(Imports, SchemaCtx)` — poly
  BODIES are out of scope **by type**.
- **M2 — ground wiring**: `inferType`'s failure branch falls back to `principalGround`,
  validated by `checkElab` (`inferType-validate`). The canon transports were the predicted
  ripple: `CanonPrincipal.agda` proves the oracle **pointwise canon-invariant** (possible,
  unlike for `inferElab`, because the oracle was designed for it: one `showCanonical`-keyed
  lookup, definitional singleton-canonical, schema-only context); `CanonAllFuns` /
  `CanonReflectAllFuns` gain `inferType-inv` (via-elab | via-oracle) and transport the oracle
  branch (opposite-side inferElab failure by reflection-contradiction, oracle answer by
  invariance, validation through the `⊢ᶜ` bridges).
- **M3 — schema routing**: `siglessSchema` (non-ground principal type in the EMPTY context)
  routes sig-less defs to `PolyFunInfo`, shared by `extractFunctions-go` and the NEW
  pending-threaded `pdn-go`/`polyDefNames` so routing and keep-bare agree exactly; mirror
  proofs via `siglessSchema-canon` + `poly⊆` restated over `pdn-go`.
- **M4 — validation**: `infer-id` (schema alias) and `infer-compose` (unification through a
  composition) un-PENDed and green; new tests `infer-compose-chain` (nested compose + eff),
  `infer-lambda` (sig-less lambda), `infer-poly-alias` (multi-variable schema alias).

Proof-engineering notes (for the next oracle-adjacent change): keep the traversal `with`-free
(`>>=R` chains make the invariance proof equational); dispatch builtins via explicit `≟`
(never string-literal patterns — proof opacity); hoist recursive helpers out of `where`
(lifting turns as-pattern subterms into reconstructions and breaks the termination checker).

**Open (the D072 ledger)**: the oracle completeness theorem (principality); v1 coverage gaps
(cata/In/ana bodies need functor metavariables; unresolved `RQualified` leaves; sig-less
bodies referencing earlier USER defs use the empty-context criterion, so only builtin-built
bodies generalize).

## D073: No Pointer Tagging, Heap Base Stays 0 — Dereference Divergences Close via Site-Discipline Facts

**Date**: 2026-08-01
**Status**: Accepted (implemented same day: `branch-tag-scrutinee-wf`,
`load-indirect{,-suc}-target-wf`, the `*-empty-stuck` bricks)
**Relates**: D054 (`Int` is a full-width modular `Word`), D061 (contracts come
from interpretations), the flat↔x86-64 correspondence's vacuity discipline
(2026-07-30 audit)

### Context

The flat↔x86-64 correspondence carried four residuals asserting run-events
equations for states where the dereferenced register (`Input1`) holds a
NON-pointer at an emitted `c-branch-tag-zero` / `load-indirect{,-suc}` site
(`branch-tag-badptr`, `branch-tag-bad`, `load-indirect{,-suc}-bad`). There the
machines genuinely diverge: the abstract branch falls through and the abstract
load halts, while the concrete `cmp [rdi],0` / `mov rax,[rdi]` reads memory at
the value's encoding — stuck if unmapped, garbage-and-continue if mapped. The
routes correspond only under "a non-pointer's encoding is not a mapped
address", which is false with tags encoding to small naturals and the heap
based at 0.

### Options

1. **Move the heap base up** so tag/code encodings sit below it. Rejected:
   D054 makes an int literal an arbitrary machine word, so no base or address
   range can ever separate literal encodings from mapped addresses; the ripple
   (entry view, `sep`, the high-water `untouched` region) buys a partial fix
   at best.
2. **Tagged/boxed value representation** (disjoint encodings for pointers vs
   non-pointers, e.g. low-bit tagging). Rejected: `enc-sv (SV-Lit fits-int v)
   = v` is the correspondence's statement that compiled code runs on RAW
   UNBOXED words — the binary really loads the immediate `v`, and the arith
   path computes on it. Changing the encoding is a runtime-representation
   redesign of the language, not a proof fix.
3. **Abstract machine halts on a non-live scrutinee** (model change). Rejected:
   the mapped-garbage concrete route still continues while the abstract halts,
   so the (false) encoding claim is still needed — plus it ripples every
   machine-invariant proof.
4. **Site-discipline (dataflow WF) residuals** — the divergent routes are
   unreachable in well-typed emitted programs: codegen emits a tag branch only
   after loading a constructed node's pointer, and a `load-indirect` only to
   dereference a pair/node pointer. State that per site, conditioned on the
   run context, in the `lea-indexed-wf` / `store-indirect{,-suc}-inbounds`
   mold.

### Decision

Option 4. The heap base stays 0 and `enc-sv` stays raw. The four divergence
residuals are replaced by three narrower dataflow facts:

- `branch-tag-scrutinee-wf` — at an emitted `c-branch-tag-zero` site,
  `Input1` holds a heap pointer to a WRITTEN TAG cell (replaces both
  `branch-tag-badptr` and `branch-tag-bad`; `dom-written` supplies the
  block-step's liveness);
- `load-indirect{,-suc}-target-wf` — at an emitted load site, `Input1` holds
  a pointer, in-bounds for its block when dynamic (the store family's exact
  conjunct, so the whole dereference family is uniform and is discharged
  together by the pointer-in-bounds invariant).

Two previously-residual routes became THEOREMS in the same move: an empty
stack cell and an empty (allocated, unwritten) heap cell halt both machines —
`stack-eq` / `dom-sized` + `heap-eq` make the concrete read unmapped, so the
trace ends exactly where the abstract machine halts (the `*-empty-stuck`
bricks + `run-events-stuck`).

### Consequences

- The `*-bad`/`badptr` class is gone from the residual map; what remains of
  the dereference story is the honest dataflow class with a discharge
  trajectory: a per-site register-shape invariant (static expectation at each
  emitted site + preservation induction — the `FlatStackPtr` pattern), plus
  the entry-model decision the in-bounds family already waits on.
- `store-indirect{,-suc}-bad` are NOT covered: stores are a genuine model gap
  (the concrete write-through-non-pointer succeeds where the abstract halts)
  and stay parked on the address-keyed-memory / store-site-check decision.

## D074: The Entry Fillers Are Tags — a Unit Input Has No Residence

**Date**: 2026-08-01
**Status**: Accepted
**Relates**: D073 (no tagging, heap base 0 — this closes the entry-model fork
its consequences section left open), D054 (raw unboxed representation), the
Plan 0.54-D item-4 move that already made `Scratch`/`Count` entry tags

### Context

The heap in-bounds invariant ("every dynamic pointer the machine holds is
in-bounds for its block", the discharge trajectory for
`store-indirect{,-suc}-inbounds` and D073's `load-indirect{,-suc}-target-wf`)
was FALSE at the entry state: `FlatFromObs.entry-regs` filled
Input1/Input2/Output with `SV-Ptr (AtDynamic (heap-loc (mkHeapRef 0) 0))`
while `entry-alloc` gives every block size 0, so the filler pointer required
`0 < 0`. The fork: (a) give ref 0 a real size at entry, or (b) make the
fillers non-pointers.

### Options

1. **Real size for ref 0 at entry.** Rejected: `dom-sized` (in-bounds ⇒
   mapped) then forces the entry heap view to contain the cell, `dom-below`
   forces the entry frontier to 8, and `r15-eq` forces the concrete `%r15` to
   heap-base+8 — but the emitted startup code sets `%r15` to exactly
   `once_heap_base`. So (a) is an extracted-compiler change (startup
   reservation + full malonzo/cabal/exit-test ×3 cycle) fabricating a phantom
   allocation no program reads.
2. **Tag fillers + residence-free unit input.** The same move Plan 0.54-D
   item 4 already made for `Scratch`/`Count`: `SV-Tag 0` encodes to 0
   (`enc-sv (SV-Tag 0) = 0`), exactly what the pointer filler encoded to, so
   `entry-corr` stays `refl` and NO binary change is needed.

### Decision

Option 2, in three parts:

- `FlatFromObs.entry-regs` fills Input1/Input2/Output with `SV-Tag 0`.
- `InputAt` gains `in-unit : A ≡ Unit → InputAt v loc s` — a unit input has
  NO residence requirement. This is needed independently of the entry state:
  after `f : IR A Unit` in a composition, `g`'s unit input residence is
  unconstrainable, so a pointer-only premise would make `comp-step`'s IH
  inapplicable.
- `readReg-typed Unit _ = just tt` (SMCore) — a unit value is materialisable
  from any register content, mirroring `readTyped Unit loc s = just tt`. Both
  `pure-sigop-out-aux` dispatch branches then land on `just tt`, so the
  Pure-SigOp value equation holds for unit-domain SigOps whatever `Input1`
  holds (`pure-sigop-out-unit`).

### Consequences

- No register (nor heap/stack cell) holds a pointer at entry, so the heap
  in-bounds invariant is TRUE (vacuously) at the entry state — the in-bounds
  family (`store-indirect{,-suc}-inbounds`, `load-indirect{,-suc}-target-wf`)
  is unblocked for its preservation induction.
- `entry-alloc` still reserves ref 0 (`next-heap-ref ≡ 1`): `entry-loc` (the
  input-loc index, now pointed at by nothing) must stay `BeforeFrontier` for
  `entry-witness`. Harmless: no pointer to the sizeless block exists anywhere.
- `IRObsCorrectF` got STRONGER (its `InputAt` premise is easier to inhabit),
  so the postulated scaffolds `obs-correct-rest`/`cata-correct` now claim
  unit-input runs work with arbitrary `Input1` content — which is true of the
  machine (unit is never read) and required for the composition discharge.

## D075: The Layering Refactor Is Rejected — `Emitted` Is Load-Bearing for the Dataflow Residuals

**Date**: 2026-08-01
**Status**: Accepted (probe run and reproduced; refactor NOT landed)
**Relates**: the 2026-07-30 vacuity fix (which introduced `Emitted prog` into
the run context), D073 (site-discipline dataflow residuals), D074 (tag entry
fillers — they make the probe's refutation immediate)

### Context

Plan 0.54 rung D item 4 proposed replacing `Emitted prog`
(`Σ ir → prog ≡ ir-to-trace ir`) in ConcFlatSim's run context with a
TRACE-PREDICATE bundle (`FrameFreeT prog × All (SlotBelow B) prog ×
All AllocMinI prog`), so the machine correspondence stops importing the
codegen layer. The 2026-08-01 analysis flagged the move as vacuity-sensitive
and required the probe recipe before landing.

### The probe (recipe of 2026-07-28/30, re-run 2026-08-01)

A scratch module stated the WOULD-BE bundle-conditioned forms of the two
dataflow residual shapes and derived `⊥` from both:

- `prog₁ = load-indirect ∷ []` satisfies the whole bundle trivially
  (`(tt , tt) , (sb-none refl ∷ []) , (tt ∷ [])`) and is fetched at the REAL
  entry state (`reach-start` + the apex's `entry-like`); the candidate
  `load-indirect-target-ptr` then hands back
  `readReg Input1 ≡ SV-Ptr loc` while D074's entry filler makes that
  register `SV-Tag 0` — constructor clash, `⊥`.
- `prog₂ = instr-ctrl (c-branch-tag-zero 0) ∷ []` refutes the candidate
  `branch-tag-scrutinee-wf` the same way.

One refutable residual anywhere makes the whole correspondence vacuous
(vacuity is all-or-nothing), so the swap cannot land in any form that
weakens the dataflow residuals' hypothesis.

### Decision

The refactor is REJECTED; `Emitted prog` stays in `RunAt`. The "impurity"
of ConcFlatSim importing the codegen layer is the honest structure: the
dataflow residuals are claims about programs THE EMITTER PRODUCED, and no
trace-SHAPE predicate can express the dataflow discipline they encode — a
bundle admits hand-buildable programs whose sites lack the discipline.

A partial swap (bundle for the theorem layer only, `Emitted` kept for the
residuals) was considered and rejected too: `Emitted` must stay in the run
context regardless, so the move would shuffle imports without changing the
trust story.

### Consequences

- Item 4 is CLOSED (rejected with evidence), not deferred.
- The only principled path that could ever weaken `Emitted` for the
  dataflow class is the per-site register-shape invariant (a static
  dataflow analysis over the trace, proved of the emitter and preserved by
  the machine — the FlatStackPtr pattern). That is those residuals'
  discharge trajectory anyway; do that, not a layering refactor.

## D076: The Dataflow Disciplines Discharge via Type-Indexed Shape Correctness (Plan 0.62)

**Date**: 2026-08-02
**Status**: Accepted (design + plan; execution not started)
**Relates**: D073 (which created the discipline residuals), D074 (whose tag
filler is one of the counterexamples), D075 (which rejected the bundle
refactor and named this as the only principled weakening of `Emitted`)

### Context

Three dataflow residuals remain in the flat↔x86-64 correspondence:
`branch-tag-scrutinee-wf` and `load-indirect{,-suc}-target-ptr` — per-site
facts about what `Input1` holds at emitted dereference/branch sites. The
standing estimate ("the FlatStackPtr pattern — static expectation per site +
preservation") understated the problem.

### Findings (each verified against the code, 2026-08-02)

1. No pc-free state invariant can express the facts — the D074 entry filler
   and literal-producing fragments legitimately put non-pointers in the
   constrained registers at other pcs.
2. No type-free (syntactic) dataflow analysis suffices — in the cata descend
   loop the next scrutinee is loaded FROM THE HEAP, and only heap TYPING
   ("a sum node's payload cell holds a node pointer") gives loads a usable
   shape.
3. The tag conjunct of the branch discipline is load-bearing: `tag-zf` is
   `false` on non-tags while the concrete `cmp` compares raw encodings
   (`enc-sv (SV-Lit fits-int 0) = 0`), so a non-tag cell flips the branch
   decision; and sum-vs-pair node discrimination is type information.

### Decision

Discharge via a TYPE-INDEXED SHAPE-CORRECTNESS theorem for codegen, built as
a standalone shape layer (Plan 0.62): `ShapeAt` = the shape-level erasure of
`ValidAtWF` (existentials where `ValidAtWF` is exact), a per-pc expectation
table emitted by a typed re-walk of `ir-to-trace'`, and a run-level
consistency preservation theorem. Design constraint: `ValidAtWF → ShapeAt`
must be a projection (gate G1), so the eventual value-correctness layer
subsumes the shape layer instead of duplicating it. The alternatives —
folding into the `obs-correct-rest` discharge (gates on the bigger semantic
theorem) and parking the disciplines (leaves D073's trajectory unwalked) —
were considered and set aside; the shape layer is self-contained and its
statement is reusable by the value layer.

### Consequences

- Plan 0.62 is the execution vehicle; milestone gates G1 (erasure is a
  projection) and G2 (the cata loop invariants close under the back-jump,
  checked by hand for `strat-nat` first) are hard stops if they fail.
- Until M4 lands, the three disciplines remain honest site+run-conditioned
  residuals; nothing else in the correspondence waits on them.

## D077: The Branch-Tag Scrutinee Discipline Is Residence-Generic (Vacuity Fix)

**Date**: 2026-08-02
**Status**: Accepted (implemented same day; probe confirmed before, refuted after)
**Relates**: D073 (which introduced the residual heap-only), plan 0.61 (which
gave stack pointers real addresses, making the fix expressible), the
2026-07-30 vacuity discipline

### Context

While building Plan 0.62's `Meets` interpretation, the shape semantics of
sums exposed that `branch-tag-scrutinee-wf` — "at an emitted
`c-branch-tag-zero` site, Input1 holds a HEAP pointer (`AtDynamic`) to a
written tag" — is REFUTABLE: `inl/inr Stack` write their tag into a STACK
slot (`instr-load-tag-lit t ∷ store-at-slot …`) and hand back an `AtStack`
pointer (`lea-slot`), and `case id id ∘ inl Stack : IR Unit Unit` reaches
the branch site with that stack pointer after six mechanical steps from the
entry state. A probe (recipe of 2026-07-28) derived `⊥`. Since vacuity is
all-or-nothing, the whole conditional correspondence was vacuous while this
stood (introduced with D073 on 2026-08-01).

### Decision

The residual is restated RESIDENCE-GENERICALLY — the scrutinee holds a
pointer (either residence) to a written tag cell, with `readLoc` covering
both:

    Σ loc. (Input1 ≡ SV-Ptr loc) × Σ k. (readLoc (floc fs) loc ≡ just (SV-Tag k))

and the machinery was DE-SPECIALIZED rather than duplicated: the tag-branch
block-steps (`block-step-c-branch-tag-zero`, `-nz`) never depended on the
residence — only on the abstract read and the CONCRETE read — so the
concrete-read equation became a PREMISE, and the routing site
(`tag-branch-step`) derives it per residence: heap via
`heap-eq`/`dom-written` (as before), stack via the live-pair theorem
`stack-ptr-current` + `rsp-eq`/`slot-addr-linear`/`stack-eq` (the same
chain plan 0.61's stack-pointer loads use). The je-halt (missing label)
route generalizes identically.

### Consequences

- The probe no longer typechecks (the refutation is impossible); the
  residual is again in the honest site-discipline class.
- Plan 0.62's discharge obligation for this residual now targets the
  generic form: the shape layer's `TagAt` covers heap sums; the stack-sum
  route will need the tag fact for stack-mode sums too (`SumTag Stack = ⊤`
  in the VALUE layer understates what the emitted code guarantees — noted
  in the plan as an M3 concern).
- Lesson (again): a residual whose statement bakes in a REPRESENTATION
  CHOICE (heap-only) for a claim that is really about a VALUE-LEVEL fact
  (a written tag) is the vacuity-prone shape; state disciplines over
  `readLoc`, not over a residence.

## D078: `SumTag` Is Mode-Independent — Stack Sums Write Their Tag Too

**Date**: 2026-08-02
**Status**: Accepted (implemented same day; cluster + certified green)
**Relates**: D077 (whose probe PROVED the stack tag write is reachable),
Plan 0.62 (whose branch-site fact needs the tag from the shape layer)

### Context

`ClosureWellFormedDef.SumTag` said `Stack ↦ ⊤` ("stack sums are
reference-based and don't store the tag") — but the emitter's
`inl/inr Stack` lowering writes `SV-Tag t` into the sum slot
(`instr-load-tag-lit t ∷ store-at-slot sum-slot ∷ …`), and the D077 probe
mechanically reached a branch reading exactly that cell. The value layer
UNDERSTATED the representation, and the understatement propagated into
Plan 0.62's `TagAt` (the shape erasure), making the branch-site tag fact
underivable for stack-mode sums.

### Decision

`SumTag m t s loc = readLoc s loc ≡ just (SV-Tag t)` for BOTH modes — kept
as per-mode clauses (identical bodies) so the symbol stays RIGID on an
abstract mode (a fully-reducing definition un-pins `transport-SumTag`'s
implicits at every call site — unification cannot invert `readLoc`).
`transport-SumTag` becomes `trans eq tg` in both clauses. `ShapeAt.TagAt`
and gate G1's `tag-of` strengthen in lockstep (the projection stays 1:1).

### Consequences

- The branch-site fact of Plan 0.62 (`site-ok` + `Meets` ⇒ a written tag
  cell, either residence) is derivable for every sum claim.
- On-path consumers all route through `transport-SumTag` — no other change.
  The orphaned legacy module `Once.CCC.Machine.IR.SumRecWF` (imported by
  nothing) constructs a Stack-mode `valid-inl-wf` with `tt` and now needs
  the tag equation its own trace provides; it joins `ApplyWF` as
  known-broken-off-path until the legacy layer is revived or deleted.
- The value layer is now FAITHFUL to the emitted representation for sums —
  the `obs-correct-rest` discharge will need exactly this field.

## D079: Float CONSTANTS Are Bit Patterns — Emit the Immediate, Not `ud2`

**Date**: 2026-08-03
**Status**: Accepted (implemented same day; `load-const-float` retired)
**Relates**: D054 (`Int` is a full machine word — same immediate path),
the flat↔x86-64 halt-correspondence family

### Context

`compile-const fits-float` emitted `ud2` ("float load not yet
implemented; trap to keep the gap visible"), while the abstract machine
loaded `SV-Lit fits-float v` into `Output` and CONTINUED. The two machines
therefore disagreed on this route, and the disagreement was carried by the
postulate `load-const-float` — which is not merely unproven but FALSE for
any program that loads a float constant and then emits an observable (the
concrete trace stops, the abstract one does not). A false axiom in the
correspondence cone is a soundness hole, not a gap.

### Decision

Emit the constant. `⟦ Float ⟧` is Agda's builtin double and a double IS a
64-bit word, so a float CONSTANT needs no floating-point unit:

- `Once.Semantics.FloatBits.float-bits : Float → ℕ` — the IEEE-754 pattern
  via `Data.Float.toWord` (NaN ↦ 0, since Agda declines to pick a NaN
  representation);
- `compile-const fits-float v = mov (reg rax) (imm (float-bits v))` —
  one instruction, so `compile-const-size` is unchanged; gas promotes
  `movq $<64-bit>` to `movabs` (verified against the assembler);
- `enc-sv-at am (SV-Lit fits-float v) = float-bits v` (was `0`), so the
  correspondence's `rax-eq` is `refl` exactly as in the int case.

Both machines now load the same word and continue;
`block-step-load-const-float` is the int block-step with the pattern as
the immediate, and `load-const-float` is DELETED.

### Consequences

- Float ARITHMETIC remains unsupported — no FPU instruction is ever
  emitted, and no arith SigOp is classified float. This decision is about
  constants only; a float that is computed on still has no lowering.
- `float-bits` is not injective (NaN), and nothing needs it to be: the
  encoding is only read forwards (abstract value ↦ concrete word), and
  both sides are literally this function.
- CODEGEN CHANGED ⇒ extraction gate applies (malonzo + cabal + exit tests
  ×3) before merge.
- The alternative — making the abstract machine halt to match `ud2` —
  was rejected: it would need the DENOTATION to halt too (else the flat
  machine and the denotation diverge instead), i.e. floats would have to
  be rejected at the frontend. That is a language-level amputation where
  a 3-line encoder suffices.

### Applied to riscv64 2026-08-13 (plan 0.65 G2) — and NOT to x86-32, on purpose

riscv64 emitted `unimp` for `instr-load-const fits-float`: the same TRAP-instead-
of-load that this decision removed from x86-64, one arch over, left behind
because riscv64 had no correspondence to hold it to account. It now emits
`li a0, <bits>`, and `block-step-load-const-float` states the correspondence.
`li` is the assembler's pseudo-instruction and expands to `lui`/`addi` — the
same trust seam as gas promoting `movq $big` to `movabs`.

**x86-32 keeps its `ud2`, and that is correct rather than lazy.** `float-bits`
is a 64-BIT pattern (`primWord64ToNat` of a `Word64`), and x86-32's word is 32
bits. Loading it into `eax` would not merely be awkward — since plan 0.70 phase
D norms immediates, it would SILENTLY TRUNCATE the pattern to its low 32 bits
and produce a wrong float with no diagnostic. Trapping is the honest behaviour
until floats have a two-word representation on 32-bit targets. Note also that
`LitFits.float-fits` (`float-bits v < modulus`) is TRUE at 64 bits and FALSE in
general at 32 — the parameter itself records the distinction.

THE GENERAL POINT: a "feature gap" on one arch is worth re-deriving rather than
inheriting. Two of the three trapping clauses were leftovers; the third was a
representation constraint. They looked identical from the outside.


## D080: The D061 SigOp Contracts Are Larger Than Their Reason — Split Them

**Date**: 2026-08-03
**Status**: Analysis accepted; the split is planned work (not yet done)
**Relates**: D061 (contracts come from interpretations), D071 (SigOp is
FFI-only), D058 (event-indexed correctness)

### The question

Why do `arith-sigop-contract` and `external-sigop-contract` need to be
postulates at all?

### The finding

They are postulates mostly because **the functions they constrain are
themselves postulated**. `Once.Adequacy.CPU.X86-64` declares

    postulate
      step-budget-x86-64 : ℕ → ℕ
      ev-x86-64          : RT.EvExtractor val-x86-64
      arith-env-x86-64   : X64S.Program → RT.ArithEnv val-x86-64

so every claim about `ev`/`env` is a constraint on an unknown function —
unprovable by construction, whatever its content. That is a very different
situation from an honest external axiom, and it currently hides three
distinct things behind one word ("contract"):

1. **`arith-env-x86-64` — purely INTERNAL, a wiring gap.** This is the
   table mapping `once_arith.block.<digest>` labels to the blocks THE
   COMPILER ITSELF EMITTED. It is derivable from `prog` by construction
   (the module's own comment says as much: "step 4: derive from `prog`'s
   emitted blocks"). Once defined, both env conjuncts —
   `env sym ≡ just pl` for an arith SigOp and `env sym ≡ nothing` for an
   external one — are facts about our own construction, hence provable.
   Nothing here is external to the program.
2. **The VALUE half of `ev-x86-64`** — "the emitted event carries the
   argument the ABI register holds". This is about our own calling
   convention and is relatable to the abstract `event-of` through the
   correspondence's `rdi-eq`. Definable and provable.
3. **The IDENTITY half of `ev`, and the post-call state** — "the symbol
   `once_linux_exit` denotes the SigOp named `linux.exit`; invoking it
   performs that effect; the callee respects the ABI (callee-saved
   registers, our heap) and returns". THIS is the irreducible part: it is
   a claim about code we do not compile and cannot see. It is closable
   only by verifying the callee (e.g. a syscall against a verified kernel),
   which is D061's TrustedBase and the same boundary CompCert keeps for
   external functions.

The `arith` contract additionally rests on results that ALREADY EXIST and
are postulate-free on three arches (`arith-block-correct`,
`dispatch-arith-preserves`); what is missing is the bridge from their
interface (ArithSimCore's read-back form) to `CompiledCorr`.

### Decision

Do not treat the two contracts as a single honest axiom. The planned split:

- DEFINE `arith-env-x86-64` from the emitted program; prove both env
  conjuncts. (Removes the env content of both contracts.)
- DEFINE the mechanical part of `ev-x86-64` (argument read + event
  construction), leaving the symbol↦SigOp denotation as data supplied per
  interpretation.
- DISCHARGE `arith-sigop-contract` from the existing arith results through
  that bridge — it is internal, so it should be a theorem.
- KEEP, as the honest per-(SigOp × target) TrustedBase, only: the foreign
  callee performs the effect its symbol denotes, respects the ABI, and
  returns.

### Consequences

- Expected outcome: `arith-sigop-contract` becomes a theorem;
  `external-sigop-contract` shrinks to the FFI core and should be renamed
  to say what it actually assumes (`foreign-call-abi` + `foreign-call-emits`).
- `step-budget-x86-64` is a separate, already-named honest gap (D5 fuel
  adequacy) and is NOT part of this split.
- Until the split lands, the census should describe these two as "one
  wiring gap + one FFI axiom", not as two axioms.

## D081: A Code Address Is Where the Label Is — Resolve at `lea`, Not at `call`

**Date**: 2026-08-03
**Status**: Accepted (design decision; execution = Plan 0.63)
**Relates**: D079 (the previous false-postulate finding), the
`x86-64-loader-faithful` trust surface, Plan 0.63

### Context

Closing `events-running-call` forced the question "what IS a code address
in the modelled machine?", and answering it exposed an inconsistency:

- `execInstr prog s (call target)` pushes `pc s + 1` and sets
  `pc := <the operand's VALUE>` — faithful to hardware;
- but `effectiveAddr s (rip+label n) = n`, with the comment "label
  resolved by linker; abstract" — the resolution is STUBBED, so `lea` of
  a body label yields the bare label NUMBER;
- while every other control transfer (`c-jmp`, `je`) resolves through
  `find-label`, which returns an instruction INDEX.

So a modelled closure call jumps to a label number interpreted as an
index. Consequently `events-running-call` is not merely unproven but
FALSE in general (same class as `load-const-float`, D079).

NOTE: the EMITTED CODE is correct and unaffected. `lea .L_thunk_n(%rip)`
materializes a real address and `call *0x8(%r12)` is the standard indirect
closure call — necessary, since a call site cannot know statically which
closure it invokes. There are no performance implications in any option;
the defect is entirely in the model's interpretation.

### Decision

Make the stubbed line true: **the address of a label is where the label
is**. `find-label` IS the linker in this model, so

    lea r (rip+label n)  ⇒  r := <resolved location of label n>

and `call`/`ret` are left EXACTLY as they are — they are already faithful
(push `pc+1`, jump to the value read; pop and jump back). `enc-sv
(SV-Code n)` becomes the resolved address, which means the encoding gains
a CODE MAP alongside the heap `AddrMap` it already carries (static, so
unlike the heap map it needs no extension lemmas).

### Rejected: resolve at `call`

Having `call` look its target up via `find-label` (making it consistent
with `c-jmp`) is a smaller diff, but it is a FICTION: real `call *mem`
jumps to an address and does not consult a label table. Every fiction in
the ISA model must be absorbed by `x86-64-loader-faithful`, which is the
bottom of the trust stack — this would GROW it, where resolving at `lea`
SHRINKS it (the model's `lea` then does what the assembler does).

### Rejected: full byte-level addresses

Modelling the program's real byte layout (address↔index map through the
whole ISA layer) is more faithful still and subsumes the parked
address-keyed-memory redesign, but it is a much larger change and is not
required to make code addresses coherent: at the model's granularity the
code address space IS instruction indices, and `find-label` maps labels
into it.

### Consequences

- `call`/`ret` semantics unchanged; one `execInstr` clause (`lea` of a
  label) changes; `enc-sv`/`sim-load-code-addr`/`block-step-load-code-addr`
  follow.
- The remaining Plan 0.63 work is unchanged in shape but now rests on a
  coherent address model: bodies into the modelled program, flat-machine
  call/ret with a return-pc stack, per-body frames.
- Shrinks what `x86-64-loader-faithful` must paper over — the same
  direction as bringing the prologue bracket and bodies inside the
  modelled pipeline.

## D082: Closure-Body Labels Get Their Own Provenance (`thunk`)

**Date**: 2026-08-03
**Status**: Accepted (design settled; execution = Plan 0.63 step 1)
**Relates**: D033 (provenance-typed labels), D081 (a code address is where
the label is), Plan 0.63

### Context

Modelling the closure call requires the callee's body to be findable in the
MODELLED program. The abstract `find-label : AbstractTrace → ℕ → Maybe ℕ`
scans for `instr-ctrl (c-label n)`, but `c-label n` lowers to
`label (once n)` → `.Lonce_n`, whereas the `lea` that CREATES a code
pointer renders `.L_thunk_n(%rip)` and `emit-thunk-body` emits
`.L_thunk_n:`. Marking body starts with plain `c-label` would make the two
sides disagree about the label's name.

### Decision

Give body labels their own provenance, mirroring D033's compiler/SigOp
split:

- `Label` gains `thunk : ℕ → Label`, rendering `_thunk_n` so the EMITTED
  TEXT IS BYTE-IDENTICAL to today's (`.L_thunk_n`) — the change is to the
  model, not to the binary;
- `FlatCtrl` gains `c-thunk : ℕ → FlatCtrl` (the body-start marker),
  lowering to `label (thunk n)`, with an abstract `find-thunk` beside
  `find-label`;
- a CALL resolves through `find-thunk`; a JUMP through `find-label`.

### Why (correct by construction)

`_≡ᵇᴸ_` is `false` across distinct provenances by its catch-all, so a call
target can NEVER match a jump label — definitionally, with no appeal to
counter uniqueness. That matters beyond tidiness: today main labels and
body labels happen to share one counter, so a unified `once` namespace
(the rejected alternative) would be collision-free only by that accident,
and would silently become unsound if bodies were ever given their own
counter. Provenance makes the property structural instead of incidental.

### Rejected: unify on `once`

Fewer constructors, but it changes the emitted label names, and it makes
collision-freedom depend on the shared-counter accident rather than on the
type. D033 rejected exactly this shape once already, for the compiler/SigOp
boundary.

### Consequences

- Plan 0.63 step 1 is now fully specified: `thunk` + `c-thunk` + `c-ret`
  constructors, their dispatch sweep, the `FlatState` extension
  (`mkFlatFull` + defaulted `mkFlat` wrapper, `fret` + `fclosure`), then
  bodies into `ir-to-trace`.
- No emitted instruction or label name changes, so existing binaries and
  the exit-test suite are unaffected by the model work.

## D083: A Pending Return Address Is a Code Address — It Relocates With the pc

**Date**: 2026-08-03
**Status**: Accepted (landed with Plan 0.63 step 1)
**Relates**: D081 (a code address is where the label is), D082 (`thunk`
provenance), Plan 0.63 step 1

### Context

Plan 0.63 step 1 gives `FlatState` a ghost return-pc stack (`fret`) and
`FlatCtrl` a `c-ret` that pops it. `CataAtRelocate` states the flat
machine's RELOCATION invariant: running an instruction in a big program
`prog` from a pc shifted by `k` equals running it standalone in the
segment `seg` and shifting the result — the bridge that splices a cata
algebra's standalone run into the embedded cata loop. The invariant was
`shift-pc k fs = record fs { fpc = fpc fs + k }`.

Adding `c-ret` breaks it as stated: a return jumps to an ABSOLUTE pc taken
off `fret`, and an unrelocated address does not move when the code does.

### Decision

`shift-pc` shifts the pending return addresses too:

    shift-pc k fs = record fs { fpc = fpc fs + k ; fret = shift-rets k (fret fs) }

with `shift-rets` an explicit recursion (not `map`) so it reduces on the
cons pattern and `flat-relocate-ret` stays `refl`.

### Why

A return address IS a code address, and relocating a program relocates
every code address in its state — that is what a linker does. The
alternative was to CONDITION `instr-reloc`/`relocate-steps` on the segment
being return-free, which would have (a) rippled a new premise through
`at-relocated-emits` and the cata assembly, and (b) been merely true-today
rather than true: step 2 puts closure bodies in the program, and a
relocated body's pending returns must land in the relocated copy.

`shift-pc` is local to `CataAtRelocate` (verified: no other module names
it), so the strengthening costs nothing downstream — every existing case
stays `refl`.

### Consequence: `c-ret` is scaffolding, not a fossil

`c-ret` joins `FrameFreeI`'s `⊥` set for now, with `instr-loop` /
`lea-indexed` / `instr-case-on-tag`. The set's meaning is "no emitted
trace contains this", which is TRUE of `c-ret` until step 2 emits the
bodies — but the reason is the opposite of a fossil's, and the clause
carries that comment. It is what routes `events-running-fetch`'s `c-ret`
case absurdly instead of adding a residual: the concrete `ret` pops the
machine stack while `do-ret` pops the ghost `fret`, and relating the two
is precisely step 2/3's new `FlatCorr` field. Step 2 deletes the clause
and supplies the real block-step.

`c-thunk` needs no such treatment — `block-step-c-thunk` is a pure pc bump
on both sides, a permanent theorem that does not depend on the
constructor being unemitted.

## D084: The Stack Pointer Is Represented Once — on the Frame, Not in the Registers

**Date**: 2026-08-04
**Status**: Accepted (landed)
**Relates**: D061 (0.61, frames are real), D083, Plan 0.63

### Context

The abstract machine carried the stack position THREE ways: `next-slot`
(compile-time frontier), `AllocState.current-frame`/`saved-frames` (0.61's
real frame stack), and `Registers.stackSlot` — a field whose own comment
read *"like rsp, but as slot count"* and whose design note called it
*"Runtime simulation state (mirrors rsp)"*.

The correspondence pinned each differently: `rsp-eq` tied `%rsp` to
`frame-base (current-frame …)`, `stack-eq`'s coverage bound read
`stackSlot`, and `run-stack-slot` existed only to prove the mirror equalled
the emitter's static budget. Making the window per-frame — which the closure
call forces — meant reconciling three facts about one physical register.

### Decision

Delete the mirror. The current frame's reserved slot count lives with the
frame stack, as `AllocState.frame-slots`, and `saved-frames` carries each
caller's beside its frame (`List (Frame × ℕ)`). `enter-frame`/`leave-frame`
update both together; nothing else can touch either.

### Why (this is a layering fix, not a rename)

Frames are a CODEGEN concept — the backend's `subq $budget*8` bracket. The
IR layer is frameless and reclaims slots by moving `next-slot`, and that is
right. The mistake was mirroring the codegen concept back INTO the abstract
machine's register file. 0.61 introduced the honest representation and left
the mirror beside it; this removes the redundancy.

Confirmed disjoint from slot reclamation before starting: `stackSlot`
appeared in the IR-WF layer only in COMMENTS, and `instr-reclaim-to` is
`s , record alloc { next-slot = n }` — the LocState passes through, so
reclamation could not touch the mirror by construction.

### Consequences

- **−421 lines net**, no new postulate, ConcFlatSim census unchanged at 6.
- `FlatStackSlot` 313 → 135 lines: proving a REGISTER field constant needed
  an induction over `exec-abstract` mutual with the nested walks; `frame-slots`
  is unreachable from `exec-abstract`, so every straight-line case is `refl`.
- `exec-abstract`'s frame ops became identity on the LocState, which makes
  the IR-WF layer's "alloc-stack only touches stackSlot" comments strictly
  more true. That layer needed no proof changes.
- `sim-push-frame`/`sim-pop-frame` and their block-steps DELETED — the `%rbp`
  frame model is a fossil, flagged deletable 2026-07-31. Removing the mirror
  broke their vacuity proofs, and writing fresh premises for dead code was
  the wrong alternative. `alloc-stack`/`dealloc-stack` are kept: `c-thunk`/
  `c-ret` compose from them.
- `Allocation.push-frame`'s `cap` argument, previously "retained for API
  compatibility but not stored", is now the frame's slot count.

### The gap it exposed — `stack-eq` covers ONE frame

`sim-dealloc-stack`'s post-bound used to be `stackSlot ∸ n`, which a
full-frame exit made `0`, so the obligation was VACUOUS. With the bound now
the restored frame's own `frame-slots`, the post genuinely has to describe
the CALLER's window — and the pre-state cannot supply it, because
`FlatCorr.stack-eq` only ever describes the current frame.

That is now an explicit `caller-window` premise with a note, not a vacuity.
**A real return correspondence needs `stack-eq` generalized to every LIVE
frame** — the clearest remaining obligation for the closure call. The
premises that stopped doing work (`entry`, `full`) were removed rather than
left for call sites to supply.

---

## D085: The Stack Correspondence Is Scoped Over Every Live Frame, With a Floor

**Date**: 2026-08-04
**Status**: TAKEN (landed — Plan 0.63, the obligation D084 exposed)

### The problem

`FlatCorr.stack-eq` described ONE frame, addressed off `%rsp`:

    stack-eq : ∀ k → k < frame-slots (falloc fs) →
      readMem (memory s) (readReg (regs s) rsp + slot-to-disp k)
        ≡ enc-maybe hv (stackMem (floc fs) (current-frame (falloc fs)) k)

That is exactly enough for straight-line code and not enough for a RETURN:
the epilogue restores the caller's frame, so the post-state must describe a
window the pre-state never mentioned. D084 turned that from a vacuity into an
explicit `caller-window` premise on `sim-dealloc-stack`; this closes it.

### Decision

`stack-eq` is scoped over the whole live frame stack —

    frames-of alloc = (current-frame alloc , frame-slots alloc) ∷ saved-frames alloc

— with each frame addressed by ITS OWN base rather than by `%rsp` (which
names only one), and the list carrying a FLOOR that is threaded along it:

    StackWindows am mem stk fl []             = ⊤
    StackWindows am mem stk fl ((f , b) ∷ fr) =
      (fl ≤ frame-base f) × Window am mem stk f b
        × StackWindows am mem stk (frame-base f + slots b) fr

with the initial floor the view's high-water mark `lo`. The current frame's
window is the head, recovered in the old `%rsp`-addressed form through
`rsp-eq` by the derived `stack-eq-cur` — so every straight-line consumer
(load/store-at-slot, restore-input, worklist-*, the tag-branch's stack route)
is a one-word change.

### Why a threaded floor, and not `All`

The plan's sketch was `All` over `frames-of`. Building it showed that a
per-frame predicate is NOT ENOUGH, and the missing content is frame
SEPARATION:

- a STACK store must leave the older frames' windows alone. With only a
  per-frame predicate nothing says the caller's cells are elsewhere, so the
  step is unprovable — and worse, for `slot ≥ frame-slots` the claim is
  FALSE: a store past its own reservation IS a store into the caller's
  window.
- a HEAP store must miss every live frame. The plan expected this from
  `sep`/`untouched`; those give "below `%rsp`", i.e. below the CURRENT
  frame's base only. Nothing in the correspondence said an older frame's
  base was also above `lo`.

The floor supplies both. Every frame's base is at or above the floor, and
the next (older) frame's floor is this frame's window END. Then:
heap writes are below `lo` ≤ every base (`dom-below` then `front-lo`), and a
stack write at `slot < b` is strictly below `frame-base f + slots b`, the
caller's floor. Both are theorems over the list, by the same transport
(`windows-above`).

### Consequences

- `sim-dealloc-stack`'s `caller-window` premise is a THEOREM
  (`windows-leave`: the epilogue drops the head, the caller's window is the
  tail) and is deleted from the signature, not left for call sites.
- The heap stores' `disj` premise stops doing work and is DELETED
  (`sim-store-indirect{,-suc}`, their block-steps, and `ptr-heap-disj` with
  them) — the disjointness is now derived, and for every frame rather than
  the top one.
- Three sites GAIN the frame discipline as a premise, because without it the
  statement is false: `sim-store-at-slot` (`slot < frame-slots`) and the two
  stack-pointer stores. Emitted code satisfies it already — the call sites
  supply `slot-read-in-frame` / `stack-ptr-current{,-suc}`, both existing
  theorems.
- `sim-alloc-stack` gains `slots n ≤ %rsp` — THE FRAME FITS. With truncated
  `∸`, `frame-base (shift cf n) + slots n` is `max (frame-base cf) (slots n)`,
  so without it the callee's window is not provably below the caller's and
  the list does not compose. The honest sibling of `heap-room` (stack
  overflow); it will be spent by `stack-room` when `c-thunk` gets its real
  block-step.
- `sim-alloc-heap`'s stack store-WF premise widened from the current frame to
  all frames — which is the form `FlatWF.wf-stack` already had, so the call
  site got SHORTER.
- No new postulate; ConcFlatSim census unchanged at 6.

### What it unlocks

`enter-frame` conses and `leave-frame` drops the head, so the frame moves are
now list operations on the evidence. That is precisely what `c-thunk`'s and
`c-ret`'s block-steps need, and it is why the closure call's correspondence
can be stated at all.

---

## D086: The Call Owns the Return-Address Slot — the Body's Marker Only Deepens the Frame

**Date**: 2026-08-04
**Status**: TAKEN (landed — Plan 0.63; corrects step 2a)

### The defect

Step 2a gave `c-thunk b` the flat semantics `enter-frame b`: shift the frame
`b` slots and push the caller's onto `saved-frames`. Checked against the
modelled ISA while sizing `block-step-c-thunk`, that is **off by one slot**.

`execInstr prog s (call target)` computes `newSp = sp ∸ slot-size` and stores
the return address there — the model is faithful to the hardware here — and
only THEN does the body's `sub rsp, 8b` run. So at the body's first
instruction the concrete `%rsp` is `base_caller − 8 − 8b`, while
`frame-base (shift-frame caller b)` is `base_caller − 8b`. `FlatCorr.rsp-eq`
(`%rsp ≡ frame-base (current-frame …)`) would have been unprovable at exactly
the step the closure call exists to justify.

Invisible today only because the markers have no producer.

### Decision

Split the frame move between the two instructions that actually move `%rsp`:

- the **CALL** enters the frame — shifting by the one slot its own push
  consumes, reserving NOTHING — and pushes the return pc onto `fret`;
- `c-thunk b` **GROWS** that frame (`grow-frame`: shift by `b`, reserve `b`,
  no push), mirroring `sub rsp, 8b`;
- `c-ret b` is unchanged: `leave-frame` restores the caller's frame wholesale,
  which is where `add rsp, 8b` followed by `ret`'s pop lands.

Each instruction's frame move now matches its own `%rsp` arithmetic.

### Why the push belongs at the call, not at the marker

Forced by an invariant already landed. `ConcFlatSim.RetMatch` requires
`saved-frames` and `fret` to have the SAME LENGTH — that is what lets a return
restore a slot count and a pc that belong together. The call pushes the return
pc; if the FRAME were pushed at the marker instead, the two stacks would differ
in length for every state between a call and its body, and the invariant would
be false there. One push per call, at the call, is the only consistent choice.

### The return-address cell belongs to no window

It sits between the callee's window END (`frame-base callee + 8b`) and the
caller's BASE, one slot wide. `stack-eq`'s frame list never claims it, because
D085 threads the next frame's floor as `≤`, not as an equality — the slack was
put there for the general case and this is what fills it. Nothing needed to
change in D085 to accommodate the call, which is the check that the two
decisions agree.

### Consequences

- `grow-frame` added beside `enter-frame`/`leave-frame`; `do-thunk` uses it.
  `enter-frame` keeps its `instr-alloc-stack` / `instr-push-frame` users.
- No behaviour change and no binary change (still no producer); census 6.
- The call's own half (`call-frame` + the `fret` push) lands with the wiring,
  where the target resolution (`fclosure` → `find-thunk`) is decided.

---

## D087: Resource Bounds Are Parameters, Not Postulates — the `--safe` Endgame

**Date**: 2026-08-05
**Status**: TAKEN (landed — `heap-room` done; `stack-room` will follow the same way)

### The fact that decides it

**`agda --safe` rejects EVERY postulate** (`SafeFlagPostulate`). Verified with a
one-line probe rather than assumed — the note at the Makefile's
`denot-safe-strict` target already said so, and the opposite belief had crept
into this work.

So the endgame for the correctness cone is not "fewer postulates" but ZERO,
with every honest assumption a MODULE PARAMETER — visible in the apex theorem's
type instead of invisible until someone audits.

### Decision

`heap-room` (and, when it arrives, `stack-room`) become PARAMETERS of
`ConcFlatSim`, supplied at the apex beside `conc-fuel`.

They are the same class as `conc-fuel`: a statement that a finite resource does
not run out. `conc-fuel` already lived at the apex; `heap-room` sitting inside
the correspondence was the outlier. After this the correspondence carries NO
resource postulate at all.

### What it forced

- **`RunContext` extracted** (`EntryLike`, `Reachable`, `Emitted`, `RunAt`). A
  module parameter's type is elaborated BEFORE the body, and the bound must
  stay conditioned on `RunAt` — unconditioned it is REFUTABLE (a view with
  `lo ≡ hfront` kills it), which is the 2026-07-30 vacuity lesson. So `RunAt`
  had to live one layer down.
- **Two different qualification forms in one type**, worth knowing before
  writing the next one: a parameterised module's ordinary names TELESCOPE its
  parameters (`RC.RunAt FS word-eq prog fs`), while its RECORD PROJECTIONS
  infer them from the record's own type (`FC.hfront hv`, not
  `FC.hfront FS word-eq hv`).

### Consequences

- ConcFlatSim census **6 → 5**. The apex gains `x86-64-heap-room`, so the total
  is flat — but the correspondence is now resource-postulate-free and the
  trusted base reads as one list in one place.
- `stack-room`, which Plan 0.63's closure frames need, NEVER ENTERS the census:
  it joins the same parameter. The earlier projection that 0.63 would end 6 → 6
  is superseded; it now ends at 4.

---

## D088: A Closure Body Must Be Emitted ONCE — the Inline Layout Is Unsound Under Cata

**Date**: 2026-08-05
**Status**: TAKEN (the finding is measured; the layout change itself is not yet
built — see plan 0.63)

### What the extraction gate found

The flip (`24b162e4`) moved closure bodies INTO the modelled program: the
`curry` clause of `ir-to-trace'` now emits

    <closure construction> ++ c-jmp end ∷ c-thunk this b ∷
    body-trace ++ c-ret b ∷ c-label end ∷ []

and `ir-to-bodies` returns `[]`. The Agda is green and every walk was
re-proved. The BINARY, run for the first time since, fails to assemble on all
three targets for four programs:

    layer5-cata-nat.s:332: Error: symbol `.L_thunk_10' is already defined
    layer5-cata-nat.s:342: Error: symbol `.Lonce_12'  is already defined

Read off the emitted assembly: lines 247–268 and 328–349 are the SAME closure
block — construction, `jmp .Lonce_11`, `.L_thunk_10:`, the body, `.Lonce_11:` —
emitted twice, verbatim.

### Why

`cata` SPLICES ITS ALGEBRA'S TRACE MORE THAN ONCE. `cata-trace-nat n l at` is,
definitionally,

    cata-nat-I₁ n l ++ at ++ (cata-nat-I₂ n l ++ at ++ cata-nat-I₃ l)

— `at` twice for nat, and the linear/branching strategies splice similarly. That
was harmless before the flip because the `curry` clause emitted NO LABEL AT ALL:
its trace was five construction instructions, of which `instr-load-code-addr
this-label` is a mere REFERENCE to the body. Duplicating a reference is fine.
The body — the DEFINITION — was emitted once, by `ir-to-bodies`, which walks the
IR and therefore visits each `curry` node once no matter how many times the
trace containing it is spliced.

The flip put four label-bearing instructions and the whole body inside `at`.
Splicing then duplicates DEFINITIONS, and duplicate labels are not assemblable.

**This is a property of the layout, not of any target.** It is invisible to the
proofs because nothing states that a compiled trace's label definitions are
unique — `LabelScope`/`LabelRange` bound where labels are MENTIONED and prove
jumps stay in segment; neither says a definition occurs once. (That gap is
worth closing on its own: it is exactly the invariant whose violation this is.)

### Decision

**The body is emitted once, hoisted out of the spliced region.** The layout
becomes the whole-program one:

    ir-to-trace ir = main-trace ++ c-jmp END ∷ all-bodies ++ c-label END ∷ []

with `ir-to-bodies` restored as the (IR-walking, hence once-per-`curry`)
producer of `all-bodies`, and the `curry` clause reverted to emitting only the
construction. Bodies stay in the MODELLED program — which is the whole point of
the flip, and what `events-running-call` needs — while their definitions are
placed by an IR walk rather than by trace splicing.

The handoff called this layout "an emitter-only alternative, traded away for
proof simplicity — revisitable". It is not an alternative: it is the only
layout in which the number of times a body is emitted is independent of how
many times its constructor's trace is spliced.

### The rejected alternative

**α-rename the labels in each cata copy.** Sound in principle, and there is
adjacent machinery (`CataAtRelocate`'s `instr-reloc`/`shift-pc` already
relocates pcs and, per D083, pending return addresses). Rejected on three
counts: it needs a label substitution over traces plus a preservation proof for
every walk that mentions labels; it multiplies emitted code by the splice count
(two or three copies of every closure body inside a cata); and it makes the
label counter's monotonicity — which `LabelRange` rests on — no longer a
property of `ir-to-trace'` alone.

### Consequences

- Plan 0.63's step 2b/2c/2d unit must be rebuilt on the hoisted layout. The
  four walk strengthenings, `SlotBudget`'s segmentation and `LabelScope`'s
  `segagree-curry` were all written against the inline layout; `segagree-curry`
  in particular exists BECAUSE the body sat inside a `c-thunk`/`c-ret` bracket
  in the middle of the parent's trace, and the hoisted layout removes that
  shape.
- `main` stays FIRST, so entry pc 0 / `EntryLike` / `pc-off` are untouched, and
  main's prologue bracket stays absorbed text (the parked `budget*8` item stays
  parked).
- The exit tests become a per-commit gate for anything touching the emitted
  trace, not a pre-merge one. Four green Agda clusters and a linking binary did
  not catch this; running it did.

---

## D089: A Label Is a Structured Identity, Not a Counter Value

**Date**: 2026-08-05
**Status**: TAKEN. Sub-step A LANDED 2026-08-05: the payload is `LabelId`
across the abstract machine, all three targets and every proof that names a
label, `owner` threaded from `cfName cf`, `path` still empty. Sub-steps B (the
splice paths — the actual duplication fix) and C (per-definition `idx` reset)
are not started; see plan 0.63.

### What broke

D088 recorded that `cata` splices its algebra's trace two or three times, so a
label DEFINITION inside it is emitted more than once, and concluded that
hoisting closure bodies would fix it. **That conclusion was wrong**, and the
probe that showed it is worth keeping:

    isEven = cata (case inl (case inr inl))          -- layer5-iseven.once

fails to assemble with `.Lonce_15/16/17/18/19` already defined, under BOTH
`--optimize` and `--no-optimize`, with **no closure involved at all**. Here the
algebra compiles to a direct `case` IR node, so `at` carries the `c-label`
definitions `IRToTrace:797–809` emits, and nat strategy splices it twice.

`git show 24b162e4` touched only the two `curry` clauses and one import line —
the `case` clause and `cata-dispatch` are untouched — so **this predates the
flip**. It has been latent since the cata codegen landed, hidden because
`layer5-iseven.once` has never carried an `-- Expected: exit N` line (checked
every revision back to Plan 0.28), so the exit-test runner silently skips it,
and because every COVERED cata test uses named user functions as algebras,
which closurise and so kept `at` label-free until the flip.

### The real defect

Uniqueness of labels was an artifact of a LINEAR TRAVERSAL: distinct
occurrences got distinct labels because a single monotone counter was consulted
in sequence. The cata emitter is not a linear traversal — it compiles the
algebra ONCE and emits the result TWICE. Both copies satisfy
`LabelScope.labels-in` (same range, same labels), because range containment is
closed under duplication.

So the missing invariant is not merely unstated: it is FALSE, and no
strengthening of the counter development recovers it while a subtree is emitted
more than once.

### Decision

The label payload becomes a structured identity:

    record LabelId : Set where
      field owner : CanonicalName   -- WHICH definition
            path  : List ℕ          -- WHERE inside it (splice-aware)
            idx   : ℕ               -- local counter within one context

    data Label : Set where
      once  : LabelId → Label
      sigop : String → ℕ → Label     -- unchanged
      thunk : LabelId → Label

Each component kills one collision source, and none depends on traversal
order. `owner` is the same `CanonicalName` the function symbol is mangled from,
so a label and its function agree by construction. `path` is extended at each
splice site, so `cata-dispatch` emitting its algebra twice yields two DIFFERENT
labels by construction. `idx` is the ordinary local counter.

The one structural consequence: **`at` becomes `List ℕ → AbstractTrace`** so
cata applies it at two distinct paths —
`I₁ ++ at (0 ∷ p) ++ (I₂ ++ at (1 ∷ p) ++ I₃)`. Every walk that proves `P at`
proves `∀ p → P (at p)` instead.

### What is NOT changed, and why

- **The provenance split stays** (D033, D082). `FlatComposition.find-thunk-pres`
  inducts over `HeadView`, where `hv-clabel` and `hv-otherlabel` exchange roles
  between the jump scan and the call scan, and its "can never match a `once`
  target" premise is `refl` because `_≡ᵇᴸ_` is `false` across CONSTRUCTORS.
  Folding provenance into `path` would turn those `refl`s into decisions over
  path contents for no gain. Only the payload becomes structured.
- **`sigop` stays**, unapplied though it currently is (SigOps lower to
  `call-sym`, and `ArithEnv = String → …` is symbol-keyed). It is load-bearing
  as a case in `FlatComposition`, it documents a namespace boundary that goes
  live the moment an arith block is addressed by label, and — the telling part
  — `sigop : String → ℕ → Label` was ALREADY identity-keyed. It was the
  counter-based `once`/`thunk` pair that was the outlier; `LabelId` makes the
  three uniform.
- **The abstract layer needs no provenance field.** Provenance already lives in
  WHICH constructor (`c-label` vs `c-thunk`) and WHICH lookup (`find-label` vs
  `find-thunk`); only `FlatCtrl`'s payload changes `ℕ → LabelId`.

### Equality

`_≡ᵇᴵ_` is `⌊ _≟ᴵ_ ⌋`, with `_≟ᴵ_` built from `_≟ᶜ_` (the equality the compiler
already trusts for definition identity), `≡-dec _≟_` and `_≟_`. Deriving it
from the decidable equality rather than hand-rolling a Bool recursion makes the
soundness the scans need (`≡ᵇᴵ-true`, consumed by `Flat.lab-eq`/`fl-go-lands`)
`toWitness` instead of fifteen lines of String/List boolean reflection.

### Consequences

- **D088 is re-graded**: hoisting closure bodies is NOT a correctness fix and is
  off the critical path. It remains available as a code-size optimisation (nat
  and linear would otherwise emit each closure body twice). The
  `LabelScope.segagree-curry` / walk-strengthening re-base D088 costed is not
  owed.
- `Compile.compileFunWithTarget`'s `l₁ ⊔ l₂` reconciliation (the comment at
  `Compile.agda:514–518` explaining why one counter must be shared between
  `irToAsm` and `irToBodies`) disappears: `owner` separates the definitions, so
  the counter can be local and reset per definition.
- `layer5-iseven.once` must gain its missing `-- Expected: exit N` line. It goes
  red until this lands, which is the honest state.

## D090: The Stack Window Is One-Directional, and Frame Entry Clears the Frame

**Date**: 2026-08-06
**Status**: TAKEN and LANDED. `Window` weakened, `SMCore.clear-frame` added and
wired into `do-thunk`, `fresh-x86` deleted, three "empty slot ⇒ concrete stuck"
lemmas deleted, `C.sim-thunk` and `block-step-c-thunk` PROVEN. Apex and all
three `ccc-*` clusters green; exit tests unchanged.

### What was wrong

`FlatCorrespondence.Window` was BIDIRECTIONAL:

    Window am mem stk f b = ∀ k → k < b →
      X.readMem mem (frame-base f + slot-to-disp k) ≡ enc-maybe-at am (stk f k)

Because `enc-maybe-at am nothing ≡ nothing`, the equation also constrained the
EMPTY case: it demanded the CONCRETE cell be unmapped wherever the abstract one
was unwritten. That is false the moment a closure is applied twice at one depth.
`lo` (the stack high-water mark) only ever DESCENDS, so the second entry
re-enters a frame at or above the mark, over the previous incarnation's live
data. The hardware clears nothing.

So `Window` was unprovable at frame entry, which is precisely what blocked
`block-step-c-thunk` — and no freshness side-condition could rescue it, because
the concrete cells genuinely are dirty. The earlier handoff's "DO NOT build
`block-step-c-thunk`, the premise is FALSE" was a correct reading of a wrong
statement.

### Decision, first half — claim only where the abstract side wrote

    Window am mem stk f b = ∀ k → k < b → ∀ v → stk f k ≡ just v →
      X.readMem mem (frame-base f + slot-to-disp k) ≡ just (enc-sv-at am v)

A match is claimed only at WRITTEN abstract cells. Frame entry becomes VACUOUS
(a fresh frame has written nothing), so `fresh-x86` — the false premise —
disappears from `sim-alloc-stack` and `block-step-alloc-stack` outright.

### Decision, second half — `do-thunk` CLEARS the entered frame

Weakening alone is not enough: the callee window is vacuous only if the ABSTRACT
frame is fresh, and `fresh-abs` fails for the mirror-image reason `fresh-x86`
did. A re-entered `shift-frame cf b` keeps the previous incarnation's abstract
writes too. Postulating it would have been assuming something FALSE.

So the fix goes in the machine, not in a premise (`SMCore.clear-frame`, wired
into `Flat.do-thunk`): entering a body clears its reserved slots, and freshness
holds BY COMPUTATION. Both `sim-thunk` and `block-step-c-thunk` now take no
freshness premise at all.

**The two halves are a matched pair; neither is sound alone.** The clear is
sound against hardware that clears nothing PRECISELY because `Window` is
one-directional — a cleared abstract cell asserts nothing about the stale
concrete one. Under the old bidirectional statement the clear would have been a
lie about memory.

### What the old statement was HIDING

Three lemmas were DELETED rather than re-proved: `slot-empty-stop`,
`load-indirect-stack-empty-stuck`, `load-indirect-suc-stack-empty-stuck`. Each
said "abstract slot empty ⇒ concrete stuck". The bidirectional `Window` supplied
that for free, and it is FALSE: the concrete machine reads whatever the previous
frame left behind while the abstract machine halts. That is a genuine
DIVERGENCE, not a proof gap — the old statement made both sides "agree" by
getting stuck together.

Their routes are made UNREACHABLE instead, by two arguments, NEITHER a
postulate:

- **slot reads** — `site-ok` now requires a non-`e-any` claim at every
  `load-from-slot` / `restore-input` / `worklist-pop`, and `MeetsSlot` sends a
  claim at an unwritten slot to `⊥` (`ShapeTable.not-any`,
  `ShapeTable.Sem.site-slot-written`, `ConcFlatSim.slot-read-written`). The
  emitter's own discipline rules the read out.
- **pointer reads into stack slots** — heap mode admits no stack pointer at all
  (`FlatStackPtr.stack-ptr-live` / `stack-ptr-suc-live`), which the code already
  relied on for the sibling `k<ss` component.

The postulate COUNT is unchanged at 11: `emitted-shape-check`'s CONTENT grew by
the `site-ok` conjunct, which is exactly the shape the plan called for.

### New lemmas, and why they are cheap

- `SMCore.clear-frame-just` — "clearing only forgets".
- `FlatCorrespondence.windows-forget` — a store that only forgets preserves
  every window. A direct payoff of one-directionality (a constraint on written
  cells cannot be invalidated by removing values), and it is why the saved
  frames ride across a frame entry with NO frame-distinctness argument.
- `FlatCorrespondence.windows-lower` — floor monotonicity, for re-anchoring the
  saved frames below the grown window.

### The ripple, and its shape

`do-thunk` now moves the `LocState`, so every flat-machine invariant whose
`c-thunk` clause was `= wf` must REBUILD its record — the record is indexed by
the whole `LocState`, so `wf` no longer typechecks even where the fields read
only `regs`. Four modules: `FlatStoreWF` (`wf-thunk`), `FlatRegTagWF`,
`FlatStackPtr` (`sp-thunk`), `FlatPtrBounds` (`pb-thunk`). In each the cleared
cells are discharged by the predicate's own `nothing` case being trivially true
(`svm-below _ nothing = ⊤`, `StackPtrOK? nothing = ⊤`, `PtrB? _ nothing = ⊤`) —
the clear can only make these invariants easier.

### Consequences

- `events-running-thunk` is UNBLOCKED (ledger #8). One input remains: a
  `stack-room` resource PARAMETER (sibling of `heap-room`, supplying
  `hfront hv ≤ lo'`), with `lo'` chosen at the dispatch site as
  `lo hv ⊓ (rsp ∸ slots b)`.
- `events-running-ret` is unblocked by the same fix but still needs the
  `FlatCorr` component relating the ghost `fret` to the machine stack.
- `events-running-call` is untouched: it is a MODEL GAP (`exec-abstract
  instr-call-closure` is the identity while `call *0x8(%r12)` transfers
  control), not a layout problem.

### FOLLOW-ON (2026-08-06): `events-running-thunk` DISCHARGED

The first of the three genuine correspondence gaps is now a theorem
(`ConcFlatSim.thunk-step`), which is what D090 was for. Two choices in the
assembly are worth recording:

**The new high-water mark is a MEET**: `lo' = lo hv ⊓ (%rsp ∸ 8b)`, not either
side alone. `lo` must not RISE — it is the lowest `%rsp` ever held, and
`untouched` over `[hfront, lo)` would otherwise claim a deeper earlier frame's
written cells are unmapped. And it must not exceed the new `%rsp`, or the frame
just reserved would sit inside the region called virgin. The two premises
`lo'≤lo` and `lo'≤rsp` are then exactly the two meet projections, and
`front-lo'` is `⊓-glb` of the view's own `front-lo` and the resource fact.

**`StackRoom` is stated ADDITIVELY** — `hfront hv + slots b ≤ %rsp` — not as its
two consequences. The block-step needs both `slots b ≤ %rsp` (the `sub` does not
underflow) and `hfront ≤ %rsp ∸ slots b` (the frame stays above the heap), and
truncated subtraction means the second does NOT imply the first. Stating them
apart would be two parameters where the additive form is one — and the additive
form is what a linker sizing pass would actually establish. It is the exact
mirror of `HeapRoom`'s `hfront + slots n ≤ lo`: the two bounds guard the two
ends of the same virgin region.

`ccc-step-bs` needed NO generalisation, which is worth knowing before someone
tries: `BlockStepAt hv hv'` discards `hv` definitionally, so a view-CHANGING
step already typechecks against `BlockStep hv'`. The only care needed at the
call site is to leave `hv'` to inference rather than pinning it to the pre-view.

## D091: The Return Correspondence Is Blocked BY the Call, Not Beside It

**Date**: 2026-08-06 · **Plan**: 0.54 rung D · **Status**: landed

### The claim

`events-running-ret` cannot be discharged before `events-running-call`. It is
not a second, independent correspondence gap that happens to sit next to the
call gap — it is the SAME gap seen from the other end, and the previous plan for
it (a `FlatCorr`/`CompiledCorr` component relating the ghost `fret` to the
machine stack, plus a divergence argument for the empty case) rests on two
premises that are both false in today's machine.

### The theorem that shows it

    ConcFlatSim.run-no-ret : ∀ prog fs → RunAt prog fs
                           → (fret fs ≡ []) × (saved-frames (falloc fs) ≡ [])

In EVERY reachable state of an emitted program, both the ghost return stack and
the saved-frame stack are EMPTY. `instr-call-closure` is the only pusher and its
abstract semantics is the identity (`exec-abstract instr-call-closure s alloc =
s , alloc`); every other step either leaves both alone (`flat-same-frames` for
the frame-free ones, `grow-frame` for `c-thunk` — D086 puts the push at the
call, so the marker moves the CURRENT frame only) or pops them (`c-ret`).
`EntryLike` starts both empty.

So no reachable state owes a return, and no closure body is ever entered.

### The two false premises this kills

**"At the outermost return `fret` is genuinely empty, and that is the program
exiting."** There is no outermost return. `ir-to-trace` emits `c-ret` in exactly
one place — the `curry` clause's inline body, `c-jmp end ∷ c-thunk ℓ b ∷ body ++
c-ret b ∷ c-label end ∷ []` — and main's own trace ends by running off the end
(`events-running-end`), not by returning. Every `c-ret` in an emitted trace is a
BODY's, reachable only through a call.

**"The `fret`↔stack component is carried like `rsp-eq`."** It is not preserved
by `c-thunk`. The cell holding the pending return address is the current frame's
window END, `frame-base + slots frame-slots`; `grow-frame b` moves the base down
by `slots b` and SETS `frame-slots := b`, so the end is preserved only when the
pre-state reservation is 0 — true of a frame a CALL just entered (D086), false
of the caller's frame the marker currently deepens. In today's machine that cell
is the caller's slot 0, which the emitter writes (`store-at-slot closure-slot`)
just before the marker. Nor can the empty case claim the cell is UNMAPPED, for
the same reason. Assuming either would have been the `fresh-x86` mistake again:
postulating something the machine makes false.

### What landed instead

`events-running-ret` is DELETED as a postulate. Its dispatch clause is the
theorem `ConcFlatSim.ret-step`, which derives `⊥` from a collision:

    ret-site-owes  (new residual) : a reachable `c-ret` site owes a return —
                                    landing there means a call entered a body,
                                    and a call pushes the return pc (D086)
    run-no-ret     (theorem)      : nothing ever owes a return

Note the new residual's TYPE mentions no `X.State`: by the ledger's own test it
is an obligation about the ABSTRACT machine, not a correspondence gap. Genuine
correspondence gaps: 2 → 1 (`events-running-call` alone).

### The honest cost, stated plainly

The pair is stronger than the postulate it replaces: it makes the cone
INCONSISTENT if a `c-ret` site is ever reachable, where the old postulate would
merely have been false there. That is a deliberate trade — it states the
assumption sharply enough to be attacked — and it rests on the emitter's `c-jmp
end` guard, which is what stops a parent falling into a body.

Two discharge routes, both real:

1. **CFG confinement** (today's machine): prove no reachable pc lies in a body
   region — the `LabelScope.emitted-jump-in-segment` mould. That DELETES
   `ret-site-owes` outright, replacing it with the `⊥` directly.
2. **Model the call** (`events-running-call`): then `instr-call-closure` pushes
   `fret`/`saved-frames`, `run-no-ret` STOPS TYPECHECKING — which is the check
   that the model really changed — and `ret-site-owes` becomes provable from the
   same push, with the return correspondence provable alongside it.

### Consequence for the plan queue

The agreed order (`ret` → `call` → merge) inverts: the call is the only genuine
correspondence gap left, and it is what unblocks the return. Plans 0.65/0.66
were already gated on both.

## D092: The Call Is Modelled — Control Transfer Belongs to the Flat Machine

**Date**: 2026-08-06 · **Plan**: 0.54 rung D · **Status**: landed (machine side)

### The change

`exec-abstract instr-call-closure s alloc = s , alloc` — the identity — was the
last MODEL GAP in the correspondence cone (D091 showed it was also what blocked
the return). It stays the identity: the structured layer has no pc to transfer.
Control transfer is the FLAT machine's business, exactly as jumps and returns
are, so `flat-exec-instr` now has real clauses for both closure instructions:

    instr-save-closure-reg  ↦  do-save-closure  — `fclosure := Input1`
    instr-call-closure      ↦  do-call          — the transfer

`do-save-closure` is not cosmetic. `fclosure` (the abstract mirror of `%r12`,
which the concrete `call *0x8(%r12)` dereferences) had NO writer at all, so
without it every modelled call would have found the entry filler and halted —
a call that never fires is not a model.

`do-call` mirrors the hardware: the closure record's SECOND cell holds the code
address (`heapMem (sucHL hl)`, a `SV-Code ℓ` written by `instr-load-code-addr`);
the body's entry is `find-thunk prog ℓ` — the CALL's scan (D082), not
`find-label`; the return pc `suc (fpc fs)` goes on the ghost `fret` and the
caller's frame on `saved-frames`, ONE push each. Anything malformed HALTS, as
`do-jump nothing` does. Enumerated, `with`-free.

### `enter-call`, and why it is not `enter-frame 1`

The concrete `call` decrements `%rsp` by one slot and stores the return address
there. So the frame entered is shifted by one slot and RESERVES NOTHING:

    enter-call alloc = record alloc { current-frame = shift-frame … 1
                                    ; frame-slots   = 0
                                    ; saved-frames  = (current-frame , frame-slots) ∷ … }

`enter-frame 1` would claim the return-address cell as the callee's slot 0 —
putting a code address inside the callee's window and breaking `StackWindows`'
floor thread the moment the caller reserved two slots. This is D086 as code.

It also fixes the cell the correspondence will need: the entered frame's window
END (`frame-base + slots frame-slots`) IS the cell the call pushed, and
`grow-frame` keeps it there because the entered frame reserves 0. That is
precisely what was NOT true before (D091's second false premise) and is what
makes the `fret`↔stack component preservable at last.

### THE ONE EXCEPTION THE INVARIANT GREW

`SegWF.seg-cur` said "the current frame's reservation IS the static segment at
the pc". A call lands on a body entry with reservation 0 while the positional
scan still reads the CALLER's segment — bodies are spliced inline, so the scan
walks straight into them. So the invariant is now a DISJUNCTION (`SegCur`):
either the equation, or "the pc holds a `c-thunk` and the reservation is 0".

Two rejected alternatives, both instructive:

- **Give the entered frame the scan's value.** Physically false, and it breaks
  the window floor thread — the callee's window would overlap the caller's.
- **Weaken to "…or the frame is empty".** True but USELESS: a consumer cannot
  refute it. The exception must be stated so that its refutation is available
  where the invariant is used, and every consumer is a slot read, so naming the
  pc's instruction does exactly that (`slot-of (instr-ctrl _) = nothing`).

This needed `Flat.find-thunk-sound` — what the call scan finds IS a body entry
for that label — which the `events-running-call` proof will need anyway. `ft-go`
became `with`-free to admit it (the module's own design rule).

### The ripple, and what the backstop caught

`instr-call-closure` left `FrameFreeI` (it moves the frame) while staying in
`EmittableI` (it is emitted) — the same split the closure markers took in 0.63.
Five flat-machine invariants gained a real case; each is two lines, because the
call writes no store and `enter-call` is a record update on the frame fields.
The twelve-row dispatch is enumerated ONCE, as `CallPost`/`callView`, and every
consumer takes the read-back equation.

The ISLAND BACKSTOP earned its keep again — two modules outside every cluster:

- `StraightTrace` — `StraightIR apply` was silently `⊤` in the catch-all. Now
  that the call transfers control, `apply` is not straight. Third instance of
  the identical pattern (`case` and `curry` were the first two).
- `CataAtRelocate` — relocation now needs a SECOND embedding fact: the call
  resolves a label through the call scan, so `find-thunk` must relocate like
  `find-label`. Was `refl` while the call was a no-op.

### Where this leaves the residuals

`events-running-ret` is BACK as a postulate (deleted 2026-08-06, restored the
same day — see D091 for why the round trip is the point) and
`events-running-call` remains one, but both changed CLASS: they are no longer
model gaps. Both sides of each equation now describe the same transition, and
`FlatComposition.find-thunk-pres` already supplies the concrete side of the
transfer. What is left is the DATA — the `CompiledCorr` component relating the
ghost `fret` to the pushed cells — plus its ~37-site ripple in `FlatSimulation`.

`run-no-ret` is DELETED, as D092 predicted it would have to be: it said no state
ever owes a return, and that was only true while the call did nothing. Its
ceasing to typecheck is the check that the model really changed.

## D093: The Return-Address Component — the Ghost Stack Is Really in Memory

**Date**: 2026-08-06 · **Plan**: 0.54 rung D · **Status**: landed (the component)

`CompiledCorr` gains one field:

    ret-eq : RetAddrs (x86-off prog) (memory s) (frames-of (falloc fs)) (fret fs)

`fret` is a GHOST list — the abstract memory is frame/slot-keyed and has no
byte-addressed pushdown — and until now nothing related it to the machine. This
field does, at the same block-offset translation the pc uses, and it is what
turns a return from an assumption into a step.

### Where the cells are, and why the pairing starts at the CURRENT frame

One cell per pending return, none of them in any window: each is the slot the
CALL consumed, sitting at the callee frame's window END — between the callee's
last slot and the caller's base. That gap is the slack `StackWindows`' floor
leaves (it is a `≤`, not an equality), and this component is what finally says
what lives in it.

Pairing `fret` with `frames-of` (current frame first) rather than with
`saved-frames` is what makes a RETURN carry: after `leave-frame` the new head is
the old second, whose cell the tail already describes, and `add rsp,8b ; ret`
writes no memory at all. The alternative anchoring (each saved frame's base
minus a slot) makes `c-thunk` free but costs an equality at the return — this
way round, one site pays and the other is definitional.

### D092 is what made it preservable

The earlier attempt at this field would have assumed something FALSE (D091's
second premise). `enter-call` fixes it: the frame a call enters reserves 0, so
its window END is exactly the cell the call pushed, and `grow-frame` keeps it
there. Hence the new `empty-frame` premise on `block-step-c-thunk` — the marker
lands the end back on the frame's own base only if it started there.

### The ripple, by kind (~37 sites)

- **straight-line**: definitional, once the two generic helpers take `RetSame`.
  They are polymorphic in the instruction, so they cannot see that a step moves
  no frame — the same reason they already take `fpc-eq`.
- **stack stores**: the write is inside the frame's window (`slot <
  frame-slots`, the emitted-code discipline) and the head's cell is the window
  END, one slot above the last slot it can reach (`ret-write-in-frame`).
- **heap stores**: the whole heap is under `hfront ≤ lo ≤ %rsp`, hence under
  every return cell (`ret-agree-above`, mirroring `windows-above`).
- **`c-thunk`**: re-anchors the head (`ret-head`).
- **the two unemittable frame ops**: take the post-state component as a premise.
  They have no caller, and only a matched prologue/epilogue producer — which
  `ir-to-trace` never emits — could discharge it.

### The new residual, and its route

`thunk-entry-empty` — a reachable body entry has an empty reservation. No
`X.State` in the type, so it is an abstract-machine obligation, not a
correspondence gap. Discharge: a `SegWF`-style induction over two emitter facts
in the `emitted-jump-in-segment` mould — a body entry is never a FALL-THROUGH
target (the emitter's `c-jmp end` guard is exactly what stops the parent falling
in) nor a JUMP target (`find-label` resolves `c-label`s, a different provenance,
D082). Then the only way in is the call, which sets `frame-slots := 0`.

### WHAT THE RETURN PROOF STILL NEEDS (designed, not built)

Three things, and they are known:

1. **The exact gap, not just the floor.** `rsp-eq` at the post-state needs
   `frame-base cur + slots frame-slots + slot-size ≡ frame-base f₀` — an
   EQUALITY where `StackWindows` threads only `≤`. It is true by construction
   (`enter-call` shifts by exactly one slot) and preserved by `c-thunk` under
   the same `empty-frame` premise. Best home: a `GapNext` conjunct inside
   `RetAddrs`' cons row — the gap and the return address are THE SAME SLOT, so
   they should travel together, and the ~37 sites then carry both at once.
2. **`C.sim-ret`** — the data correspondence for `add rsp,8b ; ret`: registers
   untouched but `%rsp`, memory untouched, and the post-state's `stack-eq` is
   the TAIL of the pre-state's, re-anchored (`windows-leave` already exists).
3. **The bracket fact**: at a `c-ret b` site, `b` IS the reservation in force
   (`ir-to-trace'` emits `c-thunk ℓ bb … c-ret bb`). Same emitter family as
   `thunk-entry-empty`; both should be discharged together.

The concrete side is already in hand: `x86 ret` reads `[%rsp]`, and after the
`add` that address is exactly the head cell this component describes.

## D094: Every Way Into a Closure Body, Refuted — the Body-Entry Invariant

**Date**: 2026-08-06 · **Plan**: 0.54 rung D · **Status**: landed

`thunk-entry-empty` — a reachable body entry has an empty reservation, the
input D093's return-address component needs — was a postulate for exactly one
commit. It is now `SegWF.seg-entry`, a projection of the run invariant, proved
by the same induction that carries the segmented budget.

### The argument is exhaustive by construction

A state whose pc holds a `c-thunk` got there somehow, and `Reachable` enumerates
the ways. Each is refuted by a fact that already existed or is cheap:

| arrival | refutation |
|---|---|
| ENTRY (pc 0) | a body entry is never at position 0 — a guard precedes it |
| FALL-THROUGH | the emitter puts a `c-jmp` immediately before a body entry, and the instruction that fell through is not one |
| JUMP | `find-label` resolves `c-label`s, so a jump lands on a `c-label` |
| RETURN | its address is one past a CALL, and a call is not a `c-jmp` |
| CALL | — this is the case that PROVES it: `enter-call` reserves nothing (D086) |

### What each refutation cost

**`NotJmpI`**, carried by exactly the two rows that fall through: `PcView.pv-suc`
and `JumpPost.jp-suc`. Putting the witness on the CONSTRUCTOR rather than
splitting `PcView` is what kept this small — a `c-jmp` never produces `jp-suc`
(`dj-aux` has no fall-through row), so the branches carry `tt` and the jump
needs no special case.

**`Flat.find-label-sound`** — the mirror of D092's `find-thunk-sound`, and the
same shape: `fl-go` became `with`-free so the proof reduces under a hypothesis
about the head. This is D082's disjoint provenances paying off a second time:
the two scans cannot land on each other's instructions, so "a jump never enters
a closure body" is a THEOREM, not a codegen assumption.

**`RetMatch`'s provenance witness** — `rm-∷` now records that a pending return
address is `suc q` with a CALL at `q`. The call is the only pusher, so the
witness is free at the push and rides everywhere else. It says a return lands
after a call site rather than anywhere, which is what rules out landing on a
body entry.

### What is left, and why it is the right shape

One codegen-class postulate:

    emitted-thunk-guarded : fetch (ir-to-trace ir) p ≡ just (c-thunk ℓ bb)
                          → Σ q → (p ≡ suc q) × Σ m → fetch … q ≡ just (c-jmp m)

Only `ir-to-trace` appears in its type — no `X.State`, no `FlatState`. It is
the emitter's own guard, stated: `ir-to-trace'` emits `… c-jmp end ∷ c-thunk ℓ
bb ∷ body …`, and that jump is exactly what stops the parent falling into the
body. Both halves come from one Σ: `p ≡ suc q` rules out the entry pc and the
fetch at `q` rules out every fall-through.

Its discharge is a structural induction over `ir-to-trace'`, and the shape that
keeps it small is worth recording before someone starts:

- carry the PREVIOUS instruction (`GuardedFrom prev t`), so the head's
  obligation is local;
- every clause's trace is prev-POLYMORPHIC, because no emitted trace BEGINS
  with a body entry — that is what makes the `++` splice lemma compose;
- a `NoThunks` decider collapses every clause that emits no body entry to
  `refl`, which is most of them including the cata walks;
- the one interesting adjacency lives inside a single literal list in each
  `curry` clause, so it needs no boundary reasoning at all.

Take the `c-ret` bracket fact (its budget IS the reservation in force) in the
same module: one induction, two consumers.

## D095: The Return Correspondence, and What the Call Still Needs

**Date**: 2026-08-06 · **Plan**: 0.54 rung D · **Status**: return LANDED

`events-running-ret` is discharged. `c-ret b` ↔ `add rsp, 8b ; ret` is proved
end to end (`ConcFlatSim.ret-step` over the new `block-step-c-ret`), and every
piece comes from D093's component:

| what the step needs | where it comes from |
|---|---|
| the ADDRESS the `ret` reads | `rsp-eq` + the bracket ⇒ `add rsp,8b` lands on the window END |
| the VALUE there | `RetAddrs`' head: `x86-off prog rpc` |
| `%rsp` after the pop | `GapNext`: the caller's base is one slot above that cell |
| the post-state's component | the pre-state's TAIL — `frames-of (leave-frame alloc)` IS `saved-frames alloc` |

### `GapNext` belongs in the component, not in `StackWindows`

The return needs the one-slot separation as an EQUALITY; the floor thread gives
only `≤`. Putting it in `RetAddrs`' cons row means it travels with the very slot
it describes — the return address and the gap ARE the same slot — and the ~37
carriers needed no change at all, only the three transports.

### What replaced the gap

Two facts about the ABSTRACT machine, neither mentioning `X.State`:
`ret-site-owes` (a reachable `c-ret` owes a return — D091's statement, now
true-and-provable because the call is modelled) and `ret-budget-matches` (the
released budget IS the reservation in force — `ir-to-trace'` writes one `bb`
twice). Both route through the same emitter induction as
`emitted-thunk-guarded`.

### THE CALL'S BLOCKER, located: D081 is a FICTION in the trusted semantics

    Semantics.effectiveAddr s (rip+label n) = idx n   -- "resolved by linker"

A code address encodes as the LABEL NUMBER. `instr-load-code-addr ℓ` writes
`SV-Code ℓ`, `enc-sv-at am (SV-Code ℓ) = idx ℓ`, and the concrete `lea rax,
.L_thunk_ℓ(%rip)` produces the same number — so those two agree today, which is
exactly why the fiction has survived. But `call *0x8(%r12)` then JUMPS to that
number, while the body sits at `x86-off prog j` for `find-thunk prog ℓ ≡ just j`.
`idx ℓ ≡ x86-off prog j` is false, so no proof of `events-running-call` exists
while the fiction stands. This is D081's open question, owned by this gap
exactly as `FlatCorrespondence`'s comment says.

**The fix makes the model MORE faithful, not less**: a real linker DOES resolve
`.L_thunk_ℓ(%rip)` to the body's address, so `execInstr prog s (lea r (rip+label
ℓ))` should resolve through `X.find-label prog (thunk ℓ)` — the program is
already in scope there — and halt when absent, as `jmp` does. Then
`FlatComposition.find-thunk-pres` (already proven) bridges the abstract scan to
that resolution modulo `x86-off`, which is precisely the call's jump target.

Cost, measured rather than guessed:

- one clause in `…X86-64.Semantics` (the `lea` of a `rip+label`);
- the ENCODING must carry a code map: `AddrMap` is `HeapLocation → ℕ` today and
  `enc-sv-at am (SV-Code n) = idx n` cannot see one. ~56 `haddr hv _`
  applications and ~37 `enc-*-at` sites — mechanical, but it is the encoding
  layer of the whole correspondence;
- the call's own block-step: it WRITES memory (the pushed return address, which
  EXTENDS `RetAddrs` with a new head), pushes a frame, and needs one resource
  premise (`slot-size ≤ %rsp` — room for the return address, a `StackRoom`-class
  parameter per D087);
- `GapNext` for the new head is then `frame-base cur ∸ slot-size + slot-size ≡
  frame-base cur`, the same no-underflow fact that premise supplies.

## D096–D098: The Correspondence Gaps Are Closed

**Date**: 2026-08-06 · **Plan**: 0.54 rung D · **Status**: landed

`events-running-{thunk,ret,call}` — the three genuine correspondence gaps this
branch set out to attack — are now all THEOREMS. No `events-running-*` postulate
remains in the cone.

### D096: a code address is an ADDRESS

    effectiveAddr s (rip+label n) = idx n     -- "resolved by linker"

`idx` is a FIELD of `LabelId` (D089) — the label's identity, no position in
anything. The machine is index-addressed (`pc` is a position, `find-label`
returns one, `jmp`/`je`/`ret` move `pc` to one), and `Semantics.agda`'s header
asks the reviewer to compare each clause against the Intel SDM, where `LEA`
yields the referenced location's address. So this was a DEFECT, not an
abstraction — and a consequential one: `call *0x8(%r12)` jumps to a value that
came from this `lea`, so model and hardware parted company on any program that
applies a closure, which made `x86-64-loader-faithful` false for those programs.
The fiction was hiding inside the trusted axiom. It went unnoticed because until
D092 the abstract call was the identity, so nothing used the value as an address.

The repair follows the model's own convention (and CompCert's `Asm.v`, which
the header names): `lea r (rip+label ℓ)` RESOLVES through `find-label prog
(thunk ℓ)`, halting when absent, exactly as `jmp` does. `AddrMap` gained a code
map so `SV-Code` can encode to a resolution at all; `CompiledCorr.code-eq` ties
that map to the program.

### D097: the correspondence tracks `%r12`

`FlatCorr.r12-eq` — the concrete closure register mirrors the flat `fclosure`.
It went untracked because nothing READ it; the call does. One consequence worth
its own invariant: the register's ENCODING must survive an allocation extending
the view, and `enc-ext` wants the value below the frontier — `fclosure` is a
`FlatState` field, so `StoreWF` says nothing about it. Hence
`FlatInv.inv-closure`, preserved by `FlatStoreWF.cl-step`.

### D098: the call

`C.sim-call` + `block-step-call` + `ConcFlatSim.call-step`. The written cell is
below every live frame's base, so nothing already corresponded to it: the
entered frame's head window is vacuous (it reserves nothing, D086) and the
caller's windows are untouched by a write under them. The two label scans agree
by `find-thunk-corr`; the pushed address is `x86-off prog (suc (fpc fs))` on
both sides by `x86-off-suc`.

### What the correspondence now rests on

Nothing in the cone is a model gap. What is left, by class:

- **abstract-machine / codegen** (no `X.State` in the type): `call-site-shape`,
  `ret-site-owes`, `ret-budget-matches`, `emitted-thunk-guarded`,
  `emitted-code-addr-has-body`, `emitted-shape-check`, `run-meets`. The first
  five are one emitter induction over `ir-to-trace'` away — the shape is written
  up in D094.
- **CPU-model stubs**: `arith-sigop-contract`, `external-sigop-contract`,
  `conc-fuel` — all three conditioned on the three UNDEFINED functions in
  `Once.Adequacy.CPU.X86-64`. A DEFINITION task, not a proof task.
- **resource parameters** (D087, not postulates): `program-bound`,
  `x86-64-heap-room`, `x86-64-stack-room`, `x86-64-call-room`, `entry-frame`.
- **boundary axioms**: `stack-top-in-stack`, `x86-64-loader-faithful`.
- **frontend**: `main-heap-moded`.

The pattern worth keeping from this rung: every one of the three gaps closed by
fixing the MACHINE rather than by assuming harder — the call was modelled
(D092), the window was made one-directional and the frame cleared (D090), the
code address was made an address (D096). Each time the "unprovable" statement
turned out to be a true statement about a machine that was not yet being
modelled correctly.

## D100: The Invariant the Axiom Was Hiding — Distinct Emitted Labels

**Date**: 2026-08-09 · **Plan**: 0.54 rung D · **Status**: landed (wiring);
the discharge is a named residual

D099 named the DEFECT: `cata-{nat,linear}` splice the algebra trace TWICE
(`I₁ ++ at ++ (I₂ ++ at ++ I₃)`) under ONE label range, so both copies carry the
same labels and `as` refuses the file:

    layer5-cata-nat.s:332: Error: symbol `.L_thunk_once_4main_10' is already
                                  defined

This entry is the INVARIANT — the reason a green tree shipped a binary the
assembler rejects, and the wiring that makes the same class of defect a type
error next time.

### Why no proof caught it — three independent reasons

1. **The model gives a duplicate-label program a perfectly good meaning.**
   `find-label` is a FIRST-MATCH scan on all three arches, and the flat machine
   resolves labels by the same first-match scan. With `.L…_10` defined twice
   both machines pick the same one, so `conc-flat-sim` is TRUE. No theorem below
   the toolchain boundary could have been false; no strengthening of the
   top-level statement could have forced uniqueness.

2. **The only layer that rejects duplicates is `as`, and that layer IS
   `<arch>-loader-faithful`** — which was stated with no precondition at all. So
   the axiom was not merely trusted, it was **FALSE** for every program the
   emitter duplicated: `as` refuses the text, so the axiom's LHS is the trace of
   nothing. Note it is EXTERNALLY false, not internally inconsistent —
   `assemble : String → List Byte` is uninterpreted and total, with no failure
   mode, so the usual `⊥`-probe could never have found this. Agda structurally
   cannot catch a defect while the premise is absent.

3. **The precondition ALREADY EXISTED, one level up, and went vacuous.**
   `ArchCorrect.assemble-correct` carries `DistinctSymbols m`, discharged by the
   real proof `program-no-clash`. But once `asm-sem` was DEFINED as
   `exec-bytes ∘ assemble` (`FlatFromObs.flat-from-obs`), that field collapsed to
   `assemble-correct = λ _ _ _ _ _ → refl` — the premise is consumed by a `refl`
   and does nothing. The trust point moved to `loader-faithful`; **the
   precondition did not move with it.**

   GENERAL TRAP, worth remembering on its own: *a precondition attached to a
   trust point stays behind when the trust point moves.* Whenever a postulated
   field becomes a definition, audit its premises — they are now decorative.

### The fix — one predicate, stated arch-generically, discharged once

- `Once.CCC.Codegen.EmittedWF` — `labels-def` / `labels-ref` over
  `AbstractTrace` (defining occurrences = `c-label`/`c-thunk`; referencing =
  `c-jmp`, the two branches, `instr-load-code-addr`), and

      record EmittedWF (at : AbstractTrace) where
        labels-unique     : AllPairs _≢_ (labels-def at)            -- `as`
        labels-resolvable : All (_∈ labels-def at) (labels-ref at)  -- `ld`

  On the ABSTRACT TRACE deliberately: one statement, all three arches, no
  per-arch restatement. `labels-resolvable` IS the existing residual
  `emitted-code-addr-has-body` stated where it belongs — folding it in kills a
  duplicate rather than adding one.

- `Once.Compile.moduleLabels` — the mirror of `moduleSyms` one level down, over
  the SAME `compileResolvedModule` list and threading the SAME counter
  `compileAllWithTarget` threads (`l₁ ⊔ l₂`). It cannot drift from what the
  backend emits. The counter is the one place the arch shows through
  (`compile-trace-cnt` allocates further labels of its own), hence
  `moduleLabels : Arch → …`; the labels themselves are read off the
  arch-independent trace.

- `Once.Adequacy.LabelClash` — `DistinctLabels arch m = AllPairs _≢_
  (moduleLabels arch Heap false m)`, the sibling of `DistinctSymbols`.

- **Premise site: `AsmTraceCorrect` + `ArchCorrect.asm-trace-correct`** — the
  shared obligation type, so one edit reaches all three arches, and each arch
  threads it into its own `<arch>-loader-faithful`. NOT on `assemble-correct`:
  that is where the vacuity trap of (3) lives.

- **Discharged ONCE at the apex**, in `Compile.WithCPU.codegen-asm-correct`,
  exactly as `program-no-clash` discharges `DistinctSymbols`. So the top-level
  `correct` gains NO hypothesis — the axiom got narrower and the apex owes a
  theorem. Interim: ONE named residual, `program-labels-distinct`, class
  **deferred proof / codegen**. The count rising is correct per the ledger's own
  gate: naming an obligation beats hiding it inside an axiom.

### It is provable, and FALSE exactly where the bug is

`LabelRange`'s bricks: counter monotonicity (DONE), containment via `LabelScope`
(DONE), uniqueness next, by the disjoint-range argument at every splice. It
fails today at exactly one place — `cata-dispatch` uses the IH for `at` TWICE at
the same range `[l, l₁)` — and holds after either cata fix. That is what "the
invariant forces the proof in the right way" means: the residual is not a
placeholder for work nobody can do, it is a false statement pointing at the bug.

### Scope, stated honestly

`compile-trace-cnt` allocates FURTHER labels per arch (case/loop expansion),
starting at the counter the trace hands out. Those are inside the range but not
in `moduleLabels`. That walk is LINEAR (it never splices a sub-trace twice), so
its freshness is a `LabelRange`-shaped one-liner per arch — the easy half. The
hard half (the non-linear `ir-to-trace'`) is the half stated.

### The wider audit this opened

Duplicate labels are one instance of a general blind spot: **`assemble : String →
List Byte` is total and uninterpreted, so NO assembler rejection is
representable.** Everything `as`/`ld` can refuse is invisible to the proofs and
sits inside `loader-faithful`. Two findings from the sweep:

- **`once_arith.block.<digest>` is not covered by `DistinctSymbols`.**
  `moduleSyms` lists only `once-symbol-path (cfName cf)`. The arith blocks
  `compileAllWithTarget` accumulates are emitted by `emitArithBlocks` as
  `.globl once_arith.block.<d>` + `once_arith.block.<d>:`, with NO dedup
  (`rewrite-ir`'s own comment says "caller may dedup by digest"; the caller just
  `DL.++`s). The symbol is a pure function of the block body, so two
  structurally identical arith subtrees anywhere in a module emit the SAME
  global symbol twice — the same defect class as D099, one level up, still live.
  Route: extend `moduleSyms` to the full defined-symbol list (functions + arith
  blocks) and dedup the block list by digest at the fold.
- **The premise says nothing about the primitive symbols we CALL.** Strata
  interpretations supply them at link time; an unresolved one is an `ld` error
  the model cannot express. Same shape as `labels-resolvable`, one level up.

The structural repair for the whole class — and the right long-term move — is to
give the assembler a failure mode (`assemble : String → Maybe (List Byte)`), so
that "the toolchain accepted this text" becomes a proposition the proofs can
carry rather than an assumption they cannot see.

---

## D101: C1 — the Cata's Algebra Is Emitted ONCE, as a Called Body

**Date**: 2026-08-10/11 · **Plan**: 0.68 step 4 · **Status**: landed
(`fix/cata-single-algebra`); x86-64 exit tests back to 55/0/0

D099 named the defect (the algebra spliced twice under one label range) and
D100 wired the invariant that will make its class a type error. This entry is
the FIX, and the two things it cost.

### The fork, and why A lost

Three options were on the table:

- **A — re-generate the second copy at a fresh label counter.** Names become
  distinct by construction and no proof machinery is new. It was built to 7 of
  8 walks on `fix/cata-label-duplication` (`a33af0b9`) and then REJECTED: an
  algebra that itself contains a `Cata` has ITS algebra duplicated too, so
  nesting depth `d` costs `2^d` copies of the innermost algebra. Correct, and
  not a tolerable steady state.
- **B — D089's splice `path`,** distinguishing the copies inside the label
  identity. `Label.path` is dead code (`ℓ o n = mkLabelId o [] n`); it would
  re-teach every label-ordering argument about paths, to distinguish copies
  that C1 does not create.
- **C1 — emit the algebra ONCE and CALL it.** Chosen.

### What C1 is

The algebra becomes a called body inside the cata's own trace — the same
`c-thunk`/`c-ret` bracket `curry` has emitted since the 0.63 flip, so this does
NOT re-open the flip that inlined bodies:

    <setup> ++ <loop skeleton> ++ c-jmp end ∷ c-thunk body bb ∷
                                  (at ++ c-ret bb ∷ c-label end ∷ [])

NO NEW INSTRUCTION. `instr-call-closure` (D092/D098) transfers control to
whatever code address sits in the closure record's second cell, so the setup
builds that 2-cell record ONCE before the loop and each application site
points `fclosure` at it. The (env, arg) pair-packing is `apply`'s TRACE, not
the instruction, so the algebra keeps its own convention: layer in `Input1`,
result in `Output`.

**The bracket goes LAST, not first** — that is load-bearing, not cosmetic.
`segagree-curry` proves `SegAgree (H ++ c-thunk … ∷ (body ++ c-ret … ∷
c-label e ∷ []))` for an arbitrary IDLE labelled prefix `H`, and with the
bracket last the loop skeleton IS that `H`. With it first the loop would be a
SUFFIX, which nothing in `LabelScope` supports.

### What it bought on the proof side (four simplifications, not costs)

The algebra is now generated at FRONTIER 0 — it runs in its own frame, exactly
as `curry`'s body does. Consequences: `frontier-mono`'s Cata clause collapsed
(the caller's frontier is not advanced by the algebra); `CataIRSlotStable`'s
witnesses became `++⁺ (all-stable?-sound _ refl) (cata-body-stable … at sat)`
instead of ~50 spelled-out entries; `SlotBudget` lost the `segok-weaken` of the
algebra into the cata's budget at every site (it was only sound because the
algebra shared the cata's frame); and `LabelScope`'s Cata case became one
`segagree-curry` application, retiring `cata-{nat,lin,br}-pieces` and
`cata-pieces` entirely — their window content moved into the combinator's
arguments. `segagree-curry`'s last premise was generalised from `b' ≤ c` to
`(b' ≤ c) ⊎ (d ≤ a)` because `curry` allocates its labels before its body and
the cata after: **a window premise phrased as an ordering is usually
disjointness that happened to be true in the first client.**

### What it costs, recorded honestly

The cata's `traces-agree` now has a CALL/RETURN excursion per layer instead of
straight-line code, so `cata-correct`'s eventual discharge must consume the
return-address residuals (#9 `ret-site-owes`/`ret-budget-matches`, #10
`call-site-shape`) inside the cata induction. Those are owed anyway; threading
them through `cata-correct` is strictly more than closing them at their own
call sites. Paid knowingly, for `2^d` → 1.

### The defect C1 itself shipped, and what it says

The first C1 emitter was green on all four clusters and WRONG: `cata-call-setup`
points `Input1` at the record to write its cells (`store-indirect`) and never
handed it back, so the skeleton's first read of the μ-value got the record's
tag cell instead. Every cata folded ZERO layers — `cata-nat` exited 0 instead
of 3. Fixed by stashing the incoming value in the call's spare slot `k` and
reloading it at the end of the setup.

The point is not the slip; it is that **nothing in the proof could fail**.
`cata-correct` is a postulate, so no theorem relates the cata's trace to the
fold, and the six codegen walks (labels, slots, frames, allocation, stability)
are all TRUE of the broken trace. The exit tests were the only witness. This is
D100's thesis restated from the other side: a top-level postulate does not
merely leave work undone, it removes the ability to be wrong.

### Status after this

`program-labels-distinct` (D100, residual #14) is now TRUE of the emitter, and
`cata-correct` stops being FALSE — it becomes an ordinary owed proof whose own
blocker is unchanged (base and ascend were amputated by `5088e571` and must be
rebuilt). Neither is discharged here.

---

## D102: The Flip Left Each Arch's Frame Ceremony Behind

**Date**: 2026-08-11 · **Plan**: 0.69 (closed by this entry) · **Status**:
landed on `fix/arch-frame-model`; all three arches 55/0/0, `cabal test` 266/266

The 0.63 flip moved closure bodies INLINE into the main trace, so `ir-to-bodies`
stopped producing anything and `irToBodies` emits `""`. What nobody noticed for
six weeks is that **each arch's per-body frame ceremony lived in that path**,
and only that path. The bodies moved; the ceremony did not move with them.

Three arches, one cause, three different amounts of damage:

| arch | what the dead path did per body | what it cost |
|---|---|---|
| x86-64 | `subq $N,%rsp` … `addq` | NOTHING — slots are already `%rsp`-relative and the return address is on the stack. The only arch that kept working. |
| x86-32 | `pushl %ebp; subl $N; movl %esp,%ebp` … | THE SLOT ANCHOR. Slots were `n(%ebp)` with `%ebp` anchored once in the function prologue, so an inlined body's `sub esp` re-anchored nothing: its slots aliased its caller's frame and ran off the end. 20 tests, all SIGSEGV. |
| riscv64 | `addi sp,-(N+8); sd ra, N(sp)` … | THE `ra` SPILL. The return address is a REGISTER and `instr-call-closure` is `jalr ra t1 0`, so a body that called anything destroyed its own return address and `ret` jumped back into itself. 37 tests, 36 of them HANGS. |

### Why no proof could see it

On x86-32 and riscv64 the entire simulation is one postulate
(`<arch>-conc-flat-sim`) plus a loader axiom. There is no theorem relating
either arch's instructions to the flat machine, so all four Agda clusters were
green throughout. Worse for x86-32: `X86-32/FrameInstantiation.agda` already
said `frame-base = sp-addr` and `slot-addr f k = sp-addr f + k * word-size` —
**the emitter had been outside its own arch's formal model the whole time**, and
the blanket postulate is exactly what made that unobservable. Compare D101,
where a postulate removed the ability to be wrong about the cata's fold; this is
the same shape at the ISA boundary.

### The fixes, and why each is two lines

Because the dead path still SHOWED the intended shape. Neither fix was a design
exercise — both were transcriptions of what `emit-thunk-body` had always done:

    x86-32:  slots become `[esp + slot*4]`, function frame becomes
             `subl $frame,%esp` … `addl $frame,%esp`, no `%ebp` traffic.
             Then the body bracket's own `sub`/`add` IS the re-anchor — which
             is why the IDENTICAL `c-thunk`/`c-ret` lowering has always been
             correct on x86-64.

    riscv64: `c-thunk n b ↦ label ∷ addi sp sp -(slots (suc b)) ∷ sd ra sp (slots b)`
             `c-ret   b   ↦ ld ra sp (slots b) ∷ addi sp sp (slots (suc b)) ∷ ret`
             One slot above the body's own budget holds `ra`; the ABSTRACT
             budget does not move, the extra word is the lowering's own.

### What this bought beyond the tests

**The three arches now share one frame model** — slots addressed off the stack
pointer, re-anchored by the body bracket itself. That was plan 0.66's stated
premise ("width is the one new axis"), which was FALSE until now: x86-32
differed on two axes, width AND frame anchor. It is true today, and it is also
what makes plan 0.65's `FlatCore` a generalisation over the ISA rather than
over the ISA plus two frame conventions.

### The general rule

D100 said a precondition attached to a trust point stays behind when the trust
point moves. This is the same rule one layer down, and the layer matters: **what
stays behind need not be a proof obligation — it can be a prologue.** When a
refactor moves WHERE code is emitted, inventory what the old site did BESIDES
emitting it. The dead path is the checklist; read it before deleting it.

---

## D103: D096 Was an ARCH FIX for a SHARED Defect — riscv64's `lla` Wrote 0

**Date**: 2026-08-13 · **Status**: Fixed · **Plan**: 0.65 (G2)

### The defect

`Target.RiscV64.Semantics`'s `lla rd, .L_thunk_ℓ` wrote **0** into `rd`:

    execInstr prog s (lla rd n) =
      just (record s { regs = writeReg (regs s) rd 0 ; pc = pc s + 1 })

with the comment "the abstract model doesn't track link-time label addresses;
advance pc, leave rd opaque (0). Not exercised by the FS-generic apex."

That value is **jumped through**. `IRToTrace` emits `instr-load-code-addr ℓ` to
build a closure record; riscv64 lowers it to this instruction; the result goes
into the record's second cell; and `instr-call-closure` lowers to
`ld t1, 8(s1) ; jalr ra, t1, 0`. So the modelled machine jumped to 0 on every
closure application while the real one jumped to the body — making
`riscv64-loader-faithful` **false** for every program that applies a closure,
with the fiction hiding inside the trusted axiom.

This is D096's defect verbatim. Fixed the same way: resolve the label through
`find-label prog (thunk ℓ)`; an absent label halts, as for `j` and the branches.

### Why it survived D096

**D096 was applied to one arch, and the reasoning that made it safe to defer
elsewhere expired without anyone re-checking.** Both defects were shielded by
the same argument — "nothing in the proof cone uses the value as an address."
For x86-64 that stopped being true when **D092 modelled the call**, and D096
followed. But D092 changed the SHARED flat machine, so it invalidated the
excuse for **every** target at once, while only x86-64's semantics was
repaired. riscv64 kept a comment asserting a safety property that D092 had
already removed.

### The general lesson

A per-arch fix to a defect found in shared machinery leaves the same defect in
the other arches, and its justification comment becomes stale SILENTLY — no
typechecker sees it, because each arch's semantics is independently well-formed.
The three targets' surfaces are now diffed mechanically (`AbstractTo*` and, as
of this entry, the code-address clause of each `Semantics`); that diff is what
found this, two days after the emitters' own asymmetries.

Corollary for plan 0.65: this is the FOURTH thing porting the correspondence to
a second arch has found that was invisible from x86-64 alone — after riscv64's
missing `compile-trace`, all three targets' missing `compile-trace-cnt-agrees`,
and riscv64's `with`-bound `step`/`exec`. Three of the four are defects rather
than absences.

### x86-32 had it too, and worse

Checked immediately, because this entry's own lesson says to. `mov-code r,
$.L_thunk_ℓ` advanced the pc and left `r` **untouched** — not even a definite
value, so the register kept whatever it held before. Its comment said this
"mirrors x86-64's `lea` of a `rip+label`", which was TRUE WHEN WRITTEN and
became false at D096. x86-32's closure call is `call *4(%ebx)`, so the same
argument applies and `x86-32-loader-faithful` was false for the same programs.

Fixed identically. **All three targets now resolve a code address through
`find-label … (thunk ℓ)` and halt on an absent label** — one defect, found
once, repaired three times, which is what "per-arch fix to shared-machinery
defect" costs when it is not chased across the arches on the day.

### What it cost

`step-lla` gains its resolved form and a sibling `step-lla-missing` — two
outcomes where there was one, exactly as `j` has. Nothing else moved on either
arch: the value was previously unconstrained, so no proof depended on it being
0 (riscv64) or stale (x86-32).

### Second instance, same arch, found 2026-08-13 (plan 0.70 phase D)

`li rd, imm` wrote **`0` for a negative immediate**. A real `li a0, -1` loads
all-ones; the model loaded zero. Same shape as the `lla` defect above — a clause
that returns a plausible-looking constant instead of doing the ISA's job — and
it had the same camouflage: a step lemma (`step-li`) stated ONLY for
non-negative immediates, with a comment explaining that the negative case "lands
on a different post-state (`0`)". The restriction read as care about a genuine
case split; it was in fact the defect, documented.

FIX: `execInstr` reads the immediate with `Once.Word.Width.fromℤ` — D054's
two's-complement reading, which also norms — so both signs are one clause, and
`step-li` now covers its whole domain. `addi` got the same treatment (`rs +
sext(imm)` is one modular addition).

LESSON, worth more than the fix: **a lemma restricted to part of an
instruction's domain is a place to look for a defect.** The restriction is
evidence that the excluded case does something the author could not state — and
"could not state" is more often wrong than subtle.


## D104: `SlotAddrNoWrap` Was REFUTABLE — a Correspondence Does Not Bound a Slot INDEX

**Date**: 2026-08-16 · **Status**: Fixed · **Plan**: 0.65 (G2)

### The claim, and why it looked safe

riscv64 has no `lea`. It computes a slot's address with `addi`, a real add, and
D054 makes `add` compute `W.⊕` unconditionally — wraparound is DEFINED
semantics, so no no-overflow precondition may sit on the instruction. The range
obligation therefore lands on the consumer, and `RiscV64/ConcFlatSim` took it as
a D087-class resource parameter:

    CompiledCorr hv prog fs s
  → fetch prog (fpc fs) ≡ just (lea-slot slot)
  → readReg (regs s) sp + slot-to-disp slot < W.modulus

It was written WITHOUT a `RunAt` premise, and not by preference: the engine's
`bs-lea-slot` field hands an arch only `(cc, h, ft)`, because that is what it
passes on x86-64, whose `lea` needs no bound at all. The commit that introduced
it (`251d5cfe`) flagged the anomaly — every sibling in the family
(`HeapRoom`/`StackRoom`/`CallRoom`) carries `RunAt`, so this one was strictly
stronger — and said to run the 2026-07-30 refutability probe before trusting it.

### The probe, and it took twenty minutes

Run 2026-08-16. `SlotAddrNoWrap → ⊥` typechecks, from a witness built by hand:

    hv    HDom ≡ λ _ → ⊥, hfront ≡ lo ≡ 0, haddr hl ≡ heap-offset hl * 8
    fs    every abstract register `SV-Tag 0`, heap and stack memory empty,
          `saved-frames ≡ []`, `frame-slots ≡ 0`, current frame based at 0
    s     every riscv64 register 0, memory `λ _ → nothing`, pc 0
    prog  `lea-slot W.modulus ∷ []`

Every field of `FlatCorr` is `refl`, an absurd lambda, or `z≤n`; `pc-off` and
the fetch are `refl`; `ret-eq` is `tt` (`fret ≡ []`) and `code-eq` is vacuous
(a one-instruction `addi` block carries no label). And the conclusion reads
`0 + modulus * 8 < modulus`, which `m≤m*n` kills.

### What the counterexample actually says

**Nothing in a CORRESPONDENCE bounds a slot INDEX.** `CompiledCorr` relates a
flat state to a machine state; a slot index comes from the PROGRAM, and the
only thing that constrains the program is `RunAt` — `Emitted` gives
`prog ≡ ir-to-trace ir`, and the shape check turns that into
`slot < frame-slots ≤ ir-stack-budget`. That is exactly why the other three
bounds carry `RunAt`, and the anomaly was the whole tell.

Note what did NOT matter: the stack pointer. `Frame` is a `StackPointer`, so
`frame-base` is bounded by the layout's `upper stack-bounds` and `sp-eq` pins
`sp` to it — the register side was never the free variable. The free variable
was the index, and it is free because a hand-picked `prog` is not an emitted
one.

### The fix, and what it cost each arch

`bs-lea-slot` gains a `RunAt prog fs` premise, so `CompiledCorrespondence` now
takes `o : CanonicalName` and imports `RunContext` privately (`EventEngine`
opens the same instance publicly; module application is by alias, so the two
`RunAt`s are one type). The dispatch passes `inv-run wf`, exactly as it does
when deriving `bs-load-tag-lit`'s range premise from `tag-fits`.

    x86-64   pays NOTHING. `bs-lea-slot = λ … cc h ft _ → block-step-lea-slot …`
             — its `lea` never needed a range fact, and dropping the argument is
             the interface working as designed.
    riscv64  `slot-addr-no-wrap` and `ResourceBounds.SlotAddrNoWrap` gain the
             premise and join their three siblings' shape.

Ledger unchanged: riscv64's bounds are module parameters not yet threaded from
the apex, so no row moved.

### The general lesson

**A residual whose premises mention only the STATE, while its conclusion
mentions the PROGRAM, is asking the wrong layer.** That is the shape to look
for — it is what "strictly stronger than its siblings" meant here, and the
family's own conditioning was the available evidence. When a field's premise
list is copied from the arch that needs the least (x86-64 passes three because
`lea` is total), the arch that needs more cannot fix it locally: it can only
close the gap from a parameter, and the parameter then inherits the field's
insufficient context.

Corollary for plan 0.65's method note: "field shapes come from the ENGINE's
call site" is right, but the engine's call site is itself a choice. When an arch
has to invent a bound to fill a field, check what the engine COULD have passed
and did not — here `FlatInv` had the `RunAt` all along.

## D105: The Call Window's Head Row Is PER-ARCH — `RetAddrs` Takes the Claim, Not `CompiledCorr` a Field

**Date**: 2026-08-16 · **Status**: Landed · **Plan**: 0.65 (G2)

### The window

D086 gives the CALL the return-address slot, and D093 says every pending return
in `fret` is really in memory at its frame's window end. Both are true on
x86-64 at every instruction boundary, because `call` pushes the address in
hardware. On RISC-V they are not: `jalr` writes `ra` and touches neither `sp`
nor memory, so between the call and the callee's `sd ra` the head pending
return has no cell at all.

The `sp` half of that was an EMITTER problem and is closed (`0338648e`: the
caller reserves its own slot with an `addi`). What is left is irreducible — for
one whole abstract instruction the return address lives in a register on one
arch and in memory on the other — and `FlatState.flink : Maybe ℕ` marks it.

### The route that does not work, and why it is inviting

The obvious move is a new `CompiledCorr` field:

    link-eq : ∀ r → flink fs ≡ just r → link-corr s (blk-off prog r)

with a `flink fs ≡ nothing` premise on the other 41 block-steps, each
discharged `λ r ()`. It fails twice. All 42 fields owe the new field WHATEVER
premise they carry — that is what a record means — and on x86-64 the
preservation claim is not even true in general: a `store-at-slot 0` writes at
`%rsp`, which is exactly where its link lives. The engine cannot rescue it
either: `FlatInv` is abstract-side only, and the concrete state lives in
`events-agree`'s arguments, so a fact about `s` has nowhere else to live.

### What works: the row itself is the parameter

`RetAddrs` takes the arch's claim and selects on `flink`:

    RetAddrs xoff mem LK (just _) ((f,b) ∷ fr) (r ∷ rs) =
      LK (frame-base f + slots b) (xoff r) × GapNext … × RetAddrs … nothing fr rs
    RetAddrs xoff mem LK nothing  ((f,b) ∷ fr) (r ∷ rs) =
      (readMem mem (frame-base f + slots b) ≡ just (xoff r)) × GapNext … × …

`CompiledCorr.ret-eq` passes `link-claim s`, a new `EI.Machine` field —
a MACHINE owes it, because it is an ABI fact:

    x86-64    λ s a v → readMem (memory s) a ≡ just v   -- ≡ its `nothing` row
    riscv64    λ s a v → rreg s ra ≡ v                  -- the address is ignored

The recursion passes `nothing` because only the head can be unspilled: a call
jumps straight to a body marker, and the marker spills. So the whole ABI
difference is the HEAD ROW CONVERSION, and that is two lemmas —
`ret-unlink` (`just`→`nothing`, what the marker does) and `ret-relink`
(`nothing`→`just`, what the call does). x86-64 discharges both with
`λ _ _ p → p`; riscv64's `ret-unlink` will be its `sd ra`.

### What it cost, measured

x86-64's ~21 `ret-eq` sites did not move at all, and that is not luck: a
post-state is a RECORD UPDATE, so a register write leaves `memory` literally
alone and the claim rides along. riscv64's sites did not move either, for the
mirror reason — a write to a CONCRETE register leaves `ra` alone by
computation. Only the two helpers polymorphic in the register
(`block-step-mv`, `block-step-li`) cannot see that, and they take a one-line
premise that is `refl` at all nine callers.

Two block-steps DO need a premise, and it is a genuine one: `bs-call` and
`bs-c-ret` both READ the head cell, so they need the memory row rather than the
link claim. `flink fs ≡ nothing` is what selects it, and the engine derives it
from `run-link-at-thunk` (a live link ⇒ the fetched instruction is a
`c-thunk`) against its own fetch. That is the lemma's whole job — it does NOT
save the block-steps, and the dead route above is why that is worth saying.

### The general lesson

**When two targets disagree about WHERE a fact lives rather than WHETHER it
holds, parameterise the fact's own statement, not the record that carries it.**
A field is owed by every member of a record; a parameter of the predicate is
owed once, at the place the two arches actually differ. The tell that the field
route was wrong was its arithmetic: one field × 42 members × 2 arches, against
one parameter × 2 arches.

Corollary, from the same session: state a transport between CLAIMS
(`∀ a v → LK a v → LK' a v`), not between STATES
(`link-claim s → link-claim s'`). The first leaves plain metas the expected
type solves; the second asks the unifier to unfold a definition, and it does
not.

## D106: RISC-V's Body Marker SPILLS Onto the Cell the Call Reserved — and Three Places That Assumed Otherwise

**Date**: 2026-08-16 · **Status**: Landed · **Plan**: 0.65 (G2)

### The instruction

D105 put the call window's head row in `RetAddrs` and left each arch to convert
it. On x86-64 the conversion is the identity — `call` already wrote the cell.
On RISC-V it is a STORE:

    c-thunk n b   label (thunk n) ; addi sp, sp, -8b ; sd ra, 8b(sp)

and `sp + 8b` after the reservation is `sp` before it, which `sp-eq` puts at the
current frame's base, which `frame-slots ≡ 0` (D094) makes the frame's window
END — the slot D086 gave the CALL. **The marker writes the head pending
return's own cell.** Three things in the development assumed no arch does that.

### 1. It needs a live link, and a pending return — both were theorems

Without `flink ≡ just r` the store overwrites a saved return address with
whatever `ra` holds; without `fret ≡ rpc ∷ rest` there is no head row to say
what `ra` holds. Both are true for the same reason `frame-slots ≡ 0` is: the
ONLY way to reach a body entry is a call (fall-through refuted by the emitter's
guard, jump by D082's disjoint provenances, return by `RetMatch`'s provenance,
entry by the guard again).

So `SegWF.seg-entry`'s conclusion now carries all three, and **the proof did not
grow by a line**: every case but the call was already `⊥-elim`, which produces a
triple as readily as an equation. Projections: `thunk-entry-empty`,
`thunk-entry-link`, `thunk-entry-ret`.

### 2. Its DATA correspondence needs `GapNext`, which lives in the OTHER component

`StackWindows` threads its floor as a `≤`: from the windows alone the caller's
frame could start exactly on the cell being written. What rules that out is
`GapNext` — the caller's base is one slot ABOVE the cell — and `GapNext` is a
row of `RetAddrs`, not of `StackWindows`.

**So the two components D093 deliberately kept separate are COUPLED on a
spilling arch, and the coupling is D086 doing its job**: the store is legal
precisely because the call reserved that cell. New core lemmas
`windows-store-gap` (windows) and `corr-store-gap` (the whole record), plus
`ret-spill` — the `RetAddrs` twin, where the head row becomes the memory row
BECAUSE of the write. The two halves cannot be separated: before the store the
cell holds nothing usable, after it the `just` row is gone.

### 3. `sim-call` was x86-64's ABI wearing the core's name

It took a `SetsRoleMem` — it ASSUMED the call writes the return address to the
reserved cell. `jalr` writes `ra` and no memory. Deleted, and replaced by
`sim-call-frame`, which proves only what the arches share: the frame descends
one slot and the entered frame reserves nothing. The arch that also stores
composes `corr-store-gap` — and the cell x86-64 pushes to IS the post-state's
gap cell, so no new lemma was needed and x86-64's call is unchanged in strength.

The core could not do that composition itself: `State` is abstract, so only an
arch can name the intermediate state (`%rsp` moved, memory not) that the real
`call` never passes through.

### 4. …and `ret-no-wrap` was short by a slot (D104 again)

riscv64 reaches the caller's base in ONE `addi sp, sp, 8(b+1)`. x86-64 does it
in two — `add rsp, 8b`, then the `ret`'s own pop — and needed a bound only on
the first, so the field said `rreg s sp-reg + slots b < modulus`. The quantity
that must be representable is THE CALLER'S FRAME BASE. Strengthened to
`slots (suc b)`; x86-64 weakens it in one line. `bs-call` likewise gained
`rreg s sp-reg < modulus`, because the caller's `addi sp,sp,-8` is a real
subtract where x86-64's `call` reserves in hardware.

### The general lesson

**An ABI difference the emitter cannot erase will not stay inside the block
step that meets it.** `sp-eq` was closable in the emitter (the caller now
reserves its own slot); the return address living in a register was not, and it
propagated into the state predicate (D105), the run invariant (`seg-entry`), the
layout lemmas (`windows-store-gap`), and a resource bound (`ret-no-wrap`) — four
layers, because each of them had quietly been stated at what ONE arch needed.

The check that catches this class early is the one D104 named: for every field
an arch has to fill, ask what the ENGINE could have passed and did not, and for
every core lemma, ask which arch's instruction set its premise shape came from.
`sim-call`'s `SetsRoleMem` is the answer to the second question, and it sat in a
module whose whole purpose is to be arch-free.

## D107: The Modelled riscv64 Loader Handed `main` a Stack Pointer of ZERO — and Only the Apex Could Have Asked

**Date**: 2026-08-17 · **Status**: Fixed · **Plan**: 0.65 (G3)

### What was wrong

    x86-64   initState = mkstate (writeReg emptyRegFile rsp stack-top) …
    riscv64  initState = mkstate emptyRegFile emptyMemory 0 false
    x86-32   initState = mkstate emptyRegFile emptyMemory initFlags 0 false

The stack grows DOWN. A `main` handed `sp ≡ 0` underflows on its first frame.
Two of the three targets modelled a loader that does that, and x86-64 did not
because it postulates `stack-top : Word` — "the `%rsp` the loader hands `main`" —
and `initState` sets `rsp` to it.

This is not a proof inconvenience. `entry-corr`'s `sp-eq` says the concrete
entry `sp` IS the entry frame's base, and its `lo-le` says the high-water mark
is at or below it. With `sp ≡ 0` and a frame based anywhere above 0, neither
holds. **The entry correspondence is not provable against the old model** — so
every step above it was resting on a state the machine cannot be in.

### Why it survived

`riscv64-conc-flat-sim` was a whole-cloth postulate at the apex: "the concrete
`run-events` equals the abstract `flat-events`", the entire simulation assumed
in one line. Nothing above the correspondence ever asked for the entry state, so
nothing ever evaluated it.

Plan 0.65's G1/G2 then built the whole riscv64 correspondence — the core
extraction, all 42 block-steps, the five stuck routes, the resource family, the
`Supply` — with that postulate still in place. **Every one of those was green
while the entry state was unusable.** The four clusters cannot see it: an
assumption that is never consumed is indistinguishable from one that is true.

### How it was found

By deleting the postulate FIRST and following the red, rather than building the
island and wiring it at the end. `initState` was the first thing that turned
red, before a line of `entry-corr` was written.

That ordering was not the one this plan followed, and the plan is the reason:
G1/G2 were an EXTRACTION — generalise x86-64's proof, instantiate at riscv64 —
and an extraction has a natural bottom-up shape. The shim at the top is what let
that shape run to completion unchallenged.

### The fix, and what it costs

riscv64 gets `stack-top` and `initState` sets `sp` to it, stated exactly as
x86-64 states it: the entry `sp` is OPAQUE (the one thing the loader tells us),
and the heap base is 0 without loss of generality since addresses are ℕ and only
the relative order matters.

With that, `entry-frame-riscv64` stops being an opaque postulate and becomes the
loader's `sp` — a riscv64 `Frame` IS a `StackPointer`, so `entry-frame-base`
collapses to `refl`, exactly the collapse x86-64 records. Net at the apex:

    OUT  riscv64-conc-flat-sim   the whole simulation, whole-cloth
    OUT  entry-frame-riscv64     an opaque `Frame`, about which nothing is provable
    IN   stack-top-in-stack      the `sp` we are handed is in the stack region
    IN   conc-fuel               D5 step-budget adequacy (x86-64 carries it too)
    IN   main-heap-moded         frontend class (x86-64 carries it too)

**x86-32 STILL HAS THE HOLE.** Fix it before its correspondence is written, not
during — the same argument applies, and there is no island there yet to protect
it from being noticed.

### The general lesson

**A postulate at the apex does not merely leave a gap — it disables the only
check that would have found the model wrong underneath it.** "Wire the
obligation in first" is usually argued as a discipline about proof structure.
This is the sharper reason: the top-level statement is what EVALUATES the model.
Until it does, a wrong model and a right one produce the same green.

Corollary for extractions specifically: generalising a working proof to a second
instance is inherently bottom-up, so it is exactly the shape of work that needs
the apex deleted at the START. The postulate you keep "until the island lands"
is the one that makes the island's greenness meaningless.

## D108: The Ninth Role Had No Producer — `Input2` Is RETIRED, Not Spilled

**Date**: 2026-08-17 · **Status**: Fixed · **Plan**: 0.66

### The blocker, as G1c left it

`FlatCore.RegRoles` needs an INJECTIVE `reg-of : Role → Reg`, or the
correspondence claims two roles agree with one register at every step. x86-32
could not supply one:

    role         x86-64   riscv64   x86-32
    stack ptr    rsp      sp        esp
    frame ptr    rbp      fp        ebp    ← the ninth role
    Output       rax      a0        eax
    Input1       rdi      t0        ecx
    Input2       rsi      a1        edx  ←┐
    Scratch      rbx      s3        edx  ←┘ SAME REGISTER
    Count        r14      s4        edi
    closure      r12      s1        ebx
    heap top     r15      s2        esi

Eight GPRs, nine roles. There is no free register: `ebp` is the live frame
anchor every i386 epilogue restores `%esp` from, so reassigning it is a SIGSEGV
(attempted and backed out 2026-08-11).

### What the count was actually saying

`Input2` had NO PRODUCER on any arch. Plan 0.2.4.5 Stage C introduced it for a
split-input calling convention; that convention was REVERTED (`IRToTrace`: "Stage
C γ-revert — uniform packed-pair convention"), and plan 0.54 rung D split the
descend tally out of it into `Count`. What remained was a register the abstract
machine carried, two instructions (`mov-output-to-input2`, `mov-input2-to-output`)
`ir-to-trace` never emitted, and a role every arch had to name — surviving
purely in proof enumerations.

So the register count was not a shortage. It was the arch with the least slack
reporting a dead role, and x86-32 was the only place the report could surface.

### Why RETIRE and not SPILL

The alternative on the table was to give x86-32's `Input2` a stack slot. That
reads local and is not: `reg-of` is REGISTER-VALUED, so a spilled role widens the
interface to `Role → Reg ⊎ Slot` and re-threads every role-indexed lemma on
x86-64 and riscv64 as well — to keep an instruction nothing emits, and to put a
memory access where the other two arches have a register.

Retiring costs ~600 mentions across 38 files and removes machine state instead of
adding an interface. The realised map is then injective everywhere: x86-32's
seven roles in seven registers (esp/eax/ecx/edx/edi/ebx/esi) with `ebp` reserved.

### The mislabelling that hid it

Three files called `%edi` "Input2" while `count-*` is what writes `%edi`
(`AbstractToX86-32`, `Arith/Backend/X86-32/Emit`, and riscv64's `s4`). None
carried a correct label, which is why review never caught that Input2 and Scratch
were one register. All three are corrected here.

### The lesson

**A role no emitter can produce is not a register shortage — it is state the
machine does not have.** When an arch cannot fill an interface injectively, ask
first which entries anything actually WRITES; the constrained arch is reporting a
defect in the shared model, not asking for an exception. And when the answer is
"nothing writes it", the fix deletes rather than widens: retiring a dead role is
the only option that makes the remaining state smaller.

Deferred, deliberately: the split-input convention returns as a type-driven
optimisation for register-fittable primitive arguments. It brings its own
register plumbing back WITH a producer, and x86-32's register pressure becomes a
real question then — answerable against emitted code rather than against an
enumeration.

## D109: A `Float` Does Not Fit in a 32-Bit Register — `FitsInReg` Is Stated Without an Arch

**Date**: 2026-08-17 · **Status**: RESOLVED — the encoding is arch-relative · **Plan**: 0.66 (X2)

### What the proof refused to accept

Porting x86-64's block-steps to x86-32 stopped here:

    x86-64   compile-abstract (instr-load-const fits-float v) = mov rax (imm (float-bits v)) ∷ []
    x86-32   compile-abstract (instr-load-const fits-float _) = ud2 ∷ []

The abstract machine LOADS the constant and keeps running; the x86-32 machine
HALTS. No block-step can relate them, so `block-step-load-const-float` is not
merely unwritten here — it is unprovable.

### The emitter is not the defect

`float-bits` is a 64-bit pattern and an i386 register is 32 bits wide. There is
no `mov` that puts a double in `%eax`, so `ud2` is the honest lowering of a
capability the target does not have. The defect is one level up.

`FitsInReg` (`Once.Type`) is ARCH-INDEPENDENT. `fits-float` asserts globally
that a `Float` is register-fittable — true at 64 bits, false at 32 — and
`ir-to-trace'` acts on it unconditionally:

    ir-to-trace' n l (const fits-float v) = … instr-load-const Ty.fits-float v ∷ …

So the IR forms an instruction the 32-bit target cannot implement.

**CORRECTION (same day, before anything was built on it): the defect is LATENT,
not live.** This entry first said "every Once program containing a float literal
traps at runtime on x86-32". No Once program can contain a float literal at all:

  * `Once/Parser/Token.agda` has `TInt`, `TString` and no float token — `TDot`
    is only ever accumulated into an operator/qualified name
    (`Parser/Expr.agda`), never into a numeral;
  * `Once/Surface/Elaborate.agda` builds exactly one literal,
    `intLit n = const fits-int ∣ n ∣ ∘ terminal`; `Float` appears nowhere in
    `Once/Surface/`.

So `ir-to-trace'`'s `const fits-float` clause is real code on a path the
FRONTEND cannot reach. A `Float` value can still exist at runtime — `intToFloat`,
`parseFloat`, `pi` are SigOps — but a float CONSTANT cannot be written. The
`ud2` lowering was therefore a defect waiting for the surface syntax, not one
shipping in binaries today, and `examples/arith-test.once` (which imports
`I.Math.Float`) only exercises the IMPORT, its `main` being `exit0@S`.

What survives unchanged is the reason the correspondence could not be written,
and the fix: the encoding is a target property. What does not survive is the
"live miscompile" framing — the right claim is that x86-32 could not have
supported float literals the day they were added.

### Why the correspondence is what found it

The same reason D107 gives. `x86-32-conc-flat-sim` assumes the whole simulation,
so nothing above ever asked what `ud2` means, and the arch that cannot do the
thing was never made to say so. Deleting the postulate is what turned it into a
type error.

### The resolution: a `Float` IS what it usually is on a 32-bit machine

Neither of the two ways out first considered (arch-dependent `FitsInReg`;
lowering the literal to memory) is needed, and both were answering the wrong
question. The premise to reject is that a `Float` is 64 bits ANYWHERE. On a
32-bit target a `Float` is SINGLE precision — which is what every 32-bit ABI
says — and then it fits a register, `FitsInReg` stays arch-independent, and the
instruction the IR forms is one the machine can execute.

So the ENCODING becomes a target property, exactly as `slot-size` already is:

    Once.Semantics.FloatBits.float-bits         -- the 64-bit pattern
    Once.Semantics.FloatBits.float-bits-single  -- the same value at 32 bits

and `FlatCore.FlatCorrespondence` takes it as a parameter `fenc`, used by
`enc-sv-at (SV-Lit fits-float v)`. 64-bit targets pass `float-bits`; x86-32
passes `float-bits-single`. The correspondence never learns which — only that
the emitter's immediate and `enc-sv` are the same function, which is what makes
the block-step `refl`.

`float-bits-single` is written IN AGDA, as arithmetic on the 64-bit pattern
(sign, re-biased exponent, truncated mantissa, with the four edge classes —
zero/subnormal, ±∞/NaN, overflow, underflow — pinned explicitly). Deliberately
not an FFI primitive: the stdlib has no double→single conversion and this repo
has no foreign bindings at all, so importing one would put the encoding of every
float constant outside the language the compiler is checked in. Rounding is
TRUNCATION, and that is a choice the correspondence permits because the encoding
is only ever read forwards — it must be DETERMINISTIC, not IEEE-default.

### The lesson

**A capability predicate with no arch parameter is an assumption that every
target is the widest one.** `fits-int`/`fits-float` read as facts about types;
they are facts about a type AND a register file. The place that discovers this
is the correspondence for the narrowest target, which is an argument for porting
to the *smallest* machine early rather than last.

## D110: `exec` Must Reduce — the `with` Form Freezes One-Step Reasoning Behind an Auxiliary

**Date**: 2026-08-17 · **Status**: Applied to all three arches · **Plan**: 0.66 (X2)

### The wall

`exec-1` is the workhorse of every block-step: one step of `exec`, driven by the
step result.

    exec-1 : halted s ≡ false → step-not-halted prog s ≡ just s' → halted s' ≡ false
           → exec (suc n) prog s ≡ exec n prog s'
    exec-1 hs snh hs' rewrite hs | snh | hs' = refl

It is NOT PROVABLE against an `exec` written with nested `with`:

    exec (suc n) prog s with halted s
    ... | true  = just s
    ... | false with step prog s
    ...   | nothing  = nothing
    ...   | just s' with halted s' …

The scrutinees freeze behind a generated auxiliary —
`Semantics.with-670 s false n prog | (step prog s | halted s)` — and no
`rewrite` of `halted` or `step-not-halted` can reach inside it. x86-64 hit this
in plan 0.27 (C3) and moved its definition; x86-32 still had the old shape, and
plan 0.66 hit the identical wall at the identical lemma.

### The decision

**The machine's `exec` is written with `if_then_else_` plus an explicit
`exec-cont` that pattern-matches the `Maybe` directly** — on every arch, as a
standing requirement of the model rather than a local fix:

    exec zero    _    s = just s
    exec (suc n) prog s = if halted s then just s else exec-cont n prog (step-not-halted prog s)
    exec-cont _ _    nothing   = nothing
    exec-cont n prog (just s') = if halted s' then just s' else exec n prog s'

The two forms are DEFINITIONALLY EQUAL on every input: in the `else` branch
`halted s` is `false`, which is exactly where `step prog s` reduces to
`step-not-halted prog s`. So `run`-by-`refl` examples and the extracted
interpreter are unaffected — this is the definition moving, not the proof.

### Why it is recorded rather than left as a repeat

It is the third time the shape mattered and the second time it cost a session to
rediscover, and it is invisible from the outside: two definitions that compute
the same function differ in whether a whole proof layer is possible. A reviewer
comparing `exec` against the ISA sees nothing wrong with the `with` form.

**The general rule**: a model's step function is consumed by REWRITING, so its
definition must expose its scrutinees. `with` is for proofs, not for the
definitions proofs reduce. Same family as "prefer top-level helpers taking
`Dec`/`Maybe` arguments over `with`-blocks", and the same family as the
MAlonzo case-tree blowups a `with`-wrapper causes — the cure is identical:
name the auxiliary and take its result as a value.

## D111: The Third Instance Is What Tests a Generic Core — Three Findings from Instantiating It

**Date**: 2026-08-17 · **Status**: Landed (2 findings closed, 1 open) · **Plan**: 0.66 (closes it)

Plan 0.65 extracted `FlatCore` from x86-64's correspondence and instantiated it
at riscv64. Two instances built together prove little: the core was shaped while
riscv64 was in view. **x86-32 is the first instance nobody tuned the core for**,
and this entry records what that measured — the reason to keep porting to a
third target even when two are green.

### 1. The extraction GENERALISED — measured, not asserted

`RegRoles`, `FlatCorrespondence`, `FlatComposition` and `ResourceBounds`
transferred to x86-32 as x86-64's files with the register file and ISA swapped,
each typechecking on the FIRST attempt. `FlatSimulation` — 42 block-steps,
~2300 lines — needed four genuine edits and no structural change:

    updateFlags takes ONE argument here (x86-32), not two
    `mov-code r ℓ` where x86-64 has `lea r (rip+label ℓ)`
    `jmp-l` where x86-64's `jmp` takes a label
    `cmp [ecx]` where x86-64 addresses `[rdi+0]`

Plan 0.66 predicted the first of those in advance as the test of whether the
core obeyed its own rule (take the branch OUTCOME in read-back form, never
mention `Flags`). It did: nothing in x86-32's `StepLemmas` is exported to the
core.

### 2. A CORE FIELD CARRIED AN ISA DETAIL — `+ 0` is a displacement (OPEN)

`CompiledCorrespondence`'s tag-branch fields say

    memory s (rreg s in1-reg + 0) ≡ just k

The `+ 0` is a DISPLACEMENT. x86-64's `[rdi+0]` and riscv64's `ld t1, 0(t0)`
both produce it, so two instances agreed and the shape looked arch-free;
x86-32's `cmp [ecx], 0` has no displacement and does not. x86-32 converts
locally with `+-identityʳ`, next to the addressing mode it belongs to.

**Open follow-up**: the core should say what it MEANS — the tag cell is at the
Input1 pointer — and let each arch add its own displacement. Two arches matching
a detail is not the same as the detail being generic, which is precisely the
failure mode this entry exists to name.

### 3. A LATENT CLOBBER the emitter has no register to avoid

`lea-indexed` on x86-32 lowers to

    mov ecx, [esp+n] ; mov eax, edx ; add eax, eax ; add eax, eax ; add ecx, eax

using `%eax` — the OUTPUT role — as the doubling temp, where x86-64 uses `rcx`,
a register with no role at all. The abstract `lea-indexed` writes only Input1,
so the lowering destroys a live value the model says survives.

**Not a live defect**: the engine refutes `lea-indexed` outright
(`frame-op-absurd` — `ir-to-trace` emits none), so no emitted trace contains it.
It is the same shape `Input2` had before D108 retired it: dead today, wrong the
day it gains a producer, and on this arch there is no spare register to fix it
with. Recorded so the next person to give `lea-indexed` a producer finds this
first.

### The width audit found nothing, and that is the result

Plan 0.66's premise was that `slot-size` (4 here, 8 elsewhere) is the one new
axis. `grep '\b8\b'` over `FlatCore` returns COMMENTS ONLY; `slot-size` is a
module parameter with a `NonZero` instance and the `word-eq` tie, and every
offset goes through it. The core was width-clean before anyone checked — which
is worth recording precisely because it is the audit that could have gone the
other way.

## D112: `Float`'s Representation Is a PARAMETER, as `Int`'s Already Is

**Date**: 2026-08-18 · **Status**: PARTLY CORRECTED BY D113 (2026-08-19) ·
**Supersedes**: 0.71's F5/F6, completes D109

> **Read D113 first.** The defect below is real and the PARAMETERISATION is
> right. The choice of what to instantiate it at — an exact `Dyadic` — is
> wrong: it gives `Float` a value level D054 deliberately removed from `Int`,
> and IEEE arithmetic rounds, so exactness is the same unprovable straddle.
> `⟦ Float ⟧` is the target's representation; `Dyadic` is the literal payload.

**Landed 2026-08-18 (0.72 P1–P3).** `Once/Float/Dyadic.agda` is the carrier and
`FloatFormat` the width; `Value`/`ValueIR`/`IRTy`/`Translate` take `FloatRep`
as a parameter and `Once.Semantics.Machine` instantiates the pair at
`(Carrier , Dyadic)`. `LitFits.float-fits` is now a THEOREM on all three
arches (`<-≤-trans (encode-fits F v) (^-monoʳ-≤ 2 (n≤1+n k))`) and no longer a
field of the record — the first of that family to be discharged rather than
threaded. Two implementation facts worth carrying forward:

- The `RInt` mirror does NOT hold everywhere. `pInfer`'s catch-all routes a
  float head to `nothing`, so `pInfer-canon`'s two `RApp (RFloat …)` cases are
  `refl` where `RInt`'s recurse into the argument. A catch-all is what makes a
  new constructor's proof obligations UNLIKE its neighbour's, in both
  directions — cf. the retired-ctor trap.
- The elaborator rejects a float literal (`FloatLiteralUnsupported`) until
  0.71's F3b supplies the typing rules. Rejecting loudly is the honest state
  for a half-wired path; the alternative is a literal that types and then means
  nothing.

### The four lines

    Once/Semantics/Value.agda:129   ⟦ Int ⟧   = IntRep      -- a PARAMETER
    Once/Semantics/Value.agda:130   ⟦ Float ⟧ = AgdaFloat   -- hardcoded, 64-bit
    Once/IRTy.agda:239              ⟦ IntRep ⟧-baseI Int   = IntRep
    Once/IRTy.agda:240              ⟦ IntRep ⟧-baseI Float = AgdaFloat

`Int`'s representation is arch-relative and EXPLICIT — a parameter instantiated
at the width-free `Carrier`, with the target's width applied at the machine by
`norm` (D054). `Float`'s is arch-relative and IMPLICIT: fixed to Agda's double
at both levels, with the target-relativity smuggled in one layer below.

### What was actually holding the impossibility

A 64-bit double cannot live in a 32-bit register, yet x86-32 compiled float
literals. The mechanism is not a postulate — it is a definition:

    Once/Type.agda:383           fits-float : FitsInReg Float   -- no arch, no premise
    FlatCorrespondence.agda:286  enc-sv-at am (SV-Lit fits-float v) = fenc v

`FitsInReg Float` is asserted unconditionally, and `enc-sv` is DEFINED as
whatever encoder the target supplies. Abstract and concrete therefore agree by
construction, and the loss is invisible to every gate: no name, no entry in the
residual ledger, no probe that can refute it. **An unstated definitional
assumption is strictly worse than an axiom** — an axiom can at least be counted.

D109 fixed the symptom (x86-32 emitted `ud2`) by making the ENCODER
target-relative. That was right as far as it went and wrong as a resting place:
it left the DENOTATION fixed at 64 bits, so the encoder had to be lossy, and the
lossiness had nowhere to be stated.

### The decision

**`Float` follows `Int`.** Its representation becomes a parameter of the value
domain and of the IR carrier, instantiated at a width-free EXACT carrier (a
dyadic rational `m / 2^e`, mirroring `Carrier = ℕ`), with the target's FORMAT
applied at the machine, mirroring `norm`.

The argument that settled it: any other answer makes `Float` the only base type
whose width ignores the target while `Int`'s tracks it. Two fixes were
considered and rejected for that reason — pinning `Float` to IEEE double
everywhere and letting x86-32 hold it in memory like `Str` (consistent, but
leaves `Float` the odd one out), and putting the width in the type as
`F32`/`F64` (sound, but changes the surface language and makes users pick).

### Consequences

- `float-bits` and `float-bits-single` are DELETED, not justified: no
  `primFloatToWord`, no NaN-encodes-as-0 edge, no unprovable faithfulness claim.
- `LitFits.float-fits` becomes provable from the encoder's construction — a
  residual deleted rather than moved.
- `FitsInReg` gains the arch (D109's option (a)) as a consequence rather than a
  separate decision.
- An 8-bit target stops being a special case: it instantiates a narrow `IntRep`
  and a narrow `FloatRep`; a target with no float format has no `Float`, which
  is a reportable fact rather than a silent re-encoding.

### The lesson

**When two base types face the same question, the one that was solved first is
the specification for the second.** `Int` had already answered "what does a
value of this type mean when the target's width varies?" — parameterise the
representation, apply the width at the machine, carry the literal's range as an
obligation. `Float` was written as though the question had never been asked, and
the gap hid for as long as nothing tried to compile a float literal on a narrow
target. The review question this yields: for any base type, ask which OTHER base
type already has its shape, and diff them.

## D113: `Float` Follows D054 — the Hardware's Promise, Not an Exact Value

**Date**: 2026-08-19 · **Status**: Decided · **Corrects D112** (same day) ·
**Extends D054 to the second numeric type**

### What D112 got right and wrong

D112 found a real defect: `⟦ Float ⟧` was hardcoded to Agda's double, so a
32-bit target's narrower format had nowhere to be stated, and the loss was
invisible to every gate. Making the representation a PARAMETER was right and
stands.

**Instantiating that parameter at an EXACT value (`Dyadic`) was wrong.** It
gave `Float` a value level that D054 had deliberately removed from `Int`, and
did so without noticing it was asserting the negation of a recorded decision.

### The argument (D054's, applied to the second type)

D054: *representation follows the promise*. A fixed-width representation
implies modular semantics, and you cannot prove fixed-width `add` equals
unbounded ℤ `+` — `255 + 1 = 0` in a byte, `= 256` in ℤ. So ℤ is not `Int`'s
meaning; the `Word` is, and ℤ survives only as scaffolding inside the modular
op and as the parked spec of a future `BigInt`.

**The same sentence holds with the words changed:**

> IEEE `fadd` ROUNDS. Exact dyadic `+` does not. They are different functions.

So an exact-value denotation for `Float` is the identical straddle. The
no-overflow side conditions D054 eliminated would return as no-rounding side
conditions, and every float arithmetic obligation would carry a "within the
exactly-representable regime" caveat — which is exactly the shape of hole D054
was written to close.

The user's framing, which is the whole decision in one line: **in the end it is
the hardware that promises what it calculates.**

### Why `Str` is not a counterexample

`⟦ Str ⟧ = String` — an exact Agda value — so the codebase is not uniformly
"denotation = machine representation". The distinction is ARITHMETIC. `Str` has
none, so an exact denotation promises nothing the machine can contradict.
`Float` has arithmetic, and its arithmetic rounds. D054's argument bites
exactly where operations exist.

### Decision

**`Float`'s denotation is the target's float representation** — the width-free
`Carrier`, with the FORMAT applied at the target, exactly as `Int`'s width is
applied by `norm`. `⟦ Float ⟧ = Carrier`, symmetric with `⟦ Int ⟧ = Carrier`.

**`Dyadic` demotes to the role ℤ has for `Int`**: the literal payload and the
parked exact spec. The frontend parses digits into a `Dyadic`, decides
representability against it, and encodes it at the target's format. It is not
what a `Float` expression MEANS.

**`encode`/`fenc` stay**, but as the literal ENCODER at codegen — not as a
bridge between two denotations. There is only one denotation now.

**F4's exactness rule becomes a statement about LITERALS**, which is where it
belongs and where it is provable. It says nothing about arithmetic, and it is
compatible with rounding (plan 0.71's successor decision).

### Consequences

- One line changes the model, because D112's parameterisation was right:
  `Once.Semantics.Value Carrier Dyadic` → `Once.Semantics.Value Carrier Carrier`.
- `enc-sv` for a float literal stops being a denotation bridge; the literal
  arrives already encoded, as `Int`'s does.
- A float literal must still reach the target UN-ENCODED at the IR level,
  because — unlike a non-negative `Int` literal, whose bit pattern is the same
  at every width — `1.5` is `0x3FC00000` at 32 bits and `0x3FF8000000000000` at
  64. That is a fact about literal PAYLOADS, not about denotations, and it is
  the same reason a `Str` literal carries a `String` to the target.
- Float arithmetic, when it lands, is whatever the target's FPU computes —
  with no exactness precondition to discharge.

### The lesson

**When a second instance of a solved problem appears, find the decision that
solved the first one before designing.** D054 had already answered "what does a
fixed-width numeric type mean?" with a general argument, and D112 re-answered
it differently for `Float` without citing it. The review question: for any new
type or representation, which EXISTING decision already covers its shape — and
does this contradict it?


## D114: The OBSERVABLE Is Part of the Spec — and It Observes Only `Int` Arguments

**Date**: 2026-08-20 · **Status**: Declaration landed; widening staged ·
**Found while**: asking why a float literal's target format did not seem to
affect the apex theorem (plan 0.73 F2c)

### The finding

`Once/Denotation/Trace.agda` records a SigOp invocation's argument **only when
the SigOp's domain is syntactically `Int`**:

    isInt? Int = just refl ; isInt? _ = nothing
    mkEvent {D} si arg = mkEvent-name (name si) (isInt? D) arg

Every other domain records `nothing`. With
`signature print : Eff (String) Unit` (`Strata/Interpretations/Linux/File.once`),
this means:

> **`print "hello"` and `print "goodbye"` have the same `Behavior`.**

A compiler that swapped every string argument would still satisfy `correct`.
The same holds for `free : Eff Buffer Unit`, `realloc`, `argv`, `getline`,
`heap_string`, and `emitF`. Only `exit@S n` is pinned, because its domain
happens to be `Int` — which is why Layer 0's exit tests are meaningful and the
three `float-emit-*.once` tests are not (they can only show the process does
not trap).

### Why it happened, which is the part worth remembering

The machine side carries the identical gate, and says why
(`Once/Adequacy/FlatEvents.agda:61-68`):

> "ℕ argument decoded from `Input1` when the input type is `Int` (**matching
> `mkEvent`'s `isInt?` gate on the source side, so the two sides can be proven
> equal**)."

**The observable was narrowed so the correspondence would go through.** That is
the spec being shaped by the proof — the same inversion D057 was written to
stop when it moved the meaning off the elaborator. A weaker observable makes
`correct` easier to prove and less worth proving, and nothing in the gate
signalled the trade.

It survived because the spec did not declare it. `Once.Spec.Meaning` re-exported
`ValueDomain`, `Behavior`, `Meaning`, `MainMeaning` — but spec-level `emit-D`
calls `mkEvent`, and `Behavior = ℕ → List SigOpEvent` names the record, so the
rule was load-bearing spec behaviour reached THROUGH declared spec modules while
living in one that was never reviewed.

### Decision

**1. The observable is spec.** `Once.Denotation.Trace` is re-exported from
`Once.Spec.Meaning`. Nothing moved — the module is 75 lines and contains only
the event vocabulary, so declaring it was the whole fix.

**2. The argument is observed as a TYPED BASE VALUE**, not as a machine word:

    record SigOpEvent : Set where
      field ev-name : CanonicalName
            ev-dom  : Type
            .ev-base : IsBaseType ev-dom
            ev-arg  : ⟦ ev-dom ⟧

Three reasons, in order of weight:

- **A machine word states the WRONG thing about compounds.** For `Str`/`Buffer`/
  products the register holds an ADDRESS. An address is a lowering artifact —
  two correct compilers with different heap layouts would then have different
  behaviours. `Maybe Carrier` does not merely fail to COVER compounds; extending
  it later would mean redefining what `ev-arg` MEANS. Typed-value makes the
  compound case an extension; machine-word makes it a rewrite.
- **It observes in the domain the meaning already computes in.** Anything else
  invents a second value language for the observable. And at the scalars the
  two coincide — `⟦ Int ⟧ = ⟦ Float ⟧ = Carrier` — so nothing of the
  "honest about registers" argument is lost: **D113 is what buys this**, because
  `⟦ Float ⟧` already IS the target's representation.
- **It is available today and deletes machinery.** Every `SigOpInfo` carries
  `baseA : IsBaseType A` (`Once/SigOp/Info.agda:167`), and `IsBaseType` is
  closed under `*`/`+` over Unit/Void/Int/Float/Str/Buffer with **no arrows** —
  `IsConcrete` already excludes callbacks as "the cases a register ABI cannot
  pass and the observational bridge cannot relate funext-free". So there is no
  funext obstacle. `mkEvent si arg = mk-event (name si) _ (baseA si) arg` has no
  dispatch at all, which retires `isInt?` and `mkEvent-name` — the latter exists
  only to keep the dispatch reducing on an abstract domain.

**3. An unfinished proof is a NAMED RESIDUAL, never a narrowed spec.** The
machine side must decode `⟦ A ⟧` out of `Input1`. For scalars that is a register
read; for compounds it is a heap walk (`readTyped`, plan 0.54 rung A, currently
Unit/Int/pairs). Where the decode is not yet proved, the arch correspondence
carries a named residual per shape that `make postulates` can see — the
difference between "we have not proved `print` passes the right string" and
"`correct` does not care what string `print` gets."

### Consequences

- Widening turns currently-discharged obligations into holes. That is the point:
  they were discharged against a claim that was too weak.
- `emitF` becomes a real observation, so the target's `FloatFormat` becomes part
  of what a program MEANS — which is the threading plan 0.73 F2c describes, now
  forced by the observable rather than adopted on principle.
- Staging: scalars (`FitsInReg`: `Int`, `Float`) need no memory reasoning and
  close the demonstrable hole; compound base types are a separate, larger piece.

### The lesson

**When a correspondence is hard to prove, check whether the fix narrowed the
claim.** Both sides of this one were gated on `isInt?` and the comment said so
in plain words for months. The guard is structural, not vigilance: if a
statement declares what counts as correct, it belongs in the reviewed spec — a
module the spec only reaches through is a module nobody reads.

**Relates**: D057 (anchor the meaning independently of the implementation),
D058 (`Behavior` is event-count-indexed), D061 (per-SigOp interpretation
contracts), D113 (`⟦ Float ⟧` is the target's representation — what makes a
typed float argument observable at all)

## D115: An `Int` Literal Out of the Target's SIGNED Range Is a TYPE ERROR

**Date**: 2026-08-20 · **Status**: Decided; implementation staged (plan 0.74) ·
**Extends D054 to literals** · **Settles the question D113/D114 left open**

### The decision

Once's integers are SIGNED. On a `w`-bit target an `Int` holds
`−2^(w−1) … 2^(w−1)−1`, so on an 8-bit target the largest literal is `127`.
**`emit 298` there does not compile.** A literal outside the target's range is
a TYPE ERROR — not a warning (Once has no warning channel yet) and not a
silent wrap.

### Why an error rather than a wrap

D054 says representation follows the promise: fixed-width `add` wraps, and
that IS the hardware's promise, so `255 + 1 = 0` in a byte is correct
arithmetic and not an error. **A literal is not arithmetic.** `2001` is a value
the programmer wrote down; silently substituting `2001 mod 256 = 209` is a
substitution nobody asked for, and it is exactly the class of silent value
change D109 was about.

The language already answers this question for the OTHER numeric type and
answers it this way: `Once.Float.Representable.accept?` REJECTS `3.14` rather
than rounding it. `Int` was simply never asked. Two types, one question, and
until now two different answers — the situation D113's lesson says to hunt
for.

### What it forces: the width must be THREADED, not baked

A range check needs a width, and so does the denotation: `⟦ Int ⟧ = Carrier`
is the residue, so `−5` denotes `2^w − 5` and is width-relative exactly as a
float literal is format-relative. This is the same shape D113 produced for
`Float`, and the machinery built for it is the template:

    arch-float-format : Arch → FloatFormat      ⟶   the width's analogue
    FrameSemantics.float-format                 ⟶   already has `frame-word`
    LitPayload fits-float = Dyadic              ⟶   LitPayload fits-int = ℤ
    lit-value fits-float d = encode fmt d       ⟶   lit-value fits-int z = fromℤ

Note `FrameSemantics.frame-word` ALREADY carries the width (8/4/8 bytes), so
the machine side needs no new field — `8 * frame-word FS` is the bit width.

### A regression this supersedes, recorded honestly

Fixing the signed-denotation bug (2026-08-20, `b2908563`) baked `Word64` into
`Arith/SigOp/Builders`, `Surface/Elaborate.intLit`,
`Denotation/Meaning` and `Denotation/SourceDenote`. That was right about
SIGNEDNESS and wrong about WIDTH: those modules serve all three targets, and
one of them is 32-bit. It is not a new promise — `block-semM` has baked 64
since it was written — but it hardcodes a target fact where the target is not
known, which is what D109 and D112 were both about. Plan 0.74 removes it.

The three sites are not equally bad and should not be fixed identically:

  * `Denotation/Meaning`, `Denotation/SourceDenote` — these ALREADY take a
    threaded target parameter (the float format, D113). The width belongs in
    the same parameter; widening it costs almost nothing, and not using a
    channel that was already there was the plain error.
  * `Surface/Elaborate.intLit` — the elaborator builds ONE IR for three
    targets and cannot know the width. The fix is the `Float` answer: the
    payload stays SOURCE SYNTAX (`ℤ`) and the machine materialises it.
  * `Arith/SigOp/Builders`' `semM` family — the hard one. `SigOpInfo`'s `semM`
    is a closed function, so threading a width means the arith SigOp
    descriptors gain one. This is the D059 bill proper.

### Consequences

- The reference meaning becomes width-indexed at `Int`, joining `Float`. One
  `Arch → target-numerics` map should carry both rather than two parallel maps.
- `accept?` gains an integer sibling, and the frontend rejects out-of-range
  literals with a real error message.
- A NEGATIVE literal becomes writable (plan 0.73 F3) and range-checked in the
  same stroke — `-129` on 8-bit is as much an error as `2001`.

**Relates**: D054 (`Int` is a signed modular `Word`), D059 (width threaded from
the arch, never hard-coded), D109 (a hardcoded target fact that made an
impossibility invisible), D113 (`Float`'s representation is the target's — the
template), D114 (the observable that made the negative-value bug visible)

## D116: A `Float` Literal ROUNDS; an `Int` Literal Must FIT

**Date**: decided earlier (recorded in plan 0.71's carry-forward); given a
number 2026-08-21, after being misread twice from a plan bullet ·
**Status**: Decided; float half deferred, int half is plan 0.74 ·
**Refines D115** · **Completes D054's argument for literals**

### The decision

**A `Float` literal always lowers.** It rounds to the target's format,
round-to-nearest-even, and warns when the rounding is inexact. `3.14` is a
legal Once program; so is `16777217.0` on a `binary32` target. Neither is an
error.

**An `Int` literal must FIT the target's signed range**, or it is a compile
error (D115). `2001` on an 8-bit target does not compile.

### Why the two differ — and why that is not an inconsistency

It looks asymmetric and is not. Each type's literal follows THAT TYPE'S
PROMISE, which is D054's rule applied one level down:

- **IEEE's promise INCLUDES rounding.** `0.1` is not exactly 0.1 in any binary
  float, in any language; rounding a literal to the format is the float
  contract, not a deviation from it. A compiler that refused `3.14` would be
  refusing to implement floats.
- **D054's promise for `Int` is modular ARITHMETIC** — `255 + 1 = 0` in a byte
  is correct, defined semantics. **A literal is not arithmetic.** `2001` is a
  value the programmer wrote; substituting its residue is a change nobody
  asked for, and nothing in the promise covers it.

So "handle `Int` and `Float` the same way" holds where it should — the
ARCHITECTURE is identical (frontend generic, backend lowers at its own
width/format) — and the failure modes differ because the promises differ.

### Consequences

- `Once.Float.Representable.accept?`'s rejection is an INTERIM, explicitly
  "sound but incomplete". It is not the design and must not be built upon.
  **It is scheduled for DELETION, not relocation** — do not move it to the
  backend on symmetry grounds; that would relocate something about to be
  removed.
- `16777217.0` (exact at `binary64`, not at `binary32`) is rejected today on
  every target. The fix is ROUNDING, not a per-target representability check:
  under this decision it compiles everywhere, exactly on the 64-bit targets and
  rounded on x86-32.
- The target-relative admissibility gate plan 0.74 introduces is therefore
  **`Int`-only**. Floats need no gate: they always lower.
- What the float half still owes: a `round : FloatFormat → Dyadic → Word`, its
  correctness (CompCert proved theirs, so we should), and a WARNING CHANNEL,
  which Once does not have yet. That channel is the reason the interim
  rejection exists — with no way to say "this rounded", refusing was the only
  honest option available.

### The lesson

**A decision that lives only in a plan's carry-forward bullet will be read as
a placeholder and built upon as if it were the design.** This one was misread
twice in one session — first as "`accept?` is how floats work", then as
"`accept?` should move to the backend for symmetry" — and both readings would
have entrenched an interim. If it constrains future work, it needs a number.

**Relates**: D054 (representation follows the promise — the argument this
applies to literals), D109 (a float's width is a target property), D113
(`Float` denotes the target's representation), D115 (an out-of-range `Int`
literal is an error)

## D117: A Float Literal's Payload Is a DECIMAL, and There Is Exactly ONE Rounding

**Date**: 2026-08-24 · **Status**: Implemented (plan 0.74 K0/K1) ·
**Implements D116** · **Same principle as D115's `ℤ` payload**

### The decision

`LitPayload fits-float` and `IR.const`'s float payload are a `Decimal` —
`record Decimal { sig : ℤ ; exp10 : ℕ }`, `Dyadic` at base ten — not a
`Dyadic`. The machine turns it into bits with `round`, at its own format,
rounding to nearest-even.

### Why the old payload could not work

**`3.14` is not a dyadic at any width.** `3.14 = 157/50` and 50 is not a power
of two, so no `Dyadic` equals it — which is why `accept?` rejected it at the
EXACTNESS step, before representability was ever consulted. A `Dyadic` payload
can only ever hold the subset `accept?` was restricting us to, so D116's
"literals round" is unimplementable with it.

The payload is SOURCE SYNTAX, and source syntax for a float literal is a
decimal. That is the same reasoning that makes an `Int` literal's payload a `ℤ`
(D115), one type over.

Holding the literal EXACTLY is the property being bought: with an exact payload
there is exactly ONE rounding, at the backend, at the target's format.

### Two alternatives, rejected

- **Agda's `Float`** — forces a rounding BEFORE the backend's, so a literal is
  rounded twice. Harmless for binary32-via-binary64 by Figueroa (53 ≥ 2·24+2),
  but it CAPS PRECISION at the payload's format, so binary128 or x87-extended
  could never be served. It is also D109/D112's mistake — a format baked where
  all targets must be served — and `primFloatToWord` has no equational theory.
- **`(ℤ , ℕ)` integer-part/fraction-part** — `3.14` and `3.014` both give
  `(3 , 14)` unless the digit count rides along, and `-0.5` has integer part
  `-0 = 0`, so THE SIGN IS LOST. The sign belongs on the significand.

### `round` does NOT route through `Dyadic.encode`

Found by the pins, and the reason the two modules stay separate. `Dyadic.shift`
is a `ℕ`, so a large value has to be written `(m · 2^K) /2^ 0`, which puts K
zero bits BELOW the significand — and `sigFieldN` can only LEFT-align. Its
`2 ^ (sig-bits ∸ (bitLen ∸ 1))` clamps to `2^0` and `modPow` then keeps the low
`sig-bits` bits, which are the zeros just introduced. `round binary64 1e41`
came out as `0x4870000000000000`, a pure power of two, with the entire fraction
`0x25dfa371a19e7` replaced by zeros. The step meant to satisfy `encode`'s
precondition was violating it.

So `roundSig` returns the significand WITH ITS BINARY EXPONENT as a `ℤ` —
positive for large literals, negative for small — and `fracField` does the
right-shift `∸` could not. That signed exponent is what `Dyadic` structurally
cannot express.

### The rounding is PINNED, because it cannot be falsified from inside

Both the meaning and the codegen call the SAME `round`, so their correspondence
is `refl`-shaped and holds whatever it computes. That is exactly how
`Once.Float.Dyadic`'s encoder once wrote the pair straight into the two fields,
typechecked, and satisfied `encode-fits`. The patterns are therefore checked
against values computed ELSEWHERE (glibc/IEEE), decided by `refl`:

    3.1  3.14  0.1  0.5  2.75  16777217  -0.5  0  1e41  1e-40

plus `round (5 /10^ 1) ≡ round (50 /10^ 2)` — the unnormalised-payload
agreement, discharged rather than assumed.

**That `round` is IEEE round-to-nearest-even is a NAMED TRUST POINT**, of the
same kind as `assemble-correct`: a spec-quality question, not a
compiler-correctness one. What must not happen is the version where nobody
states it and the compiler is "correct" about a rounding nobody checked — that
is `emit`'s low byte again (D114).

**Relates**: D109, D112 (the float-representation parameter), D113, D114 (the
unfalsifiable-from-inside lesson), D115 (`ℤ` payload, same principle), D116
(literals round — this is how)

## D118: Float Overflow Is ±∞; Underflow Is ZERO, and Once Models No Subnormals

**Date**: 2026-08-24 · **Status**: Implemented (plan 0.74 K2) ·
**Settles what D116 explicitly left open**

### The decision

Above the format's normal exponent range a float literal stores as **±∞**,
sign preserved. Below it, **zero**. Once models no subnormals.

D116 said literals round; it said nothing about the exponent range, and noted
that "whether Once models infinities at all is a real question and NOT settled
by D116". This settles it.

### Why ±∞ rather than an error

D116's own argument. The promise `Float` makes is the HARDWARE's, and the
hardware produces ±∞ — exactly as `Int`'s promise includes wrapping arithmetic
(D054). `⟦ Float ⟧` is the target's bit pattern (D113), so an infinity is just
a pattern and nothing in the value model changes.

### What this replaced, and why it was urgent

The exponent WRAPPED. `expFieldN` ends in `modPow … (exp-bits F)`, so a stored
exponent of 260 at binary32 came out as 4:

    round binary32 1e41  =  0x03800000     -- a small FINITE number

That is the same silent value substitution D115 forbids for `Int` literals, and
worse: nothing gated it at all, and it could not be found from inside, because
the meaning and the machine call the same function and agreed on the wrong
answer. It was found by writing a pin against an externally-computed pattern —
the D114 discipline, working as intended.

### The subnormal gap is a LIMITATION, stated not discovered

glibc stores `1e-40` at binary32 as the subnormal `0x000116c2`; Once stores
`0`. This is a real gap and it is PINNED as such, so it is read rather than
found later.

It is treated differently from the overflow wrap on purpose: underflow-to-zero
is BOUNDED (the value was already smaller than the format's smallest normal),
where the overflow wrap turned 1e41 into a small finite number — unbounded in
relative terms and catastrophic.

**Relates**: D054 (the hardware's promise), D113, D114, D115, D116, D117

## D119: The Arith SigOp Semantics Takes the Target's Width — the SPEC Was Wrong on x86-32

**Date**: 2026-08-23 · **Status**: Implemented (plan 0.74 J5) ·
**Instance of D059 that was mis-filed as hygiene**

### The finding

`Arith/SigOp/Builders` computed every arith `semM` with `Word64`:

    module W = OnceWord.Word64
    neg-semM x = W.⊝ x

and `Denotation/Meaning`'s `⟦ t-neg d ⟧ᵢ fmt` reaches it — threading `fmt` into
the sub-derivation and then DROPPING it. So the spec used the TARGET's width
for literals and 64 bits for arithmetic in the same expression:

    x86-32:   ⟦ int 5 ⟧       =  5             (correct)
              ⟦ neg (int 5) ⟧ =  2^64 − 5      (not even a 32-bit word)

The answer is `2^32 − 5`. This was filed as a cleanup ("modules serving three
targets should not name a width") and deferred. It is not a cleanup: the bake
is inside the MEANING.

### Why nothing caught it — the shape, for the third time

`block-semM` and `ArchCorrectness/ArithSimX86-32` baked 64 as well. Every
module that COMPARES two layers had a bake on each side: `eval≡semM` compares
the ℤ→Word evaluator with `block-semM`; `block-value-semM` compares the
abstract machine's output with the block's meaning; `ArithSimCore` compares a
concrete interpreter with `block-semM`. Fix the width in both operands and the
comparison is between something and itself — true, and about no real machine.

**That is D114's `isInt?` and the `absℤ` bug in a third costume. Two sides
wrong together is not a coincidence to notice; it is the failure mode to design
against.**

### The decision

`SigOpSem`'s `pureV` carries a `TargetNum → M.⟦A⟧ → M.⟦B⟧`, and `semM si tn` is
the old shape. Seven bakes of the literal 64 were removed from modules shared
by three targets; `ArithSimX86-32` is now `Width 32` and its correspondence is
about a machine x86-32 actually is. `Adequacy/CPU/X86-64` and `ArithSimRiscV64`
keep 64 and say so as `Width 64` rather than by the `Word64` alias, so it reads
as a claim about that target instead of the default nobody chose.

An `absℤ` bug (`IntLit.lit-int-info = λ _ → ∣ n ∣`, so `-5` meant 5) outlived
the 2026-08-20 sweep here by being unreferenced, and was fixed with it.

**Relates**: D054, D059 (width threaded from the arch — this is the instance
that was missed), D114 (the two-sides-wrong-together shape), D115

## D120: A Negated Numeral Is ONE Literal — the Spec Says So, the Front End Bridges

**Date**: 2026-08-22 · **Status**: Implemented (plan 0.74 J6)

### The decision

`-5` is a literal. The spec says what a negative numeral means:

    negLits (RInt n) = (- n) ∷ []
    negLits e        = rawIntLits e

and the elaborator folds `RUnaryOp OpNeg (RInt n)` into the literal `-n`.

### What it fixes

`-2147483648` was REFUSED on x86-32 though it is exactly that target's least
`Int` — D115's own text already implied it must compile ("`-129` on 8-bit is as
much an error as `2001`" says in the same breath that `-128` is not). A program
the target CAN express was rejected, the one failure mode `correctR-complete`
exists to rule out, and the proof missed it because the SPEC shared the blind
spot.

Independently of the range check, the compiler emitted **"load 5, then call
`arith.neg.int`"** — a RUNTIME negation of a compile-time constant. That is
wrong on its own terms. Verified on the metal after the fix: `mov
$0x80000000,%eax`, zero `neg` instructions.

### Where the truth goes — not the parser

At the level of GRAMMAR `-` really is a prefix operator and `Parser/Expr.agda`
is right to say so. Making `ParsesUnary` fold would need either an ambiguous
relation (both `pu-neg` and a `pu-neg-lit` apply when the operand is `RInt`) or
a function in the constructor's conclusion index, which breaks downstream
pattern matching. What a negative NUMERAL means is a fact about the LANGUAGE,
so it is stated in the spec and the front end bridges to it.

### The dispatch takes the decision as an ARGUMENT

    inferElabV-neg-dispatch ctx e = inferElabV-neg-aux ctx e (isRIntView e)

Matching `e` directly stops `inferElabV ctx (RUnaryOp OpNeg e)` unfolding for
an abstract `e`, which costs a 16-way `RawExpr` enumeration in THREE downstream
proofs and breaks a well-founded measure in one of them. Taking the view as an
argument — the same convention as `cfm-build-gated` taking its `Dec` — keeps
the unfolding, and the proofs split two ways instead of sixteen.

Soundness is `Once.Word.Width.⊝-fromℤ`, which could not even be STATED at the
right width until D119 (`semM neg-info` was baked at 64, so at `w = 32` the
claim read `2^64 − 5 ≟ 2^32 − 5`).

`realize-agrees` being stated OBSERVATIONALLY rather than syntactically is what
made the fold affordable: a syntactic `se ≡ realize w` would have forced
`realize` to fold too, and with it every proof that reads the derivation.

**Relates**: D054, D114, D115, D119, D121

## D121: The IR Gate Was a DETECTOR, and Detector Scaffolding Is Deleted, Not Parked

**Date**: 2026-08-25 · **Status**: Decided; scaffolding removed (plan 0.74 J6)

### The decision

A second literal-range gate over the COMPILED IR (`Once.IRLits`,
`AdmissibleIR`, `cfm-build-lits`) existed briefly and is DELETED. The
open invariant it stood for is recorded instead:

    compiledIntLits (compile of m)  ⊆  moduleIntLits m

### What it was for, and that it worked

`Once.Denotation.Admissible` already said the obligation out loud — "the
backend walks the IR instead, and that the two agree is a PROOF obligation, not
something faked by sharing a traversal" — and nothing honoured it: the backend
dispatched on `admissibleM?`, the SOURCE scan, so "backend agrees with spec"
held by sharing a traversal.

Gating on the IR made that obligation load-bearing, which turned a silent
defect into a red tree. It is what forced D120's fold and dragged D119's
`Word64` bakes out of hiding. It also proved, briefly and correctly, that
`correct` was FALSE: `compile` returned `nothing` where `⟦ src ⟧⊥` was `just`.
The gate did not break the theorem; it made the bug visible.

### Why deleted rather than kept wired

Keeping it wired costs `ElabPreservesLits` as a PREMISE on `correct` itself,
and that premise is a global induction over the elaborator — a real open
theorem, not a formality. Paying it to keep a check that can now only fire on a
compiler bug is a bad trade, and it made a ~30-line fold look expensive when it
was not.

Keeping it UNWIRED is worse than either: an unwired gate is dead code that
hides a gap instead of surfacing it as a type error.

### The invariant is bounded work

`Surface.Elaborate.intLit` is the ONLY producer of an IR `Int` literal — three
call sites, each already holding a source literal. Whoever proves it has a
bounded job, and proving it re-wires the gate at zero cost to `correct`.

**Relates**: D114, D115, D119, D120

## D122: Source Positions Ride on the LITERAL Tokens Only

**Date**: 2026-08-25 · **Status**: Implemented (plan 0.74)

### The decision

`tokenize-WF` threads a source offset; `TInt`, `TFloat` and `RFloat` carry it.
Every OTHER token does not.

### Why not every token

Measured, not guessed: positions on every token is **6738 pattern sites** across
20+ files including the verified parser, all the parsing relations and the
roundtrip proofs. On the literal constructors it is ~400 sites, mostly a `_`
added in a pattern. The lexer work — threading the offset through ten `tok-*`
helpers and re-proving `LexerBridge` — is identical under both, so widening
later is purely mechanical and costs nothing today.

### The bridge is INDEXED by the offset, not erased

Erasing the offsets — relating a position-free token stream — was the cheaper
option and does NOT compose: the parser consumes the real stream and copies a
float's offset into `RFloat`, so the parse RESULT depends on positions. A
bridge pinning only the erased stream would leave a gap exactly where
`parseStrict-sound` needs it.

`LexesChars` therefore carries the offset as an index, and every premise
advances it with `adv` — the same function the worker uses, so the relation
cannot disagree with the lexer about how far a clause moved.

### The offset stops at the AST

The elaborator drops it, so it never reaches `Surface.Expr`, the IR, the
machine or any correspondence proof. `t-float`/`g-float` carry it and pointedly
never read it: a position cannot affect whether a term is well-typed, and the
fact that it stops here is the statement that it cannot change what is
compiled.

**Relates**: D114, D117, D123 (the warning that needed it)

## D123: Warnings Are a PURE QUERY, and They Carry Numbers

**Date**: 2026-08-25 · **Status**: Implemented (plan 0.74 K4)

### The decision

    roundingWarnings : Arch → Module → List Warning

A function of the parsed module and the target. NOT threaded through `compile`,
and absent from `correct`. Warnings do not change what is compiled, so they must
not change the pipeline's type; keeping them a separate observation is what
stops them leaking into the theorem. `Once.Compile` re-exports them, which is
also what puts them on the extraction path.

### The constructors carry NUMBERS, not a string

A message is a projection and a projection is not checkable — D114's lesson,
one layer over. `TypeError` already works this way (`FloatNotRepresentable`
carried the decimal "so the message can quote it back"), and it matters more
here because the figures ARE the content. `renderWarning` is separate.

Both sides of the error are exact — the literal is a `Decimal` (D117), the
stored value is `m · 2^E` — so the difference is an exact rational and NO
FLOATING POINT is involved in computing it. `ExactQ` is unnormalised on
purpose: the figures are reported, not compared.

### ABSOLUTE and ULPS, absolute first

    3.1 b64   +2/(10·2^51) = +1/11258999068426240 ≈ +8.9e-17   +0.2 ulp
    3.1 b32   −4/(10·2^22) = −1/10485760          ≈ −9.5e-08   −0.4 ulp

The ulps are 0.2 and 0.4 — same order — while the absolute errors differ by
nine orders of magnitude. On a narrow enough format the ulps stay ~0.4 while
the absolute error reaches 3%. **A ulp-only warning would report the harmless
case and the catastrophic one identically**, which is the case a warning exists
for.

Silence on exactly-representable literals is pinned too: a warning channel that
fires on `0.5` is noise, and noise is how a warning channel dies.

### It replaces a dead error

`TypeError.FloatNotRepresentable` became unreachable when K3 made every float
literal well-typed, and is deleted. `FloatRounded` carries its three fields plus
the figures and the position: what used to abort the compile now reports.

**Relates**: D114, D116, D117, D118, D122

## D124: `-3.14` Is One Literal, and the Fold Is the ONLY Lowering It Has

**Date**: 2026-08-25 · **Status**: Implemented (plan 0.73 F3)

### The decision

`-3.14` was a TYPE ERROR — `inferElabV-RUnaryOp-aux` answered
`TypeMismatch Int Float`, because `t-neg`'s premise is at `Int` and `RFloat`
infers only at `Float`, so no derivation existed at all. It is now ONE literal
whose payload is `negate (decimalOf i f l)`, by a new rule

    t-neg-float : (i f l p : ℕ)
                → ctx ⊢ᵢ RUnaryOp OpNeg (RFloat i f l p) ∶ Float ⨾ zeroUsage

and D120's dispatch, widened from a `Maybe` to a three-way view.

### Why this is D120's route and not D120's argument

D120 folded `- <numeral>` because the alternative — "load 5, then call
`arith.neg.int`" — is a runtime negation of a compile-time constant, and
because a folded literal is what the spec's `negLits` already said `-5` means.
Both readings were available and one was better.

Here there is no second reading. `MArithIR` is `alit : ℤ → MArithIR sh`,
Int-only and monomorphic (F4), and `Surface.neg` is
`Expr Γ Ψ Int → Expr Γ Ψ Int`. A float negation is not expressible in the
surface syntax, let alone emittable. **The fold is not the better of two
lowerings; it is the only one.** That is also why `realize-infer` folds here
while it keeps `neg (int n)` for the `Int` case: it has nothing to keep.

### The rule is deliberately NOT general at `Float`

    ⊢ᵢ e ∶ Float ⨾ Ψ → ⊢ᵢ RUnaryOp OpNeg e ∶ Float ⨾ Ψ    -- REJECTED

would type `- x` for a float variable and `- someFloatRef` for a SigOp — F4's
arithmetic, which has no lowering. Narrowing the premise to `zeroUsage` does
not save it: a SigOp reference is `zeroUsage` too. A rule with no lowering is a
promise the backend then has to break, so the operand is pinned to the literal
in the rule's own index.

### The mechanism was already built, in D116

`Decimal.sig` is SIGNED — D116 chose that precisely so `-0.5` is `-5 /10^ 1`
and the sign survives a `(ℤ , ℕ)` split that would lose it. `round` reads the
sign through `signBit (sig d)` and the magnitude through `∣ sig d ∣`, so a
negated decimal takes the SAME rounding path with one bit different.
`Once.Float.Decimal.negate` existed with zero callers, and F3 is its first.

### What actually checks it — not the correspondence

Both the elaborator and `⟦ t-neg-float ⟧ᵢ` name the same `negate ∘ decimalOf`
and the same `round`, so `RealizeAgrees`' branch is `refl` and the
correspondence **cannot falsify `round`** — D117's trust point, and the third
time this shape has appeared on this branch. The checks that mean something are
elsewhere and are external:

  * Ten pins in `Once.Float.Decimal` against glibc/GHC patterns, including
    `-3.14` (inexact at both formats, so round-to-nearest-even runs on a
    negative significand) and `-16777217.0` at binary32 (a TIE, so the
    half-even rule has to break the same way on both signs).
  * `FloatEmitSpec` now runs `-0.5`, `-2.75` and `-3.14` on all three arches
    and reads the emitted machine word back out of the trace, comparing
    against GHC's own IEEE conversion.

### Two limitations, both stated rather than found

  * **`-0.0` compiles to `+0.0`.** `negate` is `ℤ.-` on the significand and
    `ℤ.- (+ 0) ≡ + 0`, so `signBit` reads `0`. Bounded exactly as D118's
    missing subnormals are: only `1/x`, `copysign` and the sign of a zero
    result can observe it, and Once has none of them because it has no float
    arithmetic at all. **If F4 lands, this is the first thing that must
    change**, which is why it is pinned in `Once.Float.Decimal`.
  * **A negative literal needs parentheses.** `emitF@T -0.5` parses as the
    SUBTRACTION `(emitF@T) - 0.5`: `-` is both prefix and infix, and an
    application ends at the first token that cannot start an atom. A grammar
    fact, unchanged by F3, and `-5` has always had it too.

### What it cost downstream, and the one thing that was not mechanical

The rule's index is `RUnaryOp OpNeg (RFloat i f l p)` — a COMPOUND index where
`t-neg`'s is a variable — so `CanonReflectMutual`, which inducts on the RAW
expression while the derivation is over `canonExpr … e`, could no longer split:
`canonExpr … e₀ ≟ RFloat i f l p` is stuck for an abstract operand.

The module's own header already said what to do — expose the head until the
index is in constructor form. Fourteen of the sixteen operand heads are
head-preserved by `canonExpr`, so the general clause still covers them and
`t-neg-float` dies on a constructor clash. `RFloat` is its own clause. `RVar`
is the one that stays stuck, and it gets `reflect-neg-var-ᵢ` — the boolean as
an explicit pattern argument, the same remedy `reflect-var-ᵢ` uses, with the
recursion passed IN so the descent stays visible to the termination checker.

`neg-non-Int-Float` in `ErrorProofs` is the lemma worth reading twice: it still
holds, but for a float LITERAL operand it is now vacuous — the failure premise
is what cannot hold, where before the operand's inference was. Read the other
way, it is a live check that the fold and the rule landed together: had the
elaborator folded without a rule in `_⊢ᵢ_∶_⨾_`, that `()` would not typecheck.

**Relates**: D054, D113, D116, D117, D118, D120, D122

## D125: `Int` Widens to `Float` Implicitly; `Float` Does Not Narrow to `Int`

**Date**: 2026-08-27 · **Status**: Decided (plan 0.75 F4) ·
**Amends OCP-0002's "domain separation"** · **Extends D116's argument**

### The decision

`1 + 1.5` compiles. The `Int` operand is converted to `Float` by a CORRECTLY
ROUNDED conversion, and the expression is a `Float`.

`Float → Int` is NOT implicit and needs an explicit conversion.

### What it replaces

OCP-0002 (implemented 2025-12-28) said:

> **Domain separation:** Mixing integers and floats is a type error.
> This prevents subtle precision loss from implicit conversions.

The concern was real; the remedy was inconsistent with what D116 later decided
for the identical phenomenon one step away.

### The argument is D116's, unchanged

`3.14` is not exactly representable, and D116 does not refuse it — it ROUNDS,
"because IEEE's promise INCLUDES rounding, exactly as `Int`'s promise includes
wrapping (D054)". An `Int` above `2^(sig-bits+1)` is not exactly representable
as a `Float` either. **It is the same phenomenon, and IEEE-754 says so
explicitly**: `convertFromInt` is a correctly-rounded operation, in the same
list as `+` and as decimal conversion. Refusing one while rounding the other
was two answers to one question — the shape D113's lesson says to look for.

**It is NOT D115's situation.** D115 refuses an out-of-range `Int` literal
because the target cannot hold that value AT ALL; the number has no
representation. An `Int` converted to `Float` always has one — approximately.
Absent and approximate are different failures.

### Measured, because the argument depends on the hardware agreeing

    (double)(2^53 + 1)     x86-64  0x4340000000000000
                           riscv64 0x4340000000000000

Identical, and the value is `2^53` — it rounded, quietly, the same way on both.
No per-arch divergence, so unlike D055 this needs no decision about WHICH
answer and no backend guard: both targets already implement IEEE's conversion.

### …and why the other direction is not symmetric

    (long long)1e300       x86-64  0x8000000000000000   ("integer indefinite")
                           riscv64 0x7fffffffffffffff   (SATURATES)
    (long long)NaN         x86-64  0x8000000000000000
                           riscv64 0x7fffffffffffffff

The hardware DIVERGES, and on ordinary out-of-range values rather than an
exotic corner. That is a third D055 situation, and it would need a decision
about which answer Once promises plus a guard on the losing target. It is also
a genuine narrowing where truncate-versus-round is a choice the programmer
should make rather than inherit. Both reasons point the same way, so
`Float → Int` stays explicit.

### NO WARNING for the conversion, and the reason is a BOUND, not a shrug

The compiler cannot know whether `x + 1.5` rounds — `x` is a runtime value. It
does not need to: correct rounding means the error is **at most half an ulp**,
and that same bound already covers `x + y` on two floats, and every arithmetic
result, and every rounded literal. Warning per site would mean warning on every
float operation in the program, which is exactly the noise D123's own header
says kills a warning channel:

> Silence on exactly-representable literals is pinned too: a warning channel
> that fires on `0.5` is noise, and noise is how a warning channel dies.

WHAT DOES WARN is the case where the exact answer is cheap and the position is
known — an `Int` LITERAL being widened whose magnitude exceeds

    2 ^ (sig-bits F + 1)        binary64: 2^53      binary32: 2^24

below which every integer converts exactly. That reuses D123's channel and its
rule unchanged: exact is silent, inexact reports with figures and a position.

### Where the rule goes

Two binop rules (`Int × Float` and `Float × Int`), not a general widening
judgment. A widening judgment would be the right factoring the moment
coercion is wanted at APPLICATION sites too — `f 1` for `f : Float → …` — and
whoever needs that should introduce it rather than add a third and fourth binop
rule.

A subsumption rule `⊢ᵢ e ∶ Int → ⊢ᵢ e ∶ Float` was rejected outright: it makes
inference ambiguous (`1` would infer at two types), and a unique inferred type
is what the bidirectional discipline and `infer-complete` are built on.
Subsumption belongs in CHECK mode, where `t-subsume` already lives.

**Relates**: D054, D113, D115 (the distinction that does NOT apply), D116, D118,
D123, D055 (why the other direction differs), OCP-0002 (amended)

---

## D126: A Closed EXPRESSION Lifts to a Constant Morphism, Not Just a Closed LITERAL

**Date**: 2026-08-28 · **Status**: Decided (plan 0.75, follow-on) ·
**Closes a gap between D018/D056 and the implementation**

### The decision

Where a pure or effectful arrow `X ⇒ B` is expected, an expression that

  1. infers at `B`, and
  2. reads no local variable (usage `zeroUsage`), and
  3. has no check-mode rule of its own

is the CONSTANT morphism `λ_. e`. One rule, `t-closed-lift`, grade-polymorphic
in the arrow's purity:

```
    ClosedLiftShape e     ctx ⊢ᵢ e ∶ A ⨾ zeroUsage
    ─────────────────────────────────────────────── t-closed-lift
    ctx ⊢ᶜ e ∶ (X ⇒[Many π] A) ⨾ zeroUsage
```

`g : Unit -> Int` with `g = 1 + 2` now typechecks. It did not before.

### What was wrong

D018 said "values, with implicit lifting to morphisms". D056 spelled it out: "a
value `v : B` used where a morphism is expected is the constant morphism". The
IMPLEMENTATION was narrower than the decision: the lift went through `⊢ᵍ`, which
ENUMERATES literal forms (`g-int`, `g-float`, `g-pair`, `g-In`, …). `1 + 1` is
not one of them, so it was rejected — with a message (`expected (Unit ω→ Int)
but got Int`) that describes the implementation's limit, not a language rule.
Nothing about `1 + 1` is less of a global element than `1` is.

### The side condition is not a hedge

`ClosedLiftShape` lists the shapes with no check-mode rule of their own. Without
it the rule fires on `λx. body` too, and then ONE expression has TWO check-mode
derivations at ONE type — `t-lam` and the lift — with different meanings. This
is the classic bidirectional side condition (subsumption applies to
non-introduction forms only), written out. The forms left out are each already
served: `RInt`/`RFloat`/`- <literal>` by the older value-lift (D018/D041/D124),
`RPair` by `checkPairLit` and `g-pair`, `RLam` by `t-lam` (which has no infer
rule at all, so the rule is not even statable there), `RApp` head-directed.

### Grade-polymorphic, because a lemma said so

`embedOrSubsume-lifts` says a check that succeeds at the pure arrow also
succeeds at the eff arrow. A pure-only lift makes that FALSE the moment a closed
expression lifts. The lemma is the guard that caught it — and its old proof,
which discharged every non-subsuming case as ABSURD ("the pure target never
subsumes, so it fails for every inferred `T'`"), is now a real proof.

### What it cost, and what that revealed

The realization is `λ_. e`, so the elaborator's and `realize`'s bodies differ by
`weaken`. Their agreement (`RealizeAgrees`) therefore needs

    ⟦ rename θ e ⟧ˢ fmt dδ ≡ ⟦ e ⟧ˢ fmt (restrictᴰ θ dδ)

which did not exist: `rename` had NO semantic justification anywhere, because
every construct that needed a closed subterm either carried it in the EMPTY
context (`cata`/`ana`) or embedded a pre-built IR morphism (`lift-morphism`).
D126 is the first construct that weakens a genuine subterm. The lemma is now
`Once.Denotation.ThinSound` — a plain structural induction, and reusable.

Three deciders had to be re-ordered to make any of this reduce (`≟T-⇒-aux`,
`≟k-aux`, `closed-lift-aux`) and `embedOrSubsume-no`'s first two type arguments
swapped so the EXPECTED type is matched first. The rule is the same in each
case: **a decider that insists on all its columns goes stuck on variables, and a
stuck decision HIDES every decision underneath it from a proof's `with`.** Same
decisions, same results, decided sooner.

### What `zeroUsage` does NOT mean (found while scoping the morphism half)

The premise says the expression CONSUMES no resource. It does **not** say the
expression READS no local, and in this semiring those differ:

    _*q_ : Zero *q _ = Zero

so `t-app`'s `Ψ₁ +ᵘ (q *ᵘ Ψ₂)` discards the argument's usage entirely at
`q = Zero`. A `Zero`-quantity arrow is writable today (`TCaret0`; the parser
test is `Int ⇒[ mk-kind Zero pure ] Unit`), so

    f : Int ^0-> Int
    λ x . … (f x) …          -- `f x` : usage zeroUsage, and MENTIONS `x`

is usage-closed while depending on the environment. Consequences:

  * **`strengthen : SExpr Γ zeroUsage A → SExpr ∅ [] A` is FALSE.** The two
    notions of "closed" in this codebase — empty context (`cata`/`ana`'s
    `Expr ∅ zeroUsage`) and zero usage in a non-empty context — are NOT
    equivalent. The first is strictly stronger.
  * **D126 is still sound**, because `⊢ᶜ` is context-indexed: `λ_. e` is
    constant in its ARGUMENT, which is all the check realm asks. The rule does
    not claim, and must not be read as claiming, environment-independence.
  * **The morphism realm cannot use this premise**, because `⊢ᵐ` realizes to a
    context-FREE `IR ⌊X⌋ ⌊A⌋`. That needs genuine independence, which only the
    empty context gives definitionally.

This is worth stating because the obvious reading of "zero usage = global
element" is the one QTT invites, and it is wrong here.

### The boundary: `compose` is NOT fixed by this

`compose f g`'s arms are MORPHISMS (`⊢ᵐ`, D063), a different realm with its own
constant rule `m-const`, which likewise takes a `⊢ᵍ`. So `compose exit@S (1 + 1)`
still fails; `compose exit@S 17` still works. The sibling rule
`m-closed : ClosedLiftShape e → ctx ⊢ᵢ e ∶ A ⨾ zeroUsage → ctx ⊢ᵐ e ∶ X ⇨[π] A`
is NOT a mechanical repeat: `realize-morph` produces an IR morphism DIRECTLY,
and `m-const` can only do that because `⊢ᵍ` derivations have `realize-global` —
a hand-written table (`intLit n`, `floatLit d`, …), one entry per literal form.
Closedness there is asserted by ENUMERATION, never derived. For a COMPUTED
closed expression the IR is `elaborate`'s output and there is no table entry.

By the section above, `m-closed`'s premise cannot be `zeroUsage` — strengthening
is unavailable because it is false. The locals-free context works for the
REALIZATION (`elaborate C.Heap (realize-infer d) ∘ terminal`, literally the line
`elaborate`'s own `cata` clause contains, related to the denotation by the
postulate-free `SourceFaithful.faithful`), and a prototype of exactly that
typechecks — rule, realization, meaning, elaborator route (termination
accepted), and the whole canon/poly family.

**Two things blocked it, in order.**

**(a) A soundness hazard, fixed.** Re-inferring in a CLEARED context resolves a
name the programmer SHADOWED: locals shadow imports (`t-var-import` carries
`lookupLocal ctx x ≡ nothing`), so with a local `x` and an import `x`,

    λ x . compose emit@E (x + 1)

infers `x` as the LOCAL in the real context and as the IMPORT in the cleared
one — the arm would compile to the import. Every existing morphism leaf avoids
this by carrying the non-shadowing premise EXPLICITLY; `⊢ᵍ` avoids it by
admitting no names. The fix is to require the context to have no locals AT ALL,
written as a context CONSTRUCTOR (`noLocals fresh imps polys sigEffs`) rather
than a side condition, so there is nothing to shadow and `debruijn` is `S∅`
definitionally. That covers every top-level definition body and honestly
excludes arms inside a lambda. It typechecks: rule, realization, meaning,
elaborator route (termination accepted), canon/poly family.

**(b) An ARCHITECTURAL boundary, which is where it stands.** `⊢ᵐ`'s
completeness statement is

    StrongElab … = Σ[ m ] Σ[ mᵐ ] … × (extract-morph-eff E ≡ just (m , refl))
                                    × (extractMorphWitness W ≡ just mᵐ)
                                    × (m ≡ realize-morph mᵐ)

That last component is a SYNTACTIC equality between the elaborator's IR and the
reference realization. It holds for every existing morphism because each is a
closed FORM — `IR.id`, `intLit n`, `⟨ m , m' ⟩` — built the same way on both
sides. It cannot hold for a morphism whose content is an ARBITRARY elaborated
expression: the elaborator's IR is built from its own `eE`, the reference's from
`realize-infer w`, and those agree only DENOTATIONALLY (that gap is the entire
reason `RealizeAgrees` exists).

Weakening the component to denotational equality is the right repair, but the
fact it would need — `⟦ eE ⟧ˢ ≐ ⟦ realize-infer w ⟧ˢ` — is
`RealizeAgrees.infer-agree`, and **`RealizeAgrees` imports `Completeness`**. The
fact lives ABOVE the layer that would have to use it. (`SourceFaithful.faithful`
is fine — nothing imports Completeness there — so only the infer half is
stranded.)

So `m-closed` is blocked on a completeness-layer question, not on a lemma:
either `StrongElab` splits (a weaker obligation for leaves whose IR is an
elaboration, keeping the strong one where the compose/case reconstruction needs
it), or the infer-agreement moves below `Completeness`. Both are architectural
and neither should be done in passing. The design that survives (a) is saved as
`d126-morphism-half.patch`.

**Relates**: D018 (the decision this implements), D056 (`composeArgB`'s
value-lift), D041 (the literal value-lift it generalizes), D063 (the realm split
that scopes it), D067 (the same grade-polymorphism argument for `t-value-lift`),
D124 (the negated-literal lift), D058 (IR-free judgment)

---

## D127: Composition Is Context-Indexed — One Lift, Written, and No Global-Element Realm

**Date**: 2026-08-29 · **Status**: LANDED 2026-09-03; plan
`0.76-context-indexed-composition.md` CLOSED and deleted (see "Where the plan
landed" at the end of this entry) ·
**Supersedes**: D018's lifting rule, D056 point 2, **D126 in full** ·
**Retires the TYPING half of**: D063's `⊢ᵐ` realm ·
**Reasoned from**: the CCC, and the OCP-0009 directed kernel's shape

### The decision

1. A `compose` / `case` / `pair` / `curry` arm is an **ordinary term of arrow
   type in the ambient context** — `Γ ⊢ e ⇐ A ⇒ B`. It need not be closed, and
   it need not be one of an enumerated list of forms.
2. **The value→morphism lift is written, never inserted.** `\_ -> e`, or the
   derived `const = curry fst`. There is no implicit rule taking a term of type
   `B` where `A ⇒ B` is expected.
3. Consequently `⊢ᵍ` as a *lifting* device, `t-value-lift`, `m-const` and the
   whole closed-form arm grammar are retired, and so is D126 — both the landed
   `⊢ᶜ` half and the blocked `⊢ᵐ` half.

`compose emit@E 5` stops being legal. `compose emit@E (\_ -> 5)` is how it is
written, and — the point — `\x -> compose emit@E (\_ -> x)` becomes legal too.

### Why: L1 and L2 are the same operation

Two liftings appear to be in play. They are one.

    L1  (context-indexed)   Hom(Γ,B) → Hom(Γ, A⇒B)     b ↦ curry (b ∘ π₁)
    L2  (global element)    Hom(1,B) → Hom(A,B)        v ↦ v ∘ !

Instantiate L1 at `Γ = 1` and transport along `Hom(1, A⇒B) ≅ Hom(A,B)`:
`curry (v ∘ π₁)` corresponds to `v ∘ π₁ ∘ ⟨!, id⟩ = v ∘ !`. That is L2. So there
is ONE lift — precompose with the projection, then transpose — it is natural in
`Γ`, and it is **total**.

**The partiality was never in the lift.** It was in *demanding the result be a
global element*, i.e. in the arm position, not in the operation. That is why
D126's `⊢ᶜ` rule and `m-const` kept wanting different premises: they are the
same rule at two bases, and only one of them was made to land somewhere
requiring `Γ = 1`.

### The space, and why this cell

Two independent axes, four cells:

|                                   | lift **written** | lift **inserted** |
|-----------------------------------|------------------|-------------------|
| arms must be global elements (Γ=1)| C                | A / B             |
| arms are Γ-indexed terms          | **F ← this**     | E                 |

A and B are not two designs; they are one done badly and done exactly. A (the
status quo) approximates "is a global element" by ENUMERATING syntactic forms —
which is why the list kept growing (`g-neg-int`, `g-neg-float`, D124/F3,
D126's `ClosedLiftShape`) and why a literal lifts while a name bound to that
same literal does not. B decides the condition exactly, and stalls elsewhere.

**Axis 1.** `Hom(Γ, A⇒B)` is a perfectly good object; nothing in the category
privileges `Γ = 1`. Requiring it is a REPRESENTATION property — "this composite
needs no closure" — promoted into the typing judgment.

**Axis 2.** The lift is total and canonical, so inserting it can never fail or
surprise; that is the honest case for implicitness. Against it: OCP-0006's
criterion makes the source language the spec, so the term you write is the term
whose meaning is defined, and insertion breaks that identity.

F is the only cell needing **no side condition anywhere**. A, B and C each must
answer "is this arm a global element?" — guessed, decided, or supplied.

### What the OCP-0009 kernel contributes

Not an argument from precedent — from shape. The directed kernel has exactly
two judgments, `Γ ⊢ t ∷ A` and `Γ ⊢ty A`, **both context-indexed, with no
context-free realm**: `Hom A t u` is a type IN A CONTEXT and its inhabitants are
ordinary terms. Its only implicit rule is `⊢conv`, which changes nothing; the
point→arrow passage `hrefl` is a NAMED constructor; and a side condition
guarding a semantic boundary is a judgment premise in `Spec/` (`Variance`),
deliberately — *"part of what the theory is, not a theorem about it"*. Both axes
above land where that kernel already is.

### What this costs, stated plainly

Context-indexed composition is built from exponentials:

    compose f g  =  curry (apply ∘ ⟨ f ∘ π₁ , apply ∘ ⟨ g ∘ π₁ , π₂ ⟩ ⟩)

so the direct `IR.∘` emission that D044/D045/D056 established is no longer what
the typing judgment hands you. Two consequences, and neither may be waved:

- **Closed arms must still emit `IR.∘`.** That becomes a PROVED SPECIALIZATION —
  one equation, discharged once — and explicitly NOT a general optimizer pass.
  D039 found the optimizer unsound (it dropped effectful SigOps), which is why
  D044/D045 removed the dependency; F must not reintroduce it.
- **`⊢ᵐ` was FORCING something.** D063's realm exists so `realize-morph` is total
  and the categorical laws are forced through the agreement bridge. Retiring the
  realm as a typing distinction does not retire that obligation; where the laws
  get forced instead is an open item the plan must answer, not assume.

### Consequences

- `compose emit@E 5` and friends stop compiling; migration is 5 sites.
- `cata`'s algebra is currently a `⊢ᵐ` morphism. Under F it becomes a
  Γ-indexed term, which admits a capturing algebra — a real semantic widening,
  to be decided deliberately rather than inherited.
- `Once.Denotation.ThinSound` (added for D126's `weaken`) loses its only
  consumer unless the new elaboration needs it.

**Relates**: D018 (the lifting this replaces), D056, D063, D044/D045, D039 (why
the fast path must be proved, not optimized), D126 (retired), OCP-0006 (source
is spec), OCP-0009 (the kernel whose shape this follows)

---

### Where the plan landed (closure note, 2026-09-03)

Plan 0.76's phases are all done and the file is deleted; this is its record.

* **Phase A** (judgment) — `⊢ᵍ` and `⊢ᵐ` deleted; 4 judgment forms -> 2,
  62 rules -> 51. `composeMid` survived as A3 required.
* **Phase B** (elaboration) — arms check with `checkElabV` at the arrow type;
  `extract-morph-eff` / `extractMorphWitness` died with the realm; the
  target-driven literal dispatch is gone.
* **Phase C** — **O1 discharged**: closed arms still emit `IR.∘`, as a PROVED
  equation used in codegen only, never as a typing-side premise.
* **Phase D** — **O2 ANSWERED in D133**, which is the load-bearing result: the
  question's premise was wrong. `⊢ᵐ` was buying a HYPOTHESIS, and binding the
  arm removes the need for it. The plan named "O2 unanswered" as its honest
  failure condition, so D133 is what let this close rather than re-open D127.
  `StrongElab` and `morph-elab` disappeared with it.
* **Phase E1/E2** — the five literal-arm surface sites rewritten to `\_ -> …`;
  `closed-expr-lift.once` retired (it tested D126); the test D127 is FOR — an
  arm capturing an enclosing binder — added.
* **Phase E3** — the gate ran green EXCEPT the island backstop, which cannot
  pass for reasons predating this branch. **That is plan 0.83's**, not an
  unfinished part of 0.76.

Risk 3 of the plan (the cata algebra widening to admit a CAPTURING algebra)
was taken deliberately as its own decision — see D131.

## D128: Float `/` Is Correctly Rounded and TOTAL; Float `%` Has No Lowering

**Date**: 2026-08-29 · **Status**: Decided (plan 0.73 follow-on) ·
**Follows**: D113 (Float follows D054), D055 (total division, one semantics)

### The decision

`/` on `Float` compiles. Its meaning is `Once.Float.Arith.fdiv` — the
correctly-rounded quotient — and it is TOTAL in D055's sense: `x/0` is a signed
infinity, `0/0` the canonical NaN, no traps, the same answer on every target.

`%` on `Float` does NOT compile, and that is not an oversight.

### Why `/` needed more than `+` and `*`

Dyadics are closed under addition and multiplication, so `roundB` receives the
EXACT result and rounds once. A quotient of two dyadics is in general not a
dyadic (`1/3`), so there is nothing exact to hand it. The remedy is the
standard one: compute enough quotient bits that the rounding position is
strictly above the last one, and fold "the division was inexact" — a non-zero
remainder — into that last bit. `roundB`'s half-even is then correct, because
the only case it can get wrong is an exact tie, and a non-zero remainder is
exactly the evidence that the tie is not exact.

**The guard shift is `+ 3`, not `+ 2`, and this is the part worth recording.**
With `+ 2` the quotient carries exactly ONE discarded bit — which is the round
bit — so the sticky is folded into the very decision it is meant to inform, and
`1.0 / 3.0` answers one ulp high. Two discarded bits, so the LSB lies strictly
below the rounding position.

`0.1 / 0.3` is the pin that discriminates: it answers ONE ULP ABOVE
`1.0 / 3.0` despite both being `0.333…`, because the operands are themselves
rounded and the true quotient falls the other side of the boundary. A divider
that truncated, or that rounded without the remainder, passes every other pin.

### Why `%` is refused

IEEE's `fmod` is a DIFFERENT function from integer remainder — it is exact,
not correctly rounded, and defined by repeated subtraction. D055's identity

    a = (a / b) * b + (a % b)

which ties Once's integer `/` and `%` together, does not survive rounding: the
rounded quotient times `b` is not `a` minus the exact remainder. So `%` is not
"division's other half" at `Float` the way it is at `Int`, and pretending
otherwise would make one operator mean two things.

It therefore needs its OWN decision — what Once's float `%` is, if it is
anything — before it can have a lowering. Until then `isFloatArithmeticOp`
refuses it at the source and the refusal is PINNED in `ElaborateProofs`, so
lifting it cannot happen silently.

### Consequences

- `adiv` in `MArithIR` is grade-polymorphic; `amod` stays `Int`-only.
- `Xfdiv-rrr` is THREE-address, unlike its commutative float neighbours: `dst
  := dst op src` cannot express `a / b` when `dst` is `b`, which is exactly the
  register assignment `compile-go` produces. The integer divide is three-address
  for the same reason.
- `divsd` / `divss` / `fdiv.d`, with D055's NaN canonicalisation after it on x86.

**Relates**: D054, D055, D113, D116, D117, D118 (±∞ on overflow, which `x/0`
now also produces)

---

## D129: WHICH Leaf a Load Reads Is a PROGRAM Fact — Typed Paths in the IR, a WF Relation Beside the ISA

**Date**: 2026-08-30 · **Status**: Decided (plan 0.72 item 6) ·
**Follows**: D112 (Float's representation is a parameter), D063 (realms)

### The decision

`ainput` in `MArithIR` carries a TYPED path — `Path sh n`, a witness that the
shape `sh` really has a leaf of numeric kind `n` at that position — instead of
an untyped `InputPath` that `project` might answer `nothing` for. The abstract
ISA below it stays untyped: `compile-go` ERASES the witness through `⌊_⌋ᴾ`,
and the fact travels beside the emitted program as a well-formedness relation
(`LoadOK` / `LoadsWF`) that the compiler DISCHARGES by induction on the IR.

### What was wrong

`R-input` — the call-site's promise about how the argument is laid out — said

    pl s-conc p ≡ fromℤ (maybe-zero (project sh p (input s-abs)))

for EVERY `InputPath p`: the concrete load equals the INTEGER reading of the
bytes there. A float leaf's bytes are a pattern, `project` answers `nothing`
there, and the relation asserts the load reads `0`. So a block with a float
PARAMETER could not satisfy its own precondition, and `Xmov-farg`'s step lemma
was a postulate (`float-arg-sim`).

That looked like a proof gap and was not one. The missing information — which
leaf this load reads — is chosen by the PROGRAM. No relation between two
STATES can recover it, so no amount of work on the state relation closes it.
(The general form: a residual bounding something the program decides, from
only a state correspondence, is refutable — the interface has to widen.)

### Why not the two alternatives

**Quantify `R-input` over untyped paths and make the ABSTRACT machine read the
raw leaf word.** This does make `Xmov-arg` and `Xmov-farg` the same operation
and needs no WF relation at all — but the premise then also constrains paths
that no shape has, demanding the concrete load answer `0` there. An arch that
cannot supply that makes the premise unsatisfiable and the whole correspondence
VACUOUS, which is the failure this codebase has already paid for once.

**Index the ISA by the shape.** Twenty instruction constructors would carry a
parameter that two of them use. The type belongs where the type information
is — in the IR — and the erasure boundary is exactly where it should stop.

### Consequences

- `R-input` quantifies over `Path sh n` only: true at BOTH leaf kinds, and
  stated only about paths that exist. Not vacuous, and not a narrowing.
- `R-step-arg` and `R-step-farg` are the SAME proof twice, and every arch
  discharges the new `rt-farg` with the same lambda as `rt-arg` — a float
  load is a load, and only the abstract reading of the bytes ever differed.
- `compile-loads` proves `LoadsWF sh (emit-program (compile-abs e))` for every
  `e`: `compile-go` emits `Xmov-arg`/`Xmov-farg` only from an `ainput`, so the
  erased path is handed straight back as its own witness. The relation is
  therefore invisible above `arith-block-correct` — no dispatch module, and no
  arch, takes it as a new premise.
- `project-path` / `projectF-path` replace the four leaf lemmas that used to
  case-split the shape by hand; the recogniser refuses a wrong-kinded chain via
  `typePath?` rather than by defaulting.
- The residual is GONE, not narrowed: `float-arg-sim` and its `IsFloatArg`
  guard are deleted.

**Relates**: D112, D113, D054

---

## D130: Composition Is LINEAR in Each Arm — the Term Language Was the Thing That Was Wrong

**Date**: 2026-08-30 · **Status**: Decided (plan 0.76 Phase B) ·
**Follows**: D127 (context-indexed composition), OCP-9 (QTT multiplicities)

### The decision

A context-indexed combinator's usage is the SUM of its arms':

    ctx ⊢ᶜ f ∶ (B ⇒[Many π] C) ⨾ Ψ₁     ctx ⊢ᶜ g ∶ (A ⇒[Many π] B) ⨾ Ψ₂
    ───────────────────────────────────────────────────────────────────
       ctx ⊢ᶜ compose f g ∶ (A ⇒[Many π] C) ⨾ (Ψ₁ +ᵘ Ψ₂)

and `Surface.Expr` gains four PRIMITIVES — `comp'`, `copair'`, `fork'`,
`curry'` — whose typing rules state that directly, one per judgment rule.

### The question D127 left open

D127 made the arms ordinary terms in the ambient context. That makes their
usage visible for the first time, and three readings are available:

| | `compose f g` costs | |
|---|---|---|
| linear | `Ψ₁ +ᵘ Ψ₂` | **chosen** |
| as-encoded | `Ψ₁ +ᵘ (Many *ᵘ Ψ₂)` | asymmetric |
| closure-conservative | `Many *ᵘ (Ψ₁ +ᵘ Ψ₂)` | |

They differ observably: whether a LINEAR local may be captured in a
`compose` arm.

### Why linear, and why QTT does not decide it

**QTT's lambda does not scale its captured context.** Atkey's rule — and
`Surface.lam` — passes `Ψ` through untouched, popping only the bound
variable's head usage. So "the closure is callable many times, therefore its
captures cost `Many`" is not how QTT counts; repeated calling is charged
where the closure is USED. That removes the third reading.

**Composition is linear in both arguments.** `comp : (B⇒C) × (A⇒B) →
(A⇒C)` uses each component of its pair exactly once — visible in its own
definition, `curry (apply ∘ ⟨fst∘fst, apply ∘ ⟨snd∘fst, snd⟩⟩)`. There is no
reading on which `g` is used more often than `f`, so the second reading's
asymmetry cannot be a fact about `∘`.

Where does that asymmetry come from, then? From encoding composition as an
APPLICATION. QTT's application rule `Γ + q·Δ ⊢ f x : B` scales the argument
by the arrow's grade because a `Many`-graded function MAY duplicate its
argument. That is correct for an arbitrary function and simply not what `∘`
does.

**So QTT supplies the bookkeeping; the category decides the rule.** The
usage index should record what composition is, and composition is bilinear.

### What it cost, and why that was the right direction

Every eliminator the term language had — `app`, `effApp`, `morph-app` —
scales its argument. So the term language could express only the
conservative reading. Rather than weaken the spec to fit it (the inversion
D057 and D114 were both written to stop), the TERM LANGUAGE gained the four
primitives, and the linearity is DISCHARGED in `Once.Surface.Elaborate`
rather than assumed: each elaborates to a closed CCC morphism composed with
`⟨ arm₁ , arm₂ ⟩`, and the pairing is what makes "each arm once" true.

### The bug this immediately caught

The first elaboration fused the arms inward —
`curry (apply ∘ ⟨ f ∘ fst , apply ∘ ⟨ g ∘ fst , snd ⟩ ⟩)` — which puts them
UNDER the `curry`. An arm that emits would then re-emit on every call of the
composite, and the trace would not match `⟦ comp' f g ⟧ˢ`, which binds both
arms outside the function it returns. The closed-morphism form
(`compIR ∘ ⟨ ef , eg ⟩`) runs each arm once, at build time.

**The usage index and the trace semantics were saying the same thing**, and
the encoding disagreed with both. That is the value of having the resource
annotation at all: it made a trace-level defect visible as a type error.

### Consequences

- `copair'` needs distributivity `Γ × (A + B) → (Γ × A) + (Γ × B)`, which
  never arose while `case` arms were closed. DERIVED (`distribIR`), not a new
  IR primitive.
- The four `IR` morphisms are closed and arm-free, which is what lets 0.76's
  O1 (closed arms still emit `IR.∘`) be stated about them alone.
- A linear local may NOT be captured in a compose arm and then have the
  composite called twice — the rule now says so.

**Relates**: D018, D056, D063, D127, OCP-9

---

## D131: A Cata's Algebra Is OBTAINED Once and APPLIED Per Layer — the Fold Rebuilds It, and That Is a Codegen Gap

**Date**: 2026-08-31 · **Status**: Decided (plan 0.76 Phase D) ·
**Follows**: D130 (composition is linear), D127 (context-indexed composition)

### The decision

`cata`'s algebra arm is evaluated ONCE, like every other combinator arm:

    ⟦ cata alg ⟧ᶜ dγ  =  ⟦alg⟧ᶜ dγ >>=T λ f → returnT (cata-sem f)

No special restriction on the algebra, and no separate realm for it. The
meaning is uniform with `comp'`/`copair'`/`fork'`/`curry'`.

The COMPILER does not do this yet: `Surface.Elaborate` emits

    Cata wfF (apply ∘ ⟨ elaborate alg ∘ terminal , id ⟩)

and `Cata`'s algebra runs per layer, so `elaborate alg ∘ terminal` is
re-entered on every layer of the fold. That agrees with the meaning only when
the algebra's BUILD is effect-free. That premise is now a NAMED residual, and
its removal is the parameterized-cata plan.

### Two claims that look alike and are not

1. **The algebra must be an arrow.** True — `cata-sem` consumes
   `⟦F A⟧ᴰ → T ⟦A⟧ᴰ`, a Kleisli arrow. Effects DURING the fold are the
   algebra's own and are legitimate; an effectful fold is a normal thing.
2. **The algebra expression must be effect-free to build.** NOT a mathematical
   requirement. It is a restriction.

Binding supplies (1) on its own: run the arm's computation once, obtain the
arrow, fold with it. An earlier draft of this decision required (2) — as a
typing-level "morphism shape" premise — on the grounds that it was "the
mathematically exact reading". It is not. It is the reading that makes the
CURRENT codegen sound, which is a different thing, and adopting it would have
let an implementation shape dictate the language definition (D057, D114).

### What this says about O2

Plan 0.76 owes O2: `⊢ᵐ`'s structural recursion forced facts that its deletion
must re-establish. This is the first concrete instance, and it is worth
naming precisely.

`CataFold.cata-fold-eq` does not assume the algebra is well-behaved — it takes

    ⟦ algE ⟧ˢ tt ≡ liftD m

as a HYPOTHESIS, and today that hypothesis is discharged by
`RealizeAgrees.extract-morph-eff-denotes`: the algebra EXTRACTS to an IR
morphism. `extract-morph-eff` is exactly what D127 deleted. So one of the
things `⊢ᵐ` was forcing is precisely "the algebra is a fixed morphism, not a
computation that produces one" — and with the realm gone, the fact has to come
from somewhere else. Under this decision it comes from the codegen actually
building the algebra once (the plan), and meanwhile from a named premise.

### Why not the alternatives

**Thread the algebra per layer in the MEANING** (making `⟦_⟧ᶜ` match the
emitter). Cheapest, and it destroys what `cata` means: with a re-derived,
possibly-effectful algebra at each layer there is no algebra, only a family,
and initiality no longer gives a unique mediating morphism. It would not be a
catamorphism. Rejected.

**Require the algebra to be morphism-shaped in the JUDGMENT.** Sound, no
codegen change, and it makes the current emitter correct. But it restricts the
language for the compiler's convenience, and it re-imposes on `cata` exactly
the kind of realm restriction D127 removed everywhere else — for a reason that
turned out not to be mathematical. Rejected as the primary answer; it remains
the fallback if the parameterized cata proves infeasible.

### Consequences

- `IR.Cata`'s algebra has domain `⟦F⟧TI C` with no environment slot, so
  hoisting needs a closed `CataM : IR (F C ⇛ C) (μF ⇛ C)` — the parameterized
  catamorphism — making the elaboration `CataM wf ∘ elaborate alg`,
  structurally identical to `compIR ∘ ⟨ ef , eg ⟩`.
- That also removes a PER-LAYER CLOSURE ALLOCATION: `elaborate alg ∘ terminal`
  is a `curry`, and heap-mode `curry` allocates (`CurryAllocWF.run-curry-heap`).
- Until then the named premise stands, classified deferred-proof/model-gap —
  not an axiom, and not a narrowing of the observable.

**Relates**: D127, D130, D057, D114

---

## D132: Plan 0.36's Nat-Shape Attack on `cata-correct` Is DELETED — Per-Shape Witnesses Were Never Going to Be the Theorem

**Date**: 2026-08-31 · **Status**: Decided (plan 0.76 / D131 migration) ·
**Follows**: D131 (parameterized cata)

### The decision

Eleven modules are deleted: `CCC/Codegen/CataNat{BuildLayer,Chain,Descend,
DescendComplete,DescendRun,Heap,HeapExtract,Producer,Seam}`,
`CCC/Codegen/CataAtRelocate`, and `CCC/Machine/IR/NatCataProof` — 2189 lines.

TEN of them were plan 0.36 task #8's attack on `IRObsCorrectFlat.cata-correct`,
carried out for the SHAPE `NatF = K Unit ⊕ Id` and never generalized. All
eleven are unreachable from every gate root (Compiler, Certified, the three
Targets, Spec/Correct, ErrorProofs) and nothing outside the set imports them.

**`CataAtRelocate` is the exception and is recorded separately here, because
an earlier draft of this entry wrongly lumped it in with the Nat attack.** It
is FUNCTOR-GENERIC: per-instruction relocation for the flat machine, saying
that running an instruction in a big program at a pc shifted by `k` equals
running it standalone and shifting the result. Its design finding is worth
keeping: the shift belongs on the RIGHT (`fpc fs + k`), and with that choice
every case is `refl` or definitional with NO arithmetic lemmas — a straight
step gives `suc (fpc fs) + k = suc (fpc fs + k)` definitionally, and a jump
lands at `q + k`, matching `find-label-distrib`'s `p + length pre`. Jumps
carry their relocation as a hypothesis; straight steps go through the
`StraightStep` classifier, so the ~16 non-control constructors need no
enumeration. ANY future attack on `cata-correct` — or on any embedded-
subprogram correspondence — wants this module back; recover it from git
rather than rederiving it.

`cata-correct` REMAINS a live named postulate in `IRObsCorrectFlat`. Deleting
its abandoned partial attack does not change that, and does not change the
residual count except downward: `NatCataProof` carried two postulates and a
`{-# TERMINATING #-}` pragma, all of which go.

### Why they were never going to work

A per-shape witness is not a theorem. `cata-correct` quantifies over every
well-formed functor; a proof for `NatF` discharges the `NatF` instance and
tells you nothing about `F ⊗ G`. The general obligation needs a proof that
case-splits the functor, and the Nat modules were a scaffold for reading off
what such a proof would need — not a step toward it.

Surfaced by D131's migration: they would each have needed the parameterized
`Cata` threaded through, which is real work spent on a path that is already
recorded as dead.

### The two findings worth keeping

1. **μ-values are NOT universally Heap.** `In-valid-bf` is mode-polymorphic —
   a μ-value's mode is its layer's mode — so a cata descend needs a Heap-
   UNIFORMITY precondition on its input, not an assumption. `CataNatProducer`
   called it `AllHeap`: a mode-polymorphic recursive predicate over the
   validity derivation asserting `mB ≡ Heap` at each cons. Anything that
   later attacks `cata-correct` in heap mode needs that predicate or its
   equivalent, and will otherwise get stuck at exactly the cons recursion.
2. **The descend/ascend split was the right decomposition** (descend to the
   base, then `build-layer` on the way up); what was wrong was fixing the
   functor while doing it.

### Not deleted

The other nineteen islands stay. In particular `Once.Category.Laws` and
`Once.Semantics.Value.Laws` — the categorical laws — are unreachable too, and
that is a question about the correctness statement, not dead code. It is
recorded against O2 rather than resolved by a deletion.

**Relates**: D131, D102 (the dead path is the checklist — read it before
deleting it; this entry is that reading)

---

## D133: O2 ANSWERED — What `⊢ᵐ` Was Forcing Was a HYPOTHESIS, and Binding the Arm Removes It

**Date**: 2026-09-01 · **Status**: Decided (plan 0.76, O2) ·
**Follows**: D127 (context-indexed composition), D130, D131

### O2 as posed, and why the premise was wrong

Plan 0.76 owed O2: `⊢ᵐ`'s structural recursion over the combinators "forces the
categorical LAWS through the agreement bridge", so deleting the realm must
re-establish that forcing.

**The premise does not survive the evidence.** `Once.Category.Laws` — the CCC
laws — has been imported exactly ONCE in the repo's history, by the 2025-12-13
verified-optimizer commit, whose correctness module is itself an island and
whose optimizer D039 found unsound. The agreement bridge (`faithful`,
`realize-agrees`) never imported it, in any commit, and proves every case
COMPUTATIONALLY. Nothing was forcing the laws, because nothing consumed them.

So O2's real question is **"what did `⊢ᵐ` actually buy?"**, answered case by
case rather than in one stroke.

### The answer, for the case that mattered

`⊢ᵐ` was supplying a HYPOTHESIS: **the arm is a fixed morphism, not a
computation that produces one.**

Concretely, `CataFold.cata-fold-eq` took

    ⟦ algE ⟧ˢ tt ≡ liftD m-alg

as a premise, and it was discharged by `RealizeAgrees.extract-morph-eff-denotes`
— i.e. by the algebra EXTRACTING to an IR morphism, which is exactly what the
realm guaranteed. Delete the realm and the premise has no supplier.

**D131 removes the need for it rather than re-supplying it.** With the algebra
BOUND (obtained once, carried by the parameterized fold), the replacement
lemma is

    cataM-fold : liftFn (cataM wf Heap) c ≡ returnT (cata-sem wf c)

which takes **no hypothesis at all**. `Once.Adequacy.CataFold` is deleted; its
one export existed only to serve the extraction path.

### The same phenomenon, one module earlier

`FaithfulLemmas.cata-body` used to need `alg-eq`, a per-layer agreement
between the IR algebra and the surface one, because the elaborated fold
REBUILT the algebra each layer while the denotation bound it. With both sides
binding, `cata-body` is a bind-congruence over a shared computation plus one
per-closure equality, and `alg-eq` is gone.

**Two proofs got SMALLER.** That is the strongest evidence available that the
model change was right rather than merely defensible: a change that only
relocated a difficulty would have moved the work, not removed it.

### The rule this yields

When a typing realm is deleted, do not ask where its THEOREMS are re-proved.
Ask which PREMISES it was silently discharging, and for each one decide
whether to re-supply it or to change the model so it is not needed. Here the
second was available, and it was also the mathematically correct reading
(D131) — the two coincided, which is usually the sign of a real fix.

**Relates**: D039, D127, D130, D131, D132; plan 0.79 §4 carries the laws half.

---

## D134: A DECISION PROCEDURE Is Not a Typing Rule — the Spec Names Properties, the Elaborator Names Deciders

**Date**: 2026-09-01 · **Status**: Decided; plan `0.80-declarative-typing-rules.md` ·
**Phase A landed**; Phase B is the same principle at a real cost, deferred
**Follows**: D044, D045 (locally-decidable bidirectional typing), OCP-0006

### The decision

A typing rule states a PROPERTY. It does not state that a particular decision
procedure returned a particular answer.

`Once.Spec.Typing` IS `Once.TypeCheck.Judgment`, re-exported verbatim — so the
declarative judgment is the language definition. Eight of its premises were
calls to the elaborator's own deciders. Phase A removes four:

    wellFormedF? F ≡ just wfF   ⟹   WellFormedF F        (t-cata-check, t-In-app-check)
    isGround schema ≡ inj₁ g    ⟹   Ground schema        (t-var-poly-instantiate-infer)
    isGround schema ≡ inj₂ tt   ⟹   ¬ (Ground schema)    (t-var-poly-instantiate)

### Why this is not a matter of taste

**An algorithm in the denotational spec makes the correctness theorem
circular.** Correctness must reference the spec — that is what it means to
prove a compiler correct. If the spec in turn references the compiler's search
strategy, "the compiler agrees with the specification" degenerates toward "the
compiler agrees with itself". The mechanical symptom is that a change to
`Once.Functor.Decide` silently changes the set of well-typed programs, and no
file under `formal/Once/Spec/` moves.

It is the same defect D127 removed one level up: `⊢ᵍ` approximated "is a
global element" by ENUMERATING syntactic forms, and the list kept growing.
Here the rules approximated "is well-formed" / "is ground" by naming the
procedure that checks it.

### What it costs, and where the cost went

Nothing, in extension: the deciders are sound and complete for their
properties, so exactly the same judgments are derivable. What was ASSUMED by
putting the decider in the rule is now PROVEN once, in
`Once.TypeCheck.DeciderComplete`:

  * `wellFormedF?-complete`, `isGround-complete` — property ⟹ the decider's
    answer (what the completeness proof needs);
  * `isGround-inj₂-¬Ground` — the decider's `inj₂` refutes the property (what
    the elaborator needs, having only its own dispatch);
  * `Ground-irrelevant`, and the pre-existing `WellFormedF-irrelevant` — the
    rule's witness is no longer pinned to the decider's output, so the two must
    be identified. Both properties are propositions, so this is available.

That trade is the point: the obligation was always there; the decider premise
was hiding it inside the language definition.

### Why Phase B is separate and NOT decided here

The other four premises — `classifyAppHead f ≡ nothing` on
`t-app`/`t-effApp`/`t-arg-driven-app-check`, and `composeMid ctx f g A ≡ just B`
on `t-compose-check` — do a DIFFERENT job. They are not deciders standing in
for properties; they make derivations essentially unique. And this system
defines the MEANING by recursion on the derivation (`⟦_⟧ᶜ`, by direct induction
on `_⊢ᶜ_`), so uniqueness is currently what makes the denotation well-defined
without a coherence theorem, and what makes `check-complete` hold by
construction.

Removing them is still right — compose denoted correctly is

    Γ ⊢ f ⇐ B ⇒ C    Γ ⊢ g ⇐ A ⇒ B   ⟹   Γ ⊢ compose f g ⇐ A ⇒ C

with `B` existential, which is what the rule already says once the premise is
deleted — but it owes coherence of `⟦_⟧ᶜ` over the ambiguity introduced, and a
restated completeness. That is the trade D044/D045 made deliberately, and it
is re-opened by plan 0.80 Phase B rather than by this entry.

### A consequence worth naming

Plan 0.76 Phase E left three `TraceSpec` programs unwritable:
`compose (\_ -> 0) (compose emit@E (\_ -> 42))` has no derivation, because
`composeArgB` cannot recover a constant-function arm's codomain — the D018
clause that used to do it keyed on the literal spelling D127 moved. TODAY that
is a LANGUAGE question, because `composeMid` is in the rule. AFTER Phase B it
is a completeness question about the elaborator: improve the search, reach more
programs, no spec change. Which is the whole reason to do Phase B.

**Relates**: D018, D044, D045, D127, OCP-0006

---

## D135: A Constant-Function Arm's Codomain Is Its Body's Type — D018, Re-Spelled for D127

**Date**: 2026-09-01 · **Status**: Decided (restores a D127 regression) ·
**Follows**: D018 (global elements), D127 (the lift is written), D044/D045

### The decision

`Classify.composeArgB` recovers a `compose` arm's codomain from a WRITTEN
constant function, not only from a bare literal:

    composeArgB ctx (RLam _ (RInt _))   _ = just Int
    composeArgB ctx (RLam _ (RFloat …)) _ = just Float
    composeArgB ctx (RLam _ (RStringLit _)) _ = just Str
    composeArgB ctx (RLam _ RUnit)      _ = just Unit

### Why: this is a REGRESSION FIX, not a new capability

D018 gave `composeArgB` the clause `RInt _ → just Int`, on the grounds that a
literal arm IS the constant morphism and its codomain is therefore known. D127
then removed the implicit value-lift, so that same constant morphism is now
SPELLED `\_ -> 42` — and the D018 clause stopped firing. The rule did not
change; the syntax it keys on moved out from under it.

The visible effect was that programs which compiled on `master` stopped
compiling, in a shape with no working rewrite:

    main = compose exit@S (compose 0 (compose emit@E 42))          -- master: OK
    main = compose exit@S (compose (\_ -> 0) (compose emit@E (\_ -> 42)))
                                                                   -- D127: rejected

The nested case is the one that breaks: `composeMid` recovers the middle type
from the second arm's codomain or the first arm's domain, and after the rewrite
BOTH are lambdas, which revealed nothing. Three `TraceSpec` cases caught it.

### Why it stays a literal enumeration

Because `composeArgB` cannot consult inference. `t-compose-check` names
`composeMid`, so `Once.TypeCheck.Classify` sits BELOW the judgment and calling
the typechecker from it would be circular. It is therefore a hand-rolled
partial synthesizer, and this entry extends it by exactly the cases D018
already covered.

That is a symptom, not a design: plan 0.80 Phase B takes `composeMid` out of
the rule, after which `composeArgB` is purely the elaborator's search and
improving it is a COMPLETENESS result rather than a language change. D134
records why that is right; this entry is what the language needs until it
happens.

### The honest cost

While `composeMid` remains a premise of `t-compose-check`, this changes the
set of well-typed programs — a language change, hence this entry. It is
strictly a widening, and every program it admits was admitted on `master`.

**Relates**: D018, D044, D045, D127, D134

---

## D136: A User MAY Define `fst` — Generators Get a Reserved NAMESPACE, Not Reserved WORDS

**Date**: 2026-09-01 (decision taken 2026-06-26 in
`plans/0.50-canonicalize-generators.md`; this entry is the record it owed) ·
**Status**: Decided · **SUPERSEDES D001** ·
**Follows**: D050 (canonical names), D064 (named defs are morphisms)

### The decision

The twelve categorical generators are identified by a CANONICAL NAME the
compiler owns — `canonical ["Generators", g]` — not by a reserved bare string.
A user may therefore define `fst`, `pair`, `case`, … in their own module: their
`User.Module.fst` and the generator `Generators.fst` are DIFFERENT NAMES, and
ordinary scoping resolves a reference to whichever is in scope.

D001 said the opposite ("Generators are reserved words … users cannot define
variables named `fst`"). D001 is superseded.

### Why D001 was wrong, and how it showed

D001's rationale was that reserving twelve names is a minor cost and makes
elaboration simpler ("no need to check for shadowing"). Both halves failed.

**It was not simpler — it was a collision.** `classifyBareBuiltin : String → …`
and `classifyAppHead` dispatch on the bare string `"fst"`, so a user's `fst`
and the generator share ONE IDENTITY SPACE. The reservation was never actually
enforced at the parser (D001 assumed it would be); what happened instead is
that the builtin silently wins:

    fst : Int -> Int
    fst x = x
    test = fst 5        -- "fst requires a pair argument"

The user's definition is unreachable and the error message is about a function
they did not call. That is a bug, and it was recorded as one in plan 0.50 on
2026-06-26 — this entry is that decision finally written down.

**It was not minor, because the cost was paid in the SPEC.** The collision has
to be excluded somewhere, so it leaked into the typing rules as side
conditions: `t-app`, `t-effApp` and `t-arg-driven-app-check` each carry
`classifyAppHead f ≡ nothing`, and the bare-builtin check rules each carry
`lookupLocal ≡ nothing` / `lookupImport ≡ nothing`. A guard against a
name collision became part of the language definition — the same defect D134
removes elsewhere, and D127 removed from `⊢ᵍ`.

### The bare-name resolution rule: GENERATORS WIN, the local is `name@this`

Canonical names cannot collide — `Generators.fst` and `User.Module.fst` are
different names, full stop. What still needs deciding is what the TOKEN `fst`
denotes at a use site. The rule:

> **A bare generator name always denotes the GENERATOR.** `fst` is `fst`,
> in every module, always.
>
> A module-level definition of a generator name is legal and is reached as
> **`fst@this`** — the existing `name@Alias` syntax, with `this` denoting the
> current module.
>
> **Lexical binders shadow normally, and this is DELIBERATE**: in
> `\fst -> … fst …` the inner `fst` is the parameter. `@this` does not apply
> there — a binder is not a module-level definition. The split is BINDING vs
> DEFINITION.

So a generator-named thing is reached three ways, and only the first is new:

| written | denotes |
|---|---|
| `fst` | the GENERATOR, in every module, always |
| `fst@this` | this module's own definition of `fst` |
| `fst@M` | module `M`'s, where `import … as M` — the EXISTING qualified path, unchanged |

**Why binder shadowing is allowed, and why it is NOT warned about.** The
reason module-level definitions do not shadow is ACTION AT A DISTANCE: a
definition two hundred lines up silently retargets every `fst` below it. A
lambda or `let` binder has no distance — it is visible in the enclosing scope,
at the use site. That is the whole difference, and it is why the argument
against one does not transfer to the other.

A warning would be a half-measure: warnings are for INVISIBLE capture, and
there is none here. Warning on `\fst -> …` would also make the rule feel like
a prohibition wearing a disguise. There is no warning.

The cost of the alternative is concrete: `id` and `pair` are ordinary variable
names — `let id = …` for an identifier, `let pair = …` — and forbidding the
whole generator set as binder names to prevent `\fst -> …`, which nobody
writes, is recurring friction for a stylistic gain. It would also reintroduce
reserved words in binder position, which is the thing this entry exists to
remove.

(One generator name, `case`, is already a lexer keyword — with `as`, `import`,
`in`, `let`, `of`, `type` — so it is unbindable for an unrelated reason. The
other sixteen are ordinary identifiers.)

**Why not the other way round** (a definition shadows, generator via
`fst@Generators`) — which is what this entry said on first writing, and was
wrong:

  * **It annotates the wrong case.** Defining `fst` is rare; USING `fst` is
    constant. Under shadowing, adding one definition silently retargets every
    `fst` in the module — action at a distance, and a reader has to know a
    module's definitions before they can read its expressions. Under this
    rule the definition is inert until explicitly named.
  * **It keeps the true half of D001.** D001's rationale — the generators are
    the language's substrate, nearer to operators than to library functions —
    was correct; what was wrong was enforcing it by FORBIDDING the name. D001
    conflated "`fst` always means the generator" with "`fst` may not be
    defined". This rule keeps the first and drops the second.
  * The earlier draft claimed the converse was impossible because Once has no
    own-module qualification. That was a failure of imagination, not an
    argument: the grammar is already being changed, and `@this` is a
    one-token addition to syntax that already exists.

**Consequences for the implementation** — and this is the reason the choice is
cheap as well as right:

  * The RESOLVER does not need the own-module definition names at all. It
    reads: a lexical binder stays bare; a generator name becomes
    `RResolved (gen x)`; anything else becomes `RResolved (canonical [x])`;
    and `name@this` becomes `RResolved (canonical [name])`. Under the
    shadowing rule it would have needed the module's whole definition set
    threaded through `canonExpr` (219 occurrences).
  * `this` must be RESERVED as an import alias — the parser does not require
    module names to be capitalized, so `import Foo as this` is lexically legal
    today and would otherwise collide.

### What it buys

Four things, all the same root cause dissolving:

  * the shadowing bug is fixed, and a user may name things what they like;
  * `named-morph-strong` / `-resolved` become dischargeable — a user
    `RResolved cn` provably has `cn ≠ Generators.*`, hence is not a builtin,
    hence takes the morphism path (the `bbc-other` assumption becomes
    type-enforced rather than postulated);
  * `classifyAppHead f ≡ nothing` stops being load-bearing, so plan 0.80 can
    remove it from the three application rules — it was only ever guarding the
    collision (measured 2026-09-01: removing it before this lands breaks
    `check-complete` on exactly the shadowing case);
  * the CanonicalName migration finishes. The generators were its last holdout.

### Why a reserved NAMESPACE rather than a reserved-name check

Enforcing D001 in the parser was the other option and it is a band-aid: it
keeps one identity space and adds a guard, so every downstream proof still has
to carry "this name is not a builtin" as a side condition. Canonicalizing
removes the ambiguity at the representation instead of forbidding half of it —
after which there is nothing to guard, and the side conditions delete rather
than move ([[feedback_canonical_name_not_bare_bandaid]]).

### Consequences

  * `compiler/test/TypeCheckSpec.hs`'s "user-defined 'fst' is shadowed by
    builtin" pinned the OLD behaviour and flips: the program is now ACCEPTED,
    and `fst 5` means the user's `fst`.
  * Generators still need no import — they resolve to `Generators.*` when not
    shadowed, which is what makes them feel primitive without being reserved.
  * A module-level `fst` does not capture the bare name; it is reached as
    `fst@this`. A lambda/let binder named `fst` does shadow, as in any
    language. See the resolution rule above.

**Relates**: D001 (superseded), D050, D064, D127, D134; plan
`0.50-canonicalize-generators.md`

---

## D137: Resolution Is Part of the Front End — `⊢R` Covers Parse AND Resolve

**Date**: 2026-09-02 · **Status**: LANDED; plan `0.81-resolution-under-specification.md`
(complete, deleted) · **Follows**: D134, D136 · **Supersedes**: the
"KEEP `ModuleTyped` over the UN-RESOLVED source" directive of plan 0.51

### The decision

`src ⊢R tp` means *"the text parses, by the grammar, to a module that resolves,
by the resolution rule, to `tp`"*, and `Typed` holds the **resolved** module.

`Once.Spec.Resolution` states the resolution rule as inference rules over
PROPERTIES — `x ∈ bound`, `GenWord x`, `FirstAt a p am` — never a call to the
decider the resolver uses. `Once.Adequacy.ResolveBridge` proves
`resolveImports` computes exactly that, both directions, imports included,
postulate-free.

### Why: two independent reasons, one of them urgent

**The resolver was unconstrained.** Its three obligations
(`resolver-preserves-typing`, `-reflects-typing`, `-preserves-trace`) all said
only that SOMETHING SURVIVES resolution. A resolver that resolved `foo` to the
WRONG module, while keeping the program well-typed and behaviour-preserving,
satisfied all three. Nothing pinned the name → `CanonicalName` map.

**D136 had made the old shape vacuous.** With bare `fst` meaning
`Generators.fst`, `ModuleTyped` over the UN-resolved module is underivable for
any program that names a generator — so with `Typed` holding `mU`, both
conjuncts of the criterion were going silent about essentially every real Once
program. And `resolver-reflects-typing` became outright FALSE: its var case
would need `⊢ᵢ RResolved (gen "fst") → ⊢ᵢ RVar "fst"`, and D136 deleted every
bare-`RVar` generator rule by design.

### Reconciling the 2026-06-26 directive

Plan 0.51 closed with "KEEP `ModuleTyped` over the UN-RESOLVED source … if it
is moved to the RESOLVED form it goes vacuous again — so DON'T". That warning
is CORRECT for moving `Typed` alone: `⊢R` would read `ParsesText text mR`,
which is false for every `tp`. Its unstated assumption was that
typing-transport is the only way to keep the resolver inside the theorem. An
independent `Resolves` relation in `⊢R` is the other way.

### What it bought

18 files / 4425 lines deleted (the whole Canon preserve/reflect family,
`ResolverBridge`, `ResolverLits`, `ResolverTrace`). Three residuals removed
(`resolver-preserves-typing-imports`, `resolver-reflects-typing-imports`,
`resolved-main-agrees`), none added. Both conjuncts of `correctR` got SHORTER,
and `admissible-resolve`/`-unresolve` disappeared — spec and gate now speak
about the same module. `CanonResolve` survives; it is about `resolveImports`
alone.

### Three things learned, worth keeping

**An independent relation earns its keep by failing.** Two spec defects were
found only by attempting the bridge: `(x , p) ∈ um` was too permissive (it also
holds for a LATER duplicate, while the resolver takes the FIRST), and
`rds-cons` could derive "a `DImport` survives". Had the relation been read off
`canonExpr`, both would have been invisible and every bridge lemma a tautology.

**De-with instead of postulating.** `resolvesModule-complete` was briefly a
named residual because `resolveDecls` dispatched with `with`, and the
hypothesis `resolveDecls … ≡ inj₂ ds'` mentions neither scrutinee. De-withing
it turned the residual into a proof. Cost: once an aux CARRIES its equations, a
plain `rewrite` cannot fire, so the producer side needs one J-style bridge.

**A green apex does not mean a working compiler.** Six `cabal test` failures
after the gate were a MISSED D136 migration in the D072 oracle — `pInfer
(RResolved cn)` asked for `"Generators.id"` while `builtinSchema` is keyed on
`"id"`, so sig-less `f = id` stopped inferring. Only the behavioural tests
could catch it.

### The hole this exposed, left for plan 0.59

    ModuleTyped m = ModuleTyped-ef m (extractFunctions (extractAliases m) m)

The spec's notion of "well-typed" is defined by RUNNING the front end, and
`extractFunctions` calls the principality oracle. That is why `_⊢R_` may name
`polyDefNames` — the two share `siglessSchema` by construction, so the oracle
enters the boundary ONCE, not twice — and why specifying the scope separately
would have added residuals to protect `⊢R` from a dependency its sibling
conjunct already has. It is the last executable inside the boundary's own
statements. The sibling case is `ParsesText`, whose leaves still mention
`skipNewlines`/`headK`.

**Relates**: D134, D136, D072; plans `0.50-canonicalize-generators.md`,
`0.59-oracle-principality.md`

---

## D138: The Generator Migration, Landed — What `RResolved (gen g)` Cost and Bought

**Date**: 2026-09-02 · **Status**: LANDED; plan `0.50-canonicalize-generators.md`
(complete, deleted) · **Implements**: D136 · **Follows**: D127, D134 ·
**Unblocked by**: D137

### What landed

Every generator is `RResolved (gen g)` — `gen` a PATTERN SYNONYM over
`canonical ("Generators" ∷ g ∷ [])`, because it must work on both sides (rule
indices in types, elaborator left-hand sides) and a function is rejected in a
pattern. All 23 judgment rules, the classifier, the elaborator, the oracle and
the resolver are keyed on it. `name@this` reaches a definition whose name a
generator has taken.

    fst : Int -> Int
    fst x = x
    test = fst@this 5     -- Typecheck OK        (the user's fst)
    test = fst 5          -- Error: requires a pair (the generator)

### What it bought, beyond D136's rule

**Premises disappeared rather than moving.** The seven point-free leaves
(`checkElab-fallback-RVar-*`) had two lookup premises each asking "is this name
shadowed?"; a generator is now a canonical name, so there is nothing to ask and
they are premise-free. `¬ (x ≡ "unit")` is gone from every rule, lemma and
record field. `checkElab-fallback-RVar`'s nine-way `classifyBareBuiltin` split
collapsed to one clause.

**Deleting the classifier was a BUG FIX, not cleanup.** Every surviving use of
`classifyBareBuiltin` was a live defect:

  * `t-var-poly-instantiate`/`-infer` carried `classifyBareBuiltin x ≡
    bbc-other` as a premise — a decider's answer standing in for a property
    (D134) — which REJECTED a user's own polymorphic `id`, the very thing D136
    allows;
  * `inferElabV-RVar-poly-aux` failed with `UnboundVariable` on seven arms, so
    a poly def named `id` never reached the telescope lookup;
  * `checkElab-RVar` dispatched a bare `RVar` on it, and was also 98 lines of
    dead code the mutual block declared and nothing called.

### Techniques this migration forced, worth reusing

**Route dispatch through a VIEW PARAMETER, never a concrete clause.** Concrete
`RResolved (gen "g")` clauses stop `checkElabV`/`inferElabV` reducing for an
abstract `cn`, which the proofs depend on. The dispatch must also TAKE the
infer result rather than recompute it, or a proof's `with inferElabV …` does
not catch the inner call.

**A `with` cannot pin `classifyGen cn`** — it reaches the goal only through
unfolding, so there is nothing to generalise. Use a J-style bridge:
`f ctx cn .(classifyGen cn) refl = refl`. Four exist
(`inferElabV-RResolved-J`, `checkElabV-RResolved-J`, `agree-RResolved-view`,
`check-agree-RResolved-view`); any new consumer of the dispatch needs one.

**Make the VIEW carry its evidence.** `t-var-resolved` needs
`NotGenerator cn` for disjointness, and the elaborator can only discharge it
because `GenView`'s `gv-other` CARRIES the witness. An uninformative
`gv-other : ∀ {cn} → GenView cn` discharges nothing — this is the analogue of
`isGround-inj₂-¬Ground`, which works only because `inj₂` is informative.

### The one that nearly escaped

The apex was green while `f = id` had stopped compiling. The D072 oracle still
keyed generator schemas on the canonical path, so `pInfer (RResolved cn)` asked
`lookupName` for `"Generators.id"` while `builtinSchema` is keyed on `"id"`.
**Only the behavioural tests caught it.** When a migration touches the front
end, a green apex is not evidence.

### Where `name@this` belongs, and why not the parser

`@alias` is ALREADY a general parser form. Putting `this` there would give BOTH
the concrete grammar and the parser special knowledge of the string (~8 modules:
`ParsesAtomExpr` + `shrinks` + `opFails` + `complete` + `ConcreteExpr` and its
four consumers). Reserving it as an alias and interpreting it in the resolver
gives exactly ONE level that knowledge — and since D137 the resolver is under
specification, so it is not an unverified level. The rule
(`Once.Spec.Resolution.re-this`) is decided BEFORE the alias table, so an
`import … as this` cannot capture it, and `re-qual`/`re-qual-unknown` carry
`alias ≢ "this"` to keep the three disjoint.

This CORRECTS an earlier reading of "convert as early as possible": the metric
is how many levels deal with the String, not how early the conversion happens.
Generators still resolve in the resolver — the first level that knows binders.

**Verified**: `Once.Certified` green; 680/680 tests; exit tests 62/0/0 on
x86-64, x86-32/qemu, riscv64/qemu.

**Relates**: D001 (superseded), D127, D134, D136, D137, D072

---

## D139: Stale Import Directives Are a Silent-Rot Channel — `make lint-imports`

**Date**: 2026-09-03 · **Status**: LANDED; plan `0.82-import-hygiene.md`
(complete, deleted) · **Follows**: D137 (found the problem while enumerating
the spec)

### The defect

**Agda only WARNS when a `using (…)` directive names something the module does
not export.** Nothing fails. So every deletion or rename leaves every import
list that mentioned it stale, silently and permanently.

That is not untidiness. A stale list makes a genuinely wrong import
indistinguishable from noise, and it defeats the one mechanism that otherwise
makes a rename safe: delete a definition and Agda reports every USE — but not
one mention in an import list.

### The gate

`formal/scripts/lint-imports.sh`, wired as `make lint-imports`. Two findings
shaped it:

  * `-W error=ModuleDoesntExport` does NOT escalate on Agda 2.8.0 — the flag is
    accepted and the warning still exits 0. Blanket `-W error` is unusable
    (2241 `CoverageNoExactSplit`, several deliberate). Hence grep-the-log.
  * `ModuleDoesntExport`, `DuplicateUsing` and `UselessPublic` are all SCOPE
    warnings, so `--only-scope-checking` suffices: ~10s per module, no
    type-checking. Crucially it reports EVERY module, where a normal build
    reports only the ones it happened to re-check.

### What it found

Four files had a `using (…)` block whose `open import` line had been DELETED,
leaving the block glued to the import above — so the names were being asked of
the WRONG module (`AbstractToX86` asked `Once.CCC.Label` for `AbstractInstr`;
`Adequacy/CPU/X86-64` asked `Once.Float.Dyadic` for `XInstr`; two asked
`Once.CanonicalName` for the `*-info` family). They compiled only because each
file ALSO imported the real module wholesale. **The import structure was lying
and nothing failed** — the thesis, in its strongest form.

Plus 222 dead names, a duplicated `CompiledCorr`, and a comment in `ConcFlatSim`
asserting that `HeapView` came from `FlatSimulation` when `FlatSimulation` does
not export it.

Final state: **0 / 0 / 0 across all 402 modules.**

### Two lessons that cost real time

**Do not convert a wholesale `open import M` into `using (…)` as part of a
hygiene pass.** Reattaching the four orphaned blocks did exactly that, and it
CHANGED BEHAVIOUR: `AbstractToX86` still type-checked, but `compile-abstract
(instr-reg-op scratch-zero)` began emitting `imm 1` instead of `imm 0`, because
restricting the import re-resolved an ambiguous name to a different module's
constructor. Only `X86-64/FlatSimulation`, further down the build, caught it.
The safe fix is to DELETE the orphaned block and keep the wholesale import;
making such an import explicit is a separate change with its own gate.

**Scripted edits to import lists need the type-checker after every pass.** The
stripper damaged files three times — it reflowed a list containing a `--`
comment and commented out the rest; it edited a LATER directive that happened
to mention the same name, deleting a `HeapView` in use; and it mangled a
four-name list to `using (e`. Each was caught by re-running the apex
immediately. A five-name edit does not need a script.

### Measurement note

Aggregated build logs over-count these warnings by ~19x: a warning in module M
is re-emitted for every module that imports M. The true figure came only from
per-file scanning — 50 + 8 across 24 files, not 944 across 95.

**Relates**: D137; plan `0.83-parked-wf-island-cluster.md` (the other gate that
does not currently run)

---

## D140: A Bridge Proof Is Not Part of the Claim — the Spec Closure Holds Relations Only

**Date**: 2026-09-03 · **Status**: Decided and landed (plan 0.84) ·
**Supersedes nothing; refines D137**

### The rule

`Once.Spec` re-exports exactly what a reviewer must read to know WHAT IS
CLAIMED. A `-sound` / `-complete` proof is evidence that the implementation
meets the claim. It is never part of the claim, and it must not be inside the
re-export closure.

Stated as a check: **every module `spec-closure.py` prints is proof-free.**

### What was wrong

Five modules each defined a relation AND proved its bridge to the executable in
the same file, so re-exporting the relation dragged the proofs in:

    Once/Adequacy/LexerBridge.agda      304 lines   2 relations  14 proofs
    Once/Adequacy/FrontEndBridge.agda   219          4            8
    Once/Adequacy/AcceptSound.agda      208          3            6
    Once/Adequacy/ModuleComplete.agda   362          4            2
    Once/Grammar/DeclBridge.agda        108          1            2

1,201 lines, 14 relations, 32 proofs. The closure was majority proof by line
count. An audit instruction that says "read 1,201 lines, most of which you do
not have to trust" is one nobody executes — which is how an audit surface rots.

### The second defect: the report under-reported too

`spec-closure.py` follows a re-export only when the `open import` carries
`public`. `Once/Grammar/DeclBridge.agda` imported its six sub-relations WITHOUT
it, yet `ParsesDecl`'s constructors MENTION them — a reviewer reading
`ParsesDecl` must read `ParsesImport`, `ParsesTypeAliasDecl`, `ParsesSignature`,
`ParsesFunDef`, `ParsesOpDecl` and `ParsesPolyType` to know what it says.

So the closure **over-reported** (module granularity dragged proofs in) and
**under-reported** (only `public` propagates) simultaneously. Fixing one alone
would have produced a smaller number that was still wrong. This is why the
count RISING is the plan working:

    before   23 modules, 4,864 lines, 32 sound/complete proofs
    after    27 modules, 4,467 lines,  0 sound/complete proofs

**Treat a falling closure count with suspicion.** It usually means a re-export
lost its `public` and part of the surface went dark, not that the spec shrank.

### The rule is proof-freeness, NOT location

`Once/Parser/TypeRelation.agda` (323 lines, 0 proofs) and
`Once.Parser.Generic.Relation` (598 lines, 0 proofs) already comply and are NOT
moved: they live in the parser hierarchy by design, because the parser's own
return type mentions them, and moving them would create a Spec -> Parser ->
Spec cycle. New modules under `Once/Spec/` are only for relations that are
currently co-located with proofs and have nowhere else to go.

`Once/Parser/Generic/` — `Relation.agda` beside `Sound.agda`/`Complete.agda` —
was the in-tree precedent this plan generalised, not a new idea.

### A relation must never import a proof module

`wordHead := is-just ∘ anyWordB`, an executable parser helper, lived in
`Once.Grammar.ImportBridge`, and three grammar RELATIONS named it. The fix is
to move the HELPER to where its `anyWordB` already lives
(`Once.Parser.Module.Core`), not to bend the rule for the relation.

### What the split makes visible, and deliberately does not fix

`Once/Spec/Module.agda` is ugly, and its header says so:

  * `ModuleTyped m = ModuleTyped-ef m (extractFunctions (extractAliases m) m)`
    — the spec's notion of "well-typed" is defined by RUNNING the front end.
  * `AllFunsTyped` names `ctxWithImportsAndSelfAndPolys` from the ELABORATOR,
    plus `resolveFunType` / `extendFunCtx` / `buildPolyCtx` /
    `collectSigEffects` from `Once.Compile`.
  * Only its BODY premise is honest: `_⊢ᶜ_∶_⨾_`, with no elaborator function.

Likewise `Once.Spec.Parsing`'s relations are phrased against `skipNewlines`,
`parseDeclB`, `allTrailing` and the lexer's classifiers.

D137 recorded this hole and **plan 0.59 owns closing it.** The split relocates
the dirt into files whose names promise spec, so a reviewer trips over it,
rather than leaving it hidden behind a proof module. Expect
`Spec/Grammar/*.agda` to read clean and `Spec/Module.agda` to read badly; that
asymmetry is honest reporting, not a defect in the split.

### Cost

No executable code moved — relations are types — so no re-extraction was
needed. Apex (`Once.Certified`) green.

**Relates**: D137 (`Typed`/`_⊢R_` into the boundary; the `ModuleTyped` hole);
D134 (the spec names properties, the elaborator names deciders); D139 (the
other silent-rot channel in import directives); plan 0.59; plan 0.85 (the same
disease in `Once.Type`, deliberately deferred — its deciders are already
`using`-restricted out, so nothing actually leaks).

---

## D141: RETRACTED IN PART — the `*WF` Cluster Is the Intended Discharge Route for Nine of Sixteen Postulates

**Date**: 2026-09-03, **corrected 2026-09-04** · **Status**: two modules
deleted, eleven RESTORED · **Relates**: D132, plan 0.64, plan 0.52 (M2)

### What this entry first said, and why it was wrong

It deleted thirteen modules under `Once/CCC/Machine/IR/` and `Once/CCC/SigOp/`
on the argument that they were a superseded per-case attack over the structured
machine. **Eleven are restored. The argument was wrong, and how it was wrong is
the useful part of this entry.**

Plan 0.64's test is: *does this island prove something the apex only postulates
— convertible-after-porting, not "resembles"?* Two errors were made applying it.

**Error 1 — the postulate list was incomplete.** `IRObsCorrectFlat` was read as
carrying 7 postulates. It carries **16**; the extractor stopped at the first
`postulate` block. The full set:

    cata-correct      obs-correct-pair    obs-correct-curry   obs-correct-Ana
    obs-correct-fst   obs-correct-inl     obs-correct-case    obs-correct-Hylo
    obs-correct-snd   obs-correct-inr     obs-correct-apply   obs-correct-Fuse
    obs-correct-In    obs-correct-Para    obs-correct-sigop-rest   comp-step

Eight of the nine names this cluster addresses were invisible when the verdict
was taken.

**Error 2 — the porting device was never looked for.** The test says
"convertible AFTER PORTING", and the port exists, is proven, and is live:

    Once/CCC/Machine/Flat.agda:1061
      exec-trace-is-flat : ... Straight prog -> exec-trace ... == exec-flat ...

On jump-free traces the structured `exec-trace` EQUALS `exec-flat`. The
architecture was deliberate and three-staged: prove per-IR-case operational
facts on the structured machine (`*WF`), lift them with `exec-trace-is-flat`,
discharge `IRObsCorrectF`. `Once.CCC.Codegen.StraightTrace` is the step-2 piece
supplying straightness for `ir-to-trace`. Comparing statements directly and
concluding "different property, different machine" answered a question the test
does not ask.

### What `IRObsCorrectF` demands, and why the cluster fits

    traces-agree   : forall k -> exists f. take k (flat-events f (ir-to-trace ir) ...)
                                        == take k (projTrace (evalD ir (inject x)) k)
    value-realized : exists f mOut ca. ResultPlace B mOut ... (eval ir x) ...

The abstract traces `ir-to-trace` emits must refine the denotation in
observables at every depth AND land the right value in the right place.
`SimpleWF.run-fst` bundles precisely `value-realized`'s ingredients — the step
result (`s'-eq`), where the output lands (`rax-eq`), `not-halted'`,
`frontier-stable`. The same work, one machine below.

### The mapping

    SimpleWF                           obs-correct-fst, obs-correct-snd
    ComposeWF                          comp-step
    CurryStackWF / CurryAllocWF        obs-correct-curry
    ApplyWF                            obs-correct-apply
    SumRecWF / SumInl- / SumInrAllocWF obs-correct-inl, -inr, -case
    PairAllocWF                        obs-correct-pair

Nine of sixteen. Restored, plus `LambekValidity` and `RecSchemePostulates`,
which `SumRecWF` imports.

### What stays deleted

  * `RecSchemeProof` — not a proof. Its `CataIH` is followed by "The full proof
    would: 1. Define cata-valid by well-founded recursion...", and it targets
    `ValidAtWF`, not `IRObsCorrectF`.
  * `Once/CCC/SigOp/Helper` — frame/heap/slot monotonicity of the transition,
    against `structured-pure-sigop-*`, which are D061 TRUSTED BASE by design and
    concern an opaque output value.

### Two cautions for whoever ports this

1. **Seven of the nine are postulate-free** (`SimpleWF`, `CurryStackWF`,
   `CurryAllocWF`, `ApplyWF`, `SumInlAllocWF`, `SumInrAllocWF`, `PairAllocWF`).
   `ComposeWF` has 3 and `SumRecWF` 2, and `SumRecWF` additionally imports
   `RecSchemePostulates.rec-scheme-semantic` — an ASSUMPTION module. Plan 0.64:
   *an island that ASSUMES rather than proves is a delete candidate, not a wire
   candidate.* Discharging `obs-correct-inl/-inr/-case` on top of
   `rec-scheme-semantic` would be postulate-shuffling. Check whether the
   inl/inr/case content is independent of it; that assumption is documented as
   serving `run-In`/`Out`.
2. **They carry plan-0.52 M2 rot** (`Type` -> `IRTy`, `WellFormedF` ->
   `WellFormedFI`) plus the D089 `o` parameter on `ClosureWellFormedDef`. Plan
   0.52 was CLOSED 2026-07-16, complete and green; the migration never reached
   these files because nothing built them.

### The lesson that survives unchanged

**An island is not merely unreachable, it is UNCHECKED.** "It still typechecks"
can never be assumed about one — and neither can "the apex does not need it",
unless the postulate list has been read in FULL and the porting device has been
looked for.

**Relates**: D132 (per-shape witnesses are not the theorem — still stands; that
cluster was a different case); plan 0.64 (the audit and the rule); plan 0.52
(the M2 migration these need); plan 0.78 (`cata-correct`, not in this set).

---

## D142: Allocation Is Mechanical — No Surface Annotation, No IR Mode, and Heap-Neutrality Is a TYPE

**Date**: 2026-09-04 · **Status**: Decided (plan 0.86), not started ·
**Supersedes**: D012, D013, D014 · **Lands**: plan 0.2.4.5

### The rule

Nothing in the language and nothing in the IR chooses where a value lives.
Placement follows from the value's role:

    IR inputs and outputs   ->  stack, or REGISTERS for linear values that fit
    internal, bounded       ->  frontier scratch
    internal, unbounded     ->  heap, FREED BY THE IR ITSELF

### What is superseded, and why the motivation does not survive

D012 put an allocation annotation in the implementation (`concat @heap a b`),
D013 scoped it to outputs, D014 added `--alloc` as the default.

The motivation was real: **a dead value can sit trapped on the stack behind a
longer-lived one**, holding its slots for the rest of the enclosing
computation. That must be recorded at full strength so it is not re-litigated
from a weaker version.

It does not survive contact with where trapped values actually come from.
`let x = e1 in e2` elaborates to `e2 ∘ ⟨ id , e1 ⟩`; the `id` keeps the whole
environment alive, so nested lets accumulate `((Γ,x),y)` and a binding used
early and dead later is a dead COMPONENT of a live product. Three consequences:

  * an unread binding already falls out to `π₁ ∘ ⟨f,g⟩ ≡ f` — pure CCC
    rewriting in the optimizer, no liveness analysis;
  * the rest are removed by ELABORATION (sink each `let` to the dominator of
    its uses, so the binding never enters the outer environment);
  * and D013 scopes the annotation to function OUTPUTS while the trapped value
    is a `let`-binding — **there is no syntax that names its placement.** The
    feature could not express a fix for the case that motivated it.

The residual — a value used early AND late, dead between, buried below newer
values — cannot be sunk (its dominator spans the gap) and reclaiming it means
repacking everything above it. That trade is accepted and WARNED about, not
optimised. Reporting, not machinery.

### The invariant, and how it is ENFORCED (OCP-0005 rung 1)

Because what crosses an IR boundary is stack-resident and heap is strictly
IR-internal and reclaimed before return, **every IR has net heap delta zero**.
This is the `StackPure` property promoted from a per-use-site mode tag to a
global law.

It is not left as prose. OCP-0005's ladder puts "make violation ill-typed"
at rung 1, and plan 0.17 already built the mechanism: each producer declares a
`bump` (delta on `next-slot` and `next-heap-ref`), `final-alloc = apply-bump
bump alloc` is derived, and `alloc-correct` ties the trace to the bump.

**The encoding is a SUBTRACTION: remove the heap delta from `bump`.** With
`bump` carrying only a `next-slot` delta, an IR that leaked heap cannot state
its own result — `final-alloc` has the same `next-heap-ref` as `alloc`, and
`alloc-correct` will not typecheck for a leaking trace. Violation becomes
ill-typed, and the record gets smaller rather than larger.

**Care required — net, not gross.** Heap-neutral does NOT mean heap-untouched.
An IR may allocate transiently and free within its own trace. `alloc-correct`
must therefore relate the trace's NET heap effect to the bump. Stating it
grossly would reject legitimate implementations.

### Consequences

  * `AllocMode` leaves the IR (six constructors: `⟨_,_⟩`, `inl`, `inr`,
    `curry`, `In`, `in-ν`) — plan 0.2.4.5 lands, whose audit found `AllocMode`
    had "drifted into a vestigial layout tag".
  * The per-mode module pairs collapse: `CurryStackWF`+`CurryAllocWF` -> one,
    `SumRecWF`+`SumInlAllocWF`+`SumInrAllocWF` -> one. Of the parked cluster's
    91 holes, ~33 are allocation bookkeeping or `ValidAtWF Heap`.
  * `--alloc` STAYS, repurposed: it no longer selects a mode (there is none),
    it selects WHICH ALLOCATOR backs the dynamic calls — bump, malloc,
    mempool, arena. That is what makes the proven allocators of plan 0.35
    reachable.

### Open, and gating the IR work

**A value escaping a DEFINITION boundary.** Within a definition, framelessness
makes escape a non-issue: `FrameFreeTrace` proves no emitted trace contains a
frame op, the backend brackets the body with one `subq $budget*8, %rsp`/`addq`,
and `ResultPlace.at-loc` places every result BELOW the frontier — so a produced
value is a lower offset nothing pops underneath. The closing `addq` is the real
boundary. Same question as `Once.Escape` / `Once.Escape.Correct` (plan 0.64
group E: the analysis is live, its correctness proof is a red island).

**Relates**: D012/D013/D014 (superseded); plan 0.86 (the work); plan 0.2.4.5
(lands); plan 0.2.4.6 (Place); plan 0.17 (the `bump` mechanism this encodes
into); plan 0.35 (allocator wiring); OCP-0005 (the encoding ladder); D141 (the
paused `*WF` port).

---

## D143: Erasure Is a SEMANTIC Claim — the Spec's Meaning Is Grade-Aware

**Date**: 2026-09-04 · **Status**: LANDED 2026-09-05 (apex green) ·
**Refines**: plan 0.52 M2 · **Relates**: D142, OCP-0005, OCP-0009 Rung 5

### The rule

The meaning of an arrow depends on its QUANTITY:

    ⟦ A ⇒[ mk-kind Zero π ] B ⟧ = ⟦ Unit ⟧ → ⟦ B ⟧    -- erased: no argument
    ⟦ A ⇒[ mk-kind _    π ] B ⟧ = ⟦ A ⟧    → ⟦ B ⟧

and `⌊_⌋ : Type → IRTy` mirrors it. Purity remains ignored — a pure and an
effectful arrow over the same `A`, `B` are the same object, which is what M2
established and it stands.

### Why the spec had to change, and why nothing smaller worked

`⌊_⌋` dropped the whole `ArrowKind`, so an erased arrow became a real
exponential WITH an argument slot. The compiler therefore declared an erasure
it then declined to perform.

Making `⌊_⌋` alone erase does not work, and the reason is precise.
`Once.Semantics.ValueIR.coh : ⟦ ⌊ T ⌋ ⟧ᴵ ≡ ⟦ T ⟧` is used in BOTH directions —
`Once.CCC.Eval`'s SigOp case is `subst id (sym (coh B)) (semM si (subst id (coh
A) x))`, and there are 114 `subst`-by-`coh` sites. With a grade-blind meaning
and an erasing `⌊_⌋`:

  * runtime -> full is canonical: an erased function ignores its argument, so
    `λ f a → f tt` recovers the full value;
  * **full -> runtime has NO canonical inhabitant.** Given an arbitrary
    `⟦A⟧ → ⟦B⟧` there is no way to produce `⟦Unit⟧ → ⟦B⟧` — you would need an
    element of `⟦A⟧`. The typing says the function ignores its argument; the
    DENOTATION does not record that, so the information is not there.

`coh` was not stuck, it was FALSE. One side forgetting the argument breaks the
equality; both sides forgetting it together restores it. That is the whole
content of this entry.

### The general statement

**Erasure is a semantic claim, and a compiler cannot honour a guarantee its
specification does not make.** While `⟦ A ⇒[ _ ] B ⟧ᴰ = ⟦A⟧ᴰ → T ⟦B⟧ᴰ`, QTT was
load-bearing in the TYPING judgment (it decides which programs are accepted)
and inert in the MEANING — so "a `Zero`-graded argument is not represented at
runtime" was a promise no specification made. Erasing and not-erasing were
observationally identical and BOTH satisfied `correct`. That is OCP-0005's
"prose decisions are silently violable", at the level of the semantics.

### Only Zero needs representation; One and Many do not

`One` and `Many` have IDENTICAL runtime representation — linearity constrains
how many times the body uses the argument (licensing in-place update and early
free), not the shape of the argument. `⇛` being ungraded is right for them.
`Zero` differs in kind: it does not encode the argument differently, it REMOVES
it. So there is one bit to represent — is there an argument — and no
"representation of quantity" to build.

### What this makes possible

`app` at a `Zero`-graded arrow elaborates without widening anything: the
argument is not in the runtime environment (`erase-arg-usage`: `Ψ₁ +ᵘ (Zero *ᵘ
Ψ₂) ≡ Ψ₁`), and the arrow has no slot to fill. The earlier idea of indexing
elaboration by a "runtime usage ⊒ QTT usage" was working around the absence of
this change rather than using it — it would have kept computing a value the
type system says does not exist.

### On the OCP-0009 POC

`bootstrap/poc/OCP0009/NbEPQTT.agda` realises the phase distinction at the
CONTEXT level (`⟦Γ⟧full` / `⟦Γ⟧run` / `erase`, with `erase-irrelevant` true by
construction), and `NbEPQTTJ.agda` the graded judgment with `erase-arg`. It has
NO erasing arrow denotation — the proposal names that as Rung 5's remaining
item ("elaborate `Γ ⊢[ ρ ] A` to the CCC IR … erasing the `𝟘`-graded
arguments"). So the POC informs the context half and stops where the arrow half
begins; **this entry rests on standard QTT semantics (Atkey), not on the POC.**
A future session should not cite the POC as authority for the arrow rule.

**Relates**: D142 (the same OCP-0005 rung-1 technique — make the representation
incapable of expressing the violation); plan 0.52 M2 (correctly erased purity,
incorrectly erased quantity with it); plan 0.86 step B.

## D144: `ThinSound` Is DELETED — a Dead Import Kept 380 Lines Nominally Live

**Context.** D143 phase-indexed the source denotation over `Γ ↾ Ψ`. The apex
build then stopped in `Once.Denotation.ThinSound`, whose statements are all over
the full `Γ`. The obvious reading was "next module to re-thread", and the
re-thread was scoped: a `thinᴰ` environment map plus a commutation family
against `restrictᴰ`, roughly 40 clauses.

**What the check found.** Across all 408 `.agda` files, `ThinSound`'s only
export `weaken-⟦⟧` appears exactly three times: its own definition, and two
`open import Once.Denotation.ThinSound using (weaken-⟦⟧)` lines in
`Adequacy/MeaningBridge` and `Adequacy/RealizeAgrees` that never reference the
name they bind. Every other export (`thin-⟦⟧`, `lookupᴰ-thin`, `⟦⟧-substΨ`,
`⟦⟧-subst₂`, `restrictᴰ-refl`, the bind congruences) has zero external uses.

The module was reachable from the apex ONLY through two dead imports. D126's own
entry predicted this: "`Once.Denotation.ThinSound` (added for D126's `weaken`)
loses its only consumer unless the new elaboration needs it." The collapsed
judgment (D127) is the new elaboration, and it does not need it.

**Decision.** Delete `Once/Denotation/ThinSound.agda` and the two dead imports.
The thinning subsystem itself STAYS — `weaken`/`weakenFromEmpty` are live in
`Elaborate`, `ElaborateProofs` and `Realize`. What died is the *denotational
soundness of renaming*, not renaming.

**Why re-threading would have been wrong even if it were live.** Over the full
`Γ`, a variable's lookup walks to index `i` and projects a different component
per `i`, so a SCOPE operation looked like it changed MEANING — that is what the
220 clauses of plumbing paid for. Over `Γ ↾ Ψ` a variable's environment is a
SINGLETON (`var i : Expr Γ (singleUse i One) A`) and `lookupᴰUsed` is a
projection whose index walk never touches the data. Thinning cannot move it, so
the `var` case — which the module's own comment calls "the lemma; everything
else is plumbing" — degenerates to `refl`. The module was not merely dead; it
was an artifact of the pre-D143 abstraction.

A `↾-thin` coherence (`subst Ctx (liveCount-thin θ Ψ) (Δ ↾ thin-usage θ Ψ) ≡
Γ ↾ Ψ`, provable in ~20 lines, thinned-in variables get `Zero` and `↾` drops
`Zero`) was written and proved during this analysis. It is NOT landed: with
`ThinSound` gone it has no consumer, and an unwired lemma kept for its
documentation value is exactly the island the project rejects. The fact is
recorded here instead.

**Method note.** Before a large re-thread, check that the module has real
CONSUMERS, not merely importers. An `open import ... using (f)` that never
applies `f` is invisible to import-graph reachability but carries no proof
obligation. [[feedback_verify_consumers_not_importers]]

## D145: A Non-Injective Index Belongs in the RECORD, Not in the Type Former

**Date**: 2026-09-05 · **Refines**: D143 · **Relates**: D144

**Context.** `MeaningBridge`'s logical relation was `RelEnv : (Γ : Ctx n) → …`,
and D143 moved every use of it to the RUNTIME context, so the bridge's premise
became `RelEnv (NamedCtx.debruijn ctx ↾ Ψ) dγ₁ dγ₂`. Each of the ~40 clauses
that splits a usage (`pair`, `let`, `case`, every binop, every application,
`lam`) then needs the relation NARROWED along the same `⊑ᵘ` witness that
`⟦_⟧ᵢ` and `⟦_⟧ˢ` apply — a `rel-restrict`/`rel-bind` combinator per shape.

**Problem.** `_↾_` is a recursive function on `Ctx`/`Usage`, not a constructor.
From an expected `RelEnv (_Γ ↾ _Ψ) …` Agda cannot recover `_Γ` or `_Ψ`: the
constraint is *blocked on the meta itself*, because `_Γ ↾ _Ψ` cannot be reduced
without knowing `_Γ`. So every combinator call reported `UnsolvedConstraints`
unless BOTH indices were pinned by hand — ~60 sites, each carrying
`{Γ = NamedCtx.debruijn ctx} {Ψ₁ = …} {Ψ₂ = …}`, and each clause additionally
binding `{ctx = ctx}` just to have the name available.

**Decision.** Index the relation by the two components SEPARATELY, in a record:

```agda
record RelEnv↾ {n} (Γ : Ctx n) (Ψ : Usage n)
               (dγ₁ dγ₂ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ) : Set where
  constructor mk↾
  field un↾ : RelEnv (Γ ↾ Ψ) dγ₁ dγ₂
```

`Γ` and `Ψ` are now ordinary record indices, solved by unification like any
other, and every combinator (`rel-restrict`, `rel-bind`, `rel-bind0`, and the
four split shapes `reˡ`/`reʳ`/`reᵐ`/`re¹`) infers them from its call site with
nothing pinned. The composite `Γ ↾ Ψ` is what the relation is ABOUT; it is not
what the relation is indexed BY, and conflating the two is what cost the
inference.

**Consequence.** Zero pinning at the ~40 clause bodies; three `mk↾`/`un↾` at
the boundary (the `var` lookup, the closed-algebra `cata` premise, and the
telescope-body recursion). The same shape applies wherever a relation is
indexed by a *computed* context — prefer the components.

## D146: Let-Sinking Is Replaced — the Boundary Convention, Not an Analysis, Is What Reclaims

**Date**: 2026-09-05 · **Supersedes**: plan 0.86 §2 · **Refines**: D142 ·
**Relates**: D143, plan 0.86 §4/§5 step D, plan 0.35, OCP-0005 rung 1

**Context.** D142 recorded that a dead value trapped behind a longer-lived one
is the real motivation the `@stack`/`@heap` annotation served, and prescribed
(plan 0.86 §2) that elaboration sink each `let` to the dominator of its uses
so the binding never enters the outer environment. Step B was to build that.

**What was checked.** Two things, both in the code rather than the plan text:

  * D142's stated cause is GONE. It reads "`let x = e1 in e2` elaborates to
    `e2 ∘ ⟨ id , e1 ⟩`; the `id` keeps the whole environment alive". After
    D143 the clause emits `restrictEnv (⊑ᵘ-+ˡ Ψ₂ …)`, not `id`, and `_↾_`
    drops `Zero` slots — so a binding dead from here on is not in the body's
    environment at the level of the TYPE. `restrictEnv`'s own `z≤o` clause is
    commented "this is the narrowing that reclaims it".

  * The slots are nevertheless not reclaimed, and `let` placement is not why.
    `ir-to-trace'` threads its frontier additively — `f ∘ g` and `⟨ f , g ⟩`
    both run `n → n₁ → n₂` and return `n₂` — so `ir-stack-budget` is the TOTAL
    number of intermediates in a function body, not the peak live at once.
    Sinking a `let` reorders which slots are taken when; against an additive
    frontier that changes the total by exactly zero. **Sinking cannot reach
    the problem it was specified to solve.**

**Why the frontier is additive, and it is not an oversight.** `⟨ f , g ⟩ Stack`
ends `lea-slot fst-slot`: a pair's VALUE is a pointer into the frame. With `f`
itself a pair, the outer `fst-slot` holds a pointer into `f`'s own interior
slot range, so those slots are live past `f`'s return and restarting `g` inside
them would corrupt the pair. Monotonicity is the conservative choice that makes
this safe.

**The decision.** Do not build let-sinking. What licenses reclamation is the
boundary invariant D142 already states — *what crosses an IR boundary is
stack- or register-resident; heap is strictly IR-internal and freed before
return* — read at full strength: resident in the BOUNDARY REGION, not merely
"somewhere on the stack, possibly inside the callee's interior". Once an IR
materialises its result into a caller-designated output location, its interior
slots are dead at return BY THE CONVENTION, and then:

  * `g` may restart at `f-start`, making `ir-stack-budget` peak-live;
  * "heap is IR-internal and reclaimed" becomes statable, which is what finally
    gives `free-heap` — an IR constructor with NO producer today, passed
    through opaquely by `Escape` and `Fusion` — something to be produced by.

**An analysis was the wrong instrument.** `Once.Escape` discovers non-escape
case by case (ten syntactic rules, all rewriting `AllocMode`). The convention
makes escape UNREPRESENTABLE instead. That is OCP-0005 rung 1, and it is the
same move D142 and D143 each made; reaching for the analysis here would have
been rung 0 dressed up.

**Consequence for the order of work.** Step D (`AllocMode` out of the IR) is
not tidying — `⟨ f , g ⟩ Heap` returns a heap pointer ACROSS an IR boundary,
which is a direct violation of the invariant, so deleting the mode is what
makes the invariant true by construction. Step B's remaining item is struck;
step C (the warning) becomes measurable against slots rather than types, and
worth building only if the budget still exceeds peak-live after D.

## D147: The Definition-Boundary Escape Question Is Destination Passing (Plan 0.2.4.5)

**Date**: 2026-09-05 · **Settles**: plan 0.86 §6 (the gate on step D) ·
**Relates**: D146, D142, **plan 0.2.4.5 (destination passing — the mechanism
this entry points at, stages A–C landed)**, plan 0.2.4.6 (Place — decides the
destinations), plan 0.64 group E

**The question §6 left open.** Within a definition, escape is a non-issue:
`FrameFreeTrace` proves no emitted trace contains a frame op, the backend
brackets the whole body with one `subq $budget*8, %rsp` / `addq`, and
`ResultPlace.at-loc` places every result below the frontier — "a lower offset
that nothing pops underneath". But the closing `addq` tears the region down, so
a closure returned from a top-level function cannot live in it. §6 called this
"the one placement decision that is not mechanical" and gated step D on it.

**It is DESTINATION PASSING, which is already the design.** Plan 0.2.4.5's
core principle is verbatim this: "CCC IRs do not know or care which allocator
placed their values. Every IR primitive takes a *destination* — a pre-computed
`ValueLocation` saying where to write its output." Plan 0.2.4.6 (Place) is the
pass that DECIDES destinations; 0.2.4.5 stages A, B and C have landed, stage E
(`InReg` inside `ValueLocation`) was tried and backed out the same day, with
register residency deferred to a separate `Place = AtStorage | InReg` used only
at result-handle handover. Plan 0.86 §5 already says step D "lands plan
0.2.4.5". **This entry claims no new mechanism** — it identifies §6's open
question as one that destination passing already answers:

    result fits in a register (`FitsInReg`)  -> `InReg` at handover
    otherwise                                -> the caller-supplied destination

A returned value needs a location that outlives the callee's `addq`; a
destination supplied by the caller IS such a location, and it is
`BeforeFrontier` in the CALLER's alloc state by construction — exactly what
`at-loc` asks for. The size is statically known from the result type, closures
included, so the placement is mechanical once the callee does not choose it.

**Why this is not merely convenient.** `at-loc` carries TWO frontier facts —
`BeforeFrontier alloc loc` and `BeforeFrontier continuation-alloc loc`. The
second is what makes a result survive into the continuation, and it is true
today only because the frontier is monotone (D146). Any scheme that reuses
slots must supply that second fact some other way; a caller-provided output
region supplies it directly, because the region is below the CALLER's frontier
and the callee never allocates under it.

**What this entry adds to 0.2.4.5 is the reason it is load-bearing for
ALLOCATION, not just for allocator-agnosticism.** 0.2.4.5 motivates
destination passing by IRs not needing to know their allocator. The `at-loc`
argument above says something stronger: destination passing is what makes
interior slots dead at return, and therefore it — and nothing at the `let`
level (D146) — is what can ever turn `ir-stack-budget` from
total-intermediates into peak-live. `at-loc` is where the invariant gets
encoded (OCP-0005 rung 1, §4's "do not leave it as prose"): not as a new
predicate, but by making the result location a parameter the callee cannot
choose.

**Consequence for the order of work.** 0.86's B' and D are 0.2.4.5's stages
**F** (destination parameter on every WF `run-*`: the caller passes
`result-loc`, the IR does not choose) and **G** (drop `AllocMode` from the six
IR signatures, 205 references). 0.2.4.5 already sequences them F → G and gives
the reason: G is "naturally subsumed once F lands — the destination parameter
replaces `AllocMode`'s 'where does this go' role."

An earlier revision of this entry claimed F and G were ONE change, on the
grounds that sequencing them rewrites `ResultPlace` / `ValidAtWF` / the `*WF`
cluster twice. **That was wrong.** F is additive (a parameter appears) and G
subtractive (a now-vacuous index disappears); each touches the structure once,
for a different reason, and F-first is exactly what makes G a deletion rather
than a redesign. Plan 0.86 §7 is amended only to NAME the stages.

**Open sequencing question.** F cascades through `Dispatcher`, `Correct` and
`IRResultAWF` — ~10 IRs, one WF module each — while 0.86 §7 says "Do NOT
resume the `*WF` port before D/E". F is not the port (it adds a parameter; the
port is TERMINATING → WF), but it lands in the same parked, currently-red
modules, so "follow the red" is not available as a signal there. Whether F
precedes or follows E (collapsing the per-mode module pairs) is settled by
neither plan.

## D148: `inl-inr-trace-state-correct` Is REFUTABLE — a Residual That Cannot Be Discharged, Not One That Is Merely Open

**Date**: 2026-09-05 · **Found by**: plan 0.86 step E, greening the `*WF`
island · **Relates**: D142/D143 (the same rung-1 move, arriving as a finding),
plan 0.64, the residual ledger

**What was found.** `Once.CCC.Machine.IR.SumRecWF.inl-inr-trace-state-correct`
is `SMP.!!`, and its STATEMENT is false. It equates

    proj₁ (exec-trace (instr-alloc-stack … ∷ instr-load-tag-lit tag ∷
                       store-at-slot result-slot ∷ …) s alloc)

with an `s-final` the caller constructs as

    record (write-loc s (AtStack frame payload-slot) input-loc)
           { regs = writeReg … Output (SV-Ptr result-loc) }

The trace STORES THE TAG at `result-slot`; the constructed `s-final` leaves
`result-slot` holding whatever `s` held. `s` is universally quantified, so the
two states differ and no proof exists.

**This was already known and precisely recorded**, in a comment above the
residual: "the s-final shape on the caller side ONLY models the payload write
and the Output register update … **The tag write at result-slot is folded into
this postulate's soundness debt** … Migrating callers to a tag-aware `s-final`
is the next step (requires a `validityWF-write-sv-at-frontier` sibling lemma in
`ClosureWellFormed`)." The entry exists to move that from a comment on a hole
into the ledger, where a refutable residual belongs.

**Why it stayed invisible.** `SumTag Stack` was `⊤`. Nothing downstream could
ask whether the tag was written, so a model that never wrote it type-checked.
Upstream later strengthened it —

    SumTag Stack t s loc = readLoc s loc ≡ just (SV-Tag t)

— with the reason recorded in place: "`SumTag Stack = ⊤` UNDERSTATED the
representation and made the branch scrutinee's tag fact underivable for stack
sums." That strengthening is what surfaces this: `run-inl` now fails to supply
the witness, because its model never performs the write.

**The compiler is NOT affected.** `ir-to-trace' n l (inl Stack)` emits
`instr-load-tag-lit 0 ∷ store-at-slot sum-slot ∷ mov-to-output ∷
store-at-slot (suc sum-slot) ∷ lea-slot sum-slot ∷ []` — the tag IS stored in
emitted code. The defect is confined to the WF island's reference model, which
nothing imports. What it would have cost is a correspondence proof discharged
against the wrong state.

**Decision.** Fix the model, not the statement. `run-inl`/`run-inr` now write
the tag (`s₀ = writeLoc s sum-loc (SV-Tag t)`) before the payload, matching
their own `inl-trace`/`inr-trace` — which were ALREADY tag-aware, so the module
disagreed with itself. Closing the rest needs the named sibling lemma
`validityWF-write-sv-at-frontier` (an arbitrary `StoredValue` written at the
frontier slot preserves the validity of anything `BeforeFrontier`, the write
being disjoint by `stack-slot-disjoint`), mirroring the existing
`validityWF-write-at-suc-frontier` clause for clause.

**The general lesson.** A `⊤`-valued predicate is not a weak invariant, it is
an ABSENT one, and it silently licenses a model that does less than the code.
This is the third time in this plan that strengthening a representation turned
a prose-level guarantee into a checkable one and found something (D142 the
annotation, D143 erasure, this the tag).

## D149

**Question.** A sum node has two cells: a tag and a payload. The payload cell
held `SV-Ptr payload-loc`, always — `valid-inl-wf` demanded a pointer plus a
recursive `ValidAtWF` for the block behind it. Should a payload that FITS IN A
REGISTER still be boxed?

**Context.** Stage F is making the WF layer's calling convention explicit:
inputs arrive at an `InputPlace` (`in-at-loc` / `in-at-reg` / `in-unit`) and
results land at a `ResultPlace` (`at-loc` / `at-reg` / `unit-result`). Once
`run-case` could receive its scrutinee's payload in a register, the pointer-only
sum representation became the thing forcing the box back into existence: to
build `inl x` from an `x` already in `Output`, `run-inl` had to allocate a heap
cell, store `x` into it, and store a pointer to it. Every `inl` of an `Int`
paid a two-cell heap allocation for a one-word value, and (given `Once.Escape`
is unwired) never freed it.

**Decision.** A sum carries its payload INLINE when the payload type inhabits
`FitsInRegI`. `ValidAtWF` gains `valid-inl-reg-wf`/`valid-inr-reg-wf`, whose
payload cell holds `prim-sv fit a` — the literal — with no sub-validity and no
recursion. The pointer form stays for structured payloads; the two are distinct
constructors rather than a mode index, so a consumer that must distinguish them
case-splits and a consumer that must not (anything reading the TAG) does not.

**Why the tag cell is untouched.** Runtime dispatch reads cell 0. Both
representations write the same tag the same way, so `tag-of-shape` needed the
new clauses verbatim, `case-on-tag` needed nothing, and no emitted code changed.
The branch is confined to the payload cell's meaning. This is what let the
change be representation-only: residual count is identical before and after.

**The cost, measured.** Seven layers case-split on a sum: ClosureWellFormed
(the constructors, `PayloadAt` with `payload-sv`/`payload-read`, reshaped
`InlValidWF`/`InrValidWF`, `decomposeInl/InrWF`, ten transports), SumRecWF
(`run-case`'s four setup lemmas generalise from a payload LOCATION to a
`StoredValue`), ShapeAt (`shape-inl-reg`/`shape-inr-reg`, `prim-sv-at`,
`valid→shape` split on the `FitsInRegI` witness so both `prim-sv` equations
reduce), ShapeTable (`tag-of-shape`, `shape-uw`), ValidAtWFHalted
(`validAtWF-set-halted`). Four were predicted, the fifth and sixth found by
building the cluster, the seventh only by a full apex build. The transports
(`shape-uw`, `validAtWF-set-halted`) are the cheap ones — with no payload
sub-structure to carry, each new clause is the old one minus its recursive call.

**What it does not yet buy.** The representation exists; nothing produces it.
`run-inl`/`run-inr` still take a payload LOCATION positionally and still emit
`instr-alloc-heap 2`. Making the box actually disappear is the next step of
stage F: give them an `InputPlace` and emit the inline form on `in-at-reg`.

**The general lesson.** When a representation change forks a constructor,
count the case-splits, not the importers — and check the transports first.
They are the majority of the sites and the least of the work, which is why the
estimate came out high and the effort came out low.

**Addendum (2026-09-06), what producing the form actually cost.** The estimate
above was for the representation. Making `run-inl`/`run-inr` produce it cost
almost nothing, for a reason worth recording: THE TRACE DID NOT CHANGE. The
emitted sequence is `instr-load-tag-lit t ∷ store-at-slot sum-slot ∷
mov-to-output ∷ store-at-slot (suc sum-slot) ∷ lea-slot sum-slot`, and
`store-at-slot` after `mov-to-output` stores whatever `Input1` holds without
inspecting it. The payload cell has ALWAYS held the input's stored value —
a pointer only when the input was memory-resident. The pointer was never in
the machine; it was in the model. So the residence surfaces in exactly two
lines of `run-inl` (`pv = input-sv ip`, and which constructor witnesses it),
and the slot arithmetic, frontier facts, trace well-formedness and every bound
record are untouched.

Three supporting pieces, each chosen the same way:

  * A UNIT payload has NO residence — `FitsInRegI Unit` is uninhabited and the
    cell cannot be shown to hold a pointer. Rather than a third constructor
    pair (≈28 mechanical clauses across the seven layers), the witness was
    WIDENED to a parameter, `InlineRep A` with `rep-prim`/`rep-unit`. The ten
    transports pass the witness through opaquely, so widening cost them
    nothing where a constructor would have cost each of them a clause:
    ClosureWellFormed went green with zero transport edits. `rep-unit` carries
    the cell's contents rather than pretending to constrain them.
  * `input-sv`/`input-read` on `InputPlace`, twins of `payload-sv`/
    `payload-read`. TOTALITY is the point: it lets the payload fact be stated
    once, before the residence split, instead of once per branch.
  * `write-sv-at-suc-frontier-preserves-before` and
    `validityWF-write-sv-at-suc-frontier`. Note `write-loc s loc val` is NOT
    `writeLoc s loc (SV-Ptr val)` — they differ on a heap cell holding a stack
    ref — so the pointer lemmas are not instances of the stored-value ones and
    the siblings had to be added rather than derived.

`inl-inr-trace-state-correct` pinned its register hypothesis to
`SV-Ptr input-loc`. It is a proof gap either way, but a gap should be stated
against what the trace does, not against what one caller happened to pass.

**What is still not wired.** Nothing CALLS `run-inl`/`run-inr`.
`RecDispatcherWF` appears only as a module parameter; the top-level dispatcher
that case-splits on the IR and routes to the per-shape handlers does not exist
yet. The stage-F interface is verified but not exercised end to end, and that
— not more per-shape work — is the next thing that would make it load-bearing.

## D150

**Question.** Why can 11 of 13 IR handlers not prove `trace-is-ir-to-trace`,
the field whose comment promises "spec/runtime divergence becomes a type
error"? Closing it for `pair` was supposed to be the easy case once the pair
had a single lowering. It is not, and the reason is not about pairs.

**The measurement.** Discharge of `trace-is-ir-to-trace`, against whether the
handler's WF trace mentions `instr-alloc-stack`:

    SimpleWF       refl x2   instr-alloc-stack mentions: 0
    ComposeWF      gap x1    instr-alloc-stack mentions: 0
    PairWF         gap x1    instr-alloc-stack mentions: 6
    ApplyWF        gap x1    instr-alloc-stack mentions: 43
    SumRecWF       gap x7    instr-alloc-stack mentions: 11
    CurryStackWF   gap x1    instr-alloc-stack mentions: 9

The only handler that PROVES it is the only one that never mentions
`instr-alloc-stack`.

**The root cause.** `AllocState.next-slot` is doing two incompatible jobs.

  * At RUNTIME it is moved by exactly one instruction —
    `exec-abstract (instr-alloc-stack n) s alloc = s , record alloc
    { next-slot = next-slot alloc + n }` (`SMCore`). Nothing else moves it.
  * At CONSTRUCTION time it is the frontier `ir-to-trace'` threads as its `n`
    argument, deciding which slots each sub-IR may use.

These agree only because WF traces contain `instr-alloc-stack` — and
**`ir-to-trace'` never emits it.** `EmittableI (instr-alloc-stack _) = ⊥` and
`FrameFreeI (instr-alloc-stack _) = ⊥` say so outright. So every handler that
reserves slots writes a trace that provably is not the emitted trace, and
`trace-is-ir-to-trace` is unprovable for it by construction. The gap is not
unfinished work; it is a modelling contradiction the gap was hiding.

`PairWF` made this concrete. Removing the instruction (the fix `SumInlAllocWF`
already applied, and which `ApplyWF`'s comment names as "Pattern 1: drop
instr-alloc-stack") immediately falsifies

    alloc-setup-eq-scratch :
      proj₂ (exec-trace setup-trace s alloc) ≡ alloc-after-scratch

because `alloc-after-scratch` is `next-slot alloc + 4` while the runtime alloc
no longer moves. The lemma's own comment says the instruction was added to
"eliminate the runtime/construction-time alignment story that PairStackWF had
to thread by hand". It did not eliminate it; it hid it behind an instruction
the compiler does not emit.

**The second, independent cause.** `ComposeWF` has NO `instr-alloc-stack` and
still cannot close the field: its trace splices `f-trace = IRResultAWF.trace
result-f`, which is opaque, where the emitter has `ir-to-trace' … f`. Closing
`refl` on any composite IR needs the RECURSIVE result to hand back its own
`trace-is-ir-to-trace` so the `++` composes — i.e. `RecDispatcherWF` must
return the correspondence. That is a structural change to the dispatcher
interface, and it is a prerequisite for every composite constructor.

**Decision — TAKEN, and forced by the spec, not chosen.** The first draft of
this entry left the choice open. Reading `Once.Spec` top-down closes it.

`CorrectCompiler.correct` says, for the soundness half:

    ∀ bytes → compile arch doOpt src ≡ just bytes →
      Σ[ tp ∈ Typed ] ((src ⊢ tp) × Admissible arch tp
                       × (exec arch bytes ≈ ⟦ arch ⟧ˢ tp))

No `AllocState`, no `next-slot`, no abstract machine appears in the criterion.
The only runtime in it is `exec arch bytes` — the CONCRETE machine on emitted
bytes. And the emitted bytes reserve their slots exactly ONCE, in the
prologue: `ir-stack-budget ir = proj-budget (ir-to-trace' 0 0 ir)`, with
`frame-slots ≡ ir-stack-budget ir` at entry — which `X86-64` calls out as
"what makes the slot cluster a theorem rather than an assumption".

So there is no per-IR runtime slot allocation ANYWHERE in the artifact the
spec talks about. `exec-abstract (instr-alloc-stack n)` bumping `next-slot`
models nothing that exists. Option (b) below is therefore not a live
alternative — it would make the abstract machine diverge from the bytes in
order to make an internal lemma go through, which is the exact inversion of
what a correctness proof is for.

    (a) IS THE ANSWER. `next-slot` is a CONSTRUCTION-time frontier only —
        the `n` that `ir-to-trace'` threads. `exec-trace`'s alloc must not
        move it. Slot discipline is carried by `IRStackBudget` and the one
        prologue reservation the criterion actually observes.

For the record, the rejected alternative and why:

  (a) `exec-trace`'s alloc stops tracking `next-slot` at all. It becomes a
      construction-time frontier only; slot discipline is carried by the
      `IRStackBudget` record and the function prologue (`subq $budget*8, %rsp`).
      This matches the stated design — `SumInlAllocWF`: "slot allocation is
      implicit in the function prologue; the abstract trace doesn't bump
      next-slot" — and it is the only option consistent with `EmittableI`.
  (b) `ir-to-trace'` emits `instr-alloc-stack`, and it is re-admitted to
      `EmittableI`/`FrameFreeI`. This contradicts the current invariants and
      changes generated code.

(a) changes `AllocState`/`exec-abstract` semantics for EVERY handler, so it is
not a pair-local edit and must not be started as one — but it is no longer a
judgement call about which internal design is nicer.

**The general lesson.** An internal invariant is not free to be invented. Its
shape is DERIVABLE from the spec, and deriving it is cheaper than discovering
by eleven proof gaps that the invention cannot be reconciled with the emitted
code. `next-slot` acquired a runtime meaning nothing in `CorrectCompiler` asks
for; every proof written against that meaning was work that could not have
closed. Proving things about a wrong internal abstraction does not produce a
correctness proof — it relocates the gap to wherever the invention meets
reality, which here was `trace-is-ir-to-trace`, eleven times.

**The second lesson.** A proof gap on a correspondence field does not mean
"this proof is not written yet". It can mean the two things being related are
not relatable as stated. Eleven gaps that all name the same field, in every
handler sharing one structural feature, is not eleven pieces of unfinished
work — it is one modelling defect wearing eleven hats. Counting which handlers
DISCHARGE the field, and what distinguishes them, found it in one measurement.

## D151

**Question.** Why is the entire `*WF` handler layer — nine modules, thousands
of lines, `IRResultAWF`, `RecDispatcherWF`, `InputPlace`, `AllocBump`,
`IRStackBudget` — imported by NOTHING?

**The measurement.** The import closure of `Once.Certified` is 335 modules.
Against it:

    ISLAND  SimpleWF  ComposeWF  ApplyWF  PairWF  SumRecWF
    ISLAND  CurryStackWF  CurryAllocWF  SumInlAllocWF  SumInrAllocWF
    LIVE    ClosureWellFormed, ShapeAt, ShapeTable, SMCore, SMPrimitives,
            FrameFree, IRToTrace, Once.IR

`ClosureWellFormed` is live, but only its TYPES are, through `ShapeAt`,
`ValidAtWFHalted`, `IRObsCorrectFlat`, `FlatFromObs`, `ReadTypedAdequate`.
The handlers that would inhabit those types are reachable from nothing.

**Walking the live path down from the criterion** —

    correct                      (Once.Spec.Correct, the criterion)
      correctᵈ / correctR-sound  (Once.Adequacy.Compile)
        correct-gm → module-to-asm-correct → codegen-asm-correct
          ArchCorrect.asm-trace-correct     (per arch)
          ArchCorrect.ir-flat-correct       (per arch)
            ir-flat-correct-of              PROVED from `traces-agree`
              ir-obs-correct ir             ← THE dispatcher
                obs-correct-pair            POSTULATE
                obs-correct-inl             POSTULATE
                obs-correct-curry           POSTULATE
                obs-correct-apply           POSTULATE
                cata-correct                POSTULATE   (17 in total)

**The finding.** `ir-obs-correct` IS the top-level dispatcher. It exists, it
is live, and it recurses structurally —
`ir-obs-correct (g ∘ f) = comp-obs-correct (ir-obs-correct g) (ir-obs-correct f)`.
Every constructor routes to a postulate, and THOSE POSTULATES ARE THE HOLES
THE WF HANDLERS WERE WRITTEN TO FILL.

They cannot fill them, because they were written against a different
interface. The live obligation is

    IRObsCorrectF ir =
      ir-size ir < program-bound →
      ∀ mIn x input-loc s alloc → next-slot alloc ≡ 0 →
      ValidAtWF mIn alloc x input-loc s → BeforeFrontier alloc input-loc →
      halted s ≡ false → InputAt x input-loc s →
      MachineRefinesObsF ir x s alloc

while the handlers prove `IRResultAWF`, take an `InputPlace`, and demand a
`RecDispatcherWF` parameter. Two vocabularies for one job: `InputAt` vs
`InputPlace`, `MachineRefinesObsF` vs `IRResultAWF`, `ir-obs-correct` vs
`RecDispatcherWF`. The shared ones — `ValidAtWF`, `ResultPlace`, `ShapeAt` —
are exactly the ones in the LIVE module.

**Why the missing dispatcher was never missing.** Earlier work recorded
"`RecDispatcherWF` appears only ever as a module parameter, so the top-level
dispatcher does not exist" and treated building it as the next step. It does
exist. It is `ir-obs-correct`, it is live, and `RecDispatcherWF` is a
reinvention of it that no one ever instantiated — which is exactly why the
parameter is never applied.

**Decision.** The handlers are restated to discharge `obs-correct-X :
IRObsCorrectF X` directly, each one deleting a postulate. `IRResultAWF`,
`RecDispatcherWF`, `AllocBump` and `IRStackBudget` are island vocabulary and
retire with the island; `ValidAtWF`, `ResultPlace`, `InputAt` and `ShapeAt`
are the live vocabulary and stay. The measure of progress is the count of the
17 postulates, not the count of green WF modules.

**Two corrections this forces to earlier entries.** D150 said the eleven
`trace-is-ir-to-trace` gaps mean the compiler's correspondence is assumed.
More precisely: they are in DEAD code, so they never weakened
`Once.Certified` — and equally, the WF layer never strengthened it. The
modelling defect D150 identified was real and its fix landed in live modules
(`SMCore`, `SMPrimitives`, `FrameFree`); the gaps themselves were not
load-bearing. And plan 0.2.4.5's stage F work on `InputPlace` — `input-sv`,
`inputPlace-transport`, the `InputPlace`-shaped `run-*` signatures — was
island work. The inline-sum-payload change (D149) is the exception that
proves the rule: it landed in `ClosureWellFormed`/`ShapeAt`/`ShapeTable`,
which are LIVE, so it stands.

**The general lesson, and it is the same one as D150 one level up.** An
internal interface is not free to be invented either. `IRObsCorrectF` was
already there, fixed from above by what `ir-flat-correct` needs — the shape
was DERIVABLE. Building `IRResultAWF` alongside it produced nine modules that
typecheck, prove real things, and discharge nothing. Bottom-up construction
does not fail loudly: it fails by being green and unreachable.

## D152

**Question.** D151 named `IRObsCorrectF` "the live internal interface, fixed
from above". Is it the PRINCIPLED obligation, or just the shape the current
gap happens to have?

**It is not principled.** It is the shape the ENTRY case needs, with the
induction step postulated so the difference never surfaces.

**The derivation, from the emitter.** `ir-to-trace'` threads a frontier `n`
and a label base `l`:

    ir-to-trace' n l (g ∘ f) =
      let (n1 , l1 , ft , fb) = ir-to-trace' n  l  f
          (n2 , l2 , gt , gb) = ir-to-trace' n1 l1 g
      in n2 , l2 , (ft ++ mov-to-input ∷ gt) , (fb ++ gb)

`g` is emitted at `n1` — the frontier `f` left — which is not 0. But

  * `ir-to-trace ir = proj-trace (ir-to-trace' 0 0 ir)`;
  * `MachineRefinesObsF ir x s alloc` speaks only about `ir-to-trace ir`,
    hence only about frontier 0;
  * `IRObsCorrectF` demands `next-slot alloc ≡ 0` at EVERY use, recursive
    ones included.

So a sub-IR's witness concerns a trace that is NOT the one spliced into the
composite. The mismatch has to be absorbed somewhere, and it is:
`comp-step` — the composition case, the single place the frontiers would have
to be reconciled — is a POSTULATE.

**What the principled obligation is.** Frontier- and label-indexed, because
the emitter is:

    IRObsCorrect ir = ∀ n l → … → next-slot alloc ≡ n → … →
      MachineRefinesObs (trace-of (ir-to-trace' n l ir)) ir x s alloc

with `n = l = 0` the entry instance the consumer uses. The rule: THE
CORRECTNESS STATEMENT MUST THREAD WHATEVER THE EMITTER THREADS. `ir-to-trace'`
threads `(n , l)`; a statement quantifying over neither cannot compose, which
is precisely why `comp-step` could not be proven and became an axiom.

The label base is not optional for the same reason — `LabelScope`'s
`label-mono` / `labels-in` / `seg-agree` machinery already exists to support
exactly this threading, which is further evidence the frontier-0 statement is
the anomaly rather than the design.

**A correction to D151.** D151 read `next-slot alloc ≡ 0` as independent
confirmation that the frontier is construction-time (D150). It is not
independent evidence of anything: it is the frontier-0 restriction in
disguise. D150's conclusion stands on its own derivation from
`CorrectCompiler.correct` and the prologue; this premise neither supports nor
undermines it.

**The general lesson, a third instance.** D150: an internal INVARIANT is not
free to be invented. D151: an internal INTERFACE is not free to be invented.
D152: and when one IS invented, the tell is a postulated INDUCTION STEP.
A statement that holds at the entry case and is assumed to compose is a
statement that was written by looking at the consumer instead of at the
recursion. Look for the axiom sitting exactly where the induction would have
had to relate two instances of the interface — `comp-step` is that axiom
here, and it names the defect precisely.

## D153

**Question.** With the obligation re-indexed by the emission site (D152), is
`comp-step` provable? No — and the second obstruction is independent of the
first.

**The defect.** `IRObsCorrectF` demanded, side by side,

    ValidAtWF mIn alloc x input-loc s →   -- memory residency AT A LOCATION
    InputAt x input-loc s →                -- whose `in-reg` asserts NO memory residency

`valid-int-wf` requires `readLoc s loc ≡ just (prim-sv fits-int n)` — a MEMORY
read. A register-resident value has no such `loc`. So when `f` returns
`at-reg`, no caller can supply `ValidAtWF` for `g`, `ihg` cannot be applied,
and both halves of `comp-step` are unprovable — in exactly the case the file's
own piece-(4) note calls "the load-bearing one for rung A".

**It was half-fixed already, and that is the instructive part.** `InputAt`'s
`in-reg` carries a note saying it was "forced top-down by `comp-step`" because
"a pointer-only precondition could never be met, and `g`'s IH could not be
applied at all". That diagnosis is exactly right. But the `ValidAtWF` premise
beside it was left in place, re-imposing memory residency through the other
door. Half a fix is no fix: the register case remained uninstantiable.

**Why the merge is principled — not an induction from cases that worked.**

  * STRUCTURAL: the obligation bound `∀ (input-loc : ValueLocation FS)` OUTSIDE
    the residence choice. It committed to the input having a location before
    `InputAt` got to decide whether it has one, then demanded memory evidence
    for that location. Incoherent on its own terms, independent of usage.
  * SYMMETRY: the output side already IS a sum. `ResultPlace` puts the evidence
    in the branch that has it — `at-loc` carries loc+validity+frontier,
    `at-reg` carries fit+equation, `unit-result` carries nothing. The input
    side being `∀loc` plus loose evidence was an unmotivated asymmetry between
    two halves of ONE interface, and `comp-step` is precisely where they meet.
  * THE TELL: `result→input` (proven under the old shape) had to conclude
    `∃[ loc ] InputAt v loc s'` and take a `dflt` location the caller invents,
    only because `InputAt` was indexed by a location it does not always
    constrain. Under the merge it states as `InputAt mOut alloc v s'` — no
    existential, no invented location. A lemma getting SIMPLER under a change
    is the sign the change removed an artifact rather than adding one.

**Decision.** Residence and its evidence travel in ONE premise:

    data InputAt (mIn : AllocMode) (alloc : AllocState) (v : ⟦ A ⟧) (s) where
      in-loc  : (loc : ValueLocation FS) → ValidAtWF mIn alloc v loc s
              → BeforeFrontier alloc loc → readReg (regs s) Input1 ≡ SV-Ptr loc → …
      in-reg  : (fit : FitsInRegI A) → readReg (regs s) Input1 ≡ prim-sv fit v → …
      in-unit : A ≡ Unit → …

Choosing `in-reg` now DISCHARGES the memory obligation instead of leaving it
to be supplied separately. `IRObsCorrectF` loses three premises.

**Corroboration at the entry.** `entry-witness` used to thread `entry-loc`,
`valid-unit-wf` and `entry-bf`. `main : IR Unit Unit` has no input residence,
so `in-unit refl` discharges it outright: that triple existed only to satisfy
a premise that should not have existed.

**The general lesson.** This is the island's `InputPlace` design, arrived at
independently from the live obligation — the third time the island turned out
to be right about WHAT the interface should be while being built in the wrong
place. A quantifier that ranges over a component before the case analysis that
decides whether the component exists is a design error, and its symptom is a
branch nobody can instantiate.

## D154

**How this was found — the method, not just the result.** The plan was to
prove a "prefix handover" lemma and then assemble `comp-value-realized` from
it. That lemma's shape was DERIVED BY REASONING about what the assembly would
need, which is a guess. Writing the assembly instead — with `tt` placeholders,
so the type errors report the real obligations — asked for something else
entirely on its first step. The guessed lemma was not what the goal wanted.

**The obligation the goal actually produced.** Applying `g`'s hypothesis in
`comp-step` demands

    next-slot _alloc ≡ n1

where `n1` is the frontier `f` leaves — `proj₁ (ir-to-trace' n l f)`, which is
where the emitter puts `g`. But D150 established that NO EXECUTION MOVES
`next-slot`: it is a construction-time frontier. So after running `f` the
runtime allocator still has `next-slot ≡ n`, while the emitter's frontier has
advanced to `n1`, and the premise cannot be met for the second component of
any composition.

**So `IRObsCorrectF`'s `next-slot alloc ≡ n` is the last remnant of the
construction/runtime conflation D150 diagnosed.** It ties a RUNTIME allocator
to a CONSTRUCTION-time frontier — precisely the two things D150 proved are
different. D152 re-indexed the obligation by the emission site and made the
premise read `≡ n` instead of `≡ 0`; that was right as far as it went, but it
preserved the coupling rather than removing it.

**The resolution already exists one layer down.** Under D150 the structured
machine got `exec-trace-nsi`: running from a construction frontier and from
the runtime allocator gives the SAME state, and allocators differing only in
`next-slot`. The flat machine needs its twin, and it is inherited rather than
new work — `flat-step-straight` is `exec-abstract` on `floc`/`falloc`, and the
per-instruction halves (`exec-abstract-state-nsi`, `exec-abstract-alloc-nsi`)
are already proved. With it, the assembly applies `ihg` at a construction
allocator whose frontier is `n1` and transports the conclusion back to the
actual run.

**The general lesson, and it is a method lesson.** A lemma whose shape was
derived by reasoning about a proof you have not written is a guess, however
well-informed. This session has four instances of the same correction:
`Shifted` gained `fret`, `flink` and `fclosure` one at a time, each forced by
the transition that uses it and none foreseen; and now a prefix lemma that the
goal never asked for. The cheap way to get an obligation's true shape is to
write the term that needs it and let the typechecker state it — placeholders
whose type errors print the goal cost one build and cannot be wrong.

## D155

**The premise no discharge ever used, and the one thing it blocked.** D154
found that `comp-value-realized` cannot apply `g`'s hypothesis, because doing
so demands `next-slot alloc' ≡ n1` for the allocator `f`'s run leaves, while
D150 established that no execution moves `next-slot`. D154 proposed to work
around the coupling: apply the hypothesis at a fabricated construction
allocator whose frontier is `n1`, and transport the conclusion back with the
flat twin of `exec-trace-nsi`.

That transport cannot exist, and the reason is worth stating: `ResultPlace`
carries `BeforeFrontier alloc loc`, whose stack case is `k < next-slot alloc`.
Transporting it from a frontier `n1` down to the run's actual `n ≤ n1` is a
STRENGTHENING — `frontier-monotone` (Allocation) goes the other way, and
rightly so. So the fabricated-allocator route buys the premise at the price of
a conclusion nobody can bring home.

**What the premise is for.** It says the emitter's scratch region `[n , …)` is
above anything the caller has live — live data is bounded by `next-slot alloc`,
which is exactly what `BeforeFrontier` means. That content is an INEQUALITY.
Stated as `≡` it says more, and D150 proved the surplus false: `next-slot` is a
construction-time frontier that execution never moves, while the emission
frontier advances through the program, so `next-slot alloc ≡ n` can hold at one
emission site and at none after it. `g ∘ f` always emits `g` at `n1 ≥ n`.

**The evidence that the surplus is dead weight.** Every discharged shape —
`obs-correct-id`, `-terminal`, `-free-heap`, `-out-μ`, `-Out`, both `-const`
clauses, `-sigop` — binds this argument as `_`. Not one of them reads it. The
only consumer was `comp-obs-correct`, which passes it through, and the only
producer `entry-witness`, where it is `next-slot (entry-alloc _) ≡ 0` and
becomes `≤ 0` by `z≤n`. So weakening `≡` to `≤` costs nothing that was being
spent.

**The change.** `IRObsCorrectF`'s premise is now `next-slot alloc ≤ n`, and
`comp-value-realized` / `comp-step` thread it. `g`'s hypothesis is then applied
at the allocator `f`'s run ACTUALLY leaves, with no fabrication and no
transport: `flat-run-keeps-next-slot` gives `next-slot alloc' ≡ next-slot
alloc`, and `frontier-mono f n l` (SlotBudget, already proved) gives `n ≤ n1`.
Composing the two with the premise discharges `next-slot alloc' ≤ n1`. Verified
against the goal, not argued: with the premise weakened, that argument
typechecks and the frontier obligation disappears from the assembly's error.

**What the goal asks for next, now that the frontier is out of the way.** One
thing, and it is purely a machine obligation — no validity, no residence, no
frontier:

    floc   (flat-run FU n l (g ∘ f) s alloc) ≡ floc   (flat-run fug n1 l1 g s' alloc')
    falloc (flat-run FU n l (g ∘ f) s alloc) ≡ falloc (flat-run fug n1 l1 g s' alloc')

`ResultPlace` mentions the run only through `floc` and `falloc`, so those two
equations are the whole of what is left of `comp-value-realized`. `Shifted`
(plan 0.88 A) is precisely their conjunction plus the four control components,
and `exec-flat-reloc` already propagates it — which is why relocation was the
right thing to build even though the prefix lemma beside it was not.

**And a limit of the CURRENT interface, forced by that statement rather than
guessed.** `flat-run fug n1 l1 g s' alloc'` starts at `mkFlat s' alloc' 0`, and
`Shifted d fsK (mkFlat s' alloc' 0)` unfolds to six components. Two are `refl`.
The other four are demands on the state the composite is in when it hands over:
`fpc ≡ suc (length (emitted n l f))`, `fret ≡ []`, `flink ≡ nothing`, and
`fclosure ≡ SV-Tag 0` — the last because `mkFlat` hardwires the closure
register to the entry filler. Meanwhile `value-realized`'s `∃ fuel` form cannot
supply even the first: at a fuel large enough to finish `f`, the run has fallen
off the end of `f`'s trace and `flat-halt` has set `halted := true`, so `g`'s
own `halted s ≡ false` premise fails. A fuel is not a handover; a STEP CHAIN to
a named settle state is. That is the next change to the interface, and it is
`value-realized`'s alone — nothing outside this module reads that field (the
apex adapter consumes only `traces-agree`).

## D156

**SUPERSEDED IN PART BY D157** — read them together. The assembly below is
real and is checked, but the two residual facts it reduces to are called
label-scope facts here, and only the JUMP half of them is. The CALL half is
refutable; D157 has the counterexample and the reason. So `comp-value-realized`
is a proof FROM those two agreements (`comp-value-realized-of`), not
outright, and it remains an axiom at the point of use.

**`comp-value-realized` is a proof.** It was one of the two axioms `comp-step`
split into (D152 A1). With D155's interface — the frontier premise weakened to
`≤`, and `value-realized` a step chain to a named settle state rather than a
fuel — the assembly goes through, and it is short:

    f's chain, relocated as a PREFIX  (same pc coordinates)
    the bridging `mov-to-input`       (one link)
    g's chain, relocated as a SUFFIX  (shifted by `length ft + 1`)

Every field of the composite's witness is then READ OFF `g`'s. That is not
luck: `shift` touches only `fpc`/`fret`/`flink`, and `ResultPlace` mentions the
run only through `floc` and `falloc`, so `place` transports literally, `live`
transports literally, and the three control fields are one `cong` each. The
hand-over itself — that the post-`mov` state IS a relocated entry state — is
`handover-eq`, a record equality out of `at-end`, `no-ret` and `no-link`. Those
three fields were added because `Shifted` asks for them; this is where they are
spent.

**What is left, and it is a different KIND of thing.** Two facts, both about
the EMITTER rather than the machine: `f`'s own jumps and calls resolve the same
way inside the composite as they do alone (`comp-prefix-agree`), and `g`'s do
too under the shift (`comp-suffix-agree`). The postulate count in
`IRObsCorrectFlat` goes 18 → 19 and that number is the wrong way to read this:
one opaque axiom about a composite RUN became two statements about LABEL SCOPE,
which is the thing `LabelScope` exists to prove (`label-mono` plus `labels-in`
give exactly the disjointness of `[l , l1)` and `[l1 , l2)`). Route known,
sub-goal named, and the machine half is finished.

**A defect found on the way, in machinery already landed.** `exec-flat-reloc`
(plan 0.88 A) takes its side condition as

    ∀ tg → find-label (t₁ ++ t₂) tg ≡ mmap (length t₁ +_) (find-label t₂ tg)

and that universal is UNSATISFIABLE the moment `t₁` defines a label of its own:
at such a `tg` the left side finds it in `t₁` and the right side is `nothing`.
It holds only over a label-free prefix — which a composite's `f` is not, as soon
as `f` contains a case, a cata or a closure. The lemma is not vacuous, but it is
restricted to a case the intended caller is not in, and the restriction is
invisible from its statement. The chain-level lemmas take the condition PER
INSTRUCTION instead — agreement of the step effect at each instruction the chain
actually fetches — which is the weakest form, is what the induction consumes,
and is meetable because the caller knows which label each fetched instruction
targets. Same lesson as the restricted-step-lemma one: a side condition stated
over more than the proof needs is where a false assumption hides.


## D157

**The two splice agreements are REFUTABLE, and the counterexample is
`curry`/`apply`.** D156 landed `comp-value-realized` as a proof from two
statements — `f`'s instructions have the same effect inside the composite as
alone, and `g`'s do too under the shift — and called them label-scope facts.
Only half of that is right.

A JUMP's target is syntactic. `c-jmp m` names `m`, `LabelScope` bounds the
labels a fragment mentions to its own window, `label-mono` makes the windows
disjoint, and the agreement follows. That half is a scope fact.

A CALL's target is not. `flat-exec-instr instr-call-closure prog fs =
do-call prog fs`, which reads the closure register, follows it into the heap,
and scans THE WHOLE PROGRAM for whatever label it finds there. Nothing in the
instruction names that label, so no property of the emitted text can bound it.
Concretely: `ir-to-trace' n l (curry body m)` puts `c-thunk (ℓ o this-label)`
INLINE in its own trace, and `ir-to-trace' n l apply` ends in
`instr-call-closure`. For `f = curry body m`, `g = apply`, at a state whose
closure resolves to `f`'s thunk label, the composite ENTERS `f`'s body while
`g` alone HALTS — `find-thunk gt _ ≡ nothing`. The two sides differ in
`halted`, so the universally-quantified agreement is false, and a postulate of
it would have been inconsistent.

**What this actually is: the fragment-vs-program gap.** `MachineRefinesObsF`
is stated over `emitted n l ir` — the fragment's OWN trace. A call that leaves
the fragment cannot be described there at all, and `apply` is exactly such a
call. This is the same family of error as D152 (a witness stated at frontier 0
while the emitter emits at `n`) and D155 (a fuel where a hand-over was needed):
the correctness statement must be indexed by what the machine actually reads,
and `do-call` reads the whole program. It also explains, without any new
argument, why `obs-correct-apply` and `obs-correct-curry` are still axioms.

**So the assembly stays, as a lemma with the agreements as ARGUMENTS.**
`comp-value-realized-of` is checked and its content is real — the three-piece
splice, the hand-over, the transport of every field. `comp-value-realized`
returns to being the axiom, and the lemma records in checkable form exactly
what that axiom reduces to: two agreements, one of which is a scope argument
and one of which needs the interface to see the program.

**Method note.** The refutation came from re-reading the postulate I had just
written and asking what its universally-quantified `st` ranges over. A residual
whose hypothesis quantifies over states with no constraint linking them to the
run is the shape that hides an inconsistency — the same tell as the
"state-premise / program-conclusion" residuals. Write the axiom, then try to
break it BEFORE building on it.

## D158

**Quantify over placement; do not relocate.** D157 left the composition proof
conditional on two splice agreements whose call case is refutable. The fix is
not a better agreement — it is to stop asking the question. A fragment's
witness is now stated IN A PROGRAM, at the offset its own text occupies, and
universally over both:

    ∀ (prog : AbstractTrace) (base : ℕ)
      → AllSlotStable prog → SpanAt prog base (emitted n l ir) → …

`SpanAt prog base t = ∀ k i → fetch t k ≡ just i → fetch prog (k + base) ≡ just i`
— fetch agreement, the weakest thing a run ever asks of a program.

**This IS the position-independence a relocation lemma was trying to prove.** A
fragment's correctness cannot depend on where it lands, because it is asserted
for EVERY landing. The difference from a shift lemma is that a shift places one
contiguous thing, and that is not enough: `ir-to-trace' n l (curry body m)`
emits the body at offset 7 of its OWN trace, so in `apply ∘ curry body` the
body and `apply` sit at unrelated offsets and no `shift d` maps both. That is
what D157's counterexample was really about. Quantifying costs nothing and
covers both, because each is placed on its own.

**`k + base`, not `base + k`.** At `k ≡ 0` it reduces to `base`, the entry
state's pc, and at literal `k` to `sucᵏ base`, where the machine actually is
after `k` straight steps. Every leaf shape's chain link is `refl` because of
that choice; with the arguments the other way round each would have needed
`+-identityʳ`.

**`comp-value-realized` is now a PROOF, unconditionally** — the postulate is
gone (18 → 17 named residuals in `IRObsCorrectFlat`). `f` and `g` are witnessed
in the SAME program, at `base` and `base + length ft + 1`, so there is no
second program for their scans to disagree with: `find-thunk prog ℓ` is the
same scan on both sides, which is exactly what `apply ∘ curry body` needs. The
splice is now three chains concatenated, with no shift, no `Shifted`, and no
side conditions. `handover-eq` lost its arithmetic too — the sequel's entry
state IS the state the bridge produced.

**Consequence: the plan 0.88 A relocation apparatus has no consumer.**
`Shifted`, the twelve `shifted-*` lemmas, `exec-flat-reloc`, `shift`,
`shifted-eq`, `flat-exec-instr-prefix`, `FlatSteps-prefix`, `FlatSteps-reloc` —
all unused now. That is the LESSONS #1 pattern once more: they were machinery
for an interface shape that was itself wrong, and proving things about it
relocated the gap rather than closing it. Left in place rather than deleted in
the same commit; deletion is its own call.

**Staged, and named as such.** `traces-agree` is still fragment-local. It has
to follow, and it cannot simply take the same index: run inside a program that
continues past the fragment, an `∃ fuel` event prefix over-collects the
successor's events. It must be bounded by the chain — `chain-events` (FlatEvents)
already exists for that.

**Also recorded, since D155 made it worse rather than better:** the hand-over
form bakes in TERMINATION — a chain to a settle state at the fragment's end.
That is right for every shape except `Ana`, which by construction has no final
state. `obs-correct-Ana` is a postulate either way, but the record's own comment
("only `Ana` carries a step-index") is where the reconciliation belongs.

## D159

**THE COMPILER OUTPUTS RELOCATABLE CODE, and that is encoded in a codomain
rather than asserted in a premise.**

### The decision

`ir-to-trace : IR A B → AbstractTrace` is the wrong codomain. A list IS a
placement: every position in it is a global index, and everything downstream
inherits that — `fpc` indexes into it, `blk-off` walks it from the start of the
program, `find-label`/`find-thunk` scan it, `Shifted` shifts indices into it.
The emitter's TYPE commits to a placement at the one level where the placement
is not yet determined.

The emitter shall produce a COMPILATION UNIT — an entry block plus a set of
NAMED blocks — and placement shall happen exactly once, in `link`:

    record CompUnit : Set where
      entry  : AbstractTrace                        -- block-local positions only
      blocks : List (LabelId × ℕ × AbstractTrace)   -- label, frame budget, body

    ir-to-unit  : IR A B → CompUnit
    link        : CompUnit → AbstractTrace           -- the ONLY place addresses appear
    ir-to-trace ir = link (ir-to-unit ir)            -- apex statement UNCHANGED

### Why this form, and not an invariant (OCP-0005)

OCP-0005's rule is "encoding turns *we decided X* into *the compiler rejects
¬X*", and its success story is `⇒[pure]`: purity is not asserted and checked,
it is a GRADE IN THE TYPE, so the violation is unsayable.

By that standard the premise form is the weak one. D158 threaded
`SpanAt prog base (emitted n l ir)` — a placement hypothesis — through the
correctness statement. That is a prose decision in typed clothing, and D157 is
the proof: a premise of exactly that kind was written, was REFUTABLE, and
nothing structural caught it. A predicate (`Relocatable : AbstractTrace → Set`)
is no better: it asserts that a representation WITH positions happens not to
depend on them, which is a claim one can state wrongly or weakly.

Removing positions from the representation is the strong form. There is then no
position-dependent statement to write.

### Why this layer

The emitter's output type is the FIRST level at which a position could enter
and the LAST at which it is still undetermined — the same principle as
"canonicalise as early as possible". Not the machine: a symbolic `fpc` bolted
onto a placed representation still lets the emitter produce placed code. Not the
apex: `correct` speaks of ONE program, so it has no fragments and nothing to say
about placement. Position-independence is a property of the induction we choose,
and the induction is fixed by what the emitter produces.

### The layering that follows

1. REPRESENTATION — `CompUnit` has no global positions. (The encoding; ¬X unsayable.)
2. UNIT WELL-FORMEDNESS — block labels are distinct. This is `LabelScope`'s real
   content, stated ONCE on the unit instead of threaded through every fragment
   proof. (`LabelScope`'s `SegAgree` induction is measured-but-unlanded; under
   units the obligation changes shape rather than needing that induction.)
3. LINK CORRECTNESS — `link` preserves behaviour. THIS is where relocation
   lives, proved once and globally.
4. APEX — `correct` unchanged.

### The relocation work is not wasted; it was applied at the wrong level

`Shifted`, the twelve `shifted-*` lemmas and `exec-flat-reloc` (plan 0.88 A) are
exactly what proving `link` behaviour-preserving requires, because `link` places
blocks at offsets. They belong to the LINKER — one global lemma — not to the
per-composition induction, where D157 showed they cannot be made to hold anyway.

### This design is already implemented at three levels; the abstract emitter
### is the one that refuses to feed it

  * `ir-to-trace'`'s fourth component is `List (ℕ × ℕ × AbstractTrace)` —
    (label, budget, trace). That IS the block map.
  * `ir-to-bodies` / `ir-to-bodies-from` are the accessors, exported.
  * All three backends implement block emission: `emit-thunk-body o cl
    (lbl , budget , body-trace)` emits `.L_thunk_<lbl>:` with its own
    `subq/addq` frame and `ret`, placed AFTER the parent's `ret` and "reachable
    only via `lea .L_thunk_<n>(%rip)`".

And NOTHING EVER FILLS IT. Every clause of `ir-to-trace'` returns `[]`, passes a
sub-IR's list through, or concatenates two. In particular `curry` INLINES its
body into the main trace and emits `c-jmp (ℓ o end-label)` purely to jump over
it — the jump and the label exist only because of the inlining — and `Cata`
splices its algebra even though its own comment says the algebra "runs in its
OWN frame as a called body (exactly as `curry`'s body is generated)".

So the abstract emitter contradicts a model the concrete backends already
implement. That divergence is the root of D157: `apply ∘ curry body` is
unprovable precisely because `curry`'s body is spliced into `curry`'s trace at
an offset unrelated to `apply`'s, so no single placement maps both.

### What collapses

  * `Shifted` + relocation in the composition proof — nothing to shift.
  * `SpanAt prog base`, `k + base`, `shuffle`, `length-++` (D158) — become
    `u.blocks ⊆ prog.blocks`, monotone, preserved by composition definitionally
    because composition of units is UNION.
  * `find-label` becomes BLOCK-LOCAL, so "a jump never leaves its body" is true
    by construction rather than a scoping theorem.
  * `find-thunk` becomes block lookup, so D082's two label namespaces become two
    TYPES rather than a naming discipline.
  * `blk-off` (412 sites) goes from a walk from the start of the PROGRAM to an
    offset within a BLOCK — from a global quantity to a local one, which is why
    fragment-local statements become possible at all.
  * `apply ∘ curry body` closes for free: the union contains the body's block.

## D160

**LABEL SCOPING COVERS THE LINKED PROGRAM, AND THE HYPOTHESIS THAT MAKES THE
TWO HALVES COMPOSE IS `NoCross`, NOT DISJOINT WINDOWS.**

### The obligation D159 created

D159 made the emitter produce a `CompUnit` and `link` the single placement:

    ir-to-trace ir = entry u ++ instr-ctrl (c-ret (entry-budget u)) ∷
                     blocks-layout (blocks u)

Every whole-program invariant then had to be re-stated over *that*, not over
the entry block. `LabelScope`'s was the last one outstanding:
`emitted-jump-in-segment` says a jump lands in the segment it left, and
`find-label` scans the WHOLE linked program — so a jump in the entry could, as
far as the old proof knew, land on a `c-label` inside a closure body. The old
proof discharged it with `seg-agree ir 0 0`, which is `SegAgree` of the ENTRY
BLOCK, applied to a goal about the program.

### Why windows cannot close it

`SegAgree` composes over `++` only when the two halves' label windows are
disjoint (`segagree-++'`). `link` cannot supply that. A closure body's labels
are drawn from INSIDE its parent's counter range — `curry` at `l` hands the
body `l+2` and adopts the body's final counter as its own — so the entry's
window and the blocks' window always overlap, at every composite.

What is true is weaker and sufficient: **no label MENTIONED on one side is
`c-label`-DEFINED on the other.**

    NoCross t1 t2 = ∀ m r s → mention-at t1 r ≡ just m
                  → fetch-at t2 s ≡ just (instr-ctrl (c-label m)) → ⊥

Disjoint windows are ONE WAY to supply `NoCross`; they are not the fact.
`segagree-++ⁿ` takes the fact. And unlike `SegAgree`, `NoCross` IS closed under
`++` on both sides (`nocross-++ˡ` / `nocross-++ʳ`), which is what makes it the
composable form.

### The shape of the proof

One record through one walk, rather than four walks over the same 29
constructors:

    record ScopeOK (t : AbstractTrace) (bs : Blocks) (lo hi : ℕ) : Set where
      field bl-in    : LabelsIn lo hi (blocks-layout bs)
            bl-agree : SegAgree (blocks-layout bs)
            nc-eb    : NoCross t (blocks-layout bs)
            nc-be    : NoCross (blocks-layout bs) t

    scope-ok : ∀ ir n l → ScopeOK (trace-of …) (bodies-of …) l (label-of …)
    linked-agree : ∀ ir → SegAgree (ir-to-trace ir)

Each case spends what it has: the 22 block-free constructors are `scope-nil`;
the two `curry` clauses have a LABEL-FREE entry (D082 — `c-thunk` and
`instr-load-code-addr` carry thunk provenance, not `once` labels), so both
`NoCross` directions are immediate, and it is inside the body's own block that
the hypothesis is first spent — the body's trace and the body's blocks share a
window, so only `NoCross` can join them. The composites (`∘`, `⟨_,_⟩`, `case`,
`Cata`) get theirs from the sub-IRs' `NoCross` recursively PLUS window
disjointness across the two sub-IRs, which is the one place windows do work:
`f`'s labels sit below `g`'s in both the entry and the block channel.

### `CataSplit`: the skeleton decomposition became a result

Every cata strategy's trace is `curry`'s shape —

    Hs ++ c-thunk thℓ bb ∷ (at ++ c-ret bb ∷ c-label endℓ ∷ [])

— and each `cata-*-agree` used to REDISCOVER that inside its own `where`-block
on the way to `segagree-curry`. The block side needs the identical
decomposition for `NoCross`, so it is now the RESULT of the four strategy
lemmas (`cata-*-split : CataSplit …`) and every consumer — `split-agree`,
`split-nc-l`, `split-nc-r` — is one application of it. A shared node-extractor,
not three copies of a case split.

### Consequence

`emitted-jump-in-segment` is now proved over `ir-to-trace ir` — the linked
program including its blocks — with no new residual. `LabelScope` was the last
red module from D159's `link` change.

## D161

**A TOOLCHAIN-TRUST AXIOM MAY NOT CERTIFY COMPILER LOGIC. `link` HAS ONE
IMPLEMENTATION.**

### The fault

`<arch>-loader-faithful` related two things:

    asm-sem asm     -- the emitted String: compileFunWithTarget builds it as
                    --   prologue ++ irToAsm ++ functionEpilogue ++ irToBodies
    conc-trace ir   -- run-trace (compile-trace-cnt o 0 (ir-to-trace ir))
                    --   …where ir-to-trace = link (ir-to-unit ir)

The right-hand side is the program every theorem is about. The left-hand side
is a DIFFERENT program, assembled by a hand-written String paste that
re-implements `link` — entry, then a literal `"    ret\n"`, then the bodies.
Nothing related the two but the axiom itself.

An axiom is allowed to say "the assembler and loader are faithful". It is not
allowed to say "and also, this hand-written concatenation equals the placement
function we proved things about". The second clause is compiler logic, and
smuggling it in is what let two real defects live:

* **The thunk symbol (D160).** `emit-thunk-body` rendered `".L_thunk_" ++
  showNat lbl`; every reference rendered `showLabelId`, which carries the
  CanonicalName path D089 added so a label and its owner read as one identity.
  Definition `.L_thunk_10`, reference `.L_thunk_once_4main_10`, on all three
  targets. The agreement was asserted in a COMMENT in `X86-64/Emit.agda`.
* **riscv64's calling convention.** `emit-thunk-body` allocates `slots b + 8`
  and spills `ra` into its own frame. `compile-abstract`'s `c-thunk` has since
  2026-08-16 used CALLER-RESERVES: allocate `slots b`, spill into the caller's
  word. While `ir-to-bodies` was always `[]` the emitter path was dead and this
  did not matter; D159 gave blocks a real existence and the emitted callee was
  suddenly on a different convention from its proved caller.

Both are the same structural fault wearing different clothes. Neither is a
codegen typo, and no amount of testing the codegen would have located the
cause — only narrowing the axiom does.

### The decision

The emitter renders the LINKED program and nothing else.

    ir-to-linked-from : ℕ → IR A B → ℕ × AbstractTrace
    ir-to-linked-from l ir = … , link (unit b t bs)

* every `irToAsm` takes it;
* the hand-written teardowns go — the trailing `addq`/`addl`, riscv64's
  `ld ra`/`addi sp`, and `functionEpilogue`'s `ret` — because `c-ret`'s
  lowering is character-for-character what they pasted on;
* `irToBodies` is DELETED: the `Target` record field, all three
  implementations, and `emit-thunk-body` with them;
* `labels-def` runs over the linked program, so `c-thunk` definitions finally
  appear in D100's distinctness list. They never had — the claim that the
  emitted local labels are distinct did not cover the very labels whose
  duplication caused the 2026-08-06 `already defined` regression.

`asm` is now by construction `programToText` of the lowered program, so the
axiom certifies only `assemble` and `exec-bytes`.

### Why this shape, and not a test

D160's symbol fix (one `thunkSym`, one `labelSym`) closes the string-drift
class but not this one: two implementations of a function will drift again,
somewhere else. The general test is **"is there a second expression of this,
and what forces them equal?"** — and the answer must be a definition, not a
comment and not an axiom.

It also makes the axiom DISCHARGEABLE. An arch that later ships a verified
loader can prove `exec-bytes (assemble (programToText p)) ≡ run-trace p`; it
could never have proved the old form, because that would have required proving
a String paste equals `link` — not a loader's business. Each arch supplies the
same narrow interface: postulate today, proof tomorrow, general proofs
unchanged.

### Still String-shaped, and therefore still able to drift

The function header (`.globl` + label) and `emitArithBlocks` are concatenated
outside the trace, and `sigop : String → ℕ → Label` carries a raw name into
codegen — the identity of an EXTERNAL symbol resolved from
`Strata/Interpretations/<mod>.<arch>` at link time, which no Agda type reaches.
Those are the remaining crossings, by the same test.

## D162 — THE BRIDGE STOPS MIRRORING AGDA'S SHAPES; A CHECK FOR WHAT IT CAN'T STOP (2026-09-08)

**Relates**: D161 (the emitter's second `link`), D165, D170 (same fault class, per D170's
entry); commit 87413ccbc; `formal/Once/Extract/Names.agda`, `formal/scripts/check-extraction-sync.sh`.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 87413ccbc (and
be34479a8, 2d44e1b75, `Compiler.agda`, `check-extraction-sync.sh`) but never written.

### Context
`Bridge.hs` computed `moduleHasMain` and `moduleImports` by pattern-matching MAlonzo
constructors (`C_DFunDef` with three fields when the constructor has two). Such a mirror fails
loudly only when a field COUNT changes; a changed field MEANING with the count intact would
compile and silently misread the AST.

### Decision
* Both predicates move into `Once.Extract.Names` as ordinary total Agda; the bridge calls them.
  `Compiler.agda`: "It contributes nothing to the theorem below — it is stable extracted NAMES
  plus two predicates the hand-written bridge used to compute by pattern-matching MAlonzo
  constructors."
* Stable names via `COMPILE GHC … as` were rejected: `--safe` (`make denot-safe`) forbids the
  pragmas in that cone, and the pragma needs a Haskell binding for every type in the signature,
  i.e. an unchecked Agda↔Haskell representation correspondence — "a new axiom in all but name".
* The remaining MAlonzo serial names stay, as a COST that can only fail at compile time;
  `make check-extraction-sync` reports them, plus `once.cabal`'s module list against what is
  actually extracted (both had drifted unnoticed for 84 commits).

### Consequences
`Bridge.hs` destructures no Agda datatype. Behaviour unchanged (43/62 exit tests before and
after — the branch's arith regression was D163's, not this commit's).

## D163 — ARITH RECOGNITION SEES TERMS UP TO THE CCC LAWS (2026-09-08)

**Relates**: plan 0.86 (QTT `restrictEnv` wrappers), D161, D164–D167 (the follow-up gap
closures), D165, D255 (later: primitives matched by meaning); commit 6d5c66166.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 6d5c66166 (and
`Recognise.agda`, `EmittedWF.agda`, `SourceTrace.agda`, 8a9d1aabe, eb95c9e76, plan 0.108) but
never written.

### Context
Branch at 43/62 exit tests, 119/737 cabal tests, every failure `undefined reference to
once_1?arithzd{add,sub,div,mod}zd{int,float}`. QTT wraps every operand in `envˡ`/`envʳ`
(`fst`, or `⟨ … ∘ fst , snd ⟩`) and `effApp` composes another on top. The recogniser matched
SYNTACTIC normal forms, so no `ArithBlock` was built and the bare `arith.<op>` SigOp reached
the emitter.

### Decision
Recognition works up to the CCC laws, each a law rather than a special case (`Recognise.agda`:
"recognition must see terms UP TO THE CCC LAWS, because the elaborator no longer hands it
normal forms"):
* re-association `(f ∘ g) ∘ h ≡ f ∘ (g ∘ h)`, applied first;
* product beta `fst ∘ ⟨a,b⟩ ≡ a`, via `recognise-path-through m p` (also fixes
  multi-variable contexts);
* distribution `⟨a,b⟩ ∘ h ≡ ⟨ a ∘ h , b ∘ h ⟩`;
* terminality `terminal ∘ h ≡ terminal`.
Float twins for all four.

### Consequences
62/62 exit tests (= master), 737/737 cabal tests. Recorded as NOT fixed: `rewrite-ir` had no
soundness proof and the model and the emitted program differed by this pass, which is why a
recogniser that stopped firing broke no theorem — taken up by D165 and D166/D167.

## D164 — CLOSE `EmittedWF`'S CATCH-ALLS; RECORD THE SIGOP GAP (2026-09-08)

**Relates**: D100 (`labels-resolvable`), D163, D166 (the gap written down here is stated
there); commit 408cb3c2b; `formal/Once/CCC/Codegen/EmittedWF.agda`.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 408cb3c2b (and
`EmittedWF.agda`, 8a9d1aabe) but never written.

### Context
`labels-def-i` and `labels-ref-i` each ended in a catch-all returning `[]`, so a new or retired
constructor silently got the verdict "defines nothing, references nothing".

### Decision
* Both walks enumerate all 31 `AbstractInstr` and all 6 `FlatCtrl` constructors. Code comment:
  "D164: ENUMERATED, not a catch-all. A new instruction must now be given a verdict here rather
  than silently defining nothing."
* `instr-sigop` is deliberately NOT added to `labels-ref`: it lowers to `call
  <once-symbol-path (name si)>`, a `.globl` symbol, while `labels-def` collects only `c-label` /
  `c-thunk`; listing it would make `labels-resolvable` false rather than useful. The needed
  obligation is a SIBLING over `CanonicalName`s with its own resolution rule, and it did not
  exist anywhere — "exactly what let D163's regression ship a `call` to a symbol nothing
  defined".

### Consequences
Behaviour unchanged. The gap is recorded where it is skipped; at this commit `EmittedWF` had
zero consumers and `<arch>-loader-faithful` covered only `as`'s "already defined" half.

## D165 — THE TOOLCHAIN AXIOM STOPS CERTIFYING THE ARITH PASS (2026-09-08)

**Status**: the split-out residual was later PROVED (plan 0.103, 8cc5daff2:
`rewrite-program-preserves`, restated at the meaning — `Adequacy/RewritePreserves.agda`); the
loader axiom itself was deleted by D262.
**Relates**: D161 (same fault one level down), D163, D255, D261/D262; commit f23c5c431.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from f23c5c431 (and many
later entries, plans 0.107/0.108/0.111, `SourceTrace.agda`, `Compile.agda`, `LiftSound.agda`,
`RewritePreserves.agda`) but never written.

### Context
`ArchCorrect.asm-trace-correct` equated `asm-sem asm n` (text generated from
`rewrite-ir (directCallIR ir)`) with `flat-trace (moduleToIR m) n` (the RAW IR). A toolchain
axiom was thereby also asserting that arith-block lifting preserves meaning — compiler logic,
invisible and uncounted. That is how D163 shipped through a green apex.

### Decision
* `moduleToIR-emitted` (with `map-rewrite`) names the IR the backend actually compiles (at
  `main`, `directCallIR` is the identity, so the difference is `rewrite-ir`).
* `asm-trace-correct`'s RHS is that program; the axiom trusts only the assembler / loader /
  printer round trip. Each `<arch>-loader-faithful` speaks about the emitted IR.
* `rewrite-preserves` is split out as a NAMED RESIDUAL (deferred proof): the block's VALUE must
  equal the subtree's, since an arith result can reach an observable SigOp's argument.
* The spec stays the RAW IR: "a specification may not depend on the optimiser."

### Consequences
`codegen-asm-correct` becomes three steps; apex theorem unchanged; residual count +1,
deliberately ("the assumption was always there, and is now countable"). "No compiler logic
inside a toolchain axiom" (D161/D165) became a cited rule (D261, D262, plans 0.107, 0.111).

## D166 — THE `ld` HALF, STATED: WHICH SIGOP SYMBOLS THIS MODULE OWES (2026-09-08)

**Status**: justification CORRECTED the same day (b058bb939); the list itself unchanged.
Wired by D167.
**Relates**: D061/D071 (a SigOp is a closed contract), D163, D164, D167; commits 8a9d1aabe,
b058bb939; `EmittedWF.agda` (`syms-ref`).
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 8a9d1aabe and
b058bb939 (and `EmittedWF.agda`) but never written.

### Context
`EmittedWF` covered `.L` locals and `DistinctSymbols` the "already defined" half for `.globl`;
the `.globl` "undefined reference" half existed nowhere.

### Decision
`syms-ref` collects the symbols the emitted text CALLS that this module must DEFINE, filtered by
`sem`'s three-way split: `pureV` SigOps are owed by this module (their only implementation is
the `arith.block.<digest>` body); `emitsV`/`haltsV` are resolved by `ld` against a linked
interpretation. Enumerated over all 31 `AbstractInstr` constructors (`instr-call-closure` names
no symbol; `instr-load-code-addr` is a local label, already in `labels-ref`).

Correction (b058bb939): the first justification ("`pureV` means nothing links it") was a
LINKING story, restating the confusion D071 corrects. Per D061 a SigOp carries a contract
(`semM` + `EffectShape` + `impl ⊨ semM`) with exactly two producers: an interpretation
(discharged off-line) or the compiler itself (arith SigOps, discharged by `rewrite-ir` lifting
into a block). "The undefined symbol is the SYMPTOM, not the fault." Recorded assumption:
"pureV ⇒ ours" holds only because interpretation contracts are always `emitsV`/`haltsV`; a pure
external would require carrying the discharge owner explicitly (`Linkage`, D071).

### Consequences
Not wired at this commit (no `SymbolsResolvable` yet); comment-only correction, apex unaffected.

## D167 — WIRE THE `ld` HALF: THE EMITTED TEXT MUST LINK (2026-09-08)

**Status**: superseded by D262 (2026-10-04): the `<arch>-loader-faithful` postulates and their
text-level preconditions are gone; `SymbolClash.agda` was deleted, and the property is now part
of the PROVED `file-wf` obligation (`Compile.agda`: "D100/D167 were its postulated halves").
**Relates**: D061/D071, D100, D163, D166, D169, D262, plan 0.64; commit eb95c9e76.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from eb95c9e76 (and
5cdba1c3d, D261, D262, plan 0.89, plan 0.107, `Adequacy/Compile.agda`) but never written.

### Context
`ld`'s rejection of a call to an undefined symbol was stated at neither level; D163 shipped such
a call (`once_15arithzddivzdint`) through a green apex.

### Decision
* `Once.Compile.moduleSymRefs` / `moduleSymDefs`, read off the SAME `ir'` the backend compiles
  (`directCallIR` then `rewrite-ir`), as `moduleLabels` is.
* `Once.Adequacy.SymbolClash.SymbolsResolvable` + named residual `program-symbols-resolvable`,
  sibling of `program-labels-distinct`.
* Threaded as a third precondition of `asm-trace-correct` and each `<arch>-loader-faithful`,
  supplied at the apex, so `correct` gains no hypothesis.
* Framed per D061/D071: the predicate is the checkable CONSEQUENCE of a compiler SigOp's
  contract being discharged by lifting; a named definition is a context projection and never
  appears in `syms-ref`.

### Consequences
`syms-ref` went from 0 consumers to 4. The residual is true today; its proof would be the
recogniser's completeness, turning a recogniser regression into a type error.

## D168 — `link-correct`: A BLOCK RUNS WHERE IT IS PLACED (2026-09-08)

**Status**: landed as plan 0.89 Phase D1. Plan 0.91 S2 (ca6931261) predicted the machinery was
"demanded after all" for `entry-blocks`; that prediction was WRONG (94ffb4105, a6b5702b6):
`blocks-placed` goes through by direct induction, and `link-block-steps` still has no consumer.
**Relates**: plan 0.89 D1, D155 (`exec-flat-reloc`'s unsatisfiable hypothesis), D157, D159
(bodies as named blocks), D170; commits daedb6725, d848c5255.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from daedb6725 and
d848c5255 (and D170, D173 era commits, plans 0.89/0.91, `FlatStepLemmas.agda`, `SMCore.agda`,
`ClosureWellFormed.agda`, `FlatFromObs.agda`) but never written; only the subheading
"D168 is demanded after all" existed.

### Context
After D159 a closure body is a named block in `link u = entry ++ c-ret ∷ blocks-layout bs`, i.e.
a MIDDLE fragment. Plan 0.89 D1 asked for ONE global `link-correct` lemma instead of a
per-composition side condition.

### Decision
* `link-block-split` (SMCore, pure list algebra): `blocks u ≡ before ++ (lbl , b , t) ∷ after
  → link u ≡ link-pre u before lbl b ++ (t ++ link-post after b)` — the offset is read off the
  presentation.
* `link-block-steps` (FlatStepLemmas): `FlatSteps t k fs fs' → FlatSteps (link u) k (shift d
  fs) (shift d fs')`, `d = length link-pre`.
* Built on chain-level lemmas (`FlatSteps-prefix` + `FlatSteps-reloc`) with PER-INSTRUCTION
  side conditions, NOT on `exec-flat-reloc`, whose `∀ tg` hypothesis is unsatisfiable once the
  prefix defines a label (D155) — and the entry always does.

### Consequences
D170's `apply` story relies on it in prose (a closure's body found by label and relocated);
the `entry-blocks` proof did not need it.

## D169 — THE `ld` HALF FOR LOCAL LABELS TOO: THE PAIR IS COMPLETE (2026-09-08)

**Status**: superseded by D262 (2026-10-04): `LabelClash.agda` and the loader axioms are gone;
the text-level residuals were consolidated into the proved `file-wf`.
**Relates**: D100 (`labels-resolvable`, unconsumed since), D159, D160, D167, D262; commit
bdc230dc3.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from bdc230dc3 (and
5b6b9193c, D262, plan 0.89, the 0.91 closure entry) but never written.

### Context
`EmittedWF.labels-resolvable` had stated "local labels resolve" since D100 with no consumer.

### Decision
Wire it, completing the 2×2 table of the toolchain's rejections:

              as: "already defined"          ld: "undefined reference"
    .globl    DistinctSymbols (NameClash)    SymbolsResolvable  (D167)
    .L        DistinctLabels  (D100)         LabelsResolvable   (D169)

`moduleLabelRefs` is read off the same `ir'` as `moduleLabels`/`moduleSymRefs`; the residual is
supplied at the apex (no new hypothesis on `correct`), so `<arch>-loader-faithful` is false only
for programs the emitter should never produce. Not idle: before D159 the `c-thunk` named by
`instr-load-code-addr` lived in inlined text, and `AbstractToRiscV.agda` records "the `lla`
referenced an undefined symbol — a link failure … invisible to the proofs".

### Consequences
`labels-ref` 0 → 2 consumers. D160's `linked-agree`/`scope-ok` named as the proof's input.

## D170

**A CLOSURE VALUE CARRIES ITS CODE'S NAME, NOT ITS CODE'S BEHAVIOUR.
`valid-closure-wf` DROPS `BodyCorrect`; `apply` LOOKS THE BODY UP.**

> **Wording corrected on review.** An earlier draft said "carries its code's
> ADDRESS". Wrong, and it undercut the point. What the value holds is
> `SV-Code body-label` with `body-label : LabelId` — a SYMBOL. The abstract
> layer has no addresses at all; one appears only at the concrete machine,
> where `sim-load-code-addr` consumes `caddr hv n ≡ j` and the code map
> resolves the label. The closure value is placement-independent PRECISELY
> because it holds a name rather than an offset — which is D159's whole point,
> and the reason `link` can put the block anywhere.

### The symptom

Plan 0.89 Phase E1 asks that `valid-closure-wf` carry "a `ValueRealized` over
the body's block" in place of `BodyCorrect`. That cannot be written:
`ValueRealized` lives in `IRObsCorrectFlat`, which IMPORTS
`ClosureWellFormed`; and it cannot move down, because `ValueRealized.place`
needs `ResultPlace`, which is inside `ClosureWellFormed`'s mutual block and
cannot be extracted — it references `ValidAtWF` itself.

The reflex is to call that a moduling problem and look for a common part to
break out, or to invert the two modules. Neither is right.

### The fault

`ValidAtWF` and `ResultPlace` belong together: both are REPRESENTATION — where
a value lives and whether the state represents it. Their mutual recursion is
honest (a pair's validity needs its components'; a result place carries a
validity). `IRResultAWF` and `ValueRealized` are EXECUTION — running an IR
produces a state satisfying those predicates. Execution above representation is
the CORRECT direction, and `IRObsCorrectFlat`'s import of `ClosureWellFormed`
is therefore right.

The one thing crossing the layers is `BodyCorrect`, and it crosses DOWNWARD:
`valid-closure-wf` — a statement about how a closure VALUE is represented —
carries a proof about how its body EXECUTES. `CurryStackWF` builds it,
`ApplyWF` consumes it (`BodyCorrect.execute body-correct arg …`), so the value
is a COURIER for an execution fact.

That single edge is:

* the only cycle in the block — `IRResultAWF` never mentions `ValidAtWF`
  directly, so `ValidAtWF → BodyCorrect → {ValidAtWF, IRResultAWF}` is it;
* why the block needs `NO_POSITIVITY_CHECK` (it sits in a constructor while
  mentioning `ValidAtWF` negatively in `execute`'s premise);
* and why `ValueRealized` cannot be moved down.

**The layering error is the type system reporting a design error.** A closure
value has no business carrying its body's behaviour.

### The decision

`valid-closure-wf` carries only REPRESENTATION:

    readLoc s closure-loc            ≡ just (SV-Ptr  env-loc)
    readLoc s (sucLoc closure-loc)   ≡ just (SV-Code body-label)
    ValidAtWF mEnv alloc env env-loc s

— all three of which it ALREADY has. The `BodyCorrect` field is deleted. The
body's behaviour is obtained where it is used: at `apply`, the code cell names
block `body-label`, the unit's block table maps it to the body, and
`link-block-steps` (D168) relocates that block's chain to wherever `link` put
it.

### Why this is possible only now

Before D159 a closure body was INLINED and NAMELESS — there was no table to
look anything up in, so the value had to carry its behaviour. D159 made bodies
named blocks of the `CompUnit`; D168 made a block's run relocate to its
placement. The courier became removable exactly when the address became
meaningful.

### Consequences

* the mutual block splits along the honest seam; `NO_POSITIVITY_CHECK` goes.
* `ValueRealized` does NOT move — it stays in the flat layer where it belongs,
  and Phase E1's blocked module-move is not needed at all.
* strictly less work than the plan's E1: no migration, one field deleted, and
  `ApplyWF`'s `BodyCorrect.execute` call replaced by a block lookup.
* it is what Phase E2 already described ("`obs-correct-apply` consumes it via
  block lookup"). The plan kept the carrying AND added the lookup; only the
  lookup is needed.
* E3 (`apply ∘ curry body`, the D157 counterexample) closes for the stated
  reason — the union contains the body's block — rather than by threading a
  witness through the value.

### Scope — is this closures only?

As an INSTANCE, yes, and checked: of `ValidAtWF`'s ten constructors —
`valid-{unit,pair,closure,inl,inr,int,float,str,buffer,primitive}-wf` — only
the closure carries an execution fact. Every other one carries `readLoc`,
`ValidAtWF` and `BeforeFrontier`, i.e. representation alone. That is exactly
why there is exactly one cycle.

As a RULE, no. The same shape appeared three more times in one day at other
layers: D161 (the emitter carried a second implementation of `link`), D162
(`Bridge.hs` mirrored an Agda datatype's shape), D165 (a toolchain axiom
carried the arith pass's correctness). One concept, expressed twice, related by
nothing. D170 is the value-level instance.

### The honest complication

`BodyCorrect` is NOT purely a courier. `CurryStackWF` calls it "recursive
dispatcher for body", and its `execute` field is a specialised
`RecDispatcherWF` — the well-founded recursion device the WF layer uses to
descend into a body whose size is below the bound. So deleting it has a second
consequence beyond breaking the cycle: THE RECURSION KNOT MOVES. `apply` must
obtain the body's behaviour from the unit's block table, and a body that itself
contains closures is handled by induction over the unit's blocks rather than by
threading a dispatcher through values.

That is the right place for it — the blocks are a finite, statically known map,
which is a better recursion measure than a size bound threaded through a value
— but it is real work and should not be described as removing redundancy.

### The general rule

A VALUE's well-formedness may mention only what is true of the value in the
state. If it carries a proof about what happens when the value is USED, the
predicate has absorbed an execution obligation, and the first symptom is a
mutual block that needs a positivity escape hatch. Carry the NAME, and look the
behaviour up where it is used.

## D171 — THE FLAT LAYER'S STORE READ-BACK IS THE SHARED FOUNDATION (2026-09-09)

**Relates**: plan 0.89 Phase E2, D170 (`valid-closure-wf` drops `BodyCorrect`), D172 (retracted;
D171 stands independently), D174 (builds the heap half); commit e2e60dd1c.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from e2e60dd1c (and
ea02c8305, 9b0f0ae7b, the D172 entry, `IRObsCorrect/{Prelude,Simple}.agda`) but never written.

### Context
Every discharged `obs-correct-*` clause touched at most `mov-to-output`; none handled
`store-at-slot`. So `obs-correct-{pair,inl,inr,curry}` — the clauses that write memory — shared
ONE missing foundation, not four difficulties. Store reasoning existed only in the
machine↔machine correspondence layer.

### Decision
Write the bridge from `flat-exec-instr` to `SMCore.writeLoc`, all three `refl` because
`store-at-slot` routes through `flat-step-straight`:

    flat-store-floc   : floc   (flat-exec-instr (store-at-slot slot) prog fs)
                      ≡ writeLoc (floc fs) (AtStack (current-frame (falloc fs)) slot)
                                 (readReg (regs (floc fs)) Output)
    flat-store-falloc : falloc (…) ≡ falloc fs
    flat-store-fpc    : fpc    (…) ≡ suc (fpc fs)

"The foundation was free; nobody had written it down."

### Consequences
With `curry-denot-[]`, `obs-correct-curry` reduces to state tracking through five instructions.
The follow-up (e20c7c4a9, comment tagged D171 in `Simple.agda`) found the `in-reg` residence a
spec question — resolved: the emitter is right, and `valid-inl-reg-wf` (0.86 F) already
expressed it.

## D172 — RAISED AND RETRACTED THE SAME DAY (2026-09-09)

**Recorded so the number is not a dangling reference: two commits mention D172,
and its claim was FALSE.**

D172 claimed that every compound-value witness demands its components be BOXED
(`readLoc s cell ≡ just (SV-Ptr loc)`), so the inline literal the emitter stores
for a register-fitting component was unsayable — and introduced `Represents`
(`rep-ptr` / `rep-inline`) to close the gap.

Both halves were wrong, and a `grep` would have shown it:

* `ValidAtWF` ALREADY has `valid-inl-reg-wf` / `valid-inr-reg-wf`
  (`ClosureWellFormed`), whose premise is
  `readLoc s (sucLoc sum-loc) ≡ just (inline-sv rep a)` with
  `rep : InlineRep A` — exactly the inline case claimed to be missing.
* `PayloadAt` ALREADY exists, with `payload-at-loc` / `payload-in-reg` — the
  same two-way split as `Represents`, notion for notion.

`Represents` was therefore a SECOND EXPRESSION OF AN EXISTING CONCEPT, which is
the fault D161, D162, D165 and D170 each removed an instance of. It is deleted;
nothing depended on it.

### The method error, which is the part worth keeping

The conclusion came from reading ONE constructor (`valid-inl-wf`), seeing it
demand `SV-Ptr`, and inferring that the witness excluded the literal case —
without checking for sibling constructors. This log's own rule is
check-then-assert, and it was skipped twice in one session: first framing the
SigOp obligation without reading D061/D071, then this.

**Before concluding that a witness cannot express something, enumerate the
constructors of the thing that would express it.**

### What survives

`flat-store-floc` / `-falloc` / `-fpc` (D171) are independent and stand: the
flat layer's store read-back was genuinely missing and is genuinely needed by
every `obs-correct-*` clause that writes memory.

The `in-reg` observation is true but useless — `inl` on a register-resident
payload is witnessed by `valid-inl-reg-wf`, not by `valid-inl-wf`. So the
sum-payload question is NOT why `obs-correct-inl` is an axiom, and that cause
remains unfound.

## D173

**THE ACTUAL OBSTACLE FOR `obs-correct-inl` (and `pair`, `inr`, `curry`):
`ResultPlace.at-loc` IS REFUTABLE FOR A FRESH STACK RESULT, BECAUSE THE FLAT
MACHINE NEVER ADVANCES `next-slot`.**

Established by enumerating constructors, after D172 was retracted for inferring
instead of enumerating.

### The obstacle

`ValueRealized.place : ResultPlace B out-mode (falloc settle) cont-alloc`, and
for a sum only `at-loc` is available — `unit-result` needs `B ≡ Unit`, `at-reg`
needs `FitsInRegI (A + B)` and `FitsInReg` has only `fits-int`/`fits-float`.

`at-loc` demands `BeforeFrontier (falloc settle) loc`. `BeforeFrontier` has
exactly three constructors, and for `inl`'s result at
`AtStack (current-frame alloc) sum-slot` every one fails:

* `stack-before` needs `sum-slot < next-slot alloc`. But `sum-slot = n` and the
  obligation's own premise is `next-slot alloc ≤ n`, so this asks for `n < n`.
* `stack-ancestor` needs `current-frame alloc ≺ f`, and `f` IS
  `current-frame alloc` — the frames are equal, not strictly ordered.
* `heap-before` is about `AtDynamic`, not `AtStack`.

And nothing rescues it by moving the frontier: all four instructions `inl`
emits — `instr-load-tag-lit`, `store-at-slot`, `mov-to-output`, `lea-slot` —
return `, alloc` UNCHANGED. So `falloc settle ≡ alloc`, and the demand is
`n < next-slot alloc ≤ n`.

**The obligation is not hard, it is FALSE as stated.** Same class as D148 and
D150: fix the model, not the statement.

### Why it is shared

Every clause whose result is a FRESH STACK CELL hits it identically —
`obs-correct-pair` (pair record at `n`), `obs-correct-inl`/`inr` (sum record at
`n`), and `obs-correct-curry` (closure record at `n`). Four axioms, one cause,
and it is NOT the payload question D172 wrongly proposed.

### The tension it comes from

D150 already recorded the halves: "`next-slot` never moves at run time, while
the emission frontier advances through the program". The WF layer lives with it
by threading a CONSTRUCTION-TIME bumped alloc — `SumInlAllocWF` proves
`BeforeFrontier alloc-final sum-loc`, not `BeforeFrontier alloc sum-loc`. The
flat layer has no such alloc: `falloc` is the runtime one, and it never moves.

### The two resolutions

1. **The machine bumps.** `flat-exec-instr` advances `next-slot` when the
   emitter writes a fresh result cell, so `falloc settle` is genuinely past the
   result and `stack-before` holds. A model change, and it must not break
   `AllSlotStable` / the arch correspondences, which currently rely on
   `next-slot` being invariant.
2. **`place` takes the bumped alloc.** `ValueRealized.place`'s FIRST alloc
   stops being `falloc settle` and becomes a chosen post-alloc, the way the WF
   layer's `result-place` already takes `alloc-final`. The clause already
   chooses `cont-alloc` freely; this makes the pair symmetric.

(2) is the smaller change and matches what the WF layer already does. (1) is
the deeper question of whether the flat machine should model slot allocation at
all, which D150 left open. Not chosen here: the discharge has named it, and
choosing is a model decision.

### D173 — SCOPE CORRECTED, and a third resolution (2026-09-09)

Two corrections to the entry above.

**It does not apply to `pair`.** I wrote "every clause whose result is a FRESH
STACK CELL hits it identically — `obs-correct-pair` (pair record at `n`)". The
pair record is NOT a stack cell: Stage G made `⟨_,_⟩` mode-free
(`⟨_,_⟩ : IR A B → IR A C → IR A (B * C)`) and heap-only, its trace contains
`instr-alloc-heap 2`, and `exec-abstract (instr-alloc-heap n)` DOES advance the
frontier — `record alloc { next-heap-ref = new-state }` — while writing
`SV-Ptr (AtDynamic addr)`. So `heap-before` is available and `at-loc` goes
through. `obs-correct-pair` is an axiom for some other reason; this is not it.

**The obstacle is STACK-MODE-SPECIFIC.** It applies to `inl Stack`,
`inr Stack` and `curry _ Stack`, whose results are `AtStack` cells at the
emission frontier that nothing bumps past. Their Heap variants allocate, so
they are already fine.

**Which makes the real resolution PLAN 0.86, not either option recorded above.**
D142's whole content is that allocation is mechanical and the surface/IR mode
goes away — "bounded internals go to frontier scratch, unbounded internals to
the heap". `⟨_,_⟩` has already made that transition; `inl`, `inr` and `curry`
still carry `AllocMode` (`IR.agda` 147/148/160) and are what remains.

Finishing 0.86 for those three dissolves the obstacle rather than working
around it: with no Stack variant there is no `AtStack` result, the allocation
bumps `next-heap-ref`, and `heap-before` discharges what `stack-before` cannot.
That is preferable to both options above — (1) teaching the flat machine to bump
`next-slot` would model an allocation the language is removing, and (2)
re-indexing `ValueRealized.place` would carry the Stack case in the interface
after the language stops having one.

So the obstacle is not a proof gap to be closed where it appears; it is an
UNFINISHED MIGRATION showing through. The order is: finish 0.86 for
`inl`/`inr`/`curry`, then discharge.

## D174 — DISCHARGE `obs-correct-inl`: PLAN 0.88'S NUMBER MOVES, 17 → 16 (2026-09-11)

**Relates**: plan 0.88 (metric: count of `obs-correct-*` postulates), D171, D173 (blocked on
`AllocMode`), plan 0.86 stage G, D176, D177, D178; commit 1c4d6fe17.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 1c4d6fe17 (and
573aca30a, da4a9710e, 108ba3efa, b0be58fd6, plan 0.88, `IRObsCorrect/{Interface,Machine,Prelude,Sum}.agda`)
but never written.

### Context
Plan 0.88 counts progress only as `obs-correct-*` postulates removed. D173's obstacle (a Stack
result at a frontier nothing bumps) dissolved when 0.86 stage G removed `AllocMode`.

### Decision
`obs-correct-inl` becomes a DEFINITION: the ten-instruction run, `traces-agree`, all `halted` and
`InstrWF` obligations, and `place` over all three residences; `in-reg`/`in-unit` postulate-free.
One named residual, `inl-mem-pres` (caller-nameable locations unchanged), for `in-loc`.
Thirteen REUSABLE machine lemmas (`store-ind-*`, `load-slot-*`, `heap-read-*`,
`heap-untouched`, `sucHL-≢`, …) — the heap read-after-write vocabulary `SMCore` ships none of by
design. Rule recorded: "only a TYPE error moving forward is evidence of progress; a scope error
is evidence of nothing but a missing name" (two lines earlier marked "typechecked" never were).

### Consequences
The flat layer claims `SpanAt prog base (emitted n l ir)`, immune to what killed the `*WF`
layer (D176). The lemmas are reused by D177 and cited by plan 0.88 for `pair`; `inl-mem-pres`
is no longer a postulate in the current tree.

## D175 — DELETE THE `!!` HATCH: EVERY OBLIGATION IS A NAMED POSTULATE (2026-09-11)

**Relates**: D061 (`sigop-preserves-halted`), D176 (used this naming), D269/D270 (later fate of
the named postulates); commit 37e2e41cb; `SMPrimitives.agda`.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 37e2e41cb (and
`SMPrimitives.agda`, D176's commit) but never written.

### Context
`postulate !! : ∀ {ℓ} {A : Set ℓ} → A` existed twice (`Once.ProofObligation`, a clone in
`SMPrimitives`), with ~105 uses.

### Decision
Both definitions deleted; every use became a named postulate with its own type (~60 created).
`SMPrimitives.agda`: "an anonymous `!!` reachable from everywhere is one node, which is no ledger
at all … Removing the definition is what keeps it gone: no future proof can reach for `!!`
without declaring what it is assuming."

### Consequences
* No `!!` was ever on the apex path; the apex ledger is unchanged. What the hatch hid were the
  OFF-PATH obligations.
* Naming separated kinds: `ASSUMED-trace-is-ir-to-trace` (the `*WF` cluster's load-bearing
  claim, 9 sites); two `REFUTABLE-…` assumptions false at `instr-alloc-heap`, supplied in
  argument position (later deleted, D269); `sigop-preserves-halted`, an interface obligation
  (later an `InstrWF` premise, D270).
* Verdict: "the WF layer proves nothing the apex postulates" — input to D176. Edits inside the
  then-red `*WF` modules were not typechecked (stated in the commit).

## D176 — DELETE THE STRUCTURED-MACHINE `*WF` CLUSTER: D141 REDONE, ON MEASUREMENT (2026-09-11)

**Relates**: D141 (deleted then retracted in part, 2026-09-02), D159, D175, plan 0.64 group M,
plan 0.88; commit 997e647b5; 108ba3efa (template index).
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 997e647b5 (and
1c4d6fe17, d044739a9, 108ba3efa, plan 0.88) but never written.

### Context
D141's earlier deletion was retracted ("it is the discharge route"). This decision re-takes it
with four independent checks.

### Decision
Delete 16 modules, 7061 lines: ApplyWF, PairWF, SumRecWF, ComposeWF, SimpleWF, CurryWF,
SumInl/InrAllocWF, LambekValidity, RecSchemePostulates, plus the tail they alone kept alive
(DispatcherArithmeticLemma, FrontierLemma, SMPrimitives/Heap, SizeBoundLemma, TraceEvaluator,
Memory/TypeSlots). Checks: (1) reachability — zero apex declarations, no outside importers;
(2) content — the layer reaches the 17 `obs-correct-*` only via `trace-is-ir-to-trace`, assumed
at 9 sites and refuted at the 2 that try; (3) structural — after D159 the structured machine
cannot execute a linked image (`instr-ctrl` is a no-op, no `fpc`); (4) termination — no
`TERMINATING` in the obs layer, and the WF size-bound device already migrated to
`IRObsCorrectF`. `ClosureWellFormed` stays.

### Consequences
Not cascaded: `MuSize`/`MuValidity`, `Optimizer/*`, `Fusion/Correct` etc. each want their own
verdict. 108ba3efa later indexed the 386 proved internal lemmas (recoverable via
`git show 997e647b^:…`) as the template for flat discharges; the verdict stands.

## D177 — DISCHARGE `obs-correct-inr`: 0.88 AT 15, THE FOUNDATION PROVES ITSELF (2026-09-11)

**Relates**: D174 (the mirrored proof and its lemmas), plan 0.88; commit 185766096.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from 185766096 but
never written.

### Context
`inr` is `inl`'s mirror: the same ten-instruction heap build with `instr-load-tag-lit 1`.

### Decision
Discharge by RENAME alone (`inl`→`inr`, tag 0→1, `valid-inl-*`→`valid-inr-*`,
`inl-mem-pres`→`inr-mem-pres`); the only manual step was importing `valid-inr-wf` /
`valid-inr-reg-wf`. Residual `inr-mem-pres` mirrors `inl-mem-pres`. Metric 17 → 16 → 15.

### Consequences
Evidence D174's thirteen lemmas are MACHINE lemmas: `inr` used all of them untouched. Scripting
rule recorded: the safety property is LOCAL VERIFICATION — a whole-block copy plus total rename
in one file, typechecked immediately, vs the stage-G failure (a shape-guessing regex across many
files). Also recorded: class G (`Para`, `in-ν`, `Ana`, `Hylo`, `Fuse`) compile to `[]` and are
REFUTABLE when the denotation emits; they need a design decision, not a proof.

## D178 — DISCHARGE `obs-correct-fst` AND `-snd`: 0.88 AT 13 (2026-09-11)

**Relates**: D174, D177, plan 0.88 (class ordering); commit a1b5270c4;
`IRObsCorrect/Simple.agda`.
**Note**: back-filled 2026-10-09 (plan 0.113 E) — the number was cited from a1b5270c4 (and
`IRObsCorrect/Simple.agda`) but never written.

### Context
`fst`/`snd` are one instruction each (`load-indirect`, `load-indirect-suc`); `valid-pair-wf`
already carries the component pointer, `BeforeFrontier` and `ValidAtWF`.

### Decision
Discharge both (`decomposePairWF` supplies `at-loc`; the other residences are absurd). Recorded:
* Class A (reads: `fst`/`snd`/`In`/`id`/`out-μ`) is CHEAPER than class B — the witness is
  derived from the input, zero new lemmas. `pair`/`curry` are not the easy half of B: they
  splice sub-IR traces and need IHs, nearer `case` in difficulty.
* A result's MODE is the destructured component's (`PairValidWF.mA`), not the input's.
* When the run depends on the residence, the whole `ValueRealized` record is per-clause.
* `InstrWF s alloc load-indirect` ignores `alloc`, so `load-indirect-twf`'s `{alloc}` is
  caller-supplied.
* "a mirror is rename-only; if it needs a structural edit, read the target's signature".

### Consequences
Metric 15 → 13. `Simple.agda`: "`fst` / `snd` — DISCHARGED (D178)".

## D179 — `Behavior` IS A RECORD: the three laws travel with the family (2026-09-12)

`Behavior = ℕ → List SigOpEvent` said "the first `n` events" in its header and
nothing in its type. Plan 0.90 makes the sentence the type:

```agda
record Behavior : Set where
  field
    at        : ℕ → List SigOpEvent
    extends   : ∀ n → ∃[ rest ] (at (suc n) ≡ at n ++ rest)
    bounded   : ∀ n → length (at n) ≤ n
    saturates : ∀ n → length (at n) < n → at (suc n) ≡ at n
```

**Why `saturates` is a field and not a convenience.** With `extends` and
`bounded` alone, `at₁ n` = "the first `min n ∣L∣` events" and `at₂ n` = "the
first `min (n/2) ∣L∣`" are both admissible families over the SAME trace `L`,
and they differ at `n = 1`. Since `_≋_` is pointwise, the two would count as
DIFFERENT behaviours — so `≋` would have been comparing production RATE as well
as trace, and a compiler could be observationally correct and still fail it for
reaching its third event one index later than the meaning. With `saturates`,
`at-stable` (`n ≤ m → at b n ≡ take n (at b m)`) pins one family per trace, so
pointwise equality IS trace equality: the inductive stand-in for bisimilarity
the header always claimed, now earned. Still no co-data, still no completion.

**What it costs a producer.** Exactly a `PrefixFamily` (TraceMonad) — `bnd`,
`sat`, `coh` — which is what `evalᴰ-good` (DenotPrefix) already proves for every
IR. So the IR meaning `⟦_⟧IR` pays nothing new; it just stops discarding the
proof it already had. The `take n` cap is GONE from `at`: `bounded` says the
prefix is already that short, so the cap only obscured which family it was.

**Three producers, three different sources for the laws.**

1. `⟦_⟧IR` (SourceTrace) — PROVES them, from `evalᴰ-good`.
2. `⟦_⟧ˢ` (Compile, surface) and `flat-trace-of` (FlatFromObs, abstract
   machine) — BORROW them, via `behavior-by`: a family pointwise equal to a
   behaviour is a behaviour. Borrowing is not weaker than proving; the equality
   is the same theorem the compiler's claim is stated with (`sd-eq`,
   `ir-flat-correct-fam`). Neither side needs a prefix-family induction of its
   own.
3. `meaningᵈ` (MainMeaning, direct) and `run-trace` (RunTraceCore, concrete
   machine) — ASSUME them, as two named residuals:
   * `mainMeaningᵈ-pf` — the `⟦_⟧ᶜ` analogue of `evalᴰ-good`. Deferred proof:
     the same induction over typed derivations discharges it. Stated about THE
     MEANING CHAIN, never about an arbitrary `MClo` (which would be false — a
     bare `ℕ → List × X` may be any family at all).
   * `run-trace-extends` / `run-trace-saturates` — what "`stepBudget` is
     adequate" MEANS: a deeper observation only adds events, and a family that
     has not filled its budget is finished. Same class and same boundary as the
     abstract `stepBudget` itself; provable the moment it is pinned.

Intermediates stay plain families (`runMainˢ`, `runMainᵈ`, `flat-trace-fam`):
every consumer compares them pointwise against a real `Behavior`, so obliging
each to rebuild the laws for a closure it only passes through would be work
with no reader.

## D180 — THE MACHINE OBLIGATION IS INDEXED BY OBSERVATION DEPTH (2026-09-12)

`ValueRealized` gained the denotational value (`TM.valueT (evalᴰ ir x) k`
instead of the pure `eval ir x` — one semantics on both halves at last), and
that immediately raised the question the pure form could not: AT WHICH BUDGET
is the value realized?

**An existential field does not compose.** With `obs-budget : ℕ` chosen by the
producer, `g ∘ f` is stuck: `evalᴰ (g ∘ f) x = evalᴰ f x >>=T evalᴰ g` spends
`f`'s events out of the composite's budget, so `g` must be applied to the value
`f` realizes AT THE COMPOSITE's depth — and a producer that picked its own
cannot be asked for that one. Recovering it would need value-stability of
`evalᴰ` (`valueT m j ≡ valueT m k`), a real theorem nothing else needs.

**So the depth moves OUTSIDE the witness.** `IRObsCorrectF ir` now ends
`… → ∀ (k : ℕ) → MachineRefinesObsF … k`, and the composition threads
`kg = k ∸ length (projTrace (evalᴰ f x) k)` — the same arithmetic `_>>=T_`
does, so the composite's value and `g`'s coincide DEFINITIONALLY and there is
no transport at the seam. This is also D058's original shape ("∃ fuel per
observation depth"), carried by the statement instead of by an ∃ inside it.

**`Out` fell out of the re-index, and the fall is the point.** A ν is now a
Kleisli value: forcing a layer is a computation, so `evalᴰ (Out wf) x` may
EMIT, while the machine's `Out` is one `mov-to-output` that emits nothing. If a
ν could reach that instruction the obligation would be FALSE. It cannot:
Class G emits NO instructions for `Ana`/`in-ν`, so no ν is ever built, and
`valid-ν-wf` — which existed only because the PURE domain made a ν a
first-order value with an already-available layer — is deleted. What replaces
it is its negation, `ν-not-resident`, and `obs-correct-Out` is discharged by
`⊥-elim`.

That is the audit's finding made mechanical: the old proof looked like a
theorem about `Out` and was a theorem about `inject x`, a ν that could not
emit. When `Ana` gets an emitter, THIS case is the one to reprove — against a
machine that forces layers, not one that moves a pointer.

## D181 — A CLOSURE'S ENVIRONMENT NEED NOT BE A POINTER (2026-09-12)

`obs-correct-curry` is the FIRST producer of `valid-closure-wf` — nothing in
the tree built one before, only transported and decomposed them. Writing it
found the constructor stated for the part of its domain that excludes the
common case.

`curry`'s emitter builds the closure record with the same ten-instruction heap
build `inl` uses, and its env cell receives whatever `Input1` held:

```
mov-to-output ∷ store-at-slot env ∷ instr-alloc-heap 2 ∷ store-at-slot clo ∷
mov-to-input ∷ load-from-slot env ∷ store-indirect ∷
instr-load-code-addr (ℓ o l) ∷ store-indirect-suc ∷ load-from-slot clo
```

`valid-closure-wf` demanded `readLoc s closure-loc ≡ just (SV-Ptr env-loc)` —
a POINTER env. That holds only for the `in-loc` input residence. For `in-reg`
the cell holds a register literal, and for `in-unit` it holds the tag filler,
which D074 says is unconstrained. So `curry` was unprovable for a `Unit`
environment — and a `Unit` environment is `main`'s, which makes the very first
closure a program builds the one that could not be witnessed.

The fix is stage F's, at the closure's first cell instead of the sum's second:
`valid-closure-reg-wf`, carrying an `InlineRep` and no env location or env
validity (an inline env has no cell of its own to be valid at), exactly as
`valid-inl-reg-wf` carries none for an inline payload. The decomposition side
gets `EnvAt` — the `PayloadAt` view one cell earlier — which collapses
`ClosureValidWF`'s `env-loc`/`mEnv`/`env-ptr`/`env-before`/`env-valid` into one
field carrying its own evidence (D153's rule).

WHAT MADE THE VALUE HALF LAND AT ALL is D179. `evalᴰ (curry body) x` is
`returnT (λ b → evalᴰ body (x , b))` and the constructor's index is
`λ arg → evalᴰ body (env , arg)` — the same term with `env := x`, so the place
is definitional. While `ValidAtWF` was indexed on the PURE domain the two sides
named different semantics and no machine reasoning could have bridged them.

`obs-correct-curry` is now discharged in full: the ten-step chain, the halting
obligations, the frontier, both cells, the result pointer and all three input
residences. One named residual remains, `curry-mem-pres` — the same
memory-preservation invariant `inl`/`inr` each name, consumed only by the
`in-loc` residence, and all three are instances of one generalisation (a
heap-allocating straight-line run preserves everything the caller can name)
that is still unwritten.

## D182 — ONE INVARIANT, NOT THREE: the ten-step memory-preservation lemma (2026-09-12)

`inl`, `inr` and `curry` each carried a postulate — `inl-mem-pres`,
`inr-mem-pres`, `curry-mem-pres` — saying that their run leaves every location
the caller can name unchanged. They were three statements of ONE invariant
about ONE shape: the same ten-instruction heap build, differing only in rows 6
and 8 (a tag literal vs an env load; a payload load vs a code address), none of
which touches memory.

`TenStepPres.mem-pres` proves it once, abstracted over exactly those two rows,
and each clause instantiates it. All three postulates are gone and no new one
replaces them.

**Why it could not reuse `derive-mem-preserved`.** That lemma (ClosureWellFormed)
proves the same statement for traces with NO heap writes (`TraceNoHeapWrites`),
and this run writes the heap twice. What makes those writes invisible to the
caller is not their ABSENCE but their FRESHNESS: they land in a block allocated
during the run, whose `ref-id` is at or above the frontier that bounds every
location the caller can name (`heap-before`). Freshness is a RUNTIME fact — the
target is read from `Input1` — so no static trace predicate can express it, and
a `TraceHeapWritesAbove` in the style of `TraceWritesAbove` would have been
unstatable. It enters as the premise `rdi6`/`rdi8` instead, which is exactly
what each clause already proved for its own cells.

**The three lemmas it is built from** are the generic form of what the clauses
were already doing per-cell:

* `mem-untouched` — an instruction that writes no memory preserves EVERY
  location (the two halves already existed: `exec-abstract-preserves-stack-slot`
  and `heap-untouched`);
* `store-slot-preserves-before` — a stack write at or above the frontier misses
  every `BeforeFrontier` location, by the three-way split;
* `store-ind-preserves-before` / `-suc-` — a heap write into a fresh block does
  the same, with `fresh-heap-≢` doing the ref-id arithmetic and `sucHL-ref`
  carrying the bound to the block's second cell.

Every state in the lemma is written with `flat-step-straight` rather than
`flat-exec-instr`: all ten instructions are non-`ctrl`, so each clause's own
nest IS these states definitionally, while `flat-exec-instr`'s catch-all would
be stuck on the abstract rows 6 and 8 — the same obstacle `StraightStep` exists
to work around.

## D183 — `apply`'s setup is proved; the call is where the missing fact lives (2026-09-12)

`apply` emits sixteen straight-line instructions and then `instr-call-closure`.
The sixteen are the same kind of run D182 generalised — three stack stashes
instead of two, two cells read out of the input pair and the closure, then the
callee's `(env , arg)` pair built on the heap — so `ApplySetupPres.setup-mem-pres`
falls straight out of D182's three lemmas. Row 5 (`instr-save-closure-reg`) is
the one step that is not `flat-step-straight`: `do-save-closure` writes the flat
closure REGISTER, which is `FlatState` and not `LocState`, so it moves no memory
and its preservation is definitional.

**The value↔label link already exists, and it is not the gap.** `callView`
(Flat) enumerates the call once: it either halts or ENTERS at
`find-thunk prog ℓ ≡ just j`, where `ℓ` is read from the closure's SECOND CELL
(`heapMem (floc fs) (sucHL hl)`), and the closure register it dereferences was
set at row 5 from `Input1`. `valid-closure-wf` says exactly what that cell
holds — `SV-Code body-label` — and its index says what the closure MEANS —
`λ arg → evalᴰ body (env , arg)`. So the witness ties the label to the body.

**What is missing is the block table.** Nothing says the block `find-thunk`
finds at `body-label` implements `body`. That is a fact about the PROGRAM, and
D170 deliberately removed the value's ability to carry it (`BodyCorrect` was
the cycle that forced `program-bound` through the whole apex). So `apply` needs
it as a named premise of the shape

```agda
CalleeFaithful prog =
  ∀ {E A B} (body : IR (E * A) B) (env : ⟦ E ⟧) (ℓ : LabelId) {m alloc cloc st}
  → ValidAtWF m alloc {A ⇛ B} (λ arg → evalᴰ body (env , arg)) cloc st
  → readLoc st (sucLoc cloc) ≡ just (SV-Code ℓ)
  → ∃[ j ] ∃[ l ] (find-thunk prog ℓ ≡ just j × SpanAt prog j (emitted 0 l body))
```

— "every closure validly resident in a state names a label whose block
implements its body". It is an invariant the machine maintains (`curry` is its
only producer, and D181's discharge is where it would be established), not a
theorem about `ValidAtWF` as it stands. Naming it is what turns
`obs-correct-apply` from a whole-clause axiom into a proof against one premise;
the alternative — putting a program index on the closure witness — would
re-create exactly the dependency D170 removed.

## D184 — THE CLOSURE WITNESS IS `Heap`-MODED; polymorphism there was refutable (2026-09-12)

`valid-closure-wf`'s mode index carried this note: "`m` stays polymorphic
because `valid-closure-wf` is also consumed at locations a caller supplies".
Writing `apply` showed that permission is not merely unused — it is FALSE.

`do-call` dispatches on the closure register's shape (`callView`, Flat):

```
go-sv (SV-Ptr (AtDynamic hl)) … = -- read the code cell, find-thunk, ENTER
go-sv (SV-Ptr (AtStack _ _))  … = cp-halt
```

So a `Stack`-resident closure HALTS the machine, while its denotation runs the
body and may emit. `obs-correct-apply` would be false — not unproved — for any
witness the polymorphic index permitted. And no such closure is ever built:
0.86 stage G left ONE lowering for `curry` and it allocates on the heap
(D181's discharge produces `Heap` and nothing else can).

So both closure constructors now conclude at `Heap`, and their
`LocMatchesMode Heap closure-loc` premise forces `AtDynamic` — which is exactly
the shape the call needs to enter. The change costs nothing downstream: every
consumer is either mode-polymorphic (the transport lemmas, which simply get a
refined index) or already at `Heap`.

This is D181's finding in the opposite direction. There the witness was too
NARROW and excluded a state the machine does produce (a unit environment);
here it was too WIDE and admitted one the machine cannot handle. Both were
found the same way — by writing the first real producer and the first real
consumer of a witness that had neither.

## D185 — `apply`'s seventeen obligations, discharged (2026-09-12)

`ApplySetupPres.Obligations` proves everything the setup's run needs, from the
premises the input's `ValidAtWF` supplies once decomposed: the input pair's two
cells, the closure's two cells, and the `BeforeFrontier` of each.

* the six conditional rows' `InstrWF` — the three indirect loads (rows 1, 3, 6)
  and the three slot loads (rows 11, 13, 15);
* the three STASHES read back — the argument (row 2 → 13), the environment
  (row 7 → 11), the new pair's pointer (row 9 → 15). Each survives the rows
  between: the other stack writes target HIGHER slots, the heap writes are a
  different kind of location, and the rest touch no memory;
* `Input1` at the two indirect stores — the fresh pair, put there by row 10 and
  surviving the slot loads (which write `Output`) and the first store;
* the sixteen `halted ≡ false` witnesses.

The environment cell is taken as a STORED VALUE, not a pointer. D181 made it
either — a pointer for a boxed env, the value itself for a register literal or
`Unit` — and `load-indirect` at row 6 reads the cell either way, so nothing in
the run needs to know which. That is the first place D181's split pays for
itself outside `curry`.

The declarations are ordered by DEPENDENCY rather than by row: the fresh pair's
pointer is what the two indirect stores aim at, so `rdi12'` has to be
established before any read that travels across them.

What is left for `obs-correct-apply` is the callee: the `FlatSteps` chain (the
fetches come from the clause's `span`, not from this module), the call step,
the block's own run relocated by `link-block-steps` (D168), the `c-ret`, and
the result place. All of it is gated on the one fact D183 named.

## D186 — UNUSED NUMBER (2026-09-12)

**Note**: back-filled 2026-10-09 (plan 0.113 E).

No decision was ever recorded under D186. `git grep D186` finds it only in plan 0.113's own
to-do list, and `git log --all --grep D186` / `-S D186` find no commit that uses it: the series
went from D185 (`apply`'s seventeen obligations, e926ae1c0) straight to D187 (a compound's cell
holds a pointer or the component, c0dae6203), both 2026-09-12. The number is skipped, not lost;
this placeholder exists so that a gap in the sequence is not mistaken for a missing entry.

---

## D187 — A COMPOUND'S CELL HOLDS A POINTER **OR** THE COMPONENT (2026-09-12)

`valid-pair-wf` demanded `SV-Ptr` in both cells. `apply` is where that became
REFUTABLE rather than merely incomplete: it copies the closure's environment
cell into the callee's argument pair, and D181 established that cell is a
pointer only for a BOXED environment — `main`'s is `Unit`, so the callee's
argument pair was unwitnessable on the main path.

That is the third instance of one defect class. D181: the closure witness too
NARROW, excluding a state the machine produces. D184: too WIDE, admitting one
it cannot handle. Here: too narrow again, and for D181's exact reason — the
emitter does not box. Every compound build copies whatever the source cell
held, so a component that arrived as a register literal lands in the cell as
itself.

**`CellAt`** is the fix, mutual with `ValidAtWF` (as `PayloadAt`/`EnvAt` are
views beside it): `cell-ptr` carries the pointer, the component's frontier and
its validity; `cell-inline` carries an `InlineRep` and the read equation, and
NOTHING else — an inline component has no cell of its own to be valid at.
`valid-pair-wf` takes two of them, which covers both cells independently where
splitting the constructor would have needed four combinations.

**What it reached.** The split propagated exactly as far as the assumption had:

* `ShapeAt` gets `CellShapeAt`, forward-declared so the two are mutual, and
  `cell→shape`/`cell-uw` mirror `valid→shape`/`shape-uw`.
* `readTyped` (SMCore) followed pointers unconditionally, so it returned
  `nothing` for precisely the pairs the old witness could not describe. It now
  dispatches per cell (`readTyped-cell`), reusing `readReg-typed` for the
  inline case — the same three shapes and the same answers the register-
  resident path already had. Enumerated rather than catch-all: under
  `--exact-split` a `StoredValue` catch-all is not preserved as a definitional
  equality, and the adequacy proof reduces through exactly this dispatch.
* `obs-correct-fst`/`-snd` gain the residence split, and it is the natural one:
  `load-indirect` reads the cell whatever it holds, so a POINTER cell still
  places the result in memory (`at-loc`) while an INLINE one lands the
  component in `Output` as a literal (`at-reg`) — stage F's own shape, arriving
  here only because the witness can finally describe it.

The eight `ValidAtWF` transport lemmas each carry one local cell-transporter
applied twice, so the recursion stays structural and `cell-inline` simply has
no sub-derivation to recurse into.

### D188 — `apply`'s remaining shape, derived (2026-09-12)

The pair split (D187) removed the blocker, and going top-down from
`obs-correct-apply`'s record derived the rest of the design. Recording it so
the next pass does not re-derive it:

**The premise.** `IRObsCorrectF` gains `CalleeRuns prog` beside
`AllSlotStable prog` — the only premise about the whole image rather than the
fragment. Conditioned on the CLOSURE WITNESS, so the body and the label are the
same ones the witness names:

```agda
CalleeRuns prog =
  ∀ {E A B} (body : IR (E * A) B) (env : ⟦ E ⟧) (ℓ : LabelId) {m alloc' cloc st}
  → ValidAtWF m alloc' {A ⇛ B} (λ arg → evalᴰ body (env , arg)) cloc st
  → readLoc st (sucLoc cloc) ≡ just (SV-Code ℓ)
  → ∃[ j ] (find-thunk prog ℓ ≡ just j
      × (∀ fs pre-alloc envArg ret-pc k mIn'
         → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ []
         → falloc fs ≡ enter-call pre-alloc
         → InputAt mIn' pre-alloc envArg (floc fs)
         → CalleeRun prog fs ret-pc body envArg k))
```

Three things about that shape were derived, not chosen:

1. **`CalleeRun` is stated at the POST-CALL STATE, not as the body's own
   `MachineRefinesObsF`.** That one starts from an `entry-flat`, whose `fret`
   is `[]`, while the call leaves one pending return address — and `Shifted`
   relates only stacks of the SAME LENGTH, so nothing bridges them. There is no
   `fret`-weakening lemma anywhere, and writing one needs a "balanced return
   stack" invariant (a `c-ret` on an empty `fret` HALTS, so a run that would
   underflow behaves differently under a deeper stack). Stating the obligation
   where the machine actually is avoids inventing that.
2. **The argument's residence is at the CALLER's frontier**, with the frame
   entry named separately (`falloc fs ≡ enter-call pre-alloc`). `enter-call`
   SHIFTS the frame, so a caller-resident component becomes an ancestor
   afterwards; that transfer needs `StackAncestorSource` payloads and belongs
   with the callee's proof, not at every call site.
3. **`ClosureValidWF` needs `loc-mode` back.** D181 dropped it; `apply` needs
   it, because `LocMatchesMode Heap` is what forces `AtDynamic` — the shape
   `do-call` enters on (D184).

**What remains** is the assembly: the 17-step `FlatSteps` chain, `callView`
with the label match, the callee's input witness (now constructible — it is
`valid-pair-wf` over two `CellAt`s, one from the closure's `EnvAt` and one from
the caller's pair cell), and `traces-agree` over the concatenated chain. Four
residence combinations share one assembly, which wants the shared part factored
into a module rather than repeated.

## D188 (completed) — `obs-correct-apply` IS A PROOF (2026-09-12)

`apply` was the last whole-clause axiom in its class. It is now discharged
against one named premise, and every mechanical part of it is proved.

**The clause.** Two of the three input residences are refuted outright — a pair
fits no register and is not `Unit`. The third decomposes: the pair's first cell
must be a `cell-ptr` (a closure is never inline: `InlineRep (A ⇛ B)` needs
`FitsInRegI` or `≡ Unit`, both absurd) and must be `AtDynamic` (D184's `Heap`
pin, refuting the `AtStack` case by the witness's own `LocMatchesMode` — which
is also the only shape `do-call` enters on). What is left is the closure, and
`decomposeClosureWF` hands over the body, the environment, the label and the
residence.

**The call is spelled out, not dispatched.** `callView`'s three levels
(`do-call-sv` / `do-call-code` / `do-call-at`) are congruences over three facts
the setup and the witness already give: the closure register holds the pointer
row 3 read out of the input pair (`ASP.closure-reg`), the cell it points at
holds the label (`ASP.code-cell`), and the premise resolves that label
(`find-thunk`). No branch of the dispatch has to be refuted separately.

**D187 is what makes the callee's input constructible.** The callee's argument
is `valid-pair-wf` over two `CellAt`s — one rebuilt from the closure's `EnvAt`,
one from the caller's own pair cell — and each is a pointer or inline
independently. Under the old pointer-only witness this step was impossible for
a `Unit` environment, which is `main`'s.

**What is assumed** is `callee-runs` (FlatFromObs), and it splits into a
provable half and a real one: "every block of the unit IS `emitted 0 l body`
for the body its label was minted for" is true by construction of the emitter
and provable by induction over `ir-to-trace'`; that the closure a RUNTIME state
holds was built by one of those `curry`s is a reachability invariant — true
(the entry heap is empty) but needing an induction over runs that nothing here
has. That is the honest content of the axiom.

Net: one whole-clause axiom replaced by one program-level invariant, with the
seventeen-instruction setup, its memory preservation, the label resolution, the
callee's input witness and the trace concatenation all proved.

## D189 — A ν IS A SUSPENSION, AND THE OLD `Out` PROOF WAS VACUOUS (2026-09-12)

**The defect.** D180 deleted `valid-ν-wf` because a Kleisli ν has no available
layer — correct. What was not checked is the postulates and proofs whose
*codomain* is a ν. With no ν constructor left in `ValidAtWF`, the lemma
`ν-not-resident : ValidAtWF m alloc {ν-type F} x loc s → ⊥` became *provable*,
and `obs-correct-Out` was discharged by applying it. The ⊥-probe

```agda
refute : ResultPlace (ν-type F) m a ca v st → ⊥
refute (at-loc loc v _ _ _ _) = ν-not-resident v
refute (at-reg () _)
```

compiled. `Out`'s correctness was therefore a theorem about the empty case, and
what made the case empty was the *emitter's own silence*: `ir-to-trace'` mapped
`Ana` and `in-ν` to `[]`, so the machine could not build a ν to feed it. A
proof that holds only because the compiler does not implement the feature is
not a proof of the compiler.

**The decision: implement it, do not delete it.** The alternative on the table
was removing `Ana`/`in-ν` from the IR. Rejected: `ν` is Once's codata — the
top-level event loop is an unfold — and the absence of an emitter is a gap to
close, not a language change to make.

**The representation.** A ν is a *suspension*: two heap cells, the seed in cell
0 and the coalgebra's code address in cell 1.

```agda
valid-ν-susp-wf : LocMatchesMode Heap ν-loc
                → CellAt alloc A seed ν-loc s
                → readLoc s (sucLoc ν-loc) ≡ just (SV-Code coalg-label)
                → BeforeFrontier alloc (sucLoc ν-loc)
                → ValidAtWF Heap alloc {ν-type F}
                    (TM.valueT (evalᴰ (Ana wf coalg) seed) 0) ν-loc s
```

This is `valid-closure-wf` with the env replaced by the seed and the body by
the coalgebra, and that is the whole point: **a closure and a suspension are
the same machine object** — a value plus the code that consumes it. `Out`
forces a layer by calling cell 1 on cell 0, which is what `apply` does to a
closure. The seed's cell is a D187 `CellAt`, so a pointer seed, a
register-sized seed and a `Unit` seed are one constructor, where `curry` still
needs `valid-closure-wf`/`valid-closure-reg-wf` to say the same thing twice.

**`as-sum` no longer unfolds a ν.** A branch-tag site may not read a ν
directly: its cell holds the seed, not a tag. It must be `Out`-ed first, and
the result of `Out` carries the `⟦ F ⟧TI (ν-type F)` expectation, which is
where the sum becomes readable. `ShapeAt`'s `shape-ν` (which mirrored the
deleted `valid-ν-wf` and claimed a resident layer) is replaced by
`shape-ν-susp`, and `site-branch-tag`'s ν clause is now refuted by `ok`.

**What this costs.** `obs-correct-Out` returns to the postulate block. That is
a *regression in count and an improvement in honesty*: it was a theorem about
nothing, and it is now a named obligation against a machine that actually
forces. It is `obs-correct-apply`'s argument (D188) applied to the coalgebra's
block, which is why the emitter lowers the force as a call rather than
inventing a second calling convention.

**The recurrence guard.** `ana` exists in `Once.Surface.Syntax` and elaborates
(`curry (Ana … ∘ snd)`), but no *concrete syntax* produces it — `RAna` is
marked internal and the parser never emits it. That is the same gap `cata` has,
and it is why a broken ν path could sit unnoticed: no exit test could reach it.
Surface syntax for `ana`/`cata` plus an exit test that runs an unfold is the
follow-on, and it is what actually prevents a repeat.

## D190 — THE TWO-CELL HEAP BUILD, FACTORED (2026-09-12)

`curry` and `Ana` emit the *same ten instructions* — `mov-to-output`,
`store-at-slot n`, `instr-alloc-heap 2`, `store-at-slot (suc n)`,
`mov-to-input`, `load-from-slot n`, `store-indirect`, `instr-load-code-addr`,
`store-indirect-suc`, `load-from-slot (suc n)` — because they build the same
object. `TwoCellBuild` is that build, once: the ten states, the `FlatSteps`
run, the ten `halted ≡ false` obligations, the object's location and frontier
facts, the two cell read-backs, the result pointer, and `valid-transport` (the
input's own validity carried across the ten steps via D182's `TenStepPres`).

Each clause supplies only its `ResultPlace` — `curry` picks
`valid-closure-wf`/`valid-closure-reg-wf` by residence, `Ana` picks
`valid-ν-susp-wf` over one `CellAt`. `obs-correct-Ana` is consequently about
fifty lines rather than three hundred, and a fix to the build is a fix to both.

`emitted n l (curry body)` and `emitted n l (Ana wf coalg)` both reduce to
`two-cell-trace n l`, so each clause's `SpanAt` premise passes into the module
unchanged — no relocation lemma, in keeping with D158.

## D191 — `Nu` IS SURFACE SYNTAX, AND `NoNu` IS RETRACTED (2026-09-12)

D189 found a vacuous proof on the ν path and traced it to the emitter. This
entry is about why nothing caught it: **a ν could not be written down.** The
type grammar had `Mu <functorSum>` and no `Nu`, so no annotation could mention
a final coalgebra, so no source program could contain an `ana`, so no exit test
could reach the ν codegen at all. The defect was not merely unproved; it was
unreachable, which is worse, because unreachable code cannot fail a test.

**What was added** is the `Mu` mirror, everywhere `Mu` appears: `GNu` in the
grammar AST, `Nu ( … )` in the printer, `pa-nu` in the parse relation, the
`name ≟ "Nu"` clause in the WF parser, the completeness clause in
`ParserBridge`, both directions of `Convert` and both round-trip proofs.
Twelve sites, one to three lines each — the footprint `Mu` already had.

**What was retracted** is `NoNu`, and it deserves naming. It was a proven
cross-stage invariant — "`parseType` only produces types satisfying `NoNu`",
i.e. the parser never emits a ν — and its stated purpose was that "downstream
stages (elaboration, IR lowering) can rely on the absence of `ν-type` in parser
output". That reliance is exactly what has to go: the ν half of the language is
not a degenerate case to be excluded, it is Once's codata, and the top-level
event loop is an unfold.

The predicate itself survives as `Expressible` / `ExpressibleF`, because its
CONTENT was always the useful part — a structural characterisation of when
`typeToGType` succeeds, independent of the partial conversion function. It
gains `ex-nu` and loses a name that no longer described it. (It already
allowed μ, so the name had been half-wrong since `GMu` landed.) What is still
inexpressible is an effect arrow at a `Zero` or `One` multiplicity, which the
grammar has no token for — that, not ν, is what the predicate now rules out.

`Nu` is a prerequisite, not the whole guard: the guard is an exit test that
runs an unfold, and that needs the `ana` term as well (D192).

## D192 (PARKED, one site short) — surface `ana`, and the ν row of `RelV`

**Status (2026-10-09)**: CLOSED by D193 (the effectful ν gets its bisimulation); the PARKED in the title is historical.

D191 made a ν type writable. This entry is the term: `ana coalg` in check mode
at `A -> Nu F`. **Nine of its ten sites are done and green; it is parked on the
tenth, and the tenth is a finding rather than a chore.** The work is kept as
`docs/compiler/D192-ana-surface.patch`.

**`ana` needs no syntax of its own.** `"ana"` was already in `genWords`, so the
resolver has always produced `RApp (RResolved (gen "ana")) coalg`; `cata` and
`In` are already surface-reachable the same way, with the functor read from the
EXPECTED type. So the term is `cata`'s mirror at every site, and each one went
green first or second try:

| site | what |
|---|---|
| `Judgment` | `t-ana-check` — `t-cata-check` with the arrow reversed |
| `Classify` | `ahv-ana`, `pba-ana`, the absurd row |
| `Elaborate` | `checkAna` / `checkAnaGo` + two dispatch rows |
| `ElaborateProofs` | `checkAnaGo-J`, `checkAnaGoV-J`, `checkAnaGo-just-success` |
| `Completeness` | `check-complete`, `subsume-complete` |
| `Realize` | one line — `Surface.ana` already existed and already elaborated |
| `Meaning` | `ana-sem`, the dual of `cata-sem` |
| `RealizeAgrees` | `agree-checkAnaGo` |

It needs TWO bridges where the cata needs five, because `checkAna` is
grade-generic: the coalgebra's grade IS the unfold's, and there is no morphism
witness to recover, so no eff-then-pure fallback to follow.

**The blocker: `RelV (ν-type F) x y = x ≡ y`.** `bridge-c` relates the direct
meaning to `⟦_⟧ˢ ∘ realize`. At the ana it must produce EQUALITY of two
`anaFᵈ` values built from two merely RELATED coalgebras. That is not provable,
and the reason is structural: `RelV`'s ν row treats codata as first-order,
which is the SAME assumption D179/D180 removed from `ValidAtWF` and D189
removed from `obs-correct-Out`. This is the fourth instance of one defect
class — *a ν modelled as if its layers were already available*.

`ValueDomain` is explicit that the denotational ν has no bisimulation: "No
bisimulation and no axiom, because `anaᵈ` is indexed by the functor" — true of
`anaᵈ-erase`, which only ever needs `cong` over a coalgebra EQUALITY, and
false of what a relational bridge needs.

**What discharges it**, and it is a known shape: the semantic ν already has
`_∼S_`, `unfoldS-∼` and the coalgebraic-extensionality axiom `bisimS-to-eq`
(Plan 0.47 step 3, "provable in Cubical Agda"). The denotational ν needs the
same three: a `_∼ᵈ_` on `νᵈ`, a coinductive "related coalgebras unfold to
bisimilar values", and `bisimᵈ-to-eq`. Then `RelV (ν-type F)` becomes
bisimilarity — which is what observational relatedness at codata SHOULD have
been — and `bridge-c`'s ana clause follows. One new axiom, of a class the
project already sanctions, replacing a row that is currently too strong to
satisfy and too weak to be right.

Parked rather than forced: postulating `ana-bridge` itself would assert that
related coalgebras give propositionally EQUAL coinductive values, which is not
merely unproven but probably false — exactly the kind of postulate D189 was
about removing.

## D193 — THE EFFECTFUL ν GETS ITS BISIMULATION; D192 CLOSES (2026-09-12)

D192 was parked one site short, on `bridge-c`'s `ana` clause. This is that
site, and the fix is the one the parking note predicted.

**The obstacle, restated.** `RelV (ν-type F) x y = x ≡ y`. `bridge-c` must
produce PROPOSITIONAL EQUALITY of two `anaFᵈ` values built from coalgebras the
logical relation merely RELATES. Relatedness is strictly weaker than equality,
so no structural argument closes it. `CataBridge` never meets this: a fold runs
over a value both sides SHARE (`RelV (μ-type F)` is also `≡`, so both folds
traverse the same `μS`), and only the per-layer step differs. An unfold shares
nothing — it BUILDS its result.

**The missing principle is coalgebraic extensionality**, and the pure side has
had it since plan 0.47: `νS` carries `_∼S_`, `unfoldS-∼` and the `bisimS-to-eq`
postulate. The effectful `νᵈ` carried none of them, and `ValueDomain` says why:
"No bisimulation and no axiom, because `anaᵈ` is indexed by the SFunctor". That
is TRUE of erasure — `anaᵈ-erase` only ever needs `cong` over a coalgebra
EQUALITY — and false of every relational statement about a ν.

**`Once.Denotation.ValueDomainLaws`** gives `νᵈ` the same three, split from the
kernel for the same reason `Semantics.Functor.Laws` is split from
`Semantics.Functor`: so a module that only needs `anaᵈ` does not import an
axiom. `_∼ᵈ_` differs from `_∼S_` in exactly the way `νᵈ` differs from `νS` —
the layer is a COMPUTATION, so bisimilarity asks for equal TRACES as well as
related layers, at every budget. Without the trace field it would relate values
that emit differently and `RelT`'s first component could not be recovered.

`anaᵈ-∼` (related seeds unfold to bisimilar values) is the coinductive core and
is mutual with `mapAnaᵈ-∼` exactly as `anaᵈ` is with `mapAnaᵈ`; guardedness
goes through because the corecursive call sits under a structural recursion on
the shape functor.

**`Once.Adequacy.AnaBridge`** is then short: `base-eq` (the converse of
`CataBridge.base-refl` — at a `K`-position `⟦ SK _ ⟧SF-rel` wants equality of
the two constants), `in-rel` (the mirror of `z-rel`: `z-rel` brings a
functor-lifted relation OUT of a layer the fold produced, `in-rel` pushes
`RelV (⟦ G ⟧T A)` INTO the layer the unfold consumes), and `ana-bridge`
itself — one `anaᵈ-rel-eq`, because both `fmapT`s are transparent on trace and
value.

**One new axiom, and it is not a new kind.** `bisimᵈ-to-eq` is `bisimS-to-eq`
at the effectful ν: standard coalgebra, provable in Cubical Agda. The
alternative considered and rejected was postulating `ana-bridge` directly,
which would assert that related coalgebras give propositionally EQUAL
coinductive values — not merely unproven but probably false, and exactly the
kind of postulate D189 spent this branch removing.

**What this closes.** Surface `ana` is landed end to end: `ana coalg` parses
(no new syntax — `"ana"` was already a `genWord`), checks against `A -> Nu F`
with `F` read from the annotation D191 made writable, elaborates to
`curry (Ana wfF … ∘ snd)`, and compiles to D189's two-cell suspension. The ν
half of the language is reachable from source for the first time.

## D194 (PARKED, one lemma short) — surface `Out`, the ν's eliminator

**Status (2026-10-09)**: CLOSED by D197 (`Out` lands). The parked patch `docs/compiler/D194-surface-out.patch` is deleted (plan 0.113 E); it is in git history.

D193 made `ana` writable end to end. This entry is what it exposed: **a ν can
now be BUILT but not OBSERVED.** `"Out"` has been a reserved `genWord` all
along, but nothing elaborated it — no `ahv-Out`, no `Surface.out`. So an exit
test still cannot read a layer back, which is the whole point of the guard.

Nine of ten sites are done and green; the work is kept as
`docs/compiler/D194-surface-out.patch`.

**`Out` is INFER, not check, and that is forced.** A check rule would have to
recover `F` by inverting `⟦ F ⟧T (ν-type F) ≡ T`, which is not syntactically
possible. Inferring the argument reads `ν-type F` off its type, where `F` is
manifest. That single choice is why `Out` costs more than `ana` did: `ana`
rides `⊢ᶜ`, where every site had a `cata` mirror, while `Out` rides `⊢ᵢ`, where
it has none.

**Three techniques the `⊢ᵢ` side forced**, each an instance of a known trap:

* *Generic codomain + eq proof.* Stated with the application `⟦ F ⟧T (ν-type
  F)` in the conclusion, every downstream function that splits on the
  conclusion's SHAPE got a stuck unification — `iFromInferEff` asks whether the
  layer is a pure arrow, and it CAN be (at `F = K (A ⇒ B)`), so the case is
  neither refutable nor solvable. The rule now concludes at a free `C` pinned
  by `⟦ F ⟧T (ν-type F) ≡ C`, and each consumer transports.
* *J-style bridge.* `inferOutGo-J`, because a `rewrite` moving from the
  elaborator's `(wellFormedF? F, refl)` to the witness's `(just wfF, eqW)`
  would have to abstract a term its own equation mentions. Same shape as
  `checkCataGo-J`, and it fails identically whether the decision arrives as a
  parameter or through the `inspectWellFormedF` view.
* *Applied IH, not general IH.* In `agree-RApp`, inside the caller's `with` the
  general IH's type no longer mentions `E.inferElabV ctx arg`, so it cannot be
  passed to a helper. The helper takes the argument's agreement ALREADY
  APPLIED.

**What remains is one lemma, and its statement is verified** (the `bridge-i`
clause typechecks against it):

```agda
out-app-bridge : RelV (ν-type F) vᴸ vᴿ
               → RelT (⟦ F ⟧T (ν-type F)) (out-sem wfF vᴸ)
                      (liftFn fmt (Out-ir wfF) vᴿ)
```

`RelV` at a ν is `≡`, so this carries NO relational content — both sides force
the same value. It is a pure coherence: the direct meaning's force (`out-sem`,
`fmapT` of `coerce-functor⁻¹-D ∘ coerce-ν-out` over `forceᵈ`) and the IR's
(`evalᴰ (Out wf)`, the same chain at `⌈_⌉`) agree. The proof is the `out`
direction of `AnaErased.coerce-νin-erase-D`, ~100 lines of transport
induction. No μ-side version exists to reuse: `out-μ` is not surface-reachable
either, so nobody has needed it.

Parked rather than committed behind a postulate. `out-app-bridge` is certainly
TRUE — unlike D192's `ana-bridge`, which would have been probably false — but
it is provable with a validated template, and this branch's standard is not to
postulate what the template can discharge.

**Second pass (same day): the lemma is now one step from done.**
`Once.Adequacy.OutErased` is written and carries:

* `Out-ir`, and `evalᴰ-subst-cod` — the CODOMAIN mirror of
  `CataErased.evalᴰ-subst-dom`, which the `In` side never needed because
  `In-ir`'s transport is on the domain.
* `subst-TI-projTrace` / `subst-TI-valueT`, `subst-id-νᵈ`,
  `force-subst-trace` / `force-subst-value` — forcing a transported ν, all
  match-to-refl.
* **`out-trace` — PROVED.** The trace half is not `[]` as `In`'s is (`Out`
  emits whatever forcing emits), so it is an equality between the two sides'
  traces, and it closes through the four transports.
* **`out-value` — PROVED down to one named residual**, `out-coh`.

`out-coh` is the whole remaining content:

```agda
subst id (cohᴰ (⟦ F ⟧T (ν-type F)))
  (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute F (ν-type F)))
    (valueT (evalᴰ fmt (IR.Out (wf-⌊⌋ wfF)) (subst id (sym (cohᴰ (ν-type F))) v)) n))
≡ coerce-functor⁻¹-D F (ν-type F) (coerce-ν-out wfF _ (valueT (forceᵈ v) n))
```

— `AnaErased.coerce-νin-erase-D` read backwards. Discharging it needs the
LAYER generalised first: the two sides' layers differ by a `tF-coh` transport,
and the `wf-*` induction needs a layer it can case-split, which
`valueT (forceᵈ v) n` is not. After that it is that lemma's five clauses
inverted. Everything else in the `Out` path is proved.

## D195 — THE FIRST `ana` PROGRAM RUNS, AND IT FOUND D191's GAP (2026-09-13)

`compiler/test/nu-ana-build.once` compiles and exits 42. It is the first source
program in Once's history to mention the ν half of the language.

**It failed on its first run, and the failure is the point.** D191 added `Nu` to
`Once.Parser.Type` — the GROUND-type parser. Def signatures are parsed by a
different one: the generic `TyAlg` parser (`Once.Parser.Generic`), instantiated
at `PolyType`. So `Nu` was writable in exactly the positions no program uses,
and `mkNu : Int -> Nu (K Int)` was a parse error.

No proof could have caught it. Both parsers were internally consistent and both
clusters were green; the ground parser's `pa-nu` was threaded through its
relation, its WF parser, its bridge and both round-trips, and all of that was
true and useless for signatures. Only compiling a program that says `Nu` in a
signature could find it — which is the D189 lesson one level down: *a feature
reachable in the proofs but not from source is not reachable.*

**The fix** adds `Nu` to the generic algebra, which is where it belonged:
`TyAlg.aNu`, the `pa-nu` relation constructor, its `atomShrink` measure, the
executable parser clause, soundness, completeness, and the `PolyType` instance
(`aNu = Pν-type`, `extraMiss-Nu`). Seven sites, each a `Mu` mirror.

**An asymmetry worth naming.** The same keyword added to
`Once.Parser.PolyType`'s own `parsePolyAtomImpl` produced ZERO proof
obligations — that clause is not covered by a soundness relation — while adding
it to the generic algebra produced five. Def signatures are parsed by a
verified component; that other impl is not, and a keyword can enter it silently.
Worth a follow-up: either it is dead and should go, or it is live and owes a
relation.

**What the test covers, measured rather than assumed.** With `mkNu` unused the
emitted `.text` is BYTE-IDENTICAL to a program without it — the def is elided,
and the test would have exercised only the frontend. Reaching the ν from `main`
(through `terminal`, the most that is possible until `Out` exists) moves `.text`
from `0x81b` to `0xd2b`. So D189's ten-instruction suspension build and its
coalgebra block are emitted, assembled, linked and RUN. What is still not
exercised is FORCING; `nu-ana-force.once` is written and waits on D194.

Exit tests: 63 passed, 0 failed, 1 skipped.

## D196 — THE DEAD POLY PARSER, AND WHY THE ISLAND TEST MISSED IT (2026-09-13)

D195 found that `Nu` had to go into the GENERIC parser, not the ground one,
because def signatures are parsed there. This is the follow-up it exposed:
`Once.Parser.PolyType` held a SECOND, UNVERIFIED implementation of the same
grammar — `parsePolyTypeImpl` and ten mutually-recursive helpers under a
termination-check-bypassing pragma, exported as `parsePolyType`. Nothing
consumed it. Deleted, ~200 lines.

**Why it mattered more than its size.** It was the one place a keyword could
enter the frontend without a proof obligation. Adding `Nu` to the generic
algebra cost five (relation constructor, shrink measure, parser clause,
soundness, completeness); adding it here cost zero, and changed nothing,
because the live path is `parsePolyTypeB → parsePolyTypeP` wrapped in
`sound-polyType`. Two implementations of one grammar, one of them unconstrained,
is drift waiting to happen.

**Why the no-islands check did not catch it, which is the transferable part.**
That check is "delete it and the build must break". A `… using (f) public`
re-export GUARANTEES the build breaks — the aggregator's `using` list stops
resolving — so dead code held up by a re-export PASSES the island test while
having zero real consumers. `parsePolyType` was wired to the build by exactly
one line in `Once/Parser.agda` and used by nothing. MERGE.md now carries the
companion check: for each `public` re-export, confirm a consumer other than the
re-export line (the aggregator's own body counts — `isUpperWord` is re-exported
AND used in `hasUpperTVar`, and is fine).

**Coverage was verified before deleting.** Both parsers accepted the same
keyword set (Unit/Void/Int/Float/Buffer/String/Eff/IO/Mu/Nu/K/Id); the quantity
arrows are handled generically by `arrowDir`; the `TLBrace` clause was a
rejection, not a feature. `Mu` did NOT need porting — it has been in the
generic parser all along, which is what `Nu` was mirrored against.

**And `lint-imports` paid for itself.** Its 8 flagged modules were one root
cause — `IRObsCorrectFlat` re-reported through its importers — with four stale
directives, three PRE-EXISTING: `valid-ν-wf` in a `using` list (D180 deleted
the constructor and left the import), the whole `do-call-sv`/`-code`/`-at`/
`enter-call` family imported from `SMCore` which exports none of them (they
come from `Flat`; the names resolved elsewhere so nothing ever broke), a
duplicated `SV-Code`, and `nhw-store-indirect`/`-suc` from `SMPrimitives`
which has neither. All fixed; the full tree lint is now clean.

## D197 — `Out` LANDS, THE ν LOOP CLOSES, AND THE GUARD FINDS A HOLE (2026-09-13)

D194's last obligation is discharged. `νout-erase-D` is PROVED — five clauses,
seven base leaves, no postulate — so `out-app-bridge` is a proof and surface
`Out` is landed. **A ν can now be written, typed, compiled, built and FORCED.**
`Out (mkNu 42)` exits 42, on x86_64, x86_32 and riscv64.

**What made the proof tractable was fixing the STATEMENT, not the proof.** Two
changes: generalise the CARRIER (at `⊕` the sub-functor changes while the
carrier does not, so tying them blocked the recursion outright), and NAME the
`⌈⌉`-side layer map (`out-layer-gen`) so the proof could `cong` over the LAYER
instead of the whole computation. After those, `wf-Id` fell to subst
cancellation, `⊕`/`⊗` to five-step push chains, and five of seven base leaves
to `refl`. Three earlier attempts failed because I was writing transport
chains against a statement the induction could not consume.

**The guard found a hole on its first live run.** Written point-free —

```once
force : Nu (K Int) -> Int
force = Out
```

— this TYPECHECKS AND EMITS NOTHING; the link then fails on an undefined
`once_5force`. `t-Out-app-infer` is an INFER rule about
`RApp (RResolved (gen "Out")) v`; there is no rule for a bare `Out`, so it
should be REJECTED. Bare point-free defs DO work for the check-mode generators
(`identity = id`), so this is specific to the infer-mode-only heads. Same
defect class as the one this whole branch started from: something accepted
that has no meaning. Left as the next task rather than patched here, because
the fix is a frontend rule change and wants its own entry.

**Test coverage, measured.** `nu-ana-build` exercises the ten-instruction
two-cell build and the coalgebra block; `nu-ana-force` exercises the CALL
through the ν's second cell — the half `obs-correct-Out` still assumes. Both
are in `Layer5Spec` (the μ file's codata dual) so `exitCases` runs them on all
three arches; `tests/run-exit-tests.sh` is x86_64 only, and until now the ν
codegen had never executed anywhere else.

Exit tests 64 passed / 0 failed / 0 SKIPPED. `cabal test` 743 passed (737 + the
six new: two programs × three arches). `make certified` green.

## D198 — `CalleeRun` IS INDEXED BY ANY IR; THE ν's CODE CELL GETS ITS OWN PREMISE, `CoalgRuns` (2026-09-13)

**Relates**: D188 (`CalleeRun`, `apply`'s callee premise), D197 (`Out` lands), D199 (landed
in the same commit, 1393d1e72, which amends this premise), D273 (the seed becomes `(e , a)`).
**Note**: back-filled 2026-10-09 (plan 0.113 E). The number was cited in D199 and in
`IRObsCorrect/Interface.agda` but never written.

### Context
`Out` forces a ν by calling the code cell its suspension holds. `apply` already had a premise
for "the called block runs" (`CalleeRuns` / the record `CalleeRun`, D188), but the record was
indexed by a closure BODY `IR (E * A) B` and its packed argument.

### Decision
Two changes, both stated in `Interface.agda`:

> D198: indexed by ANY `IR A B` and any input, not by a body-of-a-closure. Nothing in the
> fields ever used the `E * A` shape — they mention only `evalᴰ ir inp` and `B` — and the ν
> force needs the same record at a COALGEBRA `IR A (⟦F⟧TI A)` called on a bare seed. `apply`
> instantiates this at `E * A` and is otherwise unchanged.

> D198: the ν analogue of `CalleeRuns`, and a SIBLING rather than an instance because the two
> block kinds are called differently BY CONSTRUCTION: `apply` packs an `(env , arg)` pair on
> the heap and points `Input1` at it, while `Out` puts the SEED in `Input1` directly. That is
> what makes a ν's code cell a coalgebra rather than a closure body, so one premise cannot
> serve both.

`CoalgRuns prog`: for a valid ν whose code cell holds label `ℓ`, `find-thunk prog ℓ` resolves,
and running from there with the seed in `Input1` is a `CalleeRun`.

### Consequences
- D199 (same commit) re-indexed `CalleeRun` by the COMPUTATION (`B` explicit) and changed what
  `CoalgRuns` says the block computes: the forced layer `evalᴰ (Out wf) ν`, not `coalg`, since
  the block now ends with the re-suspension pass.
- `callee-runs` became `block-runs : BlockRuns`, covering both block kinds (later D213/D218).

---

## D199 — `Out` DOES NOT RE-SUSPEND, AND `obs-correct-Out` IS FALSE (2026-09-13)

I was about to write `obs-correct-Out`'s proof body. Before starting I checked
the one fact the proof would have had to establish, and it is not true.

`forceᵈ` is defined per-introduction-form:

    forceᵈ (anaᵈ H coalg a) = λ k → ( projTrace (coalg a) k
                                    , mapAnaᵈ H H coalg (valueT (coalg a) k) )
    mapAnaᵈ H SId coalg a   = anaᵈ H coalg a

Every `SId` position in the forced layer is a FRESH SUSPENSION. The machine's
`Out` is four instructions — save the ν pointer, load cell 0, move it to the
input, call cell 1 — and hands back whatever the coalgebra returned. The
coalgebra returns a layer whose recursive slots hold the raw SEED. So at every
`Id` position the machine has a seed word where the spec has a ν.

At `K Int` there are no `Id` positions, the two values coincide, and both
`nu-ana-build.once` and `nu-ana-force.once` pass. That is why this was
invisible: the entire ν test surface is a functor with no recursive position.

The discriminating program forces twice, through the recursive slot:

    mkS : Int -> Nu (K Int * Id)
    mkS = ana (pair id id)
    main = exit@S (fst (Out (snd (Out (mkS 42)))))

One force (`fst (Out (mkS 42))`) exits 42. Two forces SEGFAULT: the second
`Out` takes the seed word `42` out of the recursive slot and dereferences it as
a suspension pointer.

So `obs-correct-Out` is not "a deferred proof, not a model gap", which is what
its comment claims and what I believed when I wrote it. It is a MODEL GAP, and
the postulate is FALSE for every functor containing `Id` — the third false
axiom this branch has found, and the same defect class as the other two: a ν
modelled as if its layers were already available.

### Where the fix goes, and why not in `Out`

`Out` sees a suspension and cannot tell how it was introduced. `ana`'s layers
must be re-suspended; `in-ν`'s must NOT be, because `forceᵈ (injectν x)` maps
`mapInjectν` over a layer that already holds real νs. A re-suspension pass
inside `Out` would have to distinguish two cases that are the same two cells.

The spec already says where it belongs: forcing behaviour is a property of the
INTRODUCTION FORM, so the pass belongs at the tail of the block each form
emits. `Ana`'s coalgebra block gets it; `in-ν`'s identity stub does not. The
label to store in each new suspension's cell 1 is then statically known — it is
the emitting block's own label, which is exactly `anaᵈ H coalg` at the
recursive position.

`Ana` carries its `WellFormedFI F` witness, so the pass is generated by
structural recursion on that witness: `K` emits nothing, `Id` emits the D190
`TwoCellBuild` ten instructions, `⊗` recurses into both cells of the pair and
writes the results back, `⊕` branches on the tag and recurses. The `⊕` case needs NO fuel: it is a
STRUCTURED branch, `instr-case-on-tag f g`, which reads the tag from `*Input1`
and picks a sub-trace, and whose correspondence already exists for `case` via
`valid-inl-wf`/`valid-inr-wf`'s tag-eq fields. Only loops need fuel; this is
an if.

### What landed

`resuspend-layer` in `IRToTrace`, appended to `Ana`'s coalgebra block:

    resuspend-layer : ℕ → ℕ → LabelId → ∀ {F} → WellFormedFI F
                    → ℕ × ℕ × AbstractTrace

The layer arrives in Output in its cell representation and leaves re-suspended.
`wf-K` emits nothing. `wf-Id` emits `Ana`'s own ten instructions minus the
leading `mov-to-output` (the seed is already in Output), with the code cell
pointing at the block being emitted — self-reference, statically known, which
is exactly `anaᵈ H coalg` at the recursive position. `wf-Prod` walks both cells
of the pair and writes each transformed child back. `wf-Sum` branches.

The sum arm is why the signature carries a LABEL COUNTER. `instr-case-on-tag`
looked like the obvious instruction and is a RETIRED FOSSIL: `EmittableI` sends
it to ⊥, because one flat step must never run a nested trace. So the arm emits
the same `c-branch-tag-zero` / `c-jmp` / `c-label` skeleton `case` does, and
needs fresh labels to do it.

Both block-level obligations were found by the typechecker, not by search, and
both are now proved rather than assumed: `resuspend-stable` (CataIRSlotStable)
and `resuspend-ff` (FrameFreeTrace), each an induction mirroring the pass's own.

### The pass ALLOCATES; it does not mutate

The first version walked the layer and wrote each re-suspended child back into
its parent's cell. That is wrong, and the reason is aliasing: a coalgebra is
free to return a pointer INTO its own seed — `ana id` does, and so does
anything built from `fst`/`snd` — so mutating "the layer" can overwrite the
seed. The seed is still live: it sits in the ν's first cell, and forcing the
SAME ν again would then run the coalgebra on a corrupted value.

`mapAnaᵈ` is a pure functorial map. It builds a new layer; it does not modify
one. So each container case ALLOCATES: `⊗` builds a fresh two-cell pair from
the two transformed children, and `⊕` builds a fresh tag/payload node, taking
the tag from the arm it is in (`instr-load-tag-lit`) rather than copying it,
since each arm already knows which one it is. Nothing the pass runs on is ever
written to, so ownership of the layer never has to be established.

### `obs-correct-Out` IS NOW A PROOF

With the emitter re-suspending, the obligation is true, and it is discharged —
`apply`'s argument with the pair-packing removed. A suspension IS the callee
record (cell 0 the argument, cell 1 the code), so the setup is three rows
instead of sixteen and writes no memory at all; neither `load-indirect` nor
`mov-to-input` touches the allocator DEFINITIONALLY, so `apply`'s
frontier-advance plumbing collapses to a single `validityWF-mem-preserved`.

Three things the proof turned on:

  * the ν's location must be split as `AtDynamic` in the CLAUSE. `LocMatchesMode`
    is a ⊤/⊥ FUNCTION, not a datatype, so the heap-ness witness cannot be
    matched on — and without the split `do-call-sv` never reduces to
    `do-call-code`;
  * `go` must take the ν VALUE as an argument. Matching `valid-ν-susp-wf` has
    to force its own index, and a variable bound by the enclosing clause cannot
    be forced — the match instead tries to solve the constructor's
    `coalg`/`seed` out of an opaque `x` and gets stuck (this surfaced as
    unsolved `_coalg` metas);
  * the two functor witnesses are identified once by `rewrite
    WellFormedFI-irrelevant`, not transported at each use.

### What this does to the proof obligation

`CoalgRuns` (D198) says the ν's block computes `coalg`. That is now FALSE in a
second way: the block computes the coalgebra AND the re-suspension. The premise
has to say it computes `forceᵈ`'s value — `mapAnaᵈ H H coalg (valueT (coalg a))`
— which is what `obs-correct-Out` needs from it anyway. The emitter change makes
the obligation honest; it was the postulate, not the proof, that was wrong.

## D200 — SPLITTING `IRObsCorrectFlat`, AND HOW TO MEASURE IT (2026-09-14)

`IRObsCorrectFlat` was 4358 lines. A genuine recheck — its own `.agdai`
deleted, every dependency cached — costs **728 s and 2.2 GB**. Ten postulates
are still open in it, and `obs-correct-Out` took four compile cycles, so the
remaining work was priced at several hours of pure waiting.

After the split, rechecking one clause part (`Out`) is **14.7 s**. Same
methodology, ~50x.

### Why it was safe to split

`ir-obs-correct` is the only recursive definition in the development. Its two
recursive cases take the induction hypothesis as an ARGUMENT:

    ir-obs-correct (g ∘ f)       = comp-obs-correct (ir-obs-correct g) (ir-obs-correct f)
    ir-obs-correct (Cata wf alg) = cata-correct wf alg (ir-obs-correct alg)

So no clause calls back into the dispatcher, and no clause needs another. The
parts form a STAR over `Interface` (the obligation) and `Machine` (the step
lemmas) — not a chain. A chain would have been nearly worthless: editing the
first part would still recheck everything after it.

`bundle-telescope-for-oom` records a measured case where splitting a file did
NOT help, because the real cost was a 64-parameter module telescope. That is
worth checking before any split like this. It does not apply here: the
telescope is `{FS}` and `program-bound`.

### THE MEASUREMENT TRAP — read this before believing any timing

Agda keys interface reuse on the SOURCE HASH, not mtime. Two consequences, and
both of them produced confidently wrong conclusions during this work:

  * **`touch` does not force a recheck.** A `touch`-then-time run reported
    10 s where the real cost was 728 s.
  * **A run that exits 0 may have checked NOTHING.** Running the committed
    file as a "control to prove the environment is healthy" returned `RC=0` in
    seconds — it had loaded a cached interface. That was taken as evidence the
    environment was fine and the new proof was at fault. It was not.

The check is `grep -c 'Checking' <log>`: 0 means a cached no-op and the run
proves nothing; 1 means the module was really compiled. To force a real
recheck, delete `_build/<ver>/agda/<path>.agdai`.

Separately: a check launched as a background task is killed by the harness
watchdog within seconds regardless of content — it fired identically on the
committed file and on ten trivial `FlatState` definitions. Launched in the
foreground it runs to completion. Nine "out of memory" kills were this, not
memory: agda's real peak here is 2.2 GB with 5 GB free.

### Two Agda facts the split turned on

  * a `public` re-export carries NAMES, not the module — a fully qualified
    `Once.CCC.FrameSemantics.fs-numerics` still needs a bare `import`;
  * the prelude may be re-exported publicly along exactly ONE path. Seven
    parts re-exporting it gives seven routes to `Data.Nat._+_`, which Agda
    rejects as a clashing definition.

## D201 — `RelV` AT A ν IS BISIMILARITY; THE `bisimᵈ-to-eq` AXIOM IS GONE (2026-09-14)

The fourth and last member of the ν defect class, which the residual ledger
named and this branch had not closed:

> Four defects on this branch were one assumption in different clothes — *a ν
> modelled as if its layers were already available*: `valid-ν-wf`,
> `obs-correct-Out`, `as-sum`, and `RelV (ν-type F)` (equality of coinductive
> values).

`RelV (ν-type F) x y = x ≡ y` — the observational relation at a COINDUCTIVE
type was propositional equality. That is what `bisimᵈ-to-eq` existed to serve:
`anaᵈ-∼` proves a bisimulation, coinductively and honestly, and the axiom
converted it into the `≡` the relation demanded.

### The axiom could never have been discharged

Bisimulation-implies-equality is INDEPENDENT of MLTT — provable in Cubical
Agda, not in plain Agda. So "discharge it" was never an option; the only
options were to assume it or to stop needing it. Stating the relation honestly
is the second.

    RelV (ν-type F)  x y = x ∼ᵈ y

`bisimᵈ-to-eq` and `anaᵈ-rel-eq` are DELETED, and `Once.Denotation.
ValueDomainLaws` is now axiom-free.

### What the change cost: two sites

Measured by spiking the definition and following the red — the blast radius was
two places, and the second is the interesting one.

  * `OutErased.liftFn-Out-pair` passed `(λ _ → refl)` as the carrier's
    reflexivity. At a ν that is now the coinductive `∼ᵈ-refl` (new, mutual with
    `SF-rel-refl`, guarded exactly as `anaᵈ-∼`/`mapAnaᵈ-∼` are — no axiom).

  * `MeaningBridge.out-app-bridge` PATTERN-MATCHED `refl` on the ν relation,
    collapsing the two values to one, and its own comment said it therefore
    "carries no relational content". Under bisimilarity it carries real
    content, and Agda will not let you dodge it: splitting on `_∼ᵈ_` is
    ILLEGAL (`SplitOnCoinductive`). The clause is now the bisimulation's own
    two fields — `traceᵈ-∼` for the equal traces, `layerᵈ-∼` for the related
    layers — with `out-rel` pushing the layer relation out through the `Out`
    coercions.

`out-rel` is the dual of `AnaBridge.in-rel`. Its first statement conflated the
SHAPE functor with the CARRIER and did not typecheck; generalising the carrier
(the relation is `RelV A` for an arbitrary `A`, exactly as `in-rel` has it)
fixed it — the same correction D194's `νout-erase-D` needed.

### The pure side's axiom STAYS

`bisimS-to-eq` (plan 0.47, over `νS`) is a different case: its six uses produce
genuine EQUALITIES that get substituted into other proofs (`sem-CoIn-CoOut`,
`sem-ana-Out-id`, `forgetν-injectν`, `sem-ana-anaS`). Those cannot become
bisimilarity without rewriting the pure semantics, and the need there is
honest. One axiom removed, not two.

### Why this was worth doing before more machine-side proofs

It blocks nothing — `pair`/`case`/`In` are machine-side and touch nothing
coinductive. But it is the last member of a defect class the branch had already
paid for twice (D189, D199), and the class's lesson is that ν-shaped proofs
that look easy are wrong. The `refl` in `out-app-bridge` was exactly that: a
proof that looked easy because the relation had been weakened to let it be.

Exit tests 65 passed / 0 failed / 0 skipped. `cabal test` 746 passed.
`Once/Compiler.agda` and `Once/Certified.agda` typecheck.

## D202 — `obs-correct-pair` TAKES ITS INDUCTION HYPOTHESES (2026-09-14)

**Relates**: D152 (the same fix for composition, `comp-obs-correct`), D200 (the star-shaped
`IRObsCorrect` split), D203, D204/D206/D207/D209/D211 (the pair discharge).
**Note**: back-filled 2026-10-09 (plan 0.113 E), from commit da4a9710e.

### Context
`ir-obs-correct ⟨ f , g ⟩ = obs-correct-pair f g` passed the sub-IRs, not their correctness
proofs. But the emitted code splices both sub-runs:

    mov-to-output ∷ store-at-slot backup ∷
    ft ++ store-at-slot fst ∷ restore-input backup ∷
    gt ++ <nine-instruction heap pair build>

so, exactly like `g ∘ f`, the clause could not be proved without them. It was "unprovable in
principle, not merely unproved".

### Decision
The hypotheses arrive as ARGUMENTS (`IRObsCorrectF f → IRObsCorrectF g → …`), the way
`comp-obs-correct` takes them, and `ir-obs-correct` passes `ir-obs-correct f` / `… g`. The D200
star shape survives: no clause calls back into `ir-obs-correct`.

### Consequences
- Still an axiom at the time, "but a strictly weaker one — it now asks for more".
- Recorded for the discharge: the VALUE half is the backup/restore argument plus D174's
  heap-build lemmas; the TRACE half is the same `projTrace`/`>>=T` event-concatenation step
  as `comp-traces-agree` (done once, in D203).
- `obs-correct-pair` became a proof in D211. `case` got the same fix later (D282).

---

## D203 — `comp-traces-agree` DISCHARGED; the event-concatenation step (2026-09-14)

The postulate's own comment said it "looks PROVABLE now" and was "left as an
axiom only because the `projTrace`/`>>=T` event-concatenation step is its own
piece of work". That step is three lemmas, and the axiom is gone.

### The step

Composition denotes a BIND, and `projTrace` of a bind splits definitionally
with a THREADED budget:

    projTrace (m >>=T f) n
      = projTrace m n ++ projTrace (f …) (n ∸ length (projTrace m n))

while the machine side is a flat chain observed with `take k`. Reconciling
them is:

    take-++-split   take k (as ++ bs) ≡ take k as ++ take (k ∸ length as) bs
    minus-take      k ∸ length (take k as) ≡ k ∸ length as
    take-++-threaded  (the two composed, in the form both consumers want)

**`Bounded` is NOT needed**, which is the part worth recording. The obvious
route is "the denotation spends at most its budget, so `take k` is the identity
on it" — and `Bounded`/`PrefixFamily` are sitting right there in `TraceMonad`
inviting it. They are not required: `minus-take` says the residual budget
cannot tell whether the prefix was truncated, so the machine's
`k ∸ length (take k mEvF)` and the denotation's `k ∸ length dEvF` are the same
number without any hypothesis about either side's length.

(Both zero cases need `0∸n≡0`, not `refl`: stdlib's `_∸_` recurses on its
SECOND argument, so `0 ∸ n` does not reduce.)

### Why it could not simply be written where it stood

The obstacle was structural, not mathematical. `comp-value-realized-of` builds
the composite chain inside a pattern match on `f`'s `ValueRealized`, so
`chainF` and `chainG` exist only in that scope. A lemma stated outside it can
only reach them through a `with` abstraction over a projection — the
with-abstraction trap — or by assuming the result.

The fix is the one the with-discipline prescribes: change the DEFINITION, not
the proof. `go` now returns the whole `MachineRefinesObsF` rather than just its
value half, and takes `f`'s own trace agreement as an argument (it mentions the
matched chain, so it has to arrive from outside). `comp-step` is then `go`
applied to `mf`'s two fields.

This is the same shape D188 used on `obs-correct-apply`: a whole-clause axiom
becomes a proof by widening what the construction produces.

### Bearing on `pair`

`⟨ f , g ⟩` denotes `evalᴰ f a >>=T λ b → evalᴰ g a >>=T λ c → returnT (b , c)`
— the same threaded bind — so its trace half is now unblocked by the same three
lemmas. That was the reason to do this one first.

Postulates in the per-constructor clauses: 10 → 9. Root typechecks (68 modules
checked). Exit tests 65/0/0; `cabal test` 746 passed.

## D204 — WHY `pair` AND `case` ARE STILL OPEN: two missing facts, not two grinds (2026-09-14)

With `comp-traces-agree` discharged (D203) the remaining per-constructor
clauses are `pair`, `case`, `In`, `in-ν`, `sigop-rest`, `cata-correct` and the
three the user has deferred. Reading `pair` and `case` against the machine
shows both are blocked on something the interface does not say — the same
CLASS of finding as D202, where `pair` was unprovable because the dispatcher
did not pass its induction hypotheses.

### CORRECTION (2026-09-14, same day): "hiding" conflated two things

As first written this entry said `cata-correct` and the derived schemes "hide"
the need for `mem-pres`, which reads as though they owed something. They do
not. Two different roles were run together:

  * **Who OWES the fact.** Every IR does. `mem-pres` is a field of the
    obligation, so every clause supplies it — and most do so trivially: a
    single `mov-to-output` preserves everything (`reg-write-readLoc`),
    `terminal` emits no instruction at all. This is a universal property of
    emitted fragments, not a special burden.

  * **Who NEEDS it.** Only the clauses that read memory back ACROSS a sub-run:
    `pair` (restores its input after `f`), `cata-correct` (the loop reads its
    cursor and heap-linked stack back after each algebra run), and the derived
    schemes. While those are axioms, nothing ever asks for the field, so its
    absence is invisible. That is the sense in which they hid it: they hid a
    DEMAND, not a duty.

The one place the fact is genuinely assumed rather than proved is
`CalleeRun`/`block-runs`. At a call boundary this side cannot prove it — the
callee's run is given — so it is an honest axiom there and a theorem
everywhere else.

### `pair` — the obligation does not say what memory a run PRESERVES

`⟨ f , g ⟩` stashes its input at `backup-slot = n`, runs `f` (emitted at
frontier `n + 4`), and then does `restore-input backup-slot` so that `g` can
have the same input:

    mov-to-output ∷ store-at-slot n ∷ ft ++
    store-at-slot (suc n) ∷ restore-input n ∷ gt ++ <heap build>

For the restore to mean anything, `f`'s run must not have written slot `n`.
**Nothing in `IRObsCorrectF` says that.** `ValueRealized` has exactly ten
fields — `steps`, `settle`, `out-mode`, `cont-alloc`, `run`, `live`,
`at-end`, `no-ret`, `no-link`, `place` — and not one of them is about memory.
Nor is there a lower bound anywhere saying an emitted trace writes only slots
at or above its own frontier; `SlotBudget` bounds slots from ABOVE (they are
below the budget), which is the opposite end.

So `pair` is not merely unproved. As stated it is unprovable, exactly as it was
before D202 — for a different missing fact.

The fix is a field on `ValueRealized`:

    mem-pres : ∀ loc → BeforeFrontier alloc loc
             → readLoc (floc settle) loc ≡ readLoc s loc

It is TRUE — a sub-IR writes stack slots at or above its frontier, allocates
only fresh heap, and a call runs in its own frame — and it is what `PairWF`'s
`mem-preserved-through-setup` / `store-fst-preserves` / `bf-lift-to-scratch`
were, before D176 deleted them. Much of it already exists per-clause and is
simply not exported: `TwoCellBuild` has a `mem-pres`, `OutSetupPres` has one,
`ApplySetupPres` has `setup-mem-pres`, and D174's thirteen heap lemmas cover
`inl`/`inr`. What makes it a project rather than an edit is that EVERY clause
must then supply it — including `apply`, whose callee's preservation is not
available either (`CalleeRun` has no memory field, so `BlockRuns` would be
strengthened too).

### `case` — needs label resolution, which is a different development

Only one arm of a `case` runs, so it needs no cross-run preservation and is
untouched by the above. Its blocker is control:

    flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs
      = do-branch (tag-zf (flat-read-tag (floc fs))) m prog fs
    flat-exec-instr (instr-ctrl (c-jmp m))            prog fs
      = do-jump (find-label prog m) fs

Both consume `find-label prog m`, so the clause needs a theorem that a label
the fragment emits RESOLVES, and resolves to the position the fragment expects.
`SpanAt` is fetch agreement at given offsets; it says nothing about a scan for
a label. That theorem is what `LabelScope`'s `SegAgree` / `NoCross` /
`LabelsIn` machinery is for, and connecting it to `find-label` has not been
done.

### The shape of the finding

Three clauses in a row (`Out` at D199, `pair` at D202 and again here, `case`
here) turned out to be blocked by something the STATEMENT was missing rather
than by the difficulty of the proof. That is worth treating as the default
hypothesis when a clause resists: before grinding, check that the obligation
actually says enough to be true.

## D204b — THE STRENGTHENING LANDED: two fields, and one design correction (2026-09-14)

**Note (2026-10-09)**: numbered as a continuation of D204 (its amendment), not a separate decision.

`ValueRealized` and `CalleeRun` now say what a run does to memory and to the
allocator. Every clause supplies both; the apex axiom `block-runs` assumes them
at the call boundary, where this side cannot prove them.

    ValueRealized  mem-pres : ∀ loc → BeforeFrontier alloc loc
                            → readLoc (floc settle) loc ≡ readLoc s loc
                   bf-mono  : ∀ loc → BeforeFrontier alloc loc
                            → BeforeFrontier (falloc settle) loc

    CalleeRun      the same two, conditioned on the CALLER's `pre` together
                   with the `falloc fs ≡ enter-call pre` premise `CalleeRuns`
                   already carries.

### The correction the typechecker forced

`CalleeRun.mem-pres` was first written as `BeforeFrontier (falloc fs) loc`.
That is the CALLEE's frontier — `falloc fs` is `enter-call pre` — so it states
something about the callee's own frame and is useless to the caller, whose live
data is not before it. `Out` would not typecheck, which is how it surfaced.

### The design correction

The first attempt at the allocator half was `heap-mono : next-heap-ref alloc ≤
next-heap-ref (falloc settle)`. `Comp` then needed the frame fixed AND the slot
frontier fixed as well, i.e. three separate facts, because what it actually
wants is `frontier-monotone`'s CONCLUSION. Stating that conclusion directly —
`bf-mono` — is one field instead of three, and every clause already had it
proved as `bf-advance`. Prefer the conjunction the consumer wants over the
three facts it decomposes into.

### What it cost per clause — the point of the exercise

Nothing was hard, which is the evidence that the fact is a genuine property of
emitted fragments rather than a new obligation:

  * `id`/`fst`/`snd`/`out-μ`/`terminal`/`initial`/`free-heap`/`const` — the
    existing local `mem-eq` (a register write is invisible to `readLoc`), or
    `mem-untouched`; `bf-mono` is the identity, the allocator being untouched.
  * `SigOp` — `exec-abstract (instr-sigop si)` writes Output and the halt flag
    and nothing else, whatever the SigOp means.
  * `inl`/`inr`/`curry`/`Ana` — `TenStepPres.mem-pres` and `bf-advance`, both
    already proved and already spent internally by `valid-transport`.
  * `apply`/`Out` — the setup's own preservation composed with the callee's.
  * `g ∘ f` — `f`'s, then `g`'s.

Postulate count is unchanged (9). What changed is that `pair` is now provable:
`restore-input backup-slot` has the fact it needs.

## D205 — `mem-pres` IS CONDITIONED ONE STEP TOO TIGHT (2026-09-14)

Found by trying to use D204 for `pair`, which is what it was added for.

    mem-pres : ∀ loc → BeforeFrontier alloc loc
             → readLoc (floc settle) loc ≡ readLoc s loc

`BeforeFrontier alloc` covers stack slots `k < next-slot alloc` — the CALLER's
live data. But `pair`'s backup slot is `backup-slot = n`, and the obligation's
own premise is `next-slot alloc ≤ n`, so slot `n` is at or above that frontier
and is never `BeforeFrontier alloc`. The field does not reach the one slot
`restore-input backup-slot` depends on.

### The right condition

An emitted fragment writes only slots in `[n , budget)` — `n` being where it is
emitted — so it preserves everything BELOW ITS OWN FRONTIER, which is a
strictly larger set than the caller's live data:

    mem-pres : ∀ loc → BeforeFrontier (record alloc { next-slot = n }) loc
             → readLoc (floc settle) loc ≡ readLoc s loc

For `pair` this is exactly what is needed: `f` is emitted at `n + 4`, so it
preserves everything below `n + 4`, and `backup-slot = n` is in that range.

Weakening a HYPOTHESIS strengthens the obligation, so every clause must now
prove more — but not much more, and the shape is already there:

  * the leaf clauses' proofs are UNCONDITIONAL (`mem-eq`, `mem-untouched`:
    a register write is invisible to `readLoc` whatever the hypothesis), so
    they survive the change untouched;
  * the ten-step builds (`inl`/`inr`/`curry`/`Ana`) go through
    `store-slot-preserves-before`, which already takes the frontier-witness
    allocator and the RUN's allocator as SEPARATE parameters — so the witness
    can be swapped for the frontier-`n` one without touching the run. Their
    scratch slots are `n` and `suc n`, both `≥ n`, so the premise still holds.
  * `apply`/`Out` compose their setup's version with the callee's; a callee
    runs in its own frame, so it preserves the caller's slots outright.

### Why this is the third strengthening in a row

D202 (the dispatcher did not pass the IHs), D204 (the obligation did not say
what a run preserves) and now D205 (it said it about the wrong frontier) are
all the same discovery: `pair` is the first clause that READS MEMORY BACK
across a sub-run, so it is the first to exercise what the obligation actually
promises. Each attempt to use it has found the promise one notch too weak.
That is the top-down discipline working as intended — the alternative was
three more years of a postulate that hid all three.

## D206 — THE RE-CONDITIONING, AND THE METHOD THAT SHOULD HAVE PRODUCED IT (2026-09-14)

D205 named the defect: `mem-pres` was conditioned on the caller's frontier
(`BeforeFrontier alloc`) when what `pair` needs is the FRAGMENT'S OWN
(`backup-slot = n` sits at or above `next-slot alloc`, never below it). This
entry is the fix, and the reason the defect existed.

### The method failure

D204 and D205 both added a supporting fact by reasoning from the MACHINE —
"what does a run do to memory?" — and guessing the statement. That is
bottom-up work wearing a top-down label, and it was wrong twice, in the same
place, for the same reason: the CONSUMER was never consulted.

Strict top-down is the opposite: write the consumer, let the typechecker state
the obligation, read the field off the goal. Applied here that took one step —
a `Pair` skeleton with the restore isolated:

    restore-needs : ∀ (pF : FlatState)
                  → readLoc (floc pF) (AtStack (current-frame (falloc p1)) backup)
                    ≡ readLoc (floc p2) (AtStack (current-frame (falloc p1)) backup)

Preservation at stack slot `backup = n` in the caller's frame, with `f` emitted
at `n + 4`. The frontier-relative condition is not a guess from that goal; it
is a reading of it.

### The settled statements

    ValueRealized  mem-pres : ∀ loc → BeforeFrontier (record alloc { next-slot = n }) loc
                            → readLoc (floc settle) loc ≡ readLoc s loc
                   bf-mono  : ∀ m loc → BeforeFrontier (record alloc { next-slot = m }) loc
                            → BeforeFrontier (record (falloc settle) { next-slot = m }) loc

    CalleeRun      both, plus `pre` and the `enter-call` premise; `mem-pres`
                   ALSO over an arbitrary `m`, because a callee runs in its own
                   frame and so preserves the caller's frame ENTIRELY — a
                   stronger claim than a straight-line fragment can make, and
                   the reason the two records' fields differ.

`bf-mono` is quantified over the slot bound for the same reason `CalleeRun`'s
is: `g ∘ f` must spend `f`'s preservation at `f`'s bound and `g`'s at `g`'s, so
a witness fixed at one bound does not compose. Four formulations were tried
before this one; the generalisation over `m` is what made it converge.

### What the change cost, clause by clause

  * `Simple`, `SigOp` — NOTHING. Their proofs are unconditional (a register
    write is invisible to `readLoc` whatever the hypothesis), so weakening it
    left them untouched. That is the signal the fact is real.
  * the ten-step builds — a witness SWAP inside `TenStepPres.mem-pres`, which
    is possible only because `store-slot-preserves-before` already takes the
    frontier witness and the run's allocator as SEPARATE parameters. The run is
    not touched; their stashes are `n`, `suc n`, both at or above the swapped
    frontier.
  * the spend sites (`valid-transport`, apply's `carry`, `code-cell`) — a
    `frontier-monotone` lift, since the caller's data lies below
    `next-slot alloc ≤ n` and the hypothesis weakens UPWARD.
  * `apply`/`Out`/`g ∘ f` — compositions, unchanged in shape.

Root typechecks (11 modules). Exit tests 65/0/0; `cabal test` 746 passed.

## D207 — `pair`'s KEYSTONE, PROVED (2026-09-14)

The backup/restore argument — the part D202, D204 and D206 all existed for —
is a theorem. `Once.CCC.Codegen.IRObsCorrect.Pair` proves:

    backup-written   slot `backup` holds the input after the prologue
    backup-survives  `f`'s run leaves it alone
    restore-ok       therefore `restore-input backup` hands `g` exactly what
                     `f` was given

`restore-ok` is one `trans` of the other two. That is the measure of the three
preceding decisions: before them none of its three ingredients could be STATED
— the dispatcher did not pass `f`'s induction hypothesis (D202), the obligation
said nothing about memory (D204), and then it said it about the caller's
frontier rather than `f`'s (D206). `backup = n` sits four slots below `f-start`,
inside the window `mem-pres` now promises and outside the one it promised
first.

Two facts fell out as `refl`, worth recording because they simplify what is
left: `falloc p2 ≡ alloc` (neither prologue row touches the allocator), and
`Input1` survives both rows (`mov-to-output` writes Output, `store-at-slot` is
a `writeLoc`), so `f` can be handed the caller's own input residence unchanged.

### Status: UNWIRED, and deliberately so

`obs-correct-pair` is still the postulate; this module is not yet imported by
anything, so it is an ISLAND by the merge rule and must not reach `master` in
that state. It is committed rather than discarded because it is verified work
on the critical path, and the completion is mechanical from here:

  1. `span-f` / `span-g` — the fetch splits, modelled on `Comp.span-g`;
  2. the two IH applications, using `alloc-p2` and `input1-p2` above;
  3. the nine-instruction tail — the SAME shape as `inl`'s heap build
     (`TenStepPres` rows 2-10 at `snd-stash`, with `i6 := load-from-slot
     fst-stash` and `i8 := load-from-slot snd-stash`), so the remaining work is
     a shared `NineStepPres` or an inlined copy of `Sum`'s argument;
  4. the trace half — `take-++-threaded` twice, pair denoting the same
     threaded bind composition does.

Either pair lands and this module becomes load-bearing, or both are deleted
together. It must not sit here unwired.

## D208 — THE ALLOCATOR QUESTION, AND WHY `mem-pres` SPLITS (2026-09-14)

Asked whether the IR clauses should be proving heap-block preservation at all
— they should not, `blocks-disjoint` is a FIELD every allocator implementation
discharges — and whether it is time to run plan 0.35. Three findings.

### 1. Plan 0.35's "Why" is STALE

It says the interface is "alloc-only, no `free`". It is not.
`AllocatorInterface` already has `init`, `alloc`, **`free`**, `block-in-region`,
`blocks-disjoint`, `alloc-fresh` — all as fields. M1 is essentially done, and
`SMCore` already imports `Once.Allocator.AbstractInstance`, so the abstract
machine's alloc IS interface-routed. What is missing is M2 (no `instr-free-heap`
exists anywhere) and M3 onward (codegen still bump-lowers; nothing calls an
allocator label).

### 2. The subsystem exports exactly what the clauses need — and it is DEAD

`AbstractInstance.fresh-loc-disjoint` / `fresh-cell-disjoint` are documented as
"convenience forms in the granularity IR producers actually consume". They have
ZERO consumers. The codegen instead carries a private duplicate,
`fresh-heap-≢`, proving the same thing by the same `<-irrefl` argument.

### 3. …but the layering cannot be fixed yet, and this is the real finding

    heap-before : ref-id (heap-ref hl) < next-heap-ref alloc
                → BeforeFrontier alloc (AtDynamic hl)

**`BeforeFrontier`'s heap half IS the bump allocator's encoding.** "Live on the
heap" is *defined* as "ref-id below the frontier" — true of a bump allocator,
FALSE of a reusing one: a freed-then-reallocated `Mempool`/`Slab` slot has a low
ref-id and is not the caller's live data. So the IR cannot consume the
interface's allocator-agnostic `alloc-fresh` while its own vocabulary hard-codes
the instance's representation. Replacing that notion is precisely 0.35 M2's
liveness contract; bolting a consumption of `alloc-fresh` underneath the current
`BeforeFrontier` would only move the duplicate.

### The change: split `mem-pres`, quarantine the contingent half

    stack-pres  -- PERMANENT. Frames are the machine's, not the allocator's,
                -- and `free` never touches a stack slot.
    heap-pres   -- CONTINGENT on the bump encoding; to be restated as 0.35 M2's
                -- liveness property.

The combined form is DERIVED once (`vr-mem-pres`) by casing on the location, so
consumers that do not care keep asking for it. What the split buys is that the
bump-specific assumption is NAMED instead of hidden inside a field that is
otherwise allocator-independent — and `⟨ f , g ⟩`'s keystone (`restore-input
backup` reads `AtStack (current-frame alloc) n`) now visibly depends only on the
permanent half, so pair is not gated on the allocator at all.

### Recommendation on running 0.35: NOT the whole plan, not on this branch

M3 lowers `instr-alloc-heap` to `call alloc-label`, which changes the emitted
trace and so invalidates the heap-build proof in `inl`, `inr`, `curry`, `Ana`,
`apply` — and whatever `pair` adds. That rework is branch-scale, extracted-cone,
and lands on three arches. It belongs on its own branch after this one merges.
Note the rework is already sunk across five clauses, so finishing `pair` first
adds one more to a list of six — marginal.

Root typechecks. Exit tests 65/0/0; `cabal test` 746 passed.

## D209 — ONE HEAP BUILD OVER ANY START STATE (`NineStepPres`); PAIR's SPAN SPLITS IN FOUR (2026-09-15)

**Relates**: D202, D207 (backup survives `f`'s run), D211 (`obs-correct-pair` a proof),
D212 (removed `PairTail`, the defective instance introduced here).
**Note**: back-filled 2026-10-09 (plan 0.113 E), from aa4471383, 0b5821e87, 472a71d8e.

### Context
`inl`, `inr`, `curry`, `Ana` and `⟨ f , g ⟩` all end with the same nine instructions
(`store-at-slot n ∷ instr-alloc-heap 2 ∷ … ∷ load-from-slot (suc n) ∷ []`). `TenStepPres`
hardwired the start state to `entry-flat … ` one `mov-to-output` in, so `pair`, which starts
the nine wherever `g`'s run settled, could not use it; the alternative was a fourth inlined
copy (~370 lines).

### Decision
- `NineStepPres` (`IRObsCorrect/Machine.agda`) takes the START STATE as a parameter, plus two
  facts relating its allocator to the caller's frontier (`heapref-u1`, `cf-u1`).
  `TenStepPres` becomes a wrapper that supplies `t1` and re-exports every field; `mem-pres-from`
  is relative to the start state. "No argument is duplicated."
- `pair`'s text decomposes as `pre ++ ft ++ mid ++ gt ++ (store-at-slot snd-stash ∷ tail)`;
  `shape` proves it by `refl` ("the emitter's own `let`, spelled out"), and `span-f` / `span-g`
  split `SpanAt` mechanically. The `g` index re-association (`g-shift`) is discharged by the
  ring solver, after hand-written `trans` chains failed three times.

### Consequences
- `PairTail` instantiated the build at pair's stashes; its `heapref-gs` premise turned out to
  be unsatisfiable whenever a sub-run allocates (D212 deleted it; the clusters instantiate
  `NineStepPres` directly).
- `NineStepPres.heapref-u1` is stated with `≡` where `pair` needs `≤` (recorded at D211).

---

## D210 — `frame-pres`: the fourth thing the obligation did not say (2026-09-15)

Found by scouting `⟨ f , g ⟩` STRICTLY top-down — the clause was written as a
record with fourteen holes first, so Agda stated the obligations, and a
fourteen-agent workflow then scouted each hole against the existing toolbox
with instructions to grep and quote every helper's signature rather than name
it from memory.

Three independent verifiers converged on the same single gap: **`ValueRealized`
has no frame-preservation field.**

    frame-pres : current-frame (falloc settle) ≡ current-frame alloc

`⟨ f , g ⟩` needs it twice — `restore-input backup` reads
`AtStack (current-frame alloc) backup` AFTER `f`'s run, and transporting `f`'s
result validity to the final state calls `validityWF-frontier-advance`, whose
FIRST premise is exactly this equation. Nothing in the record said it, and
nothing in the tree derives it at `exec-flat`/`ValueRealized` level: `bf-mono`
encodes frame agreement only up to `stack-ancestor`, which is weaker than an
equation.

It is the same shape as D204 (memory), D206 (the frontier it is conditioned on)
and D208 (the stack/heap split): the obligation did not say enough for its
consumer, so it now says it. Four in a row, all found by the same clause —
`pair` is the first IR that reads memory back across a sub-run, so it is the
first to exercise what the obligation actually promises.

### It cost nothing to supply, which is the evidence it was always true

Every discharged clause ALREADY proved its own version internally and simply
did not export it: `cf-fs10` (Sum ×2, TwoCell), `cf-a16` (ApplySetupPres),
`cf-t1`/`cf-u3` (TenStepPres/NineStepPres). The straight-line clauses took
`refl`. `Out`/`apply`/`g ∘ f` compose the call's or sub-run's with their own.
All seven parts typechecked on the first attempt after the field was added.

It is TRUE for a structural reason worth recording: no emitted instruction is a
frame op — that is `FrameFreeTrace`, already proved for every emitted trace —
and a call enters and leaves its own frame.

`CalleeRun` gets the analogue, against the caller's `pre`, since `enter-call`
SHIFTS the frame and a returning callee restores it.

Also exported: `validityWF-with-bf-transfer` (ClosureWellFormed.agda:2115),
which the scouts found unexported. It takes a `bf-transfer` function directly,
so some validity transports can use `bf-mono` without needing the frontier
premises at all.

### The workflow's other finding: no principled blocker

The blocker-hunters were told not to manufacture one. They found none — the
remaining work on `pair` is grind, not discovery. What they did find is a long
list of line-citation drift and four invented helper names in the scouts' own
plans (`size-f`, `NSP.u1`, `_∘_`, a mis-stated `frontier-monotone` direction),
each caught before it cost a typecheck cycle. That is the pattern working: this
session had already burned several 10-minute round trips on exactly that class
of error.

Root typechecks. Exit tests 65/0/0; `cabal test` 746 passed.

## D211 — `obs-correct-pair` IS A PROOF (2026-09-15)

The CCC product introduction is discharged. `Pair.agda` is no longer an island;
`ir-obs-correct ⟨ f , g ⟩` routes to a real proof, and the postulate is gone
from `Simple.agda`. Per-constructor postulates: 9 → 8.

### The shape

Four independent clusters, each a parameterised module — so each was written
and typechecked WITHOUT the others existing, and they assemble by
concatenation:

    PairChain  the run: pre(2) ++ f ++ mid(2) ++ g ++ snd-store(1) ++ tail(8),
               with `handover-eq` spent TWICE (each sub-run's `run` starts at
               its own `entry-flat`, not where the previous segment settled)
    PairPlace  `valid-pair-wf` over the heap node, with both components'
               validity transported from their sub-run's settle state
    PairPres   the four preservation fields across five segments
    PairTrace  the nested bind — `take-++-threaded` twice

plus `PairAssemble`, the clause that instantiates them.

### What made it possible, and it was not this session's proof work

Four earlier decisions, each found by TRYING to use the obligation and failing:

    D202  the dispatcher did not pass `pair` its induction hypotheses
    D204  `ValueRealized` said nothing about memory
    D206  …and said it about the CALLER's frontier, not the fragment's
    D210  …and said nothing about the FRAME

`pair` is the first IR that reads memory back across a sub-run, so it is the
first to exercise what the obligation actually promises. Each attempt to use it
found the promise one notch too weak. The proof itself only became writable
once those four closed.

### Method note: what the parallel agents were and were not good for

Three agents wrote the final clause independently; all three succeeded, so the
redundancy bought nothing — and because each worktree carries its own `_build`
and the machine runs one agda at a time, three root checks SERIALISE. An hour
went to queuing, not thinking.

**Redundant attempts help when the bottleneck is reasoning and hurt when it is
a shared physical resource.** Parallelise the writing; verify once.

### The check that mattered

Before harvesting, the diff was audited for the failure mode that makes a green
build worthless — reaching it by weakening the claim. Zero new postulates, no
`TERMINATING`, no holes, no new `abstract`, and `Interface.agda` / `Machine.agda`
BYTE-IDENTICAL. The obligation `obs-correct-pair` now proves is the one it was
always stated at.

### Two defects the scouts found in this branch's own earlier work

  * `NineStepPres.heapref-u1` (D209) is stated with `≡` where `pair` needs `≤` —
    either sub-run may allocate, so the heap frontier moves. `PairTail` as
    committed is therefore NOT instantiable by any caller; the clusters bypass
    it by instantiating `NineStepPres` directly. The premise is only ever spent
    via `fresh`, which needs `≤`, so relaxing it is safe — deferred because it
    ripples into `Sum`/`TwoCell`.
  * There is no `exec-flat`-level heap-monotonicity lemma anywhere in the tree.
    The assembly manufactures one (`vr-heap-mono`) by instantiating `bf-mono` at
    a synthetic heap ref and reading `BeforeFrontier.heap-before` back out. That
    is a hack standing in for a missing fact, and a candidate FIFTH field.

`Once/Compiler.agda` and `Once/Certified.agda` typecheck. Exit tests 65/0/0;
`cabal test` 746 passed.

## D212 — DELETE THE ISLANDS THE AST DUMP FOUND; REACHABILITY, NOT IMPORTS, DECIDES (2026-09-16)

**Relates**: MERGE.md §4b (the reachability gate, D279, cb09647ca), D201 (corrected here),
D209 (`PairTail`), D214 (the same dump confirms `ir-size` dead).
**Note**: back-filled 2026-10-09 (plan 0.113 E), from commit a6e5dbcbc.

### Context
MERGE.md §4b (2026-09-10) made the apex's AST/trust-base dump (`run-ast-dumps.sh`, not
tracked in the repo) a merge gate. Its first use on the branch compared the D211 tree against
the plan 0.89 ancestor dump ("both new-format; master's is old-format and NOT comparable").

### Decision
Three constructs reachable from nothing were deleted:
- `PairTail` — 0 reachable names; its `heapref-gs` premise is unsatisfiable once either
  sub-run allocates, so no caller could instantiate it (introduced by D209).
- `fetch-drop2` — written for the span splits, never used by them.
- the ν-erasure cluster in `AnaErased` (`sem-ana-anaS`, `anaS-subst-nat`, `events-F-erase`,
  `sem-ana-erase-coh′`, `sem-ana-erase-full`), orphaned when D201 rerouted the ana bridge
  through `anaᵈ-∼`.

Kept, with reasons: `SFRel`/`coerce-SFRel` (imported by `FaithfulLemmas`; the dump showed only
its where-block internals dying — a misreading caught before deleting); `bisimS-to-eq` (its four
remaining consumers are the pure ν's Lambek/round-trip laws — deleting them is "a separate
decision"); `LabelScope`'s `curry-bl-*` losses (deferred to plan 0.89).

### Consequences
- **Correction to D201**: "the pure side's `bisimS-to-eq` stays: its six uses produce real
  equalities" was true of the source text and false of the reachability graph —
  `sem-ana-anaS` was its last reachable consumer, so the axiom had already left the trust base.
- Method fixed for later entries: deletions are judged against `reachable`, never against
  imports (§4b).

---

## D213 — `block-runs` AND `entry-size` ARE FALSE (2026-09-16)

Three emptiness probes, each written against the REAL postulate (not a
re-declared copy), each run with the `.agdai` deleted and the
`Checking Once.Adequacy.ArchCorrectness.FlatFromObs` line confirmed present,
each exiting 0 with zero errors. `probe : ⊥` typechecks three times.

    probe           refutes  block-runs / closures
    probe-ν         refutes  block-runs / coalgs
    probe-entry-size refutes entry-size

These were found by the top-down exercise for discharging `block-runs`: writing
the consumer first and asking what the premises actually give. They did not
produce a step list; they produced a refutation, which is the better outcome —
a plan built on that axiom would have been built on sand.

### The defect in `block-runs`, and why it is NOT about label uniqueness

    valid-closure-reg-wf  {body-label  : LabelId} → readLoc s (sucLoc cl)  ≡ just (SV-Code body-label)
    valid-ν-susp-wf       {coalg-label : LabelId} → readLoc s (sucLoc νl) ≡ just (SV-Code coalg-label)

A free implicit label, tied to nothing but a memory read. Fabricate a state
whose heap reads `just (SV-Code anything)` and both witnesses are inhabited at
a label no program ever minted; then `block-runs`' conclusion
(`find-thunk (ir-to-trace ir) ℓ ≡ just j`) is refutable at `ir = id {Unit}`,
which emits no blocks at all.

Uniqueness would not save it. Uniqueness says no two blocks collide; it does
not say this label belongs to any block. **The witness is a MEMORY fact being
asked to underwrite a PROGRAM fact.**

### Why labels are not special — the real asymmetry

For a pair, memory determines meaning: cell 0 holds an `A`, recursively, down
to scalars. For a closure, cell 1 holds a NAME, and the binding from name to
code lives in the PROGRAM, not the heap. A closure is the one value whose
meaning is not a function of the state alone — it is a function of
(state, program). `ValidAtWF` is a STATE predicate, so asking it to pin a
closure's meaning asks memory to witness what memory cannot contain.
`block-runs` existed to paper over exactly that, and is false because it tried
to recover a program fact from a state fact.

### …and the actual missing premise

The emitter returns TWO channels:

    ir-to-trace' : … → ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
                                    ↑ trace           ↑ BLOCK TABLE

`IRObsCorrectF` states a placement premise for ONE of them —
`SpanAt prog base (emitted n l ir)` — and says nothing whatever about where the
blocks go. **The obligation models a `CompUnit` as if it were a bare trace.**

That also explains the island cluster D212 recorded: `link-block-split`,
`link-pre`, `link-post`, `FlatSteps-middle` (D168 / plan 0.89 Phase D1) are
built, correct, and reachable from nothing, and `FlatStepLemmas.agda:359`
documents their intended architecture — for a consumer that was never written.
They are not rot; they are the missing half, stranded.

### `entry-size` — a different, simpler defect

    entry-size : ∀ (ir : IR Unit Unit) → ir-size ir < program-bound

`program-bound` is a fixed module PARAMETER; `ir-size` is unbounded
(`ir-size id = 1`, `ir-size (g ∘ f) = 1 + ir-size g + ir-size f`). Refuted by
`big n = id ∘ id ∘ …` with `n ≤ ir-size (big n)`, instantiated at
`n := program-bound`. Not a state/program confusion — a QUANTIFIER IN THE WRONG
PLACE. The true statement is per-program: `program-bound` must be chosen after
the IR, not universally quantified inside the module.

### What this does and does not mean

The COMPILER IS FINE. 746 tests pass on three architectures and the emitted
code does the right thing — unlike D199, where a false postulate hid a real
segfault. What is broken is the PROOF: `entry-witness` feeds BOTH false axioms
into `ir-obs-correct`, so everything above it (`riscv64-correct`,
`arch-correctness`, `once-compiler`, `once-certified`) is proved against them,
and ⊥ is derivable from the trust base.

`obs-correct-pair` (D211) is unaffected — verified: no pair path reaches either.

`rewrite-preserves-of`, the third postulate in that file, is NOT of this class.
It is a genuine claim about `map-rewrite` preserving the flat trace; refuting it
would need a real counterexample to the arith rewrite, not a fabrication. It
stays an honest deferred proof.

### The pattern, now earned a place in the merge gate

Fourth instance this session of ONE error: the obligation is missing a premise,
so it was replaced by an assumption that quantifies over things no program
produces (D204 memory, D206 the frontier, D210 the frame, now this). And the
third FALSE axiom on this branch (`valid-ν-wf`, `obs-correct-Out`, `block-runs`).

MERGE.md already mandates emptiness probes for new residuals. This says they
are owed by OLD ones too, and names the smell precisely: **a residual whose
CONCLUSION mentions the program while its PREMISES mention only a state.**
`block-runs` had that shape in plain sight since D188.

## D214 — `program-bound` WAS NEVER FUEL (2026-09-16)

Plan 0.91 S1. `entry-size` — refuted in D213 — is **gone, not narrowed**, and
the entire `program-bound` telescope went with it: 26 modules, `Once.Certified`
down to the leaves, zero new postulates, root green.

### The finding

The axiom said the compiled `main` fits a bound:

    entry-size : ∀ (ir : IR Unit Unit) → ir-size ir < program-bound

`program-bound` was a module parameter, so it is universally quantified while
`ir-size` is unbounded: `big n = id ∘ id ∘ …` at `n := program-bound` refutes
it. The interesting question was not *how to prove it* but **what read it**.

Nothing did. `ir-obs-correct` recurses STRUCTURALLY on the IR. Every single use
of the bound only *weakened* it to a sub-term in order to feed a sub-IH —
`comp-size-f` / `comp-size-g` in `CompC`, `szf` / `szg` in the pair and sum
clauses. Two lemmas whose entire job was to shrink a number nobody ever read.
D170 had already deleted the one genuine consumer (`body<bound` in
`valid-closure-wf`); what survived was a parameter threaded through 26 modules
to be passed down and discarded.

So the premise was deleted from `IRObsCorrectF` itself, and `entry-witness`
lost an argument:

    entry-witness ir ioc k =
  -   ioc (entry-size ir) 0 0 (ir-to-trace ir) 0 …
  +   ioc 0 0 (ir-to-trace ir) 0 …

### The closure carries its own bound

The one place a bound is real is a closure body, and it does not need a global
one:

    record ClosureWellFormed … (env : ⟦ EnvType ⟧)
    -                          (body<bound : ir-size body < program-bound)
    +                          {body-bound : ℕ}
    +                          (body<bound : ir-size body < body-bound)

"Choose the bound after the program," applied locally. `suc (ir-size body)`
discharges it.

`readLoc-stack-heap-eq` — the one thing four modules took from `ValidityDef`
and which never mentioned a bound — was hoisted into a bound-free `ReadLocEq`
module, so those four stopped inventing a bound to pass.

### The method correction, which is the durable part

S0 was written as: replace both false postulates with holes, and read the red
as the work-list. **That is the wrong instrument and it produced nothing.**
Holing a body leaves the TYPE unchanged, so Agda emits no interface for the
module and every consumer fails to LOAD rather than to typecheck: the full-root
run reported exactly one error, an `import` line in `X86-32.agda:97`, and the
rest of the cone was simply unbuildable.

The MECHANISM, verified rather than inferred — after a run where the two
definitions were holes, the interface file is simply absent:

    $ ls formal/_build/2.8.0/agda/Once/Adequacy/ArchCorrectness/FlatFromObs.agdai
    (no such file)

    X86-32.agda:97.8-49: error: [SolvedButOpenHoles]
    Module cannot be imported since it has open interaction points

An unsolved interaction meta SUPPRESSES THE INTERFACE. So the importer's error
is `[SolvedButOpenHoles]` at its `import` line — one error, at the first
importer Agda happens to reach, naming no obligation. Agda never gets as far as
the call sites, so there is no per-definition work-list to read off. The
consumer chain in that run had to be reconstructed by grep, which is precisely
the bottom-up work the plan forbids.

> **Top-down means changing a TYPE, never blanking a BODY.**
> A hole REMOVES information; a changed statement PRODUCES it.

Going red at every consumer is the *benefit* of top-down work, not its cost —
and it only happens when the STATEMENT moves. The fix that landed never used
S0's work-list: it changed the statement and followed the resulting type errors
to all 26 files.

### CONFIRMED BY THE AST DUMP (added 2026-09-16, after S2)

`./run-ast-dumps.sh` at `ca693126`, diffed against the 0.90 base. Eight
definitions left the reachable set and every one is accounted for — but two of
them are the real evidence for this entry's claim:

    - Once.IR.Size.ir-size
    - Once.IR.Size.ir-size-nt

**The size measure itself is now unreachable from `Once.Certified.once-certified`.**
Not "nothing reads it any more" as a reading of the source — provably dead from
the entry point. D170's comment called it "the whole `program-bound` /
`ir-size` / `RecDispatcherWF` apparatus"; with the parameter gone the apparatus
has no consumer in the certified cone.

The other six: `entry-size`, `comp-size-f`, `comp-size-g` and `PairAsm`'s
`szf`/`szg` were deleted here, and `ValidityDef.readLoc-stack-heap-eq` moved to
`ReadLocEq` (it reappears in the same diff's added list).

Trust base 104 → 104 across S1+S2: one swap, `entry-size` out and S2's
`entry-blocks` in. Nothing else entered or left.

### Two fossils swept

`Comp.agda:111` and `SigOp.agda:250` each carried a bare `postulate` keyword
with nothing under it — left behind when D203 and D174 discharged their
contents. They are only scope-checker warnings, but they inflate every
grep-based residual count. Removed; the commentary under them is kept.

### Open, found in passing

`ValidityDef` (`Once/CCC/Machine/Validity.agda`) is now the only module naming
`program-bound`, and it is **applied nowhere**: `IRObsCorrect/Prelude.agda:81`
re-exports `module ValidityDef` but no site instantiates it. Dead by the
consumers-not-importers test. Separate cleanup.

## D215 — THE BLOCK CHANNEL ENTERS THE OBLIGATION (2026-09-16)

Plan 0.91 S2. `IRObsCorrectF` gains a premise beside `SpanAt`:

    BlocksAt prog (blocks n l ir) →

`ir-to-trace'` returns `(budget , next-label , trace , BLOCKS)` and this
obligation had only ever quantified over the TRACE. But `curry` and `Ana` do
not put their body in the trace — they put it in the block channel, and
`blocks-layout` links it in somewhere else entirely. **That gap is what
`block-runs` was covering.**

    BlockAt prog blk@(lbl , _ , _) =
      ∃[ j ] ((find-thunk prog lbl ≡ just j) × SpanAt prog j (block-layout blk))

    BlocksAt prog bs = All (BlockAt prog) bs

`block-layout` rather than the bare body text, deliberately: `blocks-layout`
places `c-thunk`, body and `c-ret` contiguously and `find-thunk` resolves to
the `c-thunk` ITSELF (`ft-match true _ _ i = just i`, no successor). Saying it
in ONE `SpanAt` keeps that off-by-one where `block-layout` can settle it
instead of re-deriving it at every consumer.

`All` is not an arbitrary choice either. `SlotBudget.blocks-below` is already
a total structural walk over `IR` returning `All BlockOK (bodies-of
(ir-to-trace' n l ir))` — S5's proof is that induction with this predicate.

### What the type change produced — 28 sites, and no cascade

This is the S0 contrast in one table. A changed STATEMENT fails at each CALL
SITE; a blanked BODY failed at one `import` line (D214).

    Simple 9, Out 4, Apply 3, Sum 2, TwoCell 2, SigOp 1   accept as `_`
    Comp 3, PairAssemble 1                                 must SPLIT it
    ir-obs-correct (the dispatcher)                        point-free, no change
    entry-witness                                          the apex's share

Each module reported its own error at its own clause head. `Machine` was clean
because it constructs no `IRObsCorrectF`.

### The split is cheap, because the emitter hands it over

    ir-to-trace' n l (g ∘ f) = … , (ft ++ mov-to-input ∷ gt) , (fb ++ gb)

The TRACE needs `g` found past a bridge instruction; the BLOCKS are a bare
`++`. So both halves come off one `++⁻`:

    comp-blocks-f g f prog n l bl = proj₁ (++⁻ (blocks n l f) bl)
    comp-blocks-g g f prog n l bl = proj₂ (++⁻ (blocks n l f) bl)

Pair is the same shape, and `PairShape` already names the emission sites
(`f-start`/`l`, then `n1`/`l1`), so `blocks-f`/`blocks-g` line up with the
existing `span-f`/`span-g` verbatim. SMCore:1291 had recorded the fact this
rests on since D160: "the block channel is a `++`-homomorphism".

### What S2 did NOT do, stated plainly

`FlatFromObs` went from 2 residuals to 3. S2 MOVES an assumption; it does not
remove one. The reduction is S4's.

    block-runs    unchanged, still FALSE — probe re-run post-S2, `boom : ⊥`
                  still compiles (.agdai deleted, both modules rechecked)
    entry-blocks  NEW, and the point of the exercise

    entry-blocks : (ir : IR Unit Unit) → BlocksAt (ir-to-trace ir) (blocks 0 0 ir)

`entry-blocks` is about the PROGRAM, not about a STATE. D213's refutation
works by fabricating a heap that reads `just (SV-Code ℓ)`; `entry-blocks` takes
only the IR, so there is nothing to fabricate. `Once/Probe/EntryBlocksRefute`
records the failed attempt and pins the fact it rests on:

    id-has-no-blocks : blocks 0 0 (id {Unit}) ≡ []
    id-has-no-blocks = refl

At D213's own witness IR the list is EMPTY, so the content there is `All _ []`
— inhabited, not absurd. **This is not a proof that `entry-blocks` is true.**
It shows one specific attack does not transfer. Class: deferred-proof, not
axiom; S5 discharges it.

### D168 is demanded after all

The plan said the stranded `link`-relocation machinery might get its first real
consumer here, and to CHECK rather than assume. The check is positive:

    ir-to-trace ir = emitted 0 0 ir ++ c-ret ∷ blocks-layout (blocks 0 0 ir)

so S5 is exactly "where does `blocks-layout` put each block in the linked
image", which is what D168 was written for.

### Two self-inflicted collisions, and the lesson

Adding two names to a `public`-re-exported prelude broke two unrelated places:
`All`'s `[]`/`_∷_` collided with `Data.List`'s and `FlatStepsAPI`'s, and `List`
collided with a LOCAL `open import Data.List using (List)` 1600 lines into
`Pair.agda` — Agda reports `[AmbiguousName]` even though both entries are
literally `Agda.Builtin.List.List`, because it is two scope entries, not two
types. Both fixed (constructors withdrawn — S2 builds no `All`, it only splits
with `++⁻`; local import deleted).

**Every `public` name in a prelude is a potential conflict with every local
import in the cone, and the compiler surfaces them one at a time, far from the
change.** Keep preludes narrow: export the type and the lemmas, not the
constructors, until something actually constructs.

## D216 — THE FORBIDDEN QUADRANT (2026-09-17)

Three attempts at one obligation, three times the same shape, twice demonstrably
false and the third narrower but not different in kind. The rule that separates
them:

> **A premise relating a STATE to the PROGRAM may have a SYNTACTIC conclusion
> only if its hypothesis DETERMINES the syntax.**

| hypothesis   | conclusion    | example                                  | |
|--------------|---------------|------------------------------------------|-|
| state-indexed| denotational  | `CalleeRuns` — concludes about `evalᴰ body envArg` | safe |
| state-free   | syntactic     | `BlocksAt`, `entry-blocks` — about `prog` alone     | safe |
| state-indexed| **syntactic** | `block-runs`, `CodeResolves`                        | **both FALSE** |

### Why the bad quadrant is bad, precisely

A closure value determines its body's DENOTATION and nothing more:

    f-is-closure : f ≡ (λ arg → evalᴰ body (env , arg))

That is D170's rule working correctly — a value may expose only what it carries.
So any premise whose hypothesis is a closure witness and whose conclusion names
`emitted … body`, `blocks … body` or any other TEXT is asking the value for
information it provably does not have. Two IRs with one denotation decompose the
same value, and a function (`find-thunk`) must send their different texts to one
position. `Once/Probe/CodeResolvesRefute` does exactly that; the sources are
archived in `docs/compiler/probes/block-runs-refutation.md`.

`block-runs` (D213) failed the same way from the other end: its hypothesis was a
bare memory read, which determines nothing at all.

### The consequence for plan 0.91

S3 as designed is dead, and `CodeResolves` is deleted (it was threaded nowhere —
two lines, its own definition).

**CORRECTION, same day, before anything was built on it.** The paragraph that
stood here claimed the label-keyed successor `CodeWF` "sits in the same quadrant
and is narrower rather than different". That is WRONG, by this entry's own rule.

The rule is *a syntactic conclusion is allowed if the hypothesis DETERMINES the
syntax*. `CodeWF`'s conclusion mentions only `ℓ`, and its hypothesis — an
`SV-Code ℓ` readable in `s` — determines `ℓ` exactly. It is in a SAFE quadrant.

The two refuted statements failed for two DIFFERENT reasons, and neither is
"state-indexed hypothesis":

  * `CodeResolves` concluded about `emitted … body`, the body's TEXT, which the
    closure witness provably does not determine (it pins `evalᴰ body`).
  * `block-runs`' hypothesis was a bare memory read, which determines NOTHING —
    not the body, not even that the label came from this program.

Generalising from those two to "no state-indexed premise may conclude anything
syntactic" was an over-reach from two data points. The quadrant table above is
right as a summary of what was OBSERVED; it is not a licence to reject a premise
whose hypothesis pins its own conclusion.

### What the machine gets wrong — and it is NOT that it uses labels

A second correction to this entry's first draft, which proposed lowering labels
to ADDRESSES in the machine model (the original plan 0.93). That is backwards.
Labels are the RIGHT abstraction for every general part of the compiler and its
proofs; the only thing that should lower a label to an address is the arch
backend and the assembler after it — which is already what happens:

    compile-abstract (instr-load-code-addr n) = lea rax (rip+label n) ∷ []
    compile-abstract instr-call-closure       = call (mem (base+disp r12 slot-size)) ∷ []

The actual defect is narrower: a LABEL-addressed machine has been handed a
POSITIONALLY-addressed program. `prog` is a flat `AbstractTrace`, so "enter
block ℓ" is implemented as a SEARCH —

    do-call-code prog (just (SV-Code ℓ)) fs = do-call-at (find-thunk prog ℓ) fs

— and a search can fail, so the failure had to be assumed away. With the program
indexed BY LABEL, entering a block is a lookup, and whether the key exists is a
STATE-FREE property of the program: `refs prog ⊆ defs prog`, which is exactly
`LabelsResolvable` (D169, stated at the module level since then, and
`EmittedWF.labels-resolvable` since D100 with no consumer).

No address need ever appear in the general proofs.

`find-thunk` is a linear scan of the program text performed AT EVERY CALL, whose
failure case HALTS the machine — and the real backend does no such thing:

    compile-abstract (instr-load-code-addr n) = lea rax (rip+label n) ∷ []
    compile-abstract instr-call-closure       = call (mem (base+disp r12 slot-size)) ∷ []

`lea rip+label` is resolved by the ASSEMBLER and LINKER; `call *0x8(%r12)` jumps
to an address already in memory. The model defers to call time a resolution the
real pipeline performs once at link time, and an unresolvable label — a LINK
error, as D169's riscv64 note records verbatim — is modelled as a runtime halt.
`block-runs` existed to promise that halt never fires.

The repair is therefore SMALL, and stays in the label world:

  * `CodeWF prog s` — every `SV-Code ℓ` readable in `s`, in REGISTERS as well as
    memory, names a label `prog` defines. Hypothesis determines `ℓ`; conclusion
    is about `ℓ` alone.
  * `apply`/`Out` combine it with `LabelsResolvable` and the correctness family
    to BUILD `CalleeRun`, whose conclusion is already denotational.
  * `block-runs` dies.

Indexing the program by label instead of scanning it may then be an optimisation
of the model rather than a correctness requirement, since `CodeWF` plus
`LabelsResolvable` already give existence.

## D217 — ONE CELL, TWO DENOTATIONS (2026-09-17)

The gate that ends the search for a state-level premise. Verified, not argued:

    valid₀ : ValidAtWF Heap bad-alloc {Unit ⇛ Int} (λ arg → evalᴰ (const fits-int (+ 0) ∘ terminal) (tt , arg)) cloc bad-st
    valid₁ : ValidAtWF Heap bad-alloc {Unit ⇛ Int} (λ arg → evalᴰ (const fits-int (+ 1) ∘ terminal) (tt , arg)) cloc bad-st

Same cell, same state, same label, different denotations, both typecheck.
`Once/Probe/ClosureAmbiguous.agda`; sources archived in
`docs/compiler/probes/closure-ambiguity.md`.

`valid-closure-wf` binds `{body}` and `{body-label}` as free implicits tied to
the state only by `readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label)`,
and `valid-unit-wf` is unconditional — so a Unit-env closure cell says nothing
about the body whatsoever.

### Why this closes the question

`CalleeRuns` needs (1) WHERE the block is — `find-thunk prog ℓ ≡ just j` — and
(2) WHICH function it computes — `evalᴰ body envArg`. A state predicate can give
(1). **Nothing in a state can give (2).** So the search that produced
`block-runs` (D188/D213), `CodeResolves` (D216) and `CodeWF` was looking in a
place where the answer provably is not.

Four attempts, four different reasons, each visible only after the previous died:

    block-runs     state → syntactic, hypothesis determines nothing   FALSE  (D213)
    CodeResolves   state → the body's TEXT                            FALSE  (D216)
    CodeWF         state → the label alone                            sound, WRONG HALF
    BlockAt field  the VALUE carries it                               ← the remaining road

### Where the fact actually lives

Neither the program alone nor the state alone can supply it. The program knows
where block `ℓ` is; the state knows a closure holds `ℓ`; **which body `ℓ` means
is carried by neither.** The two meet at exactly one moment — CONSTRUCTION,
where `curry` / `Ana` / `in-ν` hold both their own label and their own body. So
it belongs on the witness, supplied at construction: `valid-closure-wf`,
`valid-closure-reg-wf` and `valid-ν-susp-wf` each gain a `BlockAt` field, fed
from S2's `BlocksAt` premise — which those three clauses currently discard as
`_` (TwoCell.agda:343, :429; Simple.agda:624). That is what S2 was for.

NOT the field D170 removed: `BodyCorrect` was EXECUTIONAL and made
representation depend on execution, the cycle that forced `ir-size` /
`program-bound`. `BlockAt` is text-vs-label — no execution, no cycle. Precedent
in the same file: `IRResultBase.trace-is-ir-to-trace`.

### Also settled: the label-addressing directive is ALREADY MET

`SV-Code : LabelId → StoredValue FS` (SMCore.agda:226); `find-thunk` returns an
INDEX INTO THE ABSTRACT TRACE, pinned as a `fetch` index by `find-thunk-sound`
(Flat.agda:465), not a machine address; every address is minted arch-side
(`AddrMap.cmap`, `lea rax (rip+label n)`). The general layer is label-addressed
today. Running `exec-flat` on `CompUnit` instead of `link u` would delete
`find-thunk` and retire the relocation development (`Shifted`/`shift`/
`exec-flat-reloc`, `FlatSteps-prefix/-reloc/-middle`, most of `LabelScope`) —
a large PROOF-SURFACE win, but an optimisation, not a correctness requirement.
It also cannot reduce the pc to a bare `LabelId`: `do-call-at` pushes
`suc (fpc fs)` and no label is minted for a post-call point, so the reachable
form is (site, intra-block offset).

### Open, and blocking

Proving `BlockRuns (ir-to-trace ir)` applies `ioc body`, whose own premises
include `BlockRuns (ir-to-trace ir)`. Circular. Two candidate exits — a
depth-indexed family, or a subterm order carried in the field — with different
blast radii. Settle before threading anything.

## D218 — `block-runs` IS DEMOTED FROM CLAIM TO HYPOTHESIS (2026-09-17)

No proof was added. What changed is that the top-level theorem now says what it
actually depends on.

    -- was: unconditional, and VACUOUS — it rested on a refuted postulate
    once-certified : CertifiedBuild

    -- now: conditional, and TRUE
    once-certified : BlockRunsHyp-x86-64 → BlockRunsHyp-x86-32 → BlockRunsHyp-riscv64
                   → CertifiedBuild

`block-runs` is FALSE (D213, machine-checked). An inconsistent assumption proves
everything, so the unconditional reading was worth nothing. It is no longer
postulated anywhere in the tree — it survives only in comments explaining why it
is not — and the evidence is that D213's own probe no longer compiles:

    Once/Probe/ApexInconsistent.agda:28.36-46: error: [NotInScope]
    Not in scope:
      block-runs

**The apex ⊥ is no longer writable.**

### Three separations that had to happen first

D217 forced them, and until they were made every attempted fix aimed at the
wrong one of the three:

* `BlockRuns prog` AS A PREMISE of `IRObsCorrectF` is LEGITIMATE. D188 was right
  to put it there: it is what excludes a fabricated closure, and
  `IRObsCorrectF apply` is ITSELF false without it — a state whose closure names
  an undefined label HALTS the machine on the call while the denotation says
  `f a`.
* The APEX DISCHARGE — claiming the premise always holds — is the false
  statement. That, and only that, is what is demoted here.
* What the discharge needs is BEHAVIOURAL, and no fact about a state can supply
  it (D217: one cell, two denotations). That is plan 0.93's subject.

### Two things the postulate was hiding, both found by threading it

* **There were never one assumption, but THREE.** `BlockRuns` is
  `FrameSemantics`-relative, so the single postulate was standing for x86-64,
  x86-32 and riscv64 simultaneously. `arch-correctness` now forces each target
  to name its own, the same way it already forced per-arch backend witnesses.
* **It reached further than its one call site suggested.** `conc-fuel` — the
  fuel-adequacy postulate in ALL THREE backends — depends on it through `Nof`,
  which computes a step count via `entry-witness`. From the outside that looked
  like a single use.

Neither was visible while it was a postulate. **You cannot tell what an
assumption costs until you make it explicit** — and the contrast with D214 is
exact: there, a parameter threaded through 26 modules turned out to be read
NOWHERE, because it stood for nothing; here, an assumption that looked local is
read in the fuel accounting of every backend.

### On the `public` re-exports this required

Naming a type in a signature N levels up forces a re-export at every level
between — here `ArchCorrectness` and `Once.Compiler`, for three names. That
propagation is exactly the cost plan 0.92 is about, and it sharpens 0.92's rule
into something testable:

> Re-export a name only when a consumer **cannot state its own signature**
> without it. Convenience of use is not a reason; inability to SPEAK is.

`Once.Certified` cannot write `once-certified`'s type without these three, and
the alternative — re-importing `ArchCorrectness` with its twenty-parameter
telescope — is worse. A name used only in BODIES never qualifies, since a body
can import it directly. That rule rules out almost all 345 existing re-exports.

### Status

This is a holding position, not a fix. The hypotheses are discharged by plan
0.93, which rebuilds `ValidAtWF` as a relation recursive on the TYPE (the
`MeaningRelation` shape) rather than a `data` indexed by it. If that lands,
`BlockRuns` disappears entirely and this thread is deleted with it.

## D219 — THE PRODUCT IS WHERE EFFECTS STOP (2026-09-19)

`pair` is PURE-FIXED and `case` is grade-polymorphic. That is not an oversight,
and it is the reason **no `ana` coalgebra can emit**.

### The measurement

```once
pair (compose emit@E id) id
-- expected (Int ω→ Unit) but got Eff Int Unit      -- at EVERY annotation
```

The two rules, side by side (`Judgment.agda`):

```agda
t-pair-morph-check  : ⊢ᶜ f ∶ (A ⇒[Many pure] B) → ⊢ᶜ g ∶ (A ⇒[Many pure] C)
                    → ⊢ᶜ pair f g ∶ (A ⇒[Many pure] (B * C))

t-case-copair-check : ⊢ᶜ f ∶ (A ⇒[Many π] C)    → ⊢ᶜ g ∶ (B ⇒[Many π] C)
                    → ⊢ᶜ case f g ∶ ((A + B) ⇒[Many π] C)
```

`t-curry-check` is pure-fixed too. D066 fixed all three.

### Why the asymmetry is the categorical one

Copairing two effectful arrows is unproblematic — the coproduct runs ONE of
them, so there is nothing to order. `⟨f,g⟩` with both arms effectful must
choose WHICH RUNS FIRST. A category where the tensor is not a bifunctor, and
that choice must be made explicitly (`f ⋉ g` vs `f ⋊ g`), is a **premonoidal**
category; values in a cartesian category plus computations in a premonoidal one,
joined by an identity-on-objects functor, is a **Freyd category**. `arr` was
exactly that functor; D068 retired the term former and kept the map as
`t-subsume`, so the structure is present but implicit.

The product is the one place the cartesian structure genuinely fails for
effects, and `t-pair-morph-check` is where Once stops.

### The consequence, which had not been drawn

* **Effectful ALGEBRAS work.** `cata (case terminal (compose emit@E fst))`
  compiles and emits `5`, `3` against the byte-writing interpretation — `case`,
  not `pair`.
* **Effectful COALGEBRAS are unwritable.** `ana` produces `⟦F⟧T A`, and a
  functor that carries both a payload and a seed is `K X * Id` — a product. So
  an emitting `ana` is not expressible at any useful functor.

This is what blocks the `in-ν` surface test (plan 0.93 §13): the test needs an
`in-ν` layer over an emitting ν child, and there is no way to build one.

### What is NOT yet decided

Whether to make `t-pair-morph-check` grade-polymorphic. The open question is
whether the DENOTATION already sequences the two components in a definite order
— in which case the pure-fixing is a typing restriction over a semantics that
already supports it — or whether an effect order would have to be ADDED to the
spec. That is plan 0.95.

**Relates**: D066 (fixed value-lift / m-pair / m-curry to pure), D068 (`arr`
retired, pure⊆eff is subsumption), D069 (effect-free value intros are
grade-poly), D032 (arrows, not monads), plan 0.93 §13, plan 0.95.

---

## D220 — THE EFFECT TESTS WERE VACUOUS, AND THE FIXTURE IS IN THE WRONG TREE (2026-09-19)

`layer5-cata-list-emit.once` is the north-star effectful-cata test. Its header
says the algebra "invokes the test-local `emit` Emits SigOp once per cons
layer". Built against the byte-writing interpretation it emits **zero bytes**.

### Two independent causes

**1. Bind-and-discard never forces.** The program ends

```once
main = let r = emitAll xs in exit@S 7
```

`emitAll xs` elaborates through `effApp` to a SUSPENSION (`Unit ⇒[eff] Unit`),
`let` binds it, nothing forces it. At `q = Zero` the spec erases the binding
outright (`Denotation/Meaning.agda`, D143). The test passes on `exit@S 7`, which
the program hardcodes.

Moved onto `main`'s composition chain via a top-level def, the SAME computation
emits `5`, `3`. So the machinery works and the test was simply not asking.

This is NOT the D039 optimizer-drops-effects class: it reproduces with
`--no-optimize`, and nothing on the executed path is deleted. What is discarded
is an unapplied morphism, which is cartesian-legitimate.

**2. The observable is a NOP by construction.** `Strata/Interpretations/Test/
Emit.x86_64` is `emit: ret`. Its own `.once` header says "NOT a real Strata
interpretation — exists only so the effect-emitting cata north-star tests can
invoke an effectful op." The byte-writing implementation lives in
`compiler/test/teststrata`, which only `TraceSpec` uses. Every exit-test that
resolves `emit` from `Strata/` therefore cannot observe emission at all, and an
exit code cannot distinguish "emitted then exited 7" from "exited 7".

### The rule

**An exit code is not an effect observation.** A test whose only assertion is a
hardcoded `exit@S N` guards the exit path and nothing else. If a test claims an
effect, it must be built against the byte-writing interpretation and assert the
BYTES — that is what `TraceSpec` does, and why `TraceSpec` never drifted.

Corollary: a test fixture whose runtime is a nop does not belong in the
production `Strata/` tree, where it silently satisfies imports that look like
observations.

**Relates**: D058 (correctness is the effectful-SigOp trace), D114 (the
observable is part of the spec), D039/D056 (the optimizer dropping effectful
SigOps — a different mechanism with the same symptom), D143 (grade-aware
meaning; `q = Zero` erases the bound expression), plan 0.93 §13.

## D221 — `cata-correct` IS FALSE: THE MACHINE FOLDS RIGHT-TO-LEFT (2026-09-19)

**Status (2026-10-09)**: the finding stood until the machine was fixed — plan 0.95 B1 made the fold product-order (code: c95f6a2b2; verdict dad5830d2; D286); `cata-correct` is now an open obligation (plan 0.88), not a false one.

A false postulate, hidden by a vacuous test. This is the defect the whole
verification effort exists to catch, and it survived because the only test that
could see it was asserting nothing.

### The measurement

`node(leaf 40, leaf 2)` over `Mu (K Int + (Id * Id))`, algebra
`case emit@E terminal`, forced on `main`'s composition chain and built against
the BYTE-WRITING interpretation (`compiler/test/teststrata`):

    machine trace = [2, 40]

Deeper, `node(node(leaf 1, leaf 2), leaf 3)`:

    machine trace = [3, 2, 1]        -- a complete right-to-left traversal

### What the spec says

`evalᴰ` routes `Cata` through `seqF` (`DenotTrace.agda:157-158`, `:235-238`):

```agda
evalᴰ fmt (Cata {F} wf {E} {C} alg) a =
  sem-cata (wf-⌈⌉ wf) (cata-ev-algᴰ fmt alg (proj₁ a)) (forget (proj₂ a))

cata-ev-algᴰ fmt alg env fc =
  seqF ⌈ F ⌉F fc >>=T λ layer → evalᴰ fmt alg (env , …)
```

and `seqF` at a product sequences the LEFT component first
(`ValueDomain.agda:135`):

```agda
seqF (G ⊗ H) (x , y) = seqF G x >>=T λ u → seqF H y >>=T λ v → returnT (u , v)
```

with `_>>=T_` concatenating `m`'s events FIRST (`TraceMonad.agda:52-63`):

```agda
(m >>=T f) n = let exr = m n ; eyr = f (proj₂ exr) (n ∸ length (proj₁ exr))
               in (proj₁ exr ++ proj₁ eyr , proj₂ eyr)
```

**Spec order is `[40, 2]`. The machine gives `[2, 40]`.** `Layer5Spec.hs:73`
documents the spec order — `"crown: trace [emit 40, emit 2, exit 7]"` — so the
intent was never in doubt.

### The hiding postulate

`IRObsCorrect/Interface.agda:681`:

```agda
  postulate
    cata-correct : ∀ {F} (wf : WellFormedFI F) {E A} (alg : IR (E * ⟦ F ⟧TI A) A)
                 → IRObsCorrectF alg
                 → IRObsCorrectF (Cata wf alg)
```

`ir-obs-correct (Cata wf alg) = cata-correct wf alg (ir-obs-correct alg)`
(`IRObsCorrectFlat.agda:103`). So the apex is green *because* the one statement
that would have caught this is assumed.

It is now **REFUTED**, not merely open: its conclusion `IRObsCorrectF (Cata …)`
asserts the machine's events agree with `evalᴰ (Cata …)`, and they do not at any
functor with two recursive positions.

### Why it survived

**A one-recursive-position functor cannot see it.** `Mu (K Unit + (K Int * Id))`
— the list — has a single `Id`, so `[5, 3]` is the only order either side can
produce. The list test is green and stays green. Only the two-child crown case
can distinguish, and that test was VACUOUS (D220): built to
`main = let r = emitTree t in exit@S 7`, it emitted zero bytes and passed on its
hardcoded exit code. Its assembly is **byte-identical** (same md5) to
`main = exit@S 7`.

This is the same blind spot D199 named for `Out`: *"both use `Nu (K Int)` — a
functor with NO recursive position … the entire ν test surface was that blind
spot."* The μ side had it too, and for two positions rather than one.

### The rule

**A recursion scheme is not tested until it is tested at a functor with TWO
recursive positions.** One position cannot order anything, so it cannot falsify
an ordering claim. Every scheme — `cata`, `ana`, `para`, `hylo` — needs a
two-child witness, and that witness must assert the TRACE, not an exit code.

### DECIDED (same day, after reading the codegen) — the MACHINE is wrong

The first draft of this entry argued by vote-count ("three left-first choices
against one"). That is not an argument, and the real one is narrower.

**Mathematically, left is NOT forced.** Left-first and right-first are both
lawful traversals — the standard applicative traversal and its `Backwards`
dual. The traversal laws do not decide, and any claim that they do is wrong.

**What decides is that the two products are THE SAME TYPE.** `Type.agda`:

    ⟦ F ⊗ G ⟧T X = ⟦ F ⟧T X * ⟦ G ⟧T X

so a functor-product layer *is* the CCC product. That type is reachable two
ways — built by `⟨f,g⟩` (left-first, and D211 PROVES the machine matches) and
traversed by `seqF`. A right-first `seqF` would give one type two different
effect orders depending on which combinator touched it. That is a fact about
the types, not about which document is privileged.

The asymmetry follows: right-first for `seqF` requires ALSO flipping `⟨f,g⟩`
to keep the product coherent — flipping a proved correspondence and its
emitter — to reach a semantics no more principled than the current one.
Left-first is reachable by fixing ONE codegen clause.

**The convention half.** `pair f g`, written left-to-right, runs `f` first.
The apparent counterexample — `compose f g` runs `g` first, which D056 calls
"source order" — is not one: there `g` feeds `f`, so data flow forces the
order and no convention is being exercised. `pair`'s arms take the same input
and neither feeds the other. The consistent rule is: **effects follow data
flow where data flow exists; where it does not, they follow reading order.**

**The site** (plan 0.95 B1). `visit-walk` at a product visits `G` (right) then
`F` (left) (`IRToTrace.agda:165-169`); `rebuild-walk` visits `F` then `G`
(`:181-189`) — one inversion apart against a LIFO stack. `rebuild-walk`'s own
comment reads *"popping one value-stack result per Id position,
LEFT-to-RIGHT"*, so the codegen intends the spec's order and delivers its
mirror. Measured at four shapes the divergence is an EXACT mirror every time
(`[1,2,3,4] → [4,3,2,1]`; a left-leaning and a right-leaning three-leaf tree
both give `[3,2,1]`), which is what a single product-order inversion looks like
and rules out a structural defect.

**Relates**: D220 (the vacuous test that hid it), D219 (the product's effect
order), D211 (`obs-correct-pair` proved, left-first), D199 (the same blind spot
at ν), D058 (correctness IS the effectful trace), D132 (per-shape cata witnesses
were never going to be the theorem).

## D222 — READ THE GRADE OFF THE DENOTATION: `pair` SHARES ONE π, `curry` HAS TWO (2026-09-20)

The design call plan 0.95 A owed, made from what the terms MEAN rather than from
what the elaborator happens to accept.

### The two denotations, side by side

```agda
evalᴰ fmt (⟨ f , g ⟩) a = evalᴰ fmt f a >>=T λ b → evalᴰ fmt g a >>=T λ c → returnT (b , c)
evalᴰ fmt (curry f)   a = returnT (λ b → evalᴰ fmt f (a , b))
evalᴰ fmt apply       p = proj₁ p (proj₂ p)
```

**`pair` runs its arms when the pair's arrow is applied.** Both arms' events land
in that application's trace, in order. So the arms and the result arrow all
carry the SAME grade — one shared `π`, exactly as `t-compose-check` and
`t-case-copair-check` already have it.

**`curry` runs nothing.** `returnT` — building a closure emits `[]`, always, for
any `f`. The body's effects are deferred and fire at `apply`, which is reached
through the INNER arrow. So:

    outer arrow  — EFFECT-FREE. Grade-poly (free π), per D069's rule for
                   effect-free intros: a free index, not pure-fixed + subsume.
    inner arrow  — carries the BODY's grade π′.

**Two independent purities, not one.**

    t-curry-check : ∀ {π π′}
      → ⊢ᶜ f ∶ ((A * B) ⇒[ mk-kind Many π′ ] C)
      → ⊢ᶜ curry f ∶ (A ⇒[ mk-kind Many π ] (B ⇒[ mk-kind Many π′ ] C))

### This is the closed-Freyd structure, and it is forced

In a closed Freyd category (Power–Thielecke) the exponential is the KLEISLI
exponential, and currying is an isomorphism

    Hom_C(A ⊗ B, C)  ≅  Hom_V(A, B ⇒ C)

landing in the VALUE category. Currying a computation yields a VALUE — an
effect-free map into an object of computations. That is `returnT` in the
denotation, and it is why the outer arrow cannot be where a grade lives.

### The current rule has it BACKWARDS, measured

`checkCurry` (Elaborate.agda:1511-1524) accepts exactly two shapes, and the body
is checked at `pure` in BOTH:

    k : Int -> (Int -> Int)          curry fst                     ACCEPT
    k : Eff Int (Int -> Int)         curry fst                     ACCEPT   (outer eff, via t-subsume)
    k : Int -> Eff Int Unit          curry (compose emit@E fst)    reject   <- THE MATHEMATICAL CASE
    k : Eff Int (Eff Int Unit)       curry (compose emit@E fst)    reject

`eff` is accepted where nothing happens and rejected where the effects are. An
effectful body can never be curried.

### THE GENERAL RULE, and why this is plan 0.94's disease in a second shape

D066 justified pure-fixing `m-pair`/`m-curry` with four words: *"`checkElab`
paths are pure-fixed"*. That is a statement about the IMPLEMENTATION, offered as
a reason for the RULE. `composeMid` sits in `t-compose-check` for the same kind
of reason — the elaborator needed a syntactic search, so the search became a
premise.

Both are **the elaborator's limitations leaking upward into the specification.**
Plan 0.94's rule — *every premise of a typing rule must be a judgment, not a
computation on syntax* — is the PREMISE-shaped instance. This is the
INDEX-shaped one. The rule that covers both:

> **The typing rule states the mathematics. The elaborator's job is to FIND
> derivations, not to decide which ones exist.**

The confirmation that it is one disease and not two: the curry grades are
backwards relative to `evalᴰ` and nobody noticed for a year, because the rule
was written from the elaborator instead of from the denotation.

### Consequence

The answer is NOT "make everything grade-poly". `pair` gets one shared `π` and
`curry` gets two independent ones, and the difference is visible only in their
denotations. Every remaining grade decision should be read off `evalᴰ` the same
way.

**Relates**: D219 (the product is where effects stop), D066 (pure-fixed, with
the implementation note this corrects), D068 (`arr` retired; pure ⊑ eff is
subsumption), D069 (effect-free value intros are grade-poly — the rule applied
here to `curry`'s outer arrow), D018/D032, plan 0.94, plan 0.95 A.

## D223 — PLAN 0.91 CLOSES; ITS REMAINING STEPS WERE ALREADY REASSIGNED (2026-09-21)

Plan 0.91's thesis — PROGRAM FACTS BELONG IN THE OBLIGATION — held, and it is
what made D216 findable. The plan closes; the thesis does not.

### What landed

* **S1 (D214)** — `entry-size` deleted apex-to-leaf; `program-bound` was never
  fuel, and `ir-size` became unreachable from the apex.
* **S2 (D215)** — `BlocksAt` entered `IRObsCorrectF` across 28 sites.

### S3 is DEAD, not deferred

D216 says so in those words. The consumer half cannot be done as designed:
`obs-correct-apply`/`-Out` were to take their block resolution "from the witness
instead", but `block-runs` is the ONLY producer of a `CalleeRun` in the
development — `grep -rn 'callee-run'` returns exactly one hit, the constructor
declaration at `Interface.agda:487`, never applied. A witness supplies LAYOUT
where a BEHAVIOURAL fact is needed.

### S4 and S5 have live successors, by name

* **0.91 S4 → 0.93 S5.** `BlockRuns` does not narrow; under the relational
  architecture it is deleted outright, with `ValidAtWF`, `MachineRefinesObsF`,
  `ValueRealized`, `CalleeRuns`, `CoalgRuns` and `block-runs`.
* **0.91 S5 → 0.93 S4.** *"every block the emitter produced is placed at its
  label in the linked image … the induction D188 called provable and nobody
  wrote"* — 0.91 S5 verbatim. Plan 0.93 §11 already recorded that 0.91's S1/S2
  survive and that the `BlocksAt` premise "becomes S4's statement".

### What 0.91 left behind, and where it got to

`entry-blocks` — and it is no longer a postulate. It is a DEFINITION resting on
one named fact:

    span         PROVED   blocks-placed / blocks-placed-linked / span-shift
    resolution   PROVED   ft-hit / block-resolves
    composition  PROVED   blocks-at
    scan→list    PROVED   no-thunk-miss / missBefore-from
    ThunkScope   21 of 22 constructor clauses PROVED
    entry-no-thunks + cata-thunks-in   the residuals

D168's `link-pre`/`link-post`/`link-block-split` were NOT needed. The comment in
`FlatFromObs` predicted this induction would be "the first REAL demand for that
machinery"; `blocks-placed` goes through by direct induction on the block list,
so the prediction was wrong and the machinery stays unexercised there.

### The finding the plan did not anticipate

Mapping S3–S5 surfaced that `Once.Certified` was INCONSISTENT:
`DenotPrefix.agda:151` carried `postulate evalᴰ-good-schemes : ∀ {X : Set} → X`,
reached from the apex through `FlatFromObs`'s use of `evalᴰ-good`. Machine-checked
with two ⊥-probes; now eight named per-constructor postulates with three
discharged. That is the plan's own thesis working in a direction it did not
predict — the obligation was hiding a program-INDEPENDENT falsehood rather than
a missing program fact.

**Relates**: D213 (the refutation that opened 0.91), D214, D215, D216, D217,
D218, plan 0.93 (S4/S5's live home).

## D224 — THE PURE EVALUATOR IS REFUTED, AND `Para`/`Hylo`/`Fuse` GO WITH IT (2026-09-23)

**Relates**: D054/D113 (`⟦ Void ⟧`), D060 (one denotational meaning), D062
(`para`/`fuse` are derived), D072/D179/D180 (the `T` monad), D214 (`ValidityDef`
measured dead), plan 0.68 step 5 (class G), plan 0.79 §1 (where the laws live),
plan 0.64 Group O (the optimizer chain), plan 0.98.

### The refutation

    eval : ∀ {A B} → IR A B → ⟦ A ⟧ᴵ → ⟦ B ⟧ᴵ

is not merely awkward once `Halts : B ≡ Void` (plan 0.98). It is **FALSE**.
`⌊ Void ⌋ = Void` (IRTy.agda:120) and `⟦ Void ⟧ = ⊥` (Semantics/Value.agda:126),
so `eval fmt (SigOp si)` at a halting `si` must produce `⊥` from an inhabited
domain. No total function of that type exists.

It typechecked for a year only because `Halts` carried `B ≡ Unit` and the clause
returned `tt` — **the pure model's own statement that `exit` returns**. That is
the same falsehood plan 0.98 exists to remove, one layer down from where 0.97
found it.

### Why DELETE rather than repair — and the plans decide it, not effort

Repairing means `eval` lands in `Res`. That forces
`Val.⟦ A ⇒ B ⟧ = ⟦A⟧ → Res ⟦B⟧` (Semantics/Value.agda:133-135), because
`eval (curry f) x = λ y → eval f (sem-pair x y)`. And `⟦_⟧ᴰ` **already** has
`T`-valued exponentials. So repair builds a second, strictly poorer Kleisli
model beside the one that exists — it entrenches the duplication D060 named and
0.98 exists to remove.

Two plans settle where the consumers go, and the second is decisive:

  * **plan 0.79 §1** splits the laws into two families and assigns each a
    semantics — source-level over the spec's own denotation, IR-level over
    **`evalᴰ`**, "the trace semantics, the ONE model". It says of the module in
    question: "`Category.Laws` is neither: IR-level, but over the disowned
    `eval`."
  * **plan 0.64 Group O** is where they get wired, and the apex obligation is

        opt-trace : … → ∀ n → exec arch (string-to-bytes arch asm) n
                            ≡ ⟦ just ir ⟧IR … n

    `⟦_⟧IR` is the TRACE meaning. So optimizer correctness must be a trace
    statement, and **laws stated over `eval` could never discharge it, however
    well repaired.**

Plan 0.93 §8 lists `evalᴰ` and the `T` monad under "Survives untouched". Nothing
that should exist wants `eval`.

### What went with it, and why it is the same decision

`appNatTr-F`'s only non-structural leaf is

    appNatTr-F fmt (ntK ir) a = eval fmt ir a          -- Eval.agda:81

on an ARBITRARY IR morphism — and `NatTr`'s own header calls that leaf "a pure
constant map", an intent no type enforces. `NatTr` exists only to be carried by
`Hylo`/`Fuse`. So the cluster is one decision: `Para`, `Hylo`, `Fuse`, `NatTr`,
`appNatTr-F`, `eval`.

D062 already pointed here — "`para`/`fuse` are derived, not primitive, so the
IR's five-scheme zoo collapses toward `cata`/`ana`/`hylo`", and "deforestation
stays an optimization: `fuse` is re-added to the IR only as a refinement proven
equal to `hylo`". **This goes one step further than D062 by dropping `hylo`
too**, and the reason is representational rather than schematic: `hylo` is the
constructor that CARRIES the `NatTr`. Nothing is lost in expressiveness —
a `NatTr`-shaped coalgebra is exactly D062's auto-derivable `hyloS`, and
`Cata`/`Ana` express the same fold and unfold. What is lost is the FUSED LOOP,
which D062 already classifies as an optimization rather than a scheme.

### The accounting: 23 constructors -> 20, and the recursion layer became SYMMETRIC

    12  CCC generators (D001)  id ∘ ⟨,⟩ fst snd inl inr case terminal initial curry apply
     6  structured recursion   In out-μ Cata | in-ν Out Ana
     1  const                  a global element 1 → A
     1  SigOp                  the inclusion of the signature Σ (D047)

The six are 3 + 3 — introduction, Lambek inverse, and scheme, once per side:

    μ :  In     out-μ   Cata
    ν :  in-ν   Out     Ana

Before this entry the layer was NINE and asymmetric: μ carried a fourth (`Para`)
that ν had no dual for, and `Hylo`/`Fuse` straddled the two without belonging to
either. The symmetry is not decoration — it is what "μ and ν are dual" looks
like when the derived schemes stop being primitive.

### SIX POSTULATES GO, and one of them is plan 0.68's own option

    IRObsCorrect/Simple    obs-correct-Para, obs-correct-Hylo, obs-correct-Fuse
    Denotation/DenotPrefix evalᴰ-good-Para, evalᴰ-good-Hylo, evalᴰ-good-Fuse

The first three are plan 0.68's CLASS G, whose comment states the fork exactly:
"the emitter is missing … each compiles to `[]`, so the obligation is REFUTABLE
whenever the denotation emits an event. NOT a proof task: implement the codegen,
**restrict the IR so they cannot be built**, or condition the obligation to
exclude them (Plan 0.68 step 5, and it needs a decision-log entry either way)."

This is that entry, and it takes the second option for the three of the five
that are derived schemes. `in-ν` remains in class G and is a real codegen gap.

### What the deletion DISSOLVED rather than cost

Of ~38 modules importing `Once.CCC.Eval`, **nine** used a name from it, and only
two names — `⟦_⟧` (a re-export of `Semantics.Machine`) and `eval`. The rest were
dead imports, the `feedback_verify_consumers_not_importers` shape. Then:

  * `ClosureWellFormed` and `IRObsCorrect/Interface` each DEFINED an `eval`
    alias and never used it;
  * `DenotPrefix` imported `eval` and never used it;
  * the only real consumer was `ValidityDef` — which **D214 had already measured
    dead**: "re-exported by `IRObsCorrect/Prelude` and instantiated by NOTHING.
    Dead by the consumers-not-importers test. Separate cleanup." This is that
    cleanup, forced rather than chosen. `Validity.agda` 433 -> 78 lines, keeping
    `ReadLocEq`, the part four modules actually take from it.
  * `CCC/IR/Totality` and `CCC/IR/Productivity` (green islands) proved
    `eval-total` — that the deleted function is total. Deleted with it.

The machine is untouched, as plan 0.98 §4 predicted. `semM`'s `Res` is eliminated
once, at `SMCore.res-sv`, where a stopped result takes the same
`unit-storedvalue` sentinel the unreadable-input row already takes: writing the
Output register is an ABI fact, not a semantic claim.

### The honest cost

Four modules stated over `eval` go red at their USE sites — `Category/Laws`,
`Optimize/Correct`, `Optimizer/Normal`, `Fusion/Correct`. All four were ALREADY
red (plan 0.64 Group O, M2 rot since plan 0.52), so nothing measurable
regressed; their `⟦_⟧` now comes from `Semantics.Machine` and the red lands at
each use, which is the work-list Group O needs. Restating them over `evalᴰ` is
Group O's job and is what plan 0.79 §2 already owes an answer for.

Deforestation has no IR constructor until someone re-adds `fuse` as a proven
refinement (D062's own terms).

### METHOD NOTE — deleting BY LINE is unsafe, and the audit is what saved it

The sweep was wrong twice, both times structurally:

  * **One line, several names.** `IRHead`'s constructor list puts nine tags on a
    single line, so removing that line took `h-In`, `h-out-μ`, `h-Cata`,
    `h-Out`, `h-in-ν` and `h-Ana` — all LIVE — with it.
  * **One-line head, multi-line body.** `≟IRH-diag (Para …)` has a one-line
    clause head and a six-line `with` body. Deleting the head left the body
    orphaned; it surfaced only as a `ParseError` several edits later.

Both were caught by the same check, and it is cheap: **diff every removed line
that does NOT mention a deleted name.** Everything legitimate in that list is a
continuation of a deleted block; anything else is collateral. A second scan —
for a `with`/`...` block that follows a blank line — finds orphaned bodies.

Substring-anchored region cuts also failed repeatedly on this tree's mixed
spacing (`walk (Hylo w₁ w₂ f g)  =`). Multi-line regions were done by explicit
LINE RANGE instead, computed from a grep and applied high-to-low.

## D225 — THE SPEC READS THE CODOMAIN: AN EFFECTFUL ARROW INTO `Void` HALTS (2026-09-24)

**Relates**: D060 (one denotational meaning), D224 (no total function into `⊥`),
plan 0.98 §0/§2/§9.6 (stage E: the elaborator reads the codomain), Once.Spec
closure via `Denotation/Meaning` → `Arith/SigOp/Builders.arrow-info`.

### The finding

Stage E made the ELABORATOR dispatch an effectful SigOp on its codomain —
`Void` HALTS, `Unit` EMITS, anything else is a value contract. The SPEC did not
move: `arrow-info-eff` split only on `isUnit? B`, so an effectful op into `Void`
denoted as `value-info` — a pure function `⟦ A ⟧ → ⟦ Void ⟧ = ⊥`, whose only
source is the `generic-semM` postulate. `RealizeAgrees.masq` was therefore FALSE
at `Void` (the elaborator said `stopped`, the Spec said "returns a value of ⊥"),
which is D060's "ONE meaning, two presentations" failing one layer below where
plan 0.98 §1 found it.

### Why this is not a choice

`⟦ Void ⟧ = ⊥`, and an effectful result lives in `Res X = stopped | returns X`.
`Res ⊥` has exactly ONE inhabitant, `stopped`. So up to its trace an effectful
arrow into `Void` has exactly one meaning: it stops. Categorically it is a
Kleisli arrow `A → T 0`, which exists only because the monad can abort, and can
only abort. This is the reading `exit`-like primitives have across typed
languages (`!`, `Nothing`, `never`). Any other Spec meaning at `Void` must be
"inhabited by fiat" (plan 0.98 §2) — i.e. rest on an axiom that proves ⊥.

### The change

`arrow-info-eff : CanonicalName → Dec (B ≡ Void) → Dec (B ≡ Unit) → …`,
dispatched from `arrow-info` with `isVoid? B` then `isUnit? B` — the same pair,
in the same order, that `ext-resolved-info` hands `ext-resolved-info-aux`. The
two infos now agree clause by clause (`RealizeAgrees.info-agree`, three `refl`s)
and `masq`'s three-way `lookupSigEffect` split (`masq-unit`) is deleted.

### Left open

`generic-semM : ∀ {A B} → String → TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧` still
derives ⊥ at `B = Void` (`generic-semM {Unit} {Void} "exit" tn tt : ⊥`
typechecks; present on master since plan 0.2.4.1). D225 removes the Spec's USE
of it at `Void` on the effectful path, not the postulate's type. Fixing the type
(land it in `Res`, as `semM` did) is its own plan.

## D226 — ONCE HAS ONE SUBTYPING JUDGMENT (2026-09-25)

**Status**: Accepted; implementation in plan 0.99.
**Relates**: D068 (`t-subsume`, `arr` retired), D069, D125 (subsumption belongs in
CHECK mode; `Int`→`Float` stays local), D219 (Freyd structure), D225, plan 0.94
§2/§4, plan 0.98 stage E.

### Context

0.98 stage E needs `exit : Eff Int Void` to be usable where `Unit` is expected
(`main = exit@S (g 42)`, ~95 programs). A second standalone subsumption rule
beside `t-subsume` would work, and would be the second special case of a
structure Once does not state.

### Decision

One judgment on types, `A <: B`, and one check-mode rule
`t-sub : ctx ⊢ᶜ e ∶ A ⨾ Ψ → A <: B → ctx ⊢ᶜ e ∶ B ⨾ Ψ`, replacing `t-subsume`.

**Admission criterion**: a generator enters `<:` iff its conversion is CANONICAL
(forced, not chosen) and OBSERVATION-FREE (can never lose anything observable).
Admitted: `Void <: B` (`¡`, unique and vacuous) and the grade `pure ⊑ eff` (the
Freyd embedding; erased by `⟦_⟧`). Rejected: `A <: Unit` (`!` is unique too, but it
ERASES a value and breaks linearity) and `Int <: Float` (chosen, and not injective
at fixed width — D125 stands). Closed under the type formers: arrows contravariant
in the domain and covariant in the codomain and grade, products and sums
covariant; `μ`/`ν` reflexive only; quantities not varied.

**Coherence by construction**: the rules are syntax-directed with no transitivity
rule, so each `A <: B` has at most one derivation (`<:-unique`). Transitivity is
admissible. Every derivation therefore denotes the same conversion, which is what
makes an IMPLICIT conversion sound (Reynolds; Curien–Ghelli).

**Inference is untouched**: `⊢ᵢ` reports the least (principal) type; conversion
happens only in checking mode (D125). Every premise is a judgment on types, never a
computation on syntax (plan 0.94 §2). The non-unique middle type plan 0.94 §4
flags becomes harmless: all choices denote the same map, and the principal one is
the elaborator's.

### Why `Void`, not a polymorphic `∀B`

A family of maps `A → T B` natural in `B` is, by Yoneda, the same thing as one map
`A → T 0`: `Void` is the representing object. So `Eff Int Void` is the canonical
single statement of "never returns", `<:` supplies the instances, and FFI
signatures keep concrete codomains.

### Amendment (2026-09-25, plan 0.99 phase B): the rule sits at the MODE SWITCH

As first written, `t-sub` took a CHECKED premise (`⊢ᶜ e ∶ A`), like `t-subsume`.
That is wrong once `<:` has a contravariant domain: the judgment would derive
`\x -> x + 1 ∶ Void ⇒ Int` (check the lambda at `Int ⇒ Int`, convert the domain),
and no checker can find it — checking the lambda at `Void ⇒ Int` binds `x ∶ Void`,
and `x + 1` then fails. `check-complete` would be false.

The rule is therefore the standard bidirectional subsumption (Dunfield–Krishnaswami),
at the switch from inference to checking — which is also what "inference reports the
principal type; conversion happens only where the expected type is known" says:

    t-sub : ctx ⊢ᵢ e ∶ A ⨾ Ψ → A <: B → ctx ⊢ᶜ e ∶ B ⨾ Ψ

Consequences, each a Spec-closure hunk:

* `t-embed` is DELETED: it is `t-sub` at the reflexive derivation.
* `t-subsume` is DELETED: at an inferred term it is `t-sub` at the grade derivation;
  its other use, lifting a CHECKED lambda, is taken over by —
* `t-lam` is GRADE-POLY (`mk-kind q π`, π free), D069's principle applied to
  abstraction, which introduces no effect. Every lambda was typed `pure` and lifted by
  `t-subsume` before, so this derives exactly those typings. Surface `lam` is
  grade-poly with it; `⟦_⟧ᴰ` and `⌊_⌋` already ignore the grade.
* Surface `arr'` is replaced by `coerce p e` (the realisation of `t-sub`); its IR is
  `coeIR p`, which is the IDENTITY (`idC`) for every grade-only derivation, so no
  existing program's IR changes.
* Every check rule that concluded at an arrow is already grade-poly (`t-pair-morph-check`
  since D222; compose/case/cata since D032), so the elaborator's "try eff, else check at
  pure and lift" fallbacks are deleted: the eff attempt covers them.

## D227 — THE EFFECT ANNOTATION IS DELETED; `exit` RETURNS `Void` (2026-09-25)

**Relates**: D225, D226, plan 0.98 §3 ("What this DELETES") and stage E, plan 0.99
phase E.

With D225 (the Spec reads the codomain) and D226 (`Void <: B` at the mode switch),
the `! halts` / `! emits` signature annotation and the name-keyed table it filled
(`SigEffect`, `SigEffectCtx`, `lookupSigEffect`, `collectSigEffects`,
`NamedCtx.sigEffects`) had no reader left. They are deleted.

Spec-closure hunks, each justified by this entry:

* `Spec/Grammar/Signature`: `ParsesEffAnnot` is gone; `psig-mk` concludes at the
  token remainder after the type. `! halts` is no longer syntax (a signature ending
  in it is a parse error).
* `Spec/Module`: `AllFunsTyped` loses its `sigEffs` index; the body context is
  `ctxWithImportsAndSelfAndPolys ctx polys name ty`.
* `Spec/Resolution`: `DSignature` is ternary (`name owner type`).

Sources: `Strata/Interpretations/Linux/Syscalls.once` declares
`exit0 : Eff Unit Void` and `exit : Eff Int Void`. `main = exit@S (…)` at
`Eff Unit Unit` checks by `Void <: Unit` under the arrow (D226). `ParseSpec`'s
annotation test is replaced by a `Void`-codomain test and a rejection test.

## D228 — `cata` IS AN ELIMINATOR, SO IT SYNTHESIZES; `t-sub` STAYS THE ONLY CONVERSION (2026-09-25)

**Status**: Accepted; implementation in plan 0.94 (phase C′, "b′").
**Relates**: D226 (one subtyping judgment; `t-sub` at the mode switch), D068
(`t-subsume`, the Freyd embedding `J`), D219/D222 (Freyd structure), plan 0.99 §8,
plan 0.94 §3 (the domain-given, codomain-synthesized mode).

### The finding

D226 put conversion at the switch from inference to checking (`t-sub` takes an
INFERRED premise), which is what keeps `check-complete` true. The old `t-subsume`
lifted ANY checked pure morphism to eff — the Freyd embedding `J` applied to a
checked derivation. Every check rule whose type is covariant in the raised grade
still admits that lift (lambdas and the combinators are grade-poly), but `cata` is
checked with an INVARIANT carrier (`⟦F⟧ A ⇒ A`), so

    (cata alg) x   checked at   X ⇒[eff] B,   the fold's result a pure arrow,

has a meaning and no derivation. The MODEL is still a Freyd category (meanings are
unchanged; `J` is the identity on meanings); what is lost is the typing rules'
completeness with respect to `J`. `ana` does not hit this corner: it is an
introduction, its result `νF` is not an arrow, and its carrier is its domain,
which converts only at the mode switch. (Raising grades NESTED inside types fails
for both, in the old system as well.)

### Decision

The cause is treating `cata` as check-only, as if it were an introduction. It is
the ELIMINATOR of `μF`: by initiality `cata alg` is the unique morphism `μF → A`
determined by its algebra, so its type is DETERMINED — `F` by its argument, the
carrier `A` by the algebra — and the bidirectional principle is that eliminations
synthesize. So:

* `cata`, given its domain `μF` (from the argument, or the expected arrow),
  SYNTHESIZES its result from a synthesizing algebra; `t-sub` then does every
  conversion. The corner is derived through the one existing mechanism.
* An algebra that does not synthesize (an unannotated lambda) is a type error that
  asks for an annotation, and the TYPING RULES state that requirement (the
  synthesis rule's premise is a synthesizing algebra), so `check-complete` stays
  true. The existing check-at-a-given-carrier rule is kept.
* NO separate grade rule (`t-grade`) and no interim stopgap: it would be a second
  conversion mechanism that this decision then makes redundant. The corner stays
  open until plan 0.94 phase C′ lands.
* This is the domain-given, codomain-synthesized mode plan 0.94 §3 already needs
  for `compose`, applied to `cata`; hence it lives in plan 0.94.
* Runtime is unchanged: the conversion involved is grade-only (void-free, no code)
  and `cata` still compiles to `IR.Cata`; the elaborator's synthesis path must emit
  the SAME term as the checking path.

## D229 — ELIMINATIONS CONSUME THEIR PRINCIPAL ARGUMENT UP TO SUBTYPING (2026-09-25)

**Status**: Accepted; implementation in plan 0.94 (phase A′).
**Relates**: D226 (subsumption at the mode switch), D228 (`cata` synthesizes), plan
0.94 §9 (the middle type needs narrowing), System F<:'s narrowing lemma.

### Decision

The typing judgment is to have the standard metatheory of subtyping as THEOREMS:
subsumption (D226), NARROWING (this entry) and substitution (plan 0.94). A
derivation denotes a morphism `⟦Γ⟧ → T⟦A⟧` and `A <: B` a coercion, and the
semantics is closed under post-composition (subsumption) and pre-composition on the
context (narrowing); the judgment presents it faithfully only if it is closed too.

Narrowing fails today because twelve eliminators demand their principal argument at
an EXACT shape, while two of `<:`'s generators do not preserve shape: `Void` sits
below every shape, and `pure ⊑ eff` changes an arrow's grade. So every eliminator
infers its principal argument and matches it UP TO `<:`:

* **Grades.** An eliminator that needs an `eff` head accepts any grade `π ⊑ eff`
  (`t-effApp`, `t-apply-eff-app-infer`); `pure`-requiring eliminators are unaffected
  (narrowing only lowers grades).
* **`Void`.** An eliminator whose principal argument synthesizes `Void` synthesizes
  `Void` (`¡` is unique, so this is canonical), and places NO requirement on its other
  subterms. That is ex falso: a `Void`-typed principal argument means the term
  denotes `¡` and the other subterms are dead. Requiring them to type would break
  narrowing (their expected types came from the non-`Void` shape) or force the
  checker to guess. Consequence, stated because it is visible: with `x ∶ Void`,
  `x + "s"` and `case x of …` with ill-typed branches are accepted, and mean `¡`.

Every principle lines up: eliminations consume their principal argument up to
subtyping; introductions check; conversion happens at the mode switch. Meanings and
runtime are unchanged.

### Amendment (2026-09-25): NARROWING FOR `Void` ONLY — grades are not narrowed (β)

The grade bullet above is WITHDRAWN. Application's result type depends on the
head's grade: `t-app` (pure head) gives `f x ∶ B`, `t-effApp` (eff head) gives the
suspension `f x ∶ Unit ⇒[eff] B` (D018). Lowering a variable from `eff` to `pure`
changes that result's TYPE with no conversion between the two (`B </: Unit ⇒[eff] B`),
and letting `t-effApp` also accept pure heads would give `f x` two inferred types,
breaking the uniqueness `TypeCheck/Determinism` proves.

So narrowing is a theorem for `Void` only: `Γ , x ∶ A ⊢ e ∶ T` and `Void`-narrowing
(`x ∶ Void`) gives `Γ , x ∶ Void ⊢ e ∶ T`. Grades are never lowered by the checker;
where plan 0.94 chooses a middle type, the grade is the one the programs fix. This is
all 0.94 needs (`compose f initial`).

Open for later (not decided): grade narrowing as a theorem. Two routes, each
reversing an earlier decision — (α) admit `B <: Unit ⇒[eff] B` (the Kleisli unit `η`;
reverses D127's removal of value-as-arrow lifting), or (γ) redesign effectful
application as sequencing instead of suspension (reopens D018).

### Amendment 2 (2026-09-26): the other subterms STILL SYNTHESIZE; usage is the nullary sum's

The "no requirement on its other subterms" clause above is WITHDRAWN (option (a)):
every subterm of a `Void`-principal elimination must still synthesize. Nothing
untyped stands inside a typed program, and no type is invented.

Usage follows from QTT, not from a new rule. A sum's eliminator consumes its
scrutinee plus the JOIN of its branches (`t-case`: `Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)`), because
exactly one branch runs. `Void` is the NULLARY sum, whose eliminator `¡` has no
branches, so the join is over nothing: zero. Hence the rule (i):

* a subterm evaluated up to and including the `Void` principal counts as usual;
* what the `Void` eliminator discards counts zero —
  `f x` with `f ∶ Void`: `x` counts zero; `v + e` with `v ∶ Void`: `e` counts zero;
  `e + v`: `e` ran first and counts; `case v of …` with `v ∶ Void`: the written
  branches are typed (their binders at `Void`) and count zero.

A right-operand rule requires a non-`Void` left operand, so each term has one
synthesized type and one usage (uniqueness of synthesis, `ModeAgreement.agree-ii`).
Once's quantities form the chain `0 ≤ 1 ≤ ω`, so the narrowing lemma says narrowing
never INCREASES usage. Rejected (ii): reading `v ∶ Void` as `Void + Void` and joining
the written branches — it keeps a `case`'s usage under narrowing, but an absurd head
`f x` has no arrow quantity to multiply `x` by, so usage cannot be preserved in general
anyway.

### Amendment 3 (2026-09-26): point-free arms under a `Void` input COUNT (A)

The domain-given mode needs `Void`-input rules for its eliminator combinators (`fst`,
`snd`, `case f g`, `cata alg`), because the spine hands a narrowed argument's type to the
head. Their ARMS are built when the arrow is built, before any input (D131), and building is
observable (an arm can halt); narrowing is PRECOMPOSITION with `¡` on the input and cannot
change what happens before an input arrives. So the arms are typed, emitted and counted.
The single rule behind every case: usage is what evaluation REACHES. Emitted as
`snd' (pair a b)` — evaluate both, keep the second — so no new term former is needed; a
`cata`'s closed algebra is embedded the way a definition's body is (`embedClosed`).
Rejected (B): arms count zero — it would change a narrowed program's meaning.

## D230 — THE SPINE MODE: ARGUMENT-DRIVEN APPLICATION IS AN INFERENCE, `t-arg-driven-app-check` IS DELETED (2026-09-26)

**Status**: Accepted; implementation in plan 0.94 (phase C).
**Relates**: D134 (deciders are not typing rules; `compose`'s free middle owes
coherence and a restated completeness), D226, D228 (`cata` synthesizes), D229,
plan 0.94 §3 and §10, plan 0.4-T2 / 0.55 (the `arg-driven` completeness gap).

### The finding

With `compose`'s middle type locally determined by two routes (`g` given its input,
or `f`'s synthesized input), `check-complete` needs the standard bidirectional
property CHECKING AGREES WITH INFERENCE: if a term infers `T` and checks at `U`,
then `T <: U` with the same usage. That holds when the rules are MODE-CORRECT
(Pfenning's recipe: introductions check, eliminations synthesize), i.e. when no
check rule applies to a term that also infers. Exactly one rule breaks it:
`t-arg-driven-app-check`, which CHECKS an application `f x` (inferring `x`, checking
`f` at `X ⇒ T`) even where `t-app` infers it — the overlap behind the long-standing
postulate `completeness-gap-arg-driven-app-check`.

### Decision

The domain-given judgment `⊢ᵈ` ("given its input, this term's output is determined")
gets a rule per combinator — inferable term, lambda, `compose`, `case`, `pair`,
`id`/`fst`/`snd`/`terminal`, `initial` (output `Void`), and `cata` (D228, phase C′) —
and argument-driven application becomes a mode-correct INFERENCE rule:

    ctx ⊢ᵢ x ∶ X  →  ctx ⊢ᵈ f ∶ X ⇒[pure] ↦ T  →  ctx ⊢ᵢ f x ∶ T

`t-arg-driven-app-check` and its postulate are DELETED. Where `f` also infers, the two
applications agree (same type — `d-infer` reads `f`'s own codomain — and same usage,
because `⊢ᵈ` fixes the arrow at `Many`). Checking-agrees-with-inference becomes a
theorem, both `compose` routes become complete, and C, C′ and argument-driven
application are one mechanism.

Cost, stated: a head whose output its input does not determine (`curry g`, a lambda
returning a lambda) applied in argument-driven position now needs an annotation, where
before the check target typed it — the local-inference trade D-entry 0.94 §10 already
accepted for `compose`.

Coherence: where derivations overlap, the meaning agrees by `realize-invariant` (A4),
itself still a postulate; removing ALL postulates includes proving A4.

## D231 — THE SPEC IS A CORE CALCULUS; THE COMBINATORS ARE ITS DEFINITIONS; TERMS CARRY AN EFFECT GRADE (2026-09-26)

**Relates**: plan 0.102 (phase A), OCP-0009 (POC plan §9, the `Spec/Kernel` breakout),
D032/D046/D068/D069/D222/D225 (effects on arrows), D127 (combinators linear in their
arms), D131 (an algebra is obtained once), D143 (grade-aware meaning), D226 (coercions).

### Context

The Spec's typing judgment is the bidirectional algorithm (`⊢ᵢ`/`⊢ᶜ`/`⊢ᵈ`) over named
raw syntax, with one primitive rule per combinator per mode. Every property the model
gives for free (substitution, let = def, narrowing to `Void`) became a per-rule, per-mode
obligation (plan 0.94). OCP-0009 prescribes the fix for its dependent kernel: the Spec is
a declarative core, and bidirectional checking is an implementation proven against it.

### Decision

1. **The core** (`Once.Spec.Core.*`): well-scoped de Bruijn raw terms `Tm n` and an
   extrinsic judgment `Γ ⊢[ Ψ ] t ∷ A ! π`, graded by a usage vector (QTT, exact) and an
   effect grade. The formers are those of the types: `var`/`lam`/`app`/`let′`, `unit`,
   `pair`/`fst`/`snd`, `inl`/`inr`/`case`, `absurd`, `roll`/`fold` (μ), `unfold`/`out` (ν),
   `coerce` (D226), `lit`, saturated `prim` (the arithmetic SigOps), `sigop` (FFI). This
   is the non-dependent fragment of the POC's kernel. The dependent kernel extends this
   judgment. It is never a second one.
2. **The combinators are definitions** (`Once.Spec.Core.Derived`). `id`, `compose`,
   `fst`, `snd`, `pair`, `case`, `curry`, `apply`, `terminal`, `initial`, `In`, `Out`,
   `cata`, `ana` and the `effApp` suspension are λ-terms. An arm is bound by `let`, so it
   is evaluated once and costs its own usage (D127). The compiler's path is unchanged: it
   emits `IR.compose` and owes the model lemma `⟦IR.c⟧ = ⟦definition of c⟧`, not a
   runtime translation.
3. **Terms carry an effect grade `π`.** This is D032's arrow discipline read as a
   λ-calculus. A combinator defined as a λ-term has an effectful body at an effectful
   arrow (`compose f g`'s body is `g (f x)`), so the core has to type effectful terms.
   Value introductions are `pure`, and a λ is pure whatever its body does, because the
   body's grade rides the arrow (D222). Multi-premise rules share one `π` (D222).
   `pure ⊑ eff` is the subsumption rule `⊢sub-eff`, which has no term (D068). Referencing a
   base-typed FFI constant has the grade of its codomain (D225).
4. **The meaning** (`Once.Spec.Core.Meaning`) is the surface meaning with the modes
   removed: call-by-value Kleisli morphisms `⟦Γ ↾ Ψ⟧ → T⟦A⟧`, one clause per rule.

### The grade is the surface's, not yet a semantic claim

The accepted programs must not change (plan 0.102 §3), and the surface `lam` accepts
any body at any arrow grade. So the core types two emitting leaves at ANY grade, as the
surface does:

* `out`: `ν-type F` records no grade, so forcing a layer of an effectful ν is invisible
  in the type;
* `sigop`: referencing a base-typed FFI constant at `Unit`/`Void` is a SigOp call that
  emits or halts (D225), and an FFI arrow's grade is trusted from its signature.

**Decided (2026-09-27): `pure` means no side effects**, so the grade is a semantic claim
(evaluation at a pure arrow emits nothing). A pure term that can hide a SigOp event would
make the correctness statement, which is about exactly those events, unprovable. The
core grades by what terms do:

* `ν-type` records its layers' grade, so forcing a pure ν is pure and forcing an
  effectful one is `eff`;
* an FFI signature must be honest. An arrow into `Unit` or `Void` (which emits or halts,
  D225) must be `Eff`, and a base-typed constant of type `Unit`/`Void` is rejected: a
  nullary effect is `Eff Unit Unit`, because effects live on arrows (D032);
  this is checked on the `signature` DECLARATION (`projectSig`, so `ModuleTyped` rejects a
  dishonest one), not on references: user definitions share the reference rules, and
  a pure user `f : Int -> Unit` (e.g. `terminal`) is honest and must stay accepted;
* the surface rejects a pure `lam` whose body emits.

Red tests: `compiler/test/PuritySpec.hs`. Until the surface is fixed, the core's
`⊢out`/`⊢sigop` stay at any grade, matching today's surface. They are tightened together
with it.

The equality judgment is not written yet. Following the top-down rule it lands when
something first consumes it: the combinators' defining equations (plan 0.102 C) or the
optimizer's normalization postulates.

## D232 — STANDARD QTT FOR APPLICATION: `compose`'s INNER ARM AND `effApp`'s ARGUMENT ARE SCALED (AMENDS D127) (2026-09-27)

**Relates**: D127, D231, plan 0.102.

D127 made `compose` linear in BOTH arms and `effApp` linear in its argument, arguing that
an arm is a value used once. Grades in Once live on the MORPHISM: `A ^q-> B` says how
often the function uses its argument. This is variable-based QTT (Atkey/McBride; the
POC's §7; Linear Haskell's `a %1 -> b`), and values carry no grade. In `compose f g =
λx. f (g x)`, the term `g x` is `f`'s ARGUMENT, so every resource it mentions, `g`
included, is scaled by `f`'s grade. D127's exception breaks two invariants:

* **Usage soundness.** `\(h : H ^1-> …) -> compose dup (\_ -> h)` is accepted with `h`
  used once, and at runtime returns `(h, h)`. Likewise `effApp dup h`.
* **A definition is interchangeable with its body** (plan 0.94 §0 at the combinator
  level). Unfolding `compose f g` to its definition changes the usage from `Ψf + Ψg` to
  `Ψf + ω·Ψg`.

### Decision

Standard QTT everywhere. `compose`'s inner arm costs `ω·Ψg` (generally `q·Ψg` for the
outer arm's grade `q`), and `effApp f x` costs `Ψf + ω·Ψx`, like any application. The
outer arm, `pair`, `case`, `curry`, `cata`, `ana` and the closed combinators already get
their D127 usage under the standard rule, and stay unchanged. No program in the repository
writes `^1 ->`, so no existing program changes status. The red tests are in
`compiler/test/QttSpec.hs`.

Not reopened: graded VALUES (a pair with one linear and one ω component). The standard
form is a graded tensor or Σ, `(x :1 A) ⊗ B`, a possible future former of the core. It
pays off only once linearity has runtime meaning; today only `0` (erasure) does.

## D233 — CODATA CARRIES THE EFFECT GRADE: THE EFFECTFUL STREAM IS `Nu (Eff F)` = ν(T ∘ F) (2026-09-27)

**Relates**: D032/D046/D068 (effects live on arrows), D192/D193/D194 (ν, `ana`, `Out`),
D222 (read the grade off the denotation), D231 (`pure` means no side effects).

### Context

`ana coalg` returns a LAZY stream. Its coalgebra runs later, one step per `Out`, after
`ana`'s own arrow has returned. An effectful coalgebra's effects therefore escape the
arrow that built the stream. Today both kinds of stream share the type `Nu F`, and `Out`
is typed pure, so `peek : Nu F -> …; peek v = Out v` hides the coalgebra's effects
inside a pure function. `cata` has no such problem: it consumes a finite structure
within one call, so its arrow's grade covers every algebra step.

### Decision

* **The rule.** A type carries an effect grade exactly when its values hold computations
  that have not run yet and run when the value is eliminated: the CODATA types. Once has
  two of them, arrows (`A -> B` / `Eff A B`, eliminated by application) and ν
  (eliminated by `Out`). Data types (`Unit`, `Void`, products, sums, `μ`, base types)
  hold only evaluated values and carry no grade.
* **Mathematically.** A pure coalgebra `A → F A` has the final coalgebra `ν F`, with a
  pure destructor. An effectful coalgebra `A → T (F A)` is a coalgebra of `T ∘ F`, whose
  final coalgebra `ν (T ∘ F)` is the effectful stream (a resumption), with destructor
  `ν(T∘F) → T (F (ν(T∘F)))`, an effectful arrow. A server is such a stream.
* **Internally** `ν-type F π`: one former with a grade, `ν-type F pure <: ν-type F eff`,
  and the grade is erased by the IR like an arrow's.
* **Surface syntax** `Nu F` (pure) and `Nu (Eff F)` (effectful). `Eff` in the functor
  position means "the effectful variant of this codata", as `Eff A B` does for `A -> B`.
  It is not a general functor code: `Mu (Eff F)` is ill-formed, because data carries no
  effects. `Eff (Nu F)` stays what it would mean literally, `T (ν F)`.
* **`ana`** with a coalgebra at grade `π` builds `ν-type F π`. Building runs nothing, so
  `ana`'s own arrow has an independent grade (as `curry`'s outer arrow does, D222).
* **`Out`** on `ν-type F pure` gives the layer. On `ν-type F eff`, a term-level `Out v`
  is a suspension `Eff Unit (F (ν-type F eff))`, exactly as applying an effectful arrow
  at the surface is (`effApp`).

The red test `compiler/test/PuritySpec.hs` ("pure function forcing an effectful ν")
becomes a type error for the right reason: `peek`'s parameter is a pure stream, and an
effectful one is not.

### D227 amendment (2026-09-28): a sig-less `main` is declared at `IO Unit`

`main : IO Unit` is the program's INTERFACE, fixed by the language, not an inference
result. With `exit` returning `Void` (D227), `main = exit@S …` INFERS `Eff Unit Void` and
failed the exact `IO Unit` requirement (11 tests: every sig-less exit program). A sig-less
`main` is therefore declared at `Eff Unit Unit` (`extractFunctions-sigless`, mirrored by
`Resolve.pdn-sigless`) and CHECKED there, where `Void <: Unit` (D226) accepts the halting
body. Programs that write `main : IO Unit` are unaffected.

## D234 — EVERY GROUND DEFINITION IS TYPED AT ITS DECLARATION: THE MODULE IS A TELESCOPE (PLAN 0.103 PHASE 1) (2026-09-28)

A module is well-typed iff every definition is typed ONCE, at its declaration, in its
prefix. Before this, a GROUND definition that `extractFunctions` routes to the telescope
(`PolyFunInfo`) — every `Mu`/`Nu` definition, because routing is by FFI concreteness —
was typed only at its use sites: an unused ill-typed one was accepted
(`f : Nu (K Int); f = 5`), and a used one was typed in the USE site's context.

* **Spec.** `Typed` (Once.Spec.Program) gains a fourth component `PolysTyped m`
  (Once.Spec.Module): every ground telescope entry is typed ONCE,
  `ctxWithImportsAndPolys (funCtxAt … (pfunAfter pfi)) tail ⊢ᶜ body ∶ T ⨾ 0`, in the
  monomorphic context at its declaration position (`pfunAfter` = the number of `FunInfo`s
  declared after it) and its telescope TAIL (exactly the prefix a reference's
  `lookupPolyPrefix` returns). It is stated structurally over the telescope list, so the
  telescope's meaning (an environment, phase 1c) is a plain recursion. Polymorphic entries
  are not constrained here: typing them once needs the type-substitution lemma (plan 0.103
  phase 5).
* **Implementation.** `Compile.compileGated` runs the decider `polysOK` before
  `compileAllFuns`, for `compileResolvedModule` and for `compileFromModule`'s Check and
  Build stages (one gate, every entry point).
* **Adequacy.** `Once.Adequacy.PolysCheck` proves the decider sound and complete for
  `EntriesTyped` (postulate-free); `AcceptSound.moduleToIR-polys` produces the new
  component, `ModuleComplete.moduleToIR-complete` consumes it.
* **Routing** by concreteness still decides CODEGEN (direct call vs δ-reduction); it no
  longer decides whether a definition is typed.

## D235 — A TELESCOPE REFERENCE IS A DEFINITION VARIABLE; LINKING IS SUBSTITUTION (PLAN 0.103 PHASE 1c) (2026-09-28)

**Found:** `ResolveFaithful.resolveExpr-poly-splice-faithful` equated the meaning of a spliced body
with the meaning of the `poly x A` placeholder, for an ARBITRARY elaborated body. Instantiating
the body with `inl' unit` and `inr' unit` derives `⊥`; it was on the apex path. The reference
chain pivoted on the placeholder's own meaning (an opaque internal call).

**Decision (the principled choice, not the cheapest):** the definitions environment lives in the
SEMANTICS.

* **Judgment.** `t-var-poly-instantiate-infer` has no body premise: a ground telescope entry is
  a variable of the telescope at its declared type; its body is typed once (`PolysTyped`, D234).
  The elaborator's witness is the rule itself (`bbc-other-poly-infer-witness` deleted).
* **Meaning.** `⟦_⟧` takes the telescope environment `ρ : DefMeanings (NamedCtx.polys ctx)`
  (`Denotation.DefEnv`, structural over the telescope); a reference reads it. The spec builds
  `ρ` from `PolysTyped` (`MainMeaning.defMeanings`); `⟦_⟧ᵈ` now takes `pts`.
* **Surface semantics.** `SD.⟦_⟧ˢ` takes `σ : DefsSem`; `poly x A` means `σ x A`. The compiled
  program's environment is `internalDefs` (an unlinked reference is an internal call).
  `realize` keeps references open (`poly x T`) exactly as the elaborator does, so the
  reference case of `realize-agrees` is `refl` (`infer-agreeV-RVar-poly-todo` deleted).
* **`closed`.** A new surface former `closed : Expr ∅ [] A → Expr Γ zeroUsage A` embeds a closed
  term without going through the IR (which would lower its references to internal calls).
  `embedClosed` is `closed`.
* **Linking.** `resolveExpr` splices `closed (resolve body)`, the body elaborated in ITS
  DECLARATION CONTEXT (telescope tail via `lookupPolyPrefix`, declaration imports via
  `impsOf = Compile.entryImps`), which is `PolysTyped`'s context: compile once, no dynamic
  scoping. Its faithfulness is the substitution lemma `SD_σ₀⟦resolve e⟧ ≡ SD_σR⟦e⟧`, `σR` the
  linked references' meanings; the poly case is proved.
* **Bridge.** `MeaningBridge` holds under `EnvRel ρ σ` (entrywise `RelT`); both reference
  clauses are proofs. The apex surface meaning runs in `σR` of main's link data; `bridgeᵈ`
  uses the telescope lemma `EnvRel ρSpec σR` (`Adequacy.TelescopeEnv`, PROVED: completeness
  on each entry's declaration derivation, the substitution lemma, agreement, derivation
  independence and the bridge in the tail's environments; Acc-irrelevance of the resolver).
* **Distinct telescope names.** `guardDistinct` also requires the telescope's names to be
  distinct: a definitions context with two entries of one name is ill-formed, and linking
  resolves references by name.

## D236 — A POLYMORPHIC REFERENCE IS AT AN INSTANCE OF ITS SCHEMA (PLAN 0.103 PHASE 2a) (2026-09-28)

`t-var-poly-instantiate` gains the premise `IsInstance schema T`: some total type-variable
assignment `θ` has `substPoly θ schema ≡ T`. `substPoly`/`IsInstance` are part of the type
language (exported by `Spec.Type`); the decider `instantiate` stays implementation. The
elaborator's check-mode fallback decides the premise before emitting `poly x T`, and
`Type.Instance.instantiate-complete` proves the decider complete for it. The decider was also
too loose: it matched `Eff A B` against an effectful arrow of ANY quantity, while `Eff A B` is
exactly the `Many` effectful arrow; it now requires `Many`.

Without the premise the schema was decorative: any type the body happened to check at passed.
The body premise is still not established by the elaborator (defect 7,
`bbc-other-poly-witness`), which plan 0.103 phase 6 removes.

### D236 amendment (2026-09-28): the check-mode witness is CONSTRUCTED; one residual, stated exactly

The postulate `bbc-other-poly-witness : ∀ ctx x T → ctx ⊢ᶜ RVar x ∶ T` (defect 7: it derives `⊥`
for an unbound name) is DELETED. The elaborator's check-mode polymorphic fallback now decides
every premise of `t-var-poly-instantiate` (not a local, not an import, a non-ground telescope
entry, at an instance of its schema — `instantiate` is proved SOUND as well as complete,
`Type.Instance`) and builds the rule. The one premise it cannot establish is the body's typing at
the instance, postulated as `Elaborate.poly-body-typed`: a polymorphic entry's body types at every
instance of its schema. That is exactly what plan 0.103 phase 6 derives (parametric typing plus
the type-substitution lemma) and then deletes; until then it is false in general. The matcher
moved to `Once.Type.Match` and decides equality with `_≟T_`.

## D237 — ARGUMENT-DRIVEN APPLICATION OF A POLYMORPHIC HEAD: `d-poly` (PLAN 0.103 PHASE 2b/2c) (2026-09-28)

D230 made argument-driven application an inference: the argument's type is the head's GIVEN
domain (`⊢ᵈ`). A polymorphic head (`myId 0`) had no given-mode rule, so it regressed. `d-poly`
is local type inference (Pierce–Turner): given the domain `A`, an ARROW schema (`ArrowSchema`:
`sd -> sc` pure, or `Eff sd sc`) whose codomain's free variables occur in its domain
(`CodVarsInDom`, stated with `ftv` — the type language) is instantiated at domain `A`, which
fixes the codomain `B`; the reference is typed at `A ⇒ B` (body per use until phase 6).

* **Determinacy** (`Type.Determined`): substitution sees a schema only through its free
  variables (`agree-on`/`agree-from`), so `CodVarsInDom` makes the codomain a function of the
  domain's instance (`cod-determined`). Mode agreement for `d-poly` (against itself, inference
  and check mode) is PROVED from it; `ModeAgreement` stays postulate-free.
* **Elaborator.** A variable head in given mode infers when it can (`d-infer`); otherwise the
  de-withed polymorphic fallback decides the lookups, non-groundness, the arrow split,
  `codVarsInDom?`, matches the domain (`instantiate`, sound), reads off the codomain, and checks
  the grade. `Completeness.given-complete`/`spine-complete` prove it complete for `d-poly`.
* **Meaning / bridge.** As the check-mode polymorphic reference: the body in the prefix's
  environment, converted to the given grade; `bridge-d` is a proof. The agreement of the
  elaborator's placeholder with the reference elaboration is the phase-6 residual
  `given-agreeV-RVar-poly-todo`, twin of `check-agreeV-RVar-poly-todo`.

## D238 — TYPE VARIABLES IN THE CORE ARE KINDED; `∀` MEANS ITS INSTANCES (PLAN 0.103 PHASE 3) (2026-09-28)

The core gains types over `m` de Bruijn type variables (`Spec.Core.PolyTy`) and the judgment
`Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π` over them (`Spec.Core.PolyTyping`), `Δ` a PARAMETER (one rule per
former, the ground core's rules read over `Ty m`).

* **Kinds are forced, not chosen.** A functor's `K` positions hold BASE types (`WellFormedF`),
  so a type variable used there (`List a = μ (K Unit ⊕ (K a ⊗ Id))`) must range over the base
  universe. Variables are kinded `base` / `any` — OCP-0009's universe of monotypes with its
  base sub-universe — and instantiations must respect kinds (`Respects`).
* **The ground instantiation theorem** (`PolyTyping.instantiate`, postulate-free): a derivation
  over `Δ` and a kind-respecting ground instantiation `σ` give a ground core derivation of
  `t⟪σ⟫ ∷ A⟪σ⟫`. This is the type-substitution lemma at ground targets (plan 0.103 phase 5),
  and it DEFINES the meaning of a polymorphic term at an instance: the ground meaning of the
  instantiated derivation — `∀` as the family `Π(σ). ⟦T[σ]⟧`. The ground core is unchanged.

## D239 — THE CORE TELESCOPE WITH ∀ (PLAN 0.103 PHASE 4) (2026-09-28)

The core is relative to a DEFINITIONS SIGNATURE (`Sig`: the schemas `∀Δ. T` of the earlier
definitions); both the ground and the polymorphic core gain `ref d τ`, a definition at an
instance of its schema (kind-respecting). `Spec.Core.Telescope`: a module is a telescope whose
entries are typed ONCE, over their kinds, in their prefix's signature; a `Program` ends in
`main : IO Unit`. Its meaning is the environment of families — entry `d` at a ground
instantiation `τ` means the ground meaning of `instantiate τ D` in the prefix's environment —
so `∀` means `Π(σ). ⟦T[σ]⟧` constructively, with no parametricity claim.

## D240 — THE TYPE-SUBSTITUTION LEMMA IS PROVED (PLAN 0.103 PHASE 5) (2026-09-28)

`Spec.Core.TySubst.tsubst`: `Δ ⊩ Γ ⊢[Ψ] t ∷ A ! π ⟹ Δ′ ⊩ Γ⟨σ⟩ ⊢[Ψ] t⟨σ⟩ ∷ A⟨σ⟩ ! π` for every
kind-respecting substitution `σ` of open types — a metatheorem about the core judgment,
postulate-free. "Typed once, instances for free" is now a valid argument in the core. Its
semantic counterpart is not needed: `∀` means its instances by definition (D239), and a
reference means an environment lookup at its instantiated types.

## D241 — A DEFINITION DOES NOT SEE ITSELF: NO GENERAL RECURSION THROUGH THE SELF-BINDING (PLAN 0.103 PHASE 6) (2026-09-29)

**Relates**: OCP-0003 (general recursion removed), D061/D071 (an internal reference is a
context projection, never a SigOp), D239 (the core telescope), plan 0.103 phase 6c.

**Defect.** A monomorphic (ground, concrete) definition's body was typed in
`ctxWithImportsAndSelfAndPolys ctx polys name ty`, which put the definition ITSELF into
the imports table. So `loop : Int; loop = loop` and `f n = f n` were accepted.
* That is general recursion, which OCP-0003 removed: Once is CCC plus structured
  recursion (`cata`/`ana`).
* The Spec's meaning read the self-reference as an opaque SigOp of the definition's own
  name (`sigOpRefᴰ`), while the compiler emitted a real call, so the Spec and the
  compiler disagreed.
* The core telescope (D239) cannot express it: an entry is typed in its PREFIX.

**Decision.** The body context is `ctxWithImportsAndPolys ctx polys`: a definition sees
the definitions before it and never itself. `ctxWithImportsAndSelf` and
`ctxWithImportsAndSelfAndPolys` are deleted. The rule is the one telescope entries
already obeyed. Monomorphic definitions now follow it too, which is what lets them
become arity-0 core entries (plan 0.103 phase 6c).

**Tests.** The "Recursion" group of `compiler/test/TypeCheckSpec.hs` asserted acceptance.
It becomes "No general recursion (D241)", with three rejection tests plus a test that a
later definition may use an earlier one. It stays red until the user re-extracts MAlonzo.

**Examples affected** (not built by any test; each is an unbounded server loop written as
a self-call): `examples/seL4/EchoServer/{EchoServer,echo-client,echo-client-simple}.once`
and `examples/seL4/Rootserver/{Rootserver,Rootserver-simple}.once`. An unbounded loop is a
ν (`ana`, D192), and porting them is follow-up work.

**Amendment (2026-09-29): the telescope order is part of the same defect.** Removing
the self-binding is not enough. With the pre-D241 binary, `p1 = p3; f2 = p1; p3 = f2`
(`p1`, `p3` polymorphic, `f2 : Int -> Int`) TYPECHECKS: mutual recursion with no
self-reference. The cause is two orders that disagree:
* `extractFunctions` keeps `polys` in DECLARATION order, so the "telescope tail" that
  D234 calls an entry's prefix is the entries declared AFTER it;
* a monomorphic function sees ALL telescope entries;
* an entry sees the monomorphic functions declared BEFORE it (`pfunAfter`).

The rule is D241's, applied everywhere: **a definition sees exactly the definitions
declared before it**. That makes the module a single declaration-ordered telescope,
the core `Tele` of D239 (plan 0.103 phase 6c). Red tests: "mutual recursion through
the telescope is rejected" and "a definition cannot use a later one" in
`TypeCheckSpec`.

## D242 — STRUCTURED RECURSION IS CORRECT BY CONSTRUCTION; A PRAGMA GATE GUARDS THE CONSTRUCTION (2026-09-29)

**Relates**: OCP-0003, D241, MERGE.md §4c.

D241 found general recursion leaking through the surface module layer twice. The
user's decision on how to stop that class of mistake:
* **By construction, not by a check.** The module is one declaration-ordered telescope,
  each definition typed in its prefix (plan 0.103 6c′). Its core twin `Tele` references
  only the prefix (`ref d`, `d : Fin s`), the core has no `fix`, and the core meaning is
  a total Agda function. General recursion then cannot be stated, rather than being
  rejected.
* **A gate on the construction's premise.** The argument holds only while Agda checks
  termination and positivity. Until the whole compiler builds with `--safe`,
  `formal/scripts/pragma-gate.sh` (`make pragma-gate`) is a merge gate. It fails on any
  termination, positivity, coverage or universe pragma in the import closure of
  `Once/Certified.agda` and `Once/Compiler.agda` beyond a baseline that may only shrink.

**Baseline at introduction** (source-level): `Parser/Generic/Sound` 14,
`Parser/Generic/Parser` 1, `Arith/Machine/Recognise` 2, `Arith/Machine/Rewrite` 1. Four
modules, 18 pragmas, all on the implementation side and all blocking `--safe`.

## D243 — A POLYMORPHIC DEFINITION IS TYPED ONCE, AT ITS SCHEMA WITH RIGID PARAMETERS (PLAN 0.103 PHASE 6d) (2026-09-29)

**Relates**: D236–D240, D241/D242, OCP-0009 (the DT POC, `origin/ocp-0009-levitation`).

**Decision (user, 2026-09-29).** `d : ∀ā.T = e` is well-typed iff the ONE surface judgment
types `e` at `T` with each `aᵢ` a RIGID type constant. The surface `Type` gains
`rigid k i`: the definition's `i`-th parameter, of kind `k`. Two alternatives were rejected:
* a second typing judgment over open types, which would mean two specs and a coherence
  obligation;
* type variables throughout the surface judgment, which plan 0.103 §6 already rejected.

* **Kinds are read off the schema.** A parameter occurring under a functor constant
  (`PK`) is `base` (it must be a base type for `WellFormedF` to hold at its instances);
  every other parameter is `any`. `IsBaseType (rigid base i)` holds, and nothing else is
  known about a rigid constant: the body is parametric by construction.
* **Elaboration then renaming.** The body's derivation elaborates to the core (6b).
  `⌈rigid k i⌉ = var i` maps it onto the core entry `Δ ⊩ ∅ ⊢ t ∷ ⌈T⌉`, typed once
  (D239). A use is `ref d τ` at a kind-respecting instance (`tsubst`/`instantiate`,
  D240). The per-use body premise of `t-var-poly-instantiate`/`d-poly` is deleted, and a
  `Respects`-kinds premise replaces it.

**Matches the DT POC.** There, polymorphism is Π over a universe, `(A : U₀) → El₀ A → El₀ A`
(`polyId`, `NbEPUnivH`). The body is typed once in a context extended by `A`, where `El₀ A`
is a rigid neutral, and a use is application. `rigid k i` is the non-dependent shadow of
that context variable: its index is the parameter's position in the definition's telescope
Δ, and its kind says which universe it ranges over (`base` ⊂ `any`). When OCP-0009 lands,
the constants become genuine context variables and nothing needs translating.

## D244 — INTERNAL CALLS MEAN THEIR CALLEE: THE IR IS A PROGRAM (PLAN 0.103 PHASE 6a′) (2026-09-29)

**Relates**: D061, D064, D071, D239, D241, [[generic-semM]] (the Void inconsistency).

**Finding.** A call to a monomorphic user function has never meant the function:
* the resolver turns it into `closure f`, and SD and the IR lower it to
  `SigOp (internal-info f)`;
* its contract is `pureV (generic-semM "f")`: opaque, claimed pure and eventless, and
  inconsistent at `Void`;
* the backend covers it only by `obs-correct-sigop-rest`.

The core (D239) gives `ref d` the definition's body. No bridging postulate is consistent: it
would pin one `generic-semM "f"` across every module.

**Decision (user).** Option (b), chosen on the final architecture and not on edit cost.
* The IR's semantic object is a PROGRAM: the compiled function table plus `main`. That is
  exactly the shape Once's codegen emits (one section per function, D064's direct calls) and
  the IR twin of the core `Program`.
* `evalᴰ` reads a call environment: an internal call means the callee's compiled IR, evaluated
  in the environment of the functions declared before it. It is well-founded because there is
  no recursion (D241).
* SD reads the definitions environment at `closure f`.
* The backend obligation for an internal call is local: `call once_f` runs table entry `f`.
  Each function is proved correct given its callees.

Rejected: (a) a call node carrying the callee's IR, which makes the IR a tree of inlined bodies
while codegen emits a table, and needs a linking invariant; (c) linking in the meaning only,
which is non-modular and whole-program.

## D245 — A SIGOP MEANS ITS CONTRACT; A DEFINITION REFERENCE MEANS ITS ENTRY: THE IR GETS A CALL NODE (PLAN 0.103 PHASE 6a′) (2026-09-29)

**Relates**: D061 (a SigOp carries a contract its producer discharges), D071 (whose heading
this corrects), D231, D239 (the core `Program`), D244 (the IR is a program).

**Correction.** D071 was headed "SigOp Is FFI-Only". D061 has two producers of SigOps:
* interpretations, for FFI;
* the compiler, which mints pure `arith.block.<digest>` SigOps and discharges their contract by
  lifting.

Both are legitimate. The distinction that matters is between two ways a node can mean
something, not between FFI and internal producers:
* **by contract.** The node carries a closed `semM` + `EffectShape` that is independent of the
  rest of the program. FFI SigOps and compiler-minted SigOps are both of this kind.
* **by environment.** The node means an entry of the program it belongs to. Definition
  references are of this kind.

D071's heading now says this.

**Decision.** The IR gets a dedicated call node, the IR twin of core `ref`. `SigOp` keeps
every contract-carrying operation, FFI and compiler-minted alike. D244's call environment gives
the call node its meaning, and codegen lowers it to `call once_<name>`, exactly as it lowers an
internal-ref SigOp today. `internal-info`, the `internal-ref` Linkage and the use of
`generic-semM` on this path are deleted.

**Grounding in the branch's plans.**
* **0.102/0.103.** The core already has three formers:
  * `prim` is the compiler's Pure SigOps, meaning `primSem`;
  * `sigop` is FFI, meaning `sigOpRefᴰ`;
  * `ref d τ` means `ρ d τ`, an environment lookup (`Core/Meaning.agda:167`).

  The IR has twins for the first two (`SigOp`) and none for `ref`: `internal-info` fakes one.
* **0.97/0.98.** `EffectShape` is pure, one event, or halt, and a halting SigOp returns `Void`.
  A user function may emit many events, return closures, or halt partway (0.97's `CalleeRun`).
  So any SigOp contract for a call is either false (`internal-info` claims `pureV`) or the
  callee's whole meaning, which is inlining.
* **0.88/0.93 §11.** `obs-correct-sigop-rest` covers the Pure fall-throughs, and internal calls
  are among them: their closure results are not register-resident. With a call node they leave
  that postulate. Their own obligation is "`call once_f` runs table entry `f`", and that takes
  a step toward the split by reason that 0.93 lists as owed.
* **0.89.** The machine already runs `CompUnit`s, an entry plus labelled blocks, `link`ed. An
  IR whose calls reference table entries has the same shape.

Rejected: keeping `SigOp` for internal calls and dispatching `evalᴰ` on the `internal-ref`
tag. A SigOp would then mean either its contract or an environment entry depending on a tag,
which is D071's confusion again.

**Amendment (2026-09-29): the call is the DIRECT-CALL morphism.** The first cut
typed the node `Call : IR Unit B`, modelled on `internal-info`'s closure-returner
ABI (`once_f()` returns f's value). That is not what codegen emits. D064 emits an
arrow definition uncurried (`Compile.directCallIR`), and a compiled program calls
it with the argument in the input register. The disassembly of
`compiler/test/arith-lambda-1.once` shows `call once_1f` with `%rdi` = the argument.

With the closure-returner type, the image's `once_f` would never implement what
`Call` means, and `FnRuns` would be unsatisfiable for every arrow definition. So:
* `Call : CanonicalName → IR A B`, where A and B are the direct-call morphism's
  objects;
* table entries carry `directCallIR`'s domain and codomain, and the environment is
  `ρ f A B : ⟦A⟧ → T⟦B⟧`;
* a reference is `Once.IR.Ref.refIR`, clause for clause with `directCallIR`:
  * at an arrow it is `curry (Call f ∘ snd)`, the shape the `SigOp (arrow-info f)`
    path already had;
  * otherwise it is `Call f ∘ terminal`.

The erasure agrees definitionally: `⌊ A ⇒[Zero] B ⌋ = Unit ⇛ ⌊B⌋`, the domain
`directCallIR` gives an erased arrow.

## D246 — A MODULE ENTRY'S REFERENCE IS A CALL AND MEANS THE ENTRY; THE SPEC READS AN IMPORT ENVIRONMENT (PLAN 0.103 PHASE 6a) (2026-09-30)

**Relates**: D071, D241, D244, D245, plan 0.103 phases 1c and 6a.

**Found.** After D245 the compiled program CALLS a module definition's body at every bare
reference: the compile walk hands the resolver every in-scope entry (`userList = self ∷
cimps`), so every `t-var-import` reference becomes `closure f`, which elaborates to `Call f`.
The Spec disagreed in two places:
* `⟦ t-var-import ⟧ᵢ = sigOpRefᴰ` gave a reference to a monomorphic DEFINITION an opaque
  SigOp contract (6c′ types a monomorphic definition like an import, `ModTele.mono ↦
  addImp`).
* The typechecker and `realize` emitted `sigOp x`, and the resolver rewrote it to
  `closure x`. The rewrite's faithfulness residual (`resolveExpr-sigOp-closure-faithful`,
  "a denotational no-op") is FALSE once a definition's call means its body.

**Decided (principled path, following D071 and plan 0.103 1c).**
* **A bare reference to a module entry elaborates to a call** (`closure x`), in the
  typechecker and in `realize` alike. The sigOp→closure rewrite and its postulate are
  deleted. `sigOp` remains only for SigOps: qualified external references and the
  compiler's arith blocks (D245).
* **A call means the entry.** An FFI declaration's compiled entry is its SigOp wrapper, so
  its call means the contract. A definition's call means its body. The compiled function
  table includes the FFI entries, since the emitted `call once_f` resolves to them too.
* **The Spec's meaning reads an IMPORT ENVIRONMENT**, alongside the telescope's
  `DefMeanings`. It gives each in-scope entry its meaning (FFI → contract; definition →
  its declaration-time derivation's meaning in its scope), built by the same telescope
  recursion as `defMeanings` (plan 0.103 1c: "the meaning of a context with definitions is
  an ENVIRONMENT").
* SD reads the CALL environment at `closure` (the IR's `Call`) and the reference
  environment at `poly` (a spliced telescope reference). The resolver's reference case is
  then `refl`, and the obligation "a call means its callee's body" sits where the
  environments are related (`TelescopeEnv`), by induction on the telescope.

**Why not make monomorphic definitions telescope entries instead** (plan 1b's wording)?
6b's translation and 6c′'s judgment already classify each import as FFI or definition (the
View's `ImportAt`). The import environment is that classification's meaning. Moving
definitions into the telescope would undo a landed, postulate-free design for no gain in
honesty.

## D247 — THE CORE'S `unfold` STORES ITS COALGEBRA AS A COMPUTATION (D192 IN THE CORE) (2026-09-30)

**Relates**: D192, D194, D131, plan 0.102 A, plan 0.103 6b.

**Found** while proving the 6b bridge (surface meaning = core meaning of the elaboration).
D192 decided that a ν stores its coalgebra as a COMPUTATION, bound inside each forced layer.
The surface meaning (`ana-sem`), SD and the IR's `Ana` all do this, and D192 records that
binding it outside "would make this clause disagree with both". The core did bind it
outside:
* `⟦ ⊢unfold dc ds ⟧` evaluated the coalgebra first and stored its value;
* `anaᶜ c = let′ c (lam (unfold v1 v0))` evaluated `c` once, at build.

For a coalgebra whose evaluation emits, the core then meant something different from the
compiled program, and after plan 0.103 6a the core is the apex meaning.

**Decided.** The core follows D192:
* `⟦ ⊢unfold dc ds ⟧ = ⟦ ds ⟧ >>=T ana-sem wf (⟦ dc ⟧ …)`: the coalgebra's computation
  goes into the suspension.
* `anaᶜ c = lam (unfold (wk c) v0)`: building the arrow runs nothing.

`cata` is unchanged. An algebra is evaluated once, at build (D131), in every meaning.

## D248 — AN OWN-MODULE RESOLVED REFERENCE IS A CALL (D246 FOR `RResolved`) (2026-09-30)

**Relates**: D061, D071, D136, D246, plan 0.50, plan 0.81, plan 0.103 6b/6c.

**Found** while building the telescope's environment for `realize-core` (plan 0.103 C). The
6b bridge's `Agree` asks that a `t-var-resolved` reference mean its FFI contract. That is
false for the COMMON case. The resolver (`rv-own`, `name@this`; `Spec.Resolution`) rewrites
every bare reference to an own-module definition into `RResolved (canonical [x])`. The
typechecker then took the resolved path and emitted a SigOp, as `realize` did:
* `sigOp cn` for a value;
* `lift-morphism (SigOp (ext-resolved-info …))` at a `Many` arrow.

So a program's reference to its own definition meant an opaque SigOp contract (a generic
`semM` keyed by the name), not the definition. D246 had fixed this only for `t-var-import`
(a bare `RVar`), which a resolved module no longer contains for own definitions. Before
D246 the resolver's sigOp→closure rewrite had hidden it; D246 deleted that rewrite.

**Decided (D071, D246).** A resolved reference whose canonical name has ONE part (`own x`,
a new pattern synonym for `bare x`) names an entry of this module. That entry is a
definition or the module's own FFI declaration, and either way it is in the function
table. So the reference is a CALL of it (`closure x`), exactly like a bare reference:
* in the typechecker (`resolvedValueTerm`/`resolvedArrowTerm`), in `realize`, and in the
  surface meaning (`impAt`, the import environment);
* a path of two or more parts is another module's inlined FFI signature (`resolveImports`
  inlines only signatures, keyed by the full dotted path), so it stays a SigOp with its
  canonical identity.

The core's elaboration needs no change: `own x = bare x`, so `importE` already reads the
View's classification. `Agree.agree-resolved` now covers only names that are not own
(`NotOwn`). An own-module name's agreement is `agree-import`.

**Runtime.** The emitted code for an own reference is `call once_x`, as it was under the
pre-D246 resolver rewrite. A reference into another module is unchanged.

## D249 — EVERY MODULE ENTRY HAS ITS OWN NAME, FFI DECLARATIONS INCLUDED (2026-09-30)

**Relates**: D241, D244, D245, D246, plan 0.103 C.

**Found** by the telescope walk (plan 0.103 C). A reference is a call, and a call is resolved
by name: the function table is searched latest-first for `(name, ABI)`, and the image
resolves `call once_f` by the symbol. D241 made every DEFINITION name distinct, monomorphic
and telescope together. FFI declarations were outside the guard. Since D246 they are table
entries too. Suppose an FFI declaration `f` and a definition `f` both appear. Then a
reference to the earlier one, made before the later one is declared, calls the later one at
run time. The Spec, like the typechecker, means the earlier one. That is a miscompilation,
and the walk cannot prove it away.

**Decided (D241's own principle: "a definitions context with two entries of one name is
ill-formed").** The extractor's guard also requires the names of ALL entries (definitions,
telescope entries and FFI declarations, own and imported) to be pairwise distinct
(`Parser.entryNameOf`, `NameClash.guard-entries`). Validity (identifier syntax) is still
required of the emitted names only. Imported signatures carry dotted, owner-tagged names.

**Consequence.** A module that imports the same module twice now gets its signatures twice
and is rejected. No program in `tests/`, `test/` or `examples/` does this. If it is ever
wanted, the resolver should import a path once, rather than the guard admitting duplicates.

## D250 — `pure` IS REFERENTIAL TRANSPARENCY: THE MEANING IS GRADED (PLAN 0.104; CLOSES 0.103 G) (2026-10-01)

**Relates**: D231 (the grade is a semantic claim), D068 (subeffecting), D143 (the quantity is
grade-aware in the meaning), D064 (definitions are morphisms), D241 (no general recursion),
D245; OCP-0009 (conversion is observational equality on the pure fragment).
**Reverses**: plan 0.52 M2's purity-blind arrows, in the Spec's value domain `⟦_⟧ᴰ` and in the
contract value domain `Once.Semantics.Value`.

**Found** by plan 0.103 G. `core-pure` ("a pure core computation returns and emits nothing")
could not be proved, because nothing in the Spec said it. The meaning was purity-blind: a pure
and an effectful arrow over `A`, `B` denoted the same `⟦A⟧ → T ⟦B⟧`, and the contract domain
gave a pure FFI pointer the type `⟦A⟧ → Res ⟦B⟧`. A pure-typed value could stop, so `pure`
was a promise the semantics did not make. That is D143's argument again, for the other grade.

**Decided (the mathematical definition of pureness).** `pure` means referentially transparent:
a pure term denotes a value, and replacing it by that value never changes a meaning. The
meaning of the core judgment is GRADED:

* a derivation `Γ ⊢[ Ψ ] t ∷ A ! π` denotes `⟦ Γ ↾ Ψ ⟧ → M π ⟦ A ⟧`, where `M pure X = X` and
  `M eff X = T X`, the trace monad;
* `⟦ A ⇒[ q , π ] B ⟧ᴰ = ⟦A⟧ᴰ → M π ⟦B⟧ᴰ` (at `q = Zero`, no argument, per D143), so a pure
  `Int ⇒ Int` is a total function `ℤ → ℤ`;
* `⟦ ν-type F π ⟧ᴰ` is the final coalgebra of `M π ∘ ⟦F⟧`, and a pure ν is plain codata;
* subeffecting `pure ⊑ eff` is the monad's unit `returnT`. It is not the identity, because the
  objects differ.

This is a model, not a hope, because the pure fragment is total: there is no general recursion
(D241), only `fold`/`unfold`, and every pure primitive's contract (`pureV`) returns.

**The FFI.** A contract is a value of its declared type, so a pure FFI arrow's contract is a
total function, including any function pointer it returns. `Once.Semantics.Value` is graded the
same way (`⟦ A ⇒[ pure ] B ⟧ = ⟦A⟧ → ⟦B⟧`; `eff` arrows keep `Res`). This is the meaning of the
type, not an extra rule. An interpretation that declares a pointer pure must deliver a total one.

**What stays.** The IR objects stay ungraded (plan 0.52 M2's `IRTy`). Erasing the grade at
compilation embeds the pure meaning into the effectful one along `returnT`, and the backend
correspondences are unchanged. D064's direct-call ABI is still what codegen emits. Its
agreement with the reference meaning is now a consequence for pure bodies, not a premise.

**Consequence.** `core-pure` stops being a postulate. Whether an arrow-typed definition's body
runs at the reference or at the application cannot be observed for a pure body.

## D251 — EX FALSO IS AN EXPLICIT ELIMINATOR; USAGE IS SYNTACTIC (PLAN 0.104; CLOSES 0.103 6e) (2026-10-01)

**Relates**: D226 (subtyping is a coercion; `Void <: B` is `¡`), D243 (rigid parameters),
OCP-0009's kernel (`⊢absurd` is the only ex falso).
**Withdraws**: D229's `Void` bullet (Void-principal eliminations synthesize `Void`), its
Amendment 2 (usage by reachability: what a `Void` principal discards counts zero), and its
Amendment 3 (the `Void`-input rules of the domain-given mode). D229's main principle,
eliminations consume their principal argument up to subtyping, stays.

**Found** by plan 0.103 6e. The surface substitution lemma (`poly-typed-at`) was not
structural. A base-kinded parameter may be instantiated at `Void` (the base kind is
first-order data, and `Void` is its initial object). The surface judgment then chose a
DIFFERENT rule at the instance, with a different usage: `t-binop-void-r` requires
`¬ (A ≡ Void)`, and `t-binop-void-l` drops the right operand's usage. A term's usage depended
on whether a subterm's type can return, which instantiation changes.

**Decided.** Typing is closed under substitution exactly, in type and in usage, so:

* the surface has ONE ex falso, and it already exists: the CCC's initial morphism `initial`
  (`¡`). Applied, `initial e` checks at any type with `e ∶ Void` (`t-initial-app-check`), and
  `d-initial` types it as a morphism. It is the core's `⊢absurd`;
* no other rule mentions `Void`: the Void-synthesizing eliminator rules (`t-binop-void-l/r`,
  `t-neg-void`, `t-case-void`, `t-fst/snd/apply/Out-app-void`, `t-apply-app-void`, the
  domain-given Void-input rules) are deleted;
* usage is syntactic (QTT as Atkey/McBride): every subterm counts, whether or not evaluation
  reaches it, and the arms of `case` join.

`Void <: B` (D226) stays. It is the unique morphism, it is a coercion with syntactic usage, and
it relates a rigid parameter only to itself. So it is stable under substitution.

**Consequence.** Writing `x + v` with `v ∶ Void` no longer types by itself; it is written
`initial v`, or it types through `Void <: Int` when the other operand is an `Int`. The
substitution lemma is a structural map, and its semantic twin is parametricity.

## D252 — AN ANNOTATION IS A SURFACE TYPE: IT MENTIONS NO PARAMETER (PLAN 0.104 E) (2026-10-01)

**Relates**: D243, D251.

**Decision.** `t-annot` requires `RigidFree T`. A rigid constant `rigid k i` is the
once-typed schema's internal name for its `i`-th parameter (D243). It is not surface syntax:
the grammar's annotation types are `Concrete` types (`toType`), which have no parameters.
The judgment now says so, instead of leaving it a parser fact.

**Why.** Rank-1 polymorphism is sound because a body typed at the rigid schema types at
every kinded instance, with the same raw body: the resolver re-checks that body at the
instance. The raw term carries types only in annotations. If an annotation could mention a
rigid, the instance would have to change the raw term, and the re-check of the unchanged
body would be wrong. With the premise, the substitution lemma (`poly-typed-at`) fixes every
annotation and is a structural map.

**Implementation.** The elaborator rejects a rigid annotation with
`AnnotationMentionsParameter`. The parser cannot produce one, so no program changes.
Annotating with a parameter (`(x : a)`) is a possible future feature; it would substitute the
annotation at the instance and is a separate decision.

## D253 — `main` IS AN ORDINARY ENTRY; THE PROGRAM RUNS A REFERENCE TO IT (PLAN 0.103 6a‴) (2026-10-01)

**Relates**: D241 (the module is a telescope), D245 (direct-call ABI), D246/D248 (a module
reference is a call), D249 (distinct entry names).

**Context.** `main` was treated unlike every other definition, in three places:
* the Spec's `toProgram` made `main`'s body the program's body and dropped every entry
  after it;
* the compiler rewrote `main`'s body (`maybeWrapMain`: `apply ∘ ⟨ main , terminal ⟩` at
  type `Unit`);
* the IR program left `main` out of its function table (`tbl-keep`/`isMain`), because
  the image emitted `main` as its entry.

A definition after `main` may refer to `main` (that is the telescope, not recursion). Its
body then compiles to `Call main` against a table without `main`: a dangling call. The
residual `moduleToProgram-linked` claimed the program was linked and hid it.

**Decision.** `main` is an entry like any other.
* **Spec.** The core program is the WHOLE module telescope, and its `main` term is the
  reference `ref d` to the entry `main : IO Unit` (selected by `MainIn`, as before).
  Running the program runs that reference.
* **Compiler.** No entry is rewritten: `maybeWrapMain` is deleted. Every entry is in the
  table, at its direct-call form (D245); at `IO Unit` that form IS the old wrap,
  `apply ∘ ⟨ ir ∘ terminal , id ⟩`.
* **IR program.** Its `main` is the call `Call main`, so the image's entry is a call of
  the entry `once_main`, exactly what `_start` already does.

**Consequence.** Linkedness is uniform: every reference names an earlier entry, and every
entry is in the table.

## D254 — THE COMPILER COMPILES THE REALIZATION OF ITS DERIVATION (PLAN 0.103 6a‴) (2026-10-01)

**Relates**: D063 C4 (`realize` is the reference elaboration), D253, plan 0.49.

**Context.** The verified checker (`checkElabV`) returns two things: a surface term `se` and
a typing derivation `w` of the raw body. The compiler compiled `se`. The Spec reads the
derivation: its meaning is `realize`'s term, built rule by rule from a derivation. So two
elaborations of one body lived on the apex path, and a proven 2700-line bridge
(`RealizeAgrees`: `SD⟦se⟧ ≡ SD⟦realize w⟧`) joined them. Any syntactic fact about the
compiled term had to be re-proved over the elaborator's algorithm, e.g. that every call it
emits names an entry in scope (`moduleToProgram-linked`).

**Decision.** The compiler compiles `realize w`, the realization of the derivation the
checker returns. This holds both for a definition's body (`compileFunBody`) and for the
resolver's splice of a telescope body (`applySplice`). The elaborator's `se` is no longer
compiled.

**Consequence.**
* There is one elaboration on the apex path. `realize-agrees` leaves it.
* A syntactic fact about the compiled term is an induction over the typing judgment: in
  `realize`, every call is a reference the rule found in scope, at its type.
* `RealizeAgrees`/`RealizeBridge` are deleted. They held no postulates, and nothing on the
  apex path reads `se` any more. The meaning is unchanged: the compiled term was always
  proved equal in meaning to `realize`'s, and now it simply is `realize`'s.

## D255 — THE COMPILER'S ARITHMETIC PRIMITIVES ARE IDENTIFIED BY THEIR MEANING, NOT THEIR NAME (2026-10-01)

**Relates**: D061/D071 (a SigOp is a closed contract), D165 (the arith rewrite), D250
(`pureV` is graded), the canonical-name rule.

**Context.** The arith recogniser (`Recognise.recognise-body`) decided that `SigOp si` is
addition by comparing `name si` with `bare "arith.add.int"`. The SigOp's meaning was a
`pureV f` for an arbitrary `f`, and pure FFI contracts are `pureV` too. Owned primitives
are named `owner ++ "." ++ name`. So "this SigOp is addition" rested on a pipeline-wide
convention that nothing else ever carries that name. `rewrite-program-preserves` (the
pass keeps a program's meaning) would have had to assume that convention.

**Decision.** `SigOpSem` gains `primV : ArithPrim A B → SigOpSem A B`.
* `ArithPrim` (`Once.Arith.Prim`) enumerates the compiler's arithmetic primitives
  (`p-add` … `p-i2f`).
* Their meanings, `primSem`, are fixed there.
* The builders mint `primV p`.
* The recogniser matches the constructor (`recognise-prim`), and the meaning follows
  definitionally.

**Consequence.** Behaviour is unchanged: names, emitted symbols and `semM` values are all
the same. A pure FFI contract can no longer be mistaken for arithmetic.

## D256 — THE BIDIRECTIONAL JUDGMENT IS COHERENT, PROVED BY ROUTES (2026-10-02)

**Relates**: plan 0.55 A4 (the postulate `realize-invariant`), plan 0.103 6a‴, D226 (one subtyping
judgment, `<:-unique`), D228/D230 (domain-given mode, the spine), plan 0.94 §10 (compose's middle
type), `ModeAgreement` (plan 0.94 C3).

**Context.** The telescope walk joins the checker's derivation (which the compiler compiles,
D254) to the typed module's. Their meanings agreed only by the postulate `realize-invariant`:
any two derivations of one judgment realize to terms with the same meaning. The judgment overlaps
(`t-sub` against the direct check rules, `t-app` against the spine, `d-infer` against the
domain-given rules, the two compose-check routes), so this is a theorem about the judgment.

**Decision.** Coherence is proved, in three layers.
* A **route** (`TypeCheck.Route`) between two derivations records, rule by rule, which overlap
  they took. It is heterogeneous in their types and usages: that those agree is a consequence,
  not a premise. A constructor shares an index only where a premise's context or check type
  depends on it.
* Every pair has a route (`TypeCheck.RouteBuild`): `ModeAgreement`'s case split. It has no
  `with`: the few alignments are top-level helpers taking `ModeAgreement`'s equation as an
  argument, and impossible pairs are refuted by an absurd pattern on its result.
* Coherence (`Adequacy.Coherence`) is the induction on routes, one clause per constructor, each a
  lemma of `Adequacy.CoherenceHet`: match the carried index equations, then apply a homogeneous
  law of `Adequacy.CoherenceLaws`. Where the routes differ by where a conversion sits, they
  agree because a conversion commutes with the formers and is unique (`<:-unique`); `cata`
  needs fusion with a carrier conversion, proved by the relational fold (`CataRel`). That the
  routes' types are related at all is `TypeCheck.ModeSub`.

**Why routes, not one pairwise induction.** A single pairwise induction stating the meanings
directly could not be checked within the 30 s per-module budget: its `with`-functions generalize
goals that mention the realized meaning (measured, 2026-10-02). Splitting syntax (routes) from
meaning (induction on routes) makes each layer cheap and keeps every step `with`-free.

**Consequence.** `realize-invariant` is a theorem; the postulate module `RealizeInvariant` is
deleted. Plan 0.103 has no open residual on the apex path.

## D257 — THE SPEC MEANS A PROGRAM RELATIVE TO ITS INTERPRETATION; `Eff` IS AN INTERACTION TREE (PLAN 0.105) (2026-10-03)

**Relates**: D061 (a SigOp's contract comes from its interpretation; M0.2 never landed), D058
(the observable is the SigOp event), D225 (the Spec reads the codomain; "fixing the type is its
own plan"), D231 (`HonestFFI`), D244/D246 (the call environment), D250 (graded meaning), plan
0.98 (`Res`, halting at `Void`), D161/D165 (no compiler logic inside a toolchain axiom).

**Context.** Two defects, one cause. (1) The apex was INCONSISTENT: `generic-semM : ∀ {A B} →
String → TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧ᵍ` was in `Once.Certified`'s cone, so
`generic-semM {Unit} {Void} "x" fmt _ : ⊥` typechecked, and the Spec's `⊢sigop` meant FFI
contracts through it. No restriction of the type helps: an honest type can be empty (`μ X. X`).
(2) The trace monad was a WRITER: it could record what a computation emits, and nothing could
flow back in, so `read : Eff Unit Int` was specified as a fixed function of its argument (two
reads were equal).

**Decision.**
1. **A computation of grade π means an interaction tree** over the operations π permits: done
   with a value, an answering call `op(arg)` with a continuation awaiting the answer, or a halting
   call (an operation answering `Void`) with none. `pure` permits no operations, so its tree is a
   value (D250 unchanged). `T` is that tree; it is INDUCTIVE (Once is total; coinduction stays in
   `νᵈ`'s layers). The observable is derived: run the tree against an interpretation and take the
   first `n` calls (D058's prefix family, `projTrace-pf`).
2. **FFI contracts are the program's parameter.** An `Interp` has an effectful half (`answer`,
   given the calls so far) and a pure half (a fixed function per pure contract, so referential
   transparency holds by type). Internal operations (`pureV`/`primV`/`emitsV`/`haltsV`) are
   computed; `ffiV` reads the pure half and `callsV` is a call node. `generic-semM` is deleted;
   a program importing an uninhabited contract has no interpretation, and the theorem says
   nothing about it rather than proving ⊥.
3. **The world answers; it does not stop.** An answering call always gets an answer; stopping
   happens exactly at a `Void` codomain. An input that can fail is a sum the program sees.
4. **The concrete machine writes the answer** (Phase 4 option (a)). `RunTraceCore` threads the
   binary's own log; its external-call step writes `answer-at ι` into the return register and
   returns past the call: the ABI contract, stated once in the trusted machine model. The
   rejected alternative, an apex hypothesis "after an external call the states still
   correspond", would put the compiler's own invariant (`CompiledCorr`) inside an axiom
   (D161/D165).
5. **The Spec (`Once.Spec.Correct` = `Once.Adequacy`).** `CorrectCompiler` gains an abstract
   field `Interpretation`; `⟦_⟧ˢ` and `exec` take it; the trace conjunct of `correct` is
   `∀ ι → exec arch ι bytes ≈ ⟦ arch ⟧ˢ ι tp`. The quantifier sits INSIDE the existential:
   the typed program is chosen once, world-free, because acceptance runs nothing
   (`Compile.accept-typed`). Soundness, admissibility and completeness do not mention the world.
   The instance fills `Interpretation` with `Interp`. This is the hunk's MERGE.md justification:
   a language-level decision, recorded here.

**Consequence.** `Once.Certified` is green with every `ArchCorrect` built at every `ι` (the
per-arch resource bounds and block-table hypotheses are taken `∀ ι`, since the frame semantics
carries the interpretation). `generic-semM` has no references. Still postulated, and now about
a DEFINED step: each arch's `external-sigop-contract`. Open: the arith/FFI split of
`arith-sigop-contract` (Phase 0 found both SigOp contracts false as stated; the dispatch must
split by `SigOpSem` constructor), `SigOp.decode-boxed` (decodes a boxed argument from the pointer
alone, memory-independent; looks inconsistent), and the extraction gate (an input-reading exit
test with two differing reads).

**Amendment (2026-10-03): the dispatch split landed; the `∀ ι` is VACUOUS as stated.**
* `sigop-step` routes on `sigop-owner (sem si)` (`Internal`: `pureV`/`primV`, the compiler's
  arith blocks; `External`: `ffiV`/`callsV`/`emitsV`/`haltsV`). `arith-sigop-contract` takes
  `Internal`, `external-sigop-contract` takes `External`, so neither is stated where Phase 0
  found it false. The concrete call resolver can name a PURE FFI call (`pure-ffi`), answered
  from `ι`'s pure half, which is what the flat machine computes for `ffiV`.
* FOUND (machine-checked, `Once/Probe/InterpEmpty.agda`): `Interp → ⊥`. `answer` must answer
  every `CallOp`, and `callOp n Unit base-Unit Void` asks it for an inhabitant of `⟦ Void ⟧`;
  the pure half `FFIAnswers` has the same hole at `B = Void`. So no interpretation exists and the
  apex's `∀ ι` (decision 5) quantifies over an empty type. The cause is the "one universal
  signature" of the Phase 2 design: decision 2 and §3 of the plan meant an interpretation of
  THE PROGRAM's contracts ("a program importing an uninhabited contract has no interpretation"),
  not of every conceivable one. OPEN: the fix is a design decision (see plan 0.105).

**Amendment 2 (2026-10-03, with the user): the fix is D061's three times.** Not "one
interpretation answers every contract" (empty), and not "a world provides contracts and the run
checks" (the compiler reasoning about the world). D061: building the compiler proves the apex
over an abstract interpretation; compiling a user program sees only the DECLARED signatures and
trusts them; each interpretation's author discharges its contracts off-line. The FORM of a
contract is the compiler's (D225); interpretations follow it. So the core is parameterized over
an interpretation's declared signatures `Σ` (programs are typed against them: `⊢sigop` needs
membership) and an implementation `Impl Σ` in the compiler's contract form, total on `Σ`. An
unimplementable declaration fails its author's off-line discharge and makes no compiler claim
false. Decision 5's statement becomes: for programs typed against `Σ` and every `Impl Σ`. Plan
0.105 "RESOLVED" holds the phases.

**Amendment 3 (2026-10-03): landed.** `Once.Certified` is green with the Spec stating, for the
signatures a typed program is compiled against (`sigOf`) and EVERY `Implementation` of them,
`exec arch (sigOf tp) I bytes ≈ ⟦ arch ⟧ˢ tp I`. Structural choices made on the way: the core
signature is `Sig Fs s` (the FFI signatures are the type's parameter, so one module's walk shares
them by type); `Linked` requires an FFI SigOp to be declared (the twin of table linking); an
emitting call returns `tt` by the contract form; at the interpretation boundary a SigOp is keyed by
its rendered canonical path. Open: `decode-unread`/`decode-boxed`, the extraction gate, and one FFI
contract's several names (a front-end cleanup).

## D258 — `Str` AND `Buffer` ARE REMOVED UNTIL THE MACHINE HOLDS THEIR CONTENT (PLAN 0.106) (2026-10-03)

**Relates**: D257 (plan 0.105; its §g decodes a SigOp's argument from memory), D114
(`decode-unread`, deleted), D058 (the observable is the SigOp event).

**Context.** After plan 0.105 §g every SigOp argument is decoded from memory and proved equal to
the denotation's, except a value containing `Str`/`Buffer`. The residual for those
(`decode-boxed`) is refutable: their residence (`valid-str-wf`/`valid-buffer-wf`) carries no
content, and a string literal's machine output (`structured-pure-sigop-output`) has none either.
No rewording is consistent: content-free residence breaks the argument, content-carrying
residence breaks the literal's result placement. The abstract machine does not hold strings.

**Decision.** Remove `Str` and `Buffer` from the language (types, IR, semantics, machine, type
parser) and delete the string-literal typing rule; the lexer token and AST node stay. They come
back in a later plan that models their content in the abstract machine and its concrete
correspondence. No exit test used them.

**Rejected.** A Spec premise excluding programs that pass strings to SigOps (keeps a type the
theorem excludes); keeping the refutable residual as a documented gap (the apex stays
inconsistent).

## D259 — PLANS 0.105 AND 0.106 CLOSE; THE GATE FOUND A RISCV64 FRAME BUG (2026-10-04)

**Relates**: D257 (plan 0.105), D258 (plan 0.106), D245 (direct calls), D161 (the trace owns
`ret`), D228/D226 (0.99 F, the same extraction gate).

Both plans close at one gate: `Once.Certified` green; MAlonzo re-extracted and synced; `cabal
test` 775/775; exit tests 72/0/0 on x86-64, x86-32/qemu and riscv64/qemu, including the new
`answer-two-reads` (two `fd_dup 1` calls answer 3 then 4: the world answers, a fixed function
would not). The plan files are deleted; their closure lives here.

### What landed

* **0.105 (D257 + amendments 1–3).** A program means an interaction tree run against an
  interpretation; FFI contracts are the program's parameter (`Once.Spec.Contract`: `ISig`,
  `contractOf`, `Impl Σ`); `generic-semM` deleted; the Spec's trace conjunct holds at every
  implementation. §g: a SigOp argument is decoded from MEMORY (`decode-at`, `readTyped` with
  Float and sums); `decode-unread` deleted (it gave `⊥` at `base-Void`).
* **0.106 (D258).** `Str`/`Buffer` removed, string literals rejected
  (`StringLiteralUnsupported`), `Readable` total on base types, `decode-boxed` deleted.

### What the gate found

`riscv64-irToAsm` hand-wrote an ENTRY-style frame (allocate `budget*8+8`, save `ra` inside) while
`c-ret` and every direct call (`c-call-fn`, D245, plan 0.103) are CALLEE-style: the caller
reserves the `ra` word and `c-ret` releases it. A directly-called function returned with `sp`
8 bytes low and 45/72 riscv64 exit tests segfaulted; x86 cannot see it (`call`/`ret` own the
word). The prologue is now `c-entry`'s own lowering, label dropped — the verified program image
always opened with `c-entry`, only the text path diverged — and `_start` reserves `main`'s slot.
The proof could not catch it: the emitted TEXT is outside the verified image (the class D157
names). x86-32's Linux interpretation gained `fd_dup`.

### What remains, and where it went

* `obs-correct-sigop-rest` — now exactly a NON-REGISTER CODOMAIN (structured pure/prim/FFI
  results, e.g. the comparisons' `Unit + Unit`, and answering calls returning one): plan 0.88's
  row; stated `∀ si`, narrowing it is part of that row.
* `lt-semM … ne-semM` postulated pending the Bool encoding (0.105 §6) — with the row above.
* One FFI contract still has several names (entry `bare x`, qualified, resolved) — a front-end
  cleanup, the import table keyed by `CanonicalName`.
* Strings and buffers come back in their own plan (D258's out-of-scope list: representation,
  a static-data region for literals, the concrete correspondence, `Buffer`'s mutability).
* Termination vs divergence in `Behavior` — plan 0.97 §6.
* Pre-existing islands seen by the island pass (not introduced here): `Adequacy.AnaBridge`
  (`T.resT`, the pre-0.105 trace shape), `Semantics.Coherence` (a parse error),
  `Spike.RelSpike`. Stale `ModuleDoesntExport` warnings remain (hygiene).

## D260 — PLANS 0.97, 0.98, 0.99, 0.103 AND 0.104 CLOSE AT THE D259 GATE (2026-10-04)

**Status (2026-10-09)**: its "sub-usage (QTT q ≤ q′) out of scope" is superseded by D276 (affine grades, `⊢sub-use`).

**Relates**: D259 (the gate), D227 (0.99 E), D228 (0.94 b′, which closed 0.99 §8), D246/D256
(0.103), D250/D251 (0.104).

Each of these plans had only the extraction gate left (0.98 F and 0.99 F share it, 0.103's
header says "the one remaining step", 0.104 "Next: the gate"); D259 ran it. The files are
deleted; their closure lives here.

### What landed

* **0.97** — the Spec models stopping (C, D; E discharged 0.88's `Halts` row). Its mechanism
  (`stops-D`, four conditioned fields) was then replaced by 0.98's `Res`.
* **0.98** — a halting SigOp does not return: `Res`, `haltsV : B ≡ Void`, `semM → Res`, `stops-D`
  deleted, `place` type-forced; E via 0.99 (D227). Stage D's last red module, `Adequacy.AnaBridge`
  (`T.resT`, superseded by `GradedAnaBridge`, D250, no importers), is DELETED here; the
  unimported `Semantics.Coherence` (red since 0.72 P2's two-carrier base interpretation and
  D243's rigid case) is REPAIRED rather than deleted, because OCP-0003 and the structured-
  recursion guide cite it.
* **0.99** — one subtyping judgment (A–E; §8 by 0.94 b′, D228).
* **0.103** — polymorphism in the core; the core is the Spec (D246); no open apex residual
  (D256).
* **0.104** — `pure` is referential transparency (D250); ex falso is `initial` (D251).

### What remains, and where it went

* Termination vs divergence in `Behavior`/`_≋_` — 0.97 §6's FOLLOW-ON row, unowned; D259 lists
  it too. A new plan when taken up (it changes what `correct` claims).
* 0.99 §6, deliberately out of scope: variance under `μ`/`ν`; sub-usage (QTT `q ≤ q′`).
* 0.103's performance follow-on (profile-2026-09-29): `Apply.call-eq`, `Pair.{bf,heapref,cf}-tail`,
  a backend re-profile. `PairAssemble` is no longer extracted.

## D261 — THE RISCV64 SEGFAULTS HID BEHIND `riscv64-loader-faithful`; EVERY PROLOGUE IS `c-entry`'S LOWERING (2026-10-04)

**Relates**: D259 (the gate that found it), D245 (direct calls), D161/D165 (compiler logic must
not live inside a toolchain axiom), D100/D167 (the axiom's honest preconditions), plan 0.89 D4.

**The question asked of every green-apex/red-binary pair: which postulate hid it?**
`riscv64-loader-faithful` (`ArchCorrectness/RiscV64.agda`), class "(A) TOOLCHAIN TRUST —
assembler + loader + printer". It states `asm-sem asm ≡ conc-trace (main (rewrite-program …))`:
the emitted text means what the concrete machine does on the VERIFIED image. The image opens
each program function with `c-entry` (callee-style: the caller reserves the `ra` word, `c-ret`
releases it). The text did not come from the image: `riscv64-irToAsm` hand-wrote an
ENTRY-style frame. So for every program with a direct call (D245, plan 0.103) the postulate
was FALSE — it trusted, under the name "printer", a compiler decision that disagreed with the
image. Exactly D161/D165's fault one level down.

**Fix.** All three `irToAsm`s now emit `drop 1 (compile-abstract (c-entry (e-fn o) budget))`:
the entry's own lowering, label dropped (`functionPrologue` writes it). riscv64's changed (and
`_start` reserves `main`'s slot); x86-64's and x86-32's agreed with their `c-entry` lowering
only by coincidence and now agree by construction — their binaries are byte-identical (checked
on ten test programs).

**What remains.** The text is still ASSEMBLED from per-function pieces in `Compile.agda`, not
printed from the image, so the axiom still covers more than printer + `as` + `ld`. Plan 0.89
gains row D4: the emitted text is `programToText (link image)` plus a fixed arch-only stub.

## D262 — TRUST ONLY `as`: THE LOADER AXIOMS ARE GONE; THE START IS PROVED CODE (2026-10-04)

**Relates**: D261 (the bug that forced it), D161/D165, D100/D167/D169 (the text-level residuals
this consolidates), plan 0.107, plan 0.89 D4.

**The trust law.** `ArchSemantics` gains the assembly FILE (`File`, per arch an `Image` of code,
entry, arith blocks and externs), its canonical text `print`, and ONE law,
`as-faithful : ∀ F → AsmWF F → decode (assemble (print F)) ≡ just (program F)`. The compiler's
result is the file; the CLI's text is `print` of it. `<arch>-loader-faithful` (three
postulates over the emitted TEXT) are deleted, and so are the postulated `arith-env-<arch>`: the
arith table is the file's (`block-env (blocks F)`), tied to the engine by an `ArithTable`
relation that names the program the image came from.

**One walk.** The emitted code is `compile-trace-cnt` of `program-image` — the image every proof
reasons about (`Once.Compile.image-of`). The parallel per-function text walk no longer feeds the
result.

**The start is proved code, and platform-general.** `program-image = c-start B ∷ link-top done
(main's unit) ++ table`. `c-start B` (pc 0) is a new `FlatCtrl`: flat semantics `do-thunk B`;
lowering = the heap register at the `.bss` heap's base + the frame reservation (`lea`/`lla-sym` +
`sub`/`addi`). `main` ends in a SILENT STOP (`c-label done; c-jmp done`) — programs don't return
(observables are SigOp events), so no exit syscall: the same meaning on bare metal and under an
OS. The environment contract (`initialState`) is "pc at the entry, sp in a stack region, registers
and memory empty". The run starts OUTSIDE every frame (`Reachable prog 0`, `entry-alloc 0`);
`RunWF.run-step-pc-pos` proves no step returns to pc 0, so the correspondence engine starts one
step in (`events-agree-start`, over the per-arch `block-step-c-start`) and refutes `c-start`
everywhere else (`inv-started` + `start-at-zero`). `StackRoom` covers the start's reservation as
it covers a body entry's. `file-flat-<arch>` is a THEOREM: running the file is the flat run of
the program it was emitted from.

**What is still assumed about the file**: `FileWF.file-wf` — the file is what `as`/`ld` accept
(`AsmWF`: defined once, resolved, entry in range). ONE residual over the FILE replacing three over
the text (`program-labels-distinct`, `-labels-resolvable`, `-symbols-resolvable`). Known false for
comparisons (not lifted into blocks, so their calls do not link) exactly as the old
`program-symbols-resolvable` was; plan 0.108 makes it true, and discharging it is the rest of plan
0.107 phase d. Known weakness of the environment contract: registers start at 0 in the model, so
the heap-register `lea` is not yet load-bearing in the proof (the frame reservation is — D261's
prologue is now a type error).

## D263 — COMPARISONS MEAN SOMETHING: Bool = Unit + Unit, TRUE = inr (2026-10-04)

**Relates**: plan 0.108 (phase A), D255 (compiler primitives by identity), D054 (signed words),
D262 (`FileWF.file-wf` false for comparisons).

`lt-semM … ne-semM` were POSTULATED ("comparisons need a Bool encoding decision"): the spec did not
say what `a < b` is. Decided with the user: `Bool = Unit + Unit` and **true = inr** (tag 1) — the
sum's tag is then the C truth value, so a comparison's tag IS the `setcc`/`slt` result, and `if`
branches on tag 0 for false exactly as `c-branch-tag-zero` already does. The comparisons are now
compiler primitives by identity (`ArithPrim.p-lt … p-ne`, `primV`), meaning the signed word
comparison at the target's width (`Word.Width._<ˢ_`, `_≡ʷ_`).

**Spec change, and why it is not "the proof needed it"**: `Once.Spec.Core.Meaning`'s comparison
clauses now carry `int-prim` (a primitive's meaning) instead of `int-pure` (a supplied contract). The
Spec's TEXT changes only in that witness; what changes in substance is that the meaning was
undefined and is now defined — the user's decision, not a proof convenience.

Still open (plan 0.108 B–E): the correctness proof routes `Unit + Unit` to
`obs-correct-sigop-rest`, and the emitted call does not link. The design is a TAG then an
INJECTION — a 0/1 compare in an arith block, then `bool-of : IR Int (Unit + Unit)`.

## D264 — A COMPARISON IS ITS BLOCK, THEN A TAG, THEN A SUM: proved, linked (2026-10-04)

**Relates**: D263 (what a comparison means), plan 0.108 §§5–6, D262 (`FileWF.file-wf`), D255.

**The comparison stays one IR node** (`SigOp lt-info`). A `bool-of : IR Int (Unit + Unit)` morphism
was tried and backed out (plan §6): an `IR`-level step must be correct for every residence of its
input, and an `Int` may sit behind a pointer (`in-loc`), so no word→tag step on `Input1` is sound.
The factoring lives in CODEGEN instead (`IRToTrace.cmp-trace`):

    instr-sigop (cmp-block-info op)   -- the arith block: Output := 0/1 (signed compare)
    instr-reg-op out-nz               -- Output := that word as a tag
    store-at-slot n ; instr-alloc-heap 2 ; store-at-slot (n+1) ; mov-to-input ;
    load-from-slot n ; store-indirect ; instr-load-tag-lit 0 ; store-indirect-suc ;
    load-from-slot (n+1)              -- `inl`/`inr`'s build, tag from the slot, unit payload

`out-nz` reads a word the block has JUST written to `Output`, never one behind a pointer.

**One source for "is a comparison".** `Arith.SigOp.Compare.cmp-of : SigOpSem A B → Maybe CmpOp`
(only `primV (p-cmp op)` answers). Codegen lowers by it (`sigop-trace` = `sigop-budget` ×
`sigop-code`, label and blocks independent of the choice), and the rewrite registers the same block
(`walk (SigOp si) = SigOp si , sigop-blocks (cmp-of (sem si))`), so the file DEFINES what the call
names — the reason `FileWF.file-wf` was false for comparisons is gone.

**The arith layers gain one node, all the way down.** `MArithIR.acmp`, `AbsInstr.cmp-rrr`,
`XInstr.Xcmp-rrr` (meaning `CmpOp.cmp-bit`, the 0/1 word), emitters (x86 `cmp; set<cc> %al;
movzb`, riscv `slt`/`xori`/`sub`+`seqz`/`snez`), `CompileCorrect.acmp-correct`, the backend refine,
the three ArithSims (`rt-cmp`) and confinement (x86 writes `%rax`/`%eax`). `ArithPrim`'s six
constructors became `p-cmp : CmpOp → …` (`Once.Arith.CmpOp`, one operation code).

**The proof.** `IRObsCorrect.Compare.cmp-obs` is the comparison's `IRObsCorrectF`, over
`NineStepPres` started after the two register steps; the denotation is `ret (bool c)` and the place
is `valid-inr-reg-wf`/`valid-inl-reg-wf` by the tag. `obs-correct-sigop` routes by the contract,
enumerated (no catch-all): the comparison here, every other SigOp to `obs-correct-sigop-nc` (which
carries `cmp-of (sem si) ≡ nothing` to see its one-instruction emission). Comparisons no longer
reach `obs-correct-sigop-rest`. The Spec closure is unchanged.

**Addendum (same day): a BARE primitive is a block too.** The gate's new comparison test failed
to LINK, and not because of comparisons: `4 * bit c` leaves `SigOp arith.mul.int` bare once its
operand pair (a `case`) is not arithmetic, and the recogniser only matched `SigOp si ∘ e`, so the
call named a symbol nothing defined — the exact hole `FileWF.file-wf` was postulated over. The
walk now lifts a bare primitive as `SigOp si ∘ id` (`Rewrite.bare-at`): the recogniser reads `id`'s
operands as the input's own leaves (`BView.bv-id`), `LiftSound` proves that case from the leaf
lemma, and `RewritePreserves.bare-sound` is the monad's left identity. Lifting there (not with a
`v-bare` view on `SigOp si`) keeps `body-at`'s domain index `⌊ shape ⌋` free of the stuck
`⌊ X ⌋ ≟ ⌊ shape ⌋`. Test `arith-bare-op` (`inc 3 * inc 4`). Exit tests 74/0/0 ×3, cabal 775/775.

## D265 — A `cata` ALGEBRA MAY CAPTURE LOCALS (plan 0.101, the `cata` half) (2026-10-05)

**Status (2026-10-09)**: the `ana` half it leaves open is closed by D273.

**Relates**: plan 0.101, plan 0.94 §0 (`let x = e in b` and a top-level `x = e` used in `b` are
interderivable), D131 (the algebra is obtained once), D127, plan 0.76 risk 3 (which deferred this
widening to its own entry — this one), D192/D179 (ana).

**The language change.** `t-cata-check` and `d-cata` type the algebra in the AMBIENT context and
the fold's usage is the algebra's (`Ψ`, not `zeroUsage`). This is the core's `⊢fold` (the algebra
is an ordinary term in context) and removes the last place where a definition and its definiens
were not interchangeable for `cata`: `f k = cata (case (\_ -> k) add)` and
`let b = 2 in cata (case (\_ -> b) add)` are now accepted.

**Spec hunks, each forced by that rule and nothing else:**
* `TypeCheck.Judgment` (= `Spec.Typing`): the two rules above.
* `Denotation.Meaning` (= `Spec.Meaning`): the algebra's meaning is read at the term's own
  environment `dγ` instead of the empty one `tt` — the premise now lives in that context.
* `Spec.Elaboration`: the algebra elaborates in the same context, so `closeE` is not applied.

**Implementation.** `Surface.cata` carries `Expr Γ Ψ`; the compiler elaborates `cataM ∘ elaborate alg`
(no `∘ terminal`): the algebra is OBTAINED ONCE, both in the IR and in the meaning, as D131 already
required. `Unfold`'s substitution now scopes lexically under a cata algebra (`isAlgV ahv-cata =
false`); `LetIsDef` transfers the algebra like any subterm. Exit test `cata-capture`.

**`ana` is NOT changed (the other half of plan 0.101, open).** Its meaning re-runs the coalgebra at
every forced layer (D179), so a captured coalgebra must see a FIXED environment with the seed
varying — a parameterized `Ana` in the IR (`IR (E × A) …`, the mirror of D131's parameterized
`Cata`). Threading the environment through the SEED instead gives a ν that is only bisimilar, not
equal, to the meaning's (`νᵈ` is coinductive), and the project has no bisimulation-to-equality
axiom. The parameterized `Ana` touches the ν codegen (suspension cells, re-suspension) and its
correspondence proofs, so it is its own step. Until then def ⇒ let still fails for `ana`.

## D266 — THE RUNTIME CONTRACT WAS A POSTULATE OF ⊥; ITS REGIONS ARE NOW ORDERED (2026-10-05)

**Relates**: plan 0.100 P0, `Memory/RuntimeContract.agda`, the three `<arch>-runtime` postulates,
the residual ledger (an inconsistent axiom is the worst class).

**The defect.** `RuntimeContract` placed the stack at `[0, stack-upper]` and the code at
`[0, code-upper]` — both contain address 0 — while POSTULATING `intervals-disjoint`, and its
`prog-fits : ∀ prog-len → prog-len ≤ code-upper` is false at `suc code-upper`. So the record type was
EMPTY, and each per-arch `postulate <arch>-runtime : RuntimeContract` was a postulate of `⊥`, in the
apex's import cone (the `Layout` modules instantiate `Regions`/`StackSlots`/`FrameOps` with it, and
the apex uses `InStack`, `stack-addr`, `stackAddr-write-preserves-heap`). The probe derived `⊥`
both ways before the fix.

**The fix.** The regions are ORDERED — stack `[0, su]` below heap `[hl, hu]` below code `[cl, cu]`
(`stack<heap`, `heap<code`, both bounds valid) — and `intervals-disjoint` is a THEOREM of the
order. `prog-fits`, `pc-in-code` and `code-lower-zero` are deleted: nothing consumed them.
`Probe.RuntimeContractModel` builds an instance, so the per-arch postulates are of an inhabited
type. Apex green; no consumer changed.

## D267 — `StackSlots.slot-in-stack` WAS A POSTULATE OF ⊥; DELETED (2026-10-05)

**Relates**: plan 0.100 P0 audit (after D266), `Memory/StackSlots.agda`, the residual ledger.

**The defect.** `slot-in-stack : ∀ sp k → InStack (slot-addr sp k)` (its `suc` case a local
postulate `slot-in-stack-suc`) claims every slot of every stack pointer lies in the stack. `grow`
is injective in the slot and the stack `[lower, upper]` is finite, so `suc (suc upper)` slots of
one pointer map injectively into `suc upper` addresses: pigeonhole gives `⊥` (probe checked,
then deleted). It sat in the apex cone (every `Layout` instantiates `StackSlots`).

**The fix.** Deleted, with its postulate: nothing consumed it (`slot-in-stack-0` stays, a theorem;
slots past 0 take capacity evidence from `StackCapacity`). Apex green.

## D268 — THE CONCRETE TRACE LAWS WERE A POSTULATE OF ⊥; THE BUDGET NOW READS THE RUN (2026-10-05)

**Relates**: plan 0.100 P0 audit (after D266/D267), `Arith/Backend/RunTraceCore.agda`, the three
`Adequacy/CPU/<arch>` modules, ledger P2 and #11 (`conc-fuel`), D179, D5.

**The defect.** `RunTrace.run-trace-extends` / `run-trace-saturates` — the `Behavior` laws of the
concrete machine's fuelled trace family — were postulated inside the parameterized module FOR
EVERY `stepBudget`. A non-monotone budget (`1 ↦ 1`, else `0`) on a one-instruction toy instance
emitting one event refutes `extends` at `n = 1` (`[] ≡ e ∷ rest`); the probe derived `⊥` (deleted).
Every arch's `run-trace-<arch>` used them, so it was in the apex cone.

A second, semantic defect sat under it: `step-budget-<arch> : ℕ → ℕ` was program-INDEPENDENT, and
no such function is adequate — programs with arbitrarily long event-free prefixes exist. So the
ledger's route for `conc-fuel` ("pin `step-budget` to a definition") was unavailable at that type.

**The fix.** `run-trace` takes the laws as a premise (`RunTraceCore.Adequate fam`). Each arch's
budget reads the run — `step-budget-<arch> : blocks → code → state → ℕ → ℕ` — and one postulate
per arch, `step-budget-<arch>-adequate`, states adequacy of THAT budget at the arch's `ev`. It is
consistent (the step count to the n-th event, or to the last one, is such a budget) and is the
named CPU-model axiom until the budget is defined. `conc-fuel` is unchanged in meaning, observed
at `conc-budget` (the budget of the run it states). Not Spec: the concrete run is
implementation-side. Apex green.

## D269 — DEAD POSTULATES OVER A MODULE PARAMETER, TWO OF THEM ⊥, DELETED (2026-10-05)

**Relates**: plan 0.100 P0 audit (D266–D268), `CCC/Machine/SMPrimitives.agda`,
`CCC/Machine/ClosureWellFormed.agda`.

**The lesson of D268, swept.** A postulate inside a parameterized module holds for EVERY
instantiation, so it is only as true as its weakest instance. The sweep listed 22 postulate blocks
under module parameters in the apex's import cone. Those with no consumer outside their own dead
lemma are deleted, with the lemmas:

* `REFUTABLE-effect-state-only-frame-dep` (⊥ at `instr-alloc-heap`, its own comment said so) and
  the three trace lemmas it fed — `exec-trace-same-frame`, `exec-trace-state-frame-eq`,
  `TraceWF-frame-eq` — none used;
* `REFUTABLE-alloc-heap-trace-preserves-heap-ref`, `case-on-tag-`/`loop-trace-preserves-heap-ref`
  and `exec-trace-preserves-heap-ref` (unused);
* `mem-deterministic-step` (no premise relates its two states — false) and
  `exec-trace-mem-deterministic` (unused);
* `case-on-tag-`/`loop-state-next-slot-invariant` and `exec-abstract-state-next-slot-invariant`
  (unused);
* declaration-only: `exec-trace-independent`, `exec-trace-independent-below`,
  `exec-trace-deterministic`, `exec-trace-output-deterministic`, `prod-left-setup-mem-helper`,
  `prod-left-setup-saves-input`, `validityWF-mem-preserved-excluding`, `ν-validity-in-regions-stub`.

Nothing outside the deleted lemmas named them; apex green. The LIVE ones are taken one at a time
(D270 onward).

## D270 — THE LIVE ⊥s OF THE STRUCTURED MACHINE: THE PREMISE THEY WERE, OR ABSURD (2026-10-05)

**Relates**: plan 0.100 P0 audit (D266–D269), `CCC/Machine/SMPrimitives.agda`, `SMCore.agda`,
`ClosureWellFormed.agda`.

* **`sigop-preserves-halted`** said no SigOp halts; `exec-abstract` halts on a `Halts` SigOp (an
  `exit`), so it was `⊥` given any running state (probe checked, deleted). Its own comment called
  it "a premise the caller owes", so it is one now: `InstrWF s alloc (instr-sigop si)` IS the fact
  that the step does not halt, and likewise for `instr-case-on-tag` (runs a sub-trace) and
  `instr-loop` (fuel can run out) — whose `*-preserves-halted` postulates go too. No caller ran
  `exec-abstract-preserves-halted-WF` at those three; `InstrWF-frame-eq` (unused since D269) is
  deleted rather than extended.
* **`worklist-push-preserves-stack-slot`** said `worklist-push k` changes no stack slot; it writes
  slot `k`. Its consumer's premise `instr-writes-slot i ≡ nothing` is `just k ≡ nothing` there,
  so the clause is absurd and the postulate is gone.
* **`exec-abstract-preserves-not-halted'`**, a `where`-postulate of `exec-trace-++` — "no
  instruction halts", over every instruction and state. `exec-trace-++` was unused
  (`exec-trace-append` is the proved law); both deleted.
* **`μ-validity-in-regions-stub`** moved validity between ARBITRARY states; with the dead
  `validityWF-mem-preserved-in-regions` (unsafe) and `-strong`, `LocInRegions`/`LocsInRegions`
  (347 lines, nothing outside used them), deleted.

Apex green.

## D271 — TWO MORE POSTULATES OF ⊥, BOTH UNDER DEAD CODE: DELETED (2026-10-05)

**Relates**: plan 0.100 P0 audit (D266–D270), `SigOp/Info.agda`, `Optimize.agda`,
`CCC/IR/Stack.agda`.

* **`sigOpInfo-name-coherence : name si₁ ≡ name si₂ → si₁ ≡ si₂`** — `⊥`: `mk-info' n ffiV b b` and
  `mk-info' n callsV b b` share a name and differ by constructor. It existed to make
  `_≟SigOpInfo_` a `Dec`, for the optimizer's IR decider `_≟IR_`. No live module calls `_≟IR_`
  (its importers — `Optimizer.Normal`/`IRReducible`/`PairCaseNormal`, `Optimize.Shape` — are red
  islands outside the cone), and it cannot be made honest: a `pureV` semantics is a function, so
  `SigOpInfo` equality is undecidable. The decider (its `HeadView`, aux helpers, and the
  postulate `≟const-irrelevant`) and `_≟SigOpInfo_` are deleted; `IRHead`/`_≟IRHead_`, which the
  eta rules use, stay. Equality of signature members is `_≟SigOpInfo-name_`.
* **`sum-`/`prod-layer-cap-bound`** — `layer-capacity (wf-Sum wf-Id wf-Id) wfG alg ≤
  ir-stack-requirement (Cata wfG alg)` reads `2 + R ≤ R`; the file's own comments said
  "BLOCKED: this is false when children contain Id". The whole layer-capacity model
  (`layer-capacity`, its Sum/Prod lemmas, `layer-cap-bound`, `ir-stack-req-geq-layer-cap`) had no
  consumer outside `Stack.agda`; deleted.

Apex green.

## D272 — FINDING: THE TOOLCHAIN AXIOM `as-faithful-<arch>` IS ⊥ AS STATED; FIX BELONGS TO THE SYMBOL-NAMESPACE DESIGN (2026-10-05)

**Status (2026-10-09)**: RESOLVED by D274/D275 (one FFI identity; a total symbol encoding) — `as-faithful-<arch>` is no longer ⊥.

**Relates**: plan 0.100 P0 audit (D266–D271), plan 0.107 phase d (§7, blocked on the
symbol-namespace design), `Adequacy/CPU/<arch>.as-faithful-<arch>`, `CCC/Target/<arch>/File.agda`.

**The defect.** `as-faithful-x86-64 : ∀ F → AsmWF F → decode (assemble (print F)) ≡ just F`
claims `print` is injective on well-formed images. It is not:

1. `print` drops `externs`. `mkImage [] nothing [] []` and `mkImage [] nothing [] ("x" ∷ [])`
   are both `AsmWF` and print the same text; the axiom equates them — `⊥` (probe checked, then
   deleted). The x86-32 and riscv64 twins have the same shape.
2. Printing `.extern` lines does not close it alone: `AsmWF` admits ARBITRARY symbol strings,
   so a symbol containing `"\n    ret"` forges instruction text, and two different `code`s
   print alike.

**The fix (not landed — it is phase d's decision).** `AsmWF` must carry what `as` actually
demands lexically — every defined/referenced/extern symbol is a valid assembler identifier — and
`print` must emit the externs it declares. Then injectivity is a real (provable) property of
`print`, and `FileWF.file-wf` owes symbol validity from the emitter (true by construction:
symbols are `once-symbol` z-encodings, label numbers and fixed names). This is the same
"one FFI identity; a reserved compiler namespace" decision plan 0.107 §7 is blocked on, so it is
recorded here and in the ledger, not patched halfway.

## D273 — AN ANA COALGEBRA MAY CAPTURE LOCALS; `Ana` IS PARAMETERIZED (2026-10-05)

**Relates**: plan 0.101 (the `ana` half; D265 was the `cata` half), D131 (the parameterized
`Cata`), D189/D199 (ν suspensions and re-suspension), D247 (`ana`'s coalgebra is not evaluated at
build), plan 0.94 §12 (def ⇒ let).

**The decision.** `t-ana-check` types its coalgebra in the AMBIENT context with the ana's usage
(the core's `⊢unfold` already did), and the Spec meaning reads it at the term's environment `dγ`
instead of `tt` — the same two Spec hunks D265 made for `cata`. `Spec.Elaboration` drops the
`closeE`; the core's `anaᶜ` is unchanged (its coalgebra is pure, so D247's per-call evaluation
and a once-evaluated closure mean the same).

**The IR.** `Ana : WellFormedFI F → IR (E * A) (F A) → IR (E * A) νF` — `Cata`'s mirror. Its
meaning reads the coalgebra at the FIXED `proj₁` of the seed pair at every layer, which is the
source meaning; threading the environment through the seed instead would give a ν that is only
bisimilar to it (no bisim ⇒ ≡ for `νᵈ`). The compiler elaborates `anaM ∘ elaborate coalg`
(`anaM`, `cataM`'s mirror): the closure is obtained once and is the environment. The source
meaning (`⟦ ana ⟧ˢ`) binds the coalgebra once too, as `cata`'s does.

**The codegen.** A suspension's seed cell holds the pair `(e , a)`. The forced block keeps its
input pair in slot 0 and runs the coalgebra from frontier 1; each `wf-Id` re-suspension builds a
fresh pair whose first cell copies the environment cell of the slot-0 pair, then the two-cell
suspension on it. The structural lemmas (slot budget — `resuspend-below` gains `env < n`; label
scope/range; thunk scope; frame-free; calls-linked; alloc-min; refs-closed; slot-stable) follow;
`obs-correct-Ana`/`-Out` generalize over the seed type (a pair seed is never `Unit`); the
BlockRuns premise `CoalgRuns` speaks of the pair seed.

**Consequence.** `LetIsDef`'s converse obstruction is gone (`ana` coalgebras scope lexically, so
`Unfold`'s algebra-position flag is constant `false`). Exit test `ana-capture` (41): a captured
`k` and a `let`-bound `b`, each forced through a re-suspension. Apex green.

## D274 — AN FFI DECLARATION EXTENDS THE PROGRAM'S SIGNATURE Σ; IT IS NOT A DEFINITION (2026-10-06)

**Relates**: D009/D061/D071 (an FFI reference IS the interpretation's operation), D246 and D249
(amended here, for FFI declarations), D248 (`own x`), D257 + amendment 2 (`Impl (sigOf tp)`),
plan 0.107 §9 (option A, user-approved 2026-10-06), plan 0.111 (the ABI half, not here).

**Found** (plan 0.107 §9, measured on `apply-eff-closure.once`, x86-64). Every signature of
every imported interface became a table entry with code: named by the dotted `bare` string, its
body calling ITSELF, called by nothing. They exist because since D246/D249 an FFI declaration is
ALSO a module entry: `Spec.Module`'s `ffi` step put it in the definitions scope (`addImp`), the
import environment gave its call the contract, and the IR table got `irFunOf (primCF …)`. Only
the lexer (no dotted identifiers) kept a plain-name call away from the imported ones; an OWN
`signature` (`examples/threads.once`) WAS reached by a call (`own x ↦ closure x`), so its
program called the self-calling wrapper.

**Decided.** A program is a morphism of the free CCC on a signature Σ. A `signature`
declaration is a GENERATOR of Σ (assumed; it means something only under a model, the
interpretation); a definition is BUILT from generators. The denotation already separated them
(`Spec.Core.Meaning`: `DefSem = defs × impl : Impl (sigOf S)`; `Spec.Core.Translate` never made
an FFI declaration a core `def`). The module level and the typing context now agree with it:

* `Spec.Module.Scope` has a `sig` part. The `ffi` step extends `sig`, never `imps` (the
  definitions). Σ of a typed module is still `teleSig` (= `entrySig`).
* The typing context (`NamedCtx`) carries Σ in scope (`sig`) beside the definitions
  (`imports`). A reference to a generator reads Σ: `t-var-qualified`, and `t-var-resolved` for
  EVERY canonical name, own or not; its meaning is the SigOp (`sigOpRefᵛ`, `sigop`). A
  reference to an own DEFINITION is the new rule `t-var-own` (`RResolved (own x)` found in
  `imports`), and a bare one `t-var-import`; both are calls (D246, unchanged for definitions).
  `t-var-own` carries `lookupImport (sig ctx) x ≡ nothing`: Σ is read first, exactly as the
  elaborator does, so the judgment stays syntax-directed (`ModeAgreement`, `RouteBuild`) without
  leaning on D249's guard.
* The Spec's import environment (D246) and the elaboration `View` hold definitions only.
  `Spec.Elaboration.ImportAt` loses its `ffi` case; a reference to Σ is `View.declared`.
* The compiler adds no `CompiledFun` for an FFI declaration: the function table holds built
  definitions only, the image has no FFI code, and the dead wrappers disappear from every
  binary. A reference to an own `signature` is the SigOp `own x` (symbol `once_<x>`), an extern.

**As built (2026-10-06).** `NamedCtx` gains `sig`; the top-level context is one value
`TopCtx = (Σ, definitions)` (`ctxWithImportsAndPolys : TopCtx → PolyCtx → NamedCtx`), so a
telescope entry's declaration scope (where the resolver re-elaborates its body) carries Σ too.
`Spec.Core.Translate` gains `SigSig Fs sg` (each generator in scope is in the program's
signatures, honest and ground) beside `ImpSig` (definitions only; `i-ffi` is gone). The
adequacy walks (`TeleWalk`, `ProgramLinked`, `CoreEnv`) lose their FFI-entry case and gain
"Σ grows", and the scaffolding that told an FFI key from a definition by its spelling
(`DefsValid`, `lookup-ffi`, `notOwn-invalid`, `TeleEntry.ffi-entry`, `FunBundle.primCF`,
`CompiledFun.cfIsPrimitive`) is deleted: Σ's lookup gives the declaration directly. The file's
externs are `Compile.externs-of p`: the SigOp symbols the rewritten program calls that are not
its blocks, so `ImageWF.prog-sigops` — a postulate KNOWN FALSE since plan 0.107 §7 — is a
theorem. Rigid substitution needs Σ ground as well as the definitions (`RigidSubst.TopRF`).

**Amends** D246 ("a module entry's reference is a call", "the compiled function table includes
the FFI entries"): an FFI declaration is not a module entry. D249's distinct-names guard is KEPT:
names stay pairwise distinct across definitions AND signatures, so `t-var-resolved` and
`t-var-own` never compete for a well-guarded module.

**Once.Spec header** gains the THREE TIMES (D061/D257): building the compiler = proving
`correct`, `∀ I`; compiling a program = `compile` and `sigOf tp` (Σ is a function of the
program); an interpretation, offline = an `Impl (sigOf tp)`.

**Addendum (2026-10-06, plan 0.107 §12).** D072's principal-type oracle (`TypeCheck.Principal`,
untrusted) still read leaves from the definitions only, so sig-less programs referencing an FFI
name were rejected (`infer-compose` ×3). It now reads `sig ++ imports`, the kernel's order. The
apex could not see this: the oracle is outside the verified loop by design (check-after-infer),
which makes such a defect a completeness loss, never a miscompilation.

## D275 — THE SYMBOL ENCODING IS TOTAL: EVERY NAME RENDERS TO AN `as` SYMBOL (2026-10-06)

**Relates**: D272 (`as-faithful` true as stated; `AsmWF.symbols-valid`), plan 0.50
(`once-symbol-path`, z-encoding), plan 0.107 §8 step 4, D061 (an interpretation's symbol is
the CLI's rename of the same mangling).

**Found** (plan 0.107 §8 step 4, while discharging `ImageWF.{prog,lib}-externs-valid`). The two
postulates said every extern the file declares is an `as` symbol name. They were FALSE: the
residual quantifies over every resolved `Module`, and a module whose signature is named, say,
`a b` typechecks a reference to it (`t-var-resolved`), realizes `sigOp (canonical ["a b"])`, and
`z-encode` passed the space through, so the file declared `once_3a b`. Step 1's note "true by
construction: symbols are `once-symbol-path` of lexer identifiers" held only for names that came
from the lexer, and nothing in the residual said so.

**Decided (make the model true, not the premise narrower).** The z-encoding is TOTAL. After the
seven named escapes (`z q p t b h d`), a char `as` accepts inside a symbol — a letter
(`isAlpha`), a digit, `_` — stands for itself; ANY other char takes the generic escape
`zu<decimal code>_`, which is self-delimiting (a digit run closed by `_`) and starts with `z`, so
the injectivity argument extends by one case. Names that are lexer identifiers or arith-block
names encode exactly as before; nothing the compiler emits today changes.

**Consequence.** `Target.SymbolValid.once-symbol-path-asm : ∀ cn → AsmSym (once-symbol-path cn)`
holds for EVERY canonical name, so all four validity residuals are theorems with no premise
(`Adequacy.ImageValid`): the defined symbols (labels, entries, blocks, `once_heap_base`,
`_start`) and the externs. `Label`'s decimal rendering is `showInBase 10` (the digits-provable
one; same output). The CLI's Haskell mirror (`Once.Target.SymbolName`) gets the same rule, with a
golden vector on both sides (`["a b"] ↦ once_7azu32_b`).

---

## D276 — GRADES ARE AFFINE: `One` IS AT MOST ONCE; THE ORDER IS PART OF THE SEMIRING (SUPERSEDES D003) (2026-10-06)

**Supersedes**: D003 (its semiring stands; its reading of `One` as "used exactly once" and its
silence on the order do not). **Relates**: D143 (erasure is semantic), D232 (standard QTT
scaling), D250 (pure is referential transparency), plan 0.102 §6–§7, the OCP-0009 linear-core
direction (`bootstrap/poc/OCP0009/NbEPLinCore.agda`, `NbEPLinQTT.agda`).

### Context
Plan 0.102 phase B found the exact-usage substitution lemma FALSE in `Spec/Core`: `case` joins its
arms' usages with `⊔`, the judgment has no sub-usaging, and `⊔` does not distribute over `+`
(`case (inl unit) [x] [y]` with `y` substituted for `x`: the only derivable usage is `{y:1}`, the
lemma claims `{y:ω}`). Categorically: the graded syntax does not form a category — composition
(substitution) is not defined at the grade the model gives it.

The fix needs an ORDER on grades, and D003 fixes none while saying `One` = "exactly once". The
Spec as written is already affine: `case`'s `⊔` (with `Zero < One`) lets a grade-1 variable go
unused in one arm, `⊢fst`/`⊢snd` discard a component, and `⊢lam` admits a body using its binder
below the arrow's grade. D003's text and the rules disagree.

### Decision
1. **`One` means at most once (affine).** The order is `Zero ⊑ One ⊑ Omega` (`≤q'`, `_⊑ᵘ_`
   pointwise), and it is part of the structure: `Quantity` is an ORDERED semiring.
2. **`Spec/Core` gets sub-usaging**: `Γ ⊢[ Ψ ] t ∷ A ! π → Ψ ⊑ᵘ Ψ′ → Γ ⊢[ Ψ′ ] t ∷ A ! π`. Its
   meaning is the model's discard, `restrictᵛ`.
3. **`case` takes both arms at one usage.** The join is derived (each arm sub-used to `Ψₗ ⊔ Ψᵣ`).
   The SURFACE judgment is unchanged: it stays syntax-directed and keeps `⊔`; the translation to
   the core inserts the sub-uses.

### Rationale
- **The principle is "the order is the model's maps".** Affine (a semicartesian symmetric monoidal
  category: the unit is terminal, every object can be discarded) and linear (a symmetric monoidal
  category without discard) are both principled; what is not is an order that disagrees with the
  rules. Once's rules discard, so the order is affine.
- **It is what the OCP-0009 linear core is.** `NbEPLinCore` has `drop : LTm A One` at every `A`,
  free (`df-drop`), next to `dup`; its `lcase` takes both arms over one context and reconciles
  with `drop` — this decision's `case`. Its results (`𝟙` needs no `dup`, forced by `𝟙 + 𝟙 = ω`;
  `dyn-linear`: dup-free code allocates nothing) are about duplication, which affine forbids too.
- **Nothing the compiler wants is lost.** In-place update needs uniqueness (no duplication), not
  consumption. GC-freedom holds with a compiler-inserted release at each discard. Only "must be
  consumed" (a protocol step the compiler cannot perform for the program) needs linearity; if it
  is ever wanted it is a per-type property (types without `drop`), which rejects nothing accepted
  today, unlike a global switch to the linear order.
- **The metatheory becomes exact.** Substitution at `Ψₜ +ᵘ q ·ᵘ Ψᵤ`, let = def and narrowing hold
  as equalities, so the term model is a graded category and ⟦_⟧ a functor out of it (plan 0.102 §4 B).

### Consequences
- Accepted programs: unchanged (the surface judgment is today's).
- `Spec/Core/Typing`: `⊢sub-use`, `⊢case` at one usage; `Spec/Core/Meaning`: one clause each.
- The surface→core translation and the core bridges follow the red.
- D003's "enables GC-free execution" now reads: GC-free with releases at discards.

---

## D277 — RE-EXPORTS ARE FOR INSTANCE SHARING AND THE SPEC DOOR ONLY; REMOVALS AND DEAD IMPORTS ARE MACHINE-VERIFIED (2026-10-07)

**Amended 2026-10-09 (plan 0.92 closed, 366 → 164)**: what stays is listed in plan 0.92 §11 — the Spec door, islands, and re-exports of APPLIED / parameterised modules (including record opens inside them, whose importers use the names through the applied copy). The import discipline this aims at is OCP-0010 (one import form, no re-exports but a declared `facade`).

**Relates**: plan 0.92 (all of it), MERGE.md §1 (the Spec is a re-export closure) and §4e,
the fork's `--name-resolution-report` (a2e94f6c53) and `--write-ast` (`run-ast-dumps.sh`).

### Context
A `public` re-export scopes its names against every local import in every importer's cone:
adding two lines to `IRObsCorrect/Prelude` once broke unrelated modules with `[AmbiguousName]`
1,600 lines away (plan 0.92 §1). By 2026-10-05 the tree carried 366 `public` lines; attempts to
remove them by reading the red failed (constructors silently became pattern variables; aliases,
renamings and module-name clashes defeated grep). Separately, thousands of imported names were
listed but never used.

### Decision
1. **A `public` re-export is allowed only (a) to share the instantiation of a parameterised
   module, with a measurement, or (b) as the Spec door** (`Once.Spec` and its `public` closure —
   the language definition's designed surface, MERGE.md §1). Never to hide structure.
2. **The surface only shrinks**: `scripts/public-gate.sh` and its baseline (MERGE.md §4e).
3. **Removals and dead-import prunes are verified by name resolution**: `reexport-remove.py`
   records, with the fork's `--name-resolution-report`, what every occurrence in every affected
   module resolves to, edits, re-checks, and requires the same `(name, kind, resolved)` sequence
   (qualifiers excepted where the edit requalifies). The real gate (apex, island backstop) follows.
4. **Scope: apex-live code** (the `--write-ast` reachability dump). Islands are left as they are.

### Consequences
- Plan 0.92: 366 → see the plan's final count; 4,274 dead import names pruned in 344 modules.
- What the client cannot do mechanically is a DECISION, listed in the plan: re-exports reached as
  instance copies (importers apply the facade), and parameterised re-exports (S4, measured).
- A proposal for the general tool, `--dead-imports`, lives in the Agda fork
  (`DEAD_IMPORTS_PLAN.local.md`).

## D278 — WARNINGS ARE ERRORS: `-W error` IN `Once.agda-lib`, REACHED THROUGH A RATCHET (2026-10-05)

**Relates**: plan 0.109 (closed), plan 0.92 §7 (the incident), D242 / `pragma-gate.sh` (the
ratchet pattern), MERGE.md §4d. Commits 3843d1d09 (S0), 1382f5e38 (S1–S4), 8cc88893b (S5).
**Note**: back-filled 2026-10-09 (plan 0.113 E).

### Context
Plan 0.92 removed a `public` re-export; one module then reached `Arch`'s constructors only
through it, so in `arch-semantics x86-32 = …` the out-of-scope `x86-32` became a pattern
VARIABLE, the first clause a catch-all, and every arch got x86-64's semantics. Agda reported only
warnings. Plan 0.109 §0: this is "meaning drift, not inconsistency", harmless in implementation
code but not in the Spec, the trusted model, or a definition shared by both sides of a
correspondence. Agda 2.8 has no per-warning error switch. Measured (correcting §1's first
draft): `PatternShadowsConstructor` fires for a constructor of the variable's TYPE even when it is
out of scope, so the incident did warn. That warning was lost among the other warnings.

### Decision
1. S0: a census of the apex/compiler closure, 678 warnings (354 deprecations, 298 exact-split,
   16 stale `using`, 7 unreachable, 7 no-op `rewrite`, 1 useless `private`), and a ratchet
   (`scripts/warning-gate.sh` + baseline, `make warning-gate`): a count may only go down.
   Warm checks suffice because Agda replays stored warnings from interfaces.
2. Fix every warning, behaviour-preserving first. Exact-split catch-alls are marked
   `{-# CATCHALL #-}` (≈340 clauses) when they are deliberate fallbacks. The 7 unreachable
   clauses were read before deletion. One was `Fusion.fusion-once arr`, a retired constructor
   captured as a variable, whose shadowed clauses were all identities, so deleting it changed
   nothing.
3. S5: `-W error` in `Once.agda-lib`; the ratchet is deleted. MERGE.md §4d states the rule:
   fix the cause, `CATCHALL` only for an intended fallback, per-module options need a reason.

### Consequences
- The flip's cold check found a class the replay misses: `InversionDepthReached`
  (`SlotBudget` gets `--inversion-max-depth=100`, with its reason). `make malonzo` passes
  `--no-main`. No behaviour moved: exit tests 76/0/0 ×3, cabal test 775/775.
- §6a follow-up: of 19 "small" CATCHALL sites, 13 enumerated, 6 kept with reasons. The other
  376 marked clauses stay, because enumerating one is a per-site judgement (it can break
  downstream reductions).

---

## D279 — THE MERGE GATE CHECKS REACHABILITY FROM THE APEX (MERGE.md §4b) (2026-09-10)

**Relates**: D212 (first use), D214, plan 0.64 (the content test), MERGE.md §4e (D277).
**Note**: back-filled 2026-10-09 (plan 0.113 E), from commit cb09647ca.

### Context
"A green `certified` cannot see a proof falling out of use, and nothing else in the build
performs that check." Two failures on the branch: seven `Once/Optimizer/*` modules had been
unbuildable since `fold`/`unfold`/`arr` were retired (2026-07-14, 90b430de7), yet two later
migrations edited them; and the parked `*WF` cluster accrued D159 rot because nothing builds it.

### Decision
MERGE.md gains §4b: dump the AST and trust base reachable from the apex for BOTH refs
(`run-ast-dumps.sh`) and compare, with three checks in order of severity:
- the trust base must not grow without a decision (a postulate SPLITTING, +1/−1, is fine; a
  postulate APPEARING owes a residual entry);
- a module must not LEAVE `reachable` unremarked ("removing the last consumer of a proof is a
  real event; it should be intentional");
- deletions are checked against `reachable`, never against imports, and an orphan is
  classified before cutting: superseded, unwired prize (plan 0.64's content test), or never wired.

### Consequences
- The counting trap is recorded: `counts` are DECLARATIONS. 202 `terminating-pragma` entries
  in one dump were 22 source pragmas (one pragma covers a mutual block; generated `-invert*`
  helpers inherit it). Declaration counts detect change; source counts state size.
- Placed after the extraction gate (it wants the final tree), started during step 1 because it
  runs tens of minutes per ref.

---

## D280 — THE IR LOSES `free-heap`: AN UNIMPLEMENTED STUB IS REMOVED, NOT PROVED (2026-09-18)

**Relates**: plan 0.93 S3 (its `RelIR` clause, written the same day, deleted with it), D276 (the
compiler does not free; GC-freedom "with releases at discards").
**Note**: back-filled 2026-10-09 (plan 0.113 E), from commit 692ecde1f.

### Context
The constructor was "unimplemented at BOTH ends":
- no pass constructs one: every right-hand-side occurrence rebuilds one just matched
  (`fusion-once (free-heap h) = free-heap h`, …); nothing in Surface/ or TypeCheck/ elaborates
  to it;
- its codegen freed nothing: `ir-to-trace' n l (free-heap _)` emitted `mov-to-output`;
- the escape analysis its doc comment credited does not exist (`EscapeInterface.agda` is
  imported by nothing; `CanFreeHeap` is consumed nowhere);
- the AST dump found it reachable only because the obligations must be total over the IR.

### Decision
Remove it: "an IR containing `free-heap` claimed an effect the compiler does not perform …
the constructor was misleading, not merely idle." Removed: the constructor, ~20 one-line clauses
in total functions over the IR, `Optimize`'s `h-free-heap` head with its tag and injectivity
case, and Simple.agda's postulate-free `obs-correct-free-heap`. "A postulate-free proof deleted
rather than discharged, because the thing it was about should not exist."

### Consequences
- Plan 0.93 S3's count became 5 of 13 (not 6 of 14).
- `EscapeInterface.agda` left alone: deleting the design side is a separate decision.
- Stale mentions of `free-heap` remain in comments (`IR.agda` header, `IRToTrace.agda`,
  `IRObsCorrect/Simple.agda` line ~171 "DISCHARGED", `IRObsCorrectFlat.agda`); no code.

---

## D281 — SPEC CHANGE: `in-ν` HAS ITS OWN DENOTATION; FORCING IT YIELDS THE LAYER AS GIVEN (2026-09-18)

**Relates**: D179 (`Ana` builds a suspension and emits nothing), D189 (the `in-ν` emitter),
plan 0.93 §12 ("the spec change, taken FIRST and top-down"), plan 0.98 C (dfadfb394: `evalᴰ`
enumerated, the catch-all gone).
**Note**: back-filled 2026-10-09 (plan 0.113 E), from commit faf76fd23. **This changes the
specification** (`evalᴰ`, the meaning the correctness theorem is about).

### Context
`in-ν` had no native `evalᴰ` clause and fell to the catch-all

    evalᴰ fmt ir a = λ n → (rec-trace-D fmt ir (forget a) n , inject (eval fmt ir (forget a)))

`forget` is lossy at `ν-type F`: `forgetν` reads each child at budget ZERO and drops its events.
So a ν built by `in-ν` over an EMITTING child was specified as silent. The machine leaves the
child's suspension pointer untouched, so its events would still occur at a later force. "THE
SPEC WAS WRONG, NOT THE COMPILER."

### Decision
Add the introduction form the value domain was missing (`Denotation/ValueDomain.agda`):

    in-νᵈ : ∀ {F} → ⟦ F ⟧SF (νᵈ F) → νᵈ F
    forceᵈ (in-νᵈ layer) = λ _ → ([] , layer)      -- today: `ret layer`

and give `in-ν` a native `evalᴰ` clause (`DenotTrace.agda`) returning `in-νᵈ` of the coerced
layer. `injectν` could not be reused: it maps itself over the children, whose events (from the
pure `νS`) are already gone, which is right for `inject` and wrong for `in-ν`.

### Consequences
- Change in meaning: a ν built by `in-ν` emits nothing when BUILT (unchanged), and forcing it
  yields its children AS GIVEN, so an emitting child's events now appear at that child's own
  `Out`. The old meaning had dropped them.
- Symmetric with `Ana` and simpler: no recursion, no guardedness obligation, and
  `Out ∘ in-ν ≡ id` holds definitionally.
- Why nothing caught it: the tests check the binary, this was a defect in the spec, and
  `in-ν` had no surface syntax. Plan 0.93 §12: for a spec change "a test movement here is
  EVIDENCE THE FIX IS REAL, not a regression". Root typechecked with nothing broken, "which is
  itself the finding".

---

## D282 — `obs-correct-case` TAKES ITS INDUCTION HYPOTHESES, AND EVERY JUMP HAS A STATED DESTINATION (`LabelsAt`) (2026-09-21)

**Relates**: D152 (composition), D202 (pair — this is its `case` analogue), D204 ("pair and case
are blocked on missing facts"), plan 0.88. Commits 6b351778c, 0cd7111c9, 532d3d3b8 (plan record).
**Note**: back-filled 2026-10-09 (plan 0.113 E).

### Context
Plan 0.88 had `obs-correct-case` as the last label-bearing postulate. Two of its three recorded
obstacles turned out to be defects in the STATEMENT:
- `obs-correct-case f g : IRObsCorrectF (case f g)` took no sub-witnesses — "not a weak
  statement, an unprovable one: `case f g` is correct BECAUSE `f` and `g` are".
- `c-branch-tag-zero (ℓ o l)` becomes `do-jump (find-label prog (ℓ o l))`, a scan of the WHOLE
  program, and nothing among `SpanAt`, `AllSlotStable`, `BlockRuns`, `BlocksAt` said that scan
  lands in the fragment: "an earlier `c-label (ℓ o l)` anywhere in `prog` would have taken it".

### Decision
1. As D202: `ir-obs-correct (case f g) … = obs-correct-case (ir-obs-correct f lf)
   (ir-obs-correct g lg)` — structural, both arguments subterms.
2. A new premise of `IRObsCorrectF`, `SpanAt`'s dual (`Interface.agda`):

       LabelsAt prog base t =
         ∀ m j → find-label t m ≡ just j → find-label prog m ≡ just (j + base)

   "`SpanAt` says the program FETCHES what the fragment's own text does. A branch does not
   fetch, it RESOLVES." `Comp` and `Pair` split it (`fl-go-prefix`, `fl-go-skip`, new
   `found-in-window` in `LabelResolve`); the entry instance is free (the entry trace is a
   prefix of the linked image).

### Consequences
- The third obstacle ("the branch correspondence has no model") needed none: `flat-read-tag`
  reads the cell `Input1` points at, and `valid-inl-wf`/`valid-inr-wf` already carry it.
- `obs-correct-case` was discharged 2026-09-22 (plan 0.88 17 → 7): five modules (~1500 lines,
  zero postulates), split because one module cost 4.8 GB to typecheck.

---

## D283 — THE MACHINE RELATION IS A FUNCTION ON TYPES, NOT A DATATYPE (plan 0.93) (2026-09-17)

**Relates**: D170, D213, D214, D216, D217 (the refuted designs), D218 (`BlockRuns` as hypothesis
pending this plan), `Adequacy/MeaningRelation.agda` (the template). Commits 7bc6ddf9c (plan),
a537d2b86 (S0 gate).
**Note**: back-filled 2026-10-09 (plan 0.113 E). D216/D217 only alluded to this decision.

### Context
Four replacements for the false `block-runs` were refuted (D213, D216's `CodeResolves`, `CodeWF`,
the `BlockAt` NO-GO). Plan 0.93 §2 names the common cause:

    data ValidAtWF : AllocMode → AllocState {FS} →
         {A : IRTy} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set

"A data constructor can only ASSERT facts; it cannot RECURSE ON THE INDEX", so a closure witness
cannot pin the function it denotes (D217: one cell, two denotations).

### Decision
Rebuild the machine relation in the shape of `MeaningRelation`, one layer down: `RelV`/`RelT`
mutual, by recursion on the TYPE; the arrow clause a Π over related inputs ("entering block ℓ
behaves"); the computation relation indexed by the EVENT BUDGET; recursion stopping at μ/ν (hence
no `TERMINATING`). `apply` then discharges FROM the arrow clause and `curry` ESTABLISHES it from
its IH on `body`. Labels stay labels; where a block sits is a separate, state-free layout lemma.
Rejected: an earlier draft lowering labels to addresses ("lowering belongs in the assembler").

### Consequences
- S0 stop gate PASSED (`Once/Spike/RelSpike.agda`, 857 lines, zero pragmas/postulates/holes):
  Agda accepts the type recursion, and `apply` discharges definitionally
  (`evalᴰ fmt apply p = proj₁ p (proj₂ p)` is the arrow clause's conclusion). Forced corrections:
  four types not three; the arrow clause carries `find-thunk prog lbl ≡ just j`; heap-only; `RelT`
  carries a resume pc and return stack; `RelV` takes the allocator.
- Found: `do-thunk` uses `grow-frame`, which does not reset `next-slot`, so a `next-slot ≤ n`
  premise makes `curry`'s IH unprovable.
- Status at back-fill: S1 and part of S3 landed in the spike (8 of 13 clauses, §12); `ValidAtWF`
  is still the `data` in `ClosureWellFormed.agda`; 0.91 S4/S5 were superseded by 0.93 S5/S4.

---

## D284 — `let` AND `def` ARE INTERDERIVABLE; A DEFINED NAME UNFOLDS AND FOLDS (plan 0.94) (2026-10-05)

**Relates**: plan 0.94 (closed), D131, D265 (`cata` captures), D273 (`ana` captures), plan 0.101,
plan 0.102 (`let-β`, D285). Commits 5ab0a0d33 (D1, 2026-09-26), 0c00c23ef (D2, 2026-09-26),
9c2b85f92 (converse, 2026-10-05).
**Note**: back-filled 2026-10-09 (plan 0.113 E).

### Context
Plan 0.94 §0: "`let x = e in b` and a top-level `x ≝ e` used in `b` must be interderivable … A type
system in which a definition and its definiens are not interchangeable is … stating facts about the
spelling of the program." Measured 2026-09-19: the same `u` typechecked as a top-level name and
failed as a `let`.

### Decision
Both properties are theorems, postulate-free, in all three judgments (`⊢ᵢ`, `⊢ᶜ`, `⊢ᵈ`):
- **D1, `Once.TypeCheck.LetIsDef`**: `(Γ , x ∶ A) ⊢ b ∶ B ⨾ (q ∷ Ψ) ⟺ Γ ⟨x ≝ e⟩ ⊢ b ∶ B ⨾ Ψ`
  (⟸ for some `q`). Premises are those a top-level definition needs anyway: `e` types with no
  locals, `x` is fresh, `A` is a ground signature. The let's usage slot is DROPPED. One mutual
  induction carries a relation `LD` between the two contexts.
- **def ⇒ let** was FALSE while `cata`/`ana` algebras could not capture locals; after plan 0.101
  it is `def⇒let*` (`LD` run backwards; `ld-top` deleted).
- **D2, `Once.TypeCheck.Unfold`**: `Γ⟨x ≝ e : A⟩ ⊢ b ⟺ Γ ⊢ b[(e : A)/x]` (`unfold`/`fold`). The
  name unfolds to the ANNOTATED definiens (a bare `e` such as `inl 1` need not synthesize).
  Substitution follows lexical scoping, and capture is excluded by a premise (the variable
  convention, `NC`/`Fr`), not by renaming.

### Consequences
- Moved out, not dropped: the `Void`-narrowing gate (to plan 0.102), phase E `classifyAppHead`
  (to plan 0.50). Open: α-invariance of typing, which would drop the variable-convention premise.

---

## D285 — THE TERM MODEL IS A GRADED CATEGORY; ⟦_⟧ PRESERVES COMPOSITION (2026-10-06)

**Relates**: D276 (affine grades, sub-usaging, which make substitution exact), D250 (pure is
referential transparency), plan 0.102 §4 B, §7, §8; D284. Commit 595f4680a.
**Note**: back-filled 2026-10-09 (plan 0.113 E). D276 states the reason; this records what the
apex now carries.

### Decision
A new Spec module, `Once.Spec.Core.TermModel` (a statement; proof `Once.Adequacy.TermModel`),
carried by `Once.Certified` as the new `CertifiedBuild.language` field:

> Objects are contexts, a morphism is a typed term, the identity is a variable and COMPOSITION
> IS SUBSTITUTION.

- `subst-⊢`: composition is DEFINED. Substituting a pure `u` for a variable used `q` times types
  at `Ψₜ +ᵘ q *ᵘ Ψᵤ`, "the exact QTT substitution lemma; it holds because grades are affine (D276)".
- `let-β`: ⟦_⟧ PRESERVES composition. `⟦ subst-⊢ dt du ⟧ ≡ ⟦ ⊢let (⊢sub-eff … du) dt ⟧`, which
  for a pure `u` is referential transparency.

Built from `Surface.GradeMatrix` (`_⋆ Φ` a monotone linear map, quantity laws by verified
enumeration), `Spec.Core.Subst` (simultaneous `sub-⊢`, one law of `_⋆ Φ` per rule shape;
`⊢sub-use` makes it exact), and `Adequacy.CoreSubstSem` (`sub-sem` via environment extensionality).

### Consequences
- Deliberately not stated (§8), for lack of a consumer: identity/associativity of substitution,
  the rows of the equality judgment (β/η), syntactic uniqueness for μ/ν, initiality.
- Narrowing to `Void` is now `subst-⊢`/`let-β` at `coerce`; no consumer states it yet.
- Gate: `Once.Certified` and the island backstop green; no postulates added.

---

## D286 — THE BRANCHING `cata` FOLDS IN PRODUCT ORDER: `seqF` IS SPEC, THE MACHINE WAS WRONG (plan 0.95 B) (2026-09-19)

**Relates**: D221 (the finding: the machine folded right-to-left), D211 (pair proved left-first),
D056, plan 0.95. Commits dad5830d2 (B1 verdict), c95f6a2b2 (the fix), fedf45670 (observed),
5f700172d (tests that can fail).
**Note**: back-filled 2026-10-09 (plan 0.113 E). This is the decision that answers D221.

### Context
The Tier-2 branching cata (flatten-then-rebuild over two linked stacks) emitted the exact mirror
of `seqF`'s order at every measured shape (`[1,2,3,4] → [4,3,2,1]`). `visit-walk` at `F ⊗ G`
visited G then F, `rebuild-walk` F then G, while `rebuild-walk`'s own comment said "LEFT-to-RIGHT".

### Decision
**The machine is wrong, not the spec.** "An effectful cata needs a TRAVERSAL of F over T, a
traversal of a product must choose an order, and `seqF` is that choice — so it is spec, not
derived." The spec is coherent (the same `⊗` is left-first in `seqF` and in `evalᴰ ⟨f,g⟩`, proved
to match its emitter, D211). Changing `seqF` would falsify D211 and contradict D056.

The fix swaps BOTH product clauses (`IRToTrace.agda`):

> D221: the two walks are ONE INVERSION APART, and that inversion is what makes the data pairing
> correct against a LIFO stack — it must survive. What changed is the GLOBAL order: `visit-walk`
> now pushes LEFT-to-RIGHT, so the todo LIFO pops right-first, the visit order is right-first,
> and the fold order (which is `reverse` of it …) is LEFT-FIRST — the order `seqF (G ⊗ H)`
> specifies.

### Consequences
- The rebuilt layer is unchanged; six companion proofs reordered (SlotBudget's slot witnesses changed).
- Observed after re-extraction: all four shapes now match the spec; the single-position list
  control `[5, 3]` did not move. The cata-emit tests now assert the trace against the
  byte-writing interpretation and fail on the old order on all three arches.
- `cata-correct` went from FALSE to OPEN. Nested products, `⊕` under `⊗` and three or more
  recursive positions are not yet measured.

---

## D287 — THE ARITH RECOGNISER ABSORBS, NAVIGATES AND DISTRIBUTES ONLY OVER PLUMBING (2026-10-01)

**Relates**: plan 0.20 (the recogniser), plan 0.54 (arith lowering), D163 (`terminal ∘ envʳ`
literals), D250 (pure = no event). Commit bedcfa27b.
**Note**: back-filled 2026-10-09 (plan 0.113 E).

### Context
Lifting an arithmetic subtree to one pure block drops whatever events its other parts would emit.
Three clauses of `Once.Arith.Machine.Recognise` accepted parts the block then ignored:
- a literal's right-hand side `terminal ∘ g`, for any `g`;
- reading an input path through `⟨ a , b ⟩`, for any untaken component;
- distributing `⟨ a , b ⟩ ∘ h` into `⟨ a ∘ h , b ∘ h ⟩`, which runs `h` twice.

### Decision
Each now requires ENVIRONMENT PLUMBING, `plumbing? : IR X Y → Bool` (`id`/`fst`/`snd`/`terminal`,
pairing and composition of them):

> ENVIRONMENT PLUMBING: projections, pairing, `terminal` and their composites. Its meaning is a
> value and no event, so a literal may absorb it.

> A pair is navigated only when the component NOT taken is plumbing … …and only when `h` is
> plumbing: distributing runs `h` twice, which means the same only when `h`'s meaning is a value
> and no event.

> D163: `terminal ∘ h` IS `terminal` when `h` is environment plumbing (… in the Kleisli meaning
> terminality holds only for such an `h`) … An arbitrary `h` is refused: lifting would drop its
> events.

### Consequences
- "This is the precondition under which a lifted block means the subtree it replaced."
- Nothing the elaborator produces is lost: its literal and operand shapes (QTT's environment
  restrictions) are plumbing, so its output lifts as before. The float twin gets the same rule.

## D288 — PLAN 0.101 CLOSED: BOTH RECURSION SCHEMES CAPTURE; THE LAST `let ≠ def` DIFFERENCE IS GONE (2026-10-05)

**Relates**: D265 (`cata`), D273 (`ana`), D284 (0.94: `LetIsDef`, `def⇒let*`, `Unfold`), D131,
plan 0.94 §0/§15. Commits bf9b3962b, 8de7b78db, 9b27fb4f7 (gate), 8c0eef0b1.
**Note**: closure record written 2026-10-09 (plan 0.113 E).

### Closure
- Both halves landed: `cata` (D265, 2026-10-04) and `ana` (D273, 2026-10-05). Gate at D273:
  MAlonzo re-extracted, exit tests 76/0/0 ×3 (`cata-capture` 67, `ana-capture` 41), cabal test
  775/775, apex and island backstop green.
- §3's metatheory gate is met: with no algebra position clearing the context, plan 0.94's converse
  `def⇒let*` holds (D284), `LetIsDef`'s `ld-top` is deleted, and `Unfold`'s algebra-position scope
  flag, constant `false` after D273, was dropped (8c0eef0b1).
- Risk 2 (heap `curry`'s allocation leaving the algebra path; `CurryAllocWF` losing a consumer) is
  moot: the `*WF` cluster was deleted (D176) before this plan ran.
- The core needed no change: `⊢fold`/`⊢unfold` already took the (co)algebra as an ordinary term in
  context (plan 0.102 §9). So this was a surface/IR/codegen widening only. The Spec hunks are the
  two rules plus the meaning read at `dγ` (D265/D273).

---

## D289 — PLAN 0.102 CLOSED: PHASE E RE-EVALUATED, THE OCP-0009 HAND-OFF MAPPING (2026-10-06)

**Relates**: D231 (A), D246/D256/D259/D260 (C, D via plans 0.103/0.104), D276 + D285 (B: affine
grades, the term model), D284 (0.94), OCP-0009. Commits 595f4680a (B), 87ff23d0c (close), 6cb98abb3 (gate).
**Note**: closure record written 2026-10-09 (plan 0.113 E).

### Phase E, re-evaluated (nothing retired)
- `LetIsDef`/`Unfold` STAY. They are facts about the SURFACE judgment (what the checker accepts).
  `let-β` is a meaning fact about the core. Neither implies the other, and §3 keeps the set of
  accepted programs fixed, so the surface lemmas remain the evidence for plan 0.94's property.
- The A′ ex falso rules (D229) STAY. Removing them would change which programs are accepted. Narrowing
  no longer needs them: it is `subst-⊢`/`let-β` at `coerce` (D285).
- Plan 0.101 as a core change was already true (`⊢fold`/`⊢unfold` take a term in context).

**The equality judgment waits for a consumer.** The `≈` rows (β/η per former) are unwritten. The first consumer they would have is the optimizer's
normalization postulates (`Optimizer.Normal`, 8 postulates, IR-level, a RED island off the apex,
plan 0.64 Group O). Write the rows when that chain is repaired and wired, not before.

### Phase F: the hand-off (the mapping lives only in the deleted plan §10; summarized)
OCP-0009's dependent kernel must EXTEND `Spec.Core`'s `Γ ⊢[ Ψ ] t ∷ A ! π`, never add a second
kernel. The rows: POC `RTm`/`RTy` ↔ `Tm n` + closed `Once.Type` (types become `RTy n`); Π/Σ/U/El/
Hom/Id/IMu are added as rules that carry Ψ and π. `⊢conv` is new. The deferred `≈` is the term half
of `_≅_`, and the NbE decision procedure stays outside the Spec. The graded substitution
`Ψₜ + q·Ψᵤ` (`TermModel`) is the statement subject reduction must keep. Erasure is D143's `Γ ↾ Ψ`.
`Mult` adopts D276's affine order (`NbEPLinCore`'s `drop`/`lcase` = `⊢sub-use`/one-usage `⊢case`).
`μ-type F` over `Functor` becomes a description code. Only `pure` terms may occur in types.
Open for OCP-0009: the grade of a dependent Π's domain; whether `Hom`/`Id` read terms at 𝟘.
**Action**: copy plan 0.102 §10's table into `docs/proposals/OCP-0009-…md` (it does not mention
0.102 today) before the plan file is deleted.

---

## D290 — PLAN 0.107 CLOSED: `as` IS THE ONLY TRANSLATION TRUSTED, AND `file-wf` IS A THEOREM (2026-10-06)

**Relates**: D262 (phases a–c), D272 (`as-faithful` ⊥ → true), D274 (FFI extends Σ; oracle
addendum), D275 (total symbol encoding), D009 (amended), D261, plan 0.89 D4, plans 0.110/0.111.
Commits e83f23698, 2aad95cf3, 5cd12605a, 9e1fbf6b1 (gate).
**Note**: closure record written 2026-10-09 (plan 0.113 E).

### What closed it (beyond D262/D274/D275)
- `ImageWF`'s last two postulates `prog-unique`/`lib-unique` are PROOFS, as four lemma modules:
  `CCC.Codegen.LabelDefs` (owner-free label lists, windows, disjointness), `CCC.Codegen.
  CLabelsUnique.frag` (each unit's counter labels are distinct and lie in its window, all four cata
  strategies; `fns-cl` chains windows across the table), `Adequacy.LabelSymbols.sym-key` (equal
  symbols of defined labels have equal keys), and `Adequacy.ImageUnique` (D249's name guard read back,
  `dedup-blocks`, an entry is never a block, `heap≢osp`). `lib-resolved` is proved
  (`ImageResolved.Lib`/`.Fns`). `Adequacy.EntriesValid` (the pre-D274 detour) is deleted.
- §8 step 3 (re-keying imported definitions) DISSOLVED. After D274, `resolveImports` brings only
  signatures, so the table holds only own definitions, each already `own x`.
- Regression probe: re-introducing D261's entry-style riscv64 prologue is a TYPE ERROR
  (`RiscV64/FlatComposition.agda:181`, the `c-entry` step lemma).

### What stays trusted (plan §2), and where its leftovers went
`as-faithful-<arch>` (the assembler + `print`), the ISA model, and the loader's `initialState`.
The start state's over-assumption (every register except `sp` starts at 0, so `_start`'s heap `lea`
is decorative) → plan 0.110. The CLI's `objcopy --redefine-sym` rename of interpretation symbols
is trusted Haskell on the D061 boundary → plan 0.111 (interpretation ABI).
Gate: apex + backstop green, cabal 776/776, exit tests 76/0/0 ×3.

---

## D291 — PLAN 0.108 CLOSED: COMPARISONS; ONE RESIDENCE AMBIGUITY LEFT IN `arith-sigop-contract` (2026-10-04)

**Relates**: D263 (meaning: Bool = 1 + 1, true = inr), D264 (lowering, proof, link; bare-primitive
addendum), D262. Commits ec76b1ec8, c9c84f0f6, 282935276, 6c0f24a00.
**Note**: closure record written 2026-10-09 (plan 0.113 E).

### Closure
All of phases A–E landed (D263/D264). Comparisons no longer reach `obs-correct-sigop-rest`, and
`FileWF.file-wf` is true for them (it is now a theorem, plan 0.107).

### The finding not yet logged
D264 records why `bool-of` is not an IR morphism: an `Int` input may be LOCATION-resident
(`in-loc`), and no machine step can tell a pointer from a word. Plan 0.108 §6 noted that
**arith blocks have the same ambiguity**, hidden in the postulated per-arch `arith-sigop-contract`
(e.g. `X86-64/ConcFlatSim.agda` ~669–700, still a postulate). It claims a block's dispatch
on whatever `Input1` holds. Discharging that contract must therefore pin the input's residence (a
register-resident word) or the contract is false at a boxed `Int`. Comparisons avoid it only
because `out-nz` reads `Output`, which the block itself just wrote.

---

## D292 — PLAN 0.109 CLOSED: WHAT THE `-W error` FLIP LEFT BEHIND (2026-10-05)

**Relates**: D278 (the decision and census), MERGE.md §4d, plan 0.92 §7. Commits 3843d1d09,
1382f5e38, d33ae8044, 8cc88893b, da7c868dc, b7fd7996d.
**Note**: closure record written 2026-10-09 (plan 0.113 E). The decision itself is D278.

### Closure facts
- Closed 2026-10-05. The whole non-island tree checks COLD with zero warnings, and nothing behaved
  differently: extraction OK, exit tests 76/0/0 ×3, cabal 775/775.
- One `ModuleDoesntExport` cause is a pattern to watch: three imports had a one-line import WEDGED
  before their continuation `using`. The `using` then attached to the wrong module, while the
  intended one was opened wholesale. Only the warning showed it.
- `{-# CATCHALL #-}` is accepted under `--safe`, so the ≈395 marked clauses are not a safety hole.
  They are a known hazard: a NEW constructor silently falls into the fallback (memory
  `feedback_retired_ctor_catchall_trap`). Census of the marked clauses: small 19, large 71,
  multi 86, with 72, shape 92, otherpos 14, type 41. 13 small ones were enumerated. 6 were kept with
  reasons (the `DecEq` catch-all-first helpers, `ShapeTable.load-snd` whose fallback is the weakest
  claim `e-any`, and `LabelScope.go`'s index-dependent diagonal). 376 remain, each a per-site judgement.
- Islands are outside the cold check; `-W error` bites them only when they are next built.

---

## D293 — PLAN 0.94 CLOSED: WHAT DID NOT TRANSFER, AND WHERE IT WENT (2026-10-05)

**Relates**: D284 (`LetIsDef` incl. `def⇒let*`, `Unfold`), D228–D230 (C′, B, C), D229 + amendments
(A′), D276 (affine grades), plan 0.102, plan 0.50, plan 0.80. Commit 9c2b85f92 (close).
**Note**: closure record written 2026-10-09 (plan 0.113 E).

### Two negative results worth keeping
- **The general substitution lemma is FALSE on the algorithmic judgment** (§4b). `t-case` concludes
  `Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)`, and with the definiens' usage `[One]` the two sides compute `[One]` vs `[Many]`
  (counterexample in §4b). Repairing it needs usage weakening, which the surface judgment lacks. Hence
  §4c's context-transfer statement (D284), and later D276's sub-usaging in the core, where the exact
  QTT lemma holds (D285).
- **The A′ `Void`-narrowing gate is FALSE as stated under (a)**: `t-app` CHECKS its argument against
  the head's domain, so a head narrowed to `Void` leaves a checked-only argument (a lambda) nothing to
  check against. It also collides with `t-app-void` through the spine. The A′ rules stay (D229).

### Where the moved-out items went
- The narrowing gate → plan 0.102 phase B. Closed there as `subst-⊢`/`let-β` at `coerce`, with no
  consumer stating it yet (D285).
- Phase E, removing `classifyAppHead` (still a premise, `TypeCheck/Judgment.agda` ~496) → plan 0.50.
  **Gap**: `plans/0.50-named-defs-are-morphisms.md` does not mention it. Add the row there.
- §7's structural guard (the Spec judgment must not import a computation on `RawExpr` from
  `Classify`) was not built. `Judgment.agda` still imports `Once.TypeCheck.Classify`. It goes with
  `classifyAppHead`.
- Open, not needed by anything: α-invariance of typing (would drop `Unfold`'s variable-convention premise).

---

## D294 — PLAN 0.95 CLOSED: `apply` AT AN EFFECTFUL CLOSURE IS A NEW RULE; THE EFFECT TESTS CAN FAIL (2026-09-21)

**Relates**: D219, D220, D221, D222 (phase A), D286 (phase B: the fold fix). The plan was deleted
in b486a4750. Commits 99ac70ef6 (A), c0b4ea864 (A′), 5f700172d (C-P0/1/3), c9f8cb225 (C-P4), b486a4750.
**Note**: closure record written 2026-10-09 (plan 0.113 E). Its commit message named D219–D222 as
the plan's home. A′ and phase C were in none of them.

### A′ — `t-apply-eff-app-infer` (c0b4ea864)
Phase A made a curried effectful closure buildable but not eliminable (`t-apply-*` fixed to `pure`).
A free `π` cannot state the fix. Effects live on arrows, so at an eff closure `apply` concludes
the SUSPENSION `Unit ⇒[eff] B`, not `B`. That is a different conclusion shape, so it needs a new
constructor, mirroring `t-effApp`. No new `Expr` former: `IR.curry (apply ∘ fst)` over the ungraded
`_⇛_` is what `morph-app` already wants.
- The meaning bridge caught a trace-order error: suspending the pair's evaluation with the
  application typechecks but disagrees with `morph-app`, which builds the pair eagerly. Only
  REQUIRING the two sides to agree exposes when the pair's events appear.
- **A green module can be falsified by editing another**: `RealizeAgrees` carried an absurd row
  sound only while the elaborator rejected eff closures. Absurd rows encode what the elaborator
  currently rejects, so only a whole-cone check finds this.
- Gate: `apply-eff-closure{,-snd}.once` (`fst` emits the captured value, `snd` the applied one; swapping
  the expectations fails both, on three arches).

### Phase C — the tests can fail
`buildAndRunTraceFile` + `traceCases` build a `.once` FILE against the byte-writing interpretation
(before, no harness did). The cata-emit tests now assert the ORDERED trace and fail on the pre-fix
order on all three arches. C-P2: the four `float-emit-*` tests emitted nothing (an unforced `let`);
moved onto `main`'s chain, they now reach x86-32's `emitF`, the case the D109 `ud2` regression needed.
C-P6: 16 of 17 orphan fixtures did not build (`main : Int -> Int`), and the nine `depth-*` tests
asserted a depth limit that exists nowhere in the compiler. Deleted. One (`layer4-id-inline`) was wired.
Exit tests 71/0/0 ×3, cabal 755/755.

## D295 — AN ELIMINATOR'S METHODS ARE ω-USED: `cata`/`ana` SCALE THEIR ALGEBRA'S USAGE BY `Many` (2026-10-09)

**Relates**: D232 (standard QTT for `compose`/`effApp`), D265/D273 (algebras capture), D276 (affine grades), plan 0.113 B1 (43d189085)

### Context
The 2026-10-09 merge analysis found `t-cata-check`, `t-ana-check`, `d-cata` and the core's `⊢fold`/`⊢unfold` concluding with the algebra's usage `Ψ` unscaled. Since D265/D273 an algebra may capture locals, and the fold applies it once per node (the unfold once per forced layer). An affine (`^1`) capture inside an algebra was therefore duplicated by any structure with two nodes — D232's own argument for `compose`, applied to the recursors.

### Decision
QTT's eliminator rule: the methods of a recursor sit under ω. The conclusion's usage is `Many *ᵘ Ψ` (core: `(Many *ᵘ Ψa) +ᵘ Ψt`). QTT counts uses of a closure, not evaluations: D131's "the algebra is evaluated once, applied per layer" is about effects, and each application reuses what the closure captured.

### Consequences
- Only AFFINE captures inside algebras become errors; `Many *q Many = Many`, so unrestricted captures are unaffected.
- Everywhere else the pattern is D232's: the algebra reads its environment through the `⊑ᵘ-*Many` restriction (`restrictEnv`, `restrictᴰ`/`restrictᵛ`, `rel-restrict`); usage transports via `thin-usage-*ᵘ`, `⋆-*`, `drop-*`, `up-*`. `⊢cataᶜ`/`⊢anaᶜ` conclude at `Many *ᵘ Ψ` — the `let` inside `cataᶜ` already charged ω once its variable is used per node.
- Tests: QttSpec (a linear capture in a cata algebra rejected; an unrestricted one accepted).

## D296 — QUANTITY AND PURITY ARE INDEPENDENT: AN EFFECTFUL OPERATION WITH AN ERASED ARGUMENT IS A CALL (2026-10-09)

**Relates**: D143 (erased arrows), D250 (pure = referentially transparent), D257 (contracts), plan 0.113 A3 (50e6d19bb), plan 0.114 (self-validating definitions)

### Context
Every layer treated `A ⇒[0, π] B` as a VALUE whatever `π`: `Spec.Contract.contractOf`, the elaborator (`value-info` at every erased arrow), `SourceDenote.⟦ sigOp ⟧ˢ`, and the meanings (`sigOpRefᵛ`, `sigOpRefᴰ`). `now : 0 Unit ⇒[eff] Int` would have been a constant — no event, no history — contradicting D250. No proof caught it because all four sides made the same choice (both categorical reviews of the merge analysis found it independently).

### Decision
The QUANTITY decides the key's domain (`Zero` erases the argument: `Unit`, D143); the PURITY decides value versus effect. `Zero, pure` stays a value contract / `value-info`; `Zero, eff` is `contract-eff c Unit B` and elaborates to `arrow-info (mk-kind Zero eff) name base-Unit` — a call with the erased slot `tt`, whose codomain then decides call / emit / halt like every effectful SigOp.

### Consequences
- Codegen change (extracted): an effectful FFI symbol at an erased arrow now emits a call.
- A runtime test needs an interpretation declaring such an operation (plan 0.113 D, open).

## D297 — HALTING AND EMITTING ARE INITIAL/TERMINAL UP TO ISOMORPHISM: AN HONEST FFI CODOMAIN IS SKELETAL (2026-10-09)

**Relates**: D225/D227 (the codomain decides), D231 (honest FFI), plan 0.113 B2 (b619751d5), plan 0.112 G1 (the general form)

### Context
Emit/halt is decided everywhere by syntactic `B ≡ Unit` / `B ≡ Void` (`contract-eff`, `arrow-sem-eff`, `ext-resolved-sem`). "Halts" means the codomain is empty (initial), "emits" that it is a singleton (terminal) — properties up to isomorphism. `Eff Int (Void * Int)` was an ANSWERING contract with an empty answer type: no implementation of the signature exists (`Impl Σ` empty), so the correctness theorem was vacuous for such a program.

### Decision
A skeleton: an honest FFI declaration writes an empty codomain as `Void` and a singleton one as `Unit`. `Type.Honest` gains `NotEmpty` / `NotSingleton`, structural on the first-order codomains an FFI signature can have (IsConcrete: the ABI). A data codomain must be inhabited (pure); an effectful one must also not be a singleton. Non-first-order codomains (μ, ν, rigid) are not honest. With the skeleton the syntactic dispatch is correct, not accidentally so.

### Consequences
- `Type.HonestSound.inhabited`: a `NotEmpty` type is inhabited (outside the Spec closure); the theorem it feeds — an honest signature admits an implementation — is open (plan 0.112 G1).
- Every declaration in use is unaffected. Tests: PuritySpec (four cases).

## D298 — THE SPEC'S MEANING IS THE GRADED ONE, AND THE SPEC CLOSURE IS PROOF-FREE (2026-10-09)

**Relates**: D140 (proof-free closure), D250 (graded meaning), D257 (interaction trees), D277 (the Spec door), plan 0.113 B4 (491e3eee3) and A1 (4c1f3c079)

### Context
`Once.Spec.Meaning` re-exported the purity-blind Kleisli domain `⟦_⟧ᴰ` (every arrow `A → T B`) and the surface derivation meaning over it; the meaning the apex uses — `M π` / `⟦_⟧ᵛ`, the schemes, `T` with `Interp`/`run`, the core derivation meaning `⟦_⟧` — was not exported. Separately the branch had put proofs into closure modules (`Type.Sub`, `Denotation.Behavior`, `Spec.Module`, `Spec.Contract`).

### Decision
The Spec exports the graded meaning (`TraceMonad`, `GradedDomain`, `GradedOps`, `Spec.Core.Meaning.⟦_⟧`); `ValueDomain` and `Denotation.Meaning` leave the closure (now 32 modules). Every proof moves to a `…Laws` companion outside it (`TraceMonadLaws`, `GradedDomainLaws`, `SubLaws`, `BehaviorLaws`, `ContractLaws`, `ModuleLaws`). What stays in the closure is definitions and decision procedures (`_≟q_`, `isVoid?`, `_<:?_`, …), `pure⊑` (a total function to a derivation, used computationally), and `Raw.closedLiftShape?-just` (predates the branch).

### Consequences
- The Spec door's `public` baseline rose by 2 (D277).
- A closure module may import a `…Laws` module non-publicly when a lemma is used computationally (`GradedOps` uses `value-∈` for a membership witness).

## D299 — `layer-rel` IS A THEOREM AGAIN (2026-10-09)

**Relates**: D179 (computation carrier), plan 0.113 A2 (60d045698), the residual ledger

### Context
Master PROVED the fold's layer lemma in two halves (`layer-events`, `layer-z`). D179 merged them into `layer-rel` over `RelT′` and left it a POSTULATE ("discharged below" — it was not), undocumented, on the `Once.Certified` path: a proved theorem downgraded silently.

### Decision
Prove it. `seqF` is a traversal, so the relation reduces per functor case to a VALUE step over arbitrary related values (master's `layer-z` cases restated): `K` via `base-z` (ported to `injectᵇ`), `Id` by mapping the relation (`RelT′-mono`), sums by `RelT′-fmap`, products by `RelT′-bind` twice.

### Consequences
- One fewer postulate on the certified path; no assumption replaces it.
- Rule (for MERGE.md §1's postulate delta): replacing a proof by a postulate needs a decision entry naming why; "discharged below" must be true.

## D300 — THE SPEC BORROWS COMPILER FUNCTIONS IN FOUR PLACES: RECORDED, FIXED BY PLAN 0.114 (2026-10-09)

**Relates**: D137, D140, D249, D274, plan 0.59, plan 0.114, memory "pin self-validating definitions"

### Context
The merge analysis found the Spec calling compiler functions: `Spec.Module`'s `mono` takes a definition's type from `C.resolveFunType`; `Spec.Core.Translate` builds on `Compile.FunCtx`, `Parser.FunInfo`, `Classify.lookupImport` and picks "the first `main`, exactly as `findMain`"; `⟦_⟧ˢ` becomes a `Behavior` through the compiler IR and `moduleToIR-complete`; `t-var-own` carries a negative premise only to stay disjoint from `t-var-resolved`.

### Decision
Not a vacuity (accepted programs exist; soundness ties them to the Spec) but a SELF-VALIDATION hole: a bug in a shared function moves both sides together, invisible to every proof, and completeness becomes partly tautological there. Recorded here; removed by plan 0.114 (one borrowing at a time, after this branch merges).

### Consequences
- Until 0.114 lands, MERGE.md's Spec review reads `Classify`, `Compile`'s `resolveFunType`/`findMain` and `Parser.extractFunctions` as part of the Spec.

## D301 — THE SPEC'S MEANING IS PARAMETRIC IN THE TARGET'S NUMBERS (2026-10-10)

**Relates**: D250 (graded meaning), D124 (floats), "arith needs no value spec", plan 0.113 (merge walk-through)

### Context
The per-edit walk-through of the merge found `Spec.Core.Meaning.⟦_⟧` (and `primSem`) taking a `TargetNum`: integer literals and primitives are fixed-width, at the target's `int-bits`, and floats at its `float-format`. Nowhere did the Spec say so.

### Decision
This is intended: the Spec does not pretend to unbounded integers, so overflow is part of the meaning, not undefined behaviour. "The meaning of a program" is therefore the meaning AT a target: one program may behave differently on targets of different word widths, and the correctness theorem is per target (`exec arch … ≈ ⟦ arch ⟧ˢ …`).

### Consequences
- A portable program is one whose meaning agrees at every `TargetNum` it is compiled for; nothing checks that today.
