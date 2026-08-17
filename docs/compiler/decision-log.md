# Decision Log

Design decisions made during the implementation of the Once compiler.

---

## D001: Generators as Reserved Words

**Date**: 2025-12-08
**Status**: Accepted

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
**Status**: Accepted

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
**Status**: Accepted

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
**Status**: Accepted

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
**Status**: Accepted

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
**Status**: Accepted

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

## D071: SigOp Is FFI-Only; Internal Definition References Are Context Projections (DTT-Aligned)

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
