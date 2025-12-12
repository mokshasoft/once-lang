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
