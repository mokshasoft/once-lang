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
interpretations/
  linux/
    syscalls.once     -- type declarations
    syscalls.c        -- C implementation
  browser/
    syscalls.once
    syscalls.js       -- JS implementation
  bare-metal/
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
- `interpretations/` directory at repo root, not in `compiler/`
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
