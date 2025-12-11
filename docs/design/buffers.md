# Buffers in Once

## Executive Summary

Once provides a single primitive type `Buffer` for contiguous byte storage. `String` is a type-parameterized wrapper with encoding information. Allocation strategy is orthogonal to the type system and specified via annotations in the implementation, not the type signature.

| Aspect | Design |
|--------|--------|
| **Primitive type** | `Buffer` - contiguous bytes with length |
| **String type** | `String : Encoding -> Type` - Buffer with encoding |
| **Allocation strategy** | Annotation in implementation (`@stack`, `@heap`, etc.) |
| **Default allocation** | Inferred; can be overridden via compiler flag |
| **Semantics** | Allocation doesn't change meaning, only implementation |

## The Problem: Haskell's Fragmentation

Haskell's string situation is a cautionary tale:

```haskell
String       -- [Char], linked list, slow
Text         -- packed UTF-16, fast
ByteString   -- packed bytes, fast
LazyText     -- chunked Text
LazyByteString -- chunked ByteString
-- Plus conversions: pack, unpack, encodeUtf8, decodeUtf8...
```

This happened because `String = [Char]` was baked in early, then performance reality hit. Once must avoid this.

### Root Cause Analysis

Haskell conflated two orthogonal concerns:

1. **Memory layout** - How bytes are stored (linked list vs contiguous)
2. **Interpretation** - What bytes mean (characters vs raw data)

`String` implies both "linked list" AND "characters". `ByteString` implies "packed" AND "raw bytes".

## Once's Solution: Separation of Concerns

Once separates three orthogonal concerns:

1. **Memory layout** - `Buffer` is always contiguous (primitive)
2. **Interpretation** - `String Encoding` tracks what bytes mean (type parameter)
3. **Allocation** - Where memory lives (implementation annotation)

### Buffer: The Primitive

```
Buffer : Type              -- contiguous bytes with length
```

Buffer is the single primitive for byte storage. It maps to:
- C: `struct { uint8_t* data; size_t len; }`
- JavaScript: `Uint8Array`
- Bare metal: pointer + length

### String: Encoding as Type Parameter

```
String : Encoding -> Type

String Utf8   : Type       -- UTF-8 encoded text
String Utf16  : Type       -- UTF-16 encoded text
String Ascii  : Type       -- ASCII text
```

Under the hood, `String e` wraps a `Buffer`:

```
String e = Buffer + encoding tag (erased at runtime)
```

Encoding is semantic (affects how operations work) so it belongs in the type. The type parameter is:
- Checked at compile time
- Erased at runtime (zero cost)
- Extensible (users can add encodings)

#### Built-in Encodings

```
Utf8 : Encoding      -- variable width, 1-4 bytes per character
Utf16 : Encoding     -- variable width, 2 or 4 bytes per character
Ascii : Encoding     -- fixed width, 1 byte per character (0-127)
```

#### User-Defined Encodings

Libraries can add more:

```
Latin1 : Encoding
ShiftJIS : Encoding
Windows1252 : Encoding
```

#### Operations

```
-- Encoding-agnostic (work on Buffer level)
byteLength : String e -> Int
concat : String e * String e -> String e

-- Encoding-specific
charAt : String Utf8 -> Int -> Char + IndexError
charLength : String Utf8 -> Int      -- character count, not byte count

-- Conversions
toUtf8 : String Ascii -> String Utf8     -- safe (ASCII is subset)
toBuffer : String e -> Buffer            -- drop encoding info
fromBuffer : Buffer -> String Utf8 + EncodingError   -- may fail
```

### Allocation: Implementation Detail

Allocation is orthogonal to types. The annotation goes in the **implementation**, not the type signature:

```
-- Type signature (pure, categorical meaning)
concat : Buffer * Buffer -> Buffer

-- Implementation with allocation annotation
concat @heap a b = ...

-- Or without annotation (inferred)
concat a b = ...
```

For lambdas:

```
map (@stack \x -> concat x x) myList
```

#### Why Not in Type Signature?

Type signatures should be purely semantic. Allocation:
- Doesn't change what the function computes
- Only affects where results are stored
- Is an implementation detail

Putting allocation in implementations keeps type signatures clean and categorical.

## Allocation Annotation Syntax

### Design Options Considered

**Option A: Inline type parameter style** (rejected)
```
concat : Buffer @heap * Buffer @heap -> Buffer @heap
```
Rejected: Looks like `@heap` is part of the type, suggesting it could be used on inputs. Mixes implementation into type signature.

**Option B: Separate line with `@alloc`** (rejected)
```
@alloc heap
concat : Buffer * Buffer -> Buffer
```
Rejected: Ambiguous - doesn't make clear it's about output allocation.

**Option C: Separate line with `@returns`** (considered)
```
@returns heap
concat : Buffer * Buffer -> Buffer
```
Clear about output, but adds extra line.

**Option D: In implementation with `@`** (chosen)
```
concat : Buffer * Buffer -> Buffer
concat @heap a b = ...
```
Chosen: Keeps type signature clean. Allocation is visibly an implementation choice.

### Chosen Design

```
-- Type signature (no allocation)
concat : Buffer * Buffer -> Buffer

-- Implementation (allocation specified)
concat @stack a b = ...

-- Lambda
(@heap \x -> process x)

-- No annotation (inferred from context or compiler flag)
concat a b = ...
```

### Allocation Only Applies to Outputs

Key insight: allocation annotation only makes sense for outputs.

- **Inputs**: Function accepts buffer from wherever caller provides it
- **Outputs**: Function must decide where to put the result

For linear in-place operations (`^1 -> ^1`), the output uses the same memory as input - allocation is inherited.

## Available Allocation Strategies

| Strategy | Description | Use Case |
|----------|-------------|----------|
| `stack` | Stack-allocated, automatic lifetime | Local temporaries, small buffers |
| `heap` | Heap-allocated via malloc/free | General purpose, variable lifetime |
| `pool` | Fixed-size block pool | Many small allocations of same size |
| `arena` | Bump allocation, bulk free | Request handling, compilation phases |
| `const` | Read-only constant section | String literals, static data |

### Allocator Interface Classes

Different strategies have different interfaces. Users can implement custom allocators by conforming to one of these:

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

**Built-in (no user extension):**
- `stack` - compiler manages via stack frames
- `const` - compiler places in read-only section

Users can add custom allocators without modifying the compiler by implementing one of these interface classes.

## Default Strategy and Compiler Flags

When no annotation is provided:

1. **Context** - Output inherits input's strategy (for transformations)
2. **Compiler flag** - Override the default:
   ```bash
   once build myfile.once                  # platform default
   once build --alloc=stack myfile.once    # default to stack
   once build --alloc=arena myfile.once    # default to arena
   ```
3. **Platform default** - Typically `heap` for Linux, may differ for bare metal

**Precedence:**
1. Explicit `@stack` in implementation - always wins
2. Compiler flag `--alloc=X` - default for unannotated
3. Platform default - fallback

## Semantics: Allocation Doesn't Change Meaning

For any function `f`:
- `f @heap` and `f @stack` compute the same function
- Given the same logical input, they produce the same logical output
- They differ only in where results are stored

This is testable:

```haskell
prop_allocation_independent :: Program -> Input -> Property
prop_allocation_independent program input =
  runWith Stack program input === runWith Heap program input
```

## Interaction with Quantities (QTT)

Buffer has both allocation strategy and quantity:

```
-- Type signature (no allocation)
f : Buffer ^1 -> Result

-- Implementation specifies allocation
f @heap buf = ...        -- linear heap buffer
g @stack buf = ...       -- linear stack buffer
```

### Compatibility Constraints

| Strategy | ^1 (linear) | ^w (unrestricted) |
|----------|-------------|-------------------|
| `stack` | Valid | Invalid - can't outlive frame |
| `heap` | Valid | Valid (refcount/GC) |
| `pool` | Valid | Depends on pool design |
| `arena` | Valid | Valid within arena lifetime |
| `const` | Valid | Valid (never freed) |

The compiler rejects invalid combinations.

## The Three Strata

```
+------------------------------------------------------------------+
|   Interpretations Stratum                                        |
|   - Concrete allocation implementations                          |
|   - Platform-specific code                                       |
+------------------------------------------------------------------+
|   Derived Stratum                                                |
|   - Pure code, polymorphic over allocation                       |
|   - JSON parsers, compression, algorithms                        |
+------------------------------------------------------------------+
|   Generators Stratum                                             |
|   - The 12 categorical primitives                                |
|   - No allocation concept                                        |
+------------------------------------------------------------------+
```

### Derived Stratum: Pure and Polymorphic

Code in Derived doesn't specify allocation:

```
-- Polymorphic over any strategy (no annotation)
tokenize : String Utf8 ^1 -> List Token ^1

parseJson : String Utf8 ^1 -> (Json + ParseError) ^1
```

### Interpretations Stratum: Concrete Strategies

Interpretations provide concrete allocators and can specify allocation:

```
readFile @heap : Path -> IO (Buffer + Error)

processRequest @arena : Request -> Response
```

## Buffer vs Int: Same Treatment

From the Derived stratum's perspective, `Buffer` and `Int` are treated identically:

```
add : Int * Int -> Int               -- pure, allocation invisible
concat : Buffer * Buffer -> Buffer   -- pure, allocation invisible
```

Both are primitive types with operations. The Derived stratum doesn't see where results are stored. The Interpretations stratum handles these details.

### Allocation Failure

Once's approach: **allocation failure is catastrophic**. The program terminates (like most languages handle OOM).

For bare metal with strict requirements:
- Use `arena` with pre-allocated memory
- Use `pool` with fixed-size blocks
- Static analysis can verify no dynamic allocation occurs

## Variable-Size Data

For data whose size is unknown at compile time:

- **Heap**: Growable buffer (realloc as needed)
- **Stack/Pool**: Chunked approach (list of fixed-size buffers)
- **Streaming**: Process without holding entire content

The choice is made in Interpretations based on use case.

## String Literals

String literals go into read-only constant section:

```
let greeting = "Hello, World" in ...
```

- Compiled into `.rodata` section (ELF) or equivalent
- Never freed (lifetime = program lifetime)
- Type: `String Utf8` with `@const` allocation

If you need a heap-allocated copy (e.g., to outlive the current scope):

```
let copy @heap = "Hello, World" in ...
```

## Open Questions

### 1. Arena Lifetime Tracking

How to ensure arena-allocated buffers don't escape their arena? May require rank-2 types or linear arena handles.

### 2. Slices

Should there be a `Slice` type for views into buffers? How to track that the original buffer must outlive the slice?

### 3. Sized Buffers

Should `Buffer` have an optional size parameter for compile-time size checking?

```
Buffer : Type                    -- dynamic size
Buffer { size <= 1024 } : Type   -- bounded size (refinement type)
```

This relates to the broader question of refinement types in Once. See type-system.md for discussion.

### 4. Pool Configuration

Deferred. Possible future approach: a `setup` section for library initialization.

## Summary

1. **Buffer is the single primitive** for contiguous bytes
2. **String has encoding as type parameter** - `String Utf8`, `String Ascii`, etc.
3. **Allocation is in implementation** - `concat @heap a b = ...`
4. **Type signatures are pure** - no allocation mentioned
5. **Annotations are optional** - inferred by default, compiler flag for override
6. **Three allocator interface classes** - MallocLike, PoolLike, ArenaLike
7. **User-extensible** - custom allocators implement an interface class
8. **QTT integrates** - quantity and strategy are both checked
9. **Property test** - same program, different strategies, same result

This design:
- Avoids Haskell's fragmentation
- Separates semantic concerns (encoding) from implementation (allocation)
- Enables efficient bare-metal code
- Preserves substrate independence
- Maintains categorical purity in type signatures
