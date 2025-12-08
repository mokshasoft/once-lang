# Once Compiler Architecture

## Overview

An Once compiler translates programs written in natural transformations to executable code for any target platform. The compilation is straightforward because the source language has precise mathematical semantics.

## Compiler Pipeline

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   Source    │ -> │  Categorical│ -> │  Optimized  │ -> │   Target    │
│   Once      │    │     IR      │    │     IR      │    │   Code      │
└─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘
     Parse           Type Check          Rewrite           Generate
```

## Frontend

### Parsing

Once syntax is designed for clarity and ASCII-friendliness:

```
-- Function definition
parseJson : String -> Json + ParseError
parseJson = compose validate (compose structure tokenize)

-- Data types
data Json
  = JsonNull
  | JsonBool Bool
  | JsonNumber Number
  | JsonString String
  | JsonArray (List Json)
  | JsonObject (List (String * Json))
```

The parser produces an AST of categorical terms.

### Type Checking

The type checker verifies:
- Morphisms have correct source and target types
- Composition types match: `(A -> B)` composes with `(B -> C)`
- Functor laws are respected
- Natural transformation components have correct types

Type checking is standard bidirectional type checking with inference.

## Intermediate Representation

The core IR is just the Generators:

```
data IR
  = Id Type                          -- identity
  | Compose IR IR                    -- composition
  | Fst Type Type                    -- first projection
  | Snd Type Type                    -- second projection
  | Pair IR IR                       -- pairing
  | Inl Type Type                    -- left injection
  | Inr Type Type                    -- right injection
  | Case IR IR                       -- case analysis
  | Terminal Type                    -- discard
  | Initial Type                     -- absurd
  | Curry IR                         -- currying
  | Apply Type Type                  -- application
  | Fmap Functor IR                  -- functor mapping
  | Primitive String Type Type       -- external primitives
```

This is essentially a **Categorical Abstract Machine (CAM)** - a well-studied compilation target for functional languages.

## Optimization

Because semantics are categorical, every optimization is a **law application**:

### Category Laws

```
compose f id = f                      -- right identity
compose id f = f                      -- left identity
compose f (compose g h) =             -- associativity
  compose (compose f g) h
```

### Functor Laws

```
fmap id = id                          -- identity
fmap (compose f g) =                  -- composition
  compose (fmap f) (fmap g)
```

### Product Laws

```
fst (pair f g) = f                    -- beta for products
snd (pair f g) = g
pair (compose fst h) (compose snd h) = h  -- eta for products
```

### Coproduct Laws

```
case f g (inl x) = f x                -- beta for coproducts
case f g (inr y) = g y
case (compose h inl) (compose h inr) = h  -- eta for coproducts
```

### Derived Optimizations

From these laws:

| Optimization | Law |
|--------------|-----|
| **Fusion** | `fmap f . fmap g = fmap (f . g)` |
| **Identity elimination** | `f . id = f` |
| **Dead code removal** | `terminal . f = terminal` |
| **Case simplification** | `case inl inr = id` |

The optimizer applies these rewrites until fixed point.

## Code Generation

### Generator Implementations

Each target provides implementations for the generators:

**C Target**

| Generator | C Implementation |
|-----------|------------------|
| `id` | `return x` |
| `compose f g` | `return f(g(x))` |
| `fst` | `return x.fst` |
| `snd` | `return x.snd` |
| `pair f g` | `return (struct){f(x), g(x)}` |
| `inl` | `return (union){.tag=0, .left=x}` |
| `inr` | `return (union){.tag=1, .right=x}` |
| `case f g` | `return x.tag ? g(x.right) : f(x.left)` |
| `terminal` | `return (void)0` |
| `initial` | `unreachable()` |
| `curry f` | closure or code transformation |
| `apply` | `return x.fn(x.arg)` |

**Rust Target**

| Generator | Rust Implementation |
|-----------|---------------------|
| `id` | `x` |
| `compose f g` | `f(g(x))` |
| `fst` | `x.0` |
| `snd` | `x.1` |
| `pair f g` | `(f(x), g(x))` |
| `inl` | `Left(x)` |
| `inr` | `Right(x)` |
| `case f g` | `match x { Left(l) => f(l), Right(r) => g(r) }` |
| `terminal` | `()` |
| `initial` | `match x {}` |
| `curry f` | `move \|y\| f((x, y))` |
| `apply` | `(x.0)(x.1)` |

**JavaScript Target**

| Generator | JavaScript Implementation |
|-----------|---------------------------|
| `id` | `x` |
| `compose f g` | `f(g(x))` |
| `fst` | `x[0]` |
| `snd` | `x[1]` |
| `pair f g` | `[f(x), g(x)]` |
| `inl` | `{tag: 'left', value: x}` |
| `inr` | `{tag: 'right', value: x}` |
| `case f g` | `x.tag === 'left' ? f(x.value) : g(x.value)` |
| `terminal` | `undefined` |
| `initial` | `throw 'unreachable'` |
| `curry f` | `y => f([x, y])` |
| `apply` | `x[0](x[1])` |

### Example Compilation

**Once Source**

```
double : Int -> Int
double = compose add (pair id id)

add : Int * Int -> Int
add = primitive "add"
```

**Generated C**

```c
int64_t once_double(int64_t x) {
    return add(x, x);
}

// After inlining pair id id -> diagonal
// And simplifying
```

**Generated Rust**

```rust
fn double(x: i64) -> i64 {
    add((x, x))
}
```

**Generated JavaScript**

```javascript
function double(x) {
    return add([x, x]);
}
```

## Compilation Targets

| Target | Output | Use Case |
|--------|--------|----------|
| C | `.c` + `.h` | Maximum portability |
| Rust | `.rs` | Memory safety |
| JavaScript | `.js` | Browser, Node.js |
| WebAssembly | `.wasm` | Portable binary |
| LLVM IR | `.ll` | Native optimization |
| x86_64 | `.o` | Direct native |
| ARM | `.o` | Embedded, mobile |

## Primitives and Interpretations

The compiler links primitives from the Interpretations layer:

```
-- Declared in source
primitive read : FileHandle -> External Byte

-- Compiler looks up implementation for target:
-- C: int8_t once_read(FILE* handle) { return fgetc(handle); }
-- Rust: fn read(handle: &mut File) -> io::Result<u8> { ... }
```

Different Interpretation modules provide different primitives:

```
Interpretation.POSIX    -- Unix system calls
Interpretation.Windows  -- Windows API
Interpretation.BareMetal.ARM  -- Direct hardware
Interpretation.WASM     -- Browser APIs
```

## Verification

The compiler can be formally verified because:

1. **Small trusted base**: Only ~12 generators
2. **Known laws**: Category/functor laws proven in 1940s
3. **Equational**: Each rewrite preserves equality

Proof obligations:

```coq
(* Each generator preserves semantics *)
Theorem compile_compose :
  forall f g x,
  eval (compile (Compose f g)) x =
  eval (compile f) (eval (compile g) x).

(* Each optimization is a valid law *)
Theorem optimize_sound :
  forall e e', optimize e = e' -> denote e = denote e'.
```

Estimated verification effort: ~5,000-8,000 lines of Coq (including QTT). See [Formal Verification](formal-verification.md) for details.

## Ya as Reference Implementation

**Ya** is a Haskell library implementing Once principles. It serves as:
- Proof that natural transformations work in practice
- Reference semantics for the Once language
- Test bed for compilation strategies

Ya programs demonstrate the categorical structure that Once compiles.

## Summary

| Component | Description |
|-----------|-------------|
| **Frontend** | Parse Once syntax, type check |
| **IR** | Categorical combinators (~12 constructors) |
| **Optimizer** | Apply categorical laws |
| **Backend** | Generate target code from generators |
| **Verification** | Small trusted base, known laws |

The Once compiler is simpler than typical compilers because the source language has precise, compositional semantics. Category theory does the heavy lifting.
