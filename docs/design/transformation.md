# Cross-Platform Compilation

## The Core Insight

Once programs compile to multiple target languages because they're built from universal building blocks. The 12 categorical generators exist in every programming language - they just have different syntax.

## From Once to Any Target

A Once program:

```
swap : A * B -> B * A
swap = pair snd fst
```

Contains only universal concepts:
- Take the second element of a pair (`snd`)
- Take the first element of a pair (`fst`)
- Combine two values into a pair (`pair`)

Every language can express these operations.

## Target Language Mappings

### Products

| Once | C | Rust | JavaScript | Haskell |
|------|---|------|------------|---------|
| `A * B` | `struct { A a; B b; }` | `(A, B)` | `[a, b]` | `(A, B)` |
| `fst` | `.a` | `.0` | `[0]` | `fst` |
| `snd` | `.b` | `.1` | `[1]` | `snd` |
| `pair f g` | `{f(x), g(x)}` | `(f(x), g(x))` | `[f(x), g(x)]` | `f &&& g` |

### Coproducts

| Once | C | Rust | JavaScript | Haskell |
|------|---|------|------------|---------|
| `A + B` | tagged union | `enum` | `{tag, val}` | `Either A B` |
| `inl x` | `{0, x}` | `Left(x)` | `{tag:'l', val:x}` | `Left x` |
| `inr x` | `{1, x}` | `Right(x)` | `{tag:'r', val:x}` | `Right x` |
| `case f g` | `switch` | `match` | `if tag...` | `either f g` |

### Composition

| Once | C | Rust | JavaScript | Haskell |
|------|---|------|------------|---------|
| `compose f g` | `f(g(x))` | `f(g(x))` | `f(g(x))` | `f . g` |
| `id` | `x` | `x` | `x` | `id` |

## Compilation Pipeline

```
┌──────────────┐
│  Once Source │
│  (*.once)    │
└──────┬───────┘
       │ Parse
       ▼
┌──────────────┐
│  Typed AST   │
│              │
└──────┬───────┘
       │ Lower to generators
       ▼
┌──────────────┐
│ Categorical  │
│     IR       │
└──────┬───────┘
       │ Target-specific codegen
       ▼
┌──────────────────────────────────────┐
│    C    │  Rust  │   JS   │  WASM   │
└──────────────────────────────────────┘
```

The Categorical IR is the key abstraction - it contains only generators and their compositions, with no target-specific details.

## Preserving Semantics

The categorical laws guarantee that meaning is preserved across targets:

```
-- These equalities hold in EVERY target language
compose id f       = f
compose f id       = f
compose f (compose g h) = compose (compose f g) h

fst (pair f g)     = f
snd (pair f g)     = g
pair fst snd       = id

case inl inr       = id
case f g . inl     = f
case f g . inr     = g
```

When the Once compiler transforms code using these laws, the behavior stays the same regardless of target.

## Practical Example

### Once Source

```
-- Safely access nested optional values
flatMap : (A -> Maybe B) -> Maybe A -> Maybe B
flatMap f = case (compose f id) (const nothing)
```

### Generated C

```c
typedef struct { int tag; void* val; } Maybe;

Maybe flatMap(Maybe (*f)(void*), Maybe ma) {
    if (ma.tag == 0) {  // nothing
        return (Maybe){0, NULL};
    }
    return f(ma.val);   // just: apply f
}
```

### Generated Rust

```rust
fn flat_map<A, B>(f: impl Fn(A) -> Option<B>, ma: Option<A>) -> Option<B> {
    match ma {
        None => None,
        Some(a) => f(a),
    }
}
```

### Generated JavaScript

```javascript
function flatMap(f, ma) {
    if (ma.tag === 'nothing') {
        return { tag: 'nothing' };
    }
    return f(ma.val);
}
```

Same logic, different syntax. The Once compiler generates idiomatic code for each target.

## What Transfers, What Doesn't

### Transfers to All Targets

- Pure computations (Derived stratum)
- Data transformations
- Business logic
- Algorithms

### Requires Target-Specific Code

- File I/O
- Network access
- System calls
- Hardware interaction

This is why Once separates Derived (portable) from Interpretations (platform-specific).

## Backend Architecture

Each backend implements a single interface:

```
Backend = {
  emitProduct   : Type -> Type -> TargetCode
  emitCoproduct : Type -> Type -> TargetCode
  emitCompose   : Code -> Code -> TargetCode
  emitCase      : Code -> Code -> TargetCode
  emitPair      : Code -> Code -> TargetCode
  ...
}
```

Adding a new target means implementing these ~12 functions. The rest of the compiler is shared.

## Optimization Opportunities

Because the compiler understands the categorical structure, it can apply principled optimizations:

### Composition Fusion

```
-- Before
compose (compose f g) (compose h k)

-- After (associativity)
compose f (compose g (compose h k))
```

Reduces function call overhead.

### Dead Code via Terminal

```
-- If result is discarded
terminal . expensive_computation

-- Can be simplified to
terminal
```

The computation is never needed.

### Product Simplification

```
-- Redundant pair
fst (pair f g)

-- Simplifies to
f
```

The `g` computation is eliminated.

## Current and Planned Targets

| Target | Status | Output |
|--------|--------|--------|
| C | Implemented | `.c` + `.h` |
| Rust | Planned | `.rs` |
| JavaScript | Planned | `.js` |
| WebAssembly | Planned | `.wasm` |
| LLVM IR | Planned | `.ll` |
| Haskell | Planned | `.hs` |

## Benefits

| Aspect | Traditional | Once |
|--------|-------------|------|
| Implementations | N (one per language) | 1 |
| Bug surface | N independent codebases | 1 codebase |
| Testing | N test suites | 1 test suite |
| Maintenance | N × effort | 1 × effort |

The categorical foundation makes this possible - natural transformations describe structure that every language can implement.
