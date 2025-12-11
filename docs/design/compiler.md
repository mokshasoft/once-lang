# The Once Compiler

## Overview

The Once compiler is implemented in Haskell and translates `.once` source files to C code. Unlike the Ya project (which is an embedded DSL in Haskell), Once has a standalone compiler with its own parser, type checker, and code generator.

## Source Structure

```
compiler/src/Once/
├── CLI.hs         -- Command-line interface
├── Parser.hs      -- Megaparsec-based parser
├── Syntax.hs      -- Surface syntax AST
├── TypeCheck.hs   -- Bidirectional type checking
├── Type.hs        -- Type representations
├── Elaborate.hs   -- Surface syntax to IR
├── IR.hs          -- Categorical intermediate representation
├── Optimize.hs    -- Law-based rewriting
├── Quantity.hs    -- QTT quantity tracking
├── Eval.hs        -- Interpreter (for testing)
├── Value.hs       -- Runtime values
└── Backend/
    └── C.hs       -- C code generation
```

## Compilation Pipeline

```
Source (.once)
     │
     ▼
┌─────────────┐
│   Parser    │  Parser.hs
└──────┬──────┘
       │ Syntax.Expr
       ▼
┌─────────────┐
│ Type Check  │  TypeCheck.hs
└──────┬──────┘
       │ Typed Syntax
       ▼
┌─────────────┐
│  Elaborate  │  Elaborate.hs
└──────┬──────┘
       │ IR
       ▼
┌─────────────┐
│  Optimize   │  Optimize.hs
└──────┬──────┘
       │ Optimized IR
       ▼
┌─────────────┐
│  Backend/C  │  Backend/C.hs
└──────┬──────┘
       │
       ▼
Output (.c, .h)
```

## The IR: Categorical Generators

The core intermediate representation (`IR.hs`) contains the 12 generators:

```haskell
data IR
  -- Category
  = Id Type
  | Compose IR IR

  -- Products
  | Fst Type Type
  | Snd Type Type
  | Pair IR IR
  | Terminal Type

  -- Coproducts
  | Inl Type Type
  | Inr Type Type
  | Case IR IR
  | Initial Type

  -- Exponentials
  | Curry IR
  | Apply Type Type

  -- Extensions for surface syntax
  | Var Name
  | Prim Name Type Type
  | StringLit Text
```

Every Once program elaborates to this IR before code generation.

## Optimization

The optimizer (`Optimize.hs`) applies categorical laws:

```haskell
optimize :: IR -> IR
optimize ir =
  let ir' = optimizeOnce ir
  in if ir' == ir then ir else optimize ir'
```

Rules implemented:

| Law | Before | After |
|-----|--------|-------|
| Right identity | `compose f (Id _)` | `f` |
| Left identity | `compose (Id _) f` | `f` |
| Product beta (fst) | `compose (Fst _ _) (Pair h _)` | `h` |
| Product beta (snd) | `compose (Snd _ _) (Pair _ k)` | `k` |
| Coproduct beta (inl) | `compose (Case h _) (Inl _ _)` | `h` |
| Coproduct beta (inr) | `compose (Case _ k) (Inr _ _)` | `k` |
| Associativity | `compose (compose h g) f` | `compose h (compose g f)` |

The optimizer iterates until no more rules apply (fixed point).

## C Code Generation

The C backend (`Backend/C.hs`) generates:
- A header file (`.h`) with type definitions and function declarations
- An implementation file (`.c`) with function bodies

### Type Mapping

| Once Type | C Representation |
|-----------|------------------|
| `Unit` | `struct {}` (empty) |
| `A * B` | `struct { A fst; B snd; }` |
| `A + B` | Tagged union with `tag` field |
| `A -> B` | Function pointer |
| `String Utf8` | `char*` with length |

### Generator Mapping

| IR | C Code |
|----|--------|
| `Id` | Return input unchanged |
| `Compose g f` | `g(f(x))` |
| `Fst` | `x.fst` |
| `Snd` | `x.snd` |
| `Pair f g` | `(typeof result){f(x), g(x)}` |
| `Inl` | `{.tag = 0, .left = x}` |
| `Inr` | `{.tag = 1, .right = x}` |
| `Case f g` | `x.tag ? g(x.right) : f(x.left)` |

## Usage

### Building

```bash
cd compiler
stack build
```

### Compiling Once Code

```bash
# Library mode (generates .h and .c)
stack exec -- once build example.once -o example

# Executable mode (with interpretation)
stack exec -- once build --exe --interp ../lib/Interpretations/Linux main.once -o main
```

### Example

Input (`swap.once`):
```
swap : A * B -> B * A
swap = pair snd fst
```

Output (`swap.h`):
```c
#pragma once
typedef struct { ... } swap_input;
typedef struct { ... } swap_output;
swap_output once_swap(swap_input x);
```

Output (`swap.c`):
```c
swap_output once_swap(swap_input x) {
    return (swap_output){ x.snd, x.fst };
}
```

## Interpretations

Primitives connect Once code to platform-specific functionality. The `--interp` flag specifies an interpretation directory:

```
lib/Interpretations/Linux/
├── syscalls.once  -- Primitive declarations (exit, puts, etc.)
├── syscalls.c     -- C implementations
├── memory.once    -- Memory primitives (alloc, free, etc.)
└── memory.c       -- C implementations
```

Example primitive declaration:
```
primitive puts : String Utf8 -> Unit
```

The compiler links the primitive name to its C implementation.

## Differences from Ya

| Aspect | Ya | Once Compiler |
|--------|-----|---------------|
| Implementation | Haskell EDSL | Standalone compiler |
| Input | Haskell code using Ya combinators | `.once` source files |
| Output | Runs in Haskell | Generates C code |
| Type checking | Haskell's type system | Custom type checker |
| Syntax | Haskell syntax | Once-specific syntax |

Ya demonstrates the categorical principles in Haskell. The Once compiler applies those principles to generate standalone executables.

## Future Work

- Additional backends (Rust, JavaScript, WASM)
- QTT quantity enforcement
- More optimizations (eta rules, fusion)
- Formal verification of the optimizer

## Summary

The Once compiler transforms categorical programs into efficient C code:

1. **Parse** Once syntax into an AST
2. **Type check** with bidirectional inference
3. **Elaborate** surface syntax to categorical IR
4. **Optimize** by applying categorical laws
5. **Generate** C code from IR

The small IR (~12 generators) makes each phase straightforward and amenable to formal verification.
