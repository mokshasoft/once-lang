# Once Compiler Implementation Plan

## Principles

1. **Small focused commits** - Each commit does one thing, is testable
2. **Property testing as spec** - QuickCheck properties ARE the formal specification
3. **One backend (C)** - FFI-friendly library; other languages call via C FFI
4. **Verification-ready** - Structure code so proofs can be added incrementally
5. **Fourmolu** - Consistent formatting
6. **Example-driven** - Build only what's needed to compile the current example

## Target: Hello World as Library

Once's hello world is a **library with C interface**, not a standalone executable:

```
-- swap.once
swap : A * B -> B * A
swap = pair snd fst
```

This is **pure natural transformations** - no primitives, just generators.

Compiles to:

```c
// once_swap.h
#ifndef ONCE_SWAP_H
#define ONCE_SWAP_H

typedef struct { void* fst; void* snd; } OncePair;

OncePair once_swap(OncePair x);

#endif
```

```c
// once_swap.c
#include "once_swap.h"

OncePair once_swap(OncePair x) {
    return (OncePair){ .fst = x.snd, .snd = x.fst };
}
```

Test from C:

```c
// test_swap.c
#include <stdio.h>
#include "once_swap.h"

int main() {
    OncePair input = { .fst = "hello", .snd = "world" };
    OncePair output = once_swap(input);
    printf("swap = (%s, %s)\n", (char*)output.fst, (char*)output.snd);
    // Output: swap = (world, hello)
    return 0;
}
```

**This is Once's hello world.** Pure categorical structure, callable from any language.

## Example Progression

Each example adds one capability:

| Example | New Capability | Tests |
|---------|----------------|-------|
| `swap : A * B -> B * A` | Products, projections, pairing, polymorphism | C calls Once |
| `not : Bool -> Bool` | Coproducts (Bool = Unit + Unit), case | Pattern on sum |
| `fromMaybe : A * Maybe A -> A` | Case analysis, Maybe | Handle Nothing |
| `map : (A -> B) -> List A -> List B` | Recursion, algebraic data | Recursive types |

## Architecture

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   Source    │ -> │   Typed     │ -> │  Optimized  │ -> │  C Library  │
│   .once     │    │     IR      │    │     IR      │    │  .h + .c    │
└─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘
     Parse         Type Check +           Rewrite          Generate
                  QTT Inference
```

## Phase 1: Core IR + Interpreter

**Goal**: IR that can represent `swap`, interpreter to validate semantics.

### Commits

```
1. Initialize cabal project with dependencies
2. Add fourmolu.yaml config
3. Add Quantity type with semiring operations
4. Add Quantity property tests (semiring laws)
5. Add Type representation
6. Add IR type for generators
7. Add Value type for interpreter
8. Add eval function for generators
9. Add property tests for categorical laws
```

### Key Files

**Quantity.hs**
```haskell
module Once.Quantity where

data Quantity = Zero | One | Omega
  deriving (Eq, Show)

qAdd :: Quantity -> Quantity -> Quantity
qAdd Zero r = r
qAdd r Zero = r
qAdd One One = Omega
qAdd _ _ = Omega

qMul :: Quantity -> Quantity -> Quantity
qMul Zero _ = Zero
qMul _ Zero = Zero
qMul One r = r
qMul r One = r
qMul Omega Omega = Omega
```

**IR.hs**
```haskell
module Once.IR where

import Once.Quantity
import Once.Type

data IR
  = Id Type
  | Compose IR IR
  | Fst Type Type
  | Snd Type Type
  | Pair IR IR
  | Inl Type Type
  | Inr Type Type
  | Case IR IR
  | Terminal Type
  | Initial Type
  | Curry IR
  | Apply Type Type
  | Var Name
  | Prim Name Type Type  -- primitive operation
  deriving (Eq, Show)
```

### Properties (Spec)

```haskell
-- Semiring laws
prop_qAdd_zero_left r = qAdd Zero r === r
prop_qAdd_zero_right r = qAdd r Zero === r
prop_qMul_one_left r = qMul One r === r
prop_qMul_one_right r = qMul r One === r
prop_qMul_zero_left r = qMul Zero r === Zero

-- Category laws
prop_id_right f x = eval (Compose f (Id t)) x === eval f x
prop_id_left f x = eval (Compose (Id t) f) x === eval f x
prop_assoc f g h x =
  eval (Compose f (Compose g h)) x === eval (Compose (Compose f g) h) x

-- Product laws
prop_fst_pair f g x = eval (Compose (Fst _ _) (Pair f g)) x === eval f x
prop_snd_pair f g x = eval (Compose (Snd _ _) (Pair f g)) x === eval g x
```

## Phase 2: Parser

**Goal**: Parse `swap.once` to AST.

### Commits

```
1. Add surface syntax AST types
2. Add lexer (whitespace, identifiers, symbols)
3. Add type parser
4. Add expression parser
5. Add declaration parser
6. Add parser for double.once example
7. Add parser round-trip property tests
```

### Target Syntax

```
-- Types
Int
A * B        -- product
A + B        -- sum
A -> B       -- function
A^1          -- quantity annotation

-- Expressions
x            -- variable
f x          -- application
(x, y)       -- pair
\x -> e      -- lambda
case e of    -- case
  Left a -> ...
  Right b -> ...

-- Declarations
name : Type
name = expr

primitive name : Type
```

## Phase 3: Type Checker + QTT

**Goal**: Type check `swap.once` and infer quantities.

### Commits

```
1. Add type checking context
2. Add type checking for variables and primitives
3. Add type checking for pair and projections
4. Add type checking for application
5. Add quantity constraint generation
6. Add quantity constraint solving
7. Add elaboration to IR
8. Type check double.once example
9. Add type checking property tests
```

### Properties (Spec)

```haskell
-- Well-typed programs don't get stuck
prop_progress e =
  isRight (typeCheck e) ==> isValue e || canStep e

-- Types preserved under evaluation
prop_preservation e t =
  typeCheck e === Right t ==> typeCheck (step e) === Right t

-- Linear code doesn't copy
prop_linear_no_copy e =
  inferQuantity e === One ==> not (containsDiagonal e)
```

## Phase 4: Optimizer

**Goal**: Apply categorical laws to simplify IR.

### Commits

```
1. Add rewrite rule type
2. Add identity elimination rules
3. Add composition associativity
4. Add product beta rules (fst/snd of pair)
5. Add optimization driver (iterate to fixpoint)
6. Add property: rewrites preserve semantics
```

### Properties (Spec)

```haskell
-- Rewrites preserve meaning
prop_rewrite_sound rule ir =
  case applyRule rule ir of
    Nothing -> property True
    Just ir' -> eval ir === eval ir'

-- Optimization preserves meaning
prop_optimize_sound ir = eval (optimize ir) === eval ir
```

## Phase 5: C Backend

**Goal**: Generate C library from `swap.once`.

### Commits

```
1. Add C type mapping (products -> structs, etc.)
2. Add C expression generation for generators
3. Add C function generation
4. Add C header generation
5. Generate C for swap.once
6. Add test: compile generated C with gcc
7. Add test: run C and verify result matches interpreter
```

### Properties (Spec)

```haskell
-- Generated C compiles
prop_c_compiles ir = compileWithGcc (generateC ir) === ExitSuccess

-- Generated C matches interpreter
prop_c_correct ir input =
  runGeneratedC ir input === eval ir input
```

## Phase 6: CLI

**Goal**: `once build swap.once` produces C library.

### Commits

```
1. Add CLI argument parsing
2. Add build command
3. Add check command (type check only)
4. Add analyze command (show inferred quantities)
5. Build swap.once end-to-end
```

### Usage

```bash
$ once build swap.once -o libswap
# Produces: libswap.h, libswap.c

$ once check swap.once
# Type checks, reports errors

$ once analyze swap.once
# Shows inferred quantities:
#   swap : (A * B)^1 -> (B * A)^1
#   Linear: yes
```

## Project Structure

```
compiler/
├── src/Once/
│   ├── Quantity.hs
│   ├── Type.hs
│   ├── IR.hs
│   ├── Eval.hs
│   ├── Syntax.hs
│   ├── Parser.hs
│   ├── TypeCheck.hs
│   ├── QTT.hs
│   ├── Elaborate.hs
│   ├── Optimize.hs
│   ├── Backend/
│   │   └── C.hs
│   └── CLI.hs
├── test/
│   ├── QuantitySpec.hs
│   ├── IRSpec.hs
│   ├── EvalSpec.hs
│   ├── ParserSpec.hs
│   ├── TypeCheckSpec.hs
│   ├── OptimizeSpec.hs
│   └── BackendSpec.hs
├── examples/
│   └── swap.once
├── once.cabal
├── fourmolu.yaml
└── README.md
```

## Dependencies

```yaml
dependencies:
  - base >= 4.14
  - megaparsec
  - prettyprinter
  - containers
  - mtl
  - text
  - optparse-applicative
  - process            # for running gcc in tests
  - temporary          # for temp files in tests

test-dependencies:
  - tasty
  - tasty-quickcheck
  - tasty-hunit
```

## Verification Path

### Now: Property Tests = Spec

```haskell
-- This IS the formal specification
prop_id_right f x = eval (Compose f (Id t)) x === eval f x
```

### Later: Proofs

```coq
(* Same property, now a theorem *)
Theorem id_right : forall f x, eval (Compose f (Id _)) x = eval f x.
Proof. reflexivity. Qed.
```

Properties are written to be **theorem-shaped**. Each one can become a Coq lemma.

## Milestones

| Milestone | Goal | Deliverable |
|-----------|------|-------------|
| **M1** | IR + interpreter | `eval swap === (b, a)` |
| **M2** | Parser | Parse swap.once |
| **M3** | Type checker | Type check swap.once |
| **M4** | C backend | Generate C for swap.once |
| **M5** | End-to-end | `once build swap.once` works |

## Success Criteria

```bash
# Write Once
$ cat examples/swap.once
swap : A * B -> B * A
swap = pair snd fst

# Compile to C
$ once build examples/swap.once -o libswap

# Use from C
$ cat test.c
#include "libswap.h"
#include <stdio.h>
int main() {
    OncePair p = { .fst = "hello", .snd = "world" };
    OncePair r = once_swap(p);
    printf("(%s, %s)\n", (char*)r.fst, (char*)r.snd);
}

$ gcc test.c libswap.c -o test
$ ./test
(world, hello)
```

**That's the goal.** Everything else serves this.
