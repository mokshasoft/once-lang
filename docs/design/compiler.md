# The Once Compiler

## Architecture Overview

The Once compiler transforms source code into target language output through a series of well-defined phases. The design emphasizes simplicity: because Once programs are built from ~12 categorical generators, the compiler's core is small and amenable to formal verification.

```
Source (.once)
     │
     ▼
┌─────────┐
│  Parse  │
└────┬────┘
     │ AST
     ▼
┌─────────┐
│  Type   │
│  Check  │
└────┬────┘
     │ Typed AST
     ▼
┌─────────┐
│  Lower  │
└────┬────┘
     │ Categorical IR
     ▼
┌─────────┐
│Optimize │
└────┬────┘
     │ Optimized IR
     ▼
┌─────────┐
│ Codegen │
└────┬────┘
     │
     ▼
Target (.c, .rs, .js, ...)
```

## Phase 1: Parsing

The parser converts Once source text into an abstract syntax tree.

### Input Syntax

```
-- Type signature
processData : String -> Result Data Error

-- Definition using generators
processData = compose validate parse

-- Type definitions
type Result A E = A + E
```

### Output AST

```haskell
data Expr
  = Var Name
  | App Expr Expr
  | Lam Name Expr
  | Let Name Expr Expr
  | Ann Expr Type
  | Prim Primitive
```

The AST is standard for functional languages - nothing unusual here.

## Phase 2: Type Checking

Bidirectional type checking with type inference. The type checker ensures:

1. **Morphism compatibility**: In `compose f g`, the target of `g` matches the source of `f`
2. **Product access**: `fst` and `snd` only apply to product types
3. **Sum elimination**: `case` handlers cover both branches
4. **Quantity tracking**: Linear values used exactly once (when QTT enabled)

### Type Rules

```
─────────────────────────
Γ ⊢ id : A → A

Γ ⊢ f : B → C    Γ ⊢ g : A → B
──────────────────────────────
Γ ⊢ compose f g : A → C

Γ ⊢ f : C → A    Γ ⊢ g : C → B
───────────────────────────────
Γ ⊢ pair f g : C → A × B
```

## Phase 3: Lowering to Categorical IR

The typed AST is lowered to an intermediate representation containing only the generators.

### IR Definition

```haskell
data CatIR
  = CId Type
  | CCompose CatIR CatIR
  | CFst Type Type
  | CSnd Type Type
  | CPair CatIR CatIR
  | CInl Type Type
  | CInr Type Type
  | CCase CatIR CatIR
  | CTerminal Type
  | CInitial Type
  | CCurry CatIR
  | CApply Type Type
  | CPrimitive Name Type Type
```

This is the compiler's core abstraction. Every Once program reduces to compositions of these constructors.

### Lowering Examples

| Source | Categorical IR |
|--------|---------------|
| `\x -> x` | `CId A` |
| `\x -> (x, x)` | `CPair (CId A) (CId A)` |
| `\(a,b) -> (b,a)` | `CPair (CSnd A B) (CFst A B)` |

## Phase 4: Optimization

Optimizations are applications of categorical laws. Each rewrite preserves semantics by construction.

### Identity Laws

```
compose f (CId _)  →  f
compose (CId _) f  →  f
```

### Product Laws

```
CFst `compose` CPair f g  →  f
CSnd `compose` CPair f g  →  g
CPair CFst CSnd           →  CId
```

### Coproduct Laws

```
CCase CInl CInr           →  CId
CCase f g `compose` CInl  →  f
CCase f g `compose` CInr  →  g
```

### Fusion

```
CPair (compose f h) (compose g h)  →  compose (CPair f g) h
```

The optimizer applies these rewrites to a fixed point.

## Phase 5: Code Generation

The code generator maps each IR constructor to target language constructs.

### C Backend

```haskell
genC :: CatIR -> CCode
genC (CId t)        = "x"
genC (CCompose f g) = genC f ++ "(" ++ genC g ++ "(x))"
genC (CFst _ _)     = "x.fst"
genC (CSnd _ _)     = "x.snd"
genC (CPair f g)    = "{" ++ genC f ++ ", " ++ genC g ++ "}"
genC (CInl _ _)     = "{.tag = 0, .val.left = x}"
genC (CInr _ _)     = "{.tag = 1, .val.right = x}"
genC (CCase f g)    = "x.tag ? " ++ genC g ++ " : " ++ genC f
```

### Type Representations

| Once Type | C | Rust | JavaScript |
|-----------|---|------|------------|
| `A * B` | `struct {A fst; B snd;}` | `(A, B)` | `[a, b]` |
| `A + B` | tagged union | `enum` | `{tag, val}` |
| `A -> B` | function pointer | `fn(A) -> B` | function |
| `Unit` | empty struct | `()` | `undefined` |
| `Void` | empty enum | `!` | (impossible) |

## Primitives and Interpretations

Primitives bridge Once code to platform-specific functionality.

### Declaration

```
primitive readByte : Handle -> IO (Byte + Error)
```

### Resolution

The compiler looks up primitive implementations from the specified interpretation:

```
once build program.once --interp interpretations/linux
```

The interpretation directory contains target-specific implementations:

```
interpretations/linux/
  io.c          -- readByte, writeByte, etc.
  io.h
  memory.c      -- allocation primitives
  memory.h
```

## Compiler Implementation

The current implementation is in Haskell:

```
compiler/
  src/
    Once/
      Parser.hs      -- Megaparsec-based parser
      TypeCheck.hs   -- Bidirectional type checker
      Lower.hs       -- AST to Categorical IR
      Optimize.hs    -- Law-based rewriting
      Codegen/
        C.hs         -- C code generation
```

### Building

```bash
cd compiler
stack build
stack exec -- once build example.once -o example
```

## Verification Strategy

The compiler's simplicity enables formal verification:

1. **Small IR**: Only ~12 constructors to verify
2. **Equational rewrites**: Each optimization is a proven law
3. **Compositional semantics**: Meaning defined structurally

See [What Is Proven](../formal/what-is-proven.md) for current verification status.

### Trusted Computing Base

| Component | Trust Level |
|-----------|-------------|
| Parser | Untrusted (can verify output) |
| Type checker | Trusted (ensures well-formedness) |
| Optimizer | Verified (laws proven in Agda) |
| Codegen | Trusted (target-specific) |

## Adding a New Backend

To add a new target language:

1. Create `src/Once/Codegen/NewTarget.hs`
2. Implement generator mappings:
   ```haskell
   genNewTarget :: CatIR -> NewTargetCode
   genNewTarget (CId t)        = ...
   genNewTarget (CCompose f g) = ...
   -- etc.
   ```
3. Add type representations for the target
4. Register in the compiler driver

The categorical IR isolates target-specific concerns to this single module.

## Performance Considerations

### Compilation Speed

- Parsing: O(n) in source size
- Type checking: O(n) typical, O(n²) worst case
- Optimization: O(n × k) where k is rewrite iterations
- Codegen: O(n) in IR size

### Generated Code Quality

The categorical laws enable optimizations that remove abstraction overhead:

```
-- Before optimization
pair fst snd

-- After optimization (eta reduction)
id
```

Target-specific backends can apply additional optimizations (inlining, register allocation) appropriate for their platform.
