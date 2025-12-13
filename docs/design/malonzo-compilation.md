# MAlonzo Compilation: Generating the Compiler from Agda

## Overview

This document describes the architecture for generating the Once compiler from verified Agda code using MAlonzo (Agda's Haskell backend). The goal is to have the entire compilation pipeline—desugar, optimize, codegen—generated from formally verified Agda, with the Haskell compiler acting as a thin wrapper.

## Motivation

### Why Generate from Agda?

1. **Verified by construction**: The optimizer applies categorical laws; Agda proves they preserve semantics
2. **Single source of truth**: No drift between spec (Agda) and implementation (Haskell)
3. **Trustworthy compiler**: Bugs in code generation become type errors in Agda
4. **Maintainability**: Change the Agda, regenerate the Haskell

### Current State

The Once project has parallel implementations:
- **Agda formalization** (`formal/`): Pure categorical IR, verified optimizer, x86 backend proofs
- **Haskell compiler** (`compiler/`): Full compiler with parsing, elaboration, optimization, C codegen

The Haskell IR includes constructs not in Agda (Let, LocalVar, Var, etc.), creating a mismatch.

## Two-Stage IR Architecture

### The Key Insight

Rather than adding all Haskell constructs to Agda (which complicates proofs), we use **two IRs**:

```
                    Haskell Parser/Elaborator
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                     Surface IR (Agda)                        │
│  Core constructors + Let + Prim + ConstStr                  │
└─────────────────────────────────────────────────────────────┘
                              │
                        desugar (Agda)
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                      Core IR (Agda)                          │
│  Pure categorical: id, ∘, fst, snd, ⟨,⟩, inl, inr, [,],    │
│  terminal, initial, curry, apply, fold, unfold, arr          │
└─────────────────────────────────────────────────────────────┘
                              │
                        optimize (Agda)
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   Optimized Core IR (Agda)                   │
└─────────────────────────────────────────────────────────────┘
                              │
                        codegen (Agda)
                              │
                              ▼
                          Assembly
```

### Why Two Stages?

1. **Core IR stays minimal**: 13 generators + fold/unfold + arr. No Let cases in optimizer proofs.
2. **Desugar is trivial**: One interesting equation (Let expansion), rest is structural.
3. **Existing proofs unchanged**: `Once.Optimize.Correct` works without modification.
4. **Clear separation**: Naming/binding is a Surface concern, not Core.

## Surface IR

### Definition

```agda
module Once.Surface.IR where

open import Once.Type
open import Once.IR as Core using () renaming (IR to CoreIR)

data SurfaceIR : Type → Type → Set where
  -- Embed all Core IR constructors
  id       : ∀ {A} → SurfaceIR A A
  _∘_      : ∀ {A B C} → SurfaceIR B C → SurfaceIR A B → SurfaceIR A C
  fst      : ∀ {A B} → SurfaceIR (A * B) A
  snd      : ∀ {A B} → SurfaceIR (A * B) B
  ⟨_,_⟩    : ∀ {A B C} → SurfaceIR C A → SurfaceIR C B → SurfaceIR C (A * B)
  inl      : ∀ {A B} → SurfaceIR A (A + B)
  inr      : ∀ {A B} → SurfaceIR B (A + B)
  [_,_]    : ∀ {A B C} → SurfaceIR A C → SurfaceIR B C → SurfaceIR (A + B) C
  terminal : ∀ {A} → SurfaceIR A Unit
  initial  : ∀ {A} → SurfaceIR Void A
  curry    : ∀ {A B C} → SurfaceIR (A * B) C → SurfaceIR A (B ⇒ C)
  apply    : ∀ {A B} → SurfaceIR ((A ⇒ B) * A) B
  fold     : ∀ {F} → SurfaceIR F (Fix F)
  unfold   : ∀ {F} → SurfaceIR (Fix F) F
  arr      : ∀ {A B} → SurfaceIR (A ⇒ B) (Eff A B)

  -- Surface-only constructs
  Let      : ∀ {A B C} → SurfaceIR A B → SurfaceIR (A * B) C → SurfaceIR A C
  Prim     : ∀ {A B} → String → SurfaceIR A B
  ConstStr : String → SurfaceIR Unit StringType
```

### Let Binding: De Bruijn Style

The `Let` constructor uses a clever encoding that avoids named variables:

```agda
Let : ∀ {A B C} → SurfaceIR A B → SurfaceIR (A * B) C → SurfaceIR A C
```

- First argument `e1 : SurfaceIR A B` computes the bound value
- Second argument `e2 : SurfaceIR (A * B) C` is the body
- The body receives a **pair** `(original-input, bound-value)`
- Access original input via `fst`, bound value via `snd`

**Example**: `let x = f a in g x x` becomes:
```agda
Let f (g ∘ ⟨ snd , snd ⟩)
-- f : A → B
-- g : B * B → C
-- body receives (a, f a), uses snd twice
```

This is equivalent to the categorical form but preserves the let structure until desugaring.

## Desugar Pass

### Definition

```agda
module Once.Surface.Desugar where

open import Once.Type
open import Once.Surface.IR as S
open import Once.IR as C

desugar : ∀ {A B} → S.SurfaceIR A B → C.IR A B
desugar S.id = C.id
desugar (g S.∘ f) = desugar g C.∘ desugar f
desugar S.fst = C.fst
desugar S.snd = C.snd
desugar S.⟨ f , g ⟩ = C.⟨ desugar f , desugar g ⟩
desugar S.inl = C.inl
desugar S.inr = C.inr
desugar S.[ f , g ] = C.[ desugar f , desugar g ]
desugar S.terminal = C.terminal
desugar S.initial = C.initial
desugar (S.curry f) = C.curry (desugar f)
desugar S.apply = C.apply
desugar S.fold = C.fold
desugar S.unfold = C.unfold
desugar S.arr = C.arr

-- The interesting cases:
desugar (S.Let e1 e2) = desugar e2 C.∘ C.⟨ C.id , desugar e1 ⟩
desugar (S.Prim name) = C.prim name    -- if Core has prim
desugar (S.ConstStr s) = C.constStr s  -- if Core has constStr
```

### Key Equation

The let-to-categorical translation:

```
let x = e1 in e2   ≡   e2 ∘ ⟨id, e1⟩
```

Semantically:
- Input `a : A` flows to both `id` (unchanged) and `e1` (producing `b : B`)
- Result is pair `(a, b) : A * B`
- Body `e2` receives this pair, producing final result

### Correctness (Optional Proof)

```agda
module Once.Surface.Desugar.Correct where

open import Once.Semantics
open import Once.Surface.IR as S
open import Once.Surface.Desugar

desugar-correct : ∀ {A B} (ir : S.SurfaceIR A B) (x : ⟦ A ⟧)
                → eval (desugar ir) x ≡ evalSurface ir x
desugar-correct (S.Let e1 e2) x =
  -- eval (desugar e2 ∘ ⟨id, desugar e1⟩) x
  -- = eval (desugar e2) (x , eval (desugar e1) x)
  -- = evalSurface e2 (x , evalSurface e1 x)   by IH
  -- = evalSurface (Let e1 e2) x               by definition
  ...
```

The proof is straightforward structural induction.

## MAlonzo Integration

### What is MAlonzo?

MAlonzo is Agda's Haskell backend. It compiles Agda to Haskell, generating:
- Data type definitions
- Function implementations
- FFI bindings for postulates

### Compilation Setup

MAlonzo compilation is set up in `formal/Makefile`:

```bash
cd formal
make malonzo    # Generate Haskell code to _build/malonzo/
```

The Makefile target uses these flags:
```bash
agda -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Compile.agda
```

Key flags:
- `-c` / `--compile`: Enable compilation to Haskell
- `--ghc-dont-call-ghc`: Generate Haskell but don't compile it (we want the source)
- `--compile-dir=PATH`: Output directory for generated files

### Generated Structure

Running `make malonzo` produces:
```
_build/malonzo/
├── MAlonzo/
│   ├── RTE.hs                    # Runtime support
│   └── Code/
│       ├── Once/
│       │   ├── Compile.hs        # Main entry point
│       │   ├── IR.hs             # Core IR data type
│       │   ├── Type.hs           # Type data type
│       │   ├── Optimize.hs       # Verified optimizer (~77KB!)
│       │   └── Surface/
│       │       ├── IR.hs         # Surface IR
│       │       └── Desugar.hs    # Desugar transformation
│       ├── Agda/...              # Standard library support
│       └── Data/...              # Data structure support
```

Total: ~222 Haskell files generated.

### Generated Functions

The entry point `MAlonzo.Code.Once.Compile` exports:

```haskell
-- d_compile_8 : compile = optimize ∘ desugar
d_compile_8 :: T_Type_4 -> T_Type_4 -> T_SurfaceIR_6 -> T_IR_4

-- d_compile'45'no'45'opt_16 : compile-no-opt = desugar
d_compile'45'no'45'opt_16 :: T_Type_4 -> T_Type_4 -> T_SurfaceIR_6 -> T_IR_4
```

These are the verified compilation functions that will be called from the Haskell wrapper.

### Nix Integration

MAlonzo compilation runs within the Nix development shell:
```bash
nix develop #default --command sh -c 'agda -c ...'
```

The standard library path is discovered dynamically from the Nix store to avoid hardcoded paths.

### Haskell Wrapper

The Haskell compiler imports MAlonzo-generated code:

```haskell
-- compiler/src/Once/Compile.hs
module Once.Compile (compile) where

import qualified MAlonzo.Code.Once.Compile as M
import Once.ToAgda (toAgdaIR)    -- Convert Haskell IR → Agda IR
import Once.FromAgda (fromAgdaIR) -- Convert Agda IR → Haskell IR

compile :: IR -> IR
compile = fromAgdaIR . M.compile . toAgdaIR

-- Or if we use Agda IR directly:
-- compile = M.compile
```

### FFI for Primitives

Primitives (syscalls, etc.) need FFI bindings:

```agda
-- formal/Once/Primitive.agda
postulate
  primEval : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

{-# FOREIGN GHC import Once.Primitive (primEval) #-}
{-# COMPILE GHC primEval = primEval #-}
```

## Full Pipeline

### Compilation Flow

```
hello.once
    │
    ▼
┌─────────────────┐
│  Parser (HS)    │  Megaparsec
└────────┬────────┘
         │ Syntax.Expr
         ▼
┌─────────────────┐
│ Type Check (HS) │  Bidirectional
└────────┬────────┘
         │ Typed Expr
         ▼
┌─────────────────┐
│ Elaborate (HS)  │  Surface syntax → Surface IR
└────────┬────────┘
         │ SurfaceIR (Agda type)
         ▼
┌─────────────────┐
│ Desugar (Agda)  │  MAlonzo-generated
└────────┬────────┘
         │ CoreIR (Agda type)
         ▼
┌─────────────────┐
│ Optimize (Agda) │  MAlonzo-generated, verified
└────────┬────────┘
         │ CoreIR (optimized)
         ▼
┌─────────────────┐
│ CodeGen (Agda)  │  MAlonzo-generated (future)
└────────┬────────┘
         │
         ▼
      hello.s / hello.c
```

### What's Verified?

| Component | Status | Verification |
|-----------|--------|--------------|
| Parser | Haskell | Not verified |
| Type Checker | Haskell | Not verified |
| Elaboration | Haskell | Not verified |
| Desugar | Agda | Can be verified |
| Optimizer | Agda | **Verified** (Once.Optimize.Correct) |
| CodeGen | Agda | Partially verified (Once.Backend.X86.Correct) |

The optimizer is the critical verified component—it's where categorical laws are applied.

## Implementation Roadmap

### Phase 1: Documentation ✓
- [x] D035 decision log entry
- [x] This design document
- [x] Update overview.md
- [x] Update compiler.md

### Phase 2: Agda Surface IR ✓
- [x] Create `formal/Once/Surface/IR.agda` - Surface IR with Let, Prim
- [x] Create `formal/Once/Surface/Desugar.agda` - Transformation to Core IR
- [x] Create `formal/Once/Surface/Desugar/Correct.agda` - Correctness proof
- [x] Add `surfaceir` target to `formal/Makefile`
- [x] Type-check passes

### Phase 3: MAlonzo Setup ✓
- [x] Create `formal/Once/Compile.agda` - Main entry point
- [x] Add `malonzo` target to `formal/Makefile`
- [x] Configure for Nix (dynamic stdlib discovery)
- [x] Test: generates ~222 Haskell files successfully

### Phase 4: Haskell Integration ✓
- [x] Create `Once.MAlonzo` bridge module with type/IR conversion
- [x] Import MAlonzo-generated modules into compiler (once.cabal)
- [x] Wire `d_compile_8` into compilation pipeline via `optimizeMAlonzo`
- [x] Add `--optimizer malonzo` CLI flag
- [x] Test: Both optimizers produce identical output for pure categorical IR

### Phase 5: Codegen Migration (Future)
- [ ] Move x86 codegen to Agda (in progress - see Once.Backend.X86)
- [ ] Generate x86 codegen via MAlonzo
- [ ] Full verified pipeline from SurfaceIR to assembly

### Known Limitations

**Prim postulate**: Currently `Prim` is handled via postulate. See TODO in `Once/Surface/Desugar.agda`:
```agda
-- TODO: When x86 verification is complete, consider moving Prim to Core IR
-- (Option A from desugar design discussion). This would eliminate the postulate.
```

**Funext dependency**: The correctness proof requires function extensionality (`extensionality` from `Once/Postulates.agda`). This is standard but worth noting in the TCB.

## Alternatives Considered

### Option 1: Extend Agda IR
Add Let, Var, etc. directly to `Once.IR`.

**Rejected because**: Every proof in `Once.Optimize.Correct` would need additional cases. The categorical laws don't involve Let, so these cases would be boilerplate that complicates maintenance.

### Option 2: Haskell Wrapper
Keep Agda IR pure, write Haskell code to convert.

**Rejected because**: Conversion code isn't verified. We'd have two IR definitions to maintain. Defeats the goal of generating everything from Agda.

### Option 3: Replace Haskell IR
Use Agda IR as the only IR, removing Let etc. from Haskell.

**Rejected because**: Let is genuinely useful in the elaborated code (see D029). Major refactor for unclear benefit.

## Summary

The two-stage IR architecture enables:

1. **Verified optimizer**: Core IR stays pure categorical, proofs stay clean
2. **MAlonzo generation**: Entire pipeline from Agda to Haskell
3. **Clear separation**: Surface handles naming, Core handles computation
4. **Incremental adoption**: Can migrate components one at a time

This design preserves the mathematical elegance of the categorical IR while providing practical conveniences in the surface representation.
