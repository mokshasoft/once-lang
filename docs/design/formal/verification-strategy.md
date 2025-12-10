# Formal Verification Strategy for Once

## Overview

Once is designed to be formally verifiable. This document describes the strategy for mechanized verification of the Once compiler using Agda, with extraction to Haskell.

## Why Verify?

Once's value proposition depends on guarantees:
- Linear code requires no garbage collection
- Natural transformations preserve semantics across backends
- The ~12 generators are correctly implemented

Without formal verification, these are claims. With verification, they are theorems.

## Why Agda?

### Decision Summary

We evaluated several proof assistants:

| Assistant | Strengths | Weaknesses |
|-----------|-----------|------------|
| **HOL4** | CakeML uses it, mature | SML-centric, small community |
| **Coq** | CompCert, large community | Extraction to Haskell awkward |
| **Lean 4** | Modern, fast, great tooling | No Haskell extraction |
| **Agda** | Haskell extraction, category theory libs | Less automation |
| **Idris 2** | Native QTT | Too immature |

### Why Agda Fits Once

1. **Haskell extraction**: Once's compiler is written in Haskell. Agda extracts directly to Haskell, allowing verified code to replace unverified code incrementally.

2. **agda-categories**: A mature category theory library that directly models cartesian closed categories - exactly what Once's generators are.

3. **PL community alignment**: QTT research and type theory papers often use Agda. The community that cares about Once's type system uses Agda.

4. **Dependent types**: Can express rich specifications like "well-typed programs don't go wrong" directly.

5. **Proofs are programs**: Agda's philosophy matches Once's - both emphasize that the program IS the specification.

### Acceptance

Agda proofs are accepted by the PL research community. Major conferences (POPL, ICFP, PLDI) regularly publish Agda-verified work. The trusted computing base is:
- Agda's type checker (small, well-understood)
- The MAlonzo extraction mechanism (to Haskell)
- GHC (compiles extracted Haskell)

## Architecture: Verified Core, Unverified Shell

```
┌─────────────────────────────────────────┐
│          Verified Core (Agda)           │
│  - IR, semantics, type checker, codegen │
│  - All proofs live here                 │
│  - Extracted to Haskell                 │
└────────────────┬────────────────────────┘
                 │ MAlonzo extraction
                 ▼
┌─────────────────────────────────────────┐
│         Unverified Shell (Haskell)      │
│  - Parser (megaparsec)                  │
│  - CLI (optparse-applicative)           │
│  - File IO                              │
│  - Error formatting                     │
└─────────────────────────────────────────┘
```

The **security-critical** parts are verified. The **plumbing** is not.

Why not write everything in Agda?
- Agda compiles via Haskell anyway (MAlonzo) - same TCB
- Parser/CLI in Agda is painful and slow to develop
- The bugs that matter are in the core, not the shell

## Verification Scope

### What We Will Verify

1. **Core IR semantics**: The ~12 generators and their operational semantics
2. **Categorical laws**: Identity, associativity, product/coproduct laws, exponential laws
3. **Type soundness**: Well-typed IR terms evaluate without getting stuck
4. **QTT properties**: Linear terms don't duplicate resources
5. **C backend correctness**: Generated C preserves IR semantics

### What We Will NOT Verify (Initially)

- Parser (complex, lower value)
- Pretty printer (not safety-critical)
- CLI argument handling
- GHC itself
- The C compiler (gcc/clang)

### Trusted Computing Base

The following must be trusted without proof:
- Agda's type checker
- MAlonzo extraction
- GHC
- The C compiler
- The operating system
- Hardware

This is comparable to CakeML's trusted base (HOL4 + PolyML + OS + hardware) and CompCert's (Coq + OCaml + OS + hardware).

## Project Structure

```
formal/
├── Once/
│   ├── Syntax.agda           -- AST definition
│   ├── Type.agda             -- Type representation
│   ├── IR.agda               -- IR definition (the 12 generators)
│   ├── Semantics.agda        -- Big-step operational semantics
│   │
│   ├── Category/
│   │   ├── Laws.agda         -- Categorical law statements
│   │   └── Proofs.agda       -- Proofs of categorical laws
│   │
│   ├── QTT/
│   │   ├── Quantity.agda     -- Quantity semiring (0, 1, ω)
│   │   ├── Context.agda      -- Quantitative contexts
│   │   └── Linearity.agda    -- Linearity preservation proofs
│   │
│   ├── TypeSystem/
│   │   ├── Typing.agda       -- Typing rules
│   │   ├── Progress.agda     -- Progress theorem
│   │   └── Preservation.agda -- Preservation theorem
│   │
│   └── Backend/
│       ├── C/
│       │   ├── Syntax.agda   -- C AST subset
│       │   ├── Semantics.agda -- C operational semantics
│       │   ├── CodeGen.agda  -- IR → C translation
│       │   └── Correct.agda  -- Correctness proof
│       └── ...               -- Future backends
│
├── Extract/
│   └── Main.agda             -- Extraction configuration
│
└── Once.agda-lib             -- Library definition
```

## Key Definitions (Preview)

### Types

```agda
data Type : Set where
  Unit  : Type
  Void  : Type
  _*_   : Type → Type → Type
  _+_   : Type → Type → Type
  _⇒_   : Type → Type → Type
```

### IR (The 12 Generators)

```agda
data IR : Type → Type → Set where
  -- Category
  id      : IR A A
  _∘_     : IR B C → IR A B → IR A C

  -- Products
  fst     : IR (A * B) A
  snd     : IR (A * B) B
  ⟨_,_⟩   : IR C A → IR C B → IR C (A * B)

  -- Coproducts
  inl     : IR A (A + B)
  inr     : IR B (A + B)
  [_,_]   : IR A C → IR B C → IR (A + B) C

  -- Terminal/Initial
  terminal : IR A Unit
  initial  : IR Void A

  -- Exponential
  curry   : IR (A * B) C → IR A (B ⇒ C)
  apply   : IR ((A ⇒ B) * A) B
```

### Semantics

```agda
⟦_⟧ : Type → Set
⟦ Unit ⟧    = ⊤
⟦ Void ⟧    = ⊥
⟦ A * B ⟧   = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧   = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒ B ⟧   = ⟦ A ⟧ → ⟦ B ⟧

eval : IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval id x            = x
eval (g ∘ f) x       = eval g (eval f x)
eval fst (a , b)     = a
eval snd (a , b)     = b
eval ⟨ f , g ⟩ x     = (eval f x , eval g x)
eval inl a           = inj₁ a
eval inr b           = inj₂ b
eval [ f , g ] (inj₁ a) = eval f a
eval [ f , g ] (inj₂ b) = eval g b
eval terminal _      = tt
eval (curry f) a     = λ b → eval f (a , b)
eval apply (f , a)   = f a
```

### Categorical Laws (Theorems)

```agda
-- Identity laws
id-left  : ∀ {A B} (f : IR A B) → id ∘ f ≡ f
id-right : ∀ {A B} (f : IR A B) → f ∘ id ≡ f

-- Associativity
assoc : ∀ {A B C D} (f : IR C D) (g : IR B C) (h : IR A B) →
        f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h

-- Product laws
fst-pair : ∀ {A B C} (f : IR C A) (g : IR C B) → fst ∘ ⟨ f , g ⟩ ≡ f
snd-pair : ∀ {A B C} (f : IR C A) (g : IR C B) → snd ∘ ⟨ f , g ⟩ ≡ g
pair-unique : ∀ {A B C} (h : IR C (A * B)) → ⟨ fst ∘ h , snd ∘ h ⟩ ≡ h

-- Coproduct laws
case-inl : ∀ {A B C} (f : IR A C) (g : IR B C) → [ f , g ] ∘ inl ≡ f
case-inr : ∀ {A B C} (f : IR A C) (g : IR B C) → [ f , g ] ∘ inr ≡ g
case-unique : ∀ {A B C} (h : IR (A + B) C) → [ h ∘ inl , h ∘ inr ] ≡ h

-- Exponential laws (curry/apply adjunction)
curry-apply : ∀ {A B C} (f : IR (A * B) C) →
              apply ∘ ⟨ curry f ∘ fst , snd ⟩ ≡ f
```

## Estimated Effort

Based on comparable projects:

| Component | Estimated Lines | Effort |
|-----------|----------------|--------|
| Core IR + Semantics | ~300 | 1-2 weeks |
| Categorical laws | ~400 | 2-3 weeks |
| Type system + soundness | ~500 | 3-4 weeks |
| QTT | ~400 | 2-3 weeks |
| C backend + correctness | ~1000 | 6-8 weeks |
| **Total** | **~2600** | **~4 months** |

Compare to:
- CakeML: ~100,000 lines of HOL4 over many years
- CompCert: ~100,000 lines of Coq over many years

Once is ~40x smaller in proof effort due to its simpler design.

## Integration Path

### Phase 1: Standalone Agda Proofs

Write proofs in Agda, manually check they match Haskell implementation.

### Phase 2: Extract Core IR

Extract `IR.agda` and `Semantics.agda` to Haskell. Replace hand-written `Once.IR` module.

### Phase 3: Extract Type Checker

Extract `TypeSystem/*.agda`. Replace hand-written type checker.

### Phase 4: Extract Backend

Extract `Backend/C/*.agda`. Replace hand-written C code generator.

### Phase 5: Retire Unverified Code

At this point, the entire compiler pipeline from IR to C is extracted from verified Agda.

## Dependencies

The Agda formalization will use:
- **agda-stdlib**: Standard library
- **agda-categories**: Category theory (optional, may inline needed parts)

## Relation to Property Tests

The existing QuickCheck properties in the Haskell codebase test the same properties we will prove:

```haskell
-- Current: QuickCheck property
prop_id_left f x = eval (Compose Id f) x === eval f x
```

```agda
-- Future: Agda theorem
id-left : ∀ f → id ∘ f ≡ f
```

The properties are **theorem-shaped by design**. Each QuickCheck property corresponds to an Agda theorem.

## References

- [agda-categories](https://github.com/agda/agda-categories) - Category theory library
- [PLFA](https://plfa.github.io/) - Programming Language Foundations in Agda
- [CakeML](https://cakeml.org/) - Verified ML compiler (HOL4)
- [CompCert](https://compcert.org/) - Verified C compiler (Coq)
