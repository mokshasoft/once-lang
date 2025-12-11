# What Is Proven

Current formal verification status for the Once compiler.

## Summary

The Once compiler is **partially verified** in Agda. The core semantics and elaboration from surface syntax to IR are proven correct. Code generation and optimization verification are in progress.

| Component | Status | Notes |
|-----------|--------|-------|
| Core IR semantics | ✓ Proven | 12 generators, denotational semantics |
| Categorical laws | ✓ Proven | 17 CCC law proofs |
| Type soundness | ✓ Proven | Progress, preservation, canonical forms |
| Elaboration | ✓ Proven | Surface syntax → IR preserves semantics |
| Optimization | Not started | Each rewrite rule needs proof |
| C code generation | Not started | IR → C semantics preservation |
| QTT enforcement | Not started | Linear resource tracking |

## What Is Proven

### Core IR Semantics (Phase V1)

The 12 categorical generators and their denotational semantics are defined in Agda:

- `Type.agda` - Types: Unit, Void, products, sums, functions
- `IR.agda` - The 12 generators as a GADT
- `Semantics.agda` - Evaluation function `eval : IR A B → ⟦A⟧ → ⟦B⟧`

### Categorical Laws (Phase V2)

17 theorems proving the IR satisfies cartesian closed category laws:

| Law | Theorem |
|-----|---------|
| Left identity | `eval (id ∘ f) x ≡ eval f x` |
| Right identity | `eval (f ∘ id) x ≡ eval f x` |
| Associativity | `eval ((f ∘ g) ∘ h) x ≡ eval (f ∘ (g ∘ h)) x` |
| Fst-pair | `eval (fst ∘ ⟨f,g⟩) x ≡ eval f x` |
| Snd-pair | `eval (snd ∘ ⟨f,g⟩) x ≡ eval g x` |
| Pair-eta | `eval ⟨fst,snd⟩ x ≡ x` |
| Case-inl | `eval ([f,g] ∘ inl) x ≡ eval f x` |
| Case-inr | `eval ([f,g] ∘ inr) x ≡ eval g x` |
| Case-eta | `eval [inl,inr] x ≡ x` |
| Curry-apply | `eval (apply ∘ ⟨curry f ∘ fst, snd⟩) x ≡ eval f x` |
| ... | (and 7 more) |

### Type Soundness (Phase V3)

- **Progress**: Well-typed terms evaluate (don't get stuck)
- **Preservation**: Evaluation preserves types
- **Canonical forms**: Values have expected structure
- **Compositionality**: `eval (g ∘ f) x ≡ eval g (eval f x)`

### Elaboration Correctness (Phase V4)

The main theorem:

```
elaborate-correct : ∀ ρ e. evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)
```

This proves that elaborating surface syntax (with lambdas and variables) to point-free IR preserves semantics. The elaboration handles:

- Lambda elimination via currying
- Variable resolution via projection chains
- Case expression distribution

## What Is Postulated

| Postulate | Location | Justification |
|-----------|----------|---------------|
| `extensionality` | `Once/Surface/Correct.agda` | Function extensionality |

Function extensionality is used only in proof terms, which are erased during extraction. The postulate never executes at runtime.

## Known Limitations

### Fixed Point Semantics (Fix, fold, unfold)

The current formalization of recursive types (`Fix F`) has a significant limitation. The semantics use a simple newtype wrapper:

```agda
⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧   -- Just wraps ⟦ F ⟧
```

This models `Fix F ≅ F`, but the correct equation should be:

```
Fix F ≅ F[Fix F / X]   -- F with recursive occurrences substituted
```

For example, `Nat = Fix (Unit + X)` should satisfy:
- `⟦ Nat ⟧ ≅ ⟦ Unit + Nat ⟧` = `⊤ ⊎ ⟦ Nat ⟧`

But the current model gives:
- `⟦ Nat ⟧ = ⟦Fix⟧ ⟦ Unit + X ⟧` where `X` is uninterpreted

**Impact**: The proofs `eval-fold-unfold` and `eval-unfold-fold` are trivially `refl` because `wrap`/`unwrap` are inverses of a single-layer newtype. This proves the wrapper isomorphism, not the recursive fixed point property.

**What's missing**: Type-level substitution. The `F` in `Fix F` should be a *functor* (a type with a hole), not a closed type.

See [Future Work](#future-work-fixed-point-semantics) for options to address this.

## Trusted Computing Base

The following must be trusted without proof:

1. **Agda type checker** - Verifies the proofs
2. **MAlonzo extraction** - Translates Agda to Haskell
3. **GHC** - Compiles extracted Haskell
4. **C compiler** - Compiles generated C code
5. **Parser** - Not verified (megaparsec-based)
6. **CLI** - Not verified (optparse-applicative)

This is comparable to CakeML (HOL4 + PolyML + OS) and CompCert (Coq + OCaml + OS).

## Remaining Work

| Phase | Description | Estimated Effort |
|-------|-------------|------------------|
| V5 | Optimization correctness | 1-2 weeks |
| V6 | C backend semantics | 2-3 weeks |
| V7 | Code generation correctness | 4-6 weeks |
| V8 | QTT verification | 2-3 weeks |
| V9 | End-to-end theorem | 1 week |
| V10 | Extraction integration | 2-3 weeks |

## Proof Files

All proofs are in the `formal/` directory:

```
formal/Once/
├── Type.agda              # Type definitions
├── IR.agda                # IR (12 generators)
├── Semantics.agda         # Denotational semantics
├── Category/
│   └── Laws.agda          # 17 CCC law proofs
├── TypeSystem/
│   ├── Typing.agda        # Typing rules
│   └── Soundness.agda     # Progress, preservation
└── Surface/
    ├── Syntax.agda        # Surface expression type
    ├── Elaborate.agda     # Elaboration function
    └── Correct.agda       # Elaboration correctness
```

## Future Work: Fixed Point Semantics

The current `Fix` formalization needs to be replaced with proper fixed point semantics. Here are the options:

### Option 1: Universe of Strictly Positive Functors

Define a universe of type constructors that are guaranteed strictly positive, then interpret `Fix` as the least fixed point.

```agda
data Functor : Set where
  K    : Type → Functor           -- Constant functor
  Id   : Functor                  -- Identity (the recursive position)
  _⊕_  : Functor → Functor → Functor  -- Sum
  _⊗_  : Functor → Functor → Functor  -- Product

⟦_⟧F : Functor → Set → Set
⟦ K A ⟧F X = ⟦ A ⟧
⟦ Id ⟧F X = X
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X ⊎ ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X × ⟦ G ⟧F X

data μ (F : Functor) : Set where
  ⟨_⟩ : ⟦ F ⟧F (μ F) → μ F
```

**Pros**:
- Clean categorical semantics
- Automatic positivity checking
- Can derive `fmap` generically

**Cons**:
- Limited to polynomial functors (no function types in recursive positions)
- Requires changing `Type` representation

### Option 2: Sized Types

Use Agda's sized types to ensure termination while allowing general recursion.

```agda
{-# OPTIONS --sized-types #-}

data μ (F : Set → Set) (i : Size) : Set where
  ⟨_⟩ : {j : Size< i} → F (μ F j) → μ F i
```

**Pros**:
- More expressive than polynomial functors
- Well-supported in Agda
- Allows coinductive types too (ν for greatest fixed points)

**Cons**:
- Sized types can be tricky to work with
- Less portable (Agda-specific feature)
- Proofs about sized types can be complex

### Option 3: Well-Founded Recursion

Use accessibility predicates to justify termination.

```agda
data μ (F : Set → Set) : Set where
  ⟨_⟩ : F (μ F) → μ F

-- Prove termination via well-founded induction
cata : (F (μ F) → A) → μ F → A
cata alg ⟨ x ⟩ = alg (fmap (cata alg) x)  -- needs termination proof
```

**Pros**:
- Most general approach
- Standard mathematical treatment

**Cons**:
- Requires explicit termination proofs
- Needs `fmap` for each functor
- More proof burden

### Option 4: Quotient Inductive-Inductive Types (QIITs)

Use Agda's experimental QIIT support for a higher-inductive approach.

**Pros**:
- Very expressive
- Can handle higher-order cases

**Cons**:
- Experimental feature
- Complex to use
- May not be stable across Agda versions

### Recommendation

**Option 1 (Universe of Functors)** is recommended for Once because:

1. Once's recursive types are polynomial (sums and products only)
2. The `Type` syntax already restricts what can appear in `Fix`
3. It gives the cleanest categorical semantics
4. Proofs are straightforward once the universe is set up

The implementation would:
1. Add a `Functor` type to represent strictly positive type constructors
2. Change `Fix : Type → Type` to `Fix : Functor → Type`
3. Define `⟦_⟧F` interpretation with explicit recursive position
4. Prove `fold`/`unfold` form a proper isomorphism `μF ≅ F(μF)`

## See Also

- [Formal Verification Plan](../compiler/formal-verification-plan.md) - Detailed verification roadmap
- [Verification Strategy](../design/formal/verification-strategy.md) - Why Agda, architecture decisions
- [Lessons Learned](lessons-learned.md) - Practical Agda lessons from this formalization
