# What Is Proven

Current formal verification status for the Once compiler.

## Summary

The Once compiler is **partially verified** in Agda. The core semantics and elaboration from surface syntax to IR are proven correct. Code generation and optimization verification are in progress.

| Component | Status | Notes |
|-----------|--------|-------|
| Core IR semantics | ✓ Proven | 13 generators (incl. arr for effects), denotational semantics |
| Categorical laws | ✓ Proven | 18 CCC law proofs (incl. arr identity) |
| Type soundness | ✓ Proven | Progress, preservation, canonical forms |
| Elaboration | ✓ Proven | Surface syntax → IR preserves semantics |
| x86-64 code gen | ✓ Mostly proven | 12 of 14 generators; curry/apply postulated |
| Optimization | Not started | Each rewrite rule needs proof |
| C code generation | Not started | IR → C semantics preservation |
| QTT enforcement | Not started | Linear resource tracking |

## What Is Proven

### Core IR Semantics (Phase V1)

The 13 categorical generators and their denotational semantics are defined in Agda:

- `Type.agda` - Types: Unit, Void, products, sums, functions, Eff (effects)
- `IR.agda` - The 13 generators as a GADT (including `arr` for effect lifting)
- `Semantics.agda` - Evaluation function `eval : IR A B → ⟦A⟧ → ⟦B⟧`

Note: The effect type `Eff A B` has the same semantics as `A ⇒ B` (pure functions). This is intentional - effects are a compile-time discipline, not a runtime distinction. See D032 in the decision log.

### Categorical Laws (Phase V2)

18 theorems proving the IR satisfies cartesian closed category laws (including arrow law for `arr`):

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
| Arr-identity | `eval arr f ≡ f` (D032: arr is semantically identity) |
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

### x86-64 Code Generation Correctness (Phase V7)

The main theorem:

```
codegen-x86-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 ir) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (eval ir x))
```

This proves that executing compiled x86-64 code on an encoded input produces the encoded semantic result. The proof covers 12 of 14 IR generators:

| Generator | Status | Generated Code |
|-----------|--------|----------------|
| `id` | ✓ Proven | `mov rax, rdi` |
| `compose` | ✓ Proven | `f ++ mov rdi, rax ++ g` |
| `fst` | ✓ Proven | `mov rax, [rdi]` |
| `snd` | ✓ Proven | `mov rax, [rdi+8]` |
| `pair` | ✓ Proven | Stack alloc, compute both |
| `inl` | ✓ Proven | Stack alloc, tag=0 |
| `inr` | ✓ Proven | Stack alloc, tag=1 |
| `case` | ✓ Proven | Branch on tag |
| `terminal` | ✓ Proven | `mov rax, 0` |
| `initial` | ✓ Proven | Absurd (no Void inputs) |
| `fold` | ✓ Proven | `mov rax, rdi` |
| `unfold` | ✓ Proven | `mov rax, rdi` |
| `arr` | ✓ Proven | `mov rax, rdi` |
| `curry` | Postulated | Closure creation |
| `apply` | Postulated | Indirect call |

The proofs use a layered approach:
1. **Encoding axioms**: Relate semantic values to machine words
2. **Execution helpers**: Capture single/multi-instruction execution properties
3. **Per-generator proofs**: Compose helpers to prove each generator correct
4. **Main theorem**: Case analysis using all per-generator proofs

Remaining work: `curry` and `apply` require modeling closure allocation and indirect calls.

## Assumptions and Postulates

All assumptions are centralized in `formal/Once/Postulates.agda`. This is the **single source of truth** for what is assumed without proof.

### Detecting Assumptions

To find all postulates in the formalization:

```bash
# Check if a file uses postulates (--safe fails if postulates are used)
agda --safe formal/Once/Semantics.agda

# Find all postulate declarations
grep -r "postulate" formal/

# List modules that import from Postulates.agda
grep -r "import Once.Postulates" formal/
```

### P1: Function Extensionality

| Property | Value |
|----------|-------|
| **Type** | `∀ {A B} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g` |
| **Location** | `Once/Postulates.agda` |
| **Needed by** | `Once/Surface/Correct.agda` (elaboration correctness for lambdas) |
| **Runtime effect** | None (erased during extraction) |

**Justification**: Function extensionality is consistent with Agda's type theory and holds in most models (setoid model, cubical type theory). It's a standard assumption in formalized mathematics.

### P2: x86-64 Encoding Axioms

| Property | Value |
|----------|-------|
| **Type** | `encode-*` family of postulates |
| **Location** | `Once/Backend/X86/Correct.agda` |
| **Needed by** | x86-64 code generation correctness proofs |
| **Runtime effect** | None (proof-only) |

These axioms relate semantic values to machine words:
- `encode-pair-fst/snd`: Reading from encoded pairs
- `encode-inl/inr-tag/val`: Reading from encoded sums
- `encode-*-construct`: Building encoded values from memory layouts
- `encode-fix-wrap/unwrap`: Fixed point encoding identity
- `encode-arr-identity`: Effect type encoding identity

**Justification**: These capture the intended memory layout semantics. A full formalization would model the heap explicitly and prove these as lemmas.

### P3: x86-64 Execution Helpers

| Property | Value |
|----------|-------|
| **Type** | `run-*` family of postulates |
| **Location** | `Once/Backend/X86/Correct.agda` |
| **Needed by** | x86-64 code generation correctness proofs |
| **Runtime effect** | None (proof-only) |

These capture execution properties:
- `run-single-mov*`: Single mov instruction execution
- `run-inl-seq`, `run-inr-seq`: Sum construction sequences
- `run-pair-seq`: Pair construction sequence
- `run-case-inl`, `run-case-inr`: Case branching execution
- `run-seq-compose`: Sequential composition execution
- `run-generator`: General generator execution

**Justification**: These can be proven from the operational semantics in `Semantics.agda`. The layered approach separates "what the machine does" from "how we compose proofs".

### P4: Closure Correctness (Future Work)

| Property | Value |
|----------|-------|
| **Type** | `curry-correct`, `apply-correct` |
| **Location** | `Once/Backend/X86/Correct.agda` (inline) |
| **Needed by** | Main theorem for `curry` and `apply` cases |
| **Runtime effect** | None (proof-only) |

**Justification**: Closure handling requires modeling allocation, environment capture, and indirect calls. Marked as future work.

### S1: Fixed Point Semantics (Semantic Gap)

This is **not a postulate** but a known limitation in the semantic model. The current `⟦ Fix F ⟧` interpretation uses a newtype wrapper rather than true recursive substitution. See [Known Limitations](#known-limitations) for details.

| Property | Value |
|----------|-------|
| **Type** | Semantic gap (not an axiom) |
| **Location** | `Once/Semantics.agda` |
| **Affected proofs** | `eval-fold-unfold`, `eval-unfold-fold` (trivially `refl`) |
| **Runtime effect** | None (operational semantics are correct) |

### Guidelines for Adding Assumptions

When adding a postulate or discovering a semantic gap:

1. **Centralize**: Add it to `Once/Postulates.agda` with full documentation
2. **Identify**: Label it (P2, P3, ... for postulates; S2, S3, ... for semantic gaps)
3. **Document**: Explain what is assumed and why it's needed
4. **Justify**: Why we believe this is sound
5. **Impact**: What would break if it's wrong
6. **Update**: Add it to this document

The goal is **zero hidden assumptions**. Anyone auditing the formalization should be able to find every assumption by:
1. Reading `Once/Postulates.agda`
2. Running `agda --safe` on files that should be postulate-free
3. Reading the "Known Limitations" section of this document

## Known Limitations

### Fixed Point Semantics (Fix, fold, unfold) — Semantic Gap S1

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

| Phase | Description | Status |
|-------|-------------|--------|
| V5 | Optimization correctness | Not started |
| V6 | x86-64 backend semantics | ✓ Done |
| V7 | x86-64 code generation correctness | ✓ Mostly done (curry/apply pending) |
| V8 | QTT verification | Not started |
| V9 | End-to-end theorem | Not started |
| V10 | Extraction integration | Not started |
| - | C backend (optional) | Not started |

## Proof Files

All proofs are in the `formal/` directory:

```
formal/Once/
├── Postulates.agda        # ★ CENTRAL REGISTRY OF ALL ASSUMPTIONS ★
├── Type.agda              # Type definitions
├── IR.agda                # IR (13 generators incl. arr)
├── Semantics.agda         # Denotational semantics (includes S1 semantic gap)
├── Category/
│   └── Laws.agda          # 18 CCC law proofs
├── TypeSystem/
│   ├── Typing.agda        # Typing rules
│   └── Soundness.agda     # Progress, preservation
├── Surface/
│   ├── Syntax.agda        # Surface expression type
│   ├── Elaborate.agda     # Elaboration function
│   └── Correct.agda       # Elaboration correctness (imports P1)
└── Backend/
    └── X86/
        ├── Syntax.agda    # x86-64 instruction AST
        ├── Semantics.agda # x86-64 operational semantics
        ├── CodeGen.agda   # IR → x86-64 compilation
        └── Correct.agda   # Code gen correctness (imports P2-P4)
```

**Important**: `Postulates.agda` is the authoritative source for core assumptions. Backend-specific postulates (P2-P4) are in `Backend/X86/Correct.agda`.

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
