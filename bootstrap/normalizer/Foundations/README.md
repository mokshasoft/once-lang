# Normalizer Foundations

Mathematical foundations for the bootstrap normalizer verification.

## Modules

| Module | Purpose |
|--------|---------|
| `Types.agda` | Minimal prelude, Ty, Func, decidable equality |
| `MinimalCCC.agda` | Term syntax, reduction rules, confluence, termination, WellFormed |
| `Encoding.agda` | Term encoding ⌜_⌝, injectivity proofs, Maybe as ⊤ ⊎ A |
| `Fixpoint.agda` | NormalizerSpec record, fixpoint theorems |
| `Progress.agda` | Progress lemmas for reduction |
| `Termination.agda` | Termination proofs for well-formed terms |

## Key Results

From these modules, we have:

- **Confluence**: `t ⟶* u → t ⟶* v → ∃ w. (u ⟶* w) × (v ⟶* w)`
- **Termination**: `WellFormed t → Terminates t`
- **Unique Normal Forms**: `t ⟶* u → t ⟶* v → NF u → NF v → u ≡ v`
- **Encoding Well-Formed**: `encode t` is always well-formed
- **Encoding is NF**: `encode t` is always in normal form

## NormalizerSpec

The key interface a verified normalizer must satisfy:

```agda
record NormalizerSpec : Set where
  field
    N : ConcreteNormalizer
    N-wf : WellFormed N
    N-fixpoint : IsFixpoint'' N
    produces-encoding : ∀ t → Σ u. (N ∘ encode t ⟶* encode u) × NF u
    correct-reduction : ∀ t {u} → (N ∘ encode t ⟶* encode u) → t ⟶* u
```

Once proven, `concrete-fixpoint-correctness` gives us the main theorem.
