# Bootstrap Normalizers

This directory contains the normalizer implementations for each level of the bootstrap tower.

## Structure

```
normalizer/
├── Level0/           # Minimal CCC normalizer
│   └── Normalizer.agda
├── Level1/           # + Exponentials (curry/apply)
│   └── Normalizer.agda
└── Level2/           # + Recursion schemes (ana/Out) = OCP-0003 IR
    └── Normalizer.agda
```

## The Bootstrap Tower

Each level builds on the previous:

| Level | IR | Verified By |
|-------|-----|-------------|
| **Level 0** | id, ∘, fst, snd, ⟨,⟩, inl, inr, [,], terminal, In, cata | Fixpoint + Math |
| **Level 1** | Level 0 + curry, apply | Level 0 normalizer + fixpoint |
| **Level 2** | Level 1 + ana, Out, guardedness | Level 1 normalizer + fixpoint |

## Shared Foundations

The normalizers depend on shared modules in `../spec/`:

- `Types.agda` — Ty, Func, decidable equality
- `MinimalCCC.agda` — Term, reduction, confluence, termination
- `Encoding.agda` — Term encoding, injectivity proofs
- `Fixpoint.agda` — NormalizerSpec, fixpoint theorems

## Verification Approach

Each normalizer must satisfy `NormalizerSpec` from `Fixpoint.agda`:

```agda
record NormalizerSpec : Set where
  field
    N : ConcreteNormalizer
    N-wf : WellFormed N
    N-fixpoint : IsFixpoint'' N
    produces-encoding : ∀ t → Σ u. (N ∘ encode t ⟶* encode u) × NF u
    correct-reduction : ∀ t {u} → (N ∘ encode t ⟶* encode u) → t ⟶* u
```

Once proven, `concrete-fixpoint-correctness` guarantees the normalizer is correct.
