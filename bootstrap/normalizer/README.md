# Bootstrap Normalizers

This directory contains the normalizer implementations for each level of the bootstrap tower.

## Structure

```
normalizer/
├── Agda/                 # Agda proofs (reference implementation)
│   ├── Foundations/      # Mathematical foundations
│   │   ├── Types.agda
│   │   ├── MinimalCCC.agda
│   │   ├── Encoding.agda
│   │   └── ...
│   └── Level0/           # Full CCC normalizer (products, coproducts, exponentials, μ)
│       └── Normalizer.agda
│
└── Once/                 # Once proofs (self-hosted verification)
    ├── Foundations/
    └── Level0/
```

## Level 0 IR

The complete CCC with:
- Identity and composition: `id`, `∘`
- Products: `fst`, `snd`, `⟨,⟩`
- Coproducts: `inl`, `inr`, `[,]`
- Exponentials: `curry`, `apply`
- Initial/terminal: `initial`, `terminal`
- Inductive types: `In`, `Out`, `cata`

Verified by fixpoint + mathematical foundations (confluence, termination, unique normal forms).

## Foundations

The `Foundations/` directory contains the mathematical foundations:

- `Types.agda` — Minimal prelude, Ty, Func, decidable equality
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
