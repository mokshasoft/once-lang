# Architecture Proposal v2: Categorical Formulation

## The Core Insight

A normalizer `N : TermCode' → TermCode'` is correct when:

> **Normal forms are fixpoints of N**

That is: `N ∘ encode t ⟶* encode t` for all NoRedex terms t.

## Categorical Structure

### The Normalizer as Catamorphism

Our normalizer is defined as:
```
N = cata TermF alg
```

where `alg : ⟦TermF⟧ TermCode' → TermCode'` is the algebra.

The catamorphism equation gives us:
```
N ∘ In = alg ∘ fmap TermF N
```

### The Fixpoint Property

For `N ∘ encode t ⟶* encode t` to hold, we need the algebra to "do nothing" on normal forms.

Since `encode t = In ∘ payload` for some payload, the catamorphism unfolds:
```
N ∘ encode t
  = N ∘ In ∘ payload
  ⟶ alg ∘ fmap TermF N ∘ payload
```

By induction, `fmap TermF N ∘ payload ⟶* payload` (sub-terms are fixpoints).

So we need: `alg ∘ payload ⟶* In ∘ payload`

This is the key property:

> **AlgebraPreservesNF**: On normal form payloads, `alg` acts as `In`

## The Single Spec

```agda
record NormalizerSpec (N : Term TermCode' TermCode') : Set where
  field
    alg : Term (⟦ TermF ⟧F TermCode') TermCode'
    is-cata : N ≡ cata TermF alg

    -- The algebra preserves normal forms
    preserves-nf : ∀ {A B} (t : Term A B) → NoRedex t →
                   (alg ∘ out ∘ encode t) ⟶* encode t
```

This is **one property**, not 15.

## Why This Works

The `preserves-nf` property says: when you take an encoded normal form, extract its F-structure with `out`, and apply the algebra, you get back the original encoding.

For our concrete algebra (`normalize-step`), this holds because:

1. **14 handlers are `rebuild-N = In ∘ inj-N`**: These definitionally satisfy `alg ∘ inj-N ∘ payload = In ∘ inj-N ∘ payload`.

2. **handle-comp is conditional**: It checks if operands are `id` and reduces if so. But for NoRedex inputs (which are NotIdStruct by definition), it takes the rebuild branch.

The 15-constructor case analysis is an **implementation detail** of proving `preserves-nf` for our specific algebra.

## Proof Structure

### Correctness/ (General Theory)

```
Correctness/
  ├── NormalizerSpec.agda       -- The single-property spec above
  ├── SpecImpliesFixpoint.agda  -- Generic theorem:
  │                                preserves-nf → fixpoint property
  │                                (structural induction on NoRedex)
  └── ...existing files...
```

### Implementation/ (Concrete Facts)

```
Implementation/
  ├── Normalizer.agda           -- Define alg = normalize-step
  ├── Handlers.agda             -- Define handlers
  ├── PreservesNF.agda          -- Prove: normalize-step preserves NF
  │                                (the 15-case analysis lives here)
  └── SatisfiesSpec.agda        -- Wire up: NormalizerSpec normalize
```

## The 15-Case Analysis

The structural proof that `normalize-step` satisfies `preserves-nf`:

```agda
normalize-step-preserves-nf : ∀ {A B} (t : Term A B) → NoRedex t →
                              (normalize-step ∘ out ∘ encode t) ⟶* encode t
normalize-step-preserves-nf id nr-id = done           -- handle-id = In ∘ inl
normalize-step-preserves-nf fst nr-fst = done         -- handle-fst = In ∘ inr² ∘ inl
normalize-step-preserves-nf (f ∘ g) (nr-comp ...) = handle-comp-rebuild ...
... (15 cases total)
```

14 cases are `done` (definitional). 1 case uses `handle-comp-rebuild`.

This is **internal to Implementation/** - the category theorist only sees `preserves-nf`.

## Summary

| Concept | Categorical View | Implementation View |
|---------|------------------|---------------------|
| Spec | "alg acts as In on NF" | One field: preserves-nf |
| Theorem | "preserves-nf → fixpoint" | Structural induction |
| Proof | (abstract) | 15-case analysis |

The complexity is **hidden** in Implementation/. Correctness/ presents a clean categorical interface.

## Comparison with v1

| Aspect | v1 (15-field spec) | v2 (single property) |
|--------|-------------------|---------------------|
| Spec fields | 15 | 1 |
| Category-theoretic | No (mentions handlers) | Yes (alg ≈ In on NF) |
| Where 15 cases live | Split across spec | Implementation only |
| Conceptual clarity | Medium | High |

## Open Question

Is `out` the right way to extract F-structure from an encoding? We have:
```
encode t = In ∘ payload
out = ?
```

Options:
1. Define `out` as the inverse of `In` (requires Out from CCC)
2. Work directly with `payload` by pattern matching on `t`
3. Use the catamorphism directly without explicit `out`

The cleanest might be option 3: define preserves-nf in terms of the encoding structure directly, avoiding an explicit `out` combinator.
