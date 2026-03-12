# Level 1 Normalizer

**Status**: Not yet implemented

## IR Operations

Level 0 operations plus:
- `curry : Term (A × B) C → Term A (B ⇒ C)`
- `apply : Term ((A ⇒ B) × A) B`

## Additional Reduction Rules

```
apply ∘ ⟨curry f, x⟩  ⟶  f ∘ ⟨id, x⟩   (curry-β)
curry (apply ∘ ⟨f ∘ fst, snd⟩)  ⟶  f   (curry-η)
```

## Verification

Verified by:
1. Level 0 normalizer checks well-formedness of encoding
2. Own fixpoint property proves correctness

## Dependencies

- Level 0 normalizer must be complete first
- Encoding must be extended for curry/apply
