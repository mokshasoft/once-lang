# Level 2 Normalizer

**Status**: Not yet implemented

This is the **OCP-0003 IR** — the complete Once intermediate representation.

## IR Operations

Level 1 operations plus:
- `ν F` (greatest fixpoint / coinductive types)
- `Out : νF → F(νF)` (coalgebra structure)
- `ana : (A → F A) → A → νF` (anamorphism)
- Guardedness checking for productivity

## Additional Reduction Rules

```
Out ∘ ana coalg  ⟶  fmap F (ana coalg) ∘ coalg   (ana-β)
```

Plus guardedness enforcement for `ana`.

## Verification

Verified by:
1. Level 1 normalizer checks well-formedness
2. Own fixpoint property proves correctness

## Dependencies

- Level 0 and Level 1 normalizers must be complete
- Encoding must be extended for ana/Out/ν
- Guardedness checking must be implemented
