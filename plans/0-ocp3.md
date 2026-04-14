---
parent: null
status: active
date: 2025-03-20
---

# OCP-0003: Total/Productive IR

This is the root plan. The full proposal is at `docs/proposals/OCP-0003-total-productive-ir.md`.

## Summary

OCP-0003 defines the Once IR with:
- **Categorical primitives**: Cata, Para, Ana, Apo (semantic foundation)
- **Fusions**: Hylo and other μ-anchored optimizations
- **Layered structure**: semantic correctness from categorical layer, optimization from fusion layer

## Categorical Layers

| Layer | Name | Morphisms |
|-------|------|-----------|
| 0 | Category | `id`, `∘` |
| 1 | Products | `⟨_,_⟩`, `fst`, `snd` |
| 2 | Coproducts | `inl`, `inr`, `[_,_]` |
| 3 | Terminal/Initial | `terminal`, `initial` |
| 4 | Exponentials | `curry`, `apply` |
| 5 | Initial Algebras | `In`, `cata` |
| 6 | Final Coalgebras | `Out`, `ana` |

## Child Plans

### Normalizer Track (0.1.x)
Proving the bootstrap normalizer correct using the OCP-0003 IR.

### Implementation Track (0.2.x)
Implementing the stack-allocated compiler for the OCP-0003 IR.

## Key Documents

- `docs/proposals/OCP-0003-total-productive-ir.md` - Full proposal
- `docs/proposals/OCP-0004-zero-trust-verification.md` - Bootstrap tower
- `docs/design/ir-stack-layout.md` - Stack layout design
