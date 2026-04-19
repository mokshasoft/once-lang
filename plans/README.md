# Plans

This folder tracks the planning history and dependencies between design decisions.

## Plan Tree

```
0-ocp3 (root)
│
├── 0.1-encode-betanf
│   └── 0.1.2-is-id-proofs
│       └── 0.1.3-normalizer-restructure
│           └── 0.1.4-cctower
│
├── 0.2-cata-postulates
│   └── 0.2.2-cata-remaining
│       └── 0.2.3-positive-invariants
│           └── 0.2.4-categorical-layer-0  ← ACTIVE (resume next)
│               └── 0.2.5-type-polytype-split  (completed 2026-04-17)
│                   └── 0.2.6-usage-indexed-expr  (completed 2026-04-17)
│
└── 0.3-frontend-verification-gaps  (completed 2026-04-19)
```

**Current focus**: resume `0.2.4-categorical-layer-0` — compiler-side
Layer 0 integration (MAlonzo extraction, Layer 0 test harness). The
frontend verification track (0.2.5 / 0.2.6 / 0.3) has landed; the
backend track picks up where it paused on 2026-04-14.

## Numbering Scheme

- **Branches from same parent**: new first-level number (0.1, 0.2, 0.3)
- **Linear chain**: increment last number (0.1 → 0.1.2 → 0.1.3)
- **Branch mid-chain**: add new level (0.1.3.1, 0.1.3.2)

## File Format

Each plan has a YAML header:
```yaml
---
parent: 0.1.3-normalizer-restructure
status: active | completed | blocked | abandoned
date: 2025-04-14
---
```

## Tracks

- **0.1.x (Normalizer)**: Proving the bootstrap normalizer correct
- **0.2.x (Implementation)**: Stack-allocated compiler, layer by layer

## Related Documents

- `docs/proposals/OCP-0003-total-productive-ir.md` - Root proposal
- `docs/proposals/OCP-0004-zero-trust-verification.md` - Bootstrap tower
- `docs/design/ir-stack-layout.md` - Stack layout and categorical layers
