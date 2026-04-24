# Plans

This folder tracks active and recent planning. Completed plans with no
unfinished downstream are archived in git history — see D045, D044, etc.
in `docs/compiler/decision-log.md` for durable records of landed work.

## Active Plan Tree

```
0-ocp3 (active root)
│
├── 0.2-cata-postulates (completed — retained for 0.2.4 context)
│   └── 0.2.2-cata-remaining (completed)
│       └── 0.2.3-positive-invariants (completed)
│           └── 0.2.4-categorical-layer-0 ← ACTIVE (compiler-side Layer 0 integration)
│               └── 0.2.4.1-sigop-framework (design — unblocks Layer 0 end-to-end)
│
├── 0.3-frontend-verification-gaps (completed 2026-04-19 — retained for 0.4 context)
│   └── 0.4-frontend-completeness-and-bridges (planning)
│       └── 0.4.2-end-to-end-connector (planning)
│
└── 0.6-user-polymorphism-and-strict-parser (planning — Section A landed 2026-04-20)
    ├── 0.6.1-phase-c-design (design)
    └── 0.7-parser-strictness-relational (planning)
```

## Status Summary

| Plan | Status | Notes |
|---|---|---|
| `0-ocp3` | active | Root proposal |
| `0.2-cata-postulates` | completed | Kept for 0.2.4 context |
| `0.2.2-cata-remaining` | completed | Kept for 0.2.4 context |
| `0.2.3-positive-invariants` | completed | Kept for 0.2.4 context |
| `0.2.4-categorical-layer-0` | active | Compiler Layer 0 integration |
| `0.2.4.1-sigop-framework` | design | SigOp framework for effectful ops; unblocks Layer 0's end-to-end (exit, print, readline) |
| `0.3-frontend-verification-gaps` | completed | Kept for 0.4 context |
| `0.4-frontend-completeness-and-bridges` | planning | T1–T4 (G2 completeness, parse→pretty, grammar conformance, surface-semantics bridges) |
| `0.4.2-end-to-end-connector` | planning | Depends on 0.4 — composed surface→machine theorem |
| `0.6-user-polymorphism-and-strict-parser` | planning | Section A landed; B/C in progress via children |
| `0.6.1-phase-c-design` | design | Phase C design + classifier migration |
| `0.7-parser-strictness-relational` | planning | Relational parser + proofs |

## Recently Closed (in git history + decision log)

| Plan | Closed | Reference |
|---|---|---|
| `0.1` / `0.1.2` / `0.1.3` / `0.1.4` (normalizer chain) | 2025-03-24 | initial bootstrap |
| `0.2.5-type-polytype-split` | 2026-04-17 | closed via direct landing |
| `0.2.6-usage-indexed-expr` | 2026-04-17 | closed via direct landing |
| `0.6.2-polymorphic-schema-instantiation` | 2026-04-23 | **D045** — two-phase elaborator, 0 pragmas, 0 postulates |
| `0.5-ir-extension-hygiene` | 2026-04-23 | Phase A/B (view catch-alls, `≟IRHead`) landed; Phase C superseded by 0.5.1 |
| `0.5.1-kind-unified-arrow` | 2026-04-23 | **D046** — unified `Eff` + `_⇒[_]_`; `applyEff` + placeholder postulate eliminated |
| `0.8-dot-sugar-for-compose` | 2026-04-21 | dot-sugar lands as `compose` |

## Current Focus

- **`0.2.4-categorical-layer-0`** — compiler-side Layer 0 integration (MAlonzo extraction, Layer 0 test harness). Paused since 2025-04-14; backend track resumes here.
- **`0.4` / `0.4.2`** — frontend completeness closure + end-to-end composed theorem. Natural follow-on from recently-landed `0.6.2`.

## Notes on Layout

**Completed plans kept for context**: a plan is retained if it is finished but has unfinished downstream children (so the unfinished children's context remains readable). `0.2` / `0.2.2` / `0.2.3` are kept because `0.2.4` is still active; `0.3` is kept because `0.4` depends on it.

**Completed leaf plans are removed** once their durable record is in `docs/compiler/decision-log.md` or equivalent. Git history preserves the plan file.

## Numbering Scheme

- **Branches from same parent**: new first-level number (0.1, 0.2, 0.3)
- **Linear chain**: increment last number (0.1 → 0.1.2 → 0.1.3)
- **Branch mid-chain**: add new level (0.1.3.1, 0.1.3.2)

## File Format

Each plan has a YAML header:
```yaml
---
parent: <parent-plan-id> | null
status: active | planning | design | completed | blocked | abandoned
date: YYYY-MM-DD
closed: YYYY-MM-DD  # optional — when status became completed
---
```

## Related Documents

- `docs/compiler/decision-log.md` — durable record of landed architectural decisions
- `docs/proposals/OCP-0003-total-productive-ir.md` — Root proposal
- `docs/proposals/OCP-0004-zero-trust-verification.md` — Bootstrap tower
- `docs/design/ir-stack-layout.md` — Stack layout and categorical layers
