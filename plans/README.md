# Plans

This folder tracks active and recent planning. Completed plans with no
unfinished downstream are archived in git history — see D045, D044, etc.
in `docs/compiler/decision-log.md` for durable records of landed work.

## Active Plan Tree

```
0-ocp3 (active root)
│
├── 0.9-exhaustive-semantics (Phases A-F partial — bug-hiding class closed, see D049; ~85-site discipline backlog remains, error promotion deferred)
│
├── 0.2-cata-postulates (completed — retained for 0.2.4 context)
│   └── 0.2.2-cata-remaining (completed)
│       └── 0.2.3-positive-invariants (completed)
│           └── 0.2.4-categorical-layer-0 ← ACTIVE (compiler-side Layer 0 integration)
│               ├── 0.2.4.1-sigop-framework (design — unblocks Layer 0 end-to-end)
│               ├── 0.2.4.2-closure-codegen-fix (design — partly superseded by 0.2.4.3 D1)
│               ├── 0.2.4.3-slot-model-alignment (active — no-frame model across spec / abstract trace / target trace)
│               ├── 0.2.4.4-closure-pointer-pin (active — close the closure[1] hiding place at the spec level)
│               ├── 0.2.4.5-allocmode-semantic-clarification (active, re-scoped — drop AllocMode; IR destination passing; Allocator sum type)
│               └── 0.2.4.6-place-pass (design — static analysis that decides destinations + lifetimes; subsumes Once.Escape)
│
├── 0.3-frontend-verification-gaps (completed 2026-04-19 — retained for 0.4 context)
│   └── 0.4-frontend-completeness-and-bridges (planning)
│       ├── 0.4-T3-pipeline-composition (T3 partial — Verified.Compile per-stage decomposition landed)
│       └── 0.4.2-end-to-end-connector (planning)
│
├── 0.6-user-polymorphism-and-strict-parser (planning — Section A landed 2026-04-20)
│   ├── 0.6.1-phase-c-design (design)
│   └── 0.7-parser-strictness-relational (planning)
│
└── 0.11-parameterized-trusted-base (design — `--safe` proof modules + TrustedBase parameter; orthogonal to 0.10)
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
| `0.2.4.2-closure-codegen-fix` | design (partly superseded) | B1/B2/B3 catalog kept for context; D2 (per-thunk SysV frame) replaced by 0.2.4.3 D1 (no frames) |
| `0.2.4.3-slot-model-alignment` | active | No-frame model across the three layers (SM*/WF spec, abstract trace, target trace). ApplyWF spec landed (`3760c10b`); IRToTrace.curry frontier-threading + target prologue cleanup pending. |
| `0.2.4.4-closure-pointer-pin` | active | Close the closure[1] hiding place. `body-label` field + `encode-decode-code-addr` bijection. Stage 1 (spec pin) in progress; Stage 2 (couple `instr-call-closure` to `closure[1]`) deferred. |
| `0.2.4.5-allocmode-semantic-clarification` | active (re-scoped 2026-05-05) | Drop `AllocMode` entirely. Introduce `Allocator = Stack \| Dynamic` sum type. Rename `ValueLocation` constructors to mirror Allocator (`InReg` / `AtStack` / `AtDynamic`). Two input registers (`Input1`, `Input2`) — apply doesn't pack. `IsPrimitive` collapses to `FitsInReg`; Unit erased; Str/Buffer reclassified as compound. IRs take destinations, don't choose. No `free` IR — alloc/free are SigOps. |
| `0.2.4.6-place-pass` | design | Static analysis pass (`Once.Place`) that walks IR, decides each value's destination + lifetime, inserts alloc/free SigOps for Dynamic values. Subsumes (or consumes) `Once.Escape`. Layer 0 Place is trivial (next-slot bump-allocator). |
| `0.3-frontend-verification-gaps` | completed | Kept for 0.4 context |
| `0.4-frontend-completeness-and-bridges` | planning | T1–T4 (G2 completeness, parse→pretty, grammar conformance, surface-semantics bridges) |
| `0.4-T3-pipeline-composition` | T3 partial | `Verified.Compile.correct` decomposed into named per-stage postulates (commit `4dd740cc`). Discharge of `module-to-asm-correct` chains through 0.10 + 0.2.4.3 + 0.2.4.4. |
| `0.4.2-end-to-end-connector` | planning | Depends on 0.4 — composed surface→machine theorem |
| `0.6-user-polymorphism-and-strict-parser` | planning | Section A landed; B/C in progress via children |
| `0.6.1-phase-c-design` | design | Phase C design + classifier migration |
| `0.7-parser-strictness-relational` | planning | Relational parser + proofs |
| `0.9-exhaustive-semantics` | partial | `--exact-split` enabled; bug-hiding class closed in `exec-x86` (Phase B) and `instr-consumed-slots` (Phase D). 17 CATCHALLs in DirectSim route to named postulates. ~85 safe-class warnings remain as discipline backlog. **D049** in decision log. Error promotion deferred until backlog clears. |
| `0.11-parameterized-trusted-base` | design | Make all proof modules `--safe` by parameterizing them over a single `TrustedBase` module. Closes the "is this theorem axiom-free?" audit question structurally. Orthogonal to 0.10. |

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

- **`0.2.4` family** — Layer 0 backend now resumed. Four new active/design children opened 2026-05-05 from a closure-codegen audit:
  - `0.2.4.3` — slot-model alignment (no frames, slot-frontier threading) across spec + abstract trace + target trace.
  - `0.2.4.4` — close the closure[1] hiding place at the spec level (`body-label` + `encode-decode-code-addr` bijection).
  - `0.2.4.5` (re-scoped) — drop `AllocMode`; introduce `Allocator = Stack \| Dynamic`; rename `ValueLocation` constructors (`InReg` / `AtStack` / `AtDynamic`); two input registers; `FitsInReg` replaces `IsPrimitive`; Unit erased; alloc/free as SigOps.
  - `0.2.4.6` — `Once.Place` pass: static analysis deciding destinations + lifetimes, inserting alloc/free SigOps. Subsumes `Once.Escape`.
- **`0.4-T3`** — top-level pipeline composition for `Verified.Compile.correct` landed (commit `4dd740cc`). Per-stage discharge follows once `0.10` + `0.2.4.3` + `0.2.4.4` close.
- **`0.4` / `0.4.2`** — frontend completeness closure + end-to-end composed theorem. Natural follow-on from recently-landed `0.6.2`.

## Live regression test

`(id . id . id) 42` is the canonical Layer 0 end-to-end regression for the 0.2.4 family. Current state under the partial fix:

- `id 42` → exit 42 ✓
- `(id . id) 42` → exit 42 ✓ (was broken pre-2026-05-04)
- `(id . id . id) 42` → segfaults at `RIP=0x2a` (different bug from the original saved-rbp/return-address corruption). Closes when `0.2.4.3` + `0.2.4.4` land fully.

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
