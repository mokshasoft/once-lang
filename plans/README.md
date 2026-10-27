# Plans

Open work only (29 plans). A finished plan is deleted (MERGE.md §1), after its durable content has gone
into the decision log (`docs/compiler/decision-log.md`) or into module headers. Git history
keeps the file. Each plan's own `status:` line and its "next step" section are authoritative.
This index is a map and was last re-derived from the code on 2026-10-11 (the Spec table on 2026-10-21).

## Trust base and the apex claim

| Plan | State | What remains |
|---|---|---|
| 0.11 parameterized trusted base | A done (D302) | B `ArchModel`, C world/resources, D models, E `--safe` cone, F one concrete instance |
| 0.125 calls proved, not assumed | open (2026-10-27) | S0 done; S1 `ValidAtWF` as a function on the type, S2 block-call lemma, S3 producers/consumers (incl. `cata-correct`), S4 layout, S5 delete `BlockRuns`/`BlockRunsHyp` ×3 (EMPTY, D340) |
| 0.124 unbounded abstract stack | DONE (D342): depth-tagged frames on all three arches, `shift-≺` a `FrameSemantics` field | none; consumed by 0.125 S2 |
| 0.88 discharge obs-correct | open | `obs-correct-sigop-rest` (structured codomains; split it by reason), `obs-correct-In` until 0.125 S3; `cata-correct` moved to 0.125 |
| 0.62 shape correctness | M1/M2 done | M2b, M3: `emitted-shape-check`, `run-meets` (two of `RunWF` ×7) |
| 0.67 wire arith proofs | route obsolete | owns `arith-sigop-contract` ×3; `ev`/`step-budget` definitions |
| 0.110 start state assumes less | not started | boot registers/flags |
| 0.111 interpretation ABI in the Spec | not started | the calling-convention obligation; 0.113's A3 runtime test |
| 0.89 relocatable compilation units | property delivered at the emitter and link; kept | C1 done inside 0.125; B (the machine runs units, ~1700 sites) do-or-drop decision; F optional |

## The Spec

| Plan | State | What remains |
|---|---|---|
| 0.121 before the merge | merged 2026-10-22 | §2: optional Spec improvements, echo-server test, loop name, T1/T2, the examples, tidy-ups |
| 0.122 collapse the internal language | after the merge | retarget the compiler onto the Spec layer by layer (types, core, meaning, surface); delete `Once.Internal` and the bridges |
| 0.50 named defs are morphisms | ABI landed | retire `classifyAppHead` from the judgment (moved here by D293) |
| 0.96 `IO` is not a language construct | not started | decide (§3), remove the parser sites |
| 0.79 categorical laws | not started | decide whether source-level laws are Spec metatheory |
| 0.112 categorical structures | draft | lawful structure records, then the renames |
| 0.115 rejections check why | not started | about 68 bare `isLeft` test assertions |

## Compiler and codegen

| Plan | State | What remains |
|---|---|---|
| 0.86 allocation is mechanical | open | the machine half of step D, B′, C, `Allocator` rename (F moved to 0.126) |
| 0.87 stack-resident I/O | not started | re-prove the correspondence with stack pointers |
| 0.123 memory runs out observably | after the merge | A: out of memory is a Spec end + the Host's `exhaust` (removes `HeapRoom`/`StackRoom`/`CallRoom`); C: coarse per-block room checks, static depth later, guard pages rejected |
| 0.126 allocators reclaim | after 0.123 | wire the proven allocators, `free`, reclaim per loop round, leak-freedom; turns the six "a server never ends" tests green (was 0.123 B) |
| 0.39 trace-correct optimizer | open | restate over traces, discharge `opt-trace` |
| 0.64 proof-island audit | open | group O (the optimizer chain; overlaps 0.39) and verdicts |
| 0.37 chunked cata payload stack | deferred | ISA extension + chunked codegen |
| 0.56 register-budget arith | parked | steps A–E |
| 0.100 AVR port | P0 done | phase A onward |

## Hygiene

| Plan | State | What remains |
|---|---|---|
| 0.60 rename value/meaning layers | not started | `Once.Semantics` → `Once.Value` (about 82 importers, re-extraction) |

## Bootstrap track

| Plan | State | What remains |
|---|---|---|
| 0-ocp3 | root | the OCP-0003 anchor that several plans name as `parent` |
| evaluator-instance | nearly done | migrate or retire the leftover bootstrap modules |
| tcb0-gap-closure | open | phases 1–5 (OCP-0004) |
