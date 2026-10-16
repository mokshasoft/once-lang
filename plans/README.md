# Plans

Open work only (29 plans). A finished plan is deleted (MERGE.md §1), after its durable content has gone
into the decision log (`docs/compiler/decision-log.md`) or into module headers. Git history
keeps the file. Each plan's own `status:` line and its "next step" section are authoritative.
This index is a map and was last re-derived from the code on 2026-10-11.

## Trust base and the apex claim

| Plan | State | What remains |
|---|---|---|
| 0.11 parameterized trusted base | A done (D302) | B `ArchModel`, C world/resources, D models, E `--safe` cone, F one concrete instance |
| 0.93 relation, not datatype | S3 in progress (`Once/Spike/RelSpike.agda`) | S3–S6: discharge `BlockRunsHyp` ×3 on `once-certified` |
| 0.88 discharge obs-correct | open | `cata-correct`, `obs-correct-sigop-rest`, `obs-correct-In`, `obs-correct-in-ν` |
| 0.62 shape correctness | M1/M2 done | M2b, M3: `emitted-shape-check`, `run-meets` (two of `RunWF` ×7) |
| 0.67 wire arith proofs | route obsolete | owns `arith-sigop-contract` ×3; `ev`/`step-budget` definitions |
| 0.110 start state assumes less | not started | boot registers/flags |
| 0.111 interpretation ABI in the Spec | not started | the calling-convention obligation; 0.113's A3 runtime test |
| 0.89 relocatable compilation units | mostly done | B step 4 (deferred), C (may fold into 0.93), F (optional), closing entry |

## The Spec

| Plan | State | What remains |
|---|---|---|
| 0.120 the categorical review | Spec patch D318 awaiting approval; metatheory green | user: review + `make spec-approve`; then plan 0.119 §7 D |
| 0.114 the Spec stands alone | A (gate) done; B next | the Spec is `Once/Spec`, imports only itself, no re-exports/renaming/hiding, `--safe`, definitions only, reads as categorical semantics |
| 0.59 oracle principality | open | C1/C3 coverage, P1–P4 (mgu, completeness, principality, diagnostics) |
| 0.50 named defs are morphisms | ABI landed | retire `classifyAppHead` from the judgment (moved here by D293) |
| 0.96 `IO` is not a language construct | not started | decide (§3), remove the parser sites |
| 0.79 categorical laws | not started | decide whether source-level laws are Spec metatheory |
| 0.112 categorical structures | draft | lawful structure records, then the renames |
| 0.115 rejections check why | not started | about 68 bare `isLeft` test assertions |
| 0.116 effects are Freyd | A next | coherence (one meaning per judgment) and Freyd (pure = central) on the apex; effects run once at `Zero` |
| 0.117 total and productive | C next | T+P stated in the Spec; servers by guarded iteration over the completely iterative monad (D311) |

## Compiler and codegen

| Plan | State | What remains |
|---|---|---|
| 0.86 allocation is mechanical | open | the machine half of step D, B′, C, F, `Allocator` rename |
| 0.87 stack-resident I/O | not started | re-prove the correspondence with stack pointers |
| 0.35 allocator interface | M1 done | M2–M8 (free, wiring, leak-freedom, variable-size) |
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
