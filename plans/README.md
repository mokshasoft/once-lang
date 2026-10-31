# Plans

Open work only (31 plans). A finished plan is deleted (MERGE.md §1), after its durable content has gone
into the decision log (`docs/compiler/decision-log.md`) or into module headers. Git history
keeps the file. Each plan's own `status:` line and its "next step" section are authoritative.
This index is a map and was last re-derived from the code on 2026-10-11 (the Spec table on 2026-10-21).

## Trust base and the apex claim

| Plan | State | What remains |
|---|---|---|
| 0.11 parameterized trusted base | A done (D302) | B `ArchModel`, C world/resources, D models, E `--safe` cone, F one concrete instance |
| 0.93 relation, not datatype | S3 in progress (`Once/Spike/RelSpike.agda`) | S3–S6: discharge `BlockRunsHyp` ×3 on `once-certified` |
| 0.88 discharge obs-correct | open | `cata-correct`, `obs-correct-sigop-rest`, `obs-correct-In`, `obs-correct-in-ν` |
| 0.62 shape correctness | M1/M2 done | M2b, M3: `emitted-shape-check`, `run-meets` (two of `RunWF` ×7) |
| 0.67 wire arith proofs | route obsolete | owns `arith-sigop-run` ×3 (the lookup half is a theorem, D351); `ev`/`step-budget` definitions |
| 0.110 start state assumes less | not started | boot registers/flags |
| 0.111 interpretation ABI in the Spec | not started | the calling-convention obligation; 0.113's A3 runtime test |
| 0.89 relocatable compilation units | mostly done | B step 4 (deferred), C (may fold into 0.93), F (optional), closing entry |

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
| 0.126 combinators synthesize | not started | decide grades/quantities (§2), then `s-case-fun`/`s-pair-fun`/`s-compose-fun`, metatheory, checker |

## Compiler and codegen

| Plan | State | What remains |
|---|---|---|
| 0.86 allocation is mechanical | open | the machine half of step D, B′, C, `Allocator` rename (F moved to 0.123) |
| 0.87 stack-resident I/O | not started | re-prove the correspondence with stack pointers |
| 0.123 memory runs out observably | after the merge | A: out of memory is a Spec end + the Host's `exhaust` (removes `HeapRoom`/`StackRoom`/`CallRoom`); B: wire the proven allocators, `free`, reclaim per loop round, leak-freedom (was 0.35 and 0.86 F) |
| 0.124 `once fmt` | after 0.122 | one canonical layout from the Spec's `Module` plus lexer trivia (no second syntax tree); round-trip, idempotence and comment preservation as theorems; deletes the `Grammar` printer |
| 0.125 Once in nixpkgs | A, B, C.1, C′ 1–4 done | C.2 draft `package.nix` against nixpkgs; C′ 5 server-test segfaults; D release + nixpkgs PR |
| 0.129 optimizer strength | A, B, B4, B5, C1 done; C2 dropped | C3 pair fusion, C4 Lambek; D: discovery tool on traces; E: optimality over the trace |
| 0.130 run-time cost instrumentation | not started | decide where counts come from (flat machine vs emulator); one report shape shared with the Agda fork's; dependent-type-ready keys |
| 0.64 proof-island audit | open | groups F, S, C and `TypeCheck` (group O done, D347) |
| 0.37 chunked cata payload stack | deferred | ISA extension + chunked codegen |
| 0.56 register-budget arith | parked | steps A–E |
| 0.127 Once runs on seL4 | not started | A: a seL4 Host (entry, stack, `once_leave`) and a Once root task under QEMU; B: rootserver + echo; C: other arches |
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
