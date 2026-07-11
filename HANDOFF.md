# HANDOFF — Plan 0.58 / OCP-0006 SigOp-concreteness migration

**DO NOT git-commit this file.** Branch: `ocp-0006-once-spec`.
Per-module: `timeout 250 formal/scripts/agda-safe.sh agda MODULE=Once/Path/File.agda`
(MODULE is a FILE PATH). Apex: `formal/scripts/agda-safe.sh certified` (GREEN).

## STATUS: migration LANDED, certified apex GREEN.

The IsConcrete witness is threaded end-to-end. The elaborator now REJECTS
non-concrete SigOp/FFI references (`NonConcreteSigOpType`) — a genuine, justified
behavior change (spec refinement). 3 of the 4 MeaningBridge sigop leaves are
DISCHARGED. Committed on `ocp-0006-once-spec` (commits `b233b1a6`..`217432ca`).

Key technique that unblocked it: the concreteness `with` inside the elaborator aux
is OPAQUE to external proofs, so the arrow/value clauses were DE-WITHED into
sub-auxes (`inferElabV-R{Qualified,Resolved}-{arrow,value}-aux`,
`inferElabV-RVar-import-value-aux`) taking the decision as explicit `Maybe` + eq
args. Completeness drives them type-level (`cong proj₁`); RealizeAgrees via
`agree-*ᴴ` helper lemmas that genuinely pattern-match the decision (bare `with`
fails on the delegation's baked `refl`).

## REMAINING (2 postulates in Once/Adequacy/MeaningBridge.agda)

1. `sigop-ref-arrow-bridge` — arrow-typed value ref: LHS closed `value-info`
   curried machine value vs SD's `arrow-info` closure. Needs a `generic-semM`
   β/uncurry COHERENCE fact (generic-semM is itself a postulate). Genuine design
   step, NOT mechanical — likely a new narrow coherence postulate about
   generic-semM, or restrict value-refs to non-arrow. Present options to user.
2. `cata-bridge` — fold congruence, INDEPENDENT of this migration. Strengthen the
   sig with the algebra relation (`bridge-m alg`, passable from `m-cata`), then
   prove `sem-cata` congruence over `cata-ev-algᴰ-D`.

## OTHER TODO
- `make check-all` fails ONLY on `Once/Allocator/Target/X86.agda` — a PRE-EXISTING
  dead module (added in old commit `d9803efc2`, imports non-existent
  `Once.Target.X86.Syntax`; untouched by this migration; not in the certified
  cone). See [[project_allocator_interface_unwired]]. Filtered check-all is green.
- `cabal test` / MAlonzo: the elaborator BEHAVIOR changed (non-concrete refs now
  rejected). Re-extract + hand-sync per [[feedback_malonzo_cabal_sync]]; check no
  test program relies on a non-concrete SigOp ref.
- P5 cleanup: rebuild `Once.Spec.Meaning`, canonicalize, delete duplicates, update
  OCP-0006, delete `plans/0.58-once-spec-language-definition.md`.
