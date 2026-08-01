# Merge checklist — rules for merging a work branch into `master`

Before any branch merges into `master`, walk this list top to bottom. The
point is that `master` only ever absorbs changes that are green, principled,
and accounted for in the decision log.

## 1. Rebase on a fresh master

- `git checkout master && git pull origin master`
- `git checkout <branch> && git rebase master`
- Resolve conflicts on the branch, never on master. After the rebase, the
  full verification gate must be re-run (step 2) even if the branch was green
  before — the rebase may have combined the branch with master-side changes
  neither side saw.

## 2. Verification gate

Always:

- `formal/scripts/agda-safe.sh certified` — green.
- `timeout 280 formal/scripts/agda-safe.sh agda
  MODULE=Once/Adequacy/ArchCorrectness.agda` — the three-arch cluster
  (reaches the flat↔x86-64 correspondence cone `certified` reaches only
  transitively).

If the branch touched the CODEGEN (anything the extracted compiler is built
from — parser, resolver, typechecker, `ir-to-trace`, the per-arch emitters,
`Once.Compile`, or a machine-semantics change that extraction picks up):

- Regenerate MAlonzo (one extraction after ALL Agda edits;
  `rm _build/malonzo/MAlonzo` first — see the MAlonzo→cabal sync recipe).
- `cabal test` — the exit-test suite on all three arches (x86-64, x86-32,
  riscv64) plus the unit tests. A green `certified` says nothing about the
  extracted pipeline: a removed constructor's leftover catch-all clause, or
  an unwired module, only shows up here.

Proof-only changes (new invariant modules, residual discharges, decision-log
entries) do not require re-extraction — but check the "proof-only" claim by
reading the diff, not the commit messages: a "proof" commit that edits a
function definition (not just adds lemmas) in an extracted module IS a
codegen change. `git diff master..HEAD --stat` and look at every file the
extraction covers.

## 3. Principled-change analysis

Read the full branch diff (`git diff master..HEAD`) file by file and classify
every change:

- **Principled** — makes something a theorem, narrows a residual to a named
  honest fact, fixes a model defect at the semantics (`flat-exec-instr` /
  the flat machine), deletes a site that has no producer, records a decision.
- **Shim** — special-cases a proof to get green, weakens a spec to fit an
  implementation, adds a postulate to route around a fight, conditions a
  claim on something chosen for provability rather than truth.

Shims do not merge. If a shim is unavoidable, it needs an explicit decision
(step 4) saying so and why — silent shims are how vacuity happened.

Special scrutiny, in order:

- **`Once.Spec` MUST essentially not change.** It is the one home of the
  language definition; a branch whose diff touches `Once/Spec.agda` needs a
  written justification per hunk, and "the proof needed it" is never one —
  the implementation bridges to the spec, not the spec to the
  implementation (top-down specs). Legitimate reasons are a language-level
  decision recorded in the decision log, or a pure addition that defines a
  new observable.
- **Postulate delta.** Count residuals/postulates on master vs the branch
  (`grep -rn postulate` over the correspondence cone). The delta must be
  explainable residual by residual: every NEW postulate needs a name, a
  site/run conditioning (the vacuity discipline), and the hypothesis that
  makes it true of reachable states of emitted programs. Re-run the probe
  recipe (`vacuity-probe*.agda`) if any new residual is in the
  state/program-fact class.
- **`{-# TERMINATING #-}` / `--allow-unsolved` pragmas.** None may enter the
  correspondence cone (Machine / Codegen / Adequacy).

## 4. Decision-log coverage

Every design decision the branch embodies must exist as a `D0xx` entry in
`docs/compiler/decision-log.md` BEFORE the merge — check the branch's commits
against the log. A decision is anything a future session could ask "why is it
this way?" about: a representation choice, a model change, a residual class
accepted as an honest axiom, a spec-level call. If a commit made such a
choice without an entry, write the entry now (date it when the choice was
made, not the merge date).

## 5. Merge

- Fast-forward or `--no-ff` per repo convention; do not squash away the
  per-step history — the commit messages are part of the residual genealogy
  that HANDOFF/decision-log entries reference by hash.
- After the merge: HANDOFF.md is UNTRACKED working notes and never merges;
  make sure it did not sneak into the branch.
