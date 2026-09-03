# MERGE — rules for merging a work branch into `master`

Before any branch merges into `master`, walk this list top to bottom, in this
order. The point is that `master` only ever absorbs changes that are analyzed,
approved, green, and accounted for in the decision log — and that no heavy
build artifact (MAlonzo, binaries) is regenerated before the changes it would
bake in have been analyzed and approved.

## 1. Analyze the branch changes (FIRST — before rebase or extraction)

Read the full branch diff (`git diff master..HEAD`) file by file and classify
every change:

- **Principled** — makes something a theorem, narrows a residual to a named
  honest fact, fixes a model defect at the semantics (`flat-exec-instr` /
  the flat machine), deletes a site that has no producer, records a decision.
- **Shim** — special-cases a proof to get green, weakens a spec to fit an
  implementation, adds a postulate to route around a fight, conditions a
  claim on something chosen for provability rather than truth.

Shims do not merge. If a shim is unavoidable, it needs an explicit decision
(step 2) saying so and why — silent shims are how vacuity happened.

Special scrutiny, in order:

- **`Once.Spec` MUST essentially not change.** It is the one home of the
  language definition; a branch whose diff touches it needs a written
  justification per hunk, and "the proof needed it" is never one — the
  implementation bridges to the spec, not the spec to the implementation
  (top-down specs). Legitimate reasons are a language-level decision recorded
  in the decision log, or a pure addition that defines a new observable.

  **The spec is not a path — it is a RE-EXPORT CLOSURE, and a path filter
  cannot see it.** `Once/Spec.agda` re-exports five modules, and two of them
  re-export implementation-namespaced files VERBATIM: `Once.Spec.Typing` is
  `Once.TypeCheck.Judgment`, and `Once.Spec.Meaning` re-exports from
  `Once.Denotation`. So a branch can rewrite the entire declarative typing
  judgment while `formal/Once/Spec.agda` and `formal/Once/Spec/*` show a
  one-line comment diff. Plan 0.76 did exactly that (66 rules over four
  judgment forms → 51 over two) and the path filter below printed nothing.
  Resolve the closure and diff THAT, not the directory:

      git diff master..HEAD --stat -- $(python3 formal/scripts/spec-closure.py)

  `formal/scripts/spec-closure.py` resolves the transitive `open import …
  public` closure of `Once.Spec` and prints it as paths, so the list is
  GENERATED rather than maintained — a hand-written one goes stale and is the
  same hole again. It is 16 modules today:

      Once/Spec.agda + Once/Spec/{Type,Syntax,Typing,Meaning,Correct}.agda
      Once/Type.agda            Once/TypeCheck/Raw.agda
      Once/TypeCheck/Judgment.agda                       (= Once.Spec.Typing)
      Once/Denotation/{Admissible,Trace,ValueDomain,Behavior,Meaning,MainMeaning}.agda
      Once/Adequacy.agda                                 (= Once.Spec.Correct)

  The list this file carried before named FOUR paths and omitted
  `Once/Type.agda`, `Once/TypeCheck/Raw.agda`, `Once/Adequacy.agda` and five of
  the six `Denotation` modules.

- **The re-export closure is not the whole trust surface.** Two leaks the
  closure does NOT show, found 2026-09-01 and recorded here so a reader does
  not have to rediscover them:

    * **Rule premises reach outside it.** `Once.TypeCheck.Judgment` calls
      `composeMid`, `classifyAppHead` and the four lookups from
      `Once.TypeCheck.Classify` — a module that is NOT in the closure and whose
      names `Once.Spec` does not export. So which programs are well-typed can
      be changed by editing a file the audit surface cannot see. Plan 0.80 /
      D134 is removing these premises; until it finishes, **diff
      `formal/Once/TypeCheck/Classify.agda` as part of the spec review.**
    * **The meaning is indexed by the compiler.** `Denotation.MainMeaning`'s
      `meaningᵈ` takes `C.Module` (`Once.Compile`), `AS.ModuleTyped`
      (`Once.Adequacy.AcceptSound`) and `MC.HasValidMain-decl`
      (`Once.Adequacy.ModuleComplete`) — two of them the compiler's own PROOF
      modules — and dispatches on `C.extractFunctions`. Not a logical
      circularity, but a trust one. Open; see plan 0.80's P3.
- **Top-level module impact.** The analysis must STATE which top-level
  modules the diff touches, each with what changed and why — these are the
  trust anchors, so their diffs get read hunk by hunk, not skimmed:
  `Once.Spec` (strictest, above), `Once.Certified` (what the certification
  claims), `Once.Compiler` / `Once.Compile` (the compiler statement and
  pipeline — also the extraction root), `Once.Postulates` /
  `Once.ProofObligation` (the trusted base), and the core object-language
  types (`Once.IR`, `Once.Type`, `Once.IRTy`). A change to any of these that
  the analysis cannot justify in one paragraph is a stop-the-merge finding.
  "No top-level module touched" is itself a statement the analysis must make
  explicitly (and verify by path filter:
  `git diff master..HEAD --stat -- ':(glob)formal/Once/*.agda'` — the
  `:(glob)` matters, a bare `*` crosses directories).
- **Postulate delta.** Count residuals/postulates on master vs the branch
  (`grep -rn postulate` over the correspondence cone). The delta must be
  explainable residual by residual: every NEW postulate needs a name, a
  site/run conditioning (the vacuity discipline), and the hypothesis that
  makes it true of reachable states of emitted programs. Re-run the probe
  recipe (`vacuity-probe*.agda`) if any new residual is in the
  state/program-fact class.
- **`{-# TERMINATING #-}` / `--allow-unsolved` pragmas.** None may enter the
  correspondence cone (Machine / Codegen / Adequacy).
- **`make -C formal lint-imports` is clean.** Agda only WARNS when a `using
  (…)` names something a module does not export, so a rename or deletion
  leaves stale import lists behind silently and forever (D139). The lint is a
  full-tree scope-only pass; it is fast (no type-checking) and it is the only
  check that sees a directive naming a symbol that no longer exists.
- **No islands — every change must be load-bearing on the apex proof path.**
  For every new module/lemma the branch adds, deleting it must break the
  build of `certified` (or the three-arch cluster) — an unwired supporting
  module is dead code that hides gaps instead of surfacing them as type
  errors (the `conc-flat-sim-just` lesson: a postulated apex node lets
  everything under it float disconnected). Spot-check by grepping who
  imports each new module; anything reachable from no apex is either
  deleted before merge or explicitly justified as a decision-logged
  exception.
- **Extracted-cone changes.** List which changed files the extraction covers
  (parser, resolver, typechecker, `ir-to-trace`, the per-arch emitters,
  `Once.Compile`, machine-semantics modules in the closure) — this determines
  whether step 4's extraction gate is required, and each such change needs
  its behavioral justification stated (what the compiled output now does
  differently, and why that is right).

## 1b. Plans-folder hygiene (part of the analysis)

The same read of the branch determines the state of every plan it touched
(`plans/*.md`):

- **Finished plans are DELETED** — a completed plan left in the folder reads
  as open work. Before deleting, extract anything of durable value (design
  findings, residual genealogy, techniques) into the decision log or the
  module headers it belongs in, and commit that extraction; the plan file's
  deletion notes in its commit message where the content went (the D073/P5
  precedent: the plan's own final phase instructed its deletion).
- **Unfinished plans are UPDATED** — the file must clearly state the NEXT
  item to pick up and the context needed to pick it up cold (what is done,
  what is in flight and where it lives, which gates passed). A stale plan
  whose "next step" was done three sessions ago is worse than no plan.

## 2. Decision-log coverage

Every design decision the branch embodies must exist as a `D0xx` entry in
`docs/compiler/decision-log.md` BEFORE the merge — check the branch's commits
against the log. A decision is anything a future session could ask "why is it
this way?" about: a representation choice, a model change, a residual class
accepted as an honest axiom, a spec-level call. If a commit made such a
choice without an entry, write the entry now (date it when the choice was
made, not the merge date).

**The analysis of steps 1–2 is presented for APPROVAL before anything below
runs. Nothing after this line happens on an unapproved branch.**

## 3. Rebase on a fresh master (after approval)

- `git checkout master && git pull origin master`
- `git checkout <branch> && git rebase master`
- Resolve conflicts on the branch, never on master. If the rebase pulled in
  master-side changes, re-run the quick verification
  (`formal/scripts/agda-safe.sh certified` + the three-arch cluster
  `MODULE=Once/Adequacy/ArchCorrectness.agda`) before proceeding — the
  combination is code neither side saw.

## 4. Extraction gate (after the rebase, so the artifacts match the final tree)

If step 1 found extracted-cone changes:

- Regenerate MAlonzo — ONE extraction, after all Agda edits:
  `rm -rf formal/_build/malonzo/MAlonzo && make -C formal malonzo` (syncs to
  `compiler/src/`); register any NEW extracted modules in
  `compiler/once.cabal`.
- `cabal build` + `cabal test` (under the memory-capped scope, like agda).
- Exit tests on all three arches: `tests/run-exit-tests.sh`,
  `tests/run-exit-tests-x86_32.sh`, `tests/run-exit-tests-riscv64.sh`.
  A green `certified` says nothing about the extracted pipeline: a removed
  constructor's leftover catch-all clause, or an unwired module, only shows
  up here.

Proof-only branches skip this step — but check the "proof-only" claim by
reading the diff (step 1), not the commit messages: a "proof" commit that
edits a function definition in an extracted module IS a codegen change.

## 5. Merge

- Fast-forward or `--no-ff` per repo convention; do not squash away the
  per-step history — the commit messages are part of the residual genealogy
  that HANDOFF/decision-log entries reference by hash.
- After the merge: HANDOFF.md is UNTRACKED working notes and never merges;
  make sure it did not sneak into the branch.
