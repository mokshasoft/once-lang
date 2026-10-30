# MERGE — merging a work branch into `master`

The steps below run in order. `master` takes only changes that have been analysed, approved,
are green, and are recorded in the decision log. Heavy artifacts (MAlonzo, binaries) are
regenerated only after the changes they would bake in have been approved.

This file holds rules and steps. History, counts and worked examples go in the decision log
(`docs/compiler/decision-log.md`) or in the module headers they concern, not here.

## 1. Analyse the branch (first, before rebase or extraction)

Read `git diff master..HEAD` file by file and classify every change:

- **Principled**: it turns something into a theorem, narrows an assumption to a named honest
  fact, fixes a model defect in the semantics, deletes a site with no producer, or records a
  decision.
- **Shim**: it special-cases a proof to get green, weakens a spec to fit the implementation,
  adds a postulate to route around a proof fight, or conditions a claim on something chosen
  because it is provable rather than because it is true.

Shims do not merge. An unavoidable shim needs an explicit decision entry (§2) saying so and why.

The analysis must cover each of the following.

**The Spec.**
- `Once.Spec` essentially does not change. The implementation bridges to the Spec, never the
  reverse. Every hunk that touches it needs a written justification. "The proof needed it" is
  never a justification. Legitimate reasons are a language-level decision in the decision log,
  or a pure addition that defines a new observable.
- The Spec is the directory `formal/Once/Spec` (D306): it imports only itself, re-exports nothing
  and owns its definitions. Diff it as a directory:
  `git diff master..HEAD --stat -- formal/Once/Spec`
  and check `make spec-gate`, which fails if its import closure gains a module outside it.
- Every Spec module is proof-free. A `-sound`/`-complete` proof is evidence that the
  implementation meets the claim; it is not part of the claim. A proof added to the Spec stops
  the merge. Properties of the language go in `Once.Spec.Metatheory` as statements, proved under
  `Once/Metatheory`.
  The one exemption is `Once.Spec.Type.Substitution` (D335): substitution is functorial, and the
  meaning of a reference to a polymorphic definition is not well-typed without it. Nothing may be
  added to it, and no other Spec module may prove anything.
- A meaning clause may omit or repeat a premise's meaning only if the premise is pure; an
  effectful premise is bound exactly once, left to right (plan 0.116). Its effects then happen once,
  in the order written, which the Spec's coherence and Freyd theorems rely on.

**The Spec, read through the tests.** A large Spec diff cannot be reviewed hunk by hunk. The tests
show what changed for a programmer, so analyse their diff against master as well:

```
git diff master..HEAD --name-status -- compiler/test tests examples formal/Once/Parser/Tests.agda
```

Classify every test change and judge it from first principles: is the language better, more
uniform, or closer to `GOAL.md` and its categorical reading?
- *Added*: a program is newly accepted, rejected or observed. Name the Spec change and the
  decision behind it.
- *Deleted*: something is no longer accepted or observable. Name the decision that removed it,
  and check that removing it was the intent, not a loss to get a proof through.
- *Modified expectation*: accept and reject swapped, or the exit code, trace or error changed.
  This is a change in meaning, and it must trace to a decision.
- *Modified program text only*: the surface changed (syntax, names, imports). Name the decision
  that changed the surface, and check that the program still tests what it did before.

A test change that no decision explains stops the merge. So does a Spec change that no test
witnesses, unless the analysis says why no program can observe it.

**Top-level modules.** State which of these the diff touches, what changed and why:
`Once.Spec`, `Once.Certified`, `Once.Compiler`, `Once.Compile`, the trusted base, and the core
types (`Once.IR`, `Once.Type`, `Once.IRTy`). Read their hunks line by line. If none is touched,
say so explicitly and verify it with
`git diff master..HEAD --stat -- ':(glob)formal/Once/*.agda'`.

**Trust base.** Postulates, `TERMINATING` and other check-disabling pragmas may only change with
an explanation for each entry:
- A new assumption needs a name and a decision entry, and it must be true of the reachable
  states of emitted programs. An assumption about our own code is a proof gap. Prove it; never
  make it a hypothesis (plan 0.11's rule).
- Emptiness probe: for each new residual, try `probe : P → ⊥; probe ()` in a scratch module. If
  it compiles, the residual is false and everything downstream is unsound. This is mandatory when
  a witness datatype loses a constructor.
- A new assumption whose type is not obviously inhabited owes a model, as a field of
  `NonVacuous` (`Once.Certified.Models`). A model kept in an island module rots unseen.
- Never add a check-disabling pragma to the correspondence cone (`make pragma-gate`, §5).

**Islands.** Every new module and lemma is load-bearing on the apex: deleting it must break
`make certified`. For each one, decide which of these it is:
- *wired*: it is on the apex path;
- *superseded*: something on the path replaced it, so delete it;
- *unwired prize*: it proves what the apex postulates, so wire it in;
- *metatheorem*: a property of the language rather than a premise of the compiler proof. Its
  statement goes in `Once.Spec.Metatheory`, its proof under `Once/Metatheory` (Spec-side imports
  only), and it is carried by `CertifiedBuild.language`. Wire it there or delete it.

Two cautions:
- "Unreachable" means it contributes nothing to the apex proof term. It does not mean
  deletable: re-export shells and modules needed only to compile are unreachable too. Verify a
  deletion by building, never by an import scan.
- A `public` re-export makes the build break when its target is deleted, even if nothing uses
  the name. So for every re-exported name, check that something other than the re-export line
  consumes it.

**Extracted cone.** List the changed files that extraction covers: parser, resolver,
typechecker, IR lowering, emitters, `Once.Compile`, and the machine semantics they use. For each,
state what the compiled output now does differently. This decides whether §4 runs. Check a
"proof-only" claim by reading the diff, not the commit messages.

**Emitted code and its cost.** For each extracted-cone change that alters what the compiler emits
(the optimizer, the arith pass, lowering, the emitters, the linked runtime), the decision entry
measures master against the branch over the whole corpus (`compiler/test`, `examples`, `tests`),
built the same way on both sides, per program and in total, with `tests/codegen-measure.sh`
(`measure` on each side, then `compare`):
- *Code size*: `.text` on each arch. IR size after `once optimize` is a hint; the binary decides.
  A rule that shrinks the IR and grows `.text` does not stay.
- *Memory, static*: heap allocation sites and the cells they allocate; frames reserved, the largest
  and their sum, in slots (`once stats`, over the program image every arch lowers). A change that
  moves work between stack and heap says so, and under which `--alloc` mode it was measured.
  Run-time counts (cells allocated per run, peak heap and stack, instructions executed) are plan
  0.130; until it lands, the entry says which way it expects them to move and why.
- *Reach*: programs that newly build, newly fail, or link differently.

Every program that gets worse on any measure is named in the entry, with its cause and the reason
it is accepted. A change claimed to leave the emitted code alone is checked: the corpus binaries
are byte-identical to master's on all three arches (`tests/codegen-measure.sh same`).

**Plans.** For every plan the branch touched:
- Delete a finished plan, after moving anything durable into the decision log or into module
  headers. Say in the commit message where it went.
- Update an unfinished plan so that its *next step* and the context needed to start it cold are
  current.

## 2. Decision log

Every design decision the branch embodies has a `D###` entry in
`docs/compiler/decision-log.md` before the merge. A decision is anything a future session could
ask "why is it this way?" about. Date an entry by when the decision was made.

Every entry that sets or changes a rule also updates the decision state in the same commit —
`docs/decisions/language.md` (what the Spec or a programmer sees) or `docs/decisions/internal.md`
— so the state, read with `GOAL.md`, is the one place the current intent is found. An entry that
contradicts `GOAL.md` changes `GOAL.md` openly or is wrong.

**Steps 1–2 are presented for approval. Nothing below runs on an unapproved branch.**

## 3. Rebase on a fresh master

```
git checkout master && git pull origin master
git checkout <branch> && git rebase master
```

Resolve conflicts on the branch. If the rebase pulled in master-side changes, re-run
`formal/scripts/agda-safe.sh certified` before going on.

## 4. Extraction (if §1 found extracted-cone changes)

Run this after the rebase, as one extraction after all Agda edits:

```
rm -rf formal/_build/malonzo/MAlonzo && make -C formal malonzo   # syncs compiler/src/
```

Register new modules and drop deleted ones in `compiler/once.cabal`. Then run `cabal build all`
and `cabal test` (memory-capped, like agda), and the exit tests on all three arches:
`tests/run-exit-tests.sh`, `tests/run-exit-tests-x86_32.sh`, `tests/run-exit-tests-riscv64.sh`.
A green apex says nothing about the extracted pipeline.

If §1 measured the emitted code, run `tests/codegen-measure.sh measure` on the rebased build. Its
totals must match the decision entries; a difference means an entry is stale.

## 5. Mechanical gates

```
cd formal && make merge-gate
```

It runs the following, cheapest first:

| Gate | Script | Fails when |
|---|---|---|
| `public-gate` | `scripts/public-gate.sh` | a module gains `public` re-exports beyond `public-gate.baseline` |
| `pragma-gate` | `scripts/pragma-gate.sh` | the apex/compiler closure gains a check-disabling pragma beyond `pragma-gate.baseline` |
| `metatheory-gate` | `scripts/metatheory-gate.sh` | a proof under `Once/Metatheory` imports outside the Spec side |
| `spec-gate` | `scripts/spec-import-closure.py --gate` | the Spec's full import closure gains a non-Spec module, an implementation re-export or a re-export without `using`, beyond `spec-gate.baseline` |
| `backstop` | `scripts/backstop.sh` | any module outside `backstop.islands` fails to check |
| `certified` | `scripts/agda-safe.sh` | the apex fails to check |

Rules that go with the gates:
- Baselines and the islands list are ratchets: they only shrink. An entry is lowered or removed
  in the same commit that makes that possible. Raising one needs a decision entry with the
  reason.
- Warnings are errors (`-W error`). Fix the cause; never silence a warning. Mark a catch-all
  `CATCHALL` only when it is an intended fallback. Read an unreachable clause before deleting
  it, because it may be a constructor captured as a pattern variable. A per-module option needs
  a comment giving its reason.
- Re-export only to share a parameterised module's instance, and in the Spec door. Remove
  re-exports and prune dead imports with `scripts/reexport-remove.py`, which checks name
  resolution before and after. Never edit them by eye.

## 6. Reachability (the trust base must not grow silently)

```
./run-ast-dumps.sh                              # master and the branch
HEAP=6G COMPACT=-c20 ./run-ast-dumps.sh <ref>   # if a module runs out of memory
```

This needs the Agda fork with `--write-ast` (see the script header). It takes tens of minutes
per ref, so start it during §1. Compare the two dumps:
- `counts.trustBase` and the per-marker split. A postulate appearing needs a decision entry. A
  postulate splitting into another postulate plus a proof shows up as +1/−1 and is fine.
- Modules leaving `reachable`. Removing the last consumer of a proof must be intentional,
  because nothing else in the build notices it.
- The counts are of declarations, not source sites: one pragma covers a whole mutual block and
  its generated helpers. Use the counts to detect change. Quote source-level numbers in
  decision entries.

## 7. Merge

- Fast-forward, or `--no-ff` per convention. Never squash: commit hashes are referenced from
  the decision log.
- `HANDOFF.md` is untracked working notes. It never enters a branch.
