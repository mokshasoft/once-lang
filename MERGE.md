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
- The Spec is its re-export closure, not a directory. Diff the generated list, never a
  hand-written one:
  `git diff master..HEAD --stat -- $(python3 formal/scripts/spec-closure.py)`
- Every module in that closure is proof-free. A `-sound`/`-complete` proof is evidence that the
  implementation meets the claim; it is not part of the claim. A proof added to a closure module
  stops the merge.
- If the closure count falls, suspect a lost `public` before believing the Spec shrank.
- The closure is not the whole trust surface. Wherever a closure module imports
  implementation code (see plan 0.114), the definitions it uses are part of what the Spec means
  and are reviewed as Spec. `make metatheory-gate` lists the named exceptions.

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

**Plans.** For every plan the branch touched:
- Delete a finished plan, after moving anything durable into the decision log or into module
  headers. Say in the commit message where it went.
- Update an unfinished plan so that its *next step* and the context needed to start it cold are
  current.

## 2. Decision log

Every design decision the branch embodies has a `D###` entry in
`docs/compiler/decision-log.md` before the merge. A decision is anything a future session could
ask "why is it this way?" about. Date an entry by when the decision was made.

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
