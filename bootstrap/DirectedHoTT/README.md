# DirectedHoTT — a directed dependent-type kernel for Once

**Read this first.** Migrated out of `bootstrap/poc/OCP0009/` on 2026-08-22.
That directory still holds 329 `.agda` files across several unrelated
tracks; **it is no longer built by anything** and is kept only as an
archive. Everything live is here.

## What this is

`Hom t u = t ⟶* u` — a **directed** identity type. Once's IR already owns a
directed structure (its rewrite relation), and this kernel internalises it.
See `poc/OCP0009/PATHS.md` for the fork: Path 1 is the Conversion Tower
(symmetric equality, `NbEPMon*`), Path 2 is this one. **`Id = core(Hom)`** —
symmetric equality is the maximal sub-groupoid of the directed structure,
so directed is strictly the richer primitive.

## Layout, in the order a reviewer should read it

| | | |
|---|---|---|
| `Spec/` | Syntax → Variance → Typing | **the theory.** Read this first; if it is wrong nothing else matters |
| `Trust.agda` | — | **what is assumed.** Empty, and *checked* by `tools/check-trust.sh` |
| `Metatheory/` | SubjectReduction, Confluence, Injectivity, LogicalRelation, Fundamental, Canonicity | that the theory is well-behaved |
| `Algorithm/` | DecideConversion | executable artifacts + their correctness |
| `Lib/` | Amrec, AmrecInd, IHCall, Wk, Arith, … | derived combinators |
| `Examples/` | Gcd/, Amrec, Id, … | evidence you can program in it |
| `Comparison/` | gcd three ways; the concrete IndStep | benchmarks — **built**, reported apart |
| `Negative/` | the lexrec track | refuted — **not built** |

⚠ **`Variance` is `Spec/`, not `Metatheory/`** — `Typing` imports its
syntactic predicates, so the variance judgment is part of what the theory
*is*, not a theorem about it.

## The two review questions, and which folders answer them

- **Is it sound?** `Spec/` + `Trust.agda` + `Metatheory/`. `Lib/` and
  `Examples/` cannot weaken anything, because `Trust` is empty and checked.
- **Is it any good?** `Lib/` + `Examples/`, and you **cannot** skip them.
  An empty trust surface proves soundness, not *meaningfulness*: `lexrec`
  (now in `Negative/`) was `--safe`, postulate-free, green — and
  **uncallable**, its premise unsatisfiable. That is caught by the standing
  rule that *every library branch is exercised by an Example*, not by
  `Trust`.

## Building

    ./DirectedHoTT/tools/sweep.sh              # 90 modules, ~200s warm
    ./DirectedHoTT/tools/sweep.sh --negative   # also build the refuted track
    ./DirectedHoTT/tools/check-trust.sh        # the trust surface alone

⚠ **Exit 143 is not a verdict.** It has at least three causes: a real
memory wall, the wrong garbage collector, and metavariables that never
solved. The sweep retries once with `+RTS -c` before believing it. See
`PERF.md`. In `Comparison/` a 143 is reported as UNMEASURABLE rather than
FAILED — a benchmark that does not fit is a measurement you did not get.

⚠ **Never run two Agda checks at once.** They OOM-kill each other on a
small machine, and the result is indistinguishable from a real failure.

## Where the WF axis stands

`amrec` (measure-bounded recursor) → `amrec-ind` (its induction principle)
→ `Examples/Gcd/IndG.Plumb` (gcd's induction at an **arbitrary motive**).

Two structurally different customers share one plumbing and one `StepExt`:

| | divisibility | maximality |
|---|---|---|
| motive | `QCode` — a `⌜Σ⌝` | `MaxCode` — a `⌜Π⌝` |
| leaves | **project** the IH's two conjuncts | **decode** the IH to a function |
| theorem | `Examples/Gcd/Spec` | `Examples/Gcd/MaxSpec` |

`gcdStepExt` is a fact about gcd's *step*, not either motive — proved once,
spent twice.

⚠ `Plumb` is generic in the **motive** and hard-wired to gcd (45
gcd-specific names). It is correctly an Example. The library boundary is
`Lib/AmrecInd`, generic in carrier, measure, step and motive alike.
