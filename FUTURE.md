# Future Tasks

## Standard Strata (Bundled Standard Library)

**Goal**: Bundle Strata with the compiler so users don't need `--strata` for standard imports.

**Current behavior**: Users must specify `--strata PATH` to resolve imports like `I.Linux.Syscalls`.

**Desired behavior**: Standard imports work out of the box, like GCC's libc or Rust's std.

### Approach

1. **Bundle Strata with compiler binary**
   - Use `data-files` in cabal to include `Strata/` with the executable
   - Look for Strata relative to the compiler binary path

2. **Search order** (like GCC include paths):
   ```
   1. Explicit --strata flag (override)
   2. Strata/ relative to input file (project-local)
   3. ~/.once/strata/ (user install)
   4. /usr/share/once/strata/ (system install)
   5. Bundled with compiler binary (fallback)
   ```

3. **Error handling**:
   - If no `--strata` and no imports need resolution → just work
   - If import can't be resolved → clear error with search paths tried

### Implementation Notes

- Use `Paths_once` module from cabal to find data directory
- Consider separate "standard" vs "extended" Strata modules
- Keep `-I:TYPE MODULE` for explicit override cases

## ~~OCP-0009 POC: split the four de-facto libraries out of `Examples*`~~ — DONE 2026-08-20

**Goal**: stop `Lib*` modules importing `Examples*` modules. **Achieved** —
`grep -l "open import poc.OCP0009.NbEPDirDBExamples" NbEPDirDBLib*.agda`
returns nothing.

Four new library modules, each re-exported `public` by the `Examples*` module
it came from, so **no importer outside `Lib*` had to change**:

| new module | holds | was in | `Lib*` importers repointed |
| --- | --- | --- | --- |
| `…LibNat` | `plusTm`, `⊢plus` | `…ExamplesNat` | 4 |
| `…LibOrd` | `⊢trans`, `⊢strong-base`, `⊢strong-step`, `⊢strong-base'`, `⊢strong-descend` | `…ExamplesOrd` | 6 |
| `…LibStrong` | `El-homNat`, `natAsEl`, `elAsNat`, `reflMot`, `reflTm`, `⊢reflMot`, `⊢le-refl-z/s`, `⊢le-refl` | `…ExamplesStrong` | 7 |
| `…LibMonus` | `predTm`, `monusTm`, `⊢pred`, `⊢monus`, the four reduction laws, `homˡ*`, `predMot`, `⊢predMot`, `⊢pred-le` | `…ExamplesDiv` | 1 |

### What the plan got wrong, and what made it cheap

⚠ **The `⊢le-refl-z/s` row was wrong.** The table above listed them as
"genuine examples" that stay behind. They are not demos — `⊢le-refl` is
literally `natrec ⊢reflMot ⊢le-refl-z ⊢le-refl-s`, so they are its two
branches and had to move with it. Check what a primitive is DEFINED BY
before classifying its neighbours as examples.

★ **The estimate of ~70 import sites was the expensive framing, and it was
avoidable.** The `Lib* → Examples*` edges are NARROW — only a handful of
names cross, and only 12 modules are on the library side:

```
ExamplesOrd     ⊢strong-base', ⊢strong-step                    → 7 libs
ExamplesStrong  ⊢le-refl, reflTm, natAsEl, El-homNat           → 7 libs
ExamplesNat     plusTm, ⊢plus                                  → 4 libs
ExamplesDiv     10 monus/pred names                            → 1 lib
```

So the move is: split out exactly those, have the `Examples*` module
`open import … public` its new `Lib*`, and repoint **only the `Lib*`
importers**. Every other importer — the ~70 — keeps working untouched.
Measuring the edges before planning the churn turned a ~70-site refactor
into a ~18-site one.

## OCP-0009: the SECOND Lib/Examples inversion — general lemmas stranded in examples

**Goal**: find general lemmas that live in `Examples*` because they were
STATED at that example's instantiation.

⚠ **The 2026-08-20 split does NOT cover this.** That one asked *"does any
`Lib*` import an `Examples*`?"* and drove it to zero. Sound, but it can only
see the inversion when the dependency already runs library→example. A
general lemma sitting in an example is invisible to it, because **nothing
imports it yet** — the dependency appears the moment some future library
combinator needs it.

**How it hides.** `⊢descS-at` is a fact about `descS-at`, which is
`…LibAmrec`'s own construct — but it was written at gcd's `msr` rather than
at the abstract measure `m`. Instantiating a general lemma at an example's
parameters makes it *look* example-specific when its content is not.

**Found so far** (`…ExamplesGcdEqs`, surfaced by `amrec-ind` needing a
certificate typing): `extR-id`, `extR⁶-id`, `descS-at-idR`, `⊢descS-at`.

⚠⚠ **AND THE MOVE IS NOT A PURE RENAME — MEASURED 2026-08-20.** Relocating
them with `msr → m` FAILS:

    renTm (extR idR) m != m   of type RTm (⌊ Δ ⌋ ∙)

For gcd's **closed** `msr` that identity renaming reduces away
definitionally; for an abstract `m` it is only propositional. So
`⊢descS-at`'s proof silently depends on the measure being closed, and
generalising it needs `renTm-idR` casts threaded through `descS-peel`'s
endpoints.

⇒ **Being stated at an instance can hide a real dependency on that
instance, not just a cosmetic one.** The audit below must therefore CHECK
each candidate generalises, not assume it. Reverted rather than left
half-done.

### The audit

For each `Examples*` module, list the lemmas whose statements mention only
LIBRARY constructs (`descS-at`, `auxAt`, `aIHTat`, `Hom`, `natrec`, …) and
no example-specific term, once the example's own parameters are abstracted.
Those belong in the library.

⚠ Do this at a consolidation point, and expect it to be a bigger set than
the four above — those were found by a single combinator needing a single
certificate typing.

## OCP-0009 WF library: lift `eqG`/`pwT` out of gcd into the combinator

**Goal**: make "prove a step function is IH-extensional" a LIBRARY combinator,
not something each caller rebuilds.

**Current behavior**: discharging `StepExt` for gcd (done 2026-08-17,
`…GcdStepExtA.gcdStepExt`) needed a machine that is shaped generally but is
hard-wired to gcd's `PairT` / `msr` / `⌜Nat⌝`:

| piece | what it is | gcd-specific? |
| --- | --- | --- |
| `pwT` / `pwIntro` / `pwElim` | the pointwise hypothesis as an object-language `Π`, and its intro/elim | **no** — only the carrier/measure/code are baked in |
| `eqG μ f` | the `Id`-analogue of the step's result type, carrying the two IHs and the hypothesis as `Π`-bound | **no** — same |
| `eqG-red` | a reduction of `f` is a CONVERSION of `eqG μ f` (pushes through 3 `Π`s and both `Id` sides) | **no** |
| `eqGElim` | feed `eqG` its two IHs and the hypothesis | **no** |
| `⊢natrec-var` | re-type a `natrec` at a VARIABLE scrutinee | **no** — every splitting step needs it |
| `certAt` | fix the certificate slot of a `RecCall`-shaped reduction | **no** |
| `gcdIH-w/-w²/-w³`, `pwT-w`, `gcdIH-sub`, `pwT-sub`, `eqG-sub` | the naturality twins | **no**, modulo the same hard-wiring |
| `M₁`/`M₂`/`M₃`, the four leaves, `G1z`…`G3s`, `PAIRᶻ`/`CERTᶻ`/`PAIRˢ`/`CERTˢ` | subtractive Euclid | **yes** |

⇒ Parameterised over `A` / `cM` / `m` (exactly `AmTΠ`'s parameters), everything
in the "no" rows belongs beside `StepExt` in `NbEPDirDBLibAmrec`, and **the
whole three-split pattern becomes a combinator**: "a step that case-splits `n`
times on `natrec` scrutinees is IH-extensional if each leaf is".

### Why this is worth doing

The judging criterion is `WF-LIBRARY.md`'s: an abstraction is judged by how
simple it is to USE; build cost amortises, use cost is paid by every caller.
Right now the reusable machinery is ~600 lines that the NEXT recursive function
would have to rewrite, and the genuinely function-specific part (the leaves) is
the small, cheap half. That is the wrong way round.

### Notes / constraints discovered while building it

- ⚠ **Cost forced a ten-module split.** All of it in one module OOM-killed at
  the cgroup cap on a 7 GB box. What worked, in order of effect: `where` →
  top-level Defs (leaf 4: OOM → 10s); one module per expensive term; naming
  `eqG-red`'s two instances (`split2` alone: OOM → 4.8s). A library version
  should be laid out this way from the start.
- ⚠ **Lifting is NOT universally cheaper.** The same move that rescued `leaf₃s`
  from an OOM cost 13x when applied to `gcd-gt-term`'s intermediate scrutinees
  (31s → 6m35s), because `where`-bound definitions are elaborated once per
  clause while top-level functions of the clause's parameters are re-unfolded
  at every use. The rule that holds is "one big term per Def", not "always
  lift".
- ⚠ **`eqG`'s motive boundaries are `refl` only at variables.** In the splits
  every slot is a variable and `subTy` computes; instantiating at an abstract
  carrier needs `eqG-sub`, because there `extS σ` meets a `w`.

## The arithmetic library is REDUCTION-BIASED — audit it for the propositional half

**Observed 2026-08-18, from closing equation 4's bridge.** Four ordinary
arithmetic facts had to be built from scratch before gcd's `a ≤ b` branch could
even be stated at variables:

| built | what it is |
|---|---|
| `congPred` | congruence under `predTm` |
| `⊢monus0` | `0 ∸ b ≡ 0` |
| `⊢monusSS` | `suc a ∸ suc b ≡ a ∸ b` |
| `congAt` | one-hole congruence at `Nat` |

None is exotic. The pattern in what was missing is the point:

**The library had the REDUCTION (`⟶*`) form of nearly every monus fact and
almost none of the PROPOSITIONAL (`Id`) form.** `monus-zero`, `monus-suc`,
`pred-suc`, `pred-zero`, `mlt-chain` are all `⟶*`. That is exactly the wrong
bias for "at variables" results, because a `⟶*` premise forces its subject
GROUND — a variable never reduces — which is precisely why equation 4 was
unreachable for months and why equation 3 is stuck at *numeral `b`*.

**Congruences were missing too.** `congS` existed (for `nsuc`) and nothing else,
so every step that moves an identity under a former had to be invented at the
point of use.

### The audit worth doing

1. **For each `⟶*` lemma in `…ExamplesDiv` / `…LibArith*`, ask whether the `Id`
   form exists.** Where it doesn't, ask which "at variables" theorem it blocks.
2. **Enumerate the congruences.** One per Nat former (`nsuc`, `predTm`,
   `plusTm`, `monusTm` in each argument), plus the general one-hole `congAt`
   now in `…LibArithMonus`.
3. **Order facts.** `Hom Nat` COMPUTES (`Hom-Nat-z`/`-sz`/`-ss`), so inversion,
   ex-falso and `0 ≤ n` are conversions rather than lemmas — but transitivity,
   antisymmetry and `≤` vs `∸` bridges beyond `⊢monusLe` are not, and each is a
   candidate premise for a "at variables" statement.

### Why it pays

The test for whether a missing lemma matters is the one this session used:
**does its absence force a premise that variables cannot discharge?** That is
the difference between a theorem and a vacuous one, and this repo already has a
post-mortem on two lemmas that were `--safe`, hole-free, green and vacuous.
Every propositional fact added widens what can be stated at variables; every
`⟶*`-only fact silently narrows it.

## The WF libraries do not insulate their clients — every OOM is at a use site

**Measured across 2026-08-18/19, not inferred.** Every OOM this session landed
in an `Examples` module instantiating a library, never in a library:

| where | |
|---|---|
| `irrAt` (`…GcdRec`) | OOM with ~9GB headroom |
| `gcd-gt-eq` as one term | 75 min, never finished |
| `⊢Fnr` (`…GcdLeMid`) | OOM twice — 2m04s as one term, 1m50s split into 5 `Def`s |
| `…LibAmrec` | ~53s **green** |
| `…LibNatrec` | seconds |

### The mechanism, isolated by `…ExamplesAbsProbe`

Same `irrSplit` rung, varying only what is held abstract as a module parameter:

    stp        ext          total    marginal
    ABSTRACT   ABSTRACT      5.4s    —
    gcdStp     ABSTRACT     17.5s   12.1s
    gcdStp     gcdStepExt   15.3s    9.9s

⇒ the cost is the **concrete step term, in the TYPE**. `irrT` mentions
`auxAt`, which mentions `auxS x`, which carries `stp`. `⊢Fnr`'s type is five
nested `subTy`s over `G3`, and `G3` carries the same material.

### Why this is an ABSTRACTION problem and not just "big proofs"

`AmTΠ` *is* parametrised over `stp` — that part is right, and it is why the
library itself compiles. But its exported **types mention the parameter**, so
the parametrisation does not insulate the client: a use site pays
proportionally to the step term at **every mention**, and an assembly has many.

⚠ By this project's own stated priority — *libraries may be slow, use sites must
be simple and fast* — the WF libraries currently FAIL, because the cost lands
exactly where it was not supposed to.

### The remedy is already demonstrated — `irr-at`

`irrAt` resisted NINE fixes. What worked needed BOTH halves at once:

1. **Do the elimination inside the parametrised module**, where `stp` and `ext`
   are still variables. (5.8× on the rung.)
2. **Return `Prv`, never a raw `⊢` judgement.** A type naming the witness —
   `Δ ⊢ app (prvTm (irr-ind ext …)) n₂ ∷ …` — forces the whole assembly just to
   STATE it, and kills `…LibAmrec` outright.

Generalised: **a type that names a witness pays for that witness at every
mention; `Prv` exists to prevent exactly that.**

### The audit

1. For each WF library export, ask: does its TYPE mention `stp` (directly, or
   via `auxAt`/`G3`/`irrT`)? If so, the client pays per mention.
2. Where it does, can the work move inside the parametrised module and export a
   `Prv`-wrapped (or otherwise witness-free) result?
3. `⊢Fnr` / the eq-4 assembly is the live instance: structurally correct,
   OOMs, and the first thing to try is `AbsProbe`'s abstract-then-instantiate.

## Once: a DATATYPE DECLARATION carries no totality obligation — design it out

**The trap, in Agda.** Agda's coverage checker checks **functions, not
datatypes**. A `data` declaration that is missing a constructor is a
perfectly well-formed declaration: it type-checks, the module compiles
green, and nothing anywhere is obliged to notice. The omission surfaces
only where some later *function* is finally required to produce the
missing constructor — which in OCP-0009 is several modules and many
minutes of proof-checking downstream, as a bogus-looking unification
error rather than "you forgot a case".

Concretely: adding a term former to `RTm` and forgetting to add its row
to the SN layer (`SNe`/`SN`/`SNRed`/`Ne`) is invisible until `fund` is
obliged to build one. It happened with `ordtr` (2026-08-05 → 06) and
again with `icon`/`ielim`/`⌜IMu⌝` (2026-08-22), and the only thing that
caught either was an out-of-band shell script,
`DirectedHoTT/tools/check-formers.sh`, which greps the Agda source.

**Why the asymmetry is the tell.** The development already has TWO
per-former layers that need no such script, and the script's own header
says why:

> NOT CHECKED, deliberately — these are protected by a producer's own
> coverage: `Canon`/`Prog` — `prog` must return a canonical form or a
> step for every former, so its coverage forces the decision.
> `⊩₀`/`⊩₁` rows — `fund-ty` must build an interpretation for every
> `⊢ty`.

So wherever a **total function** must produce something per former,
Agda enforces it for free. The gap is exactly the layers that are
**datatypes**.

**What Once could do about it.** Three options, in increasing order of
how much they change the language:

1. **A derived-datatype obligation.** Let a datatype declare itself
   INDEXED BY another datatype's constructors, with the checker
   demanding one row per constructor — the datatype analogue of
   coverage. Cheap, local, and it is the whole content of
   `check-formers` checks 1 and 2.

2. **Generate the layer from a DESCRIPTION.** This is the one OCP-0009
   is already building the machinery for. If the syntax is a `Desc` /
   `IDesc` rather than a hand-written `data`, then the SN layer, the
   logical relation, and the classifiers are all *computed from* that
   description. A former with no row is then not a silent omission —
   it is not expressible. ⚠ This is the dogfooding target, and it is
   the reason the indexed increment matters beyond `Vec`: the payoff is
   not "we can write `Vec`", it is "the metatheory layers stop being
   hand-maintained parallel lists".

3. **Make the classifiers total by construction too.** `check-formers`
   check 3 exists for the same reason one level down: a *function's*
   catch-all (`stkC? _ = false`) IS total, so coverage is satisfied and
   the decision is silent. That is not a datatype problem, so option 2
   does not fix it; it needs the classifier to be derived from the
   description as well, or a `--no-catch-all` discipline on the ones
   that are semantically per-former.

⚠ Cost of NOT doing this, measured 2026-08-24: `⌜IMu⌝` inherited the
catch-all `false` from three classifiers at once (`stkC?`, `stkA?`,
`stablecd?`). The consequence was not an unprovable goal — it was that
**progress was FALSE**, and it took a new reduction rule (`tr-J-IMu`)
threaded through eleven modules to fix. A one-line row at the time the
former landed would have prevented all of it.
