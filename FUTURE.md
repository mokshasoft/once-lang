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

## Once: "ORDO TYPES" — carry a COST BOUND in the type, and compose it

**The idea.** A function's type carries a complexity bound alongside its
value type, and the bounds *compose* when you apply or pass functions —
so `map`'s cost is a function of its argument's cost. Ask the compiler,
or the language server, and you are told the complexity of what you just
wrote instead of having to run it and time it.

### What provoked it, measured 2026-08-26

`DirectedHoTT/Examples/Knot/Sz.agda` assembles a 53-method tuple. Three
versions were written, all correct, differing only in how one rung is
discharged. Cold, on a 7.7 GB box:

| rung discharged by | cold |
|---|---|
| plain (Agda normalises `renTy vs` through the tail) | 140s ✓ |
| a cast along `imethsTyFrom-ren` | 350s ✓ |
| `ren-ty … there` | OOM |

Nothing in any type distinguished them. It took three ~4-minute runs to
learn that all three are **O(n²)** — `ty-Σ`'s second argument sits at
`Γ ▹ A`, so the whole remaining tail is traversed at every one of 53
rungs — and that the fix is not a better rung but to stop *enumerating*
rungs (a generic induction at an ABSTRACT tail is O(n) once). The same
lesson had already been paid for once that week: `Lib/IPay.ipayTy-wf`
took `cTm-ordtr` from OOM to 3.7s for exactly this reason.

⚠ **And note what an Ordo type would NOT have caught.** Big-O quotients
out constants, and 140 vs 350 vs OOM is a *constant-factor* difference
among three O(n²) programs. What it *would* have caught is the real
defect — "this rung is O(tail), so the chain is O(n²)" — at the
definition site, which is the diagnosis those three runs bought. ⇒ Ordo
types catch SHAPE errors early and cheaply; a profiler is still what
tells you about constants. Complementary, not competing.

### Prior art, so this is not invented from scratch

- **Danielsson, POPL '08**, *Lightweight Semiformal Time Complexity
  Analysis for Purely Functional Data Structures* — a tick/thunk monad
  with the cost in the index. ⚠ Note this is **in Agda**, so "not
  expressible in a dependent type theory" is not the obstacle.
- **RAML** (Hoffmann et al.) — *infers* polynomial bounds automatically
  for a first-order fragment by reduction to linear programming. The
  evidence that inference is feasible if the fragment is restricted.
- **Granule / Idris 2** — graded types over an arbitrary ordered
  semiring; one framework serves usage, security *and* cost.

### The structure it wants

Costs form an **ordered semiring**: sequential composition ADDs, a call
under a loop MULTIPLIES, and `≤` gives weakening (an O(n) function is
usable where O(n²) was demanded). Then

    f : A →[p] B     g : B →[q] C     ⇒   g ∘ f : A →[p + q] C

★ **Higher-order is where a TYPE earns its place over an analysis.**

    map : (A →[c] B) → List A →[n · c] List B

is *cost-polymorphic* — the bound is a variable abstracted over the
argument's cost. No profiler can give you that; it is a typing
discipline or nothing.

⚠ **The hard part is value-dependence.** `sort` is O(n log n) in the
*length*, so the grade must be indexed by a MEASURE of the input, which
drags the cost algebra into the dependent setting.

### Why Once is unusually well placed

1. `Hom Nat` **computes** here, so ordering facts are conversions rather
   than proof obligations (`Eq 4: order premise + bridge`).
2. The WF axis already puts a measure `μ : A → Nat` **in the type** of
   `⊢amrec`. A function defined by measure recursion already carries its
   own measure — the gap from "measure that justifies termination" to
   "measure that bounds cost" is small, and the expensive half is paid.
3. Once's surface is **already graded** (QTT `{0,1,ω}`). Generalising
   that semiring from usage counts to a cost algebra is the natural
   move, and Granule is the existence proof that one grade framework
   covers both.

### Risks, stated up front

- ⚠ **Infection.** This is exactly why `no-sized-types` is a hard ban
  here: an index that every signature must carry infects the whole
  development. Granule's answer is that grades are INFERRED by default
  and surface only where constrained. Decide this before module 200,
  not after.
- **Incompleteness is not optional** — bounds cannot be inferred in
  general. The practical shape is therefore *gradual*: infer and show as
  an inlay hint over the decidable fragment, CHECK where the programmer
  writes the bound down. Same bargain as gradual typing.

### Addendum 2026-08-26: cost is a property of an INSTANTIATION, not of a function

A back-to-back measurement in `Knot/Sz` sharpened the Ordo idea in a way
worth writing down, because it is the case a naive cost type gets wrong.

`Lib/IPay` has two generic lemmas of the same shape — each replaces a
hand-built chain with one induction. One is a large win, the other is a
loss, **and the difference is not in the lemma**:

| lemma | consumer | result |
|---|---|---|
| `ipayTy-wf` | needs it ONCE per method, argument abstract | `ordtr` OOM → 3.7s |
| `imethsTyFromNat-wf` | a 53-rung ENUMERATION, argument concrete each time | 147s → OOM |

⇒ **A generic lemma is only generic if its argument stays abstract at the
use site.** Instantiated at a concrete 53-element description, Agda
unfolds the induction 53 deep at every rung — the same O(n²) it was meant
to remove, now building derivations instead of normalising types.

**What this means for an Ordo type.** The cost of `imethsTyFromNat-wf` is
O(1) applied abstractly and O(n) applied concretely. So a bound attached
to a *definition* is not enough; the grade has to be a function of how the
argument is instantiated — which is the dependent, value-indexed case
(`sort` is O(n log n) *in the length*) showing up in the metatheory rather
than in user code. ⚠ A cost system that grades definitions only would
report both lemmas as wins here, and be wrong about one of them.

--------------------------------------------------------------------------
## Once: de Bruijn INDICES make a variable reference context-BOUND — should levels be an option?

Raised 2026-08-28 while writing `Examples/Knot/Lookup`, OCP-0009's first
judgement row.

### The observation

This does not type-check, and asking why turns out to be worth writing down:

```agda
A₃ : {Γ : Cx} → RTm Γ
A₃ = var (vs (vs (vs vz)))          -- ✗
```

⚠ **And it SHOULD not.** `{Γ : Cx} → RTm Γ` says "usable in ANY context,
including `ε`" — i.e. CLOSED. `⌜Nat⌝`, `nzero` and the sort tags really are
closed, which is why they are polymorphic and work. `var (vs³ vz)` is not:
it denotes the fourth variable from the inside and needs a context at least
four deep. Agda is refusing a scope error. **Nothing is broken.**

### But the friction underneath it is real, and it is NOT polymorphism

Writing that row, the actual cost was keeping **two encodings of the same
index in sync by hand**:

| | the term level | the derivation level |
|---|---|---|
| the k-th field | `var (vs^k vz)` | `⊢var (there^k here)` |

Every `iκ`'s code counts one way and its `IConWf` counts the other, and the
count changes per field *and* per binder the type sits under. Most of the
iterations on `lkHere` were off-by-one between these two, not anything
semantic. Same story in `Knot/Build`, `Knot/WkRows` and `Lib/IWk`.

### Two candidate fixes, at different levels

**(a) POC-level, and the cheaper one: generate the row's `IConWf` the way
`Lib/IWk` generates methods.** `Lib/IWk` walks an `ICon` generically and
never names a de Bruijn index; that is exactly why it has no off-by-one
class of bug. A judgement row's well-formedness is the same shape of walk.
⇒ this is a library job and needs no language change.

**(b) Language-level: de Bruijn LEVELS instead of indices.** A level is
stable under context EXTENSION, so a variable reference genuinely would be
context-polymorphic (at any context deep enough), and `A₃` above would be
legal. That is the standard answer to this exact complaint.

⚠ **The cost is not small and should be stated before anyone tries it.**
Levels make WEAKENING free and SUBSTITUTION expensive — every `subTm` has
to renumber — where indices do the reverse. This POC's whole
`renTm`/`subTm`/`extS`/`wk-single` layer, plus `Spec/Variance`'s `occTm`,
is index-shaped, and the metatheory rests on it. So this is a design axis
to evaluate on its merits, not a fix to retrofit.

### What would decide it

The `ap`-landing test the other axes use: does levels-vs-indices remove a
class of *proof* obligation, or only a class of typo? Everything seen so
far is the latter — off-by-one errors that Agda catches immediately. ⇒ on
current evidence **(a) is the one worth doing** and (b) is a note, not a
plan. Revisit if a judgement row turns out to need a variable reference
that must survive weakening *propositionally* rather than definitionally —
that would be a real obligation and would change the verdict.

## Once: TACTIC-STYLE HOLE FILLING — a syntax-directed search for the forced steps

**Where the idea came from.** Encoding OCP-0009's judgement layer produced
thousands of lines of *derivations* that a human never chose: coercion
chains (`toI`/`fromI`/`toMu`/`fordAs`), `⊢ty` well-formedness, `⊢pair`
telescope tuples, `⊢wk` depth derivations. They are generated today by a
Python emitter that has to know each rule. Idris2 has `auto` / proof
search for exactly this class, and Agda has Agsy.

★ **MEASURED, not assumed.** Replacing all 24 `⊢pair` well-formedness
arguments in `Examples/Knot/TyRedWf` with `_` gives **24 unsolved metas** —
so plain unification does *not* determine them. They are derivations, and
`_⊢ty_` has eleven constructors with no proof irrelevance.

⇒ **But that is the argument FOR a search.** The goals are strictly
syntax-directed: a goal `Γ ⊢ty Σ' A B` admits only `ty-Σ`, and its
subgoals follow the telescope's shape. Depth-first with the goal's head
selecting the rule closes all 24. This tier is most of the *volume* of a
mechanised metatheory.

### ⚠ What it would NOT do, and this is the point

The expensive steps in `SUBTM-ATTEMPTS.md` and `JUDGEMENT-ATTEMPTS.md`
were **not** unfilled holes. They were:

* `IsNum` instead of closedness — closedness cannot cross a substitution;
* `fordMap` — a κ ford is not a copy under substitution;
* an explicit general depth instead of `sucs j (var x)` — which does not
  unify;
* a tagged index for the mutual pair;
* `iρ` versus `icw-imu` for a foreign premise.

**In every one the goal itself was wrong.** A search fills a hole; it
cannot tell you the hole is in the wrong place. ⇒ do not sell this as a
silver bullet, and do not let it hide interface errors by making a wrong
statement *provable-looking*.

### ★ The real value: turning thinking into mechanism, and failing faster

Two concrete wins, both worth having:

1. **Volume.** The bookkeeping tier stops being hand- or generator-written.
2. **Faster refutation.** If the search *cannot* close a forced-looking
   goal, that is evidence the statement is wrong — arriving in seconds
   rather than after a hand-written attempt. Several of the corrections
   above took multiple attempts precisely because "this should be
   mechanical" was never tested cheaply.

### Design notes for Once

* **Syntax-directed first, not general resolution.** The win comes from
  the goal's head determining the rule; unrestricted search is what makes
  these tools unpredictable.
* **Budgeted and reported.** A search that silently gives up is
  `verification-that-covers-less-than-it-claims`; it must say what it
  could not close, by name — the same contract the row emitters have.
* **Never across an interface boundary.** If closing a goal requires
  inventing a lemma statement, refuse and report: that is the tier where
  a human is deciding what the statement should be.

---

## LIBRARIES: an INTERFACE / IMPLEMENTATION split, once the use sites settle

A library module today exports its signatures **and** every proof behind
them, and a client importing `Lib/IPay` gets all of it. The proposal is
the same split the kernel already has: an interface naming what a client
may rely on, an implementation holding the proofs.

### ⚠ The obvious justification is NOT supported by our measurements

"Clients pay to import the proofs" sounds right and this POC's own
numbers do not back it:

* interface **size** does not predict cost — `RedWfB` has a 2413 KB
  `.agdai` and checks in 5s; `JudgeWfA` has ~955 KB and took 125s;
* in the one usable profile, `Deserialization` was **3.7s of 99.6s**.

So the split should not be sold as an import-cost win until somebody
measures one. ⇒ do not cite this section as evidence that it is.

### ★ The mechanism that WOULD pay is `abstract`, and it is a different one

Agda will not unfold an `abstract` definition during conversion checking.
Cost in this POC lives in elaboration and conversion, not in loading, so
an interface whose bodies are `abstract` stops clients from unfolding
proof terms they never needed to see. That is a real lever and it is
about **unfolding**, not about bytes.

⚠ It is also a semantic commitment, not a repackaging: anything a client
proves by `refl` through a library definition breaks the moment that
definition becomes `abstract`. The split therefore has to wait until the
use sites say which equations clients actually depend on — which is
exactly the sequencing already proposed: **do it when the interface is
observed, not guessed.**

### ★ And it is the prerequisite for the documentation loop below

An interface is the surface a document can describe. Generating docs for
a module that exports 60 lemmas, 45 of them internal, documents the wrong
45.

---

## LIBRARIES: DOCUMENTATION CONVERGED BY AGENT EVALUATION

Generate per-library documentation, then **test it** by giving it to an
agent with a use site whose solution we already have, and comparing what
the agent writes to what is in the repo. Failures become documentation
deltas; iterate until they stop.

### ★ Why this is worth doing: the failure it targets is our most frequent one

Not "the proof was hard" — *"the library already had it and I rebuilt
it."* Three instances in a single day (2026-08-31):

* `⊢motAppK` — already exactly the `subAtK` wrapper; I began rebuilding
  it from `βsnd`/`βfst`/`sortMap-red` before looking.
* the emitter's `DD` role — already consumed the prepended depth; I added
  a `DDEP` role that emitted it twice and silently dropped an argument.
* `methsAt` — built for `pw?`, which turned out not to need it.

⇒ the eval question is sharp and mechanical: **did the agent find the
existing thing, or write a second one?** That is checkable without
judging proof style.

### ⚠ The experiment is only valid if the agent CANNOT read the answer

The agent has a repo. If it can `grep` the library bodies or the existing
call site, it will find the lemma and the documentation is never tested —
the run measures the search, not the doc. So the harness must hand it
**the document and the goal, and nothing else**: no `Lib/**` bodies, no
the module that already solves it. Getting this isolation wrong produces
a green result that means nothing — `verification-that-covers-less-than-
it-claims`, in a new place.

### Design notes

* **Held-out use sites, rotated.** Iterating docs against one fixed site
  converges to a doc that solves that site. Keep a pool; report per-site.
* **Record the failure MODE, not just pass/fail.** "Rebuilt an existing
  lemma", "found it but mis-instantiated", "could not state the goal" are
  three different doc bugs — the first wants a discoverability index, the
  second wants an example, the third wants the interface.
* **Two audiences, and they want opposite documents.** A user needs "what
  do I call and what does it cost me"; a library dev needs "why is the
  premise shaped like this and what was tried instead". The attempts logs
  (`SUBTM-ATTEMPTS.md`, `JUDGEMENT-ATTEMPTS.md`) are already the second
  document — do not let the first swallow them.
* **The cost model belongs in the doc.** Half this POC's dead ends were
  cost, not correctness (`half-generalization-is-worst`,
  `meta-standing-for-a-computation`). A signature that is cheap to *use*
  and ruinous to *build* is exactly what `judge-abstractions-at-the-use-
  site` says to record.

## Once: THE BUGS AGDA CANNOT SEE — and how many of them are mechanizable ANYWAY

⚠⚠ **This section starts by CORRECTING ITS OWN PREMISE.**
`DirectedHoTT/JUDGEMENT-ATTEMPTS.md` §13 classified nine real defects
from 2026-09-01 and concluded that a type checker "cannot see" the
correspondence between `Spec/Typing.agda` and the emitted rows. The
first half was measured; **the second half was wrong**, and the objection
that broke it was one sentence long: *"it is just Agda that can't find
it, right? Why can't `length X == length Y` be an invariant?"*

★ It can. Agda cannot see a correspondence **nobody wrote down**. Written
down, it checks it. `Examples/Knot/Census` is the demonstration and it is
now in the sweep.

### What was actually blocking it — and it was not Agda

The rules live in `Spec/Typing.agda` as **datatype declarations**. The
generator reads them by **parsing text in Python**, so the left-hand side
of the correspondence lived outside the logic and every invariant about
it had to be a script assertion. ⇒ the missing ingredient was never
expressiveness; it was **reflection** — a way to make the declaration a
value the logic can compute over.

### ✅ What is mechanizable TODAY (and now mechanized)

**Measured 2026-09-01: `Agda.Builtin.Reflection` works under `--safe`.**
`getDefinition` on a `data-type` yields its constructor list at
type-check time. So:

| invariant | mechanism | status |
|---|---|---|
| how many rules the SOURCE has | reflection (`rules _⊢_∷_ ≡ 32`) | ✅ `Knot/Census` |
| how many rows the ENCODING has | ordinary Agda — `IDesc` is a first-order list, so `ilen D` and `refl` | ✅ |
| **the two, RELATED** — `ilen JudgeD + 5 ≡ srcJudge` | an equation, checked in the sweep | ✅ |
| a rule ADDED to `Spec/Typing` with no row | falls out of the same equation | ✅ **new coverage** |

⚠ And the control was run: a deliberately wrong count is a type error
(`2 != 99 of type Nat`). An assertion that cannot fail proves nothing.

★★★ **This replaces a Python ratchet with a THEOREM.** The ratchet was a
FLOOR (`Judge ≥ 34`) and on 2026-09-01 the row count went 51 → 49 → 51
while depth bugs were being fixed — **the floor saw nothing, because a
floor only catches a fall below ITSELF.** The census is an exact
equation; drift is a type error, in the sweep, for free.

### ⬜ What is mechanizable but NOT YET done, in Agda as it is

1. **NAME-level correspondence.** Reflection yields constructor NAMES,
   not just their count, and the emitter derives each row's name from the
   rule's. `primQNameToString` + the emitted names would check that every
   constructor of `_⊢_∷_` has the row it should, not merely that the
   totals agree. Counting is the cheap shadow; this is the next rung.
2. ★★★ **The adequacy map, `enDeriv`.** THE tier that makes the
   *dangerous* class impossible rather than unlikely — a well-formed row
   that encodes the WRONG RULE (`dwf-cons` emitting `DescWf C` for
   `DescWf (C ◃ E)`, which typechecked). A total function
   `Γ ⊢ t ∷ A → ⟨inhabitant at ⌈Γ⌉ ⌈t⌉ ⌈A⌉⟩` cannot be written for such a
   row, because its TARGET TYPE names the index. `Knot/Map`'s
   `enTy`/`enTm` and `Knot/SzAgree` already do exactly this **for the
   syntax**; there is no `enJudge`.
   ⇒ and it is not extra work: `prog`'s type mentions `_⊢_∷_`, so step 4
   needs this correspondence anyway.
3. **Coverage, as opposed to correctness.** Two 2026-09-01 defects were
   neither: a spike left `JudgeWfJ`–`Q` as real files the sweep would
   have checked GREEN, and `check.sh` returning 0 off a cached `.agdai`
   checks nothing. These are properties of the BUILD, not of any module,
   and no in-language invariant reaches them. A content-addressed build
   would; that is a tooling item, not a language one.

### ★ What Once could do that Agda makes awkward

* **Make the declaration a value.** Everything above is reflection
  working around the fact that a datatype declaration is not data. The
  knot exists to make `RTm` a kernel type; the same move applied to
  JUDGEMENTS means the correspondence is stateable **without** a
  reflection macro and without a Python parser — one language, one
  artifact, `enDeriv` an ordinary function.
* **Totality obligations on a declaration** — see the section above on
  datatype declarations carrying none. A generated family whose row count
  is part of its INTERFACE cannot drift.
* **An adequacy obligation as a first-class notion.** "This encoding is
  faithful to that declaration" is the proposition we keep re-proving by
  hand (`LookupGen`, `SzAgree`, `WkRows`) and never state once.

⇒ ⚠ **the honest summary: of the four defect classes Agda missed, ONE was
never a language problem (counting — now checked), ONE is ordinary work
we have not done (`enDeriv`), and TWO are build-system properties.** None
of them is evidence that the checking is inherently manual. "Rely on
inspection with scripts" was the wrong conclusion and this section is
the retraction.

### ⇒ SO WHICH OF THE CHECKING SCRIPTS CAN GO? — audited 2026-09-01, and mostly NOT

Asked directly once `Knot/Census` landed. **One thing is subsumed. The
rest check different properties, and two Agda facts had to be MEASURED
before the answer was even stable — I had the first of them backwards.**

    ✅ MEASURED: `--safe` BANS `postulate`          (`SafeFlagPostulate`)
    ✅ MEASURED: `--safe` PROPAGATES through imports (`CoInfectiveImport`)

| script | verdict |
|---|---|
| `gen-knot.py`'s `_FLOOR` ratchet | ✅ **SUBSUMED** by `Knot/Census` — and strictly improved: a floor cannot see 51 → 49, an equation can |
| `poc/OCP0009/check-mf.sh`, `poc/OCP0009/check-formers.sh` | ⚪ **dead already** — `sweep.sh:24` never builds that tree. Deleting them is housekeeping, not a consequence of anything |
| `tools/check-trust.sh` | 🟡 **its CONTENT checks are redundant with `--safe`** (postulates, `TERMINATING`, `NO_POSITIVITY_CHECK`, `primTrustMe` are all rejected outright; holes stop the check). What remains is ONE thing: **that every file declares `--safe` at all** |
| `tools/check-formers.sh` gates 1–3 | 🟡 **encodable, not yet encoded** — "every `RTm` former appears in the SN layer" is a NAME-LEVEL correspondence between two datatypes, exactly what reflection does |
| `tools/check-formers.sh` gates 4–6 | ⛔ **not propositions** — vacuous rows, promissory notes, and conditional lemmas with NO CONSUMER are statements about the ABSENCE of something across the whole program. A review list, honestly labelled as one |

★★★ **AND THERE IS A REAL FIX AVAILABLE FOR `check-trust.sh`.** Because
`--safe` is co-infective, a single `--safe` module importing the WHOLE
tree makes Agda enforce the trust surface transitively. `Trust.agda`
claims to be that module — *"it is not a promise, it is checked"* — and
imports **zero** modules; the checking is entirely in the shell script.
⇒ give it the full import list and the script shrinks to the one question
that is genuinely a filesystem property: **does the import list name
every `.agda` file?** That is a `find | diff`, not a 25-line scanner.

⚠ The residue is real and worth naming: a module NOTHING imports is
invisible to the language, whatever we do. It is the same class as the
stale `JudgeWfJ`–`Q` files and a green `check.sh` off a cached `.agdai` —
**coverage, not correctness.** Those three want a content-addressed
build, and no in-language invariant reaches them.

### ★★★ THE CATEGORIES — every defect class that survived `--safe`, audited from the git history

Assembled 2026-09-01 by reading ~1000 commits for the ones whose subject
admits a defect that TYPECHECKED. ⚠ The striking result is how many were
called unencodable and are not: **A, E and most of F were closed within
one session, once the question "why can't that be an invariant?" was
asked instead of assumed.**

| | category | it actually happened | Agda TODAY | Once |
|---|---|---|---|---|
| **A** | **DATATYPE COVERAGE** — a declaration missing a row. Agda's coverage checks FUNCTIONS, not datatypes | `ordtr` absent from the whole SN layer (2026-08-05→06); `icon`/`ielim`/`⌜IMu⌝` (2026-08-22) | ✅ **NOW CHECKED** — `Metatheory/FormerCensus`, by reflection, and it NAMES the orphans | §"a DATATYPE DECLARATION carries no totality obligation" opts 1–2: a derived-datatype obligation, or generate the layer FROM the description |
| **B** | **A CATCH-ALL HIDING A MISSING CASE** — `_ = false` makes a function total, so coverage is satisfied and the omission is SILENT | `spine?`/`stablecd?` inherited `_ = false` for `icon`/`ielim` — THREE silently wrong answers, `--safe`, zero warnings (`25602107`) | ✅ **NOW PINNED** — `FormerCensus` asserts the catch-all's EXTENT (`spine?` 12 of 30, `stablecd?` 7); adding a former moves the number and FAILS. ★ AND Agda has a native flag we were not using: `--exact-split -Werror` makes a catch-all a hard error, by clause — see below | option 2 again: a function generated from a `Desc` has no catch-all to inherit. This is the strongest argument for the dogfooding target |
| **C** | **VACUITY** — a true theorem that says nothing | `subTI` quantified over an arbitrary env-top, so `consistency` was VACUOUS; `gcd-gt-gen`/`gcd-le-gen` premises uninhabitable at variables (`5edcde10`) | ⛔ not in general — an implication with an unsatisfiable premise is a fine proof | ★ **the real idea: a hypothesis OWES A NON-VACUITY WITNESS.** `∃ args. premise args` IS a proposition. Once could demand one per conditional lemma — `check-formers` gate 6 is the shadow of it |
| **D** | **ENCODING CORRESPONDENCE** — a well-formed row that encodes the WRONG RULE | `dwf-cons` emitting `DescWf C` for `DescWf (C ◃ E)` (2026-09-01) | ✅ **COUNTS** (`Knot/Census`) **AND VALUES** (`Knot/Adequacy`, 32 checks against `Knot/Map`, generated) — CONTROLLED: reintroducing the `◃` bug makes it a type error. ⬜ Row STRUCTURE/fords still want a full `enDeriv` | make the declaration a VALUE, so the correspondence is an ordinary function rather than a reflection macro over a Python-parsed source |
| **E** | **CLAIM / COMMENT DRIFT** — a header asserting "N of M" that is false | two stale census claims in `Knot/Terms`, 32 → **13** (`da699bd1`); stale ⬜/⛔ markers (`ef6e408b`, `cbb181cd`) | ✅ where NUMERIC — turn the claim into a `refl`; that is exactly what `Knot/Census` is | claims in the doc layer that are checked, not prose |
| **F** | **BUILD COVERAGE** — a file the checker never reaches | stale `JudgeWfJ`–`Q` the sweep globbed GREEN; `check.sh` rc=0 off a cached `.agdai`; a module with no `--safe` line | 🟡 mostly — `--safe` is CO-INFECTIVE, so `Trust.agda` importing the tree enforces it; the residue is `find \| diff` | content-addressed build; a project manifest that is itself checked |

⇒ ★ **the honest scoreboard: of six categories, ONE (A) was closed
outright this session, TWO (E, F) were closed in the part that matters,
ONE (D) is half-closed with the other half being ordinary work we have
not done, and TWO (B, C) are genuinely open.** "Rely on inspection with
scripts" was true of none of them by the end.

⚠⚠ **And C is the one worth Once's attention**, because it is the only
one where the obstacle is not tooling. `subTI` is the sharpest instance
in this repo's history: `--safe`, zero holes, a green build, and
`consistency` proved nothing at all. A language that made
*"this hypothesis is inhabited somewhere"* an obligation would have
caught it at the definition, not months later.

### ★★★ CATEGORY C IN DETAIL — can VACUITY be checked automatically?

Asked directly. The answer splits, and the split is the useful part.

#### ⛔ In general: NO, and it is a THEOREM, not a tooling gap

"Is this premise inhabited?" is inhabitation in a dependent type theory,
i.e. **provability** — undecidable. There is no complete automatic
vacuity checker for the same reason there is no complete prover. ⇒ any
proposal that *decides* vacuity is wrong; the question is what to do
instead.

#### ★ The move that works: turn a DECISION into a CERTIFICATE

Undecidable to decide, trivial to CHECK:

    lemma   : (x : A) → P x → Q x
    lemma-ne : Σ A P                  -- ⚠ OWED, and type-checked

Exhibiting a witness is ordinary type-checking. This is the same trade
the whole development already makes everywhere else — and it would have
killed **both** of this repo's real instances outright.

⚠⚠ **BUT A NAKED WITNESS IS NOT ENOUGH, and `gcd-gt-gen` is exactly why.**
Its premise IS inhabitable — at LITERALS. The lemma was stated at
VARIABLES, where `monusTm` is stuck and the premise is not. So "P is
inhabited somewhere" would have been discharged and the lemma still
proved nothing where it lived.

⇒ ★★★ **the obligation has to be tied to a USE SITE, not to existence:**

    a conditional lemma owes a CONSUMER, and the consumer must
    DISCHARGE the premise at the arguments the lemma is stated for.

That is decidable (a call-graph question) *plus* type-checked (the
consumer must actually build the premise). `5edcde10`'s own diagnosis was
literally *"asking what exercises these lemmas showed nothing does"* —
the check is the question, mechanized. And `subTI` fails it for the other
reason: its consumer could not supply the env-top.

#### ✅ Sound-but-incomplete things that ARE automatic today

* **structurally empty premises** — `⊥`, a datatype with no constructors,
  or a constructor set empty at the given indices. Agda already decides
  this: it is what an `()` pattern IS. `Examples/Vec.no-cons-at-zero` is
  this repo's own instance.
* **dead conditional lemmas** — `check-formers` gate 6. A graph property,
  decidable, already implemented; what it lacks is teeth, being a review
  list rather than a gate.

#### ⇒ and the user's sharper version — "forget a use-site for all BRANCHES"

★ **That one is not category C at all — it is category A pointed
backwards, and it is mechanizable with the machinery just built.**

    A  every constructor has a ROW        (production coverage)  ✅ FormerCensus
    A′ every constructor has a CONSUMER   (consumption coverage) ⬜ same technique

`Metatheory/FormerCensus` reflects over a datatype's constructors and
checks each is MENTIONED across a set of layers. Pointed at consumers
instead of producers, the identical macro answers "which branch does
nothing ever use?". ⚠ Mentioning is still the cheap shadow of exercising
— but it is exactly the shadow that caught `ordtr`, and the asymmetry is
worth naming: **we check that everything is PRODUCED and never that
anything is CONSUMED.**

#### what Once should take from this

1. **A conditional lemma owes a discharging consumer** — the strongest of
   the three, and the only one that catches `gcd-gt-gen`.
2. **Consumption coverage as a first-class obligation**, dual to the
   totality obligation already proposed for datatype declarations.
3. ⚠ **Do NOT promise a vacuity decision procedure.** It cannot exist;
   promising it is how a checker ends up trusted for something it does
   not do — which is the failure mode this whole section documents.

#### ⚠⚠ AND THE DECIDABILITY CLAIM ABOVE WAS TOO GLIB — the precise version

"Inhabitation is provability, undecidable" is the right conclusion from
the wrong premise, and the difference matters for Once.

* **Strong normalization does NOT buy decidable inhabitation.** System F
  is SN and its inhabitation problem is UNDECIDABLE (Löb 1976).
  Conversely simply-typed λ-calculus HAS decidable inhabitation
  (PSPACE-complete, Statman 1979). ⇒ totality of the TERM language is not
  the deciding property, so "Once is total" buys nothing here.
* **The deciding property is UNBOUNDED QUANTIFICATION OVER AN INFINITE
  DOMAIN in the TYPE language.** In any total theory with `ℕ` and a
  structurally-recursive step function you can write

      Halts M = Σ ℕ (λ n → run M n ≡ halted)

  — `run` structural on `n`, entirely total — and `Halts M` is inhabited
  iff `M` halts. ⇒ inhabitation is undecidable **without any general
  recursion anywhere**. Once inherits this the moment its types quantify
  over `ℕ`.

★★★ **AND THE ASYMMETRY IS THE ACTIONABLE PART.** Type-checking is
decidable in a total theory, so enumerate-and-check is a genuine
semi-decision procedure:

    "NOT vacuous" (∃ a witness)   — r.e.:      a search FINDS it, eventually
    "vacuous"     (∄ any witness) — co-r.e.:   NO procedure confirms it

⇒ a complete vacuity checker is impossible, but a complete **non-vacuity
finder** exists in the limit. That is the right shape to build: search
for a witness, and treat *found* as definitive and *not found in budget*
as a flag. It improves monotonically with compute, which "inspection"
never does.

#### ⇒ four SOUND partial vacuity checkers, in increasing order of reach

1. **Structural emptiness** — `⊥`, a constructor-free datatype, or a
   family with no constructor available at the given index. Agda already
   decides this: it is what an `()` pattern IS. ⚠ For the ENCODED
   families it is not free — `Examples/Vec.no-cons-at-zero` is a
   hand-written proof, not a decided one.
2. ★ **STUCK-INDEX emptiness — and this one would have caught the actual
   instance.** `gcd-gt-gen`'s premise was uninhabitable because
   `monusTm (nsuc A) B` with `B` a VARIABLE is stuck: it reaches neither
   `nsuc d` nor `nzero`, so no constructor's index can match. In a total
   theory normalization is DECIDABLE, so "normalize the premise's index;
   if it is a stuck neutral and every constructor Fords its index to a
   constructor-headed form, the family is empty" is a decidable check.
3. **Bounded proof search** for the witness — the semi-decision procedure
   above, i.e. Agsy. §6 of `JUDGEMENT-ATTEMPTS` already measured that
   these goals are syntax-directed and exactly Agsy-shaped.
4. **Consumer-discharge** — a conditional lemma owes a consumer that
   builds the premise at the arguments the lemma is stated for.
   Decidable (call graph) *plus* type-checked. Catches both real cases.

★ **A fifth, for Once specifically: a DECIDABLY-INHABITED FRAGMENT.**
Undecidability comes from unbounded quantification; types built only from
finite domains and bounded quantifiers have decidable inhabitation. A
language could mark that fragment and offer a COMPLETE vacuity check
inside it, refusing to guess outside. That is a real design lever and it
is honest at the boundary.

#### ⚠ AND ARE CATCH-ALLS EVEN ALLOWED UNDER `--safe`? — MEASURED: yes, and Agda has a flag for them

Asked directly, and worth testing rather than asserting.

    {-# OPTIONS --safe #-}                        catch-all → rc=0   ✅ ALLOWED
    {-# OPTIONS --safe --exact-split #-}          → CoverageNoExactSplit, NAMING the clause
    {-# OPTIONS --safe --exact-split -Werror #-}  → rc=42, a HARD GATE

★ So `--safe` says nothing about catch-alls — they are ordinary total
code, and this repo relies on it: `Metatheory/LogicalRelation` is
`--safe` and contains `spine? _ = false`.

★★★ **BUT AGDA ALREADY HAS THE CHECK, AND WE WERE NOT USING IT.**
`--exact-split` flags exactly the clauses that are not preserved as
definitional equalities — i.e. the catch-alls — **by name**, and
`-Werror` turns that into a failure. That is a NATIVE, per-clause answer
to category B, strictly more precise than counting.

⇒ two mechanisms, and they are complements, not rivals:

| | catches | cost |
|---|---|---|
| `--exact-split -Werror`, per module | every catch-all, AT ITS CLAUSE | every legitimate one must be expanded into explicit clauses — a real rewrite, and often worse code |
| `FormerCensus.catchAllN` (this repo) | a catch-all's EXTENT MOVING | none — the catch-alls stay; a new former joining one changes the number and fails |

⇒ ⬜ **the pin is the right default and `--exact-split` the right tool for
a module under suspicion.** Adopt the flag where a function is
load-bearing and small (`spine?`, `stablecd?`, the classifiers); keep the
pin everywhere, because it is the one that costs nothing and still makes
a NEW former impossible to add silently — which is the actual bug.

### ⇒ WHAT TO CALL THESE — four levels, and "metatheory" is only one of them

Asked once `FormerCensus`/`Census`/`Adequacy` existed: *is this a
metatheory of the libraries?* Nearly, and the distinction earns its keep.

| | what it establishes | needs reflection? | where |
|---|---|---|---|
| **METATHEORY** | properties of the OBJECT LANGUAGE — SN, canonicity, subject reduction | no | `Metatheory/` |
| **ADEQUACY** | the encoding is FAITHFUL to what it encodes | no — an ordinary theorem | `Knot/Adequacy`, `SzAgree`, `LookupGen`; ⬜ `enDeriv` |
| **COHERENCE** | parallel artifacts stay IN STEP — former ↔ SN row, rule ↔ emitted row, header claim ↔ fact | **yes**, when one side is a DECLARATION | `Metatheory/FormerCensus`, `Knot/Census` |
| **COVERAGE** | the checker REACHED everything | no — a build property | `Trust.agda` + `check-trust.sh` |

★ Metatheory is about the system the development is ABOUT; the other
three are about the development itself. Adequacy is the bridge: it is an
ordinary theorem whose CONTENT is a claim about our encoding. Coherence
is the one that genuinely needs reflection, because its left-hand side is
a `data` declaration rather than a definition. ⇒ **the unifying idea is
that coherence conditions are CODING CONVENTIONS MADE INTO PROPOSITIONS.**

### ★★★ AND CAN THE COHERENCE ROW BE FORCED? — yes, and the first attempt was WEAKER than what it replaced

`InIDD` shipped as `inil` — a WELL-FORMED EMPTY DESCRIPTION — because
`ICon (ε ∙)` was missing from the binder table and both `_∈ID_` rows
silently failed to translate. `Census` would have caught it and did not,
because the family had been **added without adding its census row**.

⇒ **the fix is to make the single source of truth actually single:**
`Census.agda` is now GENERATED from the generator's own family table, so
adding a family and adding its check are one act. `gen_census` refuses a
family with no entry.

⚠⚠ **BUT THE FIRST GENERATED VERSION WAS WEAKER THAN THE HAND-WRITTEN ONE,
AND ONLY THE CONTROL SHOWED IT.** It emitted the generator's OWN skip
count, which makes

    ilen D + skips ≡ rules X

true *by construction*: with both `_∈ID_` rows gone, `skips` became 2,
`ilen InIDD` became 0, and `0 + 2 ≡ 2` **passed**. The check had become
insensitive to precisely the failure it exists for.

⇒ ★ so the skip count is now a HAND-MAINTAINED CLAIM (`_SKIP_EXPECT`),
checked against reality in the generator and pinned exactly in Agda.
Control re-run: the generator refuses with
*"InIDD: 2 rule(s) did not translate, expected 0 … a rule just went
silently missing."*

★★ **THE LESSON GENERALISES AND IS THE SHARPEST ONE HERE: a check whose
EXPECTED VALUE is computed by the thing being checked is not a check.**
`_FLOOR` had this shape too (a floor cannot see a fall to itself); so did
the "N of M" prose claims. **The expected side must come from somewhere
the producer does not control** — reflection over the SOURCE datatype, or
a human-written constant.

### ⬜ SHOULD `Examples/` GET THE SAME TREATMENT? — yes, three obligations, each from a real bug

`Examples/` is where descriptions are BUILT, so it is where the
"well-formed but empty" hazard lives — the exact thing `⊢lkVz`'s note
names: *"a well-formed description with no closed inhabitant is
indistinguishable from a good one."* `InIDD` is that hazard, realised.

1. **INHABITATION** — every demonstration family exhibits a closed
   inhabitant. `⊢lkVz` and `ctx1` do it by hand; nothing forces it, and
   `Negative/WkEmp` plus `Vec.no-cons-at-zero` are the record of what
   goes wrong.
2. **CENSUS CLAIMS** — 10 files under `Examples/` carry prose `N of M`
   claims, and category E bit exactly there (`Knot/Terms`, 32 → **13**).
   Each should be a `refl`, the way `Knot/Census` now is.
3. **`Comparison/`'s REDUNDANCY claim** — it asserts two routes compute
   the same thing, in prose. That is a coherence claim and could be
   `refl`.

⇒ ★ i.e. **turn every prose claim in an `Examples/` header into a
proposition.** The technique is the one already built; what is missing is
the pass.
