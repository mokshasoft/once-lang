# DirectedHoTT · Where the build time actually goes

> Measured 2026-08-21/22. Paths below say `…ExamplesGcdX`; since the
> 2026-08-22 migration those are `DirectedHoTT/Examples/Gcd/X`.

> ⚠ This supersedes the operative half of `agda-perf-is-mutual-block-size`
> **for the gcd/example modules**. That measurement was taken on
> `NbEPDirDBFund` and is still correct *there*. It does not transfer.

Machine: **7 GB total RAM, ~3 GB free** (browser + editors resident).
That number matters — see §4.

--------------------------------------------------------------------------
## 1. The phase split is nothing like the folklore

`--profile=all`, cold module, warm deps.

| phase | `…ExamplesGcdDvdL` | `…GcdDvdA1` | `…ExamplesGcdLeMid` (`-c`) |
| --- | --- | --- | --- |
| Typing.CheckRHS | 5,080ms 35% | 74ms 1.5% | 13,329ms 17% |
| Typing.OccursCheck | 2,281ms 16% | 18ms | 4,748ms 6% |
| Deserialization | 4,031ms 28% | **4,445ms 90%** | 4,207ms 5% |
| Serialization | 2,709ms 19% | 295ms 6% | **22,976ms 30%** |
| Positivity | **67ms 0.5%** | ~0 | 9,530ms 12% |
| Termination | **13ms 0.1%** | ~0 | 1,525ms 2% |
| InterfaceInstantiateFull | 79ms | — | 8,774ms 11% |
| **Total** | **14,435ms** | **4,946ms** | **77,385ms** |
| peak RSS | 940 MB | 467 MB | — |

⇒ **Positivity + Termination is 0.6% in the gcd leaves.** The standing
advice "shrink the mutual block" is the wrong lever for that whole family.
It IS a real lever for `LeMid` (12%) and for `Fund`, which is where the
84% figure came from — those modules have the big-mutual-block shape.

⇒ **Serialization is the single largest phase for `LeMid` (30%)** while its
interface is only 0.4 MB. It is not writing volume; it is normalising terms
for storage.

--------------------------------------------------------------------------
## 2. There is a fixed per-file entry fee: ~4.4s / ~30 MB

Every gcd example deserialises its whole transitive interface closure:

| module | deps | interface bytes |
| --- | --- | --- |
| `…ExamplesGcdDvdA1` | 45 | 30.2 MB |
| `…ExamplesGcdDvdL` | 41 | 29.3 MB |
| `…ExamplesGcdLeMid` | 29 | 25.4 MB |
| `…ExamplesIHCallAgree` | 47 | **31.0 MB** |

★ `…ExamplesIHCallAgree` is the CONTROL: it is four `refl`s and zero
content, and it pays the most of any of them. The fee is content-blind.

**Two leads, one real and one not:**

- ⛔ **NOT a lever — `wk-single`/`…LR`.** 70 of 78 `…LR` importers use it
  for exactly one name, `wk-single`, which is defined in `…Type` (401 KB),
  not `…LR` (4.7 MB). Repointing all 70 changes the closure by **0.0 MB**,
  because `…LR` arrives anyway via `…Canon`/`…Fund`/`…FundSem`/`…FundSN`/
  `…LibNatVal`. Only six modules genuinely need it. Import hygiene, not
  performance. **Do not spend a day on this.**
- ✅ **A real one — `…LibAmrec` → `…LibNatVal`.** That single edge (for
  `NatVal`/`natEval`) drags in `…Canon → …Fund → …FundSem`/`…FundSN`, the
  whole canonicity stack: **18–22% of the closure, 6 modules**, for every
  amrec client. Whether it can be cut is a DESIGN question — `natEval`
  needs canonicity — but it is the one edge worth attacking.

--------------------------------------------------------------------------
## 3. ⭐⭐ THE SPLIT IS COST-NEUTRAL. THE OOM IS A GC CHOICE.

The six-way `…GcdDvdA*` split, re-merged mechanically into ONE 451-line
module (probe, since deleted), against the six built individually:

| | `-A64m -c` | `-A64m` (sweep default) |
| --- | --- | --- |
| merged, one module | **RC=0, 147s** | **RC=143 OOM, 339s** |
| six modules, summed | **147s** (7+51+13+21+21+34) | — |

`…ExamplesGcdLeMid`, same machine, same minute:

| | result |
| --- | --- |
| `-A64m -c` | **RC=0, 82s** |
| `-A64m` | **RC=143 OOM, 113s** |

★ **Splitting costs nothing and saves nothing in wall time** — 147s either
way, to the second. The per-file floor (§2) and the superlinear savings
from smaller blocks cancel almost exactly. Splitting is purely a
MEMORY-MANAGEMENT DEVICE.

★ **`+RTS -c` is a second, independent way to buy the same headroom**, and
it would have made the split unnecessary.

⚠ **`-c` is NOT a free default.** `check.sh`'s own header: `-A64m` 13.7s /
1.36 GB vs `-c` 19.8s / 1.26 GB — ~45% slower on a module that does not
need it. Applying it selectively is correct.

⚠ **What was wrong is the THRESHOLD, not the policy.** `needs_c` reads a
hand-written per-file header comment and fires on ONE module. But whether
a module OOMs depends on free RAM — `LeMid` builds under the default in a
sweep on a quiet box and OOM-kills today with a browser open. No header
comment can track that.

⇒ **FIXED: `sweep.sh` now retries once with `-c` on exit 143.** Costs
nothing when unneeded; removes the hand-maintained list; and directly
addresses the hazard sweep.sh already documented at its own line 113 (a
heavy module pulled in as a DEPENDENCY is built without its flag and dies,
surfacing as SIGTERM on the importer).

--------------------------------------------------------------------------
## 4. Two claims made during this session that the data killed

Recorded because both were plausible and both were wrong.

1. **"A1–A5 are pure per-file tax."** False — generalised from A1, which
   is merely the cheapest member. Actual: 7 / **51** / 13 / 21 / 21 / 34 s.
   The work IS distributed.
2. **"The split costs ~26s of pure overhead."** False — it is cost-neutral
   (147s vs 147s). The floor is real but is a minority of the family cost.

⚠ Also: three `…GcdLeMid` profiling runs died at 3:16 / 3:00 / 2:40 and
were twice mis-diagnosed as a `/usr/bin/time` wrapper problem or a harness
watchdog. They were **OOM kills** — the varying kill time was the tell.
`--profile=all` accumulates a large statistics table and is itself enough
to push a near-ceiling module over. Use `--profile=internal` for phase
timings on heavy modules.

--------------------------------------------------------------------------
## 5. What to do with this

- **Do not** reason from "positivity/termination is 84%" for the gcd family.
  Run `--profile=internal` first.
- **Do not** split a module to fix an exit 143 before trying `-c`.
- **Do** treat 143 as "try the other collector", never as a proof verdict.
- **Open:** the `…LibAmrec → …LibNatVal` edge (§2), worth ~20% of every
  amrec client's floor.

--------------------------------------------------------------------------
## 6. 2026-08-22 — what the reorganisation and two failed hypotheses showed

**The closure work paid; the two cost hypotheses did not.**

| | |
|---|---|
| interface closures | **−35–43%**, from two mis-filings |
| cold sweep | 2650s / 128 modules → **1144s / 89** |
| warm sweep | ~324s → **~200s** |
| live path | every module **2–3s** — the <10s target is met |

★ **The two mis-filings, and both had the same shape** — a name imported
from where it was first SEEN rather than where it is DEFINED:

- `natEval` (needs canonicity) sat beside the 3-line `NatVal` datatype, so
  `Lib/Amrec` dragged `Canon → Fund → FundSem/FundSN` to its 31 importers.
- `wk-single` is defined in `Spec/Typing` (762 lines) and 59 modules
  imported it from `Metatheory/LogicalRelation` (6271 lines).

⚠ **Closure leads are not independent.** The `wk-single` lead measured
**0.0 MB** on 2026-08-21 — `LR` arrived via `Canon`/`Fund` anyway — and
became worth 21–29% once the `natEval` edge was cut. **A negative result
about dependencies has a shelf life; re-measure after cutting any edge.**

### Two hypotheses tested and REFUTED

1. **"Transports are the cost"** (from `build-dont-transport`). Transport
   *count* does not predict cost at all: `Gcd/Motives` has the densest
   transports and is fast; `Gcd/Kernel` takes 23s with **zero**. That
   finding was about one transport at context **depth 10** over a large
   type — it is transport × depth, not transports.
2. **"Triple module instantiation is the cost."** `Gcd/Spec` instantiated
   `Stmt`, `Concl` AND `AmTΠ` at identical parameters. Predicted ~3×;
   **measured 17%**, inside the noise band. ⇒ Agda SHARES module
   applications rather than eagerly re-elaborating them. The
   "extend an instantiation rather than adding a second" rule is
   **scope hygiene, not cost**.

### ★ What IS expensive, measured

**Naming a large proof term in a type.** Writing maximality's eliminator as

    Δ ⊢ app (app (app _ e) h₁) h₂ ∷ dvdT e (app (gcdTm Δ) x)

**OOM-killed** the module at 220s, uncontended, under `-c`: the `_`
resolves to the entire `amrec-ind` proof term, which Agda then carries
*inside the type* under three applications. Returning `Prv` — the named
existential — packages it: **77s**. Same theorem, same proof.

⇒ explains why `gcdSpec` returns `Prv`, and why `gcd∣fst` gets away with
`fst _` (one constructor is cheap; three applications are not). Same
mechanism as `abstract-the-substituted-terms` (87× here): **keep large
terms out of types.**

### ⚠ The machine is currently the binding constraint

7 GB total, ~4 GB held by other processes. `Comparison/GcdIndStepConcrete`
builds in ~157s with headroom and **OOMs at 2 GB free** under `-c`,
`-A16m -c` and `-A8m -c` alike. The same module has measured 76s, 104s and
352s-then-death within one hour with no code change. **Below ~2×, a
difference here is not evidence.**

--------------------------------------------------------------------------
## 6. ★★★ THE DOMINANT COST IS DESERIALIZATION, AND THE FIX IS TO SPLIT
##    MODULES BY **WHAT CALLERS USE** — measured 2026-09-04

### 6.1 The phase split, on the knot

`--profile=all`, warm deps, four knot modules:

| module | total | deserialization | **typing** |
| --- | --- | --- | --- |
| `Knot/Census` | 5,811ms | 3,948ms (68%) | **2ms** |
| `Knot/IPayTy` | 3,622ms | 2,655ms (73%) | ~0 |
| `Knot/SubApp` | 3,383ms | 2,510ms (74%) | ~0 |
| `Knot/PayTy`  | 3,508ms | 2,599ms (74%) | ~0 |

⇒ **~70% of a knot sweep is reading interfaces.** Type checking is
noise. So the lever is not proof size, not Def-lifting (measured: 48.3s /
4.56 GB against 48.3s / 4.53 GB — *no effect*), not mutual-block size.
It is **how many bytes a module must read before it starts.**

### 6.2 What the knot was reading, and why

253 interfaces, 112 MB. The three largest were `Metatheory/Confluence`
(8.7 MB), `Metatheory/LogicalRelation` (5.4 MB), `Metatheory/Injectivity`.

**Every knot module reached `Confluence`.** The path was not a direct
import — it was:

    Knot/JudgeWfA  →  SubjectReduction  →  Confluence

and ~90 of the ~100 modules importing `SubjectReduction` used **exactly
one name from it: `⊢wk`**. They were deserializing the entire confluence
proof *in order to weaken a derivation*.

### 6.3 ★★★ THE RULE: SPLIT BY CONSUMPTION, NOT BY SUBJECT

A module is well shaped when its *interface size* matches what its
*callers* need. `SubjectReduction` was well shaped by subject — reduction
preserves typing, plus the structural lemmas that proof needs — and badly
shaped by consumption:

| what callers wanted | how many | what they paid |
| --- | --- | --- |
| `⊢wk` alone | ~90 | Confluence + Injectivity + SR |
| `⊢-cast`, `ren-ty`, `Sub⊢` … | ~15 | same |
| `sr`, `sr*`, indexed-ι | 8 | same |

Two new modules, each defined by what is *asked for*:

- **`Metatheory/RedCong`** — `⟶*` congruences, `⟶-ren`/`⟶*-ren`,
  substitution monotonicity, and `_⟶ᵀ*_` + its congruences + `red→≅ᵀ`
  (those last lifted out of `Injectivity`). Needs only `Spec`.
- **`Metatheory/TySub`** — the structural typing lemmas: `∋-cast`,
  `⊢-cast`, the naturality layer, `Ren⊢`/`⊢wk`, `Sub⊢`/`sub-lemma`/
  `⊢single`, and the five indexed-ι well-formedness lemmas. Needs
  `RedCong` and **neither `Confluence` nor `Injectivity`**.

Both parents re-export `public`, so no existing importer broke.

### 6.4 Result, measured

| | before | after |
| --- | --- | --- |
| `Confluence.agdai` reached by a knot leaf | yes, 112/112 | **no, 111/112** |
| mean metatheory bytes per knot module | **13.0 MB** | **1.78 MB** |
| `Injectivity.agdai` | 5.4 MB | 830 KB |
| modules repointed off `SubjectReduction` | — | 184 → `TySub` |
| modules repointed off `Injectivity` | — | 55 → `RedCong` |
| modules that still legitimately want `SubjectReduction` | ~100 | **5** |
| modules that still legitimately want `Injectivity` | 61 | **6** |

**7.3× less metatheory to deserialize per knot module.**

### 6.5 ⚠ How to find the cut — three checks that did the work

1. **Classify importers by their `using` list.** For each importer, is
   every name it asks for present in the candidate module? That single
   test partitioned 61 `Injectivity` importers into 55 movable / 6 not,
   with no judgement calls.
   ⚠ The name-extraction regex must include **data constructors**. A
   first pass missed `doneᵀ`/`stepᵀ` and reported 47 modules as blocked
   that were in fact already served.
2. **Grep the candidate block for the thing it must not mention.** Lines
   84–357 of `Confluence` contain `⟹` zero times — that is what proved
   the congruences were separable from the confluence proof, before
   moving a line.
3. **Compute the dependency cone of the lemmas you want to move.**
   `iihTy-wf`/`isingle-Sub⊢`/`iext-Sub⊢` sat *after* `sr` in the file and
   under a header that filed them with ι — but their cone is **five
   definitions and touches neither `sr` nor any `gen-*`**. They were
   downstream by narrative, not by dependency.

### 6.6 ⚠⚠ THE TRAP: A REPOINT THAT BUYS NOTHING

Repointing 172 modules at `TySub` moved the needle **0 MB**. Every knot
module goes through `Lib/IWk`, `Lib/ISub`, `Lib/IFold`, `Lib/IPay`, and
those four still wanted `iihTy-wf`/`isingle-Sub⊢`/`iext-Sub⊢`. **One
surviving edge in a chokepoint erases the whole win.**

⇒ Do not measure a split by how many modules you repointed. Measure it by
**transitive reachability of the heavy interface from a leaf** — and
re-measure after every step. Two of the four steps here looked like
progress and delivered nothing until the last edge was cut.

### 6.7 The dev-cycle consequence, measured

| edit | check a knot leaf |
| --- | --- |
| edit the leaf itself | **3.61 s** |
| `touch` a `Lib` module (no content change) | 4.06 s — Agda hashes content |
| **real content edit in `Lib/IMeths`** | **556.73 s** |

**154×.** So while developing a new library lemma, state it in a *temp
module that imports the real one* and promote it when the example that
needs it is finished. Moving code into `Lib` is a **correctness** lever
and an **anti-lever for sweep time** — it widens the invalidation set
(demonstrated: 1 → 89 affected modules).

### 6.8 ⚠⚠ A SWEEP'S FIRST MODULE IS BILLED FOR EVERY COLD DEPENDENCY

In the 2026-09-04 verification sweep `Knot/JudgeWfAA` reported **2295s**
and `Knot/JudgeWfA`, two lines later, reported **5s** — although
`JudgeWfAA` is the *smaller* file (305 lines against `JudgeWfAG`'s 361,
which took 84s).

| module | build order | closure | **cold when it ran** | reported |
| --- | --- | --- | --- | --- |
| `Gcd/StepExtA` | 1st | 27 | 27 | 400s |
| `Knot/JudgeWfAA` | 2nd | 89 | **75** | **2295s** |
| `Knot/JudgeWfA` | 3rd | 63 | **0** | **5s** |

`sweep.sh` times the `check.sh` invocation and Agda builds imports
transitively, so the first module to reach a subtree pays for all of it.
`JudgeWfAA` imports `JudgeWfA`…`JudgeWfZ` plus `Knot/Desc`, `Sorts`,
`Ctors`, `Terms`, `Wf`, `Lib/IWk`, `Lib/ISub`, `Lib/IFold`, `Lib/IPay`,
`Lib/IMeths`, `Lib/ICast` — 75 modules, ~30s each, which is exactly the
band the siblings then reported once those were warm.

⇒ **the `<-- SLOW` marker on the first module in the ordering is
meaningless**, every sweep, because `sweep.sh` deliberately runs the
RTS-special modules first. To time a module honestly, check it with deps
warm, or compare it against a sibling whose closure adds 0 new modules.

⚠ Memory pressure (the box dipped to 166 MB free during that window)
stretched the number but did not create it — see §4 and
`agda-oom-is-a-gc-choice`.


### 6.9 ⚠⚠ CORRECTION — §6.8's WALL-CLOCK NUMBERS WERE TAKEN UNDER CONTENTION

Another Agda run (`make agda MODULE=Once/Adequacy/RealizeAgrees.agda`, a
DIFFERENT session) was resident on this 7.6 GB box during the 2026-09-04
sweeps. `never-run-two-agda-checks-at-once` says they OOM-kill each other
and that a 143 means contention. ⇒ THE FOLLOWING ARE NOT SAFE:

* the cold sweep total (5912s) — already disclaimed above, now for a
  second reason;
* `JudgeWfAA`'s 2295s — the closure explanation in §6.8 stands (75 cold
  modules against `JudgeWfA`'s 0, and it is 5s warm), but the MAGNITUDE
  was inflated by contention as well;
* **`Trust`'s KILLED(143) at `-A64m` and `-A64m -c`.** It passed at
  `-A8m -c` in 20s while busy, and at plain `-A64m` in 13s once quiet.
  ⇒ "Trust needs a smaller nursery" is NOT established; contention
  explains it equally well. The third ladder rung stays as cheap
  insurance, not as a measured finding.

★ WHAT IS UNAFFECTED, because it is machine-independent:
  the interface byte counts (13.0 MB → 1.78 MB of metatheory per knot
  module; `Injectivity` 5.4 MB → 830 KB; total 112 MB → 107 MB) and the
  reachability counts (112/112 → 1/112 knot leaves reaching `Confluence`).
  `JudgeWfA` 179s → 4s is also safe: 45× is far outside contention noise,
  and `agda-rss-noise-floor` puts that at ±12%.

⇒ **CHECK `ps` FOR ANOTHER AGDA BEFORE TIMING ANYTHING.** This was the
third session-day whose timing conclusions had to be requalified after the
fact; it is cheaper to look first.

### 6.10 ⚠⚠⚠ §6.8 IS NOT A CURIOSITY — IT PRODUCED TWO WRONG CONCLUSIONS
###      IN THE SESSION THAT WROTE IT

§6.8 says a sweep bills the first module for its whole cold closure. That
is easy to nod at and then misread anyway, because the misreading does not
look like one: **a module whose closure was already built reports a small
number, and that number is DESERIALIZATION, not a check.** Both of the
following were believed, acted on, and wrong:

**(1) "Adding naturality lemmas took `Knot/RenMot` from 1s to 155s."**
The 1s came from a sweep line. In that sweep `Knot/JudgeWfAA` had already
built `RenMot` inside its own 2295s, so the line measured nothing.
`RenMot`'s real cold cost, with the lemmas removed AND every library
reverted to HEAD, is **264s**. There was no regression. A module
(`Knot/RenNat`) was created to fix a problem that did not exist, and its
header asserted the false measurement until it was corrected.

**(2) "`Knot/RenTm` OOMs because of the new `Lib/ISub` cascade."**
`RenTm` is OOM-killed at ~515s under the default `-A64m`, reproducibly.
It fails IDENTICALLY with `Lib/ISub` reverted to HEAD and with `RenTm`'s
own new block deleted — so neither caused it. With `-A64m -c` it passes
in 351s (233s once warm). It had never been timed alone: every sweep built
it inside `JudgeWfAA`'s closure, and JudgeWfAA carries the compacting-GC
header, so `RenTm` silently inherited `-c`. ⇒ `agda-oom-is-a-gc-choice`,
third confirmation, and `RenTm` now carries its own header.

★★★ THE RULE, stated so it cannot be nodded past:

> **A per-module sweep time is evidence about that module ONLY if its
> closure was already warm when it ran. Otherwise it is either the whole
> closure's build (too big) or a deserialization (too small). Both
> failure directions occur, and the small one is the dangerous one —
> it looks like a baseline.**

⇒ BEFORE believing any per-module number: compute `reach(M)` minus what
earlier modules already built (§6.5's third check), or re-time the module
standalone with `touch M && check.sh M` on a quiet box. And before any
timing at all, `ps -eo args | grep '[a]gda'` — see §6.9.

### 6.11 ★★★ THE OTHER HALF OF THE TEMP-MODULE DISCIPLINE: DON'T SWEEP
###      WHAT CANNOT HAVE CHANGED

§6.7 says develop a new lemma in a temp module (154×). That saves the
DEVELOPMENT cost. It does nothing about the VERIFICATION cost, and it is
easy to hand the saving straight back by running a full sweep afterwards:
a change confined to NEW LEAF MODULES has an affected closure of two or
three modules, and a full sweep re-verifies 236 that provably cannot have
changed — ~50 minutes for no information.

★ WHAT A SWEEP ADDS OVER `affected.sh` IS TWO COVERAGE GATES, AND THEY
  ARE FREE STANDING ALONE — `tools/check-trust.sh`, measured **0s**:

    == KERNEL IS INDEPENDENT: Spec/ and Metatheory/ import no Lib/ or Examples/.
    == TRUST ROOT REACHES ALL 238 modules

  The second is the one that matters for a NEW module: if it is not in
  `Trust.agda`, nothing forces it under `--safe`, and `affected.sh` would
  never notice. That is a COVERAGE question, not a correctness one — the
  same class as `verification-that-covers-less-than-it-claims`.

⇒ THE RECIPE, for a change that adds or edits only leaf modules:

    tools/check-trust.sh            0s   — coverage gates
    tools/affected.sh <module>      s    — the TRUE dependent closure, built

  valid when the previous full sweep was green. ⚠ NOT valid for an edit to
  `Lib/` or `Metatheory/` — there the closure IS most of the tree, and the
  sweep is the cheap way to build it in dependency order.

⚠ AND `affected.sh` MUST BE TRUSTED ONLY BECAUSE IT WAS FIXED. It had a
graph bug this session that reported **1** affected module where the true
answer was **89**. It now matches both import forms and prints the module
names — check the NAMES against what you edited, not just the count.


### 6.12 ⚠⚠ FOURTH INSTANCE, AND THIS ONE ALMOST SHIPPED A SPLIT

`gen_renagree`'s 25-row output was OOM-killed at **234s**, and again at
**260s** under `-c`.  Conclusion drawn: 25 rows is too much for one module,
split it like `RedWfA`/`RedWfB`.  The split was written, both halves went
green (441s and 7s), and the generator carried a comment asserting the
measurement.

★ THEN THE 441s/7s ASYMMETRY WAS CHECKED.  Half A had built the whole
closure; half B inherited it.  Re-timed with dependencies warm:

| | |
| --- | --- |
| half A (13 rows), `-c` | **9s** |
| half A (13 rows), default RTS | **9s** |
| **FULL 25-row module, default RTS** | **12s** |

⇒ the split was UNNECESSARY, the OOMs were the cold closure, and `-c` was
never needed.  Un-split.

⚠⚠⚠ THIS IS THE FOURTH TIME IN ONE SESSION (§6.10 lists the first three),
and it is the one that came closest to being permanent: the other three
were wrong *diagnoses* of things that were already green, while this one
was about to bake a structural decision — and a false justification for it
— into a GENERATOR, where it would have been inherited by every future
emitted module.

★ WHAT WOULD HAVE CAUGHT IT SOONER, and costs seconds:

    find . -name 'M.agdai' -delete && time ./check.sh …/M.agda

  run TWICE — the first rebuilds the closure, the second measures M.  Any
  per-module claim not made from the second run is not evidence.
