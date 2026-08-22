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
