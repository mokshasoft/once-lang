# DirectedHoTT · TODO

⚠ **Tracking list.** The narrative lives in `PLAN-JUDGEMENT.md` and the
dated `HANDOFF-2026-08-NN.md`; the rules in `LESSONS.md`. This file is
just the checklist, newest state as of **2026-09-01**.

Legend: ✅ done · 🟡 partly done, state recorded in the module header · ⬜ not started

---

## A. The knot (the 53-row syntax encoding)

| | item | where |
|---|---|---|
| ✅ | the table, `KnotWf`, tags, constructors | `Knot/Desc`, `Wf`, `Tags`, `Ctors` — generated |
| ✅ | inhabitants at concrete and variable depth | `Knot/Terms`, `Knot/Build` |
| ✅ | adequacy map `⌈_⌉` | `Knot/Map` — generated |
| ✅ | `Ctx` as its own family (NOT the 8th sort) | `Knot/CtxD`, `Negative/WkEmp` |
| ✅ | `sz` and the same-sort measure | `Lib/ISz`, `Lib/ISzSort`, `Knot/Sz`, `SzS` |
| ✅ | **`szsTm ⌈t⌉ ⟶* num (sz t)`, all 30 `RTm` rows** | `Knot/SzAgree` — generated |
| ✅ | census of the headers' numeric claims (C1) | fixed 2 stale claims in `Knot/Terms` |
| 🟡 | **C2** — `check-formers` 4–6 | gate 4 CLEAN, gate 6 back to 5 (2 were mine), gate 5 = 3 notes ⬜ |
| ⬜ | C2 — `Confluence`'s `⟹-⁺` `UnreachableClauses` | hygiene only; diagnosis is expensive, see below |

## B. Step 1 — `_∋_∷_`

| | item | where |
|---|---|---|
| ✅ | both rows, well-formed AND inhabited | `Knot/Lookup` |
| ✅ | the generator reproduces them | `Knot/LookupGen` (control) |

## C. Step 2 — weakening, `extS`, `subTm`

| | item | where |
|---|---|---|
| ✅ | `wkK : K i → K (sh i)` | `Knot/Wk`, `Lib/IWk` |
| ✅ | `nsuc` injective / the ford inverted | `Lib/IdSuc` |
| ✅ | the Kripke motive spiked | `Examples/KripkeSub` |
| ✅ | **`extS`** — 51 no-op methods + 2 real | `Knot/SubMot` |
| ✅ | `subTm`'s motive + `sortMap` (+3 reduction controls) | `Knot/SubMot` |
| ✅ | `sortConv` — the one lemma all 53 rows need | `Knot/SubMot` |
| ✅ | the per-row mask, verified 50 rows classify | `Lib/ISub`, `Lib/IMeths` |
| ✅ | lookup method 1 of 3 (`cTm-var`) | `Knot/SubMot` |
| ✅ | **lookup methods 2–3** (`cVar-vz`, `cVar-vs`) | `Knot/SubMot` — all 3 given rows done |
| ✅ | `⊢Var-vzKt` / `⊢Var-vsKt` — constructors at an ARBITRARY depth | `Knot/Build` rungs 4–5; ONE lemma `rtA v X` composed, not 3 chains |
| 🟡 | the 50 computed rows' **typing** | ⚠ needs a REFINED classification — see below |
| ✅ | **step 1/6 — `⊢extNK`** (the extension preserves types) | `Knot/SubMot`; took 7 attempts, see `SUBTM-ATTEMPTS.md` |
| ✅ | **step 2/6 — `⊢sPick`** (+ `⊢sucs`, `⊢extsN`) | `Lib/ISub.Sub.Typing`; forced `IsNum` |
| ✅ | **step 3/6 — `⊢isubPay`** (+`⊢kaPick`, `⊢fordMapK`, `⊢motAppK`) | `Lib/ISub.Sub.Typing`, INSTANTIATED over the knot |
| ✅ | **step 4/6 — `⊢isubMethodK`** | `Knot/SubMot` — at the KNOT, not `Lib`: the last two binders are the motive's |
| ✅ | **step 5/6 — the tuple at the mask** | `Knot/SubMot`; obligations COMPUTED — 3, not 53 |
| ✅ | **step 6/6 — `subTmK` + `⊢subTmK`** | `Knot/SubMot`; `⊢ielim` needed NO cast |

## D. Step 3 — the judgement layer (~148 rows)

⚠ A judgement is ONE description, so none lands partially. The
judgements form a CHAIN and `_⟶_` is at the bottom, so **all of D is
gated on `subTm`**.

| | item | rows |
|---|---|---|
| ✅ | the row emitter + its control | `tools/gen-knot.py`, `Knot/LookupGen` |
| ✅ | **the `IConWf` emitter** | `emit_jrowwf`; both `_∋_∷_` rows generate + typecheck (`Knot/LookupGen`) |
| 🟡 | `_⟶_` | **71 of 73** — the 2 left are `ι-elim`/`ι-ielim`, which want an object-level METHOD SELECTOR (`sel`/`fields`/`lookupD`) |
| ✅ | `_⟶ᵀ_` | **26 of 26** |
| ✅ | `_≅ᵀ_` | **4 of 4** |
| 🟡 | `_⊢ty_` + `_⊢_∷_` (mutual) | **34 of 43** — `⊢natrec` landed 2026-09-01, closing the `singleK` job (item 1) |
| ⬜ | `Canon`, `Prog` | 20 |

⚠ **The 9 still not emitted are three jobs, not nine problems** — the
`NOT EMITTED` block at the head of `Knot/JudgeRows` names each:

| job | rules |
|---|---|
| the small judgements (`DescWf`/`IDescWf` as premises) | `ty-Mu`, `ty-IMu`, `⊢⌜Mu⌝`, `⊢⌜IMu⌝`, `⊢con`, `⊢elim`, `⊢icon` — **7** |
| a boolean function over syntax (`NoNatC`) | `⊢tr` — **1** |
| a motive annotation the sort inference declines | `⊢ielim` — **1** |

★ **The ratchet is the witness, not the verdict.** `_FLOOR` in
`gen-knot.py` asserts these counts where they are computed; a row set
that SHRINKS still typechecks and still sweeps green.

## E. Step 4 — the dogfooding exhibit

| | item |
|---|---|
| ⬜ | object-level `prog` via `⊢amrec` — replacing the POC's own `prog`/`usplit`/`trS`/`ordtrS` |

⚠ **This is the target the whole path exists for** (`PLAN-JUDGEMENT` §4,
`Examples/Dogfood`). The knot is the PREREQUISITE, not the exhibit.

## F. The pending generalisation — 4 customers, 2 families

Full state: `HANDOFF-2026-08-27` §"THE PENDING GENERALISATION".

| | item |
|---|---|
| ✅ | `Lib/IMeths` — the walk, lifted out of `Examples` |
| ⚠ | `Lib/ISub` reuses `Lib/IWk`'s classification for the TERM; the TYPING needs one more datum |
| ✅ | **`iatCon-wf`** — PROVED 2026-08-30 via `iconS-Sub⊢`; the gate on `Lib/IPay` is OPEN |
| ⬜ | `payStep` is MISFILED in `Lib/IWk` (both outside customers do substitution) |
| ⬜ | `sub-w`/`²`/`³`/`⁴` want INDEXING not listing (26 customers) |
| ⬜ | the assembly lemma itself |

⚠ **Open question marks**, in increasing severity:
1. ~~`iatCon-wf`'s last case needs "substituting by a renaming IS
   renaming"~~ ✅ **DONE.** The lemma existed — `ren-subTy`, trapped in
   `Lib/Wk.nrs-wTy`'s `where` block. Lifted; case 3 closed; `iatCon-wf`
   is four lines. See `LIFTS.md` for the scan this prompted.
2. The mask may not be the last shape needed; `subTm`'s 50 computed rows
   are not typed yet.
3. ~~"`sub-w`ⁿ wants indexing" is `Lib/Wk`'s CLAIM, not a measurement~~
   ✅ **RESOLVED 2026-08-29, and the other way round.** `⊢Var-vsKt` uses
   `sub-w` and `sub-w²` at SUCCESSIVE RUNGS INSIDE ONE PROOF, composed
   into a four-step descent — which is exactly "iterates of one lemma".
   ⚠ My note of 08-28 called the same row weak evidence AGAINST; that
   reading depended on the three chains being distinct, and they were an
   artefact of half-abstraction. Evidence now points FOR the indexing.

---

## G. C2 in detail (2026-08-28)

### ✅ gate 4 — vacuously discharged rows: CLEAN
4 rows are `⊥-elim`, and **all four are `structural`** — the premise is
genuinely uninhabitable (`noVar` at `var x`, `UnitU-clash` at `unit`,
`NatU-clash` at `nzero`). ⚠ No `PLACEHOLDER` rows, which are the ones
that would stand in for a MISSING TYPING RULE. Nothing owed.

### ⬜ gate 5 — promissory notes: 3, all pre-existing
`Metatheory/LogicalRelation:3773`, `Spec/Typing:290`, `Spec/Typing:438`.
Each asserts an invariant nothing checks. ⚠ Reviewing these means
reading the surrounding rule, not running a tool.

### ✅ gate 6 — conditional lemmas with no consumer: 7 → 5
⚠ **Two of the seven were MINE, added the same day**: `muFwd*`
(`Knot/JudgeLib`) and `p5*` (`Knot/SubMot`). Both were written for
symmetry with a lemma that IS used, and neither ever acquired a caller.
Removed. ★ Symmetry is not a reason to ship a lemma — and the gate
caught it within hours, which is the argument for running it routinely
rather than as a parked item.
The remaining 5 are long-standing and in `LogicalRelation`/`SubjectReduction`.

### ⬜ the `⟹-⁺` `UnreachableClauses` warning
⚠ **Hygiene, not correctness** — the module compiles and its theorem
stands; some of 592 clauses are subsumed by earlier ones.

⚠ DIAGNOSIS IS EXPENSIVE BUT **TRACTABLE** — corrected 2026-08-28 with
data, having first written it off as "unknown, possibly very large".
Agda reports only the whole definition range (3198–4358) and there are
NO duplicate left-hand sides, so finding them means BISECTING 592
clauses. A half-split does not finish in 600s (against 2.8s intact) —
but run to completion in the background it takes **~15 min per step**,
not forever.

★ AND THE ARGUMENT IS SOUND EVEN THOUGH THE SPLIT DOES NOT TYPE-CHECK.
Dropping clauses breaks COVERAGE (`rc=42`), but the
`UnreachableClauses` warning can only be about clauses that REMAIN — so
"warning still present after dropping X" proves an unreachable clause
lies outside X.

    step 1: drop 296..591 → warning STILL present  ⇒ one lies in 0..295

⇒ ~9 steps remain, ~15 min each, for a COSMETIC gain. Continue only if
those clauses are being pruned for another reason — but the method is
now known to work, which it was not before.


## ⬜ SPLIT `Trust.agda` INTO SEVERAL ROOTS — sized 2026-09-04, not urgent

`Trust.agda` imports all 235 modules and type-checks nothing, so its
entire cost is loading every interface at once. It is the ONE module that
can never benefit from the interface-size work of `PERF.md` §6 — it
exists to load everything — and its peak memory grows monotonically with
the development. It was KILLED(143) at `-A64m` AND `-A64m -c` in the
2026-09-04 sweep, then passed at `-A8m -c` in **20s**.

★★★ AND SPLITTING COSTS NOTHING IN GUARANTEE. `check-trust.sh`'s own
header records why: `--safe` BANS `postulate` and `--safe` PROPAGATES
through imports (`CoInfectiveImport`). That propagation is **edge-local,
not root-local** — it happens on every import edge regardless of where the
walk starts. So N roots enforce exactly what one root does, provided every
module is reachable from SOME root; and "does the root set reach every
file?" is the coverage question `gen-trust.sh` already answers by diffing
the list. ⇒ this is a partition, not a weakening.

Sized, by directory, coverage verified complete (uncovered: NONE):

| root | roots | closure it must load |
| --- | --- | --- |
| single `Trust` (today) | 235 | **235** |
| `Trust/Kernel` (Spec+Metatheory+Algorithm) | 17 | 17 |
| `Trust/Lib` | 40 | 56 |
| `Trust/Knot` | 112 | **149** |
| `Trust/Examples` | 62 | 112 |
| `Trust/Comparison` | 4 | 42 |

⇒ worst single check 235 → 149. Splitting `Knot` further has a floor near
**89** — that is `JudgeWfAA`'s own closure, which it already survives — so
the realistic best is ~2.4× on peak, not more.

⚠ THERE MUST BE NO SINGLE ROOT IMPORTING THE FIVE. A `Trust.agda` that
imports them all has the same closure as today and buys nothing.

⚠ Requires updating `gen-trust.sh` (emit N lists), `check-trust.sh` (diff
against the union) and `sweep.sh` (build all roots). Do it as its OWN
commit — this is the safety-critical artifact.

⇒ NOT URGENT: `sweep.sh`'s ladder now has a third rung (`-A8m -c`) and
`Trust` passes in 20s. Do this when it stops passing, or when a reviewer
would rather read five short lists than one long one.

## ⬜ `extRNK`'s NATURALITY — the last thing between half 2 and the knot

`Lib/ISub.isubMethod-red` is PROVED but takes `ExtNSub` and `FordMapSub`
as hypotheses. At the KNOT's renaming instantiation:

* `FordMapSub` is FREE — `renFordMap fi b p = p`, so it is `refl`.
* `ExtNSub` means `extRNK`'s naturality, and that is the open one.

    extRNK d n ρ = lam (app (app (extRK (pair sVar (nsuc (w d))) (var vz))
                                 (w n)) (w ρ))
    extRK i k    = ielim KnotD i extRMethsK k

`subTm` distributes structurally through `lam`/`app`/`ielim`, and the two
`w`s are `sub-w`. ⇒ **everything reduces to `subTm σ extRMethsK ≡
extRMethsK` — the 53-method tuple being closed.**

⚠⚠ DO NOT PROVE THAT BY UNFOLDING THE TUPLE. That is
`abstract-the-substituted-terms` verbatim, measured 87× elsewhere, and the
tuple is 53 methods deep. Use the occurrence route instead — `Spec/Variance`
has `occ-sub` and `Lib/IWk` has `pinned-stable`
(`(∀ x → occTm x j ≡ false) → subTm σ j ≡ subTm τ j`), which is the shape
this wants.

⇒ NEXT after that: `nrs`'s pointwise law (parked at 8 attempts, and the
interface fix it needs — `sel-here≡`/`sel-there≡`, `Lib/Wk.towerP` — is
already committed), then `sub-agree`/`ren-agree`, which is step 3 proper.
