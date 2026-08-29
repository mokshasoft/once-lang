# DirectedHoTT · TODO

⚠ **Tracking list.** The narrative lives in `PLAN-JUDGEMENT.md` and the
dated `HANDOFF-2026-08-NN.md`; the rules in `LESSONS.md`. This file is
just the checklist, newest state as of **2026-08-28**.

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
| ⬜ | step 3/6 — `⊢isubPay`'s two recursive cases | |
| ⬜ | step 4/6 — `⊢isubMethod` | |
| ⬜ | step 5/6 — the tuple at the mask | |
| ⬜ | step 6/6 — assemble `subTmK` + `⊢subTmK` (the `⊢ielim`) | |

## D. Step 3 — the judgement layer (~148 rows)

⚠ A judgement is ONE description, so none lands partially. The
judgements form a CHAIN and `_⟶_` is at the bottom, so **all of D is
gated on `subTm`**.

| | item | rows |
|---|---|---|
| ✅ | the row emitter + its control | `tools/gen-knot.py`, `Knot/LookupGen` |
| ⬜ | the `IConWf` emitter | — |
| ⬜ | `_⟶_` | 73 |
| ⬜ | `_⟶ᵀ_` | 26 |
| ⬜ | `_≅ᵀ_` | 4 |
| ⬜ | `_⊢ty_` + `_⊢_∷_` (mutual) | 43 |
| ⬜ | `Canon`, `Prog` | 20 |

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
| 🟡 | **`iatCon-wf`** — 2 of 3 cases proved; gates generalising `Lib/IPay` off `Nat` |
| ⬜ | `payStep` is MISFILED in `Lib/IWk` (both outside customers do substitution) |
| ⬜ | `sub-w`/`²`/`³`/`⁴` want INDEXING not listing (26 customers) |
| ⬜ | the assembly lemma itself |

⚠ **Open question marks**, in increasing severity:
1. `iatCon-wf`'s last case needs "substituting by a renaming IS
   renaming" — look for that lemma before writing one.
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

