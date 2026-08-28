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
| ⬜ | **C2** — `Confluence`'s `⟹-⁺` `UnreachableClauses`; `check-formers` 4–6 | review list, not a build |

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
| 🟡 | **lookup methods 2–3** (`cVar-vz`, `cVar-vs`) | blocked on ⬇ |
| 🟡 | `⊢Var-vzKt` / `⊢Var-vsKt` — constructors at an ARBITRARY depth | `Knot/Build` — 3 round trips at 3 levels; 2 kinds of cast |
| ⬜ | the 50 computed rows' **typing** | `Lib/ISub` — `Lib/IWk` found 2 bugs here the term level could not |
| ⬜ | assemble `subTm` and its `⊢ielim` | |

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
| ✅ | `Lib/ISub` reuses `Lib/IWk`'s classification UNCHANGED |
| 🟡 | **`iatCon-wf`** — 2 of 3 cases proved; gates generalising `Lib/IPay` off `Nat` |
| ⬜ | `payStep` is MISFILED in `Lib/IWk` (both outside customers do substitution) |
| ⬜ | `sub-w`/`²`/`³`/`⁴` want INDEXING not listing (26 customers) |
| ⬜ | the assembly lemma itself |

⚠ **Open question marks**, in increasing severity:
1. `iatCon-wf`'s last case needs "substituting by a renaming IS
   renaming" — look for that lemma before writing one.
2. The mask may not be the last shape needed; `subTm`'s 50 computed rows
   are not typed yet.
3. "`sub-w`ⁿ wants indexing" is `Lib/Wk`'s CLAIM, not a measurement —
   and today's three-round-trips-at-three-levels is weak evidence
   AGAINST the simple version.
