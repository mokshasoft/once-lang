# PLAN — THE INDUCTIVE-TYPES AXIS

*Written 2026-08-13, after gates 1–5c. Successor to `SCOPE-INDUCTIVE.md`,
which scoped the axis before any of it was built; this document records
what is **done**, what is **decided**, and what is **left**, in order.*

Read with: `SCOPE-INDUCTIVE.md` (why the axis, and the description
language), `WF-LIBRARY.md` (D1–D11, the defect log), `ARCHITECTURE.md`
(the kernel map).

--------------------------------------------------------------------------
## 0. STATE IN ONE TABLE

| layer | status |
|---|---|
| description language (`DCon`/`Desc`, closed) | ✅ gates 1–4 |
| formers `Mu` / `con` / `elim` | ✅ in kernel |
| ι-rule + ξ rules | ✅ in kernel |
| confluence (`Conf`), type-level ⟹ (`Inj`) | ✅ |
| occurrence (`Var`), stuckness (`mustk?`, `LR`) | ✅ |
| SN layer (`SNe`/`SN`/`SNRed`/`Ne`) | ✅ |
| anti-renaming (`FundSN`), `Fund*` chain, `Canon`'s measure | ✅ |
| eliminator shape (gates 5/5b/5c, general) | ✅ **tupled, dependent, no η** |
| **typing rules** `⊢Mu`/`⊢con`/`⊢elim` in the kernel | ❌ **not started** ⬅ NEXT |
| subject reduction at ι, progress at ι | ⚠ **VACUOUS** — see §3 |
| the model, `⊩₀Mu` / the `MuMem` knot | ❌ **not started** |

`./sweep.sh` → ALL GREEN, 81 modules, 3 RED skipped.
`./check-formers.sh` → 26 formers / 0 orphaned; `UNMAPPED Mu` is §5.

--------------------------------------------------------------------------
## 1. WHAT IS DECIDED, AND WHY

### 1a. Descriptions are CLOSED. (`dκ : RTy ε → DCon → DCon`)

So a description mentions no ambient variable, `renTy ρ (Mu D) = Mu D`
holds ON THE NOSE, and every naturality clause is `refl`. An OPEN
description would need a parallel `renDesc`/`subDesc` development with its
own eight-lemma tower.

⚠ **Price:** `List A` for a *variable* `A` is not expressible. Open
descriptions are a later increment, not a bug.

### 1b. `lookupD` is TOTAL, and `⊢con` carries `k ∈D D`. (gate 5, Q21)

`lookupD` answers `dι` off the end, so `_⟶_` needs no
`lookup D k ≡ just C` side condition — determinism stays a pattern match
and confluence never inverts a `just`.

⚠⚠ **But totality RELOCATES the obligation, it does not remove it.**
`payTy D dι = Unit`, so an out-of-range tag with payload `unit` would be
typeable; ι then reduces to `sel k ms`, which bottoms out in `fst unit`
and has no type. **Subject reduction would be FALSE.** `⊢con` must carry
`k ∈D D`. The reduction relation stays side-condition-free; the discipline
lives entirely in typing.

### 1c. Methods are TUPLED, not curried. (gate 5c) ★ THE BIG ONE

| gate | motive | methods | result |
|---|---|---|---|
| 5 | non-dependent | curried | ✅ recursor |
| 5b | dependent | curried | needs `pair (fst p) unit ≡ p` |
| 5c | dependent | **tupled** | ✅ **no η** |

Curried `fields` hands the method `fst p`/`snd p` and never `p`, so the
method's result type can only mention the payload REBUILT from its own
binders. Needing η to identify that with `p` is **the symptom of an
information loss**, and it would couple this axis to the OPEN G4
conversion decision.

Tupled is also the principled form: a description denotes a FUNCTOR, the
payload IS the functor application, the method is its ALGEBRA
(`⟦D⟧ X → X`). The key move is `atCon k M = subTy (conS k) M`, re-basing
the motive at the PAYLOAD binder; then `atCon k M [ p ] ≡ M [ con k p ]`
by substitution composition alone — pointwise `refl` in every case.

⚠ Corrected while deciding: tupled does **not** avoid the substitution
tower (instantiating a type BUILT by substitution needs `subTy-subTy`
either way). Scorecard: **same tower, minus the η.**

### 1d. Elimination is DEPENDENT.

A recursor cannot prove anything BY INDUCTION over a user datatype, which
is the point of the axis. See `gcd-not-done-until-gaps-abc-closed` — the
same standard applies here.

--------------------------------------------------------------------------
## 2. STEP 1 — GENERALISE GATE 5c  ✅ **DONE** 2026-08-13

`SpikeIotaTup` (658 lines, `--safe`, no postulates, no holes) proves

    sr-ι-tup : Θ ⊢ m ∷ methTy D k C M →
               Θ ⊢ p ∷ payTy D C →
               Θ ⊢ fieldsT D ms C m p ∷ M [ con k p ]

for **arbitrary `DCon`** — no η premise, no restriction to the `suc`
shape.

What it took beyond the instance:

* `εwkTy` + `εwk-ren`/`εwk-sub` — a `dκ`'s CLOSED field type at any Γ;
* `payTy-ren`/`payTy-sub` — payloads are closed, so both actions are inert;
* **`ihTy-sub`** — the one genuinely new lemma: the IH tuple's
  substitution law, where `M` travels under `extS` and `q` under the
  substitution itself. Absent from the instance because one field has
  nothing to thread;
* `wk-single-id`, `sub-single-wk`, `subTm-id`/`subTy-id` — the plumbing;
* `ihs-ty` — the IH tuple inhabits its type at every field list.

★ `ihs-ty` carries the accounting that must match the model: a `dρ` field
  contributes an IH, a `dκ` field contributes **none** — skipped, not
  filled with a placeholder. That is exactly `SpikeDescSigma`'s `elimLift`
  ("a non-recursive field is not a recursive position, so no IH is owed"),
  so the term layer and the model layer agree on what a description means.

--------------------------------------------------------------------------
## 3. STEP 2 — THE KERNEL, ONCE

Do NOT land the recursor first and the dependent form after: the expensive
part is the CASCADE (`Subj`, `Canon`, `Fund` all re-open when `_⊢_∷_`
gains constructors), and doing it twice pays it twice.

1. **change `fields` to tupled** — the ι-rule's RHS. ~15 sites:
   `fields` + its 4 naturality lemmas, `p-fields`, `⟶*-fields`, `snr-ι`,
   `occ-fields`, and the ι rows in `⟶-sub` / `⟹-ren` / `⟹-sub` / `_⁺` /
   `snr-anti` / `snr-ren`.
   ⚠ `con`/`elim` **as formers** do not change, so Conf's 201 generated
   congruence clauses, `mustk?`'s three towers and the SN layer all stand.
2. `⊢Mu` / `⊢con` (with `k ∈D D`) / `⊢elim` (dependent motive).
   The kernel already ships `subTy-subTy` et al in `Pi`, so the tower
   comes for free.
3. **delete the vacuous blocks** in `Subj` (`sr`'s 4 rows) and `Canon`
   (`prog`, `usplit`) and prove them for real.
   ✅ *the check:* `check-formers.sh` check 4 must report **0** vacuous
   rows. It reports 4 today.

--------------------------------------------------------------------------
## 4. STEP 3 — DESCRIPTION WELL-FORMEDNESS

`⊢Mu` is currently unconditional; a garbage `dκ A` yields a type nothing
inhabits — permissive, not unsound. It becomes **required** for §5, where
`⊩₀ (Mu D)` needs `⊩₀ A` at every `dκ`. Mutual with `_⊢ty_`, so it grows
the mutual block — see `agda-perf-is-mutual-block-size`.

--------------------------------------------------------------------------
## 5. STEP 4 — THE MODEL (the `MuMem` knot)

`⊩₀` is a DATATYPE, so `Mu D` simply has no constructor today:
`⊩₀ (Mu D)` is UNINHABITED and everything about `Mu` downstream is
vacuous. `check-formers.sh` reports it as `UNMAPPED Mu`.

Gate 4 (`SpikeDescSigma`) and the merge (`SpikeIDescSigma`) cleared the
three-way knot in miniature —

    Lift ── calls ──▶ ⊩ ── unfolds to ──▶ MuMem ── declared with ──▶ Lift

— with positivity and termination passing. What the spikes did **not**
have: neutrals, expansion (`mm-exp` against real `SNRed`), and
anti-renaming. Those are the work.

--------------------------------------------------------------------------
## 6. STEP 5 — DOGFOOD, AND THE gcd GAPS

* **Dogfood:** `SpikeIDescSigma` Q17 already picked the target — `RTm`'s
  own shape (`var` as `dκ`, `lam` as a binding `ρ`, `app` as two `ρ`s).
  Judge the abstractions AT THE USE SITE (`judge-abstractions-at-the-use-site`).
* **gcd gaps A/B/C** (`gcd-not-done-until-gaps-abc-closed`): C first (one
  end-to-end run that actually RECURSES — today's only e2e test is
  gcd(2,0), the base case), then A (equations at VARIABLES, needs a
  propositional `Id` statement proved by dependent `natrec`), then B
  (divisibility — natural as an inductive family once §2 lands).

--------------------------------------------------------------------------
## 7. WHAT LATER INCREMENTS ARE EXPLICITLY DEFERRED

* **indexed** descriptions (`ρ : (I → I) → Con I → Con I`, gate 3) —
  needed for `Vec`, and for `RTm`'s own binding shape;
* **open/parameterised** descriptions — `List A` for variable `A` (§1a);
* the `⊩₀`/`⊩₁` split for `Mu`;
* an ORDER on `Mu` (the `Hom`-at-`Nat` analogue). `Mu` is INERT at the
  type level today, which is why `Inj` cost 10 clauses where `Nat` costs
  three endpoint-keyed unfoldings. If an order is wanted, that is where
  the cost arrives.

--------------------------------------------------------------------------
## 8. PROCESS, LEARNED THE HARD WAY 2026-08-13

* `./sweep.sh` — builds only what is SUPPOSED to be green. It skips RED
  modules (deliberate negative results), applies per-module RTS flags from
  the headers, and **refuses to start if another `agda` is running**.
  Every false alarm that day came from contention.
* **READ THE MODULE HEADER FIRST.** Three separate times the answer was
  already there — `LexSS2`'s `+RTS -c` requirement, D10's own correction
  about contention, and the RED markers — and I measured or inferred
  instead. This codebase documents itself unusually well.
* **A new `_⟶_` rule should ship with the STATEMENT of its
  subject-reduction obligation**, even if the proof is deferred. Writing
  the statement is what exposes the missing premise; that is literally how
  gate 5 found `k ∈D D`, three commits after the rule landed.
* `check-formers.sh` checks 4 and 5 make VACUITY and PROMISSORY NOTES
  visible. They report debt; they do not prove it payable.
