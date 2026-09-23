# PLAN · `nf` — THE EVALUATOR

★ Rationale and evidence: `KNOT-LESSONS.md` §10. The Knot's proofs are
not `refl` because `_⟶_` is a **relation** and the kernel has no
evaluator, so every computation step is **witnessed** instead of
**performed**: **14 702 hand-built reduction steps vs 209 `refl`s**.

---

## 0. ✅ THE GATE IS ALREADY PASSED — the metatheory is in place

The one thing that could have blocked this is whether the kernel is
known to normalize. It is, **in this tree**:

| | | |
|---|---|---|
| `snorm` | `⊢ctx Γ → Γ ⊢ t ∷ A → SN t` | `Metatheory/Fundamental:2008` |
| `confluent` | `t ⟶* u → t ⟶* v → …` | `Metatheory/Confluence:3713` |
| `church-rosser` | `t ≅ u → Σ w (t ⟶* w × u ⟶* w)` | `Metatheory/Confluence:3719` |
| `sr` | `Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A` | `Metatheory/SubjectReduction:932` |

⇒ **strong normalization, confluence and subject reduction are all
PROVED.** `nf` is not blocked on open metatheory. `SN` is the inductive
(`sn-ne`/`sn-lam`/`sn-pair`/…) characterisation, not an `Acc`.

## 1. The shape of the work

`_⟶_` has **73 rules: 24 computation + 49 congruence.** But the Knot's
proofs are overwhelmingly concentrated:

| rule | uses |
|---|---|
| `βsnd` | 1150 |
| `β` | 980 |
| `βfst` | 795 |
| `ξ-pairʳ` | 232 |
| `jsub-refl` | 142 |
| `ξ-nsuc` | 71 |
| `ι-ielim` | 34 |
| `ξ-pairˡ` | 30 |
| `natrec-suc` / `natrec-zero` | 44 |

⚠ grep mentions, so imports and signatures are included — treat as a
**distribution**, not exact counts. The shape is robust: **the β-family
alone is ~2 925**, and the top ten rules are ~95% of all use.

★★★ **THE TRADE: ~73 one-line soundness cases, proved ONCE, replace
14 702 hand-built step constructions.**

---

## 2. Phases

### ✅ Phase 0 — THE GATE — **PASSED**, see §5 and §6

1. `step : RTm Γ → Maybe (RTm Γ)` — **β, βfst, βsnd, ι-ielim only**
2. `step-sound : step t ≡ just u → t ⟶ u`
3. `steps : ℕ → RTm Γ → RTm Γ` + `steps-sound : t ⟶* steps n t`
4. rebuild **ONE** existing `SzAgree` case as `steps` + `refl`

⛔ **GATE:** the case must close, and must not be slower than the
hand-built chain it replaces. If `steps` gets stuck where the hand chain
did not, or the elaborated term explodes, this plan is wrong and we
learn it for one module's work.
⚠ Run it against the EXISTING proof, not a fresh statement — a new
statement that closes proves nothing about the 14 702.

### ⬜ Phase 1 — the full `steps`, in `Lib/Eval.agda`

All 24 computation rules + congruence descent. Each soundness case is
one line. Deliverable: `steps` + `steps-sound`, `--safe`, no postulates.
⇒ this is what actually collapses the step constructions.

### ⬜ Phase 2 — `nf` proper (drop the fuel)

`snorm` already gives `SN t` for every well-typed `t`, so a fuel-free
`nf : Γ ⊢ t ∷ A → RTm Γ` is derivable.
⚠ **Fuel is not a compromise to be embarrassed by** — it *computes*,
which is the entire point, and SN says the fuel bound exists. Phase 2 is
optional for the Knot and should not block Phase 1.
⛔ **Do NOT recurse `nf` on the `SN` witness as the primary design.**
An `SN` obtained from `snorm` is a 2 046-line logical-relations
construction; it will not reduce, so `nf` would be total but **stuck** —
failing the one requirement (§10) that it COMPUTE.

### ⬜ Phase 3 — the other two multipliers (independent of `nf`)

`nf` does not touch these; they are separate wins on the same total:

| target | lines | fix |
|---|---|---|
| the `*Rows` encoding | ~19 800 | §9's typed elaborator (kernel needs nothing — measured) |
| the 103 object-level programs | the ledger | `enDeriv` — generic deriving from `IDesc` |

---

## 3. ⚠ WHAT WILL *NOT* DISAPPEAR

**The 53-row inductions stay.** Adequacy quantifies over all `t`, so
`⌈ t ⌉` is abstract and `steps` **sticks** on it (§10.5). `nf` removes
the step construction *inside* each case; it does not remove the case
analysis, which is genuine mathematical content.

⇒ so the honest prediction is **not** "the Knot disappears". It is:
the ~14 702 step constructions collapse, the `*Rows` encoding collapses
under Phase 3, the 103 programs collapse under `enDeriv` — and what
remains is a 53-row induction per property, which is what the Knot
*should* have been all along. No number is promised here until Phase 0
measures one.

---

## 4. ★ WHY THIS BEATS AGDA / COQ / LEAN

Not one feature — the **combination**, and two thirds of it already exist:

1. ✅ **The WF axis.** The order COMPUTES, so well-founded recursion needs
   no `Acc` and use sites fight no transports. Already won.
2. ✅ **First-class descriptions.** `IDesc` is **data**. Agda/Coq/Lean's
   `data` is a *closed front-end feature you cannot compute with* —
   generic programming there needs reflection (Agda reflection, MetaCoq,
   Lean macros), which is untyped or semi-typed metaprogramming. In Once,
   `derive-sub : IDesc → Program` is an **ordinary total function**.
3. ⬜ **Mechanized metatheory of its own kernel.** SN, confluence, subject
   reduction and canonicity are proved *here*, for *this* kernel. Agda's
   metatheory is not mechanized; Coq has MetaCoq (partial); Lean 4
   partial.

★★★ **The combination nobody has: DERIVE a generic program from a
description, and PROVE it adequate, inside the system, with the proof
being `refl`** — because `nf` computes and the metatheory that licenses
it is machine-checked.

⇒ **`nf` is the missing third.** It is what turns 1 and 2 from good
ingredients into that claim.

---

## 5. ✅ PHASE 0 RESULT — `Lib/Eval.agda` EXISTS AND COMPUTES

| step | status |
|---|---|
| 1. `ev1` for β/βfst/βsnd + congruence | ✅ `Lib/Eval.agda`, rc=0 |
| 2. soundness | ✅ **by construction** — see below |
| 3. `evN` (fuel) + soundness | ✅ rc=0 |
| 4. rebuild one **existing** `SzAgree` case | ✅ **DONE — and then all 29** |

### ⚠⚠ The obvious formulation FAILED, and the failure is the design

`ev1 : RTm Γ → RTm Γ` with a separate `ev1-sound` **cannot close**:

```
app (ev1 f) _u' != ev1 (app f a) of type RTm Γ
```

`ev1 (app f a)` is **stuck on an abstract `f`** — `ev1`'s β clause must
first learn whether `f` is a `lam`. ★ **The stuck-on-abstract problem
the Knot suffers everywhere reappeared inside the tool built to remove
it.**

★★★ **The fix: return the term WITH its chain** — `Red t = Σ (RTm Γ)
(λ u → t ⟶* u)`. Soundness becomes *construction*, nothing must reduce
in order to be proved, and the catch-all is a pair we **build**.

### ✅ AND IT COMPUTES — which is the only thing that matters

```agda
t0 = fst (pair (app (lam (var vz)) unit) unit)
runs-to-unit : val (evN 2 t0) ≡ unit
runs-to-unit = refl                       -- ← `refl`, inside Agda
```

⛔ **CONTROL** (`tmp/EvalProbeNeg`): one pass short must fail, and does —
`rc=42`, `app (lam (var vz)) unit != unit`. So `evN` genuinely steps;
the `refl`s are not vacuous.

⬜ Owed: a sweep — `Lib/Eval.agda` is new and unswept.

---

## 6. ✅✅ THE GATE IS PASSED — ON REAL KNOT ROWS

Every adequacy row in the tree opens with the **same three-β prologue**,
because `ifields` is three curried `app`s (§7):

```agda
agree i (var y0) =
  head-red tagTm-var memTm-var i _
    (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
     ⟶*-appˡ (step (β _ _) done) »
     step (β _ _) done)
```

★ `Knot/SzAgree`'s own header called this irreducible — *"THE THREE βs
CANNOT JOIN IT … they are emitted per row"*. **They can.** The whole
prologue is:

```agda
  head-red tagTm-var memTm-var i _ (chainOf (evN 3 _))
```

| measured on `Knot/SzAgree` (440 lines, 29 rows) | |
|---|---|
| rows that close with `chainOf (evN 3 _)` | **29 of 29**, rc=0 |
| lines | **440 → 382 (−58, −13%)** |
| time | 16.52 s → 15.09 s |
| peak RSS | 1 641 348 KB → 1 474 020 KB |

⛔ **CONTROL**: `evN 2` (one β short) **must** fail, and does — rc=42,
`!= nsuc (num 0) of type RTm Γ'`. The rows are really being evaluated.

⚠ **On the timings**: −8.7% / −10.2% is *inside* the ±12% noise floor
(`agda-rss-noise-floor`), one sample each. The honest claim is **no
regression**, not "faster" — and no regression is exactly what the gate
asked for.

### The size of the prize, from this rule family alone

| | |
|---|---|
| exact-match three-β prologues across `Examples/Knot/` | **231**, in 8 files |
| lines they occupy | **~462** |
| of those, generated (`SzAgree`) | 30 → fix in `tools/gen-knot.py` |
| hand-written (`Occ`/`Pw`/`PwBody`/`StkA`/`StkC`/`Flat`Agree) | 201 → direct edit |

⚠ That is the **β family only, at exact-match**. `ι-ielim` (34),
`natrec-*` (44), `jsub-refl` (142) and the `βfst`/`βsnd` uses in
*non-prologue* positions are **Phase 1**, and are the larger remainder
of the 14 702.

---

## 7. ✅ PHASE 0 LANDED — 7 FILES, 230 PROLOGUES, −435 LINES

### ⚠⚠ But the first design was WRONG, and the failure is the lesson

`evN` is a **parallel** pass — it also reduces inside **arguments**.
Against the real rows:

| | `evN` (parallel) | `evSpine` (spine only) |
|---|---|---|
| `SzAgree` / `PwAgree` / `StkAAgree` | ✅ rc=0 | ✅ rc=0 |
| **`StkCAgree` / `PwBodyAgree`** | ⛔ **rc=42** | ✅ rc=0 |

The failures were `enTm y0 != …` and `enVar y0 != …`: those rows'
continuations expect the payload **un-normalised**, and the parallel
pass had already reduced it.

★★★ **OVER-REDUCTION IS A REAL FAILURE MODE.** An evaluator that reduces
*more* is *less usable*, because a proof's later steps are written
against a specific partially-reduced term. `evSpine` walks only the
application spine — exactly the three curried `app`s `ifields` leaves
behind — so it cannot touch an argument.

### The landing

| file | prologues |
|---|---|
| `OccAgree` | 50 |
| `SzAgree` · `PwAgree` · `PwBodyAgree` · `StkAAgree` · `StkCAgree` · `FlatAgree` | 30 each |
| **total** | **230** |

- **all 7 rc=0** individually, then **net −435 lines**
- ⚠ **all 7 are GENERATED.** The fix is in `tools/gen-knot.py` as a
  single `_evspine()` post-pass over the emitted text — one auditable
  rule rather than four scattered emission sites, so it cannot miss one.
- ✅ the regenerated files are **byte-identical** to the hand-verified
  versions (`diff` clean on 4 of 7 spot-checked).

### ⚠ A methodology trap worth keeping

`head -1 | grep GENERATED` said **`generated=0`** for six of these files
— their headers word it differently. Six direct edits would have been
silently overwritten by the next generator run. ⇒ **test for generated
by the generator's write sites**, never by the header.

### ⬜ Next

Phase 1: `ι-ielim` (34), `natrec-*` (44), `jsub-refl` (142), and the
`βfst`/`βsnd` uses in **non-prologue** positions — the larger remainder
of the 14 702, and each is one more `evSpine`-style clause plus one line
of chain.

### Phase 0's measured effect on the headline number

| | |
|---|---|
| step constructions before | **14 702** |
| step constructions after | **12 632** |
| ⇒ removed by the β-prologue alone | **2 070 (−14%)** |

### ⬜ Phase 1 targets, sized

| idiom still hand-built | uses |
|---|---|
| `⟶*-snd done » step (βsnd _ _) done` | **381** |
| `⟶*-fst done » step (βfst _ _) done` | **192** |
| `⟶*-ielimᵗ …` | 342 |
| `step (jsub-refl _ _ _ _) done` | 123 |
| bare `step (βsnd _ _) done` | 849 |
| bare `step (βfst _ _) done` | 705 |

★ The top two are one idiom: a **projection chain** into a nested
`pair`. `ev1` already reduces `βfst`/`βsnd`; `evSpine` deliberately does
not. ⇒ **Phase 1's first move is an `evProj`** — reduce `fst`/`snd`
spines into a `pair`, and nothing else — which is 573 two-step chains
directly, and feeds the 1 554 bare uses.
⚠ Same discipline as §7: the narrowest evaluator that discharges the
obligation. Do **not** reach for a general `nf` here.

---

## 8. 🟡 PHASE 1 — PROJECTIONS DONE

Reaching into a method tuple was a hand-built two-step chain, **573
times across 12 files**. `Lib/Eval.evProj` walks a `fst`/`snd` spine
into a nested `pair` and descends into nothing else — same narrowness as
`evSpine`, for the same measured reason.

```agda
⟶*-snd done » step (βsnd _ _) done        →   chainOf (evProj 1 _)
⟶*-fst done » step (βfst _ _) done        →   chainOf (evProj 1 _)
```

| | |
|---|---|
| replacements | **573** (381 `snd` + 192 `fst`) |
| files | **12** — 490 in 7 generated, 83 in 5 hand-written |
| projection idioms remaining | **0** |
| every file | **rc=0**, verified individually before landing |

### The running total

| | step constructions |
|---|---|
| before any of this | **14 702** |
| after Phase 0 (the β prologue) | 12 632 |
| after Phase 1 projections | **9 767** |
| ⇒ removed so far | **4 935 (−34%)** |

⚠ The generated/hand-written split was determined from `gen-knot.py`'s
**write sites**, not from file headers — the lesson from Phase 0, applied
rather than re-learned. The generator's `_evspine()` post-pass now
carries both rules and emits whichever import it actually used.

### ⬜ Phase 1, still owed

| idiom | uses |
|---|---|
| `⟶*-ielimᵗ …` | 342 |
| `step (jsub-refl _ _ _ _) done` | 123 |
| remaining bare `βfst`/`βsnd` in other positions | ~1 000 |
| `natrec-suc` / `natrec-zero` | 44 |
| `ι-ielim` / `ι-elim` head steps | 45 |

### ★ The nested case: collapse to a FIXPOINT, not depth-by-depth

Phase 1's depth-1 substitution left the nested spines half-converted:

```agda
⟶*-fst (chainOf (evProj 1 _)) » step (βfst _ _) done      -- depth 2, 376
⟶*-fst (⟶*-snd (chainOf (evProj 1 _)) » step (βsnd _ _) done)
        » step (βfst _ _) done                             -- depth 3, 176
```

⇒ do **not** chase depth 2, then 3, then 4. One rule, iterated to a
fixpoint, handles any depth:

```
⟶*-X (chainOf (evProj N _)) » step (βX _ _) done   →   chainOf (evProj N+1 _)
```

⚠ **The congruence and the β must AGREE** (`fst`/`fst`, `snd`/`snd`) — a
mismatched pair is a different term and must not be collapsed. The rule
checks it and leaves mismatches alone.

★ This is sound because **`evProj` is idempotent past normal form**
(`evProj1 t = t , done` when there is no redex), so over-fuelling is
semantically free. The only cost is extra traversals in the elaborated
term — ⚠ to be MEASURED, not assumed.

Dry run: **376 collapses across 12 files.**
