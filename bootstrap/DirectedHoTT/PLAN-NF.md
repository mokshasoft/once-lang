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

### 🟡 Phase 0 — THE GATE — **3 of 4 DONE**, see §5

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
| 4. rebuild one **existing** `SzAgree` case | ⬜ **NOT DONE — the gate is still open** |

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

### ⬜ WHAT IS STILL OWED BEFORE THE GATE IS PASSED

**Step 4: rebuild one EXISTING `SzAgree` case.** The synthetic terms
above prove `evN` computes; they do **not** prove it fires on a real
Knot term, where the encoded subterm is abstract and `evN` may stick
exactly where the hand chain did not (§3). ⚠ Until that is done, this
is a working evaluator, **not** a demonstrated replacement for the
14 702 steps. Do not claim the trade until step 4 measures it.

⬜ Also owed: a sweep — `Lib/Eval.agda` is new and unswept.
