# OCP-0009 — PLAN: QTT INTEGRATION

Companion to `PLAN-INDEXED.md` (syntax into the kernel) and
`PLAN-JUDGEMENT.md` (judgements into the kernel). This one adds the
**multiplicity discipline** — OCP-0009 Rung 5, the erasure invariant.

Branch: `ocp-0009-qtt-integration`. Merges back to the parent dHoTT
branch only if §4 lands; nothing here is a prerequisite for the knot.

⚠ **THIS IS AXIS 1 OF `PLAN-INTEGRATION.md`** — read that first. It
carries the compiler measurement this plan's decisions rest on, the
ordering (**axis 0, the prelude, comes BEFORE this file**), and the three
other axes. In particular: the grade is a record because *purity is on
the critical path to adoption*, not because records are tidy.

⚠ **THIS PLAN IS FOR THE POC.** The real compiler (`formal/Once`) has a
QTT of its own. §7 records what a cross-check against it settled — as
**evidence**, never as a dependency. `LESSONS.md` §5 stands: the POC owns
its syntax, and nothing here imports `formal/Once` or the normalizer's
CCC.

---

## 1. WHAT IS ESTABLISHED — do not re-spike any of this

### 1a. From the POC (`bootstrap/poc/OCP0009/`, 2026-07-12/13)

| | artifact | verdict | where |
|---|---|---|---|
| a | `Mult = {𝟘,𝟙,ω}`, `+ᵐ`/`·ᵐ`, 9 ordered-semiring laws, every case `refl` | ✅ `--safe` | `NbEPQTT` |
| b | usage vectors `Use Γ` + module structure `0ᵘ`/`+ᵘ`/`·ᵘ`, laws pointwise | ✅ `--safe` | `NbEPQTTJ` |
| c | a graded judgment `Γ ⊢[ρ] A` — **4 rules, simply typed** (`ι`, `×q`, `⇒[π]`) | ✅ but a TEMPLATE, not code | `NbEPQTTJ` |
| d | usage-masked runtime context `⌊Γ∣ρ⌋ᶜ`; `𝟘`-strengthening is DEFINITIONAL | ✅ — the key trick | `NbEPQTTEraseTm` |
| e | erasure soundness `erase-irrelevant`, by `refl` | ✅ **but only because CCC `β-fst` computes** | `NbEPQTTErase` |

**(a) and (b) port verbatim** — they need only `_≡_`/`refl`, which every
DirectedHoTT module already has. **(c), (d), (e) do not port**: (c) is 4
rules against this kernel's 43; (d) and (e) target `normalizer.Syntax.CCC`,
which `LESSONS.md` §5 forbids here.

### 1b. From the kernel — facts found by reading `Spec/`+`Metatheory/`

* ★ **`Cx` IS A BARE DEPTH** (`Spec/Syntax.agda:57`). So `Use ⌊Γ⌋` is a
  plain length-indexed vector — *simpler* than the POC's `Use Con`, which
  is indexed by a typed context.
* ★ **THE USAGE FUNCTION ALREADY EXISTS, IN `𝔹`.** `occTm`
  (`Spec/Variance.agda:109`) is the same recursion over all 30 `RTm` rows
  with `∨` where a usage recursion wants `+ᵐ`. Do not write it twice; three
  refinements separate them (§6b).
* ★ **`Variance` IS THE PRECEDENT FOR HOW TO ADD THIS.** Its header:
  *"in its cheapest honest form: a syntactic judgment on the RAW kernel
  types, additive-only (no existing module is touched; a JUDGMENT does not
  move the reduction side)"* — and `⊢tr` then consumes `PosC` as a premise.
  A grade discipline is the same shape of addition.
* ★ **`Algorithm/DecideConversion` IS FREE.** It is parametric in
  `dec-eq : (t u : RTm Γ) → Dec (t ≡ u)`; a grade has decidable equality.
  Zero change.
* ⚠ **REDUCTION CREATES `Π` TYPES.** `Hom-U` (`Spec/Typing.agda:545`) and
  `Hom-Π` (`:546`). A graded `Π` means a *reduction rule must invent a
  grade*. This has no counterpart in any QTT in the literature or in the
  compiler, and it is the first thing §2 says is unsettled.
* ⚠ **A PATH IS A FUNCTION HERE.** `tr-taut`
  (`Spec/Typing.agda:347`): `tr (var vz) (lam f) e ⟶ app (lam f) e`.
  Transport at the tautological motive **applies the path**. Directed
  univalence is a computation rule, so a `Hom` proof is a runtime value.

---

## 2. WHAT IS **NOT** ESTABLISHED

⚠ Read this before quoting §1 at anyone. Each row is a spike in §4.

* **`Hom` PROOFS ARE NOT UNIFORMLY ERASABLE.** The standard QTT-for-DT
  move — grade every identity proof `𝟘` and erase it — is **false in this
  kernel**. `Hom Nat m n` reduces to `Unit`/`base` (`Typing.agda:542`) and
  is erasable; `Hom U c d` reduces to `Π (El c) (El (renTm vs d))` and is
  a function you apply. Erasability is **type-directed, not
  former-directed**. `docs/proposals/OCP-0009…:1117` ("`0`-multiplicity
  bindings: equality/`Id` proofs…") is stale on exactly this point.
* **SUBJECT REDUCTION UNDER SUBUSAGING IS UNPROVEN.** §3 argues `sr`
  should need only *monotonicity* (`Ψ′ ⊑ᵘ Ψ`) rather than a usage
  equation. That is read off the shape of the order, not off a proof. If
  it is wrong, the cost of §4 roughly doubles and the plan should be
  re-decided, not ground through.
* **ELIMINATOR SCALING IS UNDECIDED, AND NOTHING SOLVES IT FOR US.**
  `⊢natrec`/`⊢elim`/`⊢ielim` (`Typing.agda:837/860/897`) run their
  step/method tuple an unknown number of times. Branch-join (`⊔ᵘ`) is the
  wrong tool — that is for choosing *between* branches. §7 records that
  the compiler dodges this by demanding a **closed** algebra; `⊢elim`'s
  methods are open terms in `Γ`, so the dodge is unavailable.
* **ERASURE VS `⟶ᵀ` IS UNTESTED.** Whether erasure commutes with type
  reduction, given that `Hom-U`/`Hom-Π` create `Π`s.
* **WHETHER `Pos`/`Neg` ARE GRADE-SENSITIVE.** Assumed not. Unchecked.
* **NO ERASING ELABORATION TARGET EXISTS.** The POC's target was the CCC
  `Term`. Here there is none, so the target must be `RTm` at a masked
  `Cx` (§4 step 5) — self-erasure, not elaboration.

---

## 3. THE DESIGN

Four routes were considered. The chosen one is **A″**.

| | route | verdict |
|---|---|---|
| A | grade the type; check usage by a FUNCTION over raw syntax, consumed as an `⊢lam` premise | ✗ — puts a **decider** in `Spec/`. The compiler's D134 / plan-0.80-A1 rule is right and applies: *the spec names properties, deciders stay in the implementation.* |
| B | usage as a judgment INDEX with exact accounting (`Γ ⊢[ρ] t ∷ A`, the POC's route (b)) | ✗ **for now** — exact accounting forces every `gen-*` inversion in `SubjectReduction` to owe a usage *equation*. Strictly stronger, strictly later. |
| A′ | grade on the arrow + usage synthesised as an output of **the** typing judgment + subusaging | ✗ — **fallback only**; the measurement below killed it |
| **A″** | **A′, but the graded judgment sits BESIDE the kernel one**: `Γ ⊢ᵍ t ∷ A ⨾ Ψ` with `forget : Γ ⊢ᵍ t ∷ A ⨾ Ψ → Γ ⊢ t ∷ A` | ✅ |

### ★ THE MEASUREMENT THAT DECIDED IT

Adding the usage output to `_⊢_∷_` itself puts a new index in every type
signature that names the judgment. Measured:

| | files | mention a typing derivation |
|---|---|---|
| `Lib/` | 40 | **33** |
| `Examples/` non-Knot | 62 | **59** |
| `Examples/Knot/` | 149 | **122** |

**214 of 251.** The `Π` grade field, by contrast, reaches only 77 files
and is almost entirely absorbed by a pattern synonym
(`pattern Π A B = Πg ωG A B` — valid in construction *and* match
position). ⚠ The tree uses **zero** pattern synonyms today, so this is a
new device and a decision, not a freebie.

Paying 214 files of signature bookkeeping for an index is a bad trade
when the alternative leaves `SubjectReduction`, `Confluence`,
`LogicalRelation`, `Canonicity`, `Lib/` and `Examples/` **untouched** —
they stay theorems about the ungraded skeleton, which is what they always
were.

### A″ in four sentences

1. `Π` and its code `⌜Π⌝` carry a **`Grade` record** — the *declared*
   bound. This IS in the kernel; see the warning below.
2. A **second judgment** `Γ ⊢ᵍ t ∷ A ⨾ Ψ` carries the synthesised usage,
   with `forget` down to the kernel judgment.
3. `⊢ᵍlam` relates declared and computed by **order, not equality**:
   body uses the binder at `q′`, arrow declares `q`, premise `q′ ≤ q`.
4. The kernel judgment, its metatheory, `Lib/` and `Examples/` do not
   change.

### ⚠ WHERE A″ WOULD BECOME A SHORTCUT

**The declared grade must be in the TYPE, in the kernel.** If the grade
lives only in the side judgment, `⊢conv` launders it across a conversion
and the whole discipline is decoration. The principled line is:

> **declared grade = part of the type (kernel); computed usage = a
> judgment about a term (layer).**

That is not an invention — it is the compiler's own architecture
(`ArrowKind` on the type, `Usage n` a separate vector, related by `≤`),
reproduced one level up. `forget` is the fibration's projection, which is
the shape `docs/proposals/…` §A.4b already commits to: *dependency is
structurally prior; grades layer on top.*

### ⚠ THE TWO COSTS A″ DEFERS — name them, do not discover them

1. **A theorem, and WHICH one is an open decision.** `forget` gives `sr`
   for the underlying term and says nothing about usage. If erasure is a
   one-shot elaboration, the debt is an **erasure-simulation** theorem
   (the POC's `erase-irrelevant`, off `refl`). If the grade must survive
   kernel reduction, the debt is **graded `sr`** after all. Different
   theorems — decide before §4 step 5.
2. **Rule-set drift, unprotected in one direction.** `forget`'s totality
   catches a graded rule with no kernel twin. The reverse is silent — add
   a kernel rule, forget its graded twin, nothing complains. That is
   `FormerCensus`'s bug exactly, and it has bitten this tree twice. §4
   step 4b is the fix, using the device already built.

⚠ **AND ONE HONEST LIMIT.** The compiler has *no* ungraded judgment —
`Usage` is an output of the only typing judgment there is. So A″'s split
is a DirectedHoTT-internal convenience; at adoption the compiler consumes
`⊢ᵍ` plus `forget` plus the metatheory, and the ungraded judgment becomes
internal. That composes, but do not mistake A″ for the shape the compiler
will inherit.

### Why a record and not a `Mult`

You pay the `Π`-field cascade across ~10 modules and 24k lines **once**.
The grade is a *product of orthogonal axes* — the compiler's is already
`Quantity × Purity`, and OCP-0007 proposes capabilities as a third.

★★ **AND PURITY IS NOT OPTIONAL LATER — IT IS ON THE CRITICAL PATH.**
`PLAN-INTEGRATION.md` §1e: the compiler's meaning is an effect trace
(`Behavior = ℕ → List SigOpEvent`), so `⟦_⟧ˢ` cannot be reached from a
purely pure kernel. `Purity` is the axis that gets there. A record field
absorbs it without touching `LogicalRelation` a second time; a bare
`Mult` guarantees paying the cascade twice.

```agda
record Grade : Set where
  constructor mk-grade
  field quantity : Mult
  -- purity: NOT cosmetic — see PLAN-INTEGRATION §1e.
  -- capabilities (OCP-0007): later, and free once this field exists.
```

### Why subusaging buys the plan

This matters only if the §3 fork lands on **graded `sr`** rather than
erasure-simulation — but if it does, it is the difference between
affordable and not. With **exact** accounting, β's reduct must use
*exactly* what the redex used, so every graded inversion owes a usage
equation. With **order**, β's reduct uses `q′ ≤ q` of the argument, so
the obligation weakens to

```agda
srᵍ : Γ ⊢ᵍ t ∷ A ⨾ Ψ → t ⟶ u → ∃[ Ψ′ ] (Ψ′ ⊑ᵘ Ψ × Γ ⊢ᵍ u ∷ A ⨾ Ψ′)
```

⚠ **This is the plan's load-bearing conjecture.** Spike it first (§4
step 0). Everything else is mechanical; this is not.

---

## 4. BUILD ORDER

### Step 0 — THE THREE SPIKES  ⬜

⚠ **Nothing in steps 1–5 is worth starting until these three answer.**
Each is a small module in `Examples/`, kept as a control afterwards.

| | spike | question | kill criterion |
|---|---|---|---|
| 0a | `sr` monotonicity at ONE rule (β at a graded `Π`) | does `Ψ′ ⊑ᵘ Ψ` close, or is an equation forced? | an equation ⇒ re-decide between A′ and B before proceeding |
| 0b | the grade `Hom-U` must invent | what grade does `Hom U c d ⟶ᵀ Π ? (El c) …` stamp? | no defensible answer ⇒ grade `Hom` proofs by ambient type instead, and `Hom-U`'s `Π` is `ω` |
| 0c | erasure vs `⟶ᵀ` | does erasure commute past `Hom-U`/`Hom-Π`? | ⇒ decides arity-preserving vs arrow-deleting erasure (§6c) |

### Step 1 — `Spec/Grade.agda`  ⬜ *(new, leaf, `--safe`)*

Port `NbEPQTT`'s semiring block **verbatim** (`Mult`, `+ᵐ`, `·ᵐ`, the 9
laws) and `NbEPQTTJ`'s vector block (`Use`, `0ᵘ`, `+ᵘ`, `·ᵘ`, the module
laws), retargeted from `Use Con` to `Use ⌊Γ⌋` over a bare depth. Add what
neither POC module has and §2 needs:

* `_⊔ᵐ_` / `_⊔ᵘ_` — the branch join;
* `_≤ᵐ_` **relational, not Boolean** — the derivation must be inductable
  on (D134's rule again);
* `_⊑ᵘ_` — pointwise order on vectors, with `⊑ᵘ-refl` and the two split
  witnesses `≤-+ˡ`/`≤-+ʳ`;
* `Grade` (§3) wrapping `Mult`.

★★ **AND THE JOIN'S LAWS — THE ONE THING THIS BRANCH PAYS BACK FIRST.**
`⊔` is defined on both sides and has **zero proven laws on either**
(`PLAN-INTEGRATION.md` §1b), while being load-bearing for the compiler's
`t-case` and for `⊢elim` here. Prove, in this module:

* `⊔` is the join for `≤` (`x ≤ x ⊔ y`, `y ≤ x ⊔ y`, and least);
* commutativity, associativity, idempotence, `𝟘` as unit;
* the interaction with `+` and `·` that `⊢elim` will actually need.

This module is pure algebra depending on nothing else in either tree.
**Hand it to the compiler regardless of whether the rest of axis 1
lands** — it is the cheapest item in the plan and the only one that is
useful even if this branch is abandoned.

⚠ Do not add lemmas to a heavily-imported module (`LESSONS.md` §3).
This is a leaf; keep it one.

### Step 2 — `Spec/Syntax.agda`: the grade on the formers  ⬜

`Π : ∀ {Γ} → Grade → RTy Γ → RTy (Γ ∙) → RTy Γ` and
`⌜Π⌝ : ∀ {Γ} → Grade → RTm Γ → RTm (Γ ∙) → RTm Γ`. Then the folds, all
one line apiece, all mechanical:

| | sites |
|---|---|
| `renTy`/`renTm`/`subTy`/`subTm` | `:286`, `:303`, `:343`, `:360` |
| the six `-cong`/composition lemmas | `:491`–`:850`, `cong₂ Π ↦ cong₂ (Π g)` |
| `Π-stable` | `:407` |

Open: **does `Σ'` get a grade too?** Standard QTT grades the first
component. Decide in step 2, not later — retrofitting it costs the same
cascade a second time.

### Step 3 — `Spec/Variance.agda`  ⬜

99 `Π`/`⌜Π⌝` sites, mechanical. **Do not** graduate `occTm` to `Mult`
here — usage is synthesised by the graded judgment in A″, not computed by
a function (§3). `occTm` stays what it is; §6b records what the graded
version *would* have been, in case B is ever taken.

### Step 4 — the KERNEL grade, then the GRADED JUDGMENT beside it  ⬜

**4a — `Spec/Typing.agda`, kernel side only.** In dependency order:

1. `_⟶ᵀ_`: `El-⌜Π⌝` (`:506`) threads the grade; `ξ-Πˡ`/`ξ-Πʳ`
   (`:522`–) mechanical; **`Hom-U` (`:545`) and `Hom-Π` (`:546`) take
   whatever step 0b settled.**
2. `Ctx`: `_▹_` carries the **declared** grade.
3. `⊢lam`/`⊢app` mention the declared grade. ⚠ **Nothing else in
   `_⊢_∷_` changes** — no usage index. That is what keeps
   `SubjectReduction`, `LogicalRelation`, `Canonicity`, `Lib/` and
   `Examples/` out of this plan (§3's measurement).

**4b — `Spec/Graded.agda` (new): `Γ ⊢ᵍ t ∷ A ⨾ Ψ` + `forget`.** All 43
rows, each with its usage output. Type-formation rows carry `0ᵘ` — a type
uses no runtime resource, and that IS the phase distinction, stated once.
`⊢ᵍlam` takes the subusage premise; `⊢ᵍapp` scales by the declared grade;
`⊢ᵍpair` adds; the eliminators take §6a's per-former table.

**4c — `Metatheory/GradedCensus.agda` (new): THE DRIFT GATE.** ⚠ Not
optional, and not a nicety. `forget`'s totality catches a graded rule with
no kernel twin; **the reverse direction is silent** — add a kernel rule,
forget its graded twin, and nothing complains. That is exactly
`FormerCensus`'s bug, which has bitten this tree twice (`ordtr`
2026-08-05, `icon`/`ielim`/`⌜IMu⌝` 2026-08-22). Same device, same
mechanism: `getDefinition` on `_⊢_∷_` and on `_⊢ᵍ_∷_⨾_`, assert every
kernel constructor is homed in ≥1 graded row, and NAME the orphans when
it fails.

⚠ Same limit as `FormerCensus`: it checks that a rule is *mentioned*, not
that the graded row says the right thing. Mentioning is the cheap shadow
of coverage — and it is the shadow that has actually caught things here.

### Step 5 — erasure, as an INVARIANT  ⬜

`Spec/Mask.agda` (or `Algorithm/Erase.agda` — decide when the shape is
known): the usage-masked context `⌊_∣_⌋ᶜ` from `NbEPQTTEraseTm`, with
`Cx` as *both* source and target. ★ The POC's four hand-written
projections (`prjˡ`/`prjʳ`/`prj¹`/`prjω`) collapse to **one order-indexed
family** here (§7) — and since the target is the same syntax, they are
plain `Ren`s, not CCC terms. This is strictly less code than the POC.

The theorem to aim at is **not** `erase-irrelevant` restated. It is:
*a `𝟘`-graded variable is not in the runtime context at all*, so
non-erasure is unrepresentable rather than merely unsound. §7 has the
argument for why that distinction is the whole point.

⚠ **DECIDE THE §3 FORK BEFORE WRITING THIS.** A″ defers a theorem and
which one depends on where erasure happens:

| if erasure is… | the debt is |
|---|---|
| a one-shot elaboration (grade, mask, then run the erased term) | **erasure-simulation** — the two reductions agree; the POC's `erase-irrelevant` generalised off `refl` |
| required to survive kernel reduction | **graded `sr`** (`srᵍ`, §3) after all |

Neither is free and they are not the same proof. Picking by default —
starting to write and seeing which one the goals ask for — is how this
lands in the wrong one.

### Step 6 — the knot  ⬜ **gated on `PLAN-JUDGEMENT` step D closing**

Do not start this until the 56 judgement rows are emitting. Then:

* `Grade` is a **numeral field** with a `< 3` ford — ⛔ **not an 8th
  sort**. `Knot/Sorts.agda:52` and `Negative/WkEmp` record what the
  8th-sort route cost when `Ctx` tried it.
* rows change shape (`jd⊢lam` is 13 fields today,
  `Knot/JudgeRows.agda:1039`); re-emit via `tools/gen-knot.py`, and the
  `_FLOOR` counts move with them.

---

## 5. COST — per module

★ **Under A″ the whole bill is the `Π` GRADE FIELD.** The graded judgment
is a new leaf module and costs nothing downstream. Everything below is
therefore *mechanical* except the two rows marked otherwise.

| module | lines | delta |
|---|---|---|
| `Spec/Grade` (new) | — | the algebra + the `⊔` laws (step 1) |
| `Spec/Syntax` | 1372 | ~20 fold clauses, mechanical |
| `Spec/Variance` | 1589 | 99 sites, mechanical |
| `Spec/Typing` | 1098 | `El-⌜Π⌝`, `ξ-Πˡ/ʳ`, `Ctx`, `⊢lam`/`⊢app` — **plus `Hom-U`/`Hom-Π`, a design decision, not a site** |
| `Spec/Graded` (new) | — | 43 rows + `forget` (step 4b) |
| `Metatheory/GradedCensus` (new) | — | the drift gate (step 4c) |
| `Metatheory/Injectivity` | 748 | `Π-inj` (`:707`) must also yield `g ≡ g′` — ★ **load-bearing**: without it `⊢conv` launders a grade and erasure is unsound. `Σ-inj` (`:740`) likewise if `Σ'` is graded |
| `Metatheory/Confluence` | 3726 | 120 `Π`/`⌜Π⌝` sites through the diamond cases |
| `Metatheory/SubjectReduction`(+`Base`) | 2444 | **the `Π` field only** — the judgment is unchanged, so no `gen-*` owes a usage witness. This is what A″ buys |
| `Metatheory/LogicalRelation` | 7007 | `⊩₀Π` (`:4210`) carries the grade; `irrel₀` at Π/Π (`:4598`) needs the grade equality from `Π-inj`; ~337 mechanical sites. Dominates build time — see `PERF.md` |
| `Metatheory/Fundamental` | 2046 | `fund-ty ty-Π` + `fund` at `⊢lam`/`⊢app` |
| `Metatheory/Canonicity` | 2081 | 141 sites; canonical forms at a graded `Π` |
| `Metatheory/RedCong`, `TySub` | 2343 | mechanical |
| `Algorithm/DecideConversion` | 110 | **0** — parametric in `dec-eq` |
| `Lib/`, `Examples/` non-Knot | 95 | **~77 sites, and a pattern synonym absorbs nearly all of them** (§3) |
| `Examples/Knot/*` | 149 | step 6, gated on `PLAN-JUDGEMENT` step D |

⚠ **The 214-of-251 figure in §3 is what A″ AVOIDS, not what it costs.**
Do not quote it as this plan's bill; quote it as the reason the bill is
not that.

⚠ `FormerCensus` is the tripwire for *formers*: anything new must be
homed in `SNe`/`SN`/`SNRed` or it names the orphan. It will **not** catch
a *field* added to an existing former — its own recorded limitation. The
grade field is exactly that shape, so nothing automated protects step 2.
Steps 2 and 4a need an `Examples/` control apiece.

---

## 6. THE PER-FORMER QUESTIONS

### 6a. Grades the judgement must assign

⚠ These are rows of `_⊢ᵍ_∷_⨾_` (step 4b), not of the kernel judgment.
Line numbers point at the kernel rule each one shadows.

| former | rule | grade | status |
|---|---|---|---|
| `⊢var` | `:715` | `singleUse x 𝟙` | settled |
| `⊢lam` | `:716` | body's tail, with `q′ ≤ q` | settled |
| `⊢app` | `:717` | `Ψf +ᵘ (q ·ᵘ Ψa)` | settled |
| `⊢pair`/`⊢fst`/`⊢snd` | `:719`,`:743`,`:744` | `+ᵘ` / pass through | settled |
| type formation (`⊢ty`, all codes) | — | `0ᵘ` | settled — this IS the phase distinction |
| `⊢natrec` | `:837` | `Ψz ⊔ᵘ (ω ·ᵘ Ψs) +ᵘ Ψn`? | ⬜ **open — §2** |
| `⊢elim`/`⊢ielim` | `:860`,`:897` | method tuple scaled by `ω`; branches joined by `⊔ᵘ` | ⬜ **open — §2** |
| `⊢tr`/`⊢jsub` | `:787`,`:825` | motive `0ᵘ`; **path NOT `0ᵘ`** (`tr-taut`) | ⬜ **open — §2** |
| `⊢ordtr` | `:739` | five `Hom Nat` proofs, all reducing to `Unit`/`base` ⇒ `0ᵘ` | ⬜ likely free, unchecked |
| `⊢absurd` | `:737` | scrutinee at `base` | ⬜ |
| `⊢hrefl`/`⊢idrefl` | `:760`,`:823` | code `0ᵘ`, term? | ⬜ |

### 6b. The graded `occTm`, if route B is ever taken

`Spec/Variance.agda:109` becomes a usage recursion under three changes,
recorded here so nobody re-derives them:

1. `𝔹`→`Mult`, `∨`→`+ᵐ`;
2. **`ω`-scale at recursive eliminators** — `natrec`'s `s`, `elim`/`ielim`'s
   `ms`; `occTm` merely `∨`s them;
3. **`𝟘` at type/code positions** — `occTm x (tr d p e)` counts the motive
   `d`; a usage recursion must not.

### 6c. Erasure's shape — arity-preserving or arrow-deleting?

The POC deletes the arrow (`⌊A ⇒[𝟘] B⌋ = ⌊B⌋`). §7 records that the
compiler deliberately does **not**. For this kernel there is an extra
argument for arity-preserving that the compiler does not have: `⟶ᵀ`
*creates* `Π` types, so an erasure that keeps the former can commute
with the congruence rules, and one that deletes it cannot. Step 0c
decides.

---

## 7. CROSS-CHECK: WHAT THE COMPILER DOES DIFFERENTLY

⚠ **EVIDENCE, NOT A DEPENDENCY.** Read on branch
`plan-0.83-0.80-0.59-spec-independence`; nothing here is imported. Fuller
measurement in `PLAN-INTEGRATION.md` §1.

★★★ **WHY THIS SECTION PINS THINGS, AND IS NOT DECORATION.** Adoption
(`PLAN-INTEGRATION.md` axis 3) joins the compiler at its erasure seam.
That seam is one of two things, and this table decides which:

| | if the two grade disciplines… | the seam is |
|---|---|---|
| ✅ | **agree** | **composition** — `_↾_`, `⊑ᵘ`, `restrictᴰ`, `eraseArrow` already exist on the compiler side and become the target directly |
| ✗ | **diverge** (exact vs subusaging, arrow-deleting vs arity-preserving) | **translation** — a bridge between two incompatible QTTs, carrying correctness obligations of its own |

Divergence is the worst outcome available in this whole plan, and it is
invisible until adoption unless pinned here. Every ✅ below is a decision
to stay composable; every ⬜ is an unpinned risk.

★ **THE SEMIRING ITSELF ALREADY AGREES**: `+q`/`*q` are the same
functions as `+ᵐ`/`·ᵐ`, table for table. What diverges is which theorems
each side has bothered to prove —

| law | POC | compiler |
|---|---|---|
| `·` assoc, distributivity | ✅ | ❌ |
| `≤` refl / trans | ❌ | ✅ |
| `⊑ᵘ-refl`, `≤-+ˡ/ʳ` | ❌ | ✅ |
| **`⊔` — anything at all** | ❌ | ❌ |

— which is why §4 step 1 is a *merge* of both law sets plus the join
laws neither has.

| | POC | compiler | taken into this plan? |
|---|---|---|---|
| grade structure | bare `Mult` | `ArrowKind = record { quantity; purity }`, orthogonal axes, own algebras | ✅ §3 — a `Grade` record |
| accounting | exact; `NbEPQTTJ` says *"no subusage order"* | `_≤q_`/`_≤q'_`; `t-lam : q′ ≤q q → …` | ✅ §3 — the plan's basis |
| usage position | judgment INDEX | judgment OUTPUT, bidirectional `⊢ᵢ`/`⊢ᶜ ⨾ Ψ` | ✅ §3 (output; **not** bidirectional — this kernel is declarative) |
| context | `Ctxq` bakes the multiplicity in | declared quantity in `Ctx` **+** separate per-subterm `Usage` | ✅ §4 step 4 |
| branches | absent | `_⊔ᵘ_`; `t-case ⨾ (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ))` | ✅ §4 step 1 — and §2 says it is only half the eliminator answer |
| the projections | four hand-written shapes | ★ ONE order-indexed family `restrictᴰ : Ψ′ ⊑ᵘ Ψ → …`, witnesses from `≤q'-+ˡ/ʳ` | ✅ §4 step 5 — the clearest single win |
| type erasure | `⌊A ⇒[𝟘] B⌋ = ⌊B⌋`, arrow vanishes | `eraseArrow Zero a b = Unit ⇛ b`, arity preserved | ⬜ step 0c |
| recursion | n/a | dodged: `t-cata-check` demands a **closed** algebra | ✗ **unavailable here** — §2 |

★★ **THE ONE THAT MATTERS MOST, AND IT IS NOT A REFINEMENT.** The POC
proves erasure is *sound*. The compiler makes non-erasure
*unrepresentable*. Its own commit says why, and the argument transfers to
this kernel unchanged:

> the spec's MEANING ignores the grade … so erasing and not-erasing are
> observationally identical and BOTH satisfy `correct`. QTT is
> load-bearing in the TYPING judgment … but inert in the meaning. So "a
> Zero-graded argument is not represented at runtime" is a RESOURCE
> guarantee nothing obliges the compiler to honour: a promise with no
> enforcement.

That is `OCP-0005`'s "prose decisions are silently violable" reached from
the QTT side, and it is why §4 step 5 aims at masking the context rather
than at restating `erase-irrelevant`.

★ **WHAT THE POC HAS THAT THE COMPILER DOES NOT.** Dependency. Every
question in §2 — a grade on a `Π` that reduction *creates*, a path that
*is* a function, erasability that is type- rather than former-directed —
is invisible at the compiler's simply-typed surface. If any of them
answers badly, that is a finding for the compiler too, not just for here.

---

## 8. STANDING CONSTRAINTS FOR THIS BRANCH

* ⛔ No import of `formal/Once` or `normalizer.Syntax.CCC`. The prelude
  names from `normalizer.Syntax.Types` (`_≡_`, `refl`, `sym`, `trans`,
  `cong`, `cong₂`, `subst`, `⊥`, `⊥-elim`) are what the other 235 modules
  already take, and are the only ones permitted.
* ⛔ No decider in `Spec/`. Properties in the spec, deciders in
  `Algorithm/`.
* ⛔ `Trust.agda` stays empty; `tools/check-trust.sh` is the gate.
* ★ Every library branch is exercised by an `Examples/` module —
  including each spike in step 0, which stays as its control.
* ⚠ Never run two Agda checks at once (`README.md`); exit 143 is not a
  verdict (`PERF.md`).
