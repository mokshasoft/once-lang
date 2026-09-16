# Computed datatype indices — the plan

*Decided 2026-09-16, from the profiling session of 2026-09-13/16. This is a
KERNEL change to `Spec/Typing`, reopening the metatheory. It is proposed
because the dogfooding exhibit measured a 267× cost with a known cause and
a known fix — which is exactly what the POC exists to find.*

--------------------------------------------------------------------------
## 0. The decision, in one line

**Every datatype constructor whose CONCLUSION contains a computed term
gets that term FORDED — replaced by a variable plus an explicit equation
argument — because a computed index makes the checker INVERT, and
inversion is unbounded search.**

### ★★ THE CRITERION — sharpened 2026-09-16, and it is the USER'S

⛔ NOT *"how big is the win?"* — that is reasoning from edit cost, which
[[principledness-over-edit-cost]] rules out for this POC.

★ **IS THE FORDED FORM EVER WORSE?** If it never is, ford it. The size of
the current win is IRRELEVANT to whether the construct is the right one.

⇒ so each candidate needs TWO measurements, not one:

| | |
|---|---|
| **A · the bad case** | a stuck eliminator in the computed term — how big is the worst case? |
| **B · the ordinary case** | no eliminator — is the forded form ever WORSE? |

**Ford iff B says never-worse.** A only sizes the prize.

⚠ AND "just fix the bad sites" IS NOT AN ALTERNATIVE. You can grep for a
construct, but you cannot see from a call site whether its type holds
something expensive — that invisibility IS the footgun. Finding the bad
sites requires profiling, which is how the 2026-09-13/16 session went.

--------------------------------------------------------------------------
## 1. The measurement that forces it

`tmp/ProbeFord` — one context, one lookup, one type containing a stuck
`ielim`, two formulations of the lookup judgement:

```agda
tc : Γ ∋c x ∷ A →                    (Γ ▹ B) ∋c vs x ∷ renTy vs A   -- COMPUTED
tf : Γ ∋f x ∷ A → renTy vs A ≡ A' → (Γ ▹ B) ∋f vs x ∷ A'            -- FORDED
```

| | ms |
|---|---|
| `lookC` — computed index | **15,998** |
| `lookF` — forded, plain `refl` | **60** |

**267×, with no naturality lemma — `refl` suffices.**

### 1.1 Why they differ, and it is not "the same work moved"

⚠ I predicted relocation, not saving, and was WRONG. The two ask for
different KINDS of work:

| form | what the checker must do |
|---|---|
| computed | solve `renTm vs ?ms ≡ myMeths` — **INVERT a renaming against a META** |
| forded | `A'` is fixed by the conclusion ⇒ both sides known ⇒ **CHECK** |

Agda printed the inversion constraint verbatim in `tmp/ProbeMatch4`:

```
renTm vs _ms_207 != myMeths
```

★ **This is `FUTURE.md`'s invariant 2 in miniature — *the checker never
searches*.** A computed index forces a search; fording replaces it with a
validation.

### 1.2 The chain it explains

| observation | |
|---|---|
| `⊢var (there here)` at a type holding a stuck `ielim` | **14,080 ms** |
| `⊢var here`, same type | **35 ms** |
| `⊢var (there² here)`, no eliminator | 49 ms |

⇒ **402× from one extra `there`**, and it is not lookup depth — the cheap
one is weakened MORE. It is one `renTy vs` over a type containing a stuck
eliminator, which forces the inversion.

⇒ and THAT is the whole `Judge` cost: 19-deep telescopes ×
`⊢var (there^k here)` × types carrying object-level eliminator calls.
Measured across 16 slots in two modules: **with** such a call
12,905–89,728 ms, **without** 44–1,537 ms, **no overlap**.

--------------------------------------------------------------------------
## 2. The audit — six datatypes, not one

Every kernel datatype whose constructor conclusion contains a computed
term:

| datatype | constructor → computed term | uses |
|---|---|---|
| **`_∋_∷_`** | `there`/`here` → `renTy vs A` | **7,581** |
| `_⟶_` | `β` → `subTm (single u) t`; `lam`/`app` → `renTm` | 1,880 |
| `_⊢_∷_` | `⊢app` → `subTy (single u) B` | 829 |
| `ICodeWf` | `icw-clo` → `εwkTm c` | 313 |
| `_⟶ᵀ_` | `Hom-U`/`Π` → `renTm` | — |
| `IDescWfFrom` | → `εwkTy` | — |

⚠ ONLY `_∋_∷_` IS MEASURED. The others are the same SHAPE; that is a
reason to spike them, not to assume them.

### 2.1 ✅ STEP 1 RAN, AND THE GATE **NARROWED THE PLAN** — 2026-09-16

`tmp/ProbeFordApp` puts `⊢app`'s `subTy (single u) B` in the same
position `tmp/ProbeFord` put `renTy vs A`. Three versions were needed
before it measured anything, and the progression is the finding:

| probe version | result | why |
|---|---|---|
| conclusion as `subTy (single u₀) Bel` | 904 ms, nothing in the table | syntactic match, no solve |
| conclusion substituted-out, `B` SPELLED | 65 / 29 ms | forward computation, no inversion |
| **`B` a HOLE — solved from the conclusion** | **UNSOLVED METAS, 883 ms** | **Agda REFUSES to invert** |

★★★ **THE GATE FAILS, AND USEFULLY.** Agda cannot invert
`subTy (single u) ?B ≡ C` and gives up INSTANTLY, where it inverts
`renTy vs ?A ≡ C` EXPENSIVELY and succeeds:

| operation solved-for | behaviour |
|---|---|
| `renTy vs ?A` | **inverts — 15,998 ms, succeeds** |
| `subTy (single u) ?B` | **refuses — unsolved meta, instant** |

⇒ **a renaming is structurally invertible; a substitution is not** (many
`B` substitute alike). Agda's INJECTIVITY heuristic fires for one and not
the other — the same counter that moved **1,431 → 3** in the `K`-motive
probe.

### 2.2 ⇒ THE AUDIT NARROWS FROM SIX TO **TWO**

The law is about **operations Agda will try to INVERT**, not about
computed indices in general:

| datatype | computed term | invertible? | verdict |
|---|---|---|---|
| **`_∋_∷_`** | `renTy vs A` | **YES** | ⬜ **FORD IT** — measured 267× |
| **`_⟶ᵀ_`** | `renTm` | **YES** | ⬜ spike, same shape |
| `_⟶_` `β` | `subTm (single u) t` | no | ⛔ leave |
| `_⊢_∷_` `⊢app` | `subTy (single u) B` | no | ⛔ **leave — MEASURED** |
| `ICodeWf` | `εwkTm = subTm εsub` | no | ⛔ leave |
| `IDescWfFrom` | `εwkTy = subTy εsub` | no | ⛔ leave |

### 2.3 ⚠⚠ CORRECTION — THE TABLE ABOVE IS **ONE WITNESS AND FOUR
###      INFERENCES**, and the inferences are a SHAPE MATCH

⚠ Caught by the user asking for the witness. What is actually held:

| datatype | evidence |
|---|---|
| `_∋_∷_` (`renTy vs A`) | **MEASURED** — 15,998 vs 60 ms |
| `_⊢_∷_` (`subTy (single u) B`) | **MEASURED** — refuses the backwards solve; 65 ms forward |
| `_⟶_` `β` (`subTm (single u) t`) | **NONE — inferred** |
| `ICodeWf` (`εwkTm = subTm εsub`) | **NONE — inferred** |
| `IDescWfFrom` (`εwkTy = subTy εsub`) | **NONE — inferred** |
| `_⟶ᵀ_` (`renTm`) | **NONE — inferred** |

⇒ I extrapolated ONE measurement to four datatypes on the grounds that
they are *"spelled with `subTm`/`renTm`"*. **That is the same shape-match
§2 was criticised for**, committed in the paragraph announcing that the
gate had prevented it.

**Two specific reasons the extrapolation may be WRONG:**

- ★ **`εwkTm = subTm εsub` is not a general substitution.** `εsub` runs
  FROM THE EMPTY CONTEXT, so `subTm εsub c` with `c : RTm ε` is a special
  case — plausibly one Agda inverts easily, there being almost nothing to
  invert. "Spelled with `subTm`" does not settle it.
- ★ **The `renTy`-invertible / `subTy`-not explanation is INFERRED FROM
  BEHAVIOUR**, not verified against Agda's injectivity machinery. It fits
  two data points, which is where most of this session's nine refuted
  models began.

### ⚠ AND THE `⊢app` VERDICT, MEASURED PROPERLY — **2.17×, AND REAL**

Five cold runs, both definitions in each:

| | samples (ms) | mean | sd | range |
|---|---|---|---|---|
| `appC` computed | 67 · 72 · 63 · 62 · 77 | **68.2** | 5.6 | 62–77 |
| `appF` forded | 29 · 35 · 29 · 30 · 34 | **31.4** | 2.6 | 29–35 |

**RANGES DO NOT OVERLAP** — the worst forded run beats the best computed
one by 1.8×. ⇒ it is a WIN, outside noise, and *"`⊢app` does not
reproduce"* was **wrong**: it reproduces at 2.17×.

⛔ **BUT IT IS STILL A BAD TRADE, FOR AN ECONOMIC REASON, NOT A
MECHANICAL ONE.** The 2.17× is a WORST CASE built on purpose — a stuck
eliminator in the codomain. Most of the 829 real uses are at ordinary
types where both forms compute in microseconds.

| | `_∋_∷_` | `⊢app` |
|---|---|---|
| measured | **267×** | 2.17× |
| where it lands | the HOT path — every deep lookup | a few sites with eliminators in the type |
| edit cost | 7,581 `refl`s | 829 `refl`s |
| verdict | **ford it** | **skip — fix the few sites directly** |

### ✅ AND THE "BAD TRADE" VERDICT IS **ALSO WRONG** — THERE IS NO TRADE

Challenged by the user: *"if we fix app we always get the same
performance or better … considering this as a POC to find the right
abstractions, I'm ok with paying the cost."* The empirical half of that
is testable, so it was tested — the same probe with an ORDINARY type
(no eliminator) beside the bad one:

| type in the codomain | computed | forded |
|---|---|---|
| **ordinary** (`K (pair sTy nzero)`) | 10 ms | **< 10 ms — below the reporting threshold** |
| **stuck eliminator** | 64–78 ms | **30–37 ms** |

⇒ **FORDED IS SAME-OR-BETTER IN BOTH.** Free where it does not matter,
2.17× where it does. **There is no trade**, so "bad trade" was wrong on
its own terms and not merely on principle.

⛔⛔ **AND THE REASONING WAS WRONG BEFORE THE NUMBERS WERE.** I argued
from EDIT COST — after being asked *"if we don't consider edit costs …
what would you propose?"*, and against this project's own recorded
decision [[principledness-over-edit-cost]]: *"OCP-0009 outputs a DESIGN;
rewriting call sites is recoverable, a formulation needing an axiom is
not."*

⚠ AND "fix the few sites individually" WAS NEVER AVAILABLE. You can grep
for `⊢app`, but you CANNOT see from a call site whether its `B` holds
something expensive — that invisibility is what makes it a footgun. The
only way to find the bad sites is to profile, which is how this entire
session went.

### ⇒ REVISED VERDICT: **FORD `⊢app` TOO**

| | `_∋_∷_` | `⊢app` |
|---|---|---|
| worst case | **267×** | 2.17× |
| ordinary case | — | **same or better** |
| closes a footgun | yes | **yes** |
| verdict | ⬜ ford | ⬜ **ford** |

★ The POC's output is a DESIGN. A construct whose cost is invisible at
the use site and unbounded in the type is the wrong design regardless of
how many sites currently trip it.

### 2.4 ⇒ THE STANDING TABLE

| datatype | computed term | A · bad case | B · ordinary | verdict |
|---|---|---|---|---|
| `_∋_∷_` | `renTy vs A` | **267×** | — | ⬜ **FORD** |
| `_⊢_∷_` `⊢app` | `subTy (single u) B` | **2.17×** | **never worse** | ⬜ **FORD** |
| `_⟶_` `β` | `subTm (single u) t` | ⬜ | ⬜ | ⬜ untested |
| `_⟶ᵀ_` | `renTm` | ⬜ | ⬜ | ⬜ untested |
| `ICodeWf` | `εwkTm = subTm εsub` | ⬜ | ⬜ | ⬜ untested |
| `IDescWfFrom` | `εwkTy = subTy εsub` | ⬜ | ⬜ | ⬜ untested |

### 2.5 ⚠ THE AUDIT ITSELF WAS WRONG — **FOUR CANDIDATES, NOT SIX**

Re-run excluding COMMENT lines (the original regex matched prose — e.g.
`IDescWfFrom`'s hit was a comment reading *"each constructor starts in
the telescope `◇ ▹ εwkTy I`"*). The real list of constructor conclusions
containing a defined function:

```
β        : … → app (lam t) u ⟶ subTm (single u) t        subTm
Hom-U    : … → Hom U c d ⟶ᵀ Π (El c) (El (renTm vs d))   renTm
here     : … → (Γ ▹ A) ∋ vz ∷ renTy vs A                 renTy
icw-clo  : … → ICodeWf (εwkTm {Θ} c)                     εwkTm
```

⇒ **`_⊢_∷_`/`⊢app` and `IDescWfFrom` were NEVER on the list** —
`⊢app`'s `subTy` is in `_⊢_∷_`, which the corrected scan does not flag,
and `IDescWfFrom`'s was prose. (The `⊢app` probe is still valid; it just
was not one of these.)

### 2.6 ★★★ THE SPLIT IS **RENAMING vs SUBSTITUTION**, measured

| operation, solved-for | Agda's behaviour |
|---|---|
| `renTy` / `renTm` | **INVERTS — expensively** (15,998 ms) |
| `subTy` | **REFUSES** — unsolved meta, instant |
| `εwkTm = subTm εsub` | **REFUSES** — unsolved meta, instant |

★ renamings are INJECTIVE, substitutions are not — so the injectivity
heuristic fires for one and not the other. ⚠ NOT the function/constructor
split I proposed mid-probe: `εwkTm` IS a function and Agda refuses,
`renTy` IS a function and Agda inverts.

### 2.7 ⇒ THE STANDING TABLE, corrected

| constructor | computed term | inverts? | A · bad case | B · ever worse? | verdict |
|---|---|---|---|---|---|
| `here`/`there` (`_∋_∷_`) | `renTy vs A` | **YES** | **267×** | — | ⬜ **FORD** |
| `⊢app` (`_⊢_∷_`) | `subTy (single u) B` | no | 2.17× | **never** | ⬜ **FORD** |
| `icw-clo` (`ICodeWf`) | `εwkTm c` | **no — measured** | none found | free both ways | ⬜ ford (usability only) |
| `Hom-U` (`_⟶ᵀ_`) | `renTm vs d` | ⬜ | ⬜ | ⬜ | ⬜ **untested** |
| `β` (`_⟶_`) | `subTm (single u) t` | ⬜ | ⬜ | ⬜ | ⬜ untested |

★ `icw-clo` has THE SHAPE BUT NOT THE EXPOSURE: 187 real uses, all
`icw-clo ⌜Nat⌝ ⊢⌜Nat⌝` — `c` explicit and tiny. The 688 `icw-ford _ _ _`
sites pass holes but `icw-ford`'s index is `⌜Id⌝ c a b`, a CONSTRUCTOR,
where inversion is structural and cheap. ⇒ fording it buys USABILITY
(holes become usable) not performance.

★ `Hom-U`'s renaming is in the TARGET and `c`/`d` solve from the SOURCE
`Hom U c d` — a constructor application — so `renTm vs d` computes
FORWARD. Predicted no exposure; ⬜ UNTESTED.

--------------------------------------------------------------------------
## 3. The order

1. ⬜ **spike `⊢app`** — ford `subTy (single u) B` in a probe and measure.
   Second data point, and the highest-frequency rule after lookup
   (829 uses; every application in every proof).
   ⚠ If it does NOT reproduce, the law is about RENAMING specifically and
   §2's audit must be re-scoped before any kernel edit.
2. ⬜ **ford `_∋_∷_`** in `Spec/Typing`. Reopens the metatheory.
3. ⬜ regenerate the 66 GENERATED files (free); repair the 117
   hand-written ones (mechanical — each site gains a `refl`).
4. ⬜ **re-measure `Judge/Elim`**. PREDICTION: `W_JΠΒ8`'s 89,728 ms —
   45% of that module — largely evaporates, since it is `⊢var` weakening
   against a 19-deep telescope. ★ This is the falsifiable claim; if the
   module does not move, the kernel change is not paying and should be
   reverted.
5. ⬜ the remaining five datatypes, each gated on its own measurement.
6. ⬜ **cost notes on the interfaces** — §4.

--------------------------------------------------------------------------
## 4. ★★ COST DOCUMENTATION ON THE INTERFACE

The deeper defect is that **the cost is invisible at the definition**.
Nothing at `there` says "this may cost 15 seconds". Convention, on every
kernel datatype and every large `Def`:

```agda
-- ⚠ COST: index is COMPUTED (`renTy vs A`) ⇒ the checker INVERTS.
--   Cheap when `A` is small; 15,998 ms when `A` holds a stuck `ielim`.
--   FORDED equivalent: 60 ms (`tmp/ProbeFord`).
-- ⇒ LAWS: `ren-∋` · `sub-∋`, in `Metatheory/TySub` (a layer up).
there : …
```

Three fields, each mechanically checkable:

1. **computed indices** — does a conclusion contain a defined function?
2. **size class** — is this a large `Def` that gets unfolded on comparison?
3. **laws, and where they live** — the lowest layer that can state them.

⇒ this is `FUTURE.md`'s invariant 1 (*unfolding is interface*) written as
prose until Once can express it as syntax. ⚠ AND TODAY IT MUST BE PROSE:
`tmp/ProbeMatch5` proved `ren-myMeths = refl` INSIDE a seal and Agda still
could not use it — **a sealed interface exports PROPOSITIONS, and the
checker needs COMPUTATION RULES.**

--------------------------------------------------------------------------
## 5. What this deliberately does NOT deliver

* **Ergonomics.** 7,581 sites gain a `refl`. In Once that belongs in
  ELABORATION — the surface inserts the equation, the core never
  computes. Here it is written by hand, and that is the POC paying for
  the finding.
* **A fix for object-level eliminators in types.** Fording removes the
  INVERSION; it does not make `ielim KnotD ms t` cheap. The Knot's
  `~15 s per eliminator call` stands until the encoding changes.
* **Sealing.** Measured 2×/3.1× on a `K`-motive probe (injectivity
  1,431 → 3) and **nothing** on Judge (injectivity 0.09%). Different
  mechanism, separate question.

--------------------------------------------------------------------------
## 6. ⚠ CONFIDENCE, stated plainly

**n = 1.** One probe, cleanly A/B'd, with a mechanism that explains both
it and an error message Agda printed independently. That is more than a
correlation and less than a law.

⚠⚠ AND THE SESSION THAT PRODUCED IT REFUTED NINE OF ITS OWN MODELS —
telescope depth, tail-renaming, motive size, index-reading, metas, the
tower machinery, description size, method-tuple sealing, and "fording
merely relocates the work". Every one looked right until measured.

⇒ **step 1 is a gate, not a formality**, and step 4 is the falsification
test for the whole plan.
