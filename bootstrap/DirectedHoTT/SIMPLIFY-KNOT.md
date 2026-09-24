# SIMPLIFYING THE KNOT — the ideas, ranked, with their evidence

★ **The metric.** Not lines. `KNOT-LESSONS` §10 and the use-site
scorecard settled this: the Knot's difficulty is **how much a proof
author must know and write per row**, measured as

| | baseline | after Phase 0+1 |
|---|---|---|
| tokens written per row | 98 | **37** (−62%) ✅ |
| distinct combinators an author must **know** | 22 | **22** (unchanged) ⛔ |
| plumbing : genuine content | — | **15 : 1** ⛔ |
| adequacy stated as `⟶*` / as `≡` | — | **84 / 0** |

⇒ effort fell by nearly two thirds; **difficulty did not move at all.**
Everything below is ranked by whether it moves the second row, not the
first. Lines are a lagging indicator and are tracked separately
(`/tmp/knot_scorecard.sh`, and §6 here).

---

## 1. ★★★ THE ONE-HOLE CONGRUENCE — **SOLVED BY A MACRO**

**The single highest-value item, and it costs nothing to take.**

The 138 `⟶*-appˡ`/`⟶*-pairʳ`/`⟶*-icon`/… lemmas are not 138 theorems.
They are **the implementation of one theorem**, which is already proved:

```agda
subTm-monoˢ : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟶* σ' x) → (t : RTm Γ) → subTm σ t ⟶* subTm σ' t   -- RedCong:717
single-mono : {u u' : RTm Γ} → u ⟶* u' → ∀ (x : Var (Γ ∙)) → single u x ⟶* single u' x         -- RedCong:809
```

so the general congruence is **one line**:

```agda
⟶*-at : (F : RTm (Γ ∙)) {t t' : RTm Γ} → t ⟶* t' → subTm (single t) F ⟶* subTm (single t') F
⟶*-at F p = subTm-monoˢ (single-mono p) F
```

★ **The representation was already discovered here too**: `congAt`
(`Lib/ArithComm:499`) takes `F : RTm (Γ ∙)` — **a term with a free
variable IS a one-hole context**, the hole being `vz`. It was applied to
object-level identities and never wired to `⟶*`.

| | |
|---|---|
| `subTm-monoˢ` used by the **metatheory** | Confluence, LogicalRelation, TySub |
| `Confluence:535` | `subTm-monoˢ (single-mono (⟹→⟶* q)) t'` — **literally `⟶*-at`** |
| used by anything under `Examples/` | **nothing** |

⇒ the Knot hand-names 22 positions per row using lemmas that exist *only
to implement the theorem it should be calling*.

### ⛔⛔ PROBED IN THREE FORMS. ALL THREE MEASURE NEGATIVE.

| form | result |
|---|---|
| `⟶*-at F p = subTm-monoˢ (single-mono p) F` | ⛔ **does not typecheck at a use site** |
| one-hole context **datatype** (`Cxt`/`plug`) | ✅ typechecks, but vocab 22→**9**, tokens **UP**, inference ⛔ |
| factoring repeated congruence prefixes | ✅ valid, but only **183 sites (~2.5%)** |

**(a) The one-liner does not work** (`tmp/AtProbe.agda`):

```
subTm (single t) (renTm vs u) != u of type RTm Γ
```

★ A term-with-a-free-variable context forces a **weakening round-trip**,
and `subTm σ (renTm vs u) ≡ u` is precisely §7's stuck `wk-single`. The
formulation reads beautifully and is unusable.

**(b) The datatype salvage typechecks** (`tmp/CxtProbe.agda`, rc=0) —
`plug` computes structurally, so no substitution and no `wk-single`. But
it is **not a use-site win**: the 8 context constructors are themselves
vocabulary (22 → 9, not 22 → 1), the non-hole arguments must be written
by hand where the named congruences got them free by unification, and

```
plug _C_131 t = app t u : RTm Γ (blocked on _C_131)
```

⇒ **Agda cannot infer the context** — inverting `plug` is higher-order
unification. Converting a file by hand would be a REGRESSION in exactly
the metric that matters.

**(c) Factoring — ✅ TAKEN, and the measure was better than the first
framing suggested.** A congruence commutes with `»`, so a prefix repeated
across chain elements is written once:

```agda
⟶*-appˡ (⟶*-appˡ (chainOf (evProj 1 _))) »        ⟶*-appˡ (⟶*-appˡ (chainOf (evProj 1 _)) »
⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (…))) »        ⇒                        ⟶*-ielimᵗ (…) »
⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (…))) »                                 ⟶*-ielimⁱ (…))) »
```

★ **The structural argument is the better one**: the factored form says
*"in this context, do these three things"*, which is the actual
mathematical content; the repeated form hides it.

| | |
|---|---|
| sites | **188**, across 13 files, **0 remaining** |
| congruence tokens | 4 635 → **4 303 (−332, −7%)**; −13% in the dense files |
| every file | **rc=0** individually |

⚠ It **CASCADES** — collapsing one run brings the next two elements to
the same indent — so the generator iterates to a fixpoint, like the
projection collapse.

⚠⚠ **MEASURED FOUR TIMES BEFORE IT WAS RIGHT.** Splitting on `»`
under-counted (14); a greedy regex over-matched and gave **0**; only
longest-common-prefix gave 183; and the real figure after cascading is
188. **A cheap measurement that disagrees with a hand-read example is
wrong** — the worked example in `row-lam` was right every time.

### ★★★ IT FLIPPED — WRITE THE UNIFICATION AS A **MACRO**

⚠ **The verdict above is about Agda FUNCTIONS, and that was the wrong
place to look.** `decTm` and every `dec*` sticks on abstract arguments
because a function must COMPUTE at type-check time. A **macro** runs at
ELABORATION time, where the goal's *syntax* is concrete even when its
*terms* are abstract:

```agda
probe : {Γ : Cx} {t t' u : RTm Γ} → t ⟶* t' → app t u ⟶* app t' u
probe p = showGoal        -- ⇒ GOAL = app t u ⟶* app t' u
```

★ **And equality on `RTm` is not needed at all.** "Identical" is just
*"the parallel walk found no difference"*, so the recursion decides it.
The abstraction that blocks `decTm` lives in `RTm`; the walk runs on
`Term`, an ordinary datatype with concrete constructors.

✅ **BUILT AND MEASURED** (`tmp/CongMacro2.agda`, rc=0, `--safe`, no
`TERMINATING`):

```agda
t1 : {Γ : Cx} {t t' u : RTm Γ} → t ⟶* t' → app t u ⟶* app t' u
t1 p = cong! p
t2 : {Γ : Cx} {t t' u b : RTm Γ} →
     t ⟶* t' → app (fst (pair t b)) u ⟶* app (fst (pair t' b)) u
t2 p = cong! p            -- ★ THREE deep, and the author writes NOTHING
```

| | named congruences | `⟶*-at` + datatype | **`cong!` macro** |
|---|---|---|---|
| vocabulary | 22 | 9 | **1** |
| position written by hand | name it | full context | **nothing** |
| non-hole args | inferred | written | **inferred** |

⛔ **CONTROLS** — it fails rather than guessing:
· wrong chain supplied → `u != t of type RTm Γ`, rc=42
· former with no `congFor` entry (`lam`) → `Γ ∙ != Γ`, rc=42

⛔⛔ **APPLIED TO A KNOT FILE, AND IT DOES NOT WORK THERE.**
`Lib/CongMacro` is sound — `t1`/`t2` close three-deep, controls fail
correctly — but **every Knot site fails**, even a single converted one:

```
(blocked on _103)  (blocked on _t_80)  (blocked on _ihs_55)
```

★ The macro needs the goal DETERMINED when it elaborates. In the probes
the goal was a *declared type*; in the Knot it is a meta. And the cause
is structural: **`SzAgree` alone has 207 `_` placeholders against 79
congruences.** The Knot is written in a `_`-heavy style whose inference
runs AFTER macros do, so the two are incompatible.
⇒ to use `cong!` you would have to write those terms out explicitly,
costing far more than 22 → 1 saves.
⇒ **vocabulary stays at 22.** Kept in `Lib/` because it is correct and
may serve a future, less meta-laden caller — but do not reach for it in
the Knot.

★ **And reflection is ALREADY ESTABLISHED HERE**:
`Metatheory/FormerCensus` uses a `macro` under `--safe`, and its header
records *"`Agda.Builtin.Reflection` works under `--safe` (measured
2026-09-01)"*. This is not a new dependency.

### ⇒ THE ROUTE THAT DOES *NOT* WORK: `decTm`

★★ **Agda cannot infer the context, but WE CAN WRITE THE UNIFICATION
OURSELVES — and this project already does, 19 times.** `Lib/IWk` and
`Lib/ISub` carry a whole family that decides a structure and returns
EVIDENCE where the unifier fails:

```agda
Chk : {A : Set} → Maybe A → Set        -- Chk nothing = ⊥ ; Chk (just _) = ⊤
get : (m : Maybe A) → Chk m → A
decCon decSucs decPin decVar decNum decClosed decKa decSubIx …   -- 19 of them
```

⇒ the call site writes `get (decX …) tt`; a failed decision is a **type
error**, and success carries **no proof obligation**. That is exactly
"write the higher-order unification ourselves", and it is already Lib
vocabulary.

⛔ **MEASURED: `decTm` would NOT work, so do not build it.** The whole
`dec*` family sticks on abstract arguments:

```
decVar vz a != nothing of type Maybe (vz ≡ a)
```

⇒ same fundamental reason the equation gate failed: a structural
recursion cannot run when an argument's head is abstract, and adequacy
always has abstract heads. The 19 existing `dec*` procedures work
because they are applied to *structurally concrete* generator-built
terms. **~30 clauses that would not have paid.**

## 2. ⛔ ADEQUACY AS AN EQUATION — **GATE RUN, AND IT FAILED**

Adequacy is stated **84 times as `⟶*`, 0 times as `≡`**. A chain to a
SPECIFIC term must be built position by position, which is *why* the
author names congruences — and why the complete evaluator `evN`
**over-reduced**: the chain had to land on one particular term.

```agda
agree : szsTm i ⌈ t ⌉ ⟶* num (sz t)            -- today
agree : nf (szsTm i ⌈ t ⌉) ≡ nf (num (sz t))   -- proposed
```

★ Under an equation, normalising MORE is harmless — both sides are
normalised. Over-reduction stops being a bug.
⛔⛔ **RUN 2026-09-23 (`tmp/GateEq.agda`), and it does NOT work.** With a
deliberately over-reducing `evF` (β-family + ι-rule + congruence
everywhere), `gate-var` fails: `refl` cannot close, and the residue shows
the evaluator **stuck** at `evF1 i .Σ.fst` — `i`, the index, is abstract.

★ **The cause is FUNDAMENTAL, not a catch-all artefact**, and
`tmp/StuckWhy.agda` separates the two:

| | |
|---|---|
| structure concrete, argument abstract — `evProj 1 (fst (pair (var x) unit))` | **rc=0**, reduces ✅ |
| bare abstract term — `evProj 1 t` | **rc=42**, `evProj1 t .Σ.fst != t` ⛔ |

⇒ an evaluator is a **structural recursion**; it cannot reduce a term
whose HEAD is abstract. Writing 30 exhaustive clauses instead of a
catch-all would not help — a bound variable of type `RTm Γ` matches **no
constructor pattern**. And adequacy quantifies over `i` and `t`, so an
abstract head is always present, even per-row where `t` is a constructor:
`i` alone blocks it.

★★★ **AND THAT IS WHY THE CHAIN SHAPE EXISTS.** A chain `lhs ⟶* rhs`
never has to normalise the abstract parts — it only names the positions
where reduction happens and leaves everything else alone. **The chain is
the correct representation for reduction under abstraction**, not an
accident of how the Knot was written.

⇒ **This redirects effort to item 1, which was the better move anyway**:
the one-hole congruence lifts a chain *through* a context and is
completely indifferent to whether the context is abstract. It needs no
normalisation, so nothing can stick.

⚠ The **WF-axis fallback is moot** — it was insurance against the IH
thread losing structurality, and the gate never got that far.

## 3. ✅ THE EVALUATOR — landed, and its ceiling is known

`Lib/Eval`: `evSpine` (application spine), `evProj` (`fst`/`snd` spine).
230 β-prologues + 573 projections + 376 nested collapses.

| | step constructions |
|---|---|
| baseline | 14 702 |
| after Phase 0 + 1 | **7 303 (−50.3%)** |

⚠ **And its ceiling: it cannot move the vocabulary**, because each
walker hard-codes ONE traversal path while the rows reduce at arbitrary
positions. That is item 1's job, not more walkers.
⚠ Two measured design constraints, both learned the hard way:
- **over-reduction is a real failure mode** — the parallel `evN` broke
  `StkCAgree`/`PwBodyAgree` (`enTm y0 != …`) because their continuations
  expect the payload un-normalised. Each walker must be the NARROWEST
  that discharges its obligation.
- **return the term WITH its chain** (`Red t = Σ (RTm Γ) (λ u → t ⟶* u)`).
  A separate soundness lemma cannot close: `ev1 (app f a)` is STUCK on an
  abstract `f`. Soundness must be construction.

## 4. ⬜ `enDeriv` — 103 object programs from the description

The ledger is **103 hand-written object-level programs**, each with its
own adequacy proof, that are one function each in Agda.
★★ **This is where Once should BEAT Agda.** Agda's `data` is a closed
front-end feature you cannot compute with — generic programming there
needs reflection. Once's `IDesc` is **first-class data**, so
`derive-sub : IDesc → Program` is an ordinary total function.
Unrealised; the 103 programs are what its absence costs.

## 5. ⬜ THE TYPED ELABORATOR — the LINE lever (§8, §9)

`gen-knot.py` is not a printer: `translate_rule` is a parser for Agda
telescopes, `infer_sorts` is type inference, `infer_depths` is scope
checking — all of which Agda computed exactly when it checked
`Spec/Typing.agda`, and the generator discards and rebuilds approximately
("crude 31/43, structural 43/43" — 12 of 43 rules silently mis-depthed).

✅ **MEASURED (§9): the kernel needs NOTHING.** `Cx` is a unary natural
and `Var Γ` is `Fin (len Γ)`, so `infer_depths` is four lines of Agda,
refl-equal to the generator's hand-counted towers.
★ **And PIN `Γ`**: with the ambient context explicit, a mis-positioned
reference becomes a standalone type error (`ε != ε ∙ of type Cx`) — the
defect class that produced `occK` and `imethTyK`. With `Γ` inferred it
type-checks silently, which would relocate the bug rather than close it.

## 6. Line/step scorecard (lagging indicator)

| stage | lines | bytes | steps |
|---|---|---|---|
| 0 baseline | 52 396 | 2 602 670 | 14 702 |
| 1 Ph0 β prologue (230) | 51 943 | 2 582 361 | 12 632 |
| 2 Ph1 projections (573) | 51 970 | 2 573 775 | 9 767 |
| 3 Ph1 fixpoint (376) | 51 984 | 2 551 613 | **7 303** |

⚠ Lines are **−0.8%** while steps are **−50.3%** — Phases 1-3 are INLINE
substitutions. Do not quote lines as the win; quote the scorecard's
use-site rows.

## 7. ⚠ A GAP IN `find-dup-lemmas.py` — it finds duplicates, not generalizations

`find-dup-lemmas.py ⟶*-appˡ` returns **0 hits**, and would never have
found item 1: `subTm-monoˢ` is not "the same type modulo holes", it is a
**generalization**. The relation that actually shrinks a codebase is
*"N instances of one theorem"*, not *"two copies of one theorem"*.
⇒ see `AGDA-TYPE-SEARCH-PROPOSAL.md`; this is a new tier.

---

## 8. ★★ GENERALISING THE WF AXIS — "COMPUTE THE RELATION"

The WF axis's essence is **not orders**. It replaces an inductive
RELATION with a COMPUTING function plus an equation, so discharging it
becomes **conversion**. Applied more widely:

| relation | could compute as | status |
|---|---|---|
| termination / order | `Hom Nat` reduces | ✅ done — the WF axis |
| **de Bruijn lookup** (`here`/`there`) | `vsⁿ`-style computation | ⬜ **the migration — 75% of the wf burden** |
| `IConWf` / `ICodeWf` | `wfCon … ≡ true` | ⬜ needs the checker below |
| `Γ ⊢ t ∷ A` | a **bidirectional type checker** | ⬜ **§8.2 — do not forget** |
| occurrence | `occTm x t ≡ false` | ✅ already computes (Bool-valued) |

### ★ THE CRITERION FOR WHEN THIS MOVE WORKS

Everything this session turned on one line, and it is worth stating
once:

> **The axis-style move works exactly where the SUBJECT IS CONCRETE.**

- adequacy quantifies over abstract `t`, `i` ⇒ `nf` stuck, `decTm` stuck,
  the equation gate **failed**
- a macro sees concrete *syntax* at elaboration time ⇒ **worked**
- wf rows are about **concrete** contexts and `ICon`s ⇒ **eligible**

That predicts which relations are winnable, and it explains why `occTm`
already computes while `⟶*` never will.

### 8.1 The measured split — what the wf burden actually IS

`RedWfA` + `RedWfB` + `TyRedWf` + `Wf` = **9 944 lines**, ~19% of the
Knot, and the proof tokens in them are:

| | tokens | share |
|---|---|---|
| de Bruijn lookup (`there`/`here`) | **14 256** | **62%** |
| `⊢var` (the lookup wrapper) | 3 101 | 13% |
| genuine typing constructors | 5 583 | 24% |

⇒ **three quarters of the wf burden is variable lookup, not typing** —
and §9 already measured that a computing lookup is FOUR LINES, refl-equal
to the hand-counted towers. ⬜ That is the migration to do first.
⚠ The unproven step is the **derivation-level bridge**: §9 proved the
*terms* agree by `refl`; producing an `IConWf` derivation from a computed
lookup is a different obligation and is the first thing to test.

### 8.2 ⬜ THE BIDIRECTIONAL TYPE CHECKER — parked, NOT dropped

The remaining 24% needs `Θ ⊢ κ ∷ U` decided, i.e. a **bidirectional type
checker for the whole kernel**, plus its soundness proof
(`wfCon … ≡ true → IConWf …`). That is the largest single piece of work
identified anywhere in these notes — plausibly larger than everything in
§§1-7 combined.

★ **But it is also the biggest prize, and it is not only about wf:**
- it would decide `IConWf`/`ICodeWf` outright
- the `⊢…` derivations throughout the Knot become `refl`
- it is the same artefact `KNOT-LESSONS` §8 says the generator is
  *already* approximating in Python (`infer_sorts` IS type inference)
- ⇒ writing it once, in Agda, retires both the generator's inference AND
  the hand-built derivations

⚠ **Its eligibility is already established by the criterion above**: the
subjects are concrete generated rows, so a checker WOULD compute on them
— unlike everything that failed this session.
⬜ Not scheduled. Do not start it on the strength of a stub probe; do the
§8.1 migration first and re-measure.
