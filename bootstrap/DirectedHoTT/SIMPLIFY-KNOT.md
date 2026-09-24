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

## 1. ⛔ THE ONE-HOLE CONGRUENCE — **PROBED 2026-09-24, MEASURE NEGATIVE**

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

**(c) Factoring** — a congruence commutes with `»`, so a prefix repeated
across chain elements can be written once. Valid, needs no new lemma,
but measured at **183 sites / ~3 161 chars**, ~2.5% of the remaining
7 303 steps. ⚠ Measured three times before it was right: splitting on
`»` under-counted (14), a greedy regex over-matched and gave **0**, and
only a longest-common-prefix comparison gives 183. A cheap measurement
that disagrees with a hand-read example is wrong.

### ⇒ WHAT WOULD FLIP IT: `decTm`, and the idiom already exists

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

⬜ **The missing piece is `decTm : (s t : RTm Γ) → Maybe (s ≡ t)`** —
decidable equality on terms — without which `findCxt whole redex` cannot
recognise the redex. `decVar` exists for `Var`; `decTm` does not, and is
~30 clauses plus congruence. **That, not `⟶*-at`, is the real
prerequisite**, and it is the only path on which item 1 pays.

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
