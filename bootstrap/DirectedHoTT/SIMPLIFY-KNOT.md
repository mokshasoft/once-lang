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

## 1. ★★★ THE ONE-HOLE CONGRUENCE — already proved, unused, one line

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

**What it buys:** vocabulary **22 → 1**, and the position stops being a
NAME you must know and becomes **DATA you can compute** — which is what
makes it automatic rather than merely shorter.
⬜ Not yet done. Measure the scorecard's *vocabulary* row before/after.

## 2. ★★ ADEQUACY AS AN EQUATION, NOT A CHAIN — gate staged

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
⬜ `tmp/GateEq.agda` is staged, with an `evF` that deliberately
over-reduces (β-family + ι-rule + congruence everywhere).
⚠ **Expected failure mode**: `⌈ t ⌉` is abstract, so `nf` sticks on
subterms and the IH must still be threaded. ⇒ if that breaks
structurality, recurse on `sz t` with the **WF axis** making the order
COMPUTE — and `sz` already exists as an object program with its adequacy
proved. The fallback is in hand before the gate runs.

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
