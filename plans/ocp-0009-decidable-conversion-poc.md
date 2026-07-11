# Plan — OCP-0009 decidable-conversion POC: resume & next steps

**Target:** OCP-0009 (most-expressible-yet-provable dependent types via a small
core), and its shared decidability core with OCP-0004.
**Status:** conversion core PROVEN for the fragment (2026-07-11).
**Branch:** `ocp-0009-poc0-nbe`, head `2326d72b`, pushed to origin.
**Vehicle:** Agda 2.8.0, IR-only. The compiler is NOT touched — this is a
separate IR→IR consumer over `normalizer.Syntax.CCC`.

---

## 0. Where we are (banked)

The **conversion problem** — decidable equality, the heart of OCP-0009 — is
**solved and machine-checked for the fragment**. The principled NbE decides the
β-theory + every congruence + **product-η**, open terms included, **funext-free**.
All 20 `poc/OCP0009/*.agda` modules build green
(`bootstrap/check.sh poc/OCP0009/<M>.agda` → EXIT 0).

**There is no remaining research wall in the conversion core.** What is left is a
dependent/CwF layer (standard now that conversion is solved), IR wiring, and — on
a *different* axis — expressiveness (IR/II). The two missing η laws are
*conservative ergonomics*, not power (see §3).

### The strategic reframe (why this matters)
Just as OCP-0004's evaluator route replaced confluence+SN with a deterministic
evaluator, OCP-0009's conversion is a **deterministic NbE**: `conv t u := nf t ≡
nf u`. Determinism replaces confluence; a proven presheaf/NbE replaces a rewrite
system. Same decidability conclusion, no confluence/SN debt. This is the core
OCP-0009 contribution and it shares the OCP-0004 normalizer discipline.

---

## 1. What is proven (module map)

**Conversion track (evaluator/enumeration), postulate-free unless noted:**
- `Conv` — `conv` decides closed first-order conversion.
- `Complete` — `eval-sound`, `≈→conv` (**funext**).
- `Sound` — `conv` decides observational `_≋_` (closed first-order).
- `Finite` — `conv-fin` decides over finite domains.
- `Decidable` — `≋-dec : … → Dec (t ≋ u)`.
- `Higher` — `conv-h`, higher-order codomains / finite args (**funext**).
- `Dependent` — Vec-index conversion, e.g. `Vec-0+3 ≡ Vec-3` (**funext**).
- `Universe` — Π/Σ universe on the real IR (`U = μ UF`), `TyConv`, Π/Σ-cong (**funext**).
- `Open` — the definitional-vs-propositional split (`0+n ≋ n` refl vs `n+0` propositional).

**Prototype NbE:** `NbE` (ad-hoc engine), `NbEConv` (`conv-nbe`).

**Principled NbE (the real result):**
- `NbEK` — presheaf foundation: thinnings `_≼_`/`_⊚_` + category laws, `Ne`/`Val`,
  `wkNe`/`wkVal` + **functor laws proven**, reflect/reify. **Postulate- & pragma-free.**
- `NbEP` — fragment syntax `Tm` (`{Unit,×,+,μ}`, no `⇒`), `emb : Tm→Term`, η-long
  `eval`, principled `nf`.
- `NbEKF` — Kripke `⇒` for `{Unit,×,⇒}`.
- `NbEPNat` — `eval-nat` (eval natural w.r.t. weakening) + `reflect-nat`.
- `NbEPRel` — inductive logical relation `≈V` + reify/reflect-`≈V` + equivalence. **Postulate-free.**
- `NbEPFund` — `eval-cong` (fundamental theorem core) + all eliminator congruences.
- `NbEPNormal` — refinement 2 infra: `Normal` (η-long predicate), `reflect-normal`,
  `eval-normal` (eval preserves normality).
- `NbEPComplete` — **the theorem**: `≈β-complete : t ≈β u → nf t ≡ nf u`, where
  `_≈β_` = β + ⊙/pair/case/cata congruence + **`η-pair` (`⟨fst,snd⟩ ≈ id`)**.
- `Transparency` — status-board re-export.

### Escape inventory (honest)
- **funext** — `Complete`, `Higher`, `Dependent`, `Universe`. Standard axiom. NOT
  used by the principled NbE relation (`NbEPRel` is inductive/funext-free).
- **TERMINATING** — `NbE`, `NbEP`, `NbEKF`, `NbEPNat`, `NbEPFund`, `NbEPNormal`,
  `NbEPComplete`; each mirrors `eval`'s recursion. Discharging = standard SN /
  logical-relation argument (tedious, not deep).
- **NO_POSITIVITY_CHECK** — `NbEKF` only (Kripke closure domain).

### The one key trick (don't re-derive it)
The extensional-relation route to η **died** on `mapCata`-vs-projection commuting
at `⊗` on neutrals (commuting-lemma explosion = STC territory). The **`Normal`
(η-long) invariant sidesteps it**: at a product `Normal` *excludes* `vNe`, so the
`mapCata`-on-a-product-neutral case is **unreachable** for normal inputs → no
commuting lemmas. η-pair then closes by reflexivity. This is the standard
"η via normal forms."

---

## 2. The design principle that decides scope: cheap-η in, expensive-η as sugar

OCP-0009's north star is *small core + desugar the rest*. η laws split cleanly
along the **negative/positive** boundary, and that boundary is exactly the
cheap/expensive boundary for the conversion checker:

- **Negative types (Unit, ×, ⇒) — η is CHEAP.** Decided by `reflect` (η-long
  values) alone, no commuting conversions. **Bake into the core.** Done for
  product (`η-pair`, via `Normal`); Unit-η holds by construction (`reflect Unit =
  vUnit`); function-η is the same reflect-based story in `NbEKF`.
- **Positive types (+, μ) — η is EXPENSIVE.** `sum-η`/`μ-η` need sheaf NbE /
  commuting conversions. They are **conservative** (Hofmann: reflecting equalities
  into definitional equality proves *no new propositions* — see §3). **Leave them
  OUT of the core and provide as surface sugar** that elaborates to explicit
  propositional proofs (`J`/transport). Keeps the checker small and the TCB minimal.

So the boundary is not arbitrary: **decide the η laws that are cheap to decide
(negative), desugar the ones that are expensive (positive).** The POC already sits
exactly on this line.

---

## 3. Remaining gaps (categorized)

### A. Conservative ergonomics — DESUGAR, don't bake in
- **sum-η (`[inl,inr]≈id`) and μ-η (`In∘Out≈id`).** Fail even on normal values
  (case/`In` on a neutral wraps it). Would need sheaf NbE / STC. But by Hofmann
  conservativity they add **no theorems** — pure ergonomics → **surface sugar**
  (elaborate to explicit η-proofs), NOT core conversion. Cost of leaving out =
  transport clutter in terms, which is the *right* price for a minimal TCB.

### B. Large but KNOWN engineering (the real path forward)
- **CwF / dependent layer proper** — contexts (telescopes), Π/Σ as adjoints,
  reindexing, dependent conversion *under a context with variables*. Main piece
  toward actual decidable *dependent* types. Its historically-hard sub-part
  (open-term conversion) **IS the principled NbE** → standard construction on
  solved conversion, not a frontier.
- **Wire the principled NbE to the real bootstrap `Code`/`Term` IR** + the
  **OCP-0004 transparency / `EvalFullCorrectness`** obligation. Engine is proven
  over `Tm` (linked to `Term` via `emb`); connecting the *decision* to the real
  normalizer + transparency proof is the remaining wiring.

### C. Standard escapes to discharge (tedious, not deep)
- TERMINATING → prove via SN / logical relation. NO_POSITIVITY → defunctionalize
  the Kripke `⇒` (or accept). funext → keep as axiom.

### D. Expressiveness frontier (DIFFERENT axis — this is the one that adds power)
- **IR/II** (induction-recursion / -induction) — genuinely *more expressivity*
  (universes-as-data, internal Tarski universe, higher proof-theoretic strength):
  new definitions/theorems, not new equations. May not elaborate into the simple
  container core (OCP-9 FAQ Q9's open ceiling). Do this **if you need**
  universes-as-data. Unlike §A, sugar cannot supply this — it is real power.

---

## 4. Suggested next step (pick one)

1. **CwF/dependent layer** (highest value — conversion is solved). Start minimal:
   contexts as telescopes, Π/Σ formers, dependent conversion routed through NbE
   `nf`. New module `NbEPCwF` on `NbEP`/`NbEPComplete`.
2. **Wire to the real IR / OCP-0004 transparency** — run the decision on the actual
   `Code` normalizer, connect to `EvalFullCorrectness`. Closes "engine matches the
   real compiler."
3. **sum-η/μ-η as surface sugar** (NOT sheaf NbE) — elaborate the two positive-η
   laws to explicit propositional proofs; keeps the core checker small. The
   principled alternative to the research-grade sheaf-NbE investment.

Both refinements are DONE (case/cata congruence + η-pair). The proposal doc
`docs/proposals/OCP-0009-decidable-dependent-types.md` §6 records each milestone.
