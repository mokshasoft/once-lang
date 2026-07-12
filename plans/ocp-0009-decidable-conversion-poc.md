# Plan — OCP-0009 decidable-conversion POC: resume & next steps

**Target:** OCP-0009 (most-expressible-yet-provable dependent types via a small
core), and its shared decidability core with OCP-0004.
**Status:** conversion core PROVEN for the fragment (2026-07-11); **CwF /
dependent layer (Rung 2) landed** — Π/Σ over the total core, open type-code
conversion decided by the principled NbE (2026-07-12); **Tarski decoder
`El : Code → Ty`** + code-driven context extension / terms-of-type (2026-07-12);
**base CwF FINISHED** — El welded to NbE conversion, indexed families (genuine
term-dependency, no IR), and the CwF term/comprehension layer (2026-07-12).
**Branch:** `ocp-0009-poc0-nbe`, head `2326d72b`, pushed to origin.
**Vehicle:** Agda 2.8.0, IR-only. The compiler is NOT touched — this is a
separate IR→IR consumer over `normalizer.Syntax.CCC`.

---

## 0. Where we are (banked)

The **conversion problem** — decidable equality, the heart of OCP-0009 — is
**solved and machine-checked for the fragment**. The principled NbE decides the
β-theory + every congruence + **product-η**, open terms included, **funext-free**.
All 22 `poc/OCP0009/*.agda` modules build green
(`bootstrap/check.sh poc/OCP0009/<M>.agda` → EXIT 0), including the new
`NbEPCwF` (CwF / dependent layer, Rung 2) and `NbEPEl` (Tarski decoder).

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
- `NbEPEl` — **the Tarski decoder + the rest of base CwF**. `Code` (first-order
  type-code family) + `El : Code → Ty`; reflection `⌜_⌝ : Code → Tm Unit U`
  lands codes as IR `U`-data agreeing with `NbEPCwF`'s smart constructors
  (self-hosting bridge). **Base CwF finished here:**
  - **`El-weld`** — El welded to NbE conversion: equal code-VALUES ⇒ equal
    decoded types, via a left-inverse decoder `decodeV : Val Unit U → Ty` that
    round-trips `El` (`decode-nfV`). Decoder lives on `Val` (the point-free
    `Term` can't be pattern-matched — `⟦One⟧F X = Unit` sends coverage into the
    `⟦F⟧F(μF) ≟ Unit` stuck state). Gap noted: value↔surface-`nf` link is
    `reifyVal`-injectivity on code-values (true, structural, unproven).
  - **Indexed families** (`Fam`/`Fib`/`Fib-cong`) — a dependent type over index
    `I` is an open code `Tm I U`; fibre `Fib F i = decodeV (eval (F⊙i) vUnit)`;
    convertible indices ⇒ equal fibres. `VecNat` = a **type-level cata** over the
    index (Natⁿ); `Vec (double 1) ≅ Vec 2` by `refl`. **Genuine term-dependency,
    NO induction-recursion.**
  - **CwF term layer** — `Tmᵗ`/`varᶜ`, term subst `_[_]ᵗ`, comprehension `_,ₛ_`,
    display map `pₛ`; comprehension laws `Cons-β-var`/`Cons-β-p`/`Cons-η` and
    `[]ᵗ-id`/`[]ᵗ-comp` all hold **definitionally under `nf`** (`refl`).
  - Code-driven context extension `Γ ▷ᶜ A = Γ ▷ El A`.
  - Honest ceiling, proven as `refl`: first-order `Π`/`Σ` decode NON-dependently
    (`El (a `Π b) = El a ⇒ El b`) — correct for a closed codomain; a codomain
    depending on the domain variable needs induction-recursion (§D, out of scope).
- `NbEPCwF` — **the CwF / dependent layer (Rung 2)**. The universe of type-codes
  `U = μ UF` lives inside the `{Unit,×,+,μ}` fragment, so Π/Σ/⇒/× are fragment
  morphisms `Tm _ U` and **type conversion IS the principled `nf`**. Delivers:
  contexts as telescopes (`Ctx`, `⟦_⟧C`), types-in-context `Typ Γ = Tm ⟦Γ⟧C U`,
  dependent conversion `Γ ⊢ A ≅ B := nf A ≡ nf B`, Π/Σ-congruence (from `≈β` +
  `≈β-complete`), and the type-substitution laws `Π[A,B][σ] ≡ Π[A[σ],B[σ]]`
  (`refl` — types are presheaves). **The new capability over `Universe.agda`
  (closed codes only): OPEN type-codes that mention the context variable, with
  computation UNDER the context** (β-redex on the variable normalized away),
  decided by `nf`. Postulate-free (reuses `NbEP`/`NbEPComplete`).
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
- **CwF / dependent layer — BASE CwF DONE (`NbEPCwF` + `NbEPEl`, Rung 2).**
  Contexts as telescopes, Π/Σ formers, dependent conversion under a context
  (open type-codes, computation under the context); Tarski decoder `El` welded
  to NbE conversion (`El-weld`); indexed families with genuine term-dependency
  and NO IR (`Fib`/`VecNat`, `Vec (double 1) ≅ Vec 2`); CwF term/comprehension
  layer with all laws `refl` under `nf`. This is exactly the "standard
  construction on solved conversion" this bullet predicted, now delivered.
  **What remains on this axis (post-base):**
  - **`reifyVal`-injectivity on code-values** — lifts `El-weld` from equal
    code-VALUES to the surface `nf ⌜c⌝ ≡ nf ⌜d⌝`. True/structural (each Val
    constructor reifies to a distinct `Term` head); a ~36-case induction, noted
    not proven. The one honest gap left inside base CwF.
  - **Identity type `Id` + `J`** (Rung 3) — turns indexing into a logic; a
    former *on top* of base CwF, the natural next rung.
  - Π/Σ as **adjoints** (the categorical universal-property presentation) and
    the remaining CwF equations beyond congruence + substitution-naturality.
  - **Dependent `Π`/`Σ` at the code level** (codomain depending on the domain
    variable) = induction-recursion — §D, a separate bill, not this axis.
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

**DONE — BASE CwF COMPLETE.** ~~CwF/dependent layer~~ (`NbEPCwF`, Rung 2):
contexts, Π/Σ formers, open-type-code conversion under a context, congruence,
substitution-naturality. ~~Tarski decoder~~ + ~~base CwF~~ (`NbEPEl`): `El`
welded to NbE conversion, indexed families (genuine term-dependency, no IR),
CwF term/comprehension layer. See §3.B.

1. **Identity type `Id` + `J`** (Rung 3) — the natural next rung: turns indexing
   into a logic (state and prove equalities). A former on top of base CwF. Pick
   intensional first. *(Or first close the `reifyVal`-injectivity gap in §3.B to
   fully weld `El-weld` to surface `nf` — smaller, tidies base CwF.)*
2. **Wire to the real IR / OCP-0004 transparency** — run the decision on the actual
   `Code` normalizer, connect to `EvalFullCorrectness`. Closes "engine matches the
   real compiler."
3. **IR/II** (§D) — the deliberate expressivity extension, taken as `Code`↔`El`
   *mutual* (universe + decoder together). Leaves the small-core discipline by
   design; do after base CwF is fully settled (this is the plan of record).
4. **sum-η/μ-η as surface sugar** (NOT sheaf NbE) — elaborate the two positive-η
   laws to explicit propositional proofs; keeps the core checker small.

Both refinements are DONE (case/cata congruence + η-pair). The proposal doc
`docs/proposals/OCP-0009-decidable-dependent-types.md` §6 records each milestone.
