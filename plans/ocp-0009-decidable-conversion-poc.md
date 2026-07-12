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
All 23 `poc/OCP0009/*.agda` modules build green
(`bootstrap/check.sh poc/OCP0009/<M>.agda` → EXIT 0), including `NbEPCwF` (CwF /
dependent layer, Rung 2), `NbEPEl` (Tarski decoder + base CwF), and `NbEPId`
(identity type `Id` + `J`, Rung 3).

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
- `NbEPId` — **the identity type `Id` + `J` (Rung 3)**. Value-indexed `Id {A}
  (u v : Val Unit A)` with `Refl` and the FULL dependent eliminator `J` (real,
  by pattern matching); `transp`/`Id-sym`/`Id-trans` from `J`. Term-level
  `Id-tm a b` is inhabited by `Refl` exactly when `a,b` convert (share the NbE
  value) — conversion reflected as a `J`-computing propositional equality
  (`Id (double 1) 2` by `Refl`, also at a code type `IdTy`); `Id→conv` sound.
  Honest boundary: `Id` = decidable conversion here; a proof-relevant
  intensional `Id` (proving `n+0=n` by induction) needs `Id` as a primitive
  NbE former or an axiom — named, not built.
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
  **Base CwF has NO unproven gap:** `faithful` (`nf ⌜c⌝ ≡ nf ⌜d⌝ → c ≡ d`, the
  reflection is injective) closes the former `reifyVal`-injectivity caveat, so
  `El-weld-nf` welds `El` to the checker's actual `nf` decision.
  **What remains on this axis (post-base):**
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

**DONE — Rung 3.** ~~Identity type `Id` + `J`~~ landed as `NbEPId`: value-indexed
`Id` + genuine dependent `J`; `Id-tm` reflects (decidable) conversion as a
`J`-computing propositional equality. Base CwF's `reifyVal`-injectivity gap is
CLOSED (`faithful`/`El-weld-nf`). Remaining next steps:

1. **Proof-relevant intensional `Id`** — the current `Id` = decidable conversion;
   proving `n+0=n`-by-induction (the `Open.agda` residual) needs `Id` as a
   primitive NbE type-former with an inductive eliminator, or an axiom (funext).
2. **Native indexed inductive families** (Rung 4) — the typing relation `⊢` etc.
   as datatypes; unlocks "phrase compiler correctness as a type." (Current
   Vec-via-open-codes is genuine but ad hoc.)
3. **Universe hierarchy** — one first-order universe today; a tower unlocks
   polymorphism + large elimination.
4. **Wire to the real IR / OCP-0004 transparency** — run the decision on the actual
   `Code` normalizer, connect to `EvalFullCorrectness`.
5. **IR/II** (§D) — the deliberate expressivity extension, `Code`↔`El` *mutual*.
   Leaves the small-core discipline by design; after base CwF is fully settled.
6. **sum-η/μ-η as surface sugar** (NOT sheaf NbE) — the two positive-η laws to
   explicit propositional proofs.

Both refinements are DONE (case/cata congruence + η-pair). The proposal doc
`docs/proposals/OCP-0009-decidable-dependent-types.md` §6 records each milestone.

---

## 5. Expressibility positioning vs Agda / Coq / Lean / Idris

**One-line:** Once-with-OCP-0009 sits at ≈ **λP + a single first-order (Tarski)
universe + indexed families + a *definitional* identity type** — a *minimal*
dependently-typed core. Below Agda/Coq/Lean/Idris2 *as proof assistants*, but
optimizing a different objective (small decidable core + self-hosting), not
proof-theoretic strength. "Built" = machine-checked in `poc/OCP0009/`.

| Axis | Once (OCP-0009, built) | Agda | Coq | Lean 4 | Idris 2 |
|---|---|---|---|---|---|
| **Dependent Π/Σ** | ✅ Rung 2, decidable via NbE | ✅ | ✅ | ✅ | ✅ |
| **Inductive types** | ✅ strictly-positive containers (μ = W-types) | ✅ | ✅ | ✅ | ✅ |
| **Indexed inductive families** | ⚠️ ad hoc — Vec via open-code decoding; native = Rung 4, unbuilt | ✅ | ✅ | ✅ | ✅ |
| **Universe structure** | ⚠️ one first-order Tarski `U`; no hierarchy/poly | ✅ ∞ + poly | ✅ ∞ + impred. Prop | ✅ ∞ + poly | ✅ cumulative |
| **Identity type** | ⚠️ *definitional* `Id`+`J` (= decidable conversion) | ✅ intensional (+cubical) | ✅ intensional | ✅ + quotients→funext | ✅ intensional |
| **Conversion** | ✅ βη **+ product-η + terminal-η, funext-free** (NbE) | βη, partial η | βη, partial η | βη + defeq proof irrel. | βη |
| **IR / II** | ❌ deferred (§D) | ✅ **the standout** | ❌ | ❌ | ❌ |
| **Coinduction** | ❌ inductive-only core (ν → propositional side) | ✅ | ✅ | ✅ | ✅ |
| **Totality** | ✅ total-only (SN core) | ✅ | ✅ | ✅ | ⚠️ total *or* partial |
| **Erasure / quantities** | 🔜 Rung 5 (QTT, by-design) | ✅ irrelevance | ⚠️ extraction | ✅ Prop-erasure | ✅ QTT native |
| **Self-hosting / reflected IR** | ✅ **distinctive** (prove-Once-in-Once) | ❌ | ❌ | ❌ | ❌ |
| **Kernel / TCB size** | ✅ **minimal by thesis** | large | large (CIC) | smallish CIC | medium |

**Honest gaps, biggest first:** (1) **IR/II** — the largest gap, and only vs
Agda (Coq/Lean/Idris lack it too); deliberately deferred. (2) **Universe
hierarchy** — one universe, not a tower. (3) **Native indexed inductives**
(Rung 4) — the Vec-via-open-codes trick is genuine but ad hoc. (4)
**Proof-relevant intensional `Id`** — the built `Id` = decidable conversion; the
big assistants' `Id` proves strictly more (`n+0=n` by induction).

**Where Once is genuinely different / ahead:** conversion is *more extensional*
than Coq/Agda's (product-η + terminal-η, funext-free); **self-hosting with a
reflected IR** (none of the four are); a **minimal decidable core** with no
confluence/SN debt (deterministic NbE shared with the compiler normalizer). A
different point on the design manifold — not strictly dominated.

---

## 6. Strategic reframing — foundations-first, to lead on every axis

**Goal (raised):** not "a minimal core + desugar," but **best-in-class on every
row of §5's table**, won through *principledness + cleanness* rather than
feature-accretion. The big systems earned their rows by bolting features onto a
growing kernel over years (Agda: IR, then sized types, then cubical as a
*separate* mode; Coq: coinduction, universe poly, SProp) — which is *why* they
are not clean. To lead on principledness we do the opposite: **find the few
foundational mechanisms from which many rows fall out at once.**

The rows are not independent — they cluster:
- **Universes + IR + large-elimination are ONE mechanism** (Dybjer–Setzer: IR
  *is* defining a universe). So the universe row and the IR/II row (§3.D) MERGE:
  do the inductive-recursive Tarski universe *properly*, and win both. This
  **inverts** the earlier "stratify to avoid IR" advice — that was right for the
  minimal-core thesis, wrong for the domination goal.
- **Identity + funext + quotients + indexed families cluster in the equality
  mechanism.** Once already holds an asset here: the NbE decides βη + product-η +
  terminal-η **funext-free** — a running start toward **Observational Type Theory
  (OTT)**.

### The revised order (foundations-first)

This **inverts** the old "defer IR / definitional-`Id` stopgap" choices, which
were correct only for the minimal-core thesis.

1. **QTT (quantitative type theory) — NEXT.** Multiplicities `0/1/ω` (erasure +
   linearity) on the settled Π/Σ/μ core. Aligns with "impose erasure from Rung 2
   onward as a design invariant" (§6-of-proposal / old Rung 5). Lower-risk,
   independently valuable, and — key — it makes the later equality/universe work
   **erasure-aware by construction**. It also *informs* the equality choice: QTT
   wants **erasable** equality (see the OTT-vs-cubical note below).
2. **Equality foundation = OTT** (+ quotient types), *not* classical cubical.
   Chosen for (a) architectural fit with the deterministic NbE, and (b)
   QTT-erasability. Replaces the definitional-`Id` stopgap (`NbEPId`) as the
   principled target.
3. **Universe-as-IR** — the single mechanism for the universe + IR/II rows.
4. Native indexed inductives, coinduction (the genuinely-hard/contested row),
   then the summit (prove Once in Once).

### Honesty on "dominate every line"

- **Genuinely winnable:** kernel/TCB, self-hosting/reflected IR (already unique),
  conversion/η (already ahead), **identity via OTT** (the NbE asset makes this a
  real shot at best-in-class), **universe+IR via a clean IR-universe**.
- **Contested — nobody has solved these cleanly, so "dominate" = best tradeoff,
  exceptionally clean, not "strictly beat":** **coinduction** (Agda sized-types
  soundness history; Coq guardedness brittle) and the **equality wars**
  (HoTT/cubical vs OTT vs setoid is *live research*).
- **TCB caveat (why size is less decisive for Once):** the summit is
  self-verification, so a *verified* larger kernel can out-trust an unverified
  small one. But self-verification **relocates** the TCB, not eliminates it
  (Gödel: a stronger kernel needs a stronger metatheory to verify; bounded by the
  diagonalization ceiling). So kernel size still matters, just less absolutely.

### Note for later — HOTT vs cubical (the univalence question)

Recorded so it can be picked up when the equality foundation is built:

- **The real objection to classical cubical for Once is COMPUTATIONAL, not TCB
  size.** Cubical's Kan-composition / `transport` normalization is intricate and
  stresses exactly the *deterministic NbE shared with the compiler* (OCP-0004)
  that Once's other wins depend on. OTT fits that architecture; cubical fights it.
- **QTT × cubical friction:** cubical **paths are computationally relevant**
  (`transport`/HIT eliminators compute), so they **resist erasure** — fighting
  QTT. **OTT equality proofs are proof-irrelevant → erase cleanly at
  multiplicity 0.** Committing to QTT is thus itself an argument for OTT.
- **Does Once NEED univalence?** For compiler-correctness + program-property
  proofs (the summit), you need funext + good propositional equality + quotients
  + indexed inductives. **Univalence is a flex, not load-bearing; HITs/quotients
  ARE useful** and OTT extends with quotient types cleanly. Match the choice to
  the summit's actual needs.
- **If univalence turns out load-bearing:** the frontier target is **Higher
  Observational Type Theory (HOTT)** (Shulman, Altenkirch, et al.) — univalence in
  an *observational*, computational, decidability-friendly style — NOT classical
  cubical. Caveat: recent, not battle-tested at scale. This is the "dominate the
  univalence row *cleanly*" bet, to evaluate when equality is on the table.
