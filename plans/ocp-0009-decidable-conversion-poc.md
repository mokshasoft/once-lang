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
All 34 `poc/OCP0009/*.agda` modules build green
(`bootstrap/check.sh poc/OCP0009/<M>.agda` → EXIT 0), including `NbEPCwF` (CwF /
dependent layer, Rung 2), `NbEPEl` (Tarski decoder + base CwF), `NbEPId`
(identity type `Id` + `J`, Rung 3), `NbEPQTT` (QTT: multiplicity semiring +
erasure), `NbEPQTTJ` (QTT graded typing judgment + elaboration, route (b)), and
the OTT equality foundation (§6 step 2) across `NbEPOTT` (value + type equality,
funext, proof-irrelevance), `NbEPOTTMu` (μ via Fix), and `NbEPOTTQ` (quotients).

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
- **OTT equality foundation (§6 step 2) — COMPLETE across 3 modules:**
  - `NbEPOTT` — observational VALUE equality `eq A` by recursion on the type
    (`{Void,Unit,×,+,⇒}`). **funext by definition** (`eq (A⇒B) f g = ∀x. eq B
    (f x)(g x)`, transport = identity) ⇒ extensional function equality provable
    funext-free (`notnot=id`); `eq` an equivalence. Observational TYPE equality
    `Eq` (inductive) + coercion `coe` (function case coerces backwards via
    `Eq-sym`) + coherence. **Proof-IRRELEVANCE** `eq-irrel` (`⇒` case discharged
    by the internal funext, taken as an explicit `Funext` param — postulate-free).
  - `NbEPOTTMu` — `eq` extended to inductive types (`μ`) on the `Fix` value model
    (`Testing.Evaluator`): `eq (μ F)(fix x)(fix y) = eqF F F x y`, reflexive,
    structural termination (no pragma). `eq Nat 2 2` by refl; distinct
    constructors compute to `⊥`.
  - `NbEPOTTQ` — QUOTIENT types the setoid/observational way: `A / R` with
    `eqQ R [a][b] = a≈b`, `elim` + `elim-resp` (the well-definedness obligation).
    Covers Once's univalence-adjacent needs without HITs.
  Chosen over cubical: fits the deterministic NbE, and proof-irrelevant equality
  erases cleanly at QTT `𝟘`.
- `NbEPUniv` — **the inductive-recursive universe (§6 step 3, the IR/II row)**.
  `U` and `El` defined MUTUALLY (Dybjer–Setzer IR): the `Π`/`Σ` codes store a
  genuine codomain family `El a → U`, so `El (`Π a b) = (x : El a) → El (b x)` —
  a genuinely DEPENDENT function type, the power the first-order `NbEPEl`
  structurally could not express. Headline: `vecC : ℕ → U` (Vec as a code-valued
  function / large elimination); `` `allVec = `Π `nat vecC `` decodes to
  `(n : ℕ) → El (vecC n)` inhabited by `zeros`; `isEmpty` is large elimination.
  **This is the step that leaves the small-core discipline by design** — IR
  enlarges the TCB/metatheory; conversion is Agda's kernel here, not the
  container NbE. Predicative (no `` `U : U ``); hierarchy noted, not built.
- `NbEPCoind` — **coinduction (the contested §5 row)**. Streams as a coinductive
  record; corecursion GUARDED by copatterns — productive, SOUND, **no sized
  types** (the feature behind Agda's unsoundness history): `repeat`/`unfold`/
  `map`/`nats`. Bisimilarity `_≈_` as the PROPOSITIONAL (coinductive) equality —
  an equivalence, with coinductive proofs (`map-id`, `map-fuse`). Matches Once's
  inductive-only discipline: `ν` stays OUT of definitional conversion; bisimulation
  is propositional (and not decidable in general — the honest frontier). Best
  principled tradeoff, not a strict win.
- `NbEPIndexed` — **native indexed inductive families (Rung 4)**. Generalizes the
  container core to INDEXED containers (Altenkirch–Morris): `IxCon` (Op/Ar/ix),
  extension `⟦_⟧ix`, indexed fixpoint `μix`, generic indexed induction `elim` (=
  `Cata` over an indexed family). Strictly positive, no pragma. `Vec` as a
  GENUINE indexed family (`nil`/`cons`, `vec2 : Vec ℕ 2` — index tracked by
  construction, vs `NbEPEl`'s fold trick). **Relations-as-datatypes** (the
  compiler-correctness-as-a-type prerequisite): `_≤_` as an indexed inductive,
  `1≤3` inhabited by evidence, `≤-refl`/`≤-trans` by induction.
- `NbEPUnivH` — **universe HIERARCHY `U₀ ⊂ U₁` (predicative)**. A single universe
  can't hold a code for itself (`Type:Type` = Girard), so `U₀`'s code lives one
  level up: `` `U₀ : U₁ `` with `El₁ `U₀ = U₀`, plus a cumulative lift `` `⇑ ``
  (`El₁ (`⇑ a) = El₀ a`). Stratified (each `El` references only the level below)
  ⇒ predicative, no `` `U:U ``. **Headline:** because `U₀` is now a first-class
  type, we can QUANTIFY over it — System-F polymorphism `(A : U₀) → El₀ A → El₀ A`
  is an honest code (`` `Π₁ `U₀ … ``), decoded and inhabited by the real
  polymorphic identity `polyId`, which computes at `` `nat₀ `` (`: ℕ → ℕ`).
  Extends to `Uₙ` by the same pattern.
- `NbEPUnivDec` — **hardening the IR universe: native decidable equality**. The
  `NbEPUniv` codes stored OPAQUE Agda functions (`El a → U`), uncomparable — so
  its conversion borrowed Agda's kernel. This DEFUNCTIONALIZES the codomain family
  into first-order DATA: `Code0` (closed) + `Code1` (one free `ℕ`-index), `El`
  decoding to genuine dependent types (`(n : ℕ) → Vec n`, inhabited by `zeros`),
  and a **native decidable equality** `_≟0_`/`_≟1_` (structural, self-contained —
  no Agda-kernel conversion). `⌊ allVec ≟0 allVec ⌋ ≡ true` runs at type-check.
  Closes the §6-step-3 caveat for this fragment. Honest boundary: decides
  STRUCTURAL code equality (codes are normal-form-like ⇒ structural =
  definitional here); general up-to-computation conversion + a hierarchy remain
  the NbE frontier.
- `NbEPElOTT` — **OTT ↔ dependent-layer wiring**. `≡→Eq` (Agda `≡` → OTT `Eq`);
  `Fib-Eq` (index conversion ⇒ OTT type-equality of the fibres); `transport-fib`
  (move a fibre element over the `Fix` denotation, justified by the index
  conversion). Demo: `Vec 2` and `Vec (double 1)` are OTT-equal and a length-2
  vector transports between them. Makes `coe`/transport load-bearing for
  dependent types. (Closed convertible indices ⇒ identity transport; nontrivial
  transport is the propositional/open-index frontier.)
- `NbEPQTTJ` — **QTT graded typing judgment (route (b), plan §7)**. Variable-based
  graded λ-calculus matching the compiler's `Surface/Context` usage vectors:
  usage vectors `Use Γ` with module structure over `Mult` (`0ᵘ`/`+ᵘ`/`·ᵘ`, laws);
  intrinsic judgment `Γ ⊢[ ρ ] A` with the usage `ρ` a JUDGMENT INDEX (well-typed
  ⇒ well-resourced by construction); `app` scales arg usage by the function
  multiplicity, `lam` moves bound-var usage into `⇒[π]`. Erasure theorem
  `erase-arg` (a `𝟘`-argument consumes no resources). Enforcement by construction:
  `idₗ` forced `⇒[𝟙]`; constant `K : ι⇒[𝟙](ι⇒[𝟘]ι)` with the ignored arg inferred
  `𝟘`. Next: elaborate `Γ ⊢[ρ] A` to the CCC IR (var→projection, lam→curry,
  app→apply), erasing `𝟘`-args.
- `NbEPQTT` — **Quantitative Type Theory foundation (plan §6, step 1)**. The
  multiplicity semiring `Mult = {𝟘,𝟙,ω}` with `+ᵐ`/`·ᵐ` and the full
  ordered-semiring laws (Atkey's resource semiring); graded contexts `Ctxq`; the
  PHASE DISTINCTION — `⟦_⟧full` keeps every entry, `⟦_⟧run` drops the `𝟘`-graded
  (index/proof) entries, `erase : Tm ⟦Γ⟧full ⟦Γ⟧run` witnesses it. **Erasure
  soundness** (`erase-irrelevant`): a `𝟘`-graded index cannot influence the
  runtime `nf` — evaluation factors through the runtime environment. Next:
  graded typing judgment (usage tracked through formers).
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
  new definitions/theorems, not new equations. **PROTOTYPED (`NbEPUniv`, §6
  step 3):** the inductive-recursive Tarski universe with genuinely dependent
  code-level Π/Σ and large elimination — the one row only Agda had. Unlike §A,
  sugar cannot supply this — it is real power, and building it **ends the
  small-core discipline by design** (IR enlarges the TCB). Open: decidable
  conversion for the IR universe *within Once's own NbE* (the POC rests on Agda's
  kernel); a universe hierarchy; II (induction-induction).

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
| **Indexed inductive families** | ✅ **native** (`NbEPIndexed`, indexed containers: Vec + relations-as-datatypes) | ✅ | ✅ | ✅ | ✅ |
| **Universe structure** | ✅ IR universe + **hierarchy `U₀⊂U₁`** (`NbEPUnivH`, predicative, polymorphism, cumulative) | ✅ ∞ + poly | ✅ ∞ + impred. Prop | ✅ ∞ + poly | ✅ cumulative |
| **Identity type** | ⚠️ *definitional* `Id`+`J` (= decidable conversion) | ✅ intensional (+cubical) | ✅ intensional | ✅ + quotients→funext | ✅ intensional |
| **Conversion** | ✅ βη **+ product-η + terminal-η, funext-free** (NbE) | βη, partial η | βη, partial η | βη + defeq proof irrel. | βη |
| **IR / II** | ✅ **IR prototyped** (`NbEPUniv` U/El mutual; `NbEPUnivDec` defunctionalized + native decidable eq) | ✅ | ❌ | ❌ | ❌ |
| **Coinduction** | ✅ **guarded/copatterns, no sized types** (`NbEPCoind`); bisim propositional | ✅ | ✅ | ✅ | ✅ |
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

1. **QTT (quantitative type theory) — SUBSTRATE DONE (`NbEPQTT`).** Multiplicity
   semiring `{𝟘,𝟙,ω}` + laws, graded contexts, erasure phase distinction +
   erasure soundness (`𝟘`-index cannot influence runtime `nf`). Aligns with
   "impose erasure from Rung 2 onward as a design invariant." **Remaining:** a
   graded *typing judgment* (usage tracked through the formers) + the general
   erasure-preserves-evaluation theorem over well-graded terms. It also *informs*
   the equality choice: QTT wants **erasable** equality (OTT-vs-cubical note).
2. **Equality foundation = OTT** (+ quotient types), *not* classical cubical.
   Chosen for (a) architectural fit with the deterministic NbE, and (b)
   QTT-erasability. Replaces the definitional-`Id` stopgap (`NbEPId`) as the
   principled target. **COMPLETE** (`NbEPOTT` value+type equality, funext,
   proof-irrelevance; `NbEPOTTMu` μ via Fix; `NbEPOTTQ` quotients). All four
   layers landed: funext by definition, `Eq`+`coe`, proof-irrelevance, μ, and
   quotients. **Wired to the dependent layer (`NbEPElOTT`):** `Eq (Vec m)(Vec n)`
   follows from index conversion, with transport of fibre elements over the `Fix`
   denotation (`Vec 2 ≅ Vec (double 1)`, transport demo). `coe`/transport is now
   load-bearing for dependent types.
3. **Universe-as-IR** — the single mechanism for the universe + IR/II rows.
   **DONE (`NbEPUniv`):** inductive-recursive `U`/`El`, genuinely dependent
   code-level Π/Σ, large elimination. Wins the IR/II row (only Agda had it). This
   is where the small-core discipline ends by design. **Hardened (`NbEPUnivDec`):**
   defunctionalized first-order codes + a NATIVE decidable equality (no longer
   Agda's kernel) for the fragment, preserving genuine dependency. **Hierarchy
   DONE (`NbEPUnivH`):** predicative `U₀ ⊂ U₁` with polymorphism over `U₀` and
   cumulativity. Remaining refinement: full up-to-computation CONVERSION (codes
   with type-level redexes / arbitrary large elimination) via a native NbE, and a
   defunctionalized/decidable hierarchy — the frontier.
4. **Native indexed inductives — DONE (`NbEPIndexed`):** indexed containers,
   `Vec`, relations-as-datatypes (`_≤_`). **Coinduction — DONE (`NbEPCoind`):**
   guarded copatterns, bisimilarity propositional (the contested row, best
   principled tradeoff). Then the summit (prove Once in Once) — the one §5-adjacent
   row still open, and the concrete goal the whole OCP motivates.

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

---

## 7. Relationship to the OCP-0006 compiler branch (`origin/ocp-0006-once-spec`)

Analyzed 2026-07-12. That branch is the **real Once compiler**: written in Agda,
machine-verified under `--safe`, **extracted to Haskell via MAlonzo**
(`make -C formal certified` → `make malonzo` copies `_build/malonzo/MAlonzo/Code/
Once/*` into `compiler/src/`; `nix build` compiles it). Hand-written Haskell is a
thin CLI/OS driver + `compiler/src/Once/Compile/Bridge.hs` (a façade over
MAlonzo's numeric-suffixed names — the only file to re-sync on re-extraction).
Architecture: 4 tiers (Kernel / Denotation-spec / Operational-impl / Adequacy),
a 7-stage pipeline, apex `Once.Certified.CertifiedBuild` = `CorrectCompiler` ∧
`VerifiedTypeChecker`; the language definition is `Once/Spec.agda` (OCP-0006).
The compile function is **parameterized over its environment** (machine model,
SigOp set, allocator) so the trust surface is explicit in the top signature.

**OCP-0009 is NOT on that branch** — `bootstrap/poc/OCP0009/` is only on
`ocp-0009-poc0-nbe`; the relationship is (for now) conceptual. But it is
concrete and strategic — OCP-0009 attacks **two real postulate clusters** of the
verified compiler:

1. **Normalization / conversion is POSTULATED** on the real compiler
   (`formal/Once/Optimizer/Normal.agda` — 6 of the branch's 59 postulates;
   `CCC/Codegen/IRTraceCorrect.agda` +3). OCP-0009's **decidable-conversion NbE
   is exactly the machinery to discharge these** — this is what our §3.B "wire to
   the real IR / OCP-0004 transparency" step concretely means: replace postulated
   normal-form/conversion reasoning with the proven decision procedure.
2. **QTT enforcement is "Not started"** on the compiler
   (`docs/formal/core/what-is-proven.md`), even though the *infrastructure*
   exists: `Quantity = Zero|One|Many` semiring (`formal/Once/Type.agda`) + **usage
   vectors** on contexts (`formal/Once/Surface/Context.agda`, `_+ᵘ_`/`_*ᵘ_`),
   tracked during **Surface elaboration**. Our `NbEPQTT` `Mult = {𝟘,𝟙,ω}` is the
   *same* semiring; the graded-judgment increment is a candidate to feed the
   compiler's unstarted enforcement.

Same substrate throughout: the compiler IR and our bootstrap NbE are both the
categorical **12-generator CCC core** (`formal/Once/IR.agda`), so OCP-0009's CwF /
dependent layer genuinely extends the *same* object language.

### This settles the QTT graded-judgment fork: choose (b), variable-based

The compiler ALREADY does QTT the variable-based way — **usage vectors on the
Surface context, tracked during `Surface → IR` elaboration** (the point-free IR
itself is *ungraded*; grading lives at the surface). So:

- **(b) variable-based graded judgment** — a small graded λ-calculus with usage
  vectors that elaborates to the IR — **matches the real compiler exactly**, is
  standard QTT (Atkey/McBride), lower-risk, and — since compiler QTT enforcement
  is unstarted — is a candidate to *become* that enforcement. It layers cleanly
  on the IR-level `erase-irrelevant` soundness already proven. **← chosen; BUILT
  as `NbEPQTTJ`** (usage-vector module, intrinsic graded judgment, `erase-arg`,
  **elaboration to the CCC IR** var→projection/lam→curry/app→apply, and the
  type-level erasure `⌊A⇒[𝟘]B⌋=⌊B⌋`). Remaining: the erasing TERM elaboration
  (drop `𝟘`-bound vars via a `𝟘`-usage strengthening lemma), whose semantic check
  needs the Kripke `⇒` NbE.
- **(a) graded point-free category** is more elegant/native but semantically
  subtle: the IR is **cartesian** (free duplication Δ and discard `terminal`), and
  grading a cartesian category is the coeffect/graded-comonad research path; the
  *clean* version of (a) would push the core toward **linear/monoidal** (replacing
  the cartesian pair/fst/snd generators) — a foundational core-redesign, not the
  next increment. Park it with the OTT / universe-as-IR foundational work: if
  Once wants best-in-class *linearity* (README: "linear code needs no GC"), a
  graded/linear IR is the honest long-term expression — evaluate then, not now.
