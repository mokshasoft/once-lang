# PLAN-EVAL — the environment-based evaluator (ROADMAP R3)

> Opened 2026-10-05. Decision: D080 (`docs/compiler/decision-log.md`).
> Supersedes PLAN-NF, whose Phase 1 shipped as PLAN-BIDI S7a
> (`Algorithm/Eval`).
> Resolves PLAN-BIDI §3g "⛔ OPEN — evaluating core programs inside Agda".

## 0. Why

- **The wall.** S7 ("the Knot in the core", PLAN-BIDI §3g) is "checker by
  evaluation": Knot families become core programs, and their tests and
  conversions are COMPUTED.
  - The certified evaluator `Algorithm/Eval` (S7a) is substitution-based:
    innermost reduction, eager δ, one `_⟶_` step at a time with its chain.
  - Run inside Agda's type checker, every β leaves a `subTm` tower as an
    unshared closure.
  - `Examples/SigCore`'s generic traversal OOMs even at fuel 40 (tests
    parked in `Negative/SigTravTest`, `Negative/SigSubKnotTest`).
  - The erased bodies are small (190 / ~900 nodes) and one elaboration takes
    ~5 s, so the cost is the evaluation strategy.
- **The principled fix is also Once's.** An environment-based evaluator
  never substitutes.
  - A closure is a body plus an environment, and a variable is a lookup.
  - It is the categorical abstract machine (environment = product, closure =
    exponential transpose, variable = projection), so it is the λ-side
    reading of the CCC-VM (ROADMAP §1, R6).
  - OCP-0009 already commits Once to NbE: conversion by evaluation to
    canonical values, because CCC βη rewriting is non-confluent.

## 1. Design

**The input is erased kernel terms (`RTm Γ`).**
- `RTm` contains no `RTy`, since motives and annotations live in the
  annotated layer. So term evaluation is self-contained, and untyped NbE
  applies.
- Types (`RTy`, for `≅ᵀ`) evaluate by a second, thin function over the term
  evaluator (E1).

**Values: untyped, de Bruijn LEVELS for free variables.**
- Levels make a value valid under any context extension, so there is NO
  renaming action on values. That is the "no Kripke" lesson
  ([[no-kripke-but-anti-renaming]]) for free, as in `poc/OCP0009` P2
  (well-scoped raw syntax, untyped values).
- The value types:

      data Val : Set
      record Clo : Set where            -- a body under ONE binder, with its environment
        field {Γ} : Cx ; env : Env Γ ; body : RTm (Γ ∙)
      record Clo₂ : Set where           -- natrec's step, psplit's body: TWO binders
        field {Γ} : Cx ; env : Env Γ ; body : RTm ((Γ ∙) ∙)
      Env : Cx → Set                    -- one value per variable (an All over Γ)

      data Val where
        vlam  : Clo → Val
        vpair : Val → Val → Val
        vunit vzero vfzero vdι : Val
        vsuc vfsuc vcon : Val → Val
        vcode : …                       -- ⌜Π⌝ ⌜Σ⌝ (with Clo) ⌜Hom⌝ ⌜Id⌝ ⌜Nat⌝ ⌜Unit⌝ ⌜IMu⌝ ⌜Fin⌝ ⌜base⌝
        vhrefl vidrefl vdσ vdρ : …      -- canonical forms of the remaining formers
        vref  : ℕ → RTm ε → Val         -- ★ lazy δ: a NAME, unfolded only when eliminated
        vne   : Ne → Val
      data Ne where
        nvar : ℕ → Ne                   -- a LEVEL
        napp nfst nsnd nnatrec nfcase nfcase0 npsplit nielim ndpay ndih
        ntr nap njsub nordtr nabsurd : …   -- one per eliminator, its scrutinee a neutral

- **Evaluation** is `eval : Fuel → Env Γ → RTm Γ → Val`, with `app`/`apply`
  on values. One fuel unit per β-like contraction, because untyped NbE needs
  it (Ω), and that makes E0–E2 terminate.
- **The rules are exactly `Algorithm/Eval.head`/`headᵀ`**:
  - every clause of `head` and `headᵀ`, including the guarded ones (`pw?`,
    `stkA?`, `stkC?`) and the `var vz`-shaped motives of `tr`;
  - ★ the guards inspect CODES. Each gets a value-level twin (`pwᵛ?` …), and
    E3 proves it agrees with the syntactic guard under readback.
- **δ is lazy.**
  - `ref d b` evaluates to `vref d b`.
  - An eliminator applied to a `vref` unfolds it (`eval ε b`) and retries.
  - Readback keeps the name, unless a full-unfolding mode is asked for.
  - So a comparison sees `ref`s as atoms first. This is the "lazy δ" PLAN-BIDI
    deferred, and `decConvFast`'s refs-as-atoms idea.
- **Readback** is `quote : ℕ → Val → RTm Γ`, at a depth (levels to indices),
  with full η-free normal forms. There is also a WEAK-HEAD mode (`whnf`), so a
  caller that needs only the head never normalises the rest
  ([[evaluator-must-not-over-reduce]]).
- **In sync with the kernel, by coverage.**
  - `eval` cases on `RTm`, so a new former is a coverage error.
  - A new RULE is caught by E1's agreement oracle against `Algorithm/Eval`
    (which is itself kept in sync by `nf-irr`).

**Agda-side cost, and why this should pass the wall (E0 measures it).**
- Environments are DATA. A variable is a list lookup, not a residual
  substitution.
- Agda's reduction of `eval ρ t` never builds `subTm σ t`.
- The remaining risk is Agda's lack of sharing across repeated `vref`
  unfoldings: each elimination of the same global re-evaluates its body.
  E0 measures it. If it bites, E4 (global value table) applies.

## 2. Stages

| # | stage | gate | state |
|---|---|---|---|
| E0 | **Spike, `Algorithm/NbE` (untrusted).** Values, `eval`, `quote`, `whnf`; the term rules SigCore uses (λ, Σ/psplit, natrec, Fin/fcase, con/ielim, dpay/dih, descriptions, codes, Id/jsub, ref) | ① the parked `SigTravTest`/`SigSubKnotTest` pass with `nfOf` = NbE, each `refl` with its negative control; ② `SigCoreTest` agrees; ③ measured time/RSS vs `normLazy` | ✅ **2026-10-05** (§2a) |
| E1 | **Full coverage + agreement oracle.** Every `head`/`headᵀ` rule; type evaluation; `Examples/NbETest`: `quote (eval t) ≡ nf t` (from `Algorithm/Eval`) on a corpus (Knot/Core entries, SigCore entries, ported OCP0009 programs: gcd facts, `div 0`, System T nested-natrec Ackermann), plus closed directed-former cases (`tr`/`ap`/`hrefl` at each code) | every corpus row green; a deliberately dropped rule turns a row red (control) | ✅ **2026-10-05** (§2b) |
| E2 | **Use it where trust is not needed.** The elaborator's weak-head evaluator (`Elab.whTm`/`whTyₖ`) becomes NbE `whnf`; test files evaluate with it; Q1 (decoder form) re-judged with E0's measurements | Elab-driven entries (SigCore, Knot/Core) unchanged and faster | ⬜ |
| E3 | **Certification** (design §2c). Soundness `t ≅ nbe t` by READING values as terms; then conversion decides by readback equality (yes: `≅`; no: distinct normal forms, Church–Rosser + `nf-uniqueᵀ`). CheckA/ConvLazy switch to it. Totality without fuel (ROADMAP Q4) later, from the LR's `wnorm`: typed NbE is forced for completeness (OCP0009 F3), and the LR already is typed | `decConvFast`/`convTm` replaced; `Knot/Core`, SigCore checking times no worse | 🟡 **terms proved 2026-10-06** (§2e); **types proved, conversion decided by NbE (`ConvNbE`, `ConvLazyNbE`) 2026-10-06** (§2f); CheckA integration being measured |
| E4 | **Sharing = references as PROJECTIONS.** If E0–E2 measure repeated δ-unfolding: a GLOBAL environment of entry values (each entry evaluated once; `ref d` is a projection from it). This is the categorical reading the compiler adopted (its D071: `⟦ref x⟧Γ = Γ(x)`, ROADMAP Q5) | measured before built ([[slower-abstraction-profile-dont-discard]]) | ⬜ conditional |
| E5 | **The CAM reading (feeds R5/R6).** Translate `RTm` to categorical combinators (Curien: `⟨_,_⟩`, `π₁`/`π₂`, `Λ`, `ev`) and prove `eval` factors through the machine; then the cost-instrumented variant per `NbEPLinCore` (allocation counts; dup-free ⇒ zero alloc) | written as PLAN-LINEAR / R6 when reached | 🔬 |

### 2a. E0 results (2026-10-05)

`Algorithm/NbE` (≈400 lines; checks in 1.4 s) — every `head` rule
transcribed, the rule-introduced binders defunctionalised (`cloHrefl`,
`cloDpay`, `cloTrPw`, `cloHomTo`, `cloK`), lazy δ by `force`. Tests use
`SigCoreEval.nfᴺ = nbe 100000`. Times are whole-module wall clock / max RSS
with cached imports (the floor, loading SigCore, is ~5.5 s / 0.48 GB).

| test | substitution evaluator (`normLazy`/`eval`) | NbE |
|---|---|---|
| `NbESigTravTest`: generic renaming (λ-calculus; the Knot against `renTm`), substitution on the λ-calculus incl. under a binder; 4 tests + 4 controls | ⛔ OOM at the cgroup cap even at fuel 40 (Lib-form decoder; was `Negative/SigTravTest`) | ✅ 10.3 s / 0.61 GB |
| `NbESigSubKnotTest`: substitution at the KNOT against `subTm`, also UNDER A BINDER (the kit's `WK` is a nested traversal); 2 tests + 2 controls | ⛔ OOM (under BOTH decoder forms for the binder case) | ✅ 8.2 s / 0.56 GB |
| `NbESigCoreTest` (= `SigCoreTest`): decoder faithful per constructor | 5.8 s / 0.50 GB | ✅ 5.6 s / 0.48 GB |
| `NbEKDTest`: the WHOLE `KD` (52 constructors) = the core decoder at `⌜KSig⌝` | ⛔ OOM (4.7 min) | ✅ 5.8 s / 0.48 GB |

- **The hypothesis held:** environments are data, so nothing builds `subTm`
  towers; the evaluation cost left is below the module-loading floor.
- **Negative controls are DECIDED inequalities** (`differs t u ≡ true` via
  `_≟Tm_`): a failing `refl` re-normalises both sides on Agda's failure path
  and is killed at the cap (rc 143), which is not a usable control
  ([[exit-143-is-not-evidence-about-cost]]).
- `Negative/SigTravTest`, `Negative/SigSubKnotTest` deleted (superseded).
- **Q1 (decoder form) re-judged:** the Lib form (B) runs; its one cost was
  evaluation, now gone — B stays (convertible with the Lib's `KD`, so the
  Knot migrates family by family).
- ⚠ Untrusted: the strongest evidence is the tests whose right-hand side is
  CONCRETE (`quoteTm (renTm …)`/`quoteTm (subTm …)`); tests with `nfᴺ` on
  both sides only show agreement with itself. E1's oracle against
  `Algorithm/Eval` is the real check.

### 2b. E1 results (2026-10-05)

- **Types** (`evalᵀ`/`rbᵀ`/`nbeᵀ`): every `headᵀ` rule; rule-introduced
  binders defunctionalised (`tcloEl`, `tcloHom`, `tcloDIh`, `tcloK`).
- **`Examples/NbEAgree`** — the oracle against `Algorithm/Eval`, 54 term rows
  + 19 type rows, open terms over three free variables: every rule and both
  sides of every guard (`pw?` through ⌜Hom⌝, `stkA?` at ⌜Nat⌝ vs `stkC?`, the
  `var vz` motives of `tr-pw`/`tr-taut`), stuck eliminators, congruence
  under binders, System T Ackermann (`ack 2 2 = 7`), a recursive datatype
  through `ielim`/`dih`, lazy δ. Checks: `bad` (disagreeing rows) `≡ []`
  and `inert` (rows already normal: the non-triviality control) `≡ []`.
  1.4 s.
- **Control:** replacing `fcase-s` by a wrong clause makes the oracle name
  row 40 (the datatype fold).

### 2c. E3 design — soundness by READING values as terms (2026-10-05)

★ **Prove it UP TO CONVERSION: `t ≅ nbe t`.** `_≅_` is the untyped
equivalence closure of `_⟶_` (`Spec/Typing`), which is all the checker
needs: a "yes" is `t ≅ nbe t ≡ nbe u ≅ u`; a "no" is two distinct NORMAL
forms (`Nf` decided structurally from `head ≡ nothing`) — Church–Rosser
turns `t ≅ nbe t` with `nbe t` normal into the chain `nf-uniqueᵀ` takes.
Up to `≅`, two reducts of one term are interchangeable, so the proof never
has to match the evaluator's FUEL between two computations of the same
value (e.g. `tr-pw`'s motive, inspected once in `trF` and re-instantiated in
`cloTrPw`), and every lemma is equational. The proof does not
need a logical relation: values are syntax-shaped, so READ them back as
(not necessarily normal) terms.

- **`⌊_⌋ : (Δ : Cx) → Val → RTm Δ`**, levels to indices as in `rb`, a
  syntactic closure `clo ρ t` read as `subTm (extS ⌊ρ⌋) t`, a stuck
  eliminator as itself. A DEFUNCTIONALISED closure reads as its rule's
  right-hand-side body (`cloHrefl C s` ↦ `hrefl (pwBody ⌊C⌋) (app (wk ⌊s⌋) v₀)`
  — `C` is forced, so `pwBody` sees the head), EXCEPT ★ `cloTrPw`, whose
  rule has a syntactic side condition (`tr-pw` needs the motive LITERALLY
  `⌜Hom⌝ c a (var vz)`): `vlam (cloTrPw d f e)` reads as the REDEX
  `tr ⌊d⌋ (lam ⌊f⌋) ⌊e⌋`, and readback first reduces the motive to that
  shape (it is `d` at the fresh level), then takes the `tr-pw` step.
- **Scoping invariant:** values built at depth `n` mention levels `< n`
  only; `⌊_⌋` at `Δ` with `len Δ = n`. Weakening stability
  `⌊v⌋_{Δ∙} ≡ renTm vs ⌊v⌋_Δ` by induction on values (the existing
  `renTm-subTm`/`subTm-subTm`/`exts-*` fusion lemmas).
- **Lemmas, by induction on fuel mirroring the evaluator:**
  ① `subTm ⌊ρ⌋ t ≅ ⌊eval ρ t⌋` (congruences via `ConvLazy.cong≅`; β/δ/each rule one
  step plus a fusion equation); ② each smart eliminator:
  `elim ⌊args⌋ ≅ ⌊smartElim args⌋`; ③ `force`: `⌊v⌋ ≅ ⌊force v⌋`;
  ④ the guards: `pwV v ≡ true → Σ c. ⌊v⌋ ⟶* c × pw? c ≡ true` (likewise
  `stkV`); ⑤ readback: `⌊v⌋ ≅ rb v`. Then `t ≡ subTm ⌊idEnv⌋ t ≅ ⌊⟦t⟧⌋ ≅ nbe t`.
- Types the same way over `_⟶ᵀ_`.
- Estimated 1500–2500 lines; the per-rule lemmas mirror `Eval.head`'s
  clauses. Totality without fuel (Q4) is separate and later.

### 2d. E3 progress (2026-10-05)

- ✅ `Algorithm/NbERead`: the reading `⌊_⌋` through a level map; renaming
  commutes with reading UNCONDITIONALLY (`ren⌊⌋`); the scope predicate `Sc`
  with `agree` (reading depends only on the levels below the scope) and
  `mono`.
- ✅ The evaluator's eliminators case on small EXHAUSTIVE VIEWS
  (`LamV`, `PairV`, `NatV`, `FinV`, `ConV`, `DescV`, `HreflV`, `IdreflV`,
  `HomV`, `VarV`, `CodeV`, `TyV`) instead of `Val` with catch-alls, so each
  proof has one case per view constructor (the redex-view lesson).
  ⚠ A catch-all view constructor CARRIES its value (`notLam f`) and clauses
  use the field: the implicit index inferred at a call site
  `lamV (force k f)` is a separate copy of the scrutinee expression, so
  using it re-evaluates it. Behaviour and timings unchanged (E0/E1 suites
  re-run: 10.4 / 8.3 / 6.0 / 1.5 s).
- ✅ `Algorithm/NbEScope`: every evaluator function preserves scope.
- ⬜ Next: the soundness lemmas ①–⑤ (§2c), up to `≅`. Two obligations
  found while designing them (2026-10-05):
  1. **Every fuel-exhaustion fallback must be SOUND, not merely stuck** —
     the proof is then fuel-agnostic (two computations of one value at
     different fuel are `≅`). Most are (`inst zero c v = vapp (vlam c) v` is
     the β-redex; stuck eliminators read as themselves). NOT yet:
     `pwAtF zero` (returns the code, not its body), `instᵀ zero`/`instᵀ₂ zero`
     (placeholders — add `tinst`/`tinst₂` values reading as the
     substitution), and readback at fuel 0 (`absurd unit unit` — must fall
     back to the value's READING, so `⌊_⌋` moves into `Algorithm/NbE`).
  2. **The pointwise rules have SYNTACTIC side conditions** (`hrefl-pw`:
     `pw? C`; `tr-pw`: motive literally `⌜Hom⌝ c a (var vz)` with `pw? c`), and
     `pwBody` is not a congruence for `≅` at arbitrary codes (a `ref` reads
     as `wk (ref …)`). Design: the evaluator FORCES the code's pw-spine
     before firing (`pwForce`; a fuel-free structural `pwN?` checks the
     result), stores the pw-NORMAL code in the closure, and reads the
     closure as the rule's right-hand side over it (`tr-pw` stores its
     bound level so the reading binds it); instantiation's re-inspection
     is related by Church–Rosser: two `≅` pw-normal codes have `≅` bodies
     (code heads are inert, so a common reduct keeps the pw-shape).
- Priority: the `SigCore` profile shows evaluation is NOT the checker's
  cost today (PERF §7). ★ REVISED the same day: the Pw POC (PLAN-BIDI §3g)
  needs a CERTIFIED conversion of a `KD`-sized closed description — the
  substitution evaluator OOMs there, NbE takes 6 s. E3 is on R4's
  critical path.
- **The `tr-pw` closure carries its WITNESS.** `cloTrPw` is created only
  when the motive, inspected at the fresh level `n`, is pw-shaped; the
  proof of its instantiation needs that fact, and a value cannot be
  re-asked. So the closure stores the inspection's pw-normal ambient `c*`,
  `a*` and the level `n` (read with `n ↦` the binder), and instantiation
  falls back to the sound `vapp (vlam (cloTrPw …)) u` whenever its own
  re-inspection does not reach pw-normal form. Church–Rosser gives
  `pwBody p ≅ pwBody q` for `≅` pw-normal codes (their heads are inert, so a
  common reduct keeps the shape and `pwBody` follows reduction).

### 2e. ★ E3 — the soundness theorem (2026-10-06)

`Algorithm/NbESound.nbe-sound : (k : ℕ) (t : RTm Γ) → t ≅ nbe k t` — at
EVERY fuel, `--safe`, no postulates; the module checks in 7.8 s.

- **Method** (§2c): read values as terms; one lemma per evaluator function
  by the same views; each rule's case is force/instantiate soundness, a
  congruence (`Algorithm/ConvCong`, generated from the ξ-rules), one kernel
  step, a fusion equation.  Scope (`NbEScope`) supplies the fresh-level
  argument (`S-fresh`, `S-fresh2`).
- **The pointwise rules decided the design** (three iterations, each
  forced by a failed proof obligation):
  1. stored inspection results needed an invariant tying them to the motive
     — not available from a value;
  2. recomputing the inspection at the CREATION fuel `k₀` broke
     termination (k₀ can exceed the current fuel);
  3. ★ final: `vlam (cloTrPw d f e)` READS AS THE REDEX `tr d (lam f) e`;
     instantiation and readback re-check the guard at their OWN fuel and
     take the kernel's `tr-pw` step only then (`S-trPwApp`, `S-rbL`).  No
     invariant, no stored fuel, structural reading.
  `hrefl-pw` forces the code's pw-SPINE and records it (`PwSpine`), so the
  rule's syntactic side condition holds of the reading (`pw-read`).
- **Church–Rosser does the conversion bookkeeping**: `⌜Hom⌝` injectivity
  (`Hom-inj`), `pwBody` between convertible pw-shaped codes (`pwBody≅`),
  substitution respecting `≅` (`sub1≅`, `sub-cong≅`, `≅-sub`).
- **Sound fallbacks everywhere** (fuel exhaustion): readback at fuel 0 is
  the reading; `tinst`/`tinst₂` at the type level.
- ⚠ **Known incompleteness (sound):** a transport whose PATH is itself a
  tr-pw λ-value is left stuck (its reading is a redex, not a syntactic λ,
  so the kernel's `tr-pw`/`tr-taut` do not apply directly).  No corpus row
  exercises it.
- ⬜ **Next for E3:** the type level (`nbeᵀ`, the same method over `_⟶ᵀ_`);
  then the checker's conversion by NbE (yes: `t ≅ nbe t`; no: distinct
  normal forms — `Nf` decided structurally, Church–Rosser + `nf-uniqueᵀ`),
  measured on SigCore / Knot/Core.

### 2f. ★ E3 — types, and the checker's side (2026-10-06, night)

- ✅ **`Algorithm/NbESoundTy.nbeᵀ-sound : A ≅ᵀ nbeᵀ k A`.** It holds at
  every fuel, is `--safe`, uses no postulates, and checks in 5.5 s.
  - The type level of the evaluator is a second layer over the terms, and
    its proof is a second layer over `NbESound`: read type values as types,
    one lemma per type-level function, each case a `_⟶ᵀ_` step
    (El-⌜…⌝, Hom-…, DIh-…), a congruence, or the term lemma for the terms
    inside.
  - The scope (`ScT`) and fresh-level lemmas (`agreeᵀ`, `renᵀ`) mirror
    `NbERead`.
- ✅ **Conversion DECIDED by NbE (`Algorithm/ConvNbE`).**
  - Normality is not a theorem about the evaluator (fuel, stuck rules),
    but it is DECIDABLE on the output. `Eval`'s certificate `Nf`/`Nfᵀ` is
    syntactic, so `nf?`/`nfᵀ?` check it in one pass.
  - Certified normal forms decide conversion both ways: "yes" when they
    are equal; "no" because two convertible normal forms are equal
    (Church–Rosser, `nf-convᵀ`).
- ✅ **Lazy conversion by NbE (`Algorithm/ConvLazyNbE`).** `ConvLazy`'s
  strategy (syntactic, weak-head, fields), with the weak-head step being
  the READING of the value (`S-eval`/`T-eval`).
- ✅ **CheckA uses NbE (committed configuration).**
  - `decTo`: the NbE decision first (yes/no), then the old procedures
    (lazy, evaluation, derivation-driven) only when a readback is not
    certified normal.
  - `viewΠ`/`viewΣ`: the NbE-certified normal form first; `domΠ≅` needs
    only `≅` and `Nfᵀ`. The evaluation route remains as the fallback.
  - Clean timings (interfaces deleted):

    | module | HEAD | committed |
    |---|---|---|
    | SigCore | 18.7 s | 20.2 s |
    | SigMeth | 48 s / 3.3 GB | 40.9 s / 2.0 GB |

- 🔬 **`ConvLazyNbE` before the decision: measured, not adopted.**
  - On SigCore/SigMeth: 23.3 s / 55.6 s.
  - On Pw's sort-0 rows (13 empty leaves): 90 s → 58 s. Naming
    `SI₂`/`SD₂`/the telescope as entries brought it to 54 s.
  - Kept as a proven module.
- ⛔ **Pw's rows still cost about 3.6 s per EMPTY leaf.**
  - Ruled out: the views (NbE 90 s against eval 99 s) and elaboration
    (5.9 s ≈ the module baseline). The cost is in CheckA's rules.
  - Hypothesis, unconfirmed: the rows' types contain `app KΣ s` at a
    VARIABLE sort. NbE must unfold the quoted signature to apply it, so
    every readback or reading of such a type prints the WHOLE stuck
    signature cascade. If so, the fix is glued evaluation (folded and
    unfolded value forms; compare folded first; smalltt), which is E4's
    "references as projections" in practice.
  - The profiling run (`tools/agda-profile.sh DirectedHoTT/Negative/PwCoreSort0.agda`) was
    stopped by the host's memory-pressure reaper. Rerun it on a quiet
    machine before designing E4.

**Fallback, recorded and not chosen.** If E0's gate fails because Agda's
evaluator itself is the limit, run evaluation tests COMPILED (MAlonzo, a
test executable) and keep `refl` tests only for small cases. That would
leave the checker's in-Agda conversion problem open, which is why it is a
fallback.

## 3. Rules for this plan

- **Untrusted until E3.** Nothing in `Metatheory/` or CheckA's "yes" depends
  on `Algorithm/NbE` before its soundness theorem exists. Tests and the
  elaborator may use it freely (a wrong elaborator result is re-checked).
- **Every `refl` test has a negative control** (a wrong RHS that fails).
- **Measure cold, one Agda at a time, under the cgroup wrap**
  ([[agda-runners-need-the-cgroup-wrap]], [[never-run-two-agda-checks-at-once]]).
- **The POC owns its syntax.** OCP0009's NbE modules are a reference for
  shape. Nothing is imported from them.
