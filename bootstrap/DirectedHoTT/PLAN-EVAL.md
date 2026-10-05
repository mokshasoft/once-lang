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
| E0 | **Spike, `Algorithm/NbE` (untrusted).** Values, `eval`, `quote`, `whnf`; the term rules SigCore uses (λ, Σ/psplit, natrec, Fin/fcase, con/ielim, dpay/dih, descriptions, codes, Id/jsub, ref) | ① the parked `SigTravTest`/`SigSubKnotTest` pass with `nfOf` = NbE, each `refl` with its negative control; ② `SigCoreTest` agrees; ③ measured time/RSS vs `normLazy` | ⬜ next |
| E1 | **Full coverage + agreement oracle.** Every `head`/`headᵀ` rule; type evaluation; `Examples/NbETest`: `quote (eval t) ≡ nf t` (from `Algorithm/Eval`) on a corpus (Knot/Core entries, SigCore entries, ported OCP0009 programs: gcd facts, `div 0`, System T nested-natrec Ackermann), plus closed directed-former cases (`tr`/`ap`/`hrefl` at each code) | every corpus row green; a deliberately dropped rule turns a row red (control) | ⬜ |
| E2 | **Use it where trust is not needed.** The elaborator's weak-head evaluator (`Elab.whTm`/`whTyₖ`) becomes NbE `whnf`; test files evaluate with it; Q1 (decoder form) re-judged with E0's measurements | Elab-driven entries (SigCore, Knot/Core) unchanged and faster | ⬜ |
| E3 | **Certification.** Soundness: a relation `t ⊩ v` ("`t ⟶*` a term whose readback-head matches `v`") with `eval`-soundness by the usual environment lemma; readback gives `t ⟶* quote v`. Conversion then decides by `quote` equality (yes: the chains; no: `nf-uniqueᵀ` as today). CheckA/ConvLazy switch to it. Totality without fuel (ROADMAP Q4) from the LR's `wnorm`: well-typed ⇒ evaluation terminates. Typed NbE is forced for completeness (OCP0009 F3), and the LR already is typed | `decConvFast`/`convTm` replaced; `Knot/Core`, SigCore checking times no worse | ⬜ |
| E4 | **Sharing.** If E0–E2 measure repeated δ-unfolding: a signature-level value table (each entry evaluated once, `vref` carries its value). Also the elaborator-side reuse | measured before built ([[slower-abstraction-profile-dont-discard]]) | ⬜ conditional |
| E5 | **The CAM reading (feeds R5/R6).** Translate `RTm` to categorical combinators (Curien: `⟨_,_⟩`, `π₁`/`π₂`, `Λ`, `ev`) and prove `eval` factors through the machine; then the cost-instrumented variant per `NbEPLinCore` (allocation counts; dup-free ⇒ zero alloc) | written as PLAN-LINEAR / R6 when reached | 🔬 |

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
