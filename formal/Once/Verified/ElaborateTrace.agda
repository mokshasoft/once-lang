-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.ElaborateTrace — the elaboration trace-preservation bridge.
--
-- Plan 0.46 / D057 Part B. Discharges `compiled-main-trace` (#10): the
-- elaborated IR's denotational trace (`evalᴰ`) agrees, event-prefix-wise,
-- with the INDEPENDENT untyped operational reference (`SS.eval`). This is
-- the load-bearing cross-check that makes the elaborator load-bearing.
--
-- Method (no `checkElab` refactor): reason via the intrinsically-typed
-- `SExpr` that `checkElab` produces (clean, structural) + the clean
-- `Surface.elaborate`. The connection between the untyped operational
-- world and the typed denotational world is the standard mutual
-- LOGICAL RELATION below:
--   * `_~⟨ A ⟩_`  — an untyped `Value` SIMULATES a denotational `⟦A⟧ᴰ`.
--   * `CompSim`   — an operational computation (fuel-indexed `Result`)
--     simulates a denotational computation (`T ⟦B⟧ᴰ`), cross-meter
--     (D059 form 1: `∀ j → ∃ s`, the observable is the event prefix).
--
-- This file defines the relation; the bridge induction (Phase A
-- non-recursive → B Cata → C Ana) is built on top.
------------------------------------------------------------------------

module Once.Verified.ElaborateTrace where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; take)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Integer using () renaming (∣_∣ to absℤ)
open import Data.String using (String)

open import Once.Type
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type;
         Int; Float; Str; Buffer)
open import Once.CCC.IR using (terminal)
open import Once.Surface.Elaborate using (intLit; strLit)
open import Once.TypeCheck.Raw using (RUnit; RInt; RStringLit)
open import Once.Verified.SourceSemantics
  using (Value; Vpair; Vinl; Vinr; Vint; Vstr;
         apply; eval; Env; Result; Defs; runTraceEval)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ; evalᴰ)
open import Once.Verified.TraceMonad using (T; projTrace; valueT)
open import Once.Surface.Syntax using (Ctx; ∅; _,_^_)
open import Once.Surface.Elaborate using (⟦_⟧ᶜ)

module _ (defs : Defs) where
  mutual
    ------------------------------------------------------------------
    -- VALUE relation: an untyped `Value` simulates a denotational
    -- value `⟦A⟧ᴰ`. Recursion is on the TYPE `A` (structural).
    -- Base = equality (`Int` via `absℤ`, since `⟦Int⟧ᴰ = ℕ`); products
    -- and sums are structural; the ARROW is the logical-relation clause
    -- (related inputs ↦ simulating computations). `μ`/`ν` are the
    -- Phase B/C cases (Cata/Ana) — currently `⊤`, tightened there.
    ------------------------------------------------------------------
    infix 4 _~⟨_⟩_
    _~⟨_⟩_ : Value → (A : Type) → ⟦ A ⟧ᴰ → Set
    _         ~⟨ Unit ⟩        _        = ⊤
    _         ~⟨ Void ⟩        _        = ⊤
    Vpair a b ~⟨ A * B ⟩       d        = (a ~⟨ A ⟩ proj₁ d) × (b ~⟨ B ⟩ proj₂ d)
    _         ~⟨ A * B ⟩       _        = ⊥
    Vinl a    ~⟨ A + B ⟩       (inj₁ x) = a ~⟨ A ⟩ x
    Vinr b    ~⟨ A + B ⟩       (inj₂ y) = b ~⟨ B ⟩ y
    _         ~⟨ A + B ⟩       _        = ⊥
    Vint n    ~⟨ Int ⟩         d        = absℤ n ≡ d
    _         ~⟨ Int ⟩         _        = ⊥
    -- `Str` values are NOT observable (events carry only int args via `argℕ`,
    -- which ignores `Vstr`), and literal/arith values get no value spec
    -- (`feedback_arith_no_value_spec`: `str-lit-semM` is abstract). So the
    -- relation does not track string values.
    _         ~⟨ Str ⟩         _        = ⊤
    fv        ~⟨ A ⇒[ k ] B ⟩  f        =
      ∀ (w : Value) (a : ⟦ A ⟧ᴰ) → w ~⟨ A ⟩ a → CompSim B (f a) (λ s → apply s defs fv w)
    _         ~⟨ μ-type F ⟩    _        = ⊤
    _         ~⟨ ν-type F ⟩    _        = ⊤
    _         ~⟨ Float ⟩       _        = ⊤
    _         ~⟨ Buffer ⟩      _        = ⊤

    ------------------------------------------------------------------
    -- COMPUTATION relation: the operational `op` (a fuel-indexed
    -- `Result` of running) simulates the denotational computation
    -- `c : T ⟦B⟧ᴰ`, CROSS-METER (D059 form 1): at every observation
    -- depth `j`, SOME operational fuel `s` makes the first-`j` event
    -- prefixes agree AND the produced value simulate. The `∃ s` is the
    -- productivity witness for the step meter; the observable is the
    -- event prefix.
    ------------------------------------------------------------------
    -- FUEL-STABLE form: at every observation depth `j`, SOME threshold fuel `s`
    -- exists such that for ALL `s' ≥ s` the event prefixes agree and the value
    -- simulates. Baking the `∀ s' ≥ s` into `CompSim` makes it COMPOSITIONAL:
    -- structural cases combine sub-witnesses by `max`, with no separate
    -- fuel-monotonicity lemma (each `CompSim` carries its own stability).
    CompSim : (B : Type) → T ⟦ B ⟧ᴰ → (ℕ → Result) → Set
    CompSim B c op =
      ∀ (j : ℕ) → ∃[ s ] (∀ (s' : ℕ) → s ≤ s' →
          (take j (projTrace c j) ≡ take j (runTraceEval (op s')))
          × ResultRel B (op s') (valueT c j))

    -- The operational result (which must succeed, `just`) carries a
    -- value simulating the denotational value.
    ResultRel : (B : Type) → Result → ⟦ B ⟧ᴰ → Set
    ResultRel B (just (v , _)) d = v ~⟨ B ⟩ d
    ResultRel B nothing        _ = ⊥

  ------------------------------------------------------------------
  -- ENVIRONMENT relation: an untyped `SS.eval` environment `ρ`
  -- (most-recent binding first) simulates a denotational environment
  -- `⟦ ⟦Γ⟧ᶜ ⟧ᴰ` at the typed context `Γ`, pointwise via the value-sim.
  -- The context interpretation is the nested product
  -- `⟦ ∅ ⟧ᶜ = Unit`, `⟦ Γ , A ⟧ᶜ = ⟦Γ⟧ᶜ * A`, so `⟦ ⟦Γ,A⟧ᶜ ⟧ᴰ`
  -- reduces to `⟦ ⟦Γ⟧ᶜ ⟧ᴰ × ⟦A⟧ᴰ` definitionally (proj₁ = the rest,
  -- proj₂ = the most-recent binding `A`). This is the de-Bruijn(`Γ`)
  -- ↔ named(`ρ`) bridge for the `var`/`lam` cases.
  ------------------------------------------------------------------
  EnvRel : List (String × Value) → ∀ {n} (Γ : Ctx n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → Set
  EnvRel _              ∅           _  = ⊤
  EnvRel []             (Γ , A ^ q) _  = ⊥
  EnvRel ((_ , v) ∷ ρ') (Γ , A ^ q) dγ =
    EnvRel ρ' Γ (proj₁ dγ) × (v ~⟨ A ⟩ proj₂ dγ)

  ------------------------------------------------------------------
  -- Phase A — first leaf, end-to-end (validates the foundation).
  -- The `unit` SExpr: `elaborate unit = terminal`, `evalᴰ terminal =
  -- returnT tt` (no events), and `SS.eval RUnit = just (Vunit , [])`.
  -- So at every depth `j`, one step of `SS.eval` (`s = 1`) matches:
  -- both traces are `[]` (`refl`) and `Vunit ~⟨ Unit ⟩ tt` holds (`tt`).
  ------------------------------------------------------------------
  cs-unit : ∀ {A} (dγ : ⟦ A ⟧ᴰ) (ρ : Env)
          → CompSim Unit (evalᴰ (terminal {A}) dγ) (λ s → eval s defs ρ RUnit)
  cs-unit dγ ρ j = suc zero , λ { (suc s') _ → refl , tt }

  -- `int n`: `elaborate (int n) = intLit n = const fits-int n ∣n∣ ∘ terminal`
  -- (pure ⇒ no events), `SS.eval (RInt n) = just (Vint n , [])`. Traces both
  -- `[]`; value `Vint n ~⟨ Int ⟩ ∣n∣ = (absℤ n ≡ ∣n∣)` = refl.
  cs-int : ∀ {Γ} (n : _) (dγ : ⟦ Γ ⟧ᴰ) (ρ : Env)
         → CompSim Int (evalᴰ (intLit n {Γ}) dγ) (λ s → eval s defs ρ (RInt n))
  cs-int n dγ ρ j = suc zero , λ { (suc s') _ → refl , refl }

  -- `str s`: `elaborate (str s) = strLit s = SigOp (str-lit-info s) ∘ terminal`
  -- (str-lit-info is Pure ⇒ no events), `SS.eval (RStringLit s) = just (Vstr s , [])`.
  cs-str : ∀ {Γ} (s : _) (dγ : ⟦ Γ ⟧ᴰ) (ρ : Env)
         → CompSim Str (evalᴰ (strLit s {Γ}) dγ) (λ z → eval z defs ρ (RStringLit s))
  cs-str s dγ ρ j = suc zero , λ { (suc s') _ → refl , tt }
