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

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; ≤-trans)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Data.List.Properties using (∷-injective; ++-identityʳ)
open import Data.Integer using () renaming (∣_∣ to absℤ)
open import Data.String using (String)

open import Once.Type
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type;
         Int; Float; Str; Buffer)
open import Once.CCC.IR using (IR; id; _∘_; terminal; ⟨_,_⟩; AllocMode)
open import Once.Surface.Elaborate using (intLit; strLit)
open import Once.TypeCheck.Raw using (RawExpr; RUnit; RInt; RStringLit; RPair; RLet)
open import Once.Verified.SourceSemantics
  using (Value; Vunit; Vpair; Vinl; Vinr; Vint; Vstr;
         apply; eval; Env; Result; Defs; runTraceEval)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ; evalᴰ)
open import Once.Verified.TraceMonad using (T; projTrace; valueT)
open import Once.Surface.Syntax using (Ctx; ∅; _,_^_)
open import Once.Surface.Elaborate using (⟦_⟧ᶜ)

-- A list is determined by all its `take`-prefixes. The key lemma for
-- composing `CompSim` under `++`: `CompSim` holds at EVERY depth `j`, so
-- prefix-agreement at all `j` yields FULL trace equality, which then
-- concatenates. (Generic; independent of `defs`.)
take-determines : ∀ {ℓ} {A : Set ℓ} (xs ys : List A)
                → (∀ j → take j xs ≡ take j ys) → xs ≡ ys
take-determines []       []       h = refl
take-determines []       (y ∷ ys) h with h 1
... | ()
take-determines (x ∷ xs) []       h with h 1
... | ()
take-determines (x ∷ xs) (y ∷ ys) h =
  cong₂ _∷_ (proj₁ (∷-injective (h 1)))
            (take-determines xs ys (λ j → proj₂ (∷-injective (h (suc j)))))

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
    -- FULL-TRACE (finite) form: SOME threshold fuel `s` exists such that for ALL
    -- `s' ≥ s` the operational trace EQUALS the denotational trace and the value
    -- simulates. The denotational side is read at budget `0`: for a FINITE
    -- computation (no `Ana`) the trace is budget-independent, so `c 0` is the
    -- full trace. This composes DIRECTLY under `++` (no `take`, no monotonicity,
    -- no per-`j` reconciliation): `>>=T` at index `0` concatenates definitionally,
    -- and full sub-trace equalities concatenate. (This is the finite form, valid
    -- for all of Phase A/B; the productive `Ana` (Phase C) — whose trace is NOT
    -- budget-independent, `c 0 = []` ≠ its events — gets a separate sim. The
    -- top-level `take k` observable follows from full equality + budget-independence.)
    -- TERMINATING form: beyond a threshold `s`, the operational run STABILISES
    -- to a fixed result `just (v , evs)`; the trace `evs` equals the
    -- denotational trace (`proj₁ (c 0)`) and the value `v` simulates. Exposing
    -- the fixed `(v , evs)` is what the value-DEPENDENT structural cases
    -- (`let`/`app`/`case`) need — they reuse `v` in the continuation. (Finite
    -- form; `Ana` (Phase C) gets a separate productive sim.)
    CompSim : (B : Type) → T ⟦ B ⟧ᴰ → (ℕ → Result) → Set
    CompSim B c op =
      ∃[ s ] Σ[ v ∈ Value ] Σ[ evs ∈ List SigOpEvent ]
        ((∀ (s' : ℕ) → s ≤ s' → op s' ≡ just (v , evs))
         × (proj₁ (c 0) ≡ evs)
         × (v ~⟨ B ⟩ valueT c 0))

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
  cs-unit dγ ρ = suc zero , Vunit , [] , (λ { (suc s') _ → refl }) , refl , tt

  -- `int n`: `elaborate (int n) = intLit n = const fits-int n ∣n∣ ∘ terminal`
  -- (pure ⇒ no events), `SS.eval (RInt n) = just (Vint n , [])`. Traces both
  -- `[]`; value `Vint n ~⟨ Int ⟩ ∣n∣ = (absℤ n ≡ ∣n∣)` = refl.
  cs-int : ∀ {Γ} (n : _) (dγ : ⟦ Γ ⟧ᴰ) (ρ : Env)
         → CompSim Int (evalᴰ (intLit n {Γ}) dγ) (λ s → eval s defs ρ (RInt n))
  cs-int n dγ ρ = suc zero , Vint n , [] , (λ { (suc s') _ → refl }) , refl , refl

  -- `str s`: `elaborate (str s) = strLit s = SigOp (str-lit-info s) ∘ terminal`
  -- (str-lit-info is Pure ⇒ no events), `SS.eval (RStringLit s) = just (Vstr s , [])`.
  cs-str : ∀ {Γ} (s : _) (dγ : ⟦ Γ ⟧ᴰ) (ρ : Env)
         → CompSim Str (evalᴰ (strLit s {Γ}) dγ) (λ z → eval z defs ρ (RStringLit s))
  cs-str s dγ ρ = suc zero , Vstr s , [] , (λ { (suc s') _ → refl }) , refl , tt

  -- STRUCTURAL composition: `pair`. `elaborate (pair a b) = ⟨ a' , b' ⟩`,
  -- `SS.eval (RPair ea eb) = eval ea >>=ᵣ λ va → eval eb >>=ᵣ λ vb → just (Vpair…)`.
  -- Given CompSim for both sub-computations, the pair's CompSim holds: threshold
  -- `suc (sa ⊔ sb)` (the `suc` for `RPair`'s fuel-decrement); at `suc k` the
  -- sub-evals run at `k ≥ sa,sb` (via `≤-trans`/`m≤m⊔n`), each `just` (from
  -- ResultRel ≢ ⊥), the full sub-traces concatenate (`cong₂ _++_`), and the value
  -- is `(Vpair … ) ~⟨ B * C ⟩ (dfa , dgb)` from the two sub value-sims.
  cs-pair : ∀ {Γ B C} (a' : IR Γ B) (b' : IR Γ C) (m : AllocMode)
            (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (ea eb : RawExpr)
          → CompSim B (evalᴰ a' x) (λ s → eval s defs ρ ea)
          → CompSim C (evalᴰ b' x) (λ s → eval s defs ρ eb)
          → CompSim (B * C) (evalᴰ (⟨ a' , b' ⟩ m) x) (λ s → eval s defs ρ (RPair ea eb))
  cs-pair {Γ} {B} {C} a' b' m x ρ ea eb
          (sa , va , ea-evs , opa-eq , tra , rra)
          (sb , vb , eb-evs , opb-eq , trb , rrb) =
    suc (sa ⊔ sb) , Vpair va vb , ea-evs ++ (eb-evs ++ []) ,
    op-eq , cong₂ _++_ tra (cong₂ _++_ trb refl) , (rra , rrb)
    where
    op-eq : ∀ s' → suc (sa ⊔ sb) ≤ s' →
            eval s' defs ρ (RPair ea eb) ≡ just (Vpair va vb , ea-evs ++ (eb-evs ++ []))
    op-eq (suc k) (s≤s le)
      rewrite opa-eq k (≤-trans (m≤m⊔n sa sb) le)
            | opb-eq k (≤-trans (n≤m⊔n sa sb) le) = refl

  -- STRUCTURAL composition: `let`. `elaborate (let' e1 e2) = e2' ∘ ⟨ id , e1' ⟩`,
  -- `SS.eval (RLet x e1 e2) = eval e1 >>=ᵣ λ v1 → eval ((x,v1)∷ρ) e2`. The
  -- continuation `e2` runs in the environment EXTENDED with `e1`'s value, so its
  -- CompSim is supplied parameterized by the bound value `(v1, dv1)` and their
  -- relation (the bridge IH). `e1`'s exposed result `v1` is reused both to
  -- extend `ρ` operationally and to instantiate the continuation.
  cs-let : ∀ {Γ A B} (e1' : IR Γ A) (e2' : IR (Γ * A) B) (m : AllocMode)
           (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (xn : String) (re1 re2 : RawExpr)
         → CompSim A (evalᴰ e1' x) (λ s → eval s defs ρ re1)
         → (∀ (v1 : Value) (dv1 : ⟦ A ⟧ᴰ) → v1 ~⟨ A ⟩ dv1
              → CompSim B (evalᴰ e2' (x , dv1)) (λ s → eval s defs ((xn , v1) ∷ ρ) re2))
         → CompSim B (evalᴰ (e2' ∘ ⟨ id , e1' ⟩ m) x) (λ s → eval s defs ρ (RLet xn re1 re2))
  cs-let {Γ} {A} {B} e1' e2' m x ρ xn re1 re2
         (s1 , v1 , e1-evs , op1 , tr1 , rr1)
         hyp2 with hyp2 v1 (valueT (evalᴰ e1' x) 0) rr1
  ... | (s2 , v2 , e2-evs , op2 , tr2 , rr2) =
        suc (s1 ⊔ s2) , v2 , e1-evs ++ e2-evs ,
        op-eq ,
        trans (cong₂ (λ p q → (p ++ []) ++ q) tr1 tr2)
              (cong (_++ e2-evs) (++-identityʳ e1-evs)) ,
        rr2
    where
    op-eq : ∀ s' → suc (s1 ⊔ s2) ≤ s' →
            eval s' defs ρ (RLet xn re1 re2) ≡ just (v2 , e1-evs ++ e2-evs)
    op-eq (suc k) (s≤s le)
      rewrite op1 k (≤-trans (m≤m⊔n s1 s2) le)
            | op2 k (≤-trans (n≤m⊔n s1 s2) le) = refl
