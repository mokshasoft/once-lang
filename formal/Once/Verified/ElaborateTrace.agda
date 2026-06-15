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

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _⊔_; _∸_)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; ≤-trans; m∸n≤m; 1+n≰n; n≤1+n)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.List.Base using (replicate; length)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Data.List.Properties using (∷-injective; ++-identityʳ; ++-assoc; length-replicate)
open import Data.Integer using () renaming (∣_∣ to absℤ)
open import Data.Char using (Char)
open import Data.String using (String; fromList) renaming (_≟_ to _≟str_)
open import Agda.Builtin.String.Properties using (primStringFromListInjective)

open import Once.Type
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type;
         Int; Float; Str; Buffer)
open import Once.CCC.IR using (IR; id; _∘_; terminal; initial; ⟨_,_⟩; AllocMode; case; fst; snd; curry; inl; inr; arr)
  renaming (apply to applyᴵ)
open import Once.Surface.Elaborate using (intLit; strLit; distribute; proj; addIR; subIR; mulIR; negIR; elaborate)
open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RLam; RUnit; RInt; RStringLit; RPair; RLet; RApp; RDestruct;
         RBinOp; RUnaryOp; BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
         OpLt; OpLe; OpGt; OpGe; OpEq; OpNe; UnaryOp; OpNeg)
open import Once.Verified.SourceSemantics
  using (Value; Vunit; Vpair; Vinl; Vinr; Vint; Vstr; Vclos; Vbuiltin; Vsigop; Vin;
         apply; eval; Env; Result; Defs; runTraceEval; lookupEnv;
         bFst; bSnd; bInl; bInr; binResult; classifyB; BTag)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ; evalᴰ)
open import Once.Verified.TraceMonad using (T; returnT; projTrace; valueT)
open import Once.Surface.Syntax using (Ctx; ∅; _,_^_; lookup; Usage; Expr;
         var; lam; app; effApp; pair; fst'; snd'; inl'; inr'; case'; unit; absurd;
         let'; int; str; add; sub; mul; div; mod'; neg;
         arr'; sigOp; closure; poly; lift-morphism; morph-app; cata)
  renaming (lt to Elt; le to Ele; gt to Egt; ge to Ege; eq to Eeq; ne to Ene)
open import Once.CCC.IR using (fst; snd)
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

-- PROBE: does `evalᴰ` reduce definitionally through the `distribute` machinery
-- (apply/curry/swap closures)? If `refl` typechecks, `cs-case` is tractable.
distribute-inl-probe : ∀ {Γ A B} (m : AllocMode) (x : ⟦ Γ ⟧ᴰ) (da : ⟦ A ⟧ᴰ)
  → evalᴰ (distribute {Γ} {A} {B} m) (x , inj₁ da) ≡ returnT (inj₁ (x , da))
distribute-inl-probe m x da = refl

-- CANONICAL VARIABLE NAMES (D-bridge, option 1). A binder at de-Bruijn LEVEL
-- `k` (absolute position from the outermost binder) is named `cname k`. Levels
-- are stable under context extension, so a variable's canonical name never
-- changes, and DISTINCT levels give DISTINCT names (`cname` injective via
-- `primStringFromListInjective` + `length-replicate`) — so `lookupEnv` (which
-- searches most-recent-first by string equality) resolves a canonical name to
-- exactly its de-Bruijn position, NO shadowing. The α-renaming between a real
-- source `body` and its canonical erasure is a SEPARATE invariance lemma.
cname : ℕ → String
cname k = fromList (replicate k 'a')

-- A binder's LEVEL `n ∸ suc (toℕ i)` is strictly below the head level `n`
-- (it equals `m ∸ toℕ i ≤ m < suc m` for `n = suc m`), so they differ.
n∸si≢n : ∀ {n} (i : Fin n) → n ∸ suc (toℕ i) ≢ n
n∸si≢n {suc m} i eq = 1+n≰n (subst (_≤ m) eq (m∸n≤m m (toℕ i)))

cname-inj : ∀ {a b} → cname a ≡ cname b → a ≡ b
cname-inj {a} {b} eq =
  trans (sym (length-replicate a))
        (trans (cong length
                  (primStringFromListInjective (replicate a 'a') (replicate b 'a') eq))
               (length-replicate b))

cname-≢ : ∀ {a b} → a ≢ b → cname a ≢ cname b
cname-≢ a≢b eq = a≢b (cname-inj eq)

-- `lookupEnv` skips a head binding whose name differs from the query.
lookupEnv-skip : ∀ (ρ : Env) (x y : String) (v : Value)
               → x ≢ y → lookupEnv ((y , v) ∷ ρ) x ≡ lookupEnv ρ x
lookupEnv-skip ρ x y v x≢y with x ≟str y
... | yes p = ⊥-elim (x≢y p)
... | no  _ = refl

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
    Vint n    ~⟨ Int ⟩         d        = n ≡ d
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
  -- The head binding's NAME is fixed to `cname n` (the de-Bruijn LEVEL of the
  -- most-recent binder in a context of length `suc n`), so `lookupEnv` resolves
  -- canonical names positionally (`cname` injective ⇒ no shadowing).
  EnvRel : List (String × Value) → ∀ {n} (Γ : Ctx n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → Set
  EnvRel _              ∅                       _  = ⊤
  EnvRel []             (Γ , A ^ q)             _  = ⊥
  EnvRel ((y , v) ∷ ρ') (_,_^_ {n} Γ A q)       dγ =
    (y ≡ cname n) × EnvRel ρ' Γ (proj₁ dγ) × (v ~⟨ A ⟩ proj₂ dγ)

  ------------------------------------------------------------------
  -- VARIABLE case (`var i`). `elaborate (var i) = proj i` (a pure nest
  -- of `fst`/`snd`, trace `[]`); `SS.eval (RVar (cname level))` resolves
  -- by name. `proj-trace`: the projection emits no events. `envrel-lookup`:
  -- given `EnvRel`, the canonical name at the variable's LEVEL
  -- (`n ∸ suc (toℕ i)`) looks up to a value that simulates the projection.
  ------------------------------------------------------------------
  proj-trace : ∀ {n} {Γ : Ctx n} (i : Fin n) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ)
             → proj₁ (evalᴰ (proj {Γ = Γ} i) dγ 0) ≡ []
  proj-trace {Γ = Γ , A ^ q} fzero    dγ = refl
  proj-trace {Γ = Γ , A ^ q} (fsuc i) dγ = proj-trace {Γ = Γ} i (proj₁ dγ)

  envrel-lookup : ∀ {n} {Γ : Ctx n} (i : Fin n) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (ρ : Env)
                → EnvRel ρ Γ dγ
                → Σ[ v ∈ Value ]
                    (lookupEnv ρ (cname (n ∸ suc (toℕ i))) ≡ just v)
                    × (v ~⟨ lookup Γ i ⟩ valueT (evalᴰ (proj {Γ = Γ} i) dγ) 0)
  envrel-lookup {suc n} {Γ , A ^ q} fzero dγ ((y , v) ∷ ρ') (refl , env' , vsim)
    with cname n ≟str cname n
  ... | yes _ = v , refl , vsim
  ... | no ¬p = ⊥-elim (¬p refl)
  envrel-lookup {suc n} {Γ , A ^ q} (fsuc i) dγ ((y , v) ∷ ρ') (refl , env' , vsim)
    with envrel-lookup {n} {Γ} i (proj₁ dγ) ρ' env'
  ... | (v' , lk , vsim') =
        v' , trans (lookupEnv-skip ρ' (cname (n ∸ suc (toℕ i))) (cname n) v
                      (cname-≢ (n∸si≢n i))) lk , vsim'

  cs-var : ∀ {n} {Γ : Ctx n} (i : Fin n) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (ρ : Env)
         → EnvRel ρ Γ dγ
         → CompSim (lookup Γ i) (evalᴰ (proj {Γ = Γ} i) dγ)
                   (λ z → eval z defs ρ (RVar (cname (n ∸ suc (toℕ i)))))
  cs-var {n} {Γ} i dγ ρ env with envrel-lookup {n} {Γ} i dγ ρ env
  ... | (v , lk , vsim) =
        suc zero , v , [] , op-eq , proj-trace {Γ = Γ} i dγ , vsim
    where
    op-eq : ∀ z → suc zero ≤ z
          → eval z defs ρ (RVar (cname (n ∸ suc (toℕ i)))) ≡ just (v , [])
    op-eq (suc k) _ rewrite lk = refl

  ------------------------------------------------------------------
  -- LAMBDA case (`lam`). `elaborate (lam q _ e) = curry (elaborate e) m`,
  -- `evalᴰ (curry f m) dγ = returnT (λ b → evalᴰ f (dγ,b))` (a Kleisli
  -- closure, trace `[]`); `SS.eval (RLam x re) = just (Vclos ρ x re, [])`.
  -- The value-sim arrow clause `Vclos … ~⟨A⇒B⟩ (λ b → …)` is EXACTLY the
  -- body's bridge IH: applying the operational closure runs `eval` in the
  -- extended env (`apply (suc k) (Vclos ρ x body) w = eval k ((x,w)∷ρ) body`),
  -- so the IH's computation-sim transfers after a one-step fuel shift.
  cs-lam : ∀ {n} {Γ : Ctx n} {A B kk} (e' : IR (⟦ Γ ⟧ᶜ * A) B) (m : AllocMode)
           (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (ρ : Env) (re-body : RawExpr)
         → (∀ (w : Value) (a : ⟦ A ⟧ᴰ) → w ~⟨ A ⟩ a
              → CompSim B (evalᴰ e' (dγ , a))
                        (λ z → eval z defs ((cname n , w) ∷ ρ) re-body))
         → CompSim (A ⇒[ kk ] B) (evalᴰ (curry {k = kk} e' m) dγ)
                   (λ z → eval z defs ρ (RLam (cname n) re-body))
  cs-lam {n} {Γ} {A} {B} {kk} e' m dγ ρ re-body hyp =
    suc zero , Vclos ρ (cname n) re-body , [] , op-eq , refl , vsim
    where
    op-eq : ∀ z → suc zero ≤ z
          → eval z defs ρ (RLam (cname n) re-body)
            ≡ just (Vclos ρ (cname n) re-body , [])
    op-eq (suc k) _ = refl
    vsim : Vclos ρ (cname n) re-body ~⟨ A ⇒[ kk ] B ⟩ (λ b → evalᴰ e' (dγ , b))
    vsim w a rel with hyp w a rel
    ... | (s , v , evs , op , tr , rr) =
          suc s , v , evs , (λ { (suc k) (s≤s le) → op k le }) , tr , rr

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
  -- (pure ⇒ no events), `SS.eval (RInt n) = just (Vint ∣n∣ , [])` (D054/B:
  -- `absℤ`-converted to the ℕ machine rep). Both traces `[]`; the IR value is
  -- `∣n∣` and the operational value `Vint ∣n∣`, so `∣n∣ ≡ ∣n∣` = refl.
  cs-int : ∀ {Γ} (n : _) (dγ : ⟦ Γ ⟧ᴰ) (ρ : Env)
         → CompSim Int (evalᴰ (intLit n {Γ}) dγ) (λ s → eval s defs ρ (RInt n))
  cs-int n dγ ρ = suc zero , Vint (absℤ n) , [] , (λ { (suc s') _ → refl }) , refl , refl

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

  -- STRUCTURAL composition: `app`. `elaborate (app f x) = apply ∘ ⟨ f' , x' ⟩`,
  -- `SS.eval (RApp rf rx) = eval rf >>=ᵣ λ vg → eval rx >>=ᵣ λ vx → apply vg vx`.
  -- The `apply` step's CompSim comes from `f`'s value-sim — `vg ~⟨ A ⇒ B ⟩ dclo`
  -- IS the logical-relation clause `∀ w a → w~a → CompSim B (dclo a)(apply·vg·w)`,
  -- instantiated at `x`'s result `(vx , dx)`. Three-way trace `f ++ (x ++ apply)`.
  cs-app : ∀ {Γ A B kk} (f' : IR Γ (A ⇒[ kk ] B)) (x' : IR Γ A) (m : AllocMode)
           (xenv : ⟦ Γ ⟧ᴰ) (ρ : Env) (rf rx : RawExpr)
         → CompSim (A ⇒[ kk ] B) (evalᴰ f' xenv) (λ s → eval s defs ρ rf)
         → CompSim A (evalᴰ x' xenv) (λ s → eval s defs ρ rx)
         → CompSim B (evalᴰ (applyᴵ ∘ ⟨ f' , x' ⟩ m) xenv) (λ s → eval s defs ρ (RApp rf rx))
  cs-app {Γ} {A} {B} {kk} f' x' m xenv ρ rf rx
         (sf , vg , f-evs , opf , trf , rrf)
         (sx , vx , x-evs , opx , trx , rrx)
         with rrf vx (valueT (evalᴰ x' xenv) 0) rrx
  ... | (sapp , vapp , app-evs , opapp , trapp , rrapp) =
        suc (sf ⊔ (sx ⊔ sapp)) , vapp , f-evs ++ (x-evs ++ app-evs) ,
        op-eq , tr-eq , rrapp
    where
    op-eq : ∀ s' → suc (sf ⊔ (sx ⊔ sapp)) ≤ s' →
            eval s' defs ρ (RApp rf rx) ≡ just (vapp , f-evs ++ (x-evs ++ app-evs))
    op-eq (suc k) (s≤s le)
      rewrite opf   k (≤-trans (m≤m⊔n sf (sx ⊔ sapp)) le)
            | opx   k (≤-trans (≤-trans (m≤m⊔n sx sapp) (n≤m⊔n sf (sx ⊔ sapp))) le)
            | opapp k (≤-trans (≤-trans (n≤m⊔n sx sapp) (n≤m⊔n sf (sx ⊔ sapp))) le) = refl
    tr-eq : proj₁ (evalᴰ (applyᴵ ∘ ⟨ f' , x' ⟩ m) xenv 0) ≡ f-evs ++ (x-evs ++ app-evs)
    tr-eq = begin
      proj₁ (evalᴰ (applyᴵ ∘ ⟨ f' , x' ⟩ m) xenv 0)
        ≡⟨ cong₂ _++_ (cong₂ _++_ trf (cong (_++ []) trx)) trapp ⟩
      (f-evs ++ (x-evs ++ [])) ++ app-evs
        ≡⟨ cong (_++ app-evs) (cong (f-evs ++_) (++-identityʳ x-evs)) ⟩
      (f-evs ++ x-evs) ++ app-evs
        ≡⟨ ++-assoc f-evs x-evs app-evs ⟩
      f-evs ++ (x-evs ++ app-evs)
        ∎
      where open ≡-Reasoning

  -- STRUCTURAL composition: `case`. `elaborate (case' s l r) = case l' r' ∘
  -- distribute m ∘ ⟨ id , s' ⟩ m`; `SS.eval (RDestruct s xl l yr r)` evaluates
  -- `s`, then branches on `Vinl a`/`Vinr b`, running `l`/`r` in the env extended
  -- with the payload. The denotational side ROUTES through `distribute` (which
  -- reduces definitionally, per `distribute-inl-probe`): `(x, inj₁ da) ↦ inl
  -- (x, da)`, then `case l' r'` picks `l'`. The branch is forced to agree by the
  -- value-sim (`Vinl a ~⟨A+B⟩ ds` ⟹ `ds = inj₁ da`); non-`Vinl`/`Vinr` `s` is ⊥.
  cs-case : ∀ {Γ A B C} (s' : IR Γ (A + B)) (l' : IR (Γ * A) C) (r' : IR (Γ * B) C)
            (m : AllocMode) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (xl yr : String) (rs rl rr : RawExpr)
          → CompSim (A + B) (evalᴰ s' x) (λ z → eval z defs ρ rs)
          → (∀ (a : Value) (da : ⟦ A ⟧ᴰ) → a ~⟨ A ⟩ da
               → CompSim C (evalᴰ l' (x , da)) (λ z → eval z defs ((xl , a) ∷ ρ) rl))
          → (∀ (b : Value) (db : ⟦ B ⟧ᴰ) → b ~⟨ B ⟩ db
               → CompSim C (evalᴰ r' (x , db)) (λ z → eval z defs ((yr , b) ∷ ρ) rr))
          → CompSim C (evalᴰ (case l' r' ∘ distribute m ∘ ⟨ id , s' ⟩ m) x)
                      (λ z → eval z defs ρ (RDestruct rs xl rl yr rr))
  -- `op-eq` for the two branches, extracted to top-level so the dispatching
  -- `with` needs NO nested `with` (which would clash with the `...` column
  -- count of the sibling/absurd clauses). Their types name only `eval`, so
  -- they are unaffected by the `evalᴰ s' x 0` abstraction in `cs-case`.
  op-eq-destruct-l :
    ∀ (ρ : Env) (xl yr : String) (rs rl rr : RawExpr)
      (ss sl : ℕ) (a vl : Value) (s-evs l-evs : List SigOpEvent)
    → (∀ z → ss ≤ z → eval z defs ρ rs ≡ just (Vinl a , s-evs))
    → (∀ z → sl ≤ z → eval z defs ((xl , a) ∷ ρ) rl ≡ just (vl , l-evs))
    → ∀ z → suc (ss ⊔ sl) ≤ z
    → eval z defs ρ (RDestruct rs xl rl yr rr) ≡ just (vl , s-evs ++ l-evs)
  op-eq-destruct-l ρ xl yr rs rl rr ss sl a vl s-evs l-evs ops opl (suc k) (s≤s le)
    rewrite ops k (≤-trans (m≤m⊔n ss sl) le)
          | opl k (≤-trans (n≤m⊔n ss sl) le) = refl

  op-eq-destruct-r :
    ∀ (ρ : Env) (xl yr : String) (rs rl rr : RawExpr)
      (ss sr : ℕ) (b vr : Value) (s-evs r-evs : List SigOpEvent)
    → (∀ z → ss ≤ z → eval z defs ρ rs ≡ just (Vinr b , s-evs))
    → (∀ z → sr ≤ z → eval z defs ((yr , b) ∷ ρ) rr ≡ just (vr , r-evs))
    → ∀ z → suc (ss ⊔ sr) ≤ z
    → eval z defs ρ (RDestruct rs xl rl yr rr) ≡ just (vr , s-evs ++ r-evs)
  op-eq-destruct-r ρ xl yr rs rl rr ss sr b vr s-evs r-evs ops opr (suc k) (s≤s le)
    rewrite ops k (≤-trans (m≤m⊔n ss sr) le)
          | opr k (≤-trans (n≤m⊔n ss sr) le) = refl

  -- The full pair `evalᴰ s' x 0` (NOT just `valueT … 0`) is abstracted, so
  -- BOTH its trace half (`proj₁`) AND its value half (`proj₂`, which DRIVES
  -- the `distribute`/`case` branch) become concrete in the goal — the trace
  -- term then reduces. The branch hypothesis is destructured by an irrefutable
  -- `let` (no nested `with`), and `tr-eq` is inline (the goal is already in the
  -- reduced/abstracted form). `trs : se ≡ s-evs` bridges the abstracted trace
  -- `se` to the CompSim's `s-evs`.
  cs-case {Γ} {A} {B} {C} s' l' r' m x ρ xl yr rs rl rr
          (ss , vs , s-evs , ops , trs , rrs) lh rh
    with evalᴰ s' x 0 | vs | rrs
  ... | (se , inj₁ da) | Vinl a | rra =
        let (sl , vl , l-evs , opl , trl , rrl) = lh a da rra in
        suc (ss ⊔ sl) , vl , s-evs ++ l-evs ,
        op-eq-destruct-l ρ xl yr rs rl rr ss sl a vl s-evs l-evs ops opl ,
        trans (cong (((se ++ []) ++ []) ++_) trl)
              (cong (_++ l-evs) (trans (++-identityʳ (se ++ [])) (trans (++-identityʳ se) trs))) ,
        rrl
  ... | (se , inj₂ db) | Vinr b | rrb =
        let (sr , vr , r-evs , opr , trr , rrr) = rh b db rrb in
        suc (ss ⊔ sr) , vr , s-evs ++ r-evs ,
        op-eq-destruct-r ρ xl yr rs rl rr ss sr b vr s-evs r-evs ops opr ,
        trans (cong (((se ++ []) ++ []) ++_) trr)
              (cong (_++ r-evs) (trans (++-identityʳ (se ++ [])) (trans (++-identityʳ se) trs))) ,
        rrr
  ... | (_ , inj₂ _) | Vinl _      | ()
  ... | (_ , inj₁ _) | Vinr _      | ()
  ... | (_ , _)      | Vunit       | ()
  ... | (_ , _)      | Vpair _ _   | ()
  ... | (_ , _)      | Vint _      | ()
  ... | (_ , _)      | Vstr _      | ()
  ... | (_ , _)      | Vclos _ _ _ | ()
  ... | (_ , _)      | Vbuiltin _ _ | ()
  ... | (_ , _)      | Vsigop _ _  | ()
  ... | (_ , _)      | Vin _       | ()

  ------------------------------------------------------------------
  -- BUILTIN-APPLICATION cases (`fst'`/`snd'`/`inl'`/`inr'`). These typed
  -- constructors have NO raw constructor — `checkElab` produces them from
  -- `RApp (RVar "fst"/"snd"/"inl"/"inr") e`, and `SS.eval` routes through
  -- `resolveName name = Vbuiltin bName []` + `applyBuiltin`. The
  -- no-shadowing-of-builtin-names invariant (user-confirmed) is carried as
  -- the hypothesis `∀ z → eval (suc z) defs ρ (RVar name) ≡ just (Vbuiltin
  -- bName [] , [])` — the bridge discharges it from `lookupEnv`/`lookupDef`
  -- both `nothing` (canonical `"aaa…"` env names never collide with a
  -- builtin name; `defs` does not redefine builtins).
  --
  -- `op-eq-builtin1`: the operational `RApp (RVar name) re` evaluates the
  -- name to its builtin, `re` to its (single) argument, then applies — three
  -- definitional `>>=ᵣ` steps; threshold `suc (suc se)` (one `suc` for the
  -- `RApp` decrement, one so the `RVar name` lookup sees a `suc` fuel).
  op-eq-builtin1 :
    ∀ (nm : String) (bval : Value) (ρ : Env) (re : RawExpr)
      (se : ℕ) (varg vres : Value) (evs : List SigOpEvent)
    → (∀ z → eval (suc z) defs ρ (RVar nm) ≡ just (bval , []))
    → (∀ z → se ≤ z → eval z defs ρ re ≡ just (varg , evs))
    → (∀ f → apply (suc f) defs bval varg ≡ just (vres , []))
    → ∀ z → suc (suc se) ≤ z → eval z defs ρ (RApp (RVar nm) re) ≡ just (vres , evs)
  op-eq-builtin1 nm bval ρ re se varg vres evs nameres opre appres
                 (suc (suc k)) (s≤s (s≤s le))
    rewrite nameres k
          | opre (suc k) (≤-trans le (n≤1+n k))
          | appres k
          | ++-identityʳ evs = refl

  -- `fst'`: `elaborate (fst' e) = fst ∘ elaborate e`; `evalᴰ (fst ∘ e') x`
  -- has value `proj₁ (e'-value)`, trace `e'-trace`. The value-sim at `A * B`
  -- FORCES the operational value to be `Vpair va vb` (non-`Vpair` ⇒ ⊥), and
  -- `applyBuiltin bFst (Vpair va vb ∷ []) = just (va , [])`.
  cs-fst : ∀ {Γ A B} (e' : IR Γ (A * B)) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (re : RawExpr)
         → (∀ z → eval (suc z) defs ρ (RVar "fst") ≡ just (Vbuiltin bFst [] , []))
         → CompSim (A * B) (evalᴰ e' x) (λ z → eval z defs ρ re)
         → CompSim A (evalᴰ (fst ∘ e') x) (λ z → eval z defs ρ (RApp (RVar "fst") re))
  cs-fst {Γ} {A} {B} e' x ρ re nameres (se , ve , ee-evs , ope , tre , rre)
    with ve | rre
  ... | Vpair va vb | (rra , rrb) =
        suc (suc se) , va , ee-evs ,
        op-eq-builtin1 "fst" (Vbuiltin bFst []) ρ re se (Vpair va vb) va ee-evs
          nameres ope (λ _ → refl) ,
        trans (++-identityʳ (proj₁ (evalᴰ e' x 0))) tre , rra
  ... | Vunit       | ()
  ... | Vinl _      | ()
  ... | Vinr _      | ()
  ... | Vint _      | ()
  ... | Vstr _      | ()
  ... | Vclos _ _ _ | ()
  ... | Vbuiltin _ _ | ()
  ... | Vsigop _ _  | ()
  ... | Vin _       | ()

  -- `snd'`: symmetric to `cs-fst`, second projection.
  cs-snd : ∀ {Γ A B} (e' : IR Γ (A * B)) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (re : RawExpr)
         → (∀ z → eval (suc z) defs ρ (RVar "snd") ≡ just (Vbuiltin bSnd [] , []))
         → CompSim (A * B) (evalᴰ e' x) (λ z → eval z defs ρ re)
         → CompSim B (evalᴰ (snd ∘ e') x) (λ z → eval z defs ρ (RApp (RVar "snd") re))
  cs-snd {Γ} {A} {B} e' x ρ re nameres (se , ve , ee-evs , ope , tre , rre)
    with ve | rre
  ... | Vpair va vb | (rra , rrb) =
        suc (suc se) , vb , ee-evs ,
        op-eq-builtin1 "snd" (Vbuiltin bSnd []) ρ re se (Vpair va vb) vb ee-evs
          nameres ope (λ _ → refl) ,
        trans (++-identityʳ (proj₁ (evalᴰ e' x 0))) tre , rrb
  ... | Vunit       | ()
  ... | Vinl _      | ()
  ... | Vinr _      | ()
  ... | Vint _      | ()
  ... | Vstr _      | ()
  ... | Vclos _ _ _ | ()
  ... | Vbuiltin _ _ | ()
  ... | Vsigop _ _  | ()
  ... | Vin _       | ()

  -- `inl'`: `elaborate (inl' a) = inl m ∘ elaborate a`; `evalᴰ (inl m ∘ e') x`
  -- has value `inj₁ (e'-value)`. `Vinl ve ~⟨A+B⟩ inj₁ d` reduces to `ve ~⟨A⟩ d`,
  -- which is the sub-value-sim `rre` — no value-casing needed.
  cs-inl : ∀ {Γ A B} (e' : IR Γ A) (m : AllocMode) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (re : RawExpr)
         → (∀ z → eval (suc z) defs ρ (RVar "inl") ≡ just (Vbuiltin bInl [] , []))
         → CompSim A (evalᴰ e' x) (λ z → eval z defs ρ re)
         → CompSim (A + B) (evalᴰ (inl {A} {B} m ∘ e') x) (λ z → eval z defs ρ (RApp (RVar "inl") re))
  cs-inl {Γ} {A} {B} e' m x ρ re nameres (se , ve , ee-evs , ope , tre , rre) =
        suc (suc se) , Vinl ve , ee-evs ,
        op-eq-builtin1 "inl" (Vbuiltin bInl []) ρ re se ve (Vinl ve) ee-evs
          nameres ope (λ _ → refl) ,
        trans (++-identityʳ (proj₁ (evalᴰ e' x 0))) tre , rre

  -- `inr'`: symmetric, right injection.
  cs-inr : ∀ {Γ A B} (e' : IR Γ B) (m : AllocMode) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (re : RawExpr)
         → (∀ z → eval (suc z) defs ρ (RVar "inr") ≡ just (Vbuiltin bInr [] , []))
         → CompSim B (evalᴰ e' x) (λ z → eval z defs ρ re)
         → CompSim (A + B) (evalᴰ (inr {A} {B} m ∘ e') x) (λ z → eval z defs ρ (RApp (RVar "inr") re))
  cs-inr {Γ} {A} {B} e' m x ρ re nameres (se , ve , ee-evs , ope , tre , rre) =
        suc (suc se) , Vinr ve , ee-evs ,
        op-eq-builtin1 "inr" (Vbuiltin bInr []) ρ re se ve (Vinr ve) ee-evs
          nameres ope (λ _ → refl) ,
        trans (++-identityʳ (proj₁ (evalᴰ e' x 0))) tre , rre

  -- `absurd`: `elaborate (absurd v) = initial ∘ elaborate v`, `v : … Void`.
  -- `⟦ Void ⟧ᴰ = ⊥`, so the sub-computation's denotational value
  -- `valueT (evalᴰ e' x) 0 : ⊥` — the whole case is vacuous (no source program
  -- ever produces a `Void` value). The conclusion's raw is just the sub-raw `re`
  -- (`absurd` has no raw constructor of its own).
  cs-absurd : ∀ {Γ A} (e' : IR Γ Void) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (re : RawExpr)
            → CompSim Void (evalᴰ e' x) (λ z → eval z defs ρ re)
            → CompSim A (evalᴰ (initial {A} ∘ e') x) (λ z → eval z defs ρ re)
  cs-absurd e' x ρ re _ = ⊥-elim (valueT (evalᴰ e' x) 0)

  ------------------------------------------------------------------
  -- ARITHMETIC (`add`/`sub`/`mul`/`neg`). `elaborate (add a b) = addIR ∘
  -- ⟨a',b'⟩ m`, `addIR = SigOp add-info` (Pure ⇒ NO trace events). Per D054/B
  -- the value domain is ℕ on both sides and the SigOp `add-semM = a +ℕ b` is
  -- the SAME ℕ op `SS.eval`'s `binResult OpAdd = Vint (a +ℕ b)` uses — so the
  -- value-sim composes as `cong₂ _+_`. (`div`/`mod`/comparisons await their
  -- still-postulated `semM`s being shared/defined.)
  --
  -- `int-val`: the `Int` value-sim forces the operational value to be a `Vint`.
  int-val : ∀ (v : Value) (d : ⟦ Int ⟧ᴰ) → v ~⟨ Int ⟩ d
          → Σ[ n ∈ ℕ ] (v ≡ Vint n) × (n ≡ d)
  int-val (Vint n)      d eq = n , refl , eq
  int-val Vunit         d ()
  int-val (Vpair _ _)   d ()
  int-val (Vinl _)      d ()
  int-val (Vinr _)      d ()
  int-val (Vin _)       d ()
  int-val (Vstr _)      d ()
  int-val (Vclos _ _ _) d ()
  int-val (Vbuiltin _ _) d ()
  int-val (Vsigop _ _)  d ()

  -- The operational `RBinOp` step, threshold `suc (sa ⊔ sb)` (one `suc` for
  -- the decrement). Both args evaluated, then `binResult` (which emits `[]`).
  op-eq-binop :
    ∀ (op : BinOp) (ρ : Env) (ea eb : RawExpr) (sa sb : ℕ)
      (van vbn vr : ℕ) (ea-evs eb-evs : List SigOpEvent)
    → (∀ z → sa ≤ z → eval z defs ρ ea ≡ just (Vint van , ea-evs))
    → (∀ z → sb ≤ z → eval z defs ρ eb ≡ just (Vint vbn , eb-evs))
    → binResult op (Vint van) (Vint vbn) ≡ just (Vint vr , [])
    → ∀ z → suc (sa ⊔ sb) ≤ z
    → eval z defs ρ (RBinOp op ea eb) ≡ just (Vint vr , ea-evs ++ (eb-evs ++ []))
  op-eq-binop op ρ ea eb sa sb van vbn vr ea-evs eb-evs opa opb bres (suc k) (s≤s le)
    rewrite opa k (≤-trans (m≤m⊔n sa sb) le)
          | opb k (≤-trans (n≤m⊔n sa sb) le)
          | bres = refl

  -- Common shape for the three binary arith lemmas: differs only in the IR
  -- `SigOp`, the raw `BinOp`, and the ℕ operation (passed as `⊕` with proof
  -- that `binResult op = Vint (van ⊕ vbn)` and the denotational value reduces
  -- to `va_d ⊕ vb_d`).
  cs-add : ∀ {Γ} (a' b' : IR Γ Int) (m : AllocMode) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (ea eb : RawExpr)
         → CompSim Int (evalᴰ a' x) (λ s → eval s defs ρ ea)
         → CompSim Int (evalᴰ b' x) (λ s → eval s defs ρ eb)
         → CompSim Int (evalᴰ (addIR ∘ ⟨ a' , b' ⟩ m) x)
                       (λ s → eval s defs ρ (RBinOp OpAdd ea eb))
  cs-add {Γ} a' b' m x ρ ea eb
         (sa , va , ea-evs , opa , tra , rra) (sb , vb , eb-evs , opb , trb , rrb)
    with int-val va _ rra | int-val vb _ rrb
  ... | (van , refl , rran) | (vbn , refl , rrbn) =
        suc (sa ⊔ sb) , Vint (van +ℕ vbn) , ea-evs ++ (eb-evs ++ []) ,
        op-eq-binop OpAdd ρ ea eb sa sb van vbn (van +ℕ vbn) ea-evs eb-evs opa opb refl ,
        trans (++-identityʳ _) (cong₂ (λ p q → p ++ (q ++ [])) tra trb) ,
        cong₂ _+ℕ_ rran rrbn

  cs-sub : ∀ {Γ} (a' b' : IR Γ Int) (m : AllocMode) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (ea eb : RawExpr)
         → CompSim Int (evalᴰ a' x) (λ s → eval s defs ρ ea)
         → CompSim Int (evalᴰ b' x) (λ s → eval s defs ρ eb)
         → CompSim Int (evalᴰ (subIR ∘ ⟨ a' , b' ⟩ m) x)
                       (λ s → eval s defs ρ (RBinOp OpSub ea eb))
  cs-sub {Γ} a' b' m x ρ ea eb
         (sa , va , ea-evs , opa , tra , rra) (sb , vb , eb-evs , opb , trb , rrb)
    with int-val va _ rra | int-val vb _ rrb
  ... | (van , refl , rran) | (vbn , refl , rrbn) =
        suc (sa ⊔ sb) , Vint (van ∸ vbn) , ea-evs ++ (eb-evs ++ []) ,
        op-eq-binop OpSub ρ ea eb sa sb van vbn (van ∸ vbn) ea-evs eb-evs opa opb refl ,
        trans (++-identityʳ _) (cong₂ (λ p q → p ++ (q ++ [])) tra trb) ,
        cong₂ _∸_ rran rrbn

  cs-mul : ∀ {Γ} (a' b' : IR Γ Int) (m : AllocMode) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (ea eb : RawExpr)
         → CompSim Int (evalᴰ a' x) (λ s → eval s defs ρ ea)
         → CompSim Int (evalᴰ b' x) (λ s → eval s defs ρ eb)
         → CompSim Int (evalᴰ (mulIR ∘ ⟨ a' , b' ⟩ m) x)
                       (λ s → eval s defs ρ (RBinOp OpMul ea eb))
  cs-mul {Γ} a' b' m x ρ ea eb
         (sa , va , ea-evs , opa , tra , rra) (sb , vb , eb-evs , opb , trb , rrb)
    with int-val va _ rra | int-val vb _ rrb
  ... | (van , refl , rran) | (vbn , refl , rrbn) =
        suc (sa ⊔ sb) , Vint (van *ℕ vbn) , ea-evs ++ (eb-evs ++ []) ,
        op-eq-binop OpMul ρ ea eb sa sb van vbn (van *ℕ vbn) ea-evs eb-evs opa opb refl ,
        trans (++-identityʳ _) (cong₂ (λ p q → p ++ (q ++ [])) tra trb) ,
        cong₂ _*ℕ_ rran rrbn

  -- `neg`: `elaborate (neg e) = negIR ∘ e'`, `neg-semM _ = 0` (placeholder),
  -- and `SS.eval`'s `neg (Vint _) = Vint 0` — both 0, value-sim `refl`.
  cs-neg : ∀ {Γ} (e' : IR Γ Int) (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (re : RawExpr)
         → CompSim Int (evalᴰ e' x) (λ s → eval s defs ρ re)
         → CompSim Int (evalᴰ (negIR ∘ e') x) (λ s → eval s defs ρ (RUnaryOp OpNeg re))
  cs-neg {Γ} e' x ρ re (se , ve , ev , op , tr , rr) with int-val ve _ rr
  ... | (vn , refl , rrn) =
        suc se , Vint 0 , ev , op-eq , trans (++-identityʳ _) tr , refl
      where
      op-eq : ∀ z → suc se ≤ z
            → eval z defs ρ (RUnaryOp OpNeg re) ≡ just (Vint 0 , ev)
      op-eq (suc k) (s≤s le) rewrite op k le | ++-identityʳ ev = refl

  -- `arr'` (effect lifting): `elaborate (arr' f) = arr ∘ elaborate f`,
  -- `evalᴰ arr g = returnT g` — `arr` is value-identity (trace `[]`), and the
  -- arrow value-sim `_~⟨A⇒[k]B⟩_` is PARAMETRIC in the kind `k`, so the
  -- sub-computation's `CompSim` transfers unchanged (only the trace gets `++[]`).
  cs-arr : ∀ {Γ A B q} (e' : IR Γ (A ⇒[ Once.Type.pureK q ] B))
             (x : ⟦ Γ ⟧ᴰ) (ρ : Env) (re : RawExpr)
         → CompSim (A ⇒[ Once.Type.pureK q ] B) (evalᴰ e' x) (λ s → eval s defs ρ re)
         → CompSim (A ⇒[ Once.Type.effK ] B) (evalᴰ (arr ∘ e') x) (λ s → eval s defs ρ re)
  cs-arr e' x ρ re (s , ve , evs , op , tr , rr) =
    s , ve , evs , op , trans (++-identityʳ _) tr , rr

  ------------------------------------------------------------------
  -- THE BRIDGE SPINE (top-down). `erase` turns a typed `Expr` into the raw
  -- form `SS.eval` runs (canonical de-Bruijn-LEVEL names for binders); `bridge`
  -- is the structural induction relating `evalᴰ (elaborate m e)` to
  -- `SS.eval (erase e)`, dispatching to the per-constructor `cs-*` lemmas. The
  -- recursive cases pass the IH as the continuation hypothesis (lam/let/case),
  -- with the bound var named `cname n` (the level of the new binder), matching
  -- `EnvRel`'s head-name discipline.
  --
  -- Not-yet-discharged constructors route through `bridge-hole`: `effApp`
  -- (D018 suspension FORK — needs a decision), `div`/`mod` (div-by-zero policy,
  -- D054-deferred), comparisons `lt..ne` (concrete `semM` — determined, pending),
  -- `arr'` (determined), `sigOp`/`closure`/`poly` (effect/fn primitives),
  -- `lift-morphism`/`morph-app`/`cata` (morphism realm + Cata phase).
  ------------------------------------------------------------------
  erase : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → RawExpr
  erase {n} (var i)        = RVar (cname (n ∸ suc (toℕ i)))
  erase {n} (lam q _ e)    = RLam (cname n) (erase e)
  erase (app f x)          = RApp (erase f) (erase x)
  erase (effApp f x)       = RApp (erase f) (erase x)
  erase (pair a b)         = RPair (erase a) (erase b)
  erase (fst' e)           = RApp (RVar "fst") (erase e)
  erase (snd' e)           = RApp (RVar "snd") (erase e)
  erase (inl' e)           = RApp (RVar "inl") (erase e)
  erase (inr' e)           = RApp (RVar "inr") (erase e)
  erase {n} (case' s l r)  = RDestruct (erase s) (cname n) (erase l) (cname n) (erase r)
  erase unit               = RUnit
  erase (absurd e)         = erase e
  erase {n} (let' e1 e2)   = RLet (cname n) (erase e1) (erase e2)
  erase (int x)            = RInt x
  erase (str s)            = RStringLit s
  erase (add a b)          = RBinOp OpAdd (erase a) (erase b)
  erase (sub a b)          = RBinOp OpSub (erase a) (erase b)
  erase (mul a b)          = RBinOp OpMul (erase a) (erase b)
  erase (div a b)          = RBinOp OpDiv (erase a) (erase b)
  erase (mod' a b)         = RBinOp OpMod (erase a) (erase b)
  erase (neg e)            = RUnaryOp OpNeg (erase e)
  erase (Elt a b)          = RBinOp OpLt (erase a) (erase b)
  erase (Ele a b)          = RBinOp OpLe (erase a) (erase b)
  erase (Egt a b)          = RBinOp OpGt (erase a) (erase b)
  erase (Ege a b)          = RBinOp OpGe (erase a) (erase b)
  erase (Eeq a b)          = RBinOp OpEq (erase a) (erase b)
  erase (Ene a b)          = RBinOp OpNe (erase a) (erase b)
  erase (arr' f)           = erase f
  erase (sigOp name)       = RVar name
  erase (closure name)     = RVar name
  erase (poly name T)      = RVar name
  erase (lift-morphism _)  = RUnit
  erase (morph-app _ e)    = erase e
  erase (cata _ _)         = RUnit

  postulate
    -- No-shadow obligation (user-confirmed): a canonical env never binds a
    -- builtin name and `defs` doesn't redefine one, so `RVar name` resolves to
    -- its `Vbuiltin`. Discharge: `cname k ≢ <builtin>` + `lookupDef defs name ≡
    -- nothing`.
    canonical-no-shadow :
      ∀ {n} {Γ : Ctx n} {dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ} (ρ : Env) → EnvRel ρ Γ dγ
      → (name : String) (bt : BTag) → classifyB name ≡ just bt
      → ∀ z → eval (suc z) defs ρ (RVar name) ≡ just (Vbuiltin bt [] , [])

  bridge : ∀ (m : AllocMode) {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
             (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (ρ : Env) → EnvRel ρ Γ dγ
         → CompSim A (evalᴰ (elaborate m e) dγ) (λ z → eval z defs ρ (erase e))

  postulate
    -- The not-yet-discharged constructors (see the header above). Each clause
    -- below instantiates this at its constructor; replacing a clause with a real
    -- `cs-*` lemma discharges that hole.
    bridge-hole :
      ∀ (m : AllocMode) {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
        (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (ρ : Env) → EnvRel ρ Γ dγ
      → CompSim A (evalᴰ (elaborate m e) dγ) (λ z → eval z defs ρ (erase e))

  bridge m {n} {Γ} (var i)      dγ ρ env = cs-var i dγ ρ env
  bridge m {n} (lam q _ e)      dγ ρ env =
    cs-lam {kk = Once.Type.pureK q} (elaborate m e) m dγ ρ (erase e)
      (λ w a rel → bridge m e (dγ , a) ((cname n , w) ∷ ρ) (refl , env , rel))
  bridge m (app f x)            dγ ρ env =
    cs-app (elaborate m f) (elaborate m x) m dγ ρ (erase f) (erase x)
      (bridge m f dγ ρ env) (bridge m x dγ ρ env)
  bridge m (pair a b)           dγ ρ env =
    cs-pair (elaborate m a) (elaborate m b) m dγ ρ (erase a) (erase b)
      (bridge m a dγ ρ env) (bridge m b dγ ρ env)
  bridge m (fst' e)             dγ ρ env =
    cs-fst (elaborate m e) dγ ρ (erase e)
      (canonical-no-shadow ρ env "fst" bFst refl) (bridge m e dγ ρ env)
  bridge m (snd' e)             dγ ρ env =
    cs-snd (elaborate m e) dγ ρ (erase e)
      (canonical-no-shadow ρ env "snd" bSnd refl) (bridge m e dγ ρ env)
  bridge m (inl' e)             dγ ρ env =
    cs-inl (elaborate m e) m dγ ρ (erase e)
      (canonical-no-shadow ρ env "inl" bInl refl) (bridge m e dγ ρ env)
  bridge m (inr' e)             dγ ρ env =
    cs-inr (elaborate m e) m dγ ρ (erase e)
      (canonical-no-shadow ρ env "inr" bInr refl) (bridge m e dγ ρ env)
  bridge m {n} (case' s l r)    dγ ρ env =
    cs-case (elaborate m s) (elaborate m l) (elaborate m r) m dγ ρ
      (cname n) (cname n) (erase s) (erase l) (erase r)
      (bridge m s dγ ρ env)
      (λ a da rel → bridge m l (dγ , da) ((cname n , a) ∷ ρ) (refl , env , rel))
      (λ b db rel → bridge m r (dγ , db) ((cname n , b) ∷ ρ) (refl , env , rel))
  bridge m {n} {Γ} unit         dγ ρ env = cs-unit {⟦ Γ ⟧ᶜ} dγ ρ
  bridge m (absurd e)           dγ ρ env =
    cs-absurd (elaborate m e) dγ ρ (erase e) (bridge m e dγ ρ env)
  bridge m {n} (let' e1 e2)     dγ ρ env =
    cs-let (elaborate m e1) (elaborate m e2) m dγ ρ (cname n) (erase e1) (erase e2)
      (bridge m e1 dγ ρ env)
      (λ v1 dv1 rel → bridge m e2 (dγ , dv1) ((cname n , v1) ∷ ρ) (refl , env , rel))
  bridge m {n} {Γ} (int x)      dγ ρ env = cs-int {⟦ Γ ⟧ᶜ} x dγ ρ
  bridge m {n} {Γ} (str s)      dγ ρ env = cs-str {⟦ Γ ⟧ᶜ} s dγ ρ
  bridge m (add a b)            dγ ρ env =
    cs-add (elaborate m a) (elaborate m b) m dγ ρ (erase a) (erase b)
      (bridge m a dγ ρ env) (bridge m b dγ ρ env)
  bridge m (sub a b)            dγ ρ env =
    cs-sub (elaborate m a) (elaborate m b) m dγ ρ (erase a) (erase b)
      (bridge m a dγ ρ env) (bridge m b dγ ρ env)
  bridge m (mul a b)            dγ ρ env =
    cs-mul (elaborate m a) (elaborate m b) m dγ ρ (erase a) (erase b)
      (bridge m a dγ ρ env) (bridge m b dγ ρ env)
  bridge m (neg e)              dγ ρ env =
    cs-neg (elaborate m e) dγ ρ (erase e) (bridge m e dγ ρ env)
  bridge m (arr' f)             dγ ρ env =
    cs-arr (elaborate m f) dγ ρ (erase f) (bridge m f dγ ρ env)
  -- Holes (see header) — one catch-all covers every not-yet-discharged
  -- constructor (effApp, div, mod', lt..ne, arr', sigOp/closure/poly,
  -- lift-morphism/morph-app, cata). It does NOT destructure `e`, so the free
  -- result-type implicits of `sigOp`/`closure`/`poly` (where `elaborate`
  -- dispatches on the type shape) stay abstract. Discharge = peel a constructor
  -- off into a real clause above.
  bridge m e                    dγ ρ env = bridge-hole m e dγ ρ env

  -- Closed-program specialisation (the entry the `#10` connection needs): a
  -- CLOSED `Expr ∅ ∅ A` (the shape of `main`) elaborated in the empty env. The
  -- empty environment trivially relates (`EnvRel [] ∅ tt = ⊤`), and `⟦ ⟦ ∅ ⟧ᶜ ⟧ᴰ
  -- = ⊤`, so `dγ = tt`. This is `evalᴰ (elaborate m e) tt` ↔ `SS.eval [] (erase e)`,
  -- one step from `compiled-main-trace` (which still needs: the compiler identity
  -- `ir = elaborate (checkElab body)`, α-invariance `SS.eval body ≈ SS.eval
  -- (erase (checkElab body))`, and the CompSim → take-k reading).
  bridge-main : ∀ (m : AllocMode) {Ψ : Usage 0} {A} (e : Expr ∅ Ψ A)
              → CompSim A (evalᴰ (elaborate m e) tt) (λ z → eval z defs [] (erase e))
  bridge-main m e = bridge m e tt [] tt
