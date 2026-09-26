-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RealizeAgrees — the proof behind `RealizeBridge.realize-agrees`
-- (Plan 0.49 piece 3). `checkElab`'s emitted term `se` denotes the same as the
-- canonical `realize` term read off its typing witness `w` (which `realize`
-- consumes, INDEPENDENT of `checkElab`'s term). A wrong elaboration breaks the apex.
--
-- Stated over the ELABORATOR EQUATION (`inferElabV`/`checkElabV ≡ (success … , w)`),
-- NOT an arbitrary derivation: the witness `w` is then exactly the elaborator's
-- own output, so `se` is well-defined (an arbitrary `⊢ᶜ` derivation over-generates
-- — `t-embed (t-pair …)` vs the `t-pair-lit-check` the checker actually emits).
-- Induct on `e`, fold the elaborator via `with inferElabV ctx a in eqa` (now clean
-- because the multi-`with` `inferElabV` clauses were refactored to aux helpers).
-- `faithful`-style agreements: `_>>=T_` threads each sub at the same depth `k`.
--
-- WIP: leaves + `RPair` (infer) validate the equation-form technique end to end;
-- the rest route through `infer-agreeV-todo`/`check-agreeV-todo`
-- ([[feedback_scaffold_then_discharge]] — to be emptied).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)
-- plan 0.74 J6 step 3: `⊝-fromℤ` — negating a literal IS the negated literal.
import Once.Word as OnceWord
import Data.List as DL

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.RealizeAgrees (fmt : TargetNum) where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-mono-<; +-mono-≤; m≤m+n; m≤n+m; +-suc; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Data.Bool using (true)
import Once.Type
open import Once.Type using (Type; Int; Unit; Void; Float; Str; Buffer; _*_; _+_; μ-type; ν-type;
                             Purity; pure; eff; mk-kind; Quantity; Many; One; Zero; _⇒[_]_; isUnit?; isVoid?; ⟦_⟧T; Functor)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx; extendNamedCtx; lookupImport; lookupLocal; ctxWithImportsAndPolys;
  GenView; classifyGen; gv-id; gv-fst; gv-snd; gv-terminal; gv-initial; gv-inl; gv-inr; gv-unit; gv-other)
open import Once.TypeCheck.Elaborate using (success; failure; VerifiedInferResult; VerifiedCheckResult)
import Once.TypeCheck.Elaborate as E
open import Once.IR as IR using (IR)
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Maybe.Properties using (just-injective)
open import Once.Denotation.TraceMonad using (T; returnT; resT-lift; _>>=T_; fmapT)
open import Once.Type.Sub using (_<:_; _<:?_; _⊑π?_; sub-arr; <:-refl)
open import Once.Type.DecEq using (_≟T_)
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Postulates using (extensionality)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Once.TypeCheck.Judgment using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; _⊢ᵈ_∶_⇒[_]↦_⨾_; t-int; t-str; t-unit; t-pair; t-neg; t-neg-float; t-let; t-binop-arith; t-binop-cmp)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Surface.Syntax as Surface using (Expr; Usage; ⟦_⟧ᶜ; pair; neg; let'; sigOp; lift-morphism; app; lam)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; liftFn; anaFᵈ; coerce-functor-D)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.SigOp.Info using (mk-info'; haltsV; emitsV; pureV; ffi-concrete; semM)
open import Once.Arith.SigOp.Builders using (generic-semM; arrow-info-eff; i2f-info; add-info; sub-info; mul-info; div-info; mod-info; fadd-info; fsub-info; fmul-info; fdiv-info; lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
import Once.Denotation.SourceDenote as SD
open import Once.Surface.Seq using (seq; seq0; embedClosed; closed-usage-eq)
open import Once.Surface.Properties using (+ᵘ-identityʳ)
open import Once.Surface.Elaborate using (elaborate)
open import Once.Adequacy.SourceFaithful fmt using (faithful; T-ext-at)
open import Once.CanonicalName using (CanonicalName; showCanonical; bare; NotGenerator; gen; GenWord; genWord?)
open import Once.Functor.Translate using (WellFormedF; IsBaseType; IsConcrete; con-base; con-fun; base-Unit)
open import Once.Functor.Decide using (wellFormedF?; isBaseType?; isConcrete?)

private
  -- D143: the RUNTIME environment. `⟦_⟧ˢ` is phase-indexed, so agreement is
  -- stated over `debruijn ctx ↾ Ψ` — the variables the term actually uses —
  -- not the full context. Mirrors `EnvRun` in `Once.Denotation.Meaning`.
  Env : (ctx : NamedCtx) → Usage (NamedCtx.size ctx) → Set
  Env ctx Ψ = ⟦ ⟦ NamedCtx.debruijn ctx Surface.↾ Ψ ⟧ᶜ ⟧ᴰ

-- | Two-sided bind congruence. Both monadic arguments and both continuations
-- are PARAMETERS: `m >>=T f` REDUCES, so a congruence that leaves `m` or `f` to
-- be inferred poses an unsolvable higher-order constraint.
-- plan 0.98: ONE equation of computations. The budget-indexed form is gone —
-- with `T` a record, equal-at-every-budget IS equality (as in `FaithfulLemmas`).
SD-subst-usage′ : ∀ {n} {Γ : Surface.Ctx n} {A} {Ψ Ψ' : Usage n} (eq : Ψ ≡ Ψ')
                   {e : Expr Γ Ψ A} dγ
  → SD.⟦ subst (λ u → Expr Γ u A) eq e ⟧ˢ fmt dγ ≡ SD.⟦ e ⟧ˢ fmt (subst _ (sym eq) dγ)
SD-subst-usage′ refl dγ = refl

bind2-agree : ∀ {X Y : Set} (mR mU : T X) (gR gU : X → T Y)
  → (mR ≡ mU) → (∀ v → gR v ≡ gU v)
  → (mR >>=T gR) ≡ (mU >>=T gU)
bind2-agree mR .mR gR gU refl ge = cong (λ g → mR >>=T g) (extensionality ge)

-- | The BINARY-OPERAND shape, shared by every two-operand node. Both sides run
-- the same continuation `g`; they differ only in the two operand denotations,
-- each of which lives on its own narrowing of the runtime environment.
binop-agree : ∀ {X Y Z : Set} (mR mU : T X) (nR nU : T Y) (g : X → Y → T Z)
  → (mR ≡ mU) → (nR ≡ nU)
  → (mR >>=T λ x → nR >>=T λ y → g x y)
            ≡ (mU >>=T λ x → nU >>=T λ y → g x y)
binop-agree mR mU nR nU g me ne =
  bind2-agree mR mU (λ x → nR >>=T λ y → g x y) (λ x → nU >>=T λ y → g x y) me
    (λ x → bind2-agree nR nU (λ y → g x y) (λ y → g x y) ne (λ y → refl))

-- | The APPLICATION shape. `⟦ app ⟧ˢ` splits on the arrow's quantity — at
-- `Zero` the argument is ERASED, so it is never evaluated and only the
-- function's IH exists to use — hence this is a top-level helper with three
-- clauses rather than a `q`-general `with` branch ([[feedback_with_clauses_painful]],
-- [[feedback_mutual_block_syntax]]). The IHs come in ENVIRONMENT-GENERAL, so
-- each clause simply applies them at the narrowing its own denotation carries.
app-agree : ∀ {ctx : NamedCtx} {A B : Type} (q : Quantity)
            {Ψ₁ Ψ₂ : Usage (NamedCtx.size ctx)}
            (fR fU : Expr (NamedCtx.debruijn ctx) Ψ₁ (A ⇒[ mk-kind q pure ] B))
            (xR xU : Expr (NamedCtx.debruijn ctx) Ψ₂ A)
          → (∀ E → SD.⟦ fR ⟧ˢ fmt E ≡ SD.⟦ fU ⟧ˢ fmt E)
          → (∀ E → SD.⟦ xR ⟧ˢ fmt E ≡ SD.⟦ xU ⟧ˢ fmt E)
          → ∀ (dγ : Env ctx (Ψ₁ Surface.+ᵘ (q Surface.*ᵘ Ψ₂)))
          → SD.⟦ app fR xR ⟧ˢ fmt dγ ≡ SD.⟦ app fU xU ⟧ˢ fmt dγ
app-agree {ctx = ctx} {A = A} Zero {Ψ₁} {Ψ₂} fR fU xR xU fIH xIH dγ =
  bind2-agree (SD.⟦ fR ⟧ˢ fmt Ef) (SD.⟦ fU ⟧ˢ fmt Ef)
              (λ vf → vf tt) (λ vf → vf tt) (fIH Ef) (λ v → refl)
  where Ef = restrictᴰ {Γ = NamedCtx.debruijn ctx}
               (Surface.⊑ᵘ-+ˡ Ψ₁ (Zero Surface.*ᵘ Ψ₂)) dγ
app-agree {ctx = ctx} {A = A} One {Ψ₁} {Ψ₂} fR fU xR xU fIH xIH dγ =
  bind2-agree (SD.⟦ fR ⟧ˢ fmt Ef) (SD.⟦ fU ⟧ˢ fmt Ef)
    (λ vf → SD.⟦ xR ⟧ˢ fmt Ex >>=T λ vx → vf vx)
    (λ vf → SD.⟦ xU ⟧ˢ fmt Ex >>=T λ vx → vf vx)
    (fIH Ef)
    (λ vf → bind2-agree (SD.⟦ xR ⟧ˢ fmt Ex) (SD.⟦ xU ⟧ˢ fmt Ex)
                (λ vx → vf vx) (λ vx → vf vx) (xIH Ex) (λ v → refl))
  where Ef = restrictᴰ {Γ = NamedCtx.debruijn ctx}
               (Surface.⊑ᵘ-+ˡ Ψ₁ (One Surface.*ᵘ Ψ₂)) dγ
        Ex = restrictᴰ {Γ = NamedCtx.debruijn ctx}
               (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*One Ψ₂)
                  (Surface.⊑ᵘ-+ʳ Ψ₁ (One Surface.*ᵘ Ψ₂))) dγ
app-agree {ctx = ctx} {A = A} Many {Ψ₁} {Ψ₂} fR fU xR xU fIH xIH dγ =
  bind2-agree (SD.⟦ fR ⟧ˢ fmt Ef) (SD.⟦ fU ⟧ˢ fmt Ef)
    (λ vf → SD.⟦ xR ⟧ˢ fmt Ex >>=T λ vx → vf vx)
    (λ vf → SD.⟦ xU ⟧ˢ fmt Ex >>=T λ vx → vf vx)
    (fIH Ef)
    (λ vf → bind2-agree (SD.⟦ xR ⟧ˢ fmt Ex) (SD.⟦ xU ⟧ˢ fmt Ex)
                (λ vx → vf vx) (λ vx → vf vx) (xIH Ex) (λ v → refl))
  where Ef = restrictᴰ {Γ = NamedCtx.debruijn ctx}
               (Surface.⊑ᵘ-+ˡ Ψ₁ (Many Surface.*ᵘ Ψ₂)) dγ
        Ex = restrictᴰ {Γ = NamedCtx.debruijn ctx}
               (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ₂)
                  (Surface.⊑ᵘ-+ʳ Ψ₁ (Many Surface.*ᵘ Ψ₂))) dγ

-- | The LAMBDA shape. `⟦ lam ⟧ˢ` splits on BOTH the arrow's quantity `q` and
-- the binder's usage in the body `q'`: at `q = Zero` the meaning takes no
-- argument, and at `q' = Zero` the binder never enters the body's environment
-- (`bindᴰ0`), so no witness of `A` is required. Six clauses, constrained by
-- `q' ≤q q`. A top-level helper rather than a `with`-branch split, and the body
-- IH arrives ENVIRONMENT-GENERAL so each clause applies it directly.
lam-agree : ∀ {ctx : NamedCtx} {A B : Type} {π : Purity} (q q' : Quantity)
            {Ψ : Usage (NamedCtx.size ctx)}
            (leq : (q' Once.Type.≤q q) ≡ true)
            (bR bU : Expr (NamedCtx.debruijn ctx Surface., A) (q' Surface.∷ Ψ) B)
          → (∀ E → SD.⟦ bR ⟧ˢ fmt E ≡ SD.⟦ bU ⟧ˢ fmt E)
          → ∀ (dγ : Env ctx Ψ)
          → SD.⟦ lam {π = π} q leq bR ⟧ˢ fmt dγ ≡ SD.⟦ lam {π = π} q leq bU ⟧ˢ fmt dγ
lam-agree {ctx = ctx} {A = A} Zero Zero leq bR bU bIH dγ =
  cong returnT
    (extensionality (λ _ → bIH (bindᴰ0 {Γ = NamedCtx.debruijn ctx} {A = A} dγ)))
lam-agree {ctx = ctx} {A = A} One Zero leq bR bU bIH dγ =
  cong returnT
    (extensionality (λ a → bIH (bindᴰ0 {Γ = NamedCtx.debruijn ctx} {A = A} dγ)))
lam-agree {ctx = ctx} {A = A} Many Zero leq bR bU bIH dγ =
  cong returnT
    (extensionality (λ a → bIH (bindᴰ0 {Γ = NamedCtx.debruijn ctx} {A = A} dγ)))
lam-agree {ctx = ctx} {A = A} One One leq bR bU bIH dγ =
  cong returnT
    (extensionality (λ a → bIH (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} One dγ a)))
lam-agree {ctx = ctx} {A = A} Many One leq bR bU bIH dγ =
  cong returnT
    (extensionality (λ a → bIH (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} One dγ a)))
lam-agree {ctx = ctx} {A = A} Many Many leq bR bU bIH dγ =
  cong returnT
    (extensionality (λ a → bIH (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} Many dγ a)))

-- Agreement of the elaborator's emitted term `se` with `realize`(its witness),
-- over the elaborator equation. (Forward sigs for the mutual block + scaffolds.)
------------------------------------------------------------------------
-- The expression measure. Defined HERE (not just before the mutual block it
-- terminates) because D127 made the combinator helpers take a SUB-EXPRESSION
-- induction hypothesis bounded by `μ`: a combinator arm is now an ordinary
-- term, so its agreement is the recursion's, not a morphism-extraction fact.
------------------------------------------------------------------------
μ : RawExpr → ℕ
μ (Raw.RVar _) = 1
μ (Raw.RQualified _ _) = 1
μ (Raw.RResolved _) = 1
μ (Raw.RApp f x) = suc (μ f +ℕ μ x)
μ (Raw.RLam _ b) = suc (μ b)
μ (Raw.RLet _ e₁ e₂) = suc (μ e₁ +ℕ μ e₂)
μ (Raw.RPair a b) = suc (μ a +ℕ μ b)
μ (Raw.RDestruct s _ l _ r) = suc (μ s +ℕ (μ l +ℕ μ r))
μ Raw.RUnit = 1
μ (Raw.RInt _) = 1
μ (Raw.RFloat _ _ _ _) = 1
μ (Raw.RStringLit _) = 1
μ (Raw.RAnnot e _) = suc (μ e)
μ (Raw.RBinOp _ a b) = suc (μ a +ℕ μ b)
μ (Raw.RUnaryOp _ e) = suc (μ e)
μ (Raw.RAna _ e) = suc (μ e)

-- generic subterm size bounds (raw ℕ; instantiate with the μ of children)
μ<-l : ∀ a b → a < suc (a +ℕ b)
μ<-l a b = s≤s (m≤m+n a b)
μ<-r : ∀ a b → b < suc (a +ℕ b)
μ<-r a b = s≤s (m≤n+m b a)
μ<-d-s : ∀ s l r → s < suc (s +ℕ (l +ℕ r))
μ<-d-s s l r = s≤s (m≤m+n s (l +ℕ r))
μ<-d-l : ∀ s l r → l < suc (s +ℕ (l +ℕ r))
μ<-d-l s l r = s≤s (≤-trans (m≤m+n l r) (m≤n+m (l +ℕ r) s))
-- D127: an applied combinator's INNER arm `RApp (RApp hd f) g` — `μ f` is
-- strictly below the whole node, which is what `subIH` asks for.
inner-arm-< : ∀ (hd f g : RawExpr) → μ f < μ (Raw.RApp (Raw.RApp hd f) g)
inner-arm-< hd f g =
  ≤-trans (μ<-r (μ hd) (μ f))
    (≤-trans (m≤m+n (suc (μ hd +ℕ μ f)) (μ g)) (n≤1+n _))

μ<-d-r : ∀ s l r → r < suc (s +ℕ (l +ℕ r))
μ<-d-r s l r = s≤s (≤-trans (m≤n+m r l) (m≤n+m (l +ℕ r) s))


InferAgreeV : (ctx : NamedCtx) (e : RawExpr) {A : Type} {Ψ : Usage (NamedCtx.size ctx)}
              {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ} {w : ctx ⊢ᵢ e ∶ A ⨾ Ψ}
            → E.inferElabV ctx e ≡ (success A Ψ se d f , w) → Set
InferAgreeV ctx e {Ψ = Ψ} {se = se} {w = w} _ =
  ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ

CheckAgreeV : (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ : Usage (NamedCtx.size ctx)}
              {se : Expr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ}
            → E.checkElabV ctx e T ≡ (success Ψ se d f , w) → Set
CheckAgreeV ctx e T {Ψ = Ψ} {se = se} {w = w} _ =
  ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ

-- `infer-agreeV` is now TOTAL (every RawExpr constructor handled; the RApp
-- apply head is a morph-app congruence, `other` rides `agree-RApp-other-aux`).
-- Only check-mode's
-- non-`t-embed` specials (RLam/RVar-bbc/RPair-product/RInt-vlift/literals)
-- remain as a postulate.
postulate
  -- The RVar residual: ONLY `poly` (rides the `bbc-other-poly-witness` gap). The 6
  -- bare builtins (id/fst/snd/terminal/initial/inl/inr) are now DISCHARGED below.
  check-agreeV-RVar-poly-todo : ∀ (ctx : NamedCtx) (x : String) (T : Type) {fe snd Ψ se d f w}
    → E.checkElabV-RVar-bbc-other-aux ctx x T (failure fe , snd) ≡ (success Ψ se d f , w)
    → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
  -- Plan 0.58 / D071: the INFER-mode twin — the ground telescope reference's
  -- `poly` emission rides the `bbc-other-poly-infer-witness` gap the same way.
  infer-agreeV-RVar-poly-todo : ∀ (ctx : NamedCtx) (x : String) {A Ψ se d f w}
    → E.inferElabV-RVar-poly-aux ctx x ≡ (success A Ψ se d f , w)
    → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
  -- (Plan 0.55 D#2: `check-RApp-todo` ELIMINATED — all RApp check views discharged
  -- by explicit `agree-check-RApp` clauses; the residual is the narrow
  -- `agree-cata-denotes` denotational leaf. See below.)

-- DISCHARGED bbc-id leaf: `spec id = lift-morphism IR.id`, `realize-morph (m-id) =
-- IR.id`, so the sole success leaf (arrow target A⇒A, both lookups absent, A≟A) is
-- `refl`; every other target / lookup-found branch fails ⇒ absurd success-eq.
check-agreeV-RVar-id : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-id-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agreeV-RVar-id ctx (X ⇒[ mk-kind Many π ] Y) eq
  with X ≟T Y | eq
... | yes refl | refl = λ dγ → refl
... | no _ | ()
check-agreeV-RVar-id ctx Unit ()
check-agreeV-RVar-id ctx Void ()
check-agreeV-RVar-id ctx Int ()
check-agreeV-RVar-id ctx Float ()
check-agreeV-RVar-id ctx Str ()
check-agreeV-RVar-id ctx Buffer ()
check-agreeV-RVar-id ctx (_ * _) ()
check-agreeV-RVar-id ctx (_ + _) ()
check-agreeV-RVar-id ctx (μ-type _) ()
check-agreeV-RVar-id ctx (ν-type _) ()
check-agreeV-RVar-id ctx (_ ⇒[ mk-kind One _ ] _) ()
check-agreeV-RVar-id ctx (_ ⇒[ mk-kind Zero _ ] _) ()

-- DISCHARGED bbc-fst leaf: success at `(A * B) ⇒[Many π] A'` (lookups absent, A≟A');
-- `spec fst = lift-morphism IR.fst`, `realize-morph (m-fst) = IR.fst` ⇒ `refl`. All
-- other targets make `checkElabV-RVar-bbc-fst-failure-aux` reduce to `failure`, so
-- the success premise is a constructor clash Agda coverage prunes (no absurd matrix).
check-agreeV-RVar-fst : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-fst-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agreeV-RVar-fst ctx ((A * B) ⇒[ mk-kind Many π ] A') eq
  with A ≟T A' | eq
... | yes refl | refl = λ dγ → refl
... | no _ | ()

-- DISCHARGED bbc-snd (as fst, success at `(A * B) ⇒[Many π] B'` with B≟B').
check-agreeV-RVar-snd : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-snd-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agreeV-RVar-snd ctx ((A * B) ⇒[ mk-kind Many π ] B') eq
  with B ≟T B' | eq
... | yes refl | refl = λ dγ → refl
... | no _ | ()

-- DISCHARGED bbc-terminal: success at the canonical target; every other target makes
-- the elaborator dispatch fail (absurd success-eq). Codomain-fixed ⇒ quantity must
-- be concrete, so enumerate Many/One/Zero × codomain as plain top-level () (no
-- with-abstraction); non-arrow targets auto-prune via the premise clash.
check-agreeV-RVar-terminal : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-terminal-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many π ] Unit) refl = λ dγ → refl
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Unit) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Unit) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Void) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Void) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Void) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Int) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Int) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Int) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Float) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Float) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Float) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Str) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Str) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Str) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Buffer) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Buffer) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Buffer) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (_ * _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (_ * _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (_ * _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (_ + _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (_ + _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (_ + _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (μ-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (μ-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (μ-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (ν-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (ν-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (ν-type _)) ()

-- DISCHARGED bbc-initial: success at `Void ⇒[Many π] A` (no type-eq, lookups only).
check-agreeV-RVar-initial : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-initial-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agreeV-RVar-initial ctx (Void ⇒[ mk-kind Many π ] A) refl = λ dγ → refl

-- DISCHARGED bbc-inl: success at the canonical target; every other target makes
-- the elaborator dispatch fail (absurd success-eq). Codomain-fixed ⇒ quantity must
-- be concrete, so enumerate Many/One/Zero × codomain as plain top-level () (no
-- with-abstraction); non-arrow targets auto-prune via the premise clash.
check-agreeV-RVar-inl : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-inl-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many π ] (A' + B)) eq
  with A ≟T A' | eq
... | yes refl | refl = λ dγ → refl
... | no _ | ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (_ + _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (_ + _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Unit) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Unit) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Unit) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Void) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Void) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Void) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Int) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Int) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Int) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Float) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Float) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Float) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Str) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Str) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Str) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Buffer) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Buffer) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Buffer) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (_ * _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (_ * _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (_ * _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (μ-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (μ-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (μ-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (ν-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (ν-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (ν-type _)) ()

-- DISCHARGED bbc-inr: success at the canonical target; every other target makes
-- the elaborator dispatch fail (absurd success-eq). Codomain-fixed ⇒ quantity must
-- be concrete, so enumerate Many/One/Zero × codomain as plain top-level () (no
-- with-abstraction); non-arrow targets auto-prune via the premise clash.
check-agreeV-RVar-inr : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-inr-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many π ] (A + B')) eq
  with B ≟T B' | eq
... | yes refl | refl = λ dγ → refl
... | no _ | ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (_ + _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (_ + _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Unit) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Unit) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Unit) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Void) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Void) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Void) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Int) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Int) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Int) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Float) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Float) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Float) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Str) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Str) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Str) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Buffer) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Buffer) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Buffer) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (_ * _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (_ * _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (_ * _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (μ-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (μ-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (μ-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (ν-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (ν-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (ν-type _)) ()

-- RPair folded top-level (no `with`): take both sub-results explicitly +
-- their sub-IHs as functions; the de-withed `inferElabV-RPair-aux` reduces by
-- pattern-matching them. success/success is the real case; a `failure` sub
-- makes the aux a `failure`, so the success equation is absurd.
agree-RPair : ∀ {ctx : NamedCtx} {a b : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RPair a b ∶ A ⨾ Ψ}
  (rA : VerifiedInferResult ctx a) (rB : VerifiedInferResult ctx b)
  → E.inferElabV-RPair-aux ctx a b rA rB ≡ (success A Ψ se d f , w)
  → (∀ {Aₐ Ψₐ aE dₐ fₐ} {wA : ctx ⊢ᵢ a ∶ Aₐ ⨾ Ψₐ}
       → rA ≡ (success Aₐ Ψₐ aE dₐ fₐ , wA) → ∀ dγ → SD.⟦ aE ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer wA ⟧ˢ fmt dγ)
  → (∀ {Bᵦ Ψᵦ bE dᵦ fᵦ} {wB : ctx ⊢ᵢ b ∶ Bᵦ ⨾ Ψᵦ}
       → rB ≡ (success Bᵦ Ψᵦ bE dᵦ fᵦ , wB) → ∀ dγ → SD.⟦ bE ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer wB ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RPair {ctx = ctx} (success Aₐ Ψₐ aE dₐ fₐ , wA) (success Bᵦ Ψᵦ bE dᵦ fᵦ , wB)
            refl subA subB dγ =
  bind2-agree
    (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
    (λ va → SD.⟦ bE ⟧ˢ fmt E₂ >>=T λ vb → returnT (va , vb))
    (λ va → SD.⟦ realize-infer wB ⟧ˢ fmt E₂ >>=T λ vb → returnT (va , vb))
    (subA refl E₁)
    (λ va → bind2-agree
                (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
                (λ vb → returnT (va , vb)) (λ vb → returnT (va , vb))
                (subB refl E₂) (λ vb → refl))

  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RPair (failure _ , _) _ () subA subB
agree-RPair (success _ _ _ _ _ , _) (failure _ , _) () subA subB

-- RUnaryOp(neg) folded top-level (avoids mutual-block `...|` ambiguity,
-- [[feedback_mutual_block_syntax]]): takes the sub-result explicitly + the
-- sub-IH as a function (applied only in the Int branch). Non-Int/failure subs
-- make `inferElabV-RUnaryOp-aux` a `failure`, so the success equation is absurd.
agree-RUnaryOp : ∀ {ctx : NamedCtx} {e : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RUnaryOp Raw.OpNeg e ∶ A ⨾ Ψ}
  (rE : VerifiedInferResult ctx e)
  → E.inferElabV-RUnaryOp-aux ctx e rE ≡ (success A Ψ se d f , w)
  → (∀ {T' Ψ' eE' d' fr'} {wE' : ctx ⊢ᵢ e ∶ T' ⨾ Ψ'}
       → rE ≡ (success T' Ψ' eE' d' fr' , wE')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer wE' ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RUnaryOp (success Int Ψ eE d fr , wE) refl subAg dγ rewrite subAg refl dγ = refl
-- D229 / plan 0.94 §13: a `Void` operand — the term is the operand's.
agree-RUnaryOp (success Once.Type.Void Ψ eE d fr , wE) refl subAg dγ = subAg refl dγ
agree-RUnaryOp (failure _ , _) () subAg
agree-RUnaryOp (success Once.Type.Unit _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Float _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Str _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Buffer _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.* _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.+ _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (Once.Type.μ-type _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (Once.Type.ν-type _) _ _ _ _ , _) () subAg

-- RBinOp folded top-level (mirrors `inferElabV-RBinOp-aux`'s left-type /
-- right-type / op dispatch). Both operands must elaborate to `Int`; any other
-- left/right shape makes the aux `failure`, so the success equation is absurd
-- (`()`). For the 11 success ops the witness is `t-binop-{arith,cmp} refl w₁ w₂`
-- and `se` is the matching arithmetic/comparison IR; `realize-infer` rebuilds
-- the SAME IR over `realize-infer w₁/w₂`, so rewriting both operand IHs at
-- `(dγ,k)` (the binary op denotation is fuel-`k`-pointwise, as for `agree-RPair`)
-- closes each case with `refl`.
agree-RBinOp : ∀ {ctx : NamedCtx} (op : Raw.BinOp) {e₁ e₂ : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RBinOp op e₁ e₂ ∶ A ⨾ Ψ}
  (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
  → E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂ ≡ (success A Ψ se d f , w)
  → (∀ {A₁ Ψ₁ e₁E d₁ f₁} {w₁ : ctx ⊢ᵢ e₁ ∶ A₁ ⨾ Ψ₁}
       → r₁ ≡ (success A₁ Ψ₁ e₁E d₁ f₁ , w₁) → ∀ dγ → SD.⟦ e₁E ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ)
  → (∀ {A₂ Ψ₂ e₂E d₂ f₂} {w₂ : ctx ⊢ᵢ e₂ ∶ A₂ ⨾ Ψ₂}
       → r₂ ≡ (success A₂ Ψ₂ e₂E d₂ f₂ , w₂) → ∀ dγ → SD.⟦ e₂E ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w₂ ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
-- left operand fails to be Int → aux is `failure`
agree-RBinOp op (failure _ , _) _ () s₁ s₂
agree-RBinOp op (success Unit _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Void _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Str _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Buffer _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ * _) _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ + _) _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ ⇒[ _ ] _) _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (μ-type _) _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (ν-type _) _ _ _ _ , _) _ () s₁ s₂
-- left is Int, right fails to be Int → aux is `failure`
agree-RBinOp op (success Int _ _ _ _ , _) (failure _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Unit _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Void _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Str _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Buffer _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ * _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ + _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ ⇒[ _ ] _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (μ-type _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (ν-type _) _ _ _ _ , _) () s₁ s₂
-- both Int → the op picks the IR; the two operand IHs, one equation each
agree-RBinOp {ctx = ctx} Raw.OpAdd (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM add-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpSub (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM sub-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpMul (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM mul-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpDiv (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM div-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpMod (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM mod-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpLt (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM lt-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpLe (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM le-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpGt (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM gt-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpGe (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM ge-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpEq (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM eq-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpNe (success Int Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM ne-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
-- PLAN 0.75 F4: `Float` on the left is no longer absurd — it selects the float
-- family. Same shape as the integer block above: a mismatched right operand
-- still makes the aux a `failure`, and the three real ops rewrite both operand
-- IHs. `/`, `%` and the comparisons stay absurd at `Float`, which is what
-- `isFloatArithmeticOp` buys.
agree-RBinOp op (success Float _ _ _ _ , _) (failure _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Unit _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Void _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Str _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Buffer _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (_ * _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (_ + _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (_ ⇒[ _ ] _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (μ-type _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (ν-type _) _ _ _ _ , _) () s₁ s₂
agree-RBinOp {ctx = ctx} Raw.OpAdd (success Float Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fadd-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpSub (success Float Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fsub-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpMul (success Float Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fmul-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpDiv (success Float Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fdiv-info fmt (va , vb))) (s₁ refl E₁) (s₂ refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp Raw.OpMod (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLt (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLe (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGt (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGe (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpEq (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpNe (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
-- D125: the mixed forms are no longer absurd — the `Int` side widens. Same
-- two-IH rewrite; the `i2f` node sits inside the elaborated term on one side
-- and inside `realize-infer`'s output on the other, so it cancels.
agree-RBinOp {ctx = ctx} Raw.OpAdd (success Int Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁ >>=T ci2f) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁ >>=T ci2f)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fadd-info fmt (va , vb))) (bind2-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
                           ci2f ci2f (s₁ refl E₁) (λ v → refl))
                (s₂ refl E₂)
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpAdd (success Float Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂ >>=T ci2f) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂ >>=T ci2f)
              (λ va vb → resT-lift (semM fadd-info fmt (va , vb))) (s₁ refl E₁)
                (bind2-agree (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
                           ci2f ci2f (s₂ refl E₂) (λ v → refl))
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpSub (success Int Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁ >>=T ci2f) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁ >>=T ci2f)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fsub-info fmt (va , vb))) (bind2-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
                           ci2f ci2f (s₁ refl E₁) (λ v → refl))
                (s₂ refl E₂)
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpSub (success Float Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂ >>=T ci2f) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂ >>=T ci2f)
              (λ va vb → resT-lift (semM fsub-info fmt (va , vb))) (s₁ refl E₁)
                (bind2-agree (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
                           ci2f ci2f (s₂ refl E₂) (λ v → refl))
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpMul (success Int Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁ >>=T ci2f) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁ >>=T ci2f)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fmul-info fmt (va , vb))) (bind2-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
                           ci2f ci2f (s₁ refl E₁) (λ v → refl))
                (s₂ refl E₂)
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpMul (success Float Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂ >>=T ci2f) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂ >>=T ci2f)
              (λ va vb → resT-lift (semM fmul-info fmt (va , vb))) (s₁ refl E₁)
                (bind2-agree (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
                           ci2f ci2f (s₂ refl E₂) (λ v → refl))
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpDiv (success Int Ψₐ aE _ _ , wA) (success Float Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁ >>=T ci2f) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁ >>=T ci2f)
              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
              (λ va vb → resT-lift (semM fdiv-info fmt (va , vb))) (bind2-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
                           ci2f ci2f (s₁ refl E₁) (λ v → refl))
                (s₂ refl E₂)
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp {ctx = ctx} Raw.OpDiv (success Float Ψₐ aE _ _ , wA) (success Int Ψᵦ bE _ _ , wB)
             refl s₁ s₂ dγ =
  binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize-infer wA ⟧ˢ fmt E₁)
              (SD.⟦ bE ⟧ˢ fmt E₂ >>=T ci2f) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂ >>=T ci2f)
              (λ va vb → resT-lift (semM fdiv-info fmt (va , vb))) (s₁ refl E₁)
                (bind2-agree (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize-infer wB ⟧ˢ fmt E₂)
                           ci2f ci2f (s₂ refl E₂) (λ v → refl))
  where
    ci2f = λ va → resT-lift (semM i2f-info fmt va)
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψₐ Ψᵦ) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψₐ Ψᵦ) dγ
agree-RBinOp Raw.OpMod (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpMod (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLt (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLt (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLe (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLe (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGt (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGt (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGe (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGe (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpEq (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpEq (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpNe (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpNe (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂

-- RLet folded with-free via two levels (e₂'s context depends on e₁'s type A):
-- `agree-RLet` matches the e₁ result, `agree-RLet2` the e₂ result; the let'
-- agreement threads `v1` through `_>>=T_` by inline rewrite (rewrite the bound
-- IH at `(dγ,k)` — fixing `v1` — then the body IH at the now-fixed
-- `(dγ, proj₂ ⟦realize w₁⟧)`). The e₂ IH
-- is passed as a function of A (only knowable after matching e₁).
agree-RLet2 : ∀ {ctx : NamedCtx} {x e₁ e₂ A B} {Ψ₁ : Usage (NamedCtx.size ctx)}
  {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ B} {d f} {w : ctx ⊢ᵢ Raw.RLet x e₁ e₂ ∶ B ⨾ Ψ}
  (e₁E : Expr (NamedCtx.debruijn ctx) Ψ₁ A) (d₁ f₁ : ℕ) (w₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁)
  (rE2 : VerifiedInferResult (extendNamedCtx ctx x A) e₂)
  → E.inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ w₁ rE2 ≡ (success B Ψ se d f , w)
  → (∀ dγ → SD.⟦ e₁E ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ)
  → (∀ {B' q Ψ₂' e₂E d₂' f₂'} {w₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B' ⨾ (q ∷ᵘ Ψ₂')}
       → rE2 ≡ (success B' (q ∷ᵘ Ψ₂') e₂E d₂' f₂' , w₂)
       → ∀ dγ' → SD.⟦ e₂E ⟧ˢ fmt dγ' ≡ SD.⟦ realize-infer w₂ ⟧ˢ fmt dγ')
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
-- D143: at an ERASED binder the bound term is never evaluated and the body
-- runs on the UNEXTENDED runtime environment, so only the body's IH is used.
agree-RLet2 {ctx = ctx} {A = A} {Ψ₁ = Ψ₁} e₁E d₁ f₁ w₁
            (success B (Zero ∷ᵘ Ψ₂) e₂E d₂ f₂ , w₂) refl e₁ag e₂IH dγ =
  e₂IH refl (bindᴰ0 {Γ = NamedCtx.debruijn ctx} {A = A}
               (restrictᴰ {Γ = NamedCtx.debruijn ctx}
                  (Surface.⊑ᵘ-+ˡ Ψ₂ (Zero Surface.*ᵘ Ψ₁)) dγ))
agree-RLet2 {ctx = ctx} {A = A} {Ψ₁ = Ψ₁} e₁E d₁ f₁ w₁
            (success B (One ∷ᵘ Ψ₂) e₂E d₂ f₂ , w₂) refl e₁ag e₂IH dγ =
  bind2-agree
    (SD.⟦ e₁E ⟧ˢ fmt E₁) (SD.⟦ realize-infer w₁ ⟧ˢ fmt E₁)
    (λ v1 → SD.⟦ e₂E ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} One E₂ v1))
    (λ v1 → SD.⟦ realize-infer w₂ ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} One E₂ v1))
    (e₁ag E₁)
    (λ v1 → e₂IH refl (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} One E₂ v1))

  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx}
           (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*One Ψ₁) (Surface.⊑ᵘ-+ʳ Ψ₂ (One Surface.*ᵘ Ψ₁))) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψ₂ (One Surface.*ᵘ Ψ₁)) dγ
agree-RLet2 {ctx = ctx} {A = A} {Ψ₁ = Ψ₁} e₁E d₁ f₁ w₁
            (success B (Many ∷ᵘ Ψ₂) e₂E d₂ f₂ , w₂) refl e₁ag e₂IH dγ =
  bind2-agree
    (SD.⟦ e₁E ⟧ˢ fmt E₁) (SD.⟦ realize-infer w₁ ⟧ˢ fmt E₁)
    (λ v1 → SD.⟦ e₂E ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} Many E₂ v1))
    (λ v1 → SD.⟦ realize-infer w₂ ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} Many E₂ v1))
    (e₁ag E₁)
    (λ v1 → e₂IH refl (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} Many E₂ v1))

  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx}
           (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ₁) (Surface.⊑ᵘ-+ʳ Ψ₂ (Many Surface.*ᵘ Ψ₁))) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψ₂ (Many Surface.*ᵘ Ψ₁)) dγ
agree-RLet2 e₁E d₁ f₁ w₁ (failure _ , _) () e₁ag e₂IH

agree-RLet : ∀ {ctx : NamedCtx} {x e₁ e₂ B} {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ B} {d f} {w : ctx ⊢ᵢ Raw.RLet x e₁ e₂ ∶ B ⨾ Ψ}
  (rE1 : VerifiedInferResult ctx e₁)
  → E.inferElabV-RLet-aux ctx x e₁ e₂ rE1 ≡ (success B Ψ se d f , w)
  → (∀ {A Ψ₁ e₁E d₁ f₁} {w₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁}
       → rE1 ≡ (success A Ψ₁ e₁E d₁ f₁ , w₁) → ∀ dγ → SD.⟦ e₁E ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ)
  → (∀ {A} → (rE2 : VerifiedInferResult (extendNamedCtx ctx x A) e₂)
       → E.inferElabV (extendNamedCtx ctx x A) e₂ ≡ rE2
       → ∀ {B' q Ψ₂' e₂E d₂' f₂'} {w₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B' ⨾ (q ∷ᵘ Ψ₂')}
         → rE2 ≡ (success B' (q ∷ᵘ Ψ₂') e₂E d₂' f₂' , w₂)
         → ∀ dγ' → SD.⟦ e₂E ⟧ˢ fmt dγ' ≡ SD.⟦ realize-infer w₂ ⟧ˢ fmt dγ')
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RLet {ctx} {x} {e₁} {e₂} (success A Ψ₁ e₁E d₁ f₁ , w₁) eq e₁IH e₂IH dγ =
  agree-RLet2 e₁E d₁ f₁ w₁ (E.inferElabV (extendNamedCtx ctx x A) e₂) eq
              (e₁IH refl) (λ p → e₂IH (E.inferElabV (extendNamedCtx ctx x A) e₂) refl p) dγ
agree-RLet (failure _ , _) () e₁IH e₂IH

-- THE MASQUERADE (Plan 0.50): at a `Many`-arrow, the elaborator's
-- `lift-morphism (IR.SigOp (ext-resolved-info cn π))` denotes the same as
-- `realize`'s `sigOp cn`. D225 collapsed it: the elaborator
-- (`ext-resolved-info-aux`) and the Spec (`arrow-info-eff`) now read the SAME
-- two decisions off the codomain — `isVoid?` then `isUnit?` — so the two infos
-- agree clause by clause, every clause `refl`. The former `lookupSigEffect`
-- split is gone with the side table; it was also where the two disagreed
-- (`true != false`: the table said HALTS, the Spec could not see it).
info-agree : ∀ {Dom Cod : Type} (cn : CanonicalName)
               (dV : Dec (Cod ≡ Void)) (dU : Dec (Cod ≡ Unit))
               (bDom : IsBaseType Dom) (cCod : IsConcrete Cod)
           → E.ext-resolved-info-aux cn eff dV dU bDom cCod ≡ arrow-info-eff cn dV dU bDom cCod
info-agree cn (yes refl) _          bDom cCod = refl
info-agree cn (no _)     (yes refl) bDom cCod = refl
info-agree cn (no _)     (no _)     bDom cCod = refl

masq : ∀ {ctx : NamedCtx} {Dom Cod : Type} (cn : CanonicalName) (π : Purity)
       (bDom : IsBaseType Dom) (cCod : IsConcrete Cod)
       (dγ : Env ctx Surface.zeroUsage)
     → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {A = Dom} {B = Cod} {π = π} (IR.SigOp (E.ext-resolved-info {Dom} {Cod} ctx cn π bDom cCod)) ⟧ˢ fmt dγ
      ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many π ] Cod} cn (con-fun bDom cCod) ⟧ˢ fmt dγ
masq {ctx} {Dom} {Cod} cn pure bDom cCod dγ = cong returnT (liftFn-SigOp {Dom} {Cod} (E.ext-resolved-info ctx cn pure bDom cCod) bDom)
masq {ctx} {Dom} {Cod} cn eff bDom cCod dγ =
  cong returnT
    (trans (cong (λ i → liftFn fmt {Dom} {Cod} (IR.SigOp i))
                 (info-agree {Dom} {Cod} cn (isVoid? Cod) (isUnit? Cod) bDom cCod))
           (liftFn-SigOp {Dom} {Cod} (arrow-info-eff cn (isVoid? Cod) (isUnit? Cod) bDom cCod) bDom))

-- The RQualified analogue of `masq`. `ext-arrow-info` decides its codomain via
-- `_≟T_` (NOT the `isVoid?`/`isUnit?` the Spec's `sigOp` uses), so the bridge
-- follows the elaborator's two decisions and forces the Spec's to match: each
-- `yes refl` fixes `Cod`, after which `isVoid?`/`isUnit?` compute; in the last
-- branch a Spec-side `yes` contradicts the elaborator's `no`.
masq-arrow : ∀ {ctx : NamedCtx} {Dom Cod : Type} (alias name : String) (π : Purity)
       (bDom : IsBaseType Dom) (cCod : IsConcrete Cod)
       (dγ : Env ctx Surface.zeroUsage)
     → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {A = Dom} {B = Cod} {π = π} (IR.SigOp (E.ext-arrow-info {Dom} {Cod} ctx alias name π bDom cCod)) ⟧ˢ fmt dγ
      ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many π ] Cod} (bare (alias ++ "." ++ name)) (con-fun bDom cCod) ⟧ˢ fmt dγ
masq-arrow {ctx} {Dom} {Cod} alias name pure bDom cCod dγ = cong returnT (liftFn-SigOp {Dom} {Cod} (E.ext-arrow-info ctx alias name pure bDom cCod) bDom)
masq-arrow {ctx} {Dom} {Cod} alias name eff bDom cCod dγ with Cod ≟T Void
... | yes refl = cong returnT (liftFn-SigOp {Dom} {Cod} (mk-info' (bare (alias ++ "." ++ name)) (haltsV refl) bDom (ffi-concrete cCod)) bDom)
... | no ¬v with Cod ≟T Unit
...   | yes refl = cong returnT (liftFn-SigOp {Dom} {Cod} (mk-info' (bare (alias ++ "." ++ name)) (emitsV refl) bDom (ffi-concrete cCod)) bDom)
...   | no ¬u with isVoid? Cod | isUnit? Cod
...     | yes refl | _        = ⊥-elim (¬v refl)
...     | no _     | yes refl = ⊥-elim (¬u refl)
...     | no _     | no _     = cong returnT (liftFn-SigOp {Dom} {Cod} (mk-info' (bare (alias ++ "." ++ name)) (pureV (generic-semM (alias ++ "." ++ name))) bDom (ffi-concrete cCod)) bDom)

-- RResolved agreement, dispatched on the import-lookup result exactly as the
-- elaborator's `inferElabV-RResolved-aux` does. A `Many`-arrow type resolves to
-- the effect-aware `lift-morphism (SigOp (ext-resolved-info …))` whose
-- agreement with realize's `sigOp cn` IS the `masq`-erade; every other type
-- resolves to `sigOp cn` directly (= realize) so agreement is `refl`. The type
-- shapes are ENUMERATED (not a catch-all): the aux's `just ty` clause sits
-- behind the `just (Many-arrow)` clause, so on an abstract type it would not
-- reduce — mirroring `Completeness`'s `go`. `nothing` ⇒ the aux fails, so the
-- success-eq is absurd.
-- `failure` and `success` are distinct constructors of `InferElabResult`, so a
-- proof identifying them is absurd (used to discharge the `nothing`-lookup case,
-- where the elaborator fails but the agreement obligation assumes success).
fail≢succ : ∀ {n} {Δ : Surface.Ctx n} {te} {A} {Ψ} {se : Surface.Expr Δ Ψ A} {d f}
          → _≡_ {A = E.InferElabResult Δ} (failure te) (success A Ψ se d f) → ⊥
fail≢succ ()

-- Plan 0.58 de-with drivers: pattern-match the concreteness decision GENUINELY
-- (as helper params), so the arrow/value aux commits to a `success`/`failure`
-- clause. The caller passes `(isBaseType? A) refl`/`(isConcrete? ty) refl`; the
-- application stays well-typed at the goal even when those are stuck.
agree-RResolved-arrowᴴ : ∀ (ctx : NamedCtx) (cn : CanonicalName) (ng : NotGenerator cn) {A B : Type} (π : Purity)
  (lkup : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just (A ⇒[ mk-kind Many π ] B))
  (mbA : Maybe (IsBaseType A)) (eqbA : isBaseType? A ≡ mbA)
  (mcB : Maybe (IsConcrete B)) (eqcB : isConcrete? B ≡ mcB)
  {A' Ψ se d f w}
  → E.inferElabV-RResolved-arrow-aux ctx cn ng lkup mbA eqbA mcB eqcB ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RResolved-arrowᴴ ctx cn ng {A} {B} π lkup (just bA) eqbA (just cB) eqcB refl dγ = masq {ctx} {A} {B} cn π bA cB dγ
agree-RResolved-arrowᴴ ctx cn ng π lkup nothing eqbA _ eqcB eqS dγ = ⊥-elim (fail≢succ (cong proj₁ eqS))
agree-RResolved-arrowᴴ ctx cn ng π lkup (just _) eqbA nothing eqcB eqS dγ = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RResolved-valueᴴ : ∀ (ctx : NamedCtx) (cn : CanonicalName) (ng : NotGenerator cn) (ty : Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just ty)
  (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
  {A' Ψ se d f w}
  → E.inferElabV-RResolved-value-aux ctx cn ng ty lkup mc eqc ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RResolved-valueᴴ ctx cn ng ty lkup (just conc) eqc refl dγ = refl
agree-RResolved-valueᴴ ctx cn ng ty lkup nothing eqc eqS dγ = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RResolved : ∀ (ctx : NamedCtx) (cn : CanonicalName) (ng : NotGenerator cn) (lhs : Maybe Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ lhs)
  {A Ψ se d f w}
  → E.inferElabV-RResolved-aux ctx cn ng lhs lkup ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RResolved ctx cn ng (just (A ⇒[ mk-kind Many π ] B)) lkup eqS dγ =
  agree-RResolved-arrowᴴ ctx cn ng π lkup (isBaseType? A) refl (isConcrete? B) refl eqS dγ
agree-RResolved ctx cn ng (just (A ⇒[ mk-kind One π ] B)) lkup eqS dγ =
  agree-RResolved-valueᴴ ctx cn ng (A ⇒[ mk-kind One π ] B) lkup (isConcrete? (A ⇒[ mk-kind One π ] B)) refl eqS dγ
agree-RResolved ctx cn ng (just (A ⇒[ mk-kind Zero π ] B)) lkup eqS dγ =
  agree-RResolved-valueᴴ ctx cn ng (A ⇒[ mk-kind Zero π ] B) lkup (isConcrete? (A ⇒[ mk-kind Zero π ] B)) refl eqS dγ
agree-RResolved ctx cn ng (just Unit) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng Unit lkup (isConcrete? Unit) refl eqS dγ
agree-RResolved ctx cn ng (just Void) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng Void lkup (isConcrete? Void) refl eqS dγ
agree-RResolved ctx cn ng (just Int) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng Int lkup (isConcrete? Int) refl eqS dγ
agree-RResolved ctx cn ng (just Float) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng Float lkup (isConcrete? Float) refl eqS dγ
agree-RResolved ctx cn ng (just Str) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng Str lkup (isConcrete? Str) refl eqS dγ
agree-RResolved ctx cn ng (just Buffer) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng Buffer lkup (isConcrete? Buffer) refl eqS dγ
agree-RResolved ctx cn ng (just (A * B)) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng (A * B) lkup (isConcrete? (A * B)) refl eqS dγ
agree-RResolved ctx cn ng (just (A + B)) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng (A + B) lkup (isConcrete? (A + B)) refl eqS dγ
agree-RResolved ctx cn ng (just (μ-type F)) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng (μ-type F) lkup (isConcrete? (μ-type F)) refl eqS dγ
agree-RResolved ctx cn ng (just (ν-type F)) lkup eqS dγ = agree-RResolved-valueᴴ ctx cn ng (ν-type F) lkup (isConcrete? (ν-type F)) refl eqS dγ
agree-RResolved ctx cn ng nothing lkup eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))

-- D136: the elaborator dispatches `RResolved` on `classifyGen cn` first, so
-- agreement has to name the VIEW to reduce. Seven generators fail infer (the
-- success equation is absurd), `unit` infers the literal, and only `gv-other`
-- reaches the import lookup — carrying the witness the aux now takes.
agree-RResolved-view : ∀ (ctx : NamedCtx) (cn : CanonicalName) (gv : GenView cn)
  {A Ψ se d f w}
  → E.inferElabV-RResolved-dispatch ctx cn gv ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RResolved-view ctx cn gv-unit refl dγ = refl
agree-RResolved-view ctx cn gv-id eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RResolved-view ctx cn gv-fst eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RResolved-view ctx cn gv-snd eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RResolved-view ctx cn gv-terminal eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RResolved-view ctx cn gv-initial eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RResolved-view ctx cn gv-inl eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RResolved-view ctx cn gv-inr eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RResolved-view ctx cn (gv-other ng) eq dγ =
  agree-RResolved ctx cn ng (lookupImport (NamedCtx.imports ctx) (showCanonical cn)) refl eq dγ

-- RVar (non-unit): cases the lookup-aux. Local → the bound SExpr IS realize's
-- `eE`; import → both elaborator and `realize-infer` emit `sigOp (bare x)`;
-- neither-found → the success equation is absurd. No `masq` (unlike RResolved,
-- whose aux emits a `lift-morphism` for arrows).
-- D136: the aux also de-withes the RESERVED-WORD decision, so this cases on it
-- too. A reserved word in the import table is unreachable bare, so that arm
-- FAILS and its success equation is absurd.
agree-RVar-importᴴ : ∀ (ctx : NamedCtx) (x : String)
  (eq-loc : lookupLocal ctx x ≡ nothing) (ty : Type)
  (eq-imp : lookupImport (NamedCtx.imports ctx) x ≡ just ty)
  (gw : Dec (GenWord x)) (eqg : genWord? x ≡ gw)
  (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
  {A' Ψ se d f w}
  → E.inferElabV-RVar-import-value-aux ctx x eq-loc ty eq-imp gw eqg mc eqc ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RVar-importᴴ ctx x eq-loc ty eq-imp (no _) eqg (just conc) eqc refl dγ = refl
agree-RVar-importᴴ ctx x eq-loc ty eq-imp (no _) eqg nothing eqc eqS dγ =
  ⊥-elim (fail≢succ (cong proj₁ eqS))
agree-RVar-importᴴ ctx x eq-loc ty eq-imp (yes _) eqg _ eqc eqS dγ =
  ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RVar : ∀ (ctx : NamedCtx) (x : String)
  (locLhs : Maybe (∃[ A ] ∃[ Ψ ] (Surface.SVar (NamedCtx.debruijn ctx) Ψ A)))
  (eq-loc : lookupLocal ctx x ≡ locLhs)
  (impLhs : Maybe Type) (eq-imp : lookupImport (NamedCtx.imports ctx) x ≡ impLhs)
  {A Ψ se d f w}
  → E.inferElabV-RVar-lookup-aux ctx x locLhs eq-loc impLhs eq-imp ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RVar ctx x (just (A , Ψ , se)) eq-loc impLhs eq-imp refl dγ = refl
agree-RVar ctx x nothing eq-loc (just ty) eq-imp eqS dγ =
  agree-RVar-importᴴ ctx x eq-loc ty eq-imp (genWord? x) refl (isConcrete? ty) refl eqS dγ
-- Plan 0.58 / D071: both lookups failed → the POLY FALLBACK (a ground
-- telescope name infers at its declared type). Its success rides the
-- premise-erased witness, so agreement is the narrow infer-poly residual.
agree-RVar ctx x nothing eq-loc nothing eq-imp eq dγ =
  infer-agreeV-RVar-poly-todo ctx x eq dγ

-- RQualified agreement, dispatched on the import-lookup of the dotted path,
-- exactly as `inferElabV-RQualified-aux` does. A `Many`-arrow resolves to the
-- effect-aware `lift-morphism (SigOp (ext-arrow-info …))` whose agreement with
-- realize's `sigOp (bare (alias.name))` is `masq-arrow`; every other type
-- resolves to that same `sigOp` directly (= realize) so agreement is `refl`.
-- `nothing` ⇒ the aux fails, so the success-eq is absurd.
agree-RQualified-arrowᴴ : ∀ (ctx : NamedCtx) (name alias : String) {A B : Type} (π : Purity)
  (lkup : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just (A ⇒[ mk-kind Many π ] B))
  (mbA : Maybe (IsBaseType A)) (eqbA : isBaseType? A ≡ mbA)
  (mcB : Maybe (IsConcrete B)) (eqcB : isConcrete? B ≡ mcB)
  {A' Ψ se d f w}
  → E.inferElabV-RQualified-arrow-aux ctx name alias lkup mbA eqbA mcB eqcB ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RQualified-arrowᴴ ctx name alias {A} {B} π lkup (just bA) eqbA (just cB) eqcB refl dγ = masq-arrow {ctx} {A} {B} alias name π bA cB dγ
agree-RQualified-arrowᴴ ctx name alias π lkup nothing eqbA _ eqcB eqS dγ = ⊥-elim (fail≢succ (cong proj₁ eqS))
agree-RQualified-arrowᴴ ctx name alias π lkup (just _) eqbA nothing eqcB eqS dγ = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RQualified-valueᴴ : ∀ (ctx : NamedCtx) (name alias : String) (ty : Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just ty)
  (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
  {A' Ψ se d f w}
  → E.inferElabV-RQualified-value-aux ctx name alias ty lkup mc eqc ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RQualified-valueᴴ ctx name alias ty lkup (just conc) eqc refl dγ = refl
agree-RQualified-valueᴴ ctx name alias ty lkup nothing eqc eqS dγ = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RQualified : ∀ (ctx : NamedCtx) (name alias : String) (lhs : Maybe Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs)
  {A Ψ se d f w}
  → E.inferElabV-RQualified-aux ctx name alias lhs lkup ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RQualified ctx name alias (just (A ⇒[ mk-kind Many π ] B)) lkup eqS dγ =
  agree-RQualified-arrowᴴ ctx name alias π lkup (isBaseType? A) refl (isConcrete? B) refl eqS dγ
agree-RQualified ctx name alias (just (A ⇒[ mk-kind One π ] B)) lkup eqS dγ =
  agree-RQualified-valueᴴ ctx name alias (A ⇒[ mk-kind One π ] B) lkup (isConcrete? (A ⇒[ mk-kind One π ] B)) refl eqS dγ
agree-RQualified ctx name alias (just (A ⇒[ mk-kind Zero π ] B)) lkup eqS dγ =
  agree-RQualified-valueᴴ ctx name alias (A ⇒[ mk-kind Zero π ] B) lkup (isConcrete? (A ⇒[ mk-kind Zero π ] B)) refl eqS dγ
agree-RQualified ctx name alias (just Unit) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias Unit lkup (isConcrete? Unit) refl eqS dγ
agree-RQualified ctx name alias (just Void) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias Void lkup (isConcrete? Void) refl eqS dγ
agree-RQualified ctx name alias (just Int) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias Int lkup (isConcrete? Int) refl eqS dγ
agree-RQualified ctx name alias (just Float) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias Float lkup (isConcrete? Float) refl eqS dγ
agree-RQualified ctx name alias (just Str) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias Str lkup (isConcrete? Str) refl eqS dγ
agree-RQualified ctx name alias (just Buffer) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias Buffer lkup (isConcrete? Buffer) refl eqS dγ
agree-RQualified ctx name alias (just (A * B)) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias (A * B) lkup (isConcrete? (A * B)) refl eqS dγ
agree-RQualified ctx name alias (just (A + B)) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias (A + B) lkup (isConcrete? (A + B)) refl eqS dγ
agree-RQualified ctx name alias (just (μ-type F)) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias (μ-type F) lkup (isConcrete? (μ-type F)) refl eqS dγ
agree-RQualified ctx name alias (just (ν-type F)) lkup eqS dγ = agree-RQualified-valueᴴ ctx name alias (ν-type F) lkup (isConcrete? (ν-type F)) refl eqS dγ
agree-RQualified ctx name alias nothing lkup eq dγ = ⊥-elim (fail≢succ (cong proj₁ eq))

-- D230: the spine's agreement — the application congruence, the head on its
-- domain-given IH and the argument on its inferred one.
agree-inferSpine : ∀ {ctx : NamedCtx} (f arg : RawExpr) (eqAH : E.classifyAppHead f ≡ nothing)
  (r : VerifiedInferResult ctx arg) {A Ψ se d fr} {w : ctx ⊢ᵢ Raw.RApp f arg ∶ A ⨾ Ψ}
  → E.inferSpine ctx f arg eqAH r ≡ (success A Ψ se d fr , w)
  → (rIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ arg ∶ T' ⨾ Ψ'}
       → r ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (fGivenIH : ∀ {A' π' B' Ψ' eE' d' fr'} {w' : ctx ⊢ᵈ f ∶ A' ⇒[ π' ]↦ B' ⨾ Ψ'}
       → E.elabGivenV ctx f A' π' ≡ (success B' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-inferSpine f arg eqAH (failure _ , _) () rIH fGivenIH
agree-inferSpine {ctx} f arg eqAH (success X Ψx xE dx frx , wX) eq rIH fGivenIH dγ
  with E.elabGivenV ctx f X pure in feq | eq
... | failure _ , _ | ()
... | success T Ψf fE df frf , wF | refl =
        app-agree {ctx = ctx} {A = X} {B = T} Many fE (realize-d wF) xE (realize-infer wX)
          (λ E → fGivenIH feq E) (λ E → rIH refl E) dγ

-- RApp agreement, dispatched on the app-head VIEW (a parameter of
-- `inferElabV-RApp-dispatch`, so we case it directly — no `with` on
-- `classifyAppHeadView`). 9 check-only/initial heads FAIL in infer mode, so the
-- success-eq is absurd. The 5 builtin-combinator heads emit `morph-app IR.X arg`
-- (unary `>>=T`, same morphism both sides ⇒ `rewrite` the arg IH) or `arr' arg`
-- (denotational identity ⇒ the arg IH directly); their `realize-infer (t-X-app)`
-- is the same shape over the witness. `ahv-apply` emits `morph-app apply argE`
-- (same morphism both sides ⇒ arg-IH congruence); `ahv-other` (generic
-- app/effApp; also needs the FUNCTION-position agreement) rides
-- `agree-RApp-other-aux` below.
-- ahv-other (infer) — the verified counterpart of `inferElabV-RApp-other-aux`.
-- The elaborator emits `app fE xE` (pure arrow) or `effApp fE xE` (Many-eff
-- arrow), and `realize-infer (t-app …) = app (realize-infer wF) (realize wX)`
-- (resp. `effApp …`) — the SAME shape — so the agreement is a plain
-- application congruence: the FUNCTION position rides `fInferIH` (f is inferred)
-- and the ARGUMENT position rides `argCheckIH` (the arg is CHECKED at f's
-- domain). The app denotation is a nested `_>>=T_`, closed by `bind2-agree`
-- (outer = fInferIH; inner = argCheckIH with a definitionally-equal
-- continuation ⇒ `refl`). effApp wraps the same body in `returnT (λ _ → …)`, so
-- it is the app proof under `extensionality`. Every non-arrow / eff-One/Zero f
-- makes the elaborator fail ⇒ success-eq absurd. The `lhs`/`eqAH` arguments
-- mirror `inferElabV-RApp-other-aux` exactly (so the dispatch reduces).
-- D229 / plan 0.94 §13: ex falso — the elaborator emits the principal alone,
-- and so does `realize`.
agree-app-void : ∀ {ctx : NamedCtx} (f x : RawExpr) (eqAH : E.classifyAppHead f ≡ nothing)
  {Ψ₁ : Usage (NamedCtx.size ctx)} {fE : Expr (NamedCtx.debruijn ctx) Ψ₁ Void} {df ff : ℕ}
  {wF : ctx ⊢ᵢ f ∶ Void ⨾ Ψ₁}
  (r : VerifiedInferResult ctx x) {A Ψ se d fr} {w : ctx ⊢ᵢ Raw.RApp f x ∶ A ⨾ Ψ}
  → E.inferElabV-RApp-void ctx f x eqAH fE df ff wF r ≡ (success A Ψ se d fr , w)
  → (∀ dγ → SD.⟦ fE ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer wF ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-app-void f x eqAH (failure _ , _) () h
agree-app-void f x eqAH (success _ _ _ _ _ , _) refl h dγ = h dγ

agree-RApp-other-aux : ∀ {ctx : NamedCtx} (f arg : RawExpr) {A Ψ se d fr w}
  (lhs : Maybe E.PolyBuiltinApp) (eqAH : E.classifyAppHead f ≡ lhs)
  → E.inferElabV-RApp-other-aux ctx f arg lhs eqAH ≡ (success A Ψ se d fr , w)
  → (fInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ f ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx f ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → (argInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ arg ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx arg ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (fGivenIH : ∀ {A' π' B' Ψ' eE' d' fr'} {w' : ctx ⊢ᵈ f ∶ A' ⇒[ π' ]↦ B' ⨾ Ψ'}
       → E.elabGivenV ctx f A' π' ≡ (success B' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RApp-other-aux f arg (just _) eqAH () fInferIH argCheckIH argInferIH fGivenIH
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH argInferIH fGivenIH dγ
  with E.inferElabV ctx f | eq
-- D230: the head does not synthesize — the spine.
... | failure _ , _ | eq₁ = agree-inferSpine f arg eqAH (E.inferElabV ctx arg) eq₁ argInferIH fGivenIH dγ
... | success Unit _ _ _ _ , _ | ()
... | success Void Ψ₁ fE df ff , wF | eq₁ = agree-app-void f arg eqAH (E.inferElabV ctx arg) eq₁ (λ E → fInferIH refl E) dγ
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ * _) _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
... | success (A ⇒[ mk-kind q pure ] B) Ψ₁ fE df ff , wF | eq₁
      with E.checkElabV ctx arg A in xeq | eq₁
... | failure _ , _ | ()
... | success Ψ₂ xE dx fx , wX | refl =
        app-agree {ctx = ctx} {A = A} {B = B} q fE (realize-infer wF) xE (realize wX)
          (λ E → fInferIH refl E) (λ E → argCheckIH xeq E) dγ
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH argInferIH fGivenIH dγ
  | success (A ⇒[ mk-kind Many eff ] B) Ψ₁ fE df ff , wF | eq₁
      with E.checkElabV ctx arg A in xeq | eq₁
... | failure _ , _ | ()
... | success Ψ₂ xE dx fx , wX | refl =
        cong returnT
          (extensionality (λ _ →
            bind2-agree (SD.⟦ fE ⟧ˢ fmt Ef) (SD.⟦ realize-infer wF ⟧ˢ fmt Ef)
              (λ vf → SD.⟦ xE ⟧ˢ fmt Ex >>=T λ vx → vf vx)
              (λ vf → SD.⟦ realize wX ⟧ˢ fmt Ex >>=T λ vx → vf vx)
              (fInferIH refl Ef)
              (λ vf → bind2-agree (SD.⟦ xE ⟧ˢ fmt Ex) (SD.⟦ realize wX ⟧ˢ fmt Ex)
                          (λ vx → vf vx) (λ vx → vf vx)
                          (argCheckIH xeq Ex) (λ _ → refl))))
  where
    Ef = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ
    Ex = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH argInferIH fGivenIH dγ
  | success (A ⇒[ mk-kind One eff ] B) _ _ _ _ , _ | ()
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH argInferIH fGivenIH dγ
  | success (A ⇒[ mk-kind Zero eff ] B) _ _ _ _ , _ | ()

-- D194: the `Out` analogue of `agree-checkCataGo` — the decision argument is
-- explicit so the caller never has to abstract it.
agree-inferOutGo : ∀ (ctx : NamedCtx) (arg : RawExpr) (F : Functor)
    (Ψ : Usage (NamedCtx.size ctx))
    (argE : Expr (NamedCtx.debruijn ctx) Ψ (ν-type F)) (d fr : ℕ)
    (w : ctx ⊢ᵢ arg ∶ ν-type F ⨾ Ψ)
    (mw : Maybe (WellFormedF F)) (eqW : wellFormedF? F ≡ mw)
    {A : Type} {Ψ' : Usage (NamedCtx.size ctx)}
    {se : Expr (NamedCtx.debruijn ctx) Ψ' A} {d' fr' : ℕ}
    {w' : ctx ⊢ᵢ Raw.RApp (Raw.RResolved (gen "Out")) arg ∶ A ⨾ Ψ'}
  → E.inferOutGo ctx arg F Ψ argE d fr w mw eqW ≡ (success A Ψ' se d' fr' , w')
  -- the ARGUMENT'S AGREEMENT, already applied. Not the general IH: inside the
  -- caller's `with` the scrutinee is abstracted, so the general IH's type no
  -- longer mentions `E.inferElabV ctx arg` and cannot be passed along. The
  -- applied form has no such dependency.
  → (argAgree : ∀ dγ' → SD.⟦ argE ⟧ˢ fmt dγ' ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ')
  → ∀ (dγ : Env ctx Ψ') → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ

agree-RApp : ∀ (ctx : NamedCtx) (f arg : RawExpr) {A Ψ se d fr w}
  (vw : E.AppHeadView f) (veq : E.classifyAppHeadView f ≡ vw)
  → E.inferElabV-RApp-dispatch ctx f arg vw veq ≡ (success A Ψ se d fr , w)
  → (argIH : ∀ {A' Ψ' argE d' fr'} {w' : ctx ⊢ᵢ arg ∶ A' ⨾ Ψ'}
       → E.inferElabV ctx arg ≡ (success A' Ψ' argE d' fr' , w')
       → ∀ dγ → SD.⟦ argE ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  -- function-position + checked-arg IHs (only `ahv-other` consumes them).
  → (fInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ f ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx f ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  -- D230: the head's domain-given IH (only `ahv-other`'s spine consumes it).
  → (fGivenIH : ∀ {A' π' B' Ψ' eE' d' fr'} {w' : ctx ⊢ᵈ f ∶ A' ⇒[ π' ]↦ B' ⨾ Ψ'}
       → E.elabGivenV ctx f A' π' ≡ (success B' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
-- check-only / infer-failing heads: the dispatch is `failure`, so success-eq absurd.
agree-RApp ctx f arg E.ahv-inl veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-inr veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-initial veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-pair-applied veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-compose-applied veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-case-applied veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-In veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-cata veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-curry veq eq argIH fInferIH argCheckIH fGivenIH dγ = ⊥-elim (fail≢succ (cong proj₁ eq))
-- ahv-id : any-typed arg, result morph-app id.
agree-RApp ctx f arg E.ahv-id veq eq argIH fInferIH argCheckIH fGivenIH dγ with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success T Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
-- ahv-terminal : any-typed arg, result morph-app terminal.
agree-RApp ctx f arg E.ahv-terminal veq eq argIH fInferIH argCheckIH fGivenIH dγ with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success T Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
-- D194: ahv-Out. The `wellFormedF?` decision cannot be `with`-abstracted here
-- — it sits under the `refl` the argument's own `with` produced — so it goes
-- to a helper that takes it explicitly, exactly as `agree-checkCataGo` does.
agree-RApp ctx f arg E.ahv-Out veq eq argIH fInferIH argCheckIH fGivenIH dγ
  with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (ν-type F) Ψ argE d fr , w | eq₁ =
      agree-inferOutGo ctx arg F Ψ argE d fr w (wellFormedF? F) refl eq₁
        (λ dγ' → argIH refl dγ') dγ
... | success Void Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl

-- ahv-fst : arg must be a product; other shapes fail.
agree-RApp ctx f arg E.ahv-fst veq eq argIH fInferIH argCheckIH fGivenIH dγ with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (A * B) Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
... | success Unit _ _ _ _ , _ | ()
... | success Void Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
-- ahv-snd : arg must be a product; other shapes fail.
agree-RApp ctx f arg E.ahv-snd veq eq argIH fInferIH argCheckIH fGivenIH dγ with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (A * B) Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
... | success Unit _ _ _ _ , _ | ()
... | success Void Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
-- (Plan 0.52 M1: `ahv-arr` agree clause retired with the surface `arr` builtin.)
-- ahv-apply / ahv-other : genuine semantic content (deferred).
-- ahv-apply: arg must infer to `(A ⇒[Many,pure] B) * A`; se = `morph-app apply argE`
-- (elaborator emits the apply MORPHISM directly — no specApply lambda / weakening),
-- witness `t-apply-app-infer w`, realize = `morph-app apply (realize-infer w)` ⇒ a
-- plain morph-app congruence (rewrite the arg IH). Every other arg-type fails ⇒ absurd.
agree-RApp ctx f arg E.ahv-apply veq eq argIH fInferIH argCheckIH fGivenIH dγ with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success Unit _ _ _ _ , _ | ()
... | success Void Ψ argE d fr , w | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
... | success (Unit * _) _ _ _ _ , _ | ()
... | success (Void * _) _ _ _ _ , _ | ()
... | success (Int * _) _ _ _ _ , _ | ()
... | success (Float * _) _ _ _ _ , _ | ()
... | success (Str * _) _ _ _ _ , _ | ()
... | success (Buffer * _) _ _ _ _ , _ | ()
... | success ((_ * _) * _) _ _ _ _ , _ | ()
... | success ((_ + _) * _) _ _ _ _ , _ | ()
... | success ((μ-type _) * _) _ _ _ _ , _ | ()
... | success ((ν-type _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind One pure ] _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind One eff ] _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind Zero pure ] _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind Zero eff ] _) * _) _ _ _ _ , _ | ()
... | success ((A ⇒[ mk-kind Many pure ] B) * A') Ψ argE d fr , w | eq₁ with A ≟T A' | eq₁
... | yes refl | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
... | no _ | ()
-- D222 / plan 0.95 A′: the EFF-closure row. This USED TO BE an absurd pattern
-- (`… (_ ⇒[ mk-kind Many eff ] _) * _ … | ()`), sound only because the
-- elaborator's `ahv-apply` dispatch FAILED at an effectful closure. It succeeds
-- now, so the row is live and needs the pure row's proof — which transfers
-- unchanged: both emit `morph-app <morphism> argE` and `realize-infer` emits the
-- same morphism, so agreement is the argument's IH and `refl`.
agree-RApp ctx f arg E.ahv-apply veq eq argIH fInferIH argCheckIH fGivenIH dγ
  | success ((A ⇒[ mk-kind Many eff ] B) * A') Ψ argE d fr , w | eq₁ with A ≟T A' | eq₁
... | yes refl | refl rewrite argIH refl (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                      (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
... | no _ | ()
-- ahv-other: the dispatch reduces to `inferElabV-RApp-other ctx f arg =
-- inferElabV-RApp-other-aux ctx f arg (classifyAppHead f) refl`, so `eq` already
-- has the aux's type; delegate (the IHs ride f-infer and arg-check).
agree-RApp ctx f arg E.ahv-other veq eq argIH fInferIH argCheckIH fGivenIH dγ =
  agree-RApp-other-aux f arg (E.classifyAppHead f) refl eq fInferIH argCheckIH argIH fGivenIH dγ

-- RAnnot infers by CHECKING `e` against the annotation `T₀`; witness is
-- `t-annot witness`, se is the check-elaborated `eE`, and
-- `realize-infer (t-annot witness) = realize witness`, so agreement IS the
-- supplied `check-agreeV ctx e T₀` IH. A check failure makes the eq absurd.
agree-RAnnot : ∀ {ctx : NamedCtx} {e : RawExpr} {T₀ : Type} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RAnnot e T₀ ∶ A ⨾ Ψ}
  (r : VerifiedCheckResult ctx e T₀)
  → E.inferElabV-RAnnot-aux ctx e T₀ r ≡ (success A Ψ se d f , w)
  → (∀ {Ψ' eE' d' fr' w'} → r ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RAnnot (success Ψ' eE' d' fr' , witness) refl IH dγ = IH refl dγ
agree-RAnnot (failure _ , _) () IH

------------------------------------------------------------------------
-- D127: `morph-realize` (`extract-morph-eff E ≡ realize-morph (extractMorphWitness
-- W)`) is DELETED, along with `checkG-realize`. Both existed to reconcile the
-- elaborator's IR with the reference elaboration's IR for a CLOSED arm. There is
-- no closed arm any more: the elaborator emits `Surface.comp'`/`copair'`/`fork'`/
-- `curry'`/`cata` and `realize` emits the SAME nodes over the SAME sub-witnesses,
-- so every combinator agreement is an ordinary congruence over its arms'
-- agreements — which is what makes them need an induction hypothesis where the
-- old proofs needed none.
--
-- `SubCheckIH ctx-free`: the arm IH, quantified over the CONTEXT as well as the
-- expression, because `cata`'s algebra is checked in the CLEARED context. Bounded
-- by `μ`, so the caller discharges it from its own `Acc`.
------------------------------------------------------------------------

SubCheckIH : ℕ → Set
SubCheckIH n = ∀ (ctx' : NamedCtx) (e' : RawExpr) → μ e' < n
  → ∀ {T' Ψ' eE' d' fr'} {w' : ctx' ⊢ᶜ e' ∶ T' ⨾ Ψ'}
  → E.checkElabV ctx' e' T' ≡ (success Ψ' eE' d' fr' , w')
  → ∀ (dγ : Env ctx' Ψ') → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ

SubInferIH : ℕ → Set
SubInferIH n = ∀ (ctx' : NamedCtx) (e' : RawExpr) → μ e' < n
  → ∀ {T' Ψ' eE' d' fr'} {w' : ctx' ⊢ᵢ e' ∶ T' ⨾ Ψ'}
  → E.inferElabV ctx' e' ≡ (success T' Ψ' eE' d' fr' , w')
  → ∀ (dγ : Env ctx' Ψ') → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ

-- Plan 0.94 §10: the domain-given twin.
SubGivenIH : ℕ → Set
SubGivenIH n = ∀ (ctx' : NamedCtx) (e' : RawExpr) → μ e' < n
  → ∀ {A' π' B' Ψ' eE' d' fr'} {w' : ctx' ⊢ᵈ e' ∶ A' ⇒[ π' ]↦ B' ⨾ Ψ'}
  → E.elabGivenV ctx' e' A' π' ≡ (success B' Ψ' eE' d' fr' , w')
  → ∀ (dγ : Env ctx' Ψ') → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w' ⟧ˢ fmt dγ

-- Plan 0.94 §10: the two compose routes. Both emit `comp'` over the arms, and
-- `realize` builds the SAME node over the same sub-witnesses, so each route is
-- the arms' agreements under one congruence. The `f`-route's arm carries its
-- conversion on both sides (`coerce p`), so its agreement is the infer IH mapped.
agree-checkCompose-f : ∀ (ctx : NamedCtx) (f g : RawExpr) (A C : Type) (π : Purity)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ (A ⇒[ mk-kind Many π ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RResolved (gen "compose")) f) g ∶ (A ⇒[ mk-kind Many π ] C) ⨾ Ψ}
  → E.checkCompose-f ctx f g A C π ≡ (success Ψ se d fr , w)
  → (fIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ f ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx f ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (gIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ g ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx g T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-checkCompose-f ctx f g A C π disp fIH gIH dγ
  with E.inferElabV ctx f in eqf | disp
... | failure _ , _ | ()
... | success Unit _ _ _ _ , _ | ()
... | success Void _ _ _ _ , _ | ()
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ * _) _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
... | success (_ ⇒[ mk-kind Zero _ ] _) _ _ _ _ , _ | ()
... | success (_ ⇒[ mk-kind One _ ] _) _ _ _ _ , _ | ()
... | success (B ⇒[ mk-kind Many π′ ] C′) Ψf fE df frf , wF | d₁
      with (B ⇒[ mk-kind Many π′ ] C′) <:? (B ⇒[ mk-kind Many π ] C) | d₁
...   | no _ | ()
...   | yes p | d₂ with E.checkElabV ctx g (A ⇒[ mk-kind Many π ] B) in eqg | d₂
...     | failure _ , _ | ()
...     | success Ψg gE dg frg , wG | refl =
          binop-agree (SD.⟦ Surface.coerce p fE ⟧ˢ fmt E₁) (SD.⟦ Surface.coerce p (realize-infer wF) ⟧ˢ fmt E₁)
                      (SD.⟦ gE ⟧ˢ fmt E₂) (SD.⟦ realize wG ⟧ˢ fmt E₂)
                      (λ vf vg → returnT (λ a → vg a >>=T vf))
                      (cong (fmapT ⟦ p ⟧<:) (fIH refl E₁)) (gIH eqg E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψf Ψg) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψf Ψg) dγ

agree-checkCompose-g : ∀ (ctx : NamedCtx) (f g : RawExpr) (A C : Type) (π : Purity)
  (rG : E.VerifiedGivenResult ctx g A π)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ (A ⇒[ mk-kind Many π ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RResolved (gen "compose")) f) g ∶ (A ⇒[ mk-kind Many π ] C) ⨾ Ψ}
  → E.checkCompose-g ctx f g A C π rG ≡ (success Ψ se d fr , w)
  → (rGIH : ∀ {B' Ψ' eE' d' fr'} {w' : ctx ⊢ᵈ g ∶ A ⇒[ π ]↦ B' ⨾ Ψ'}
       → rG ≡ (success B' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w' ⟧ˢ fmt dγ)
  → (fCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ f ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx f T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → (fInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ f ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx f ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (gCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ g ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx g T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-checkCompose-g ctx f g A C π (failure _ , _) disp rGIH fCheckIH fInferIH gCheckIH dγ =
  agree-checkCompose-f ctx f g A C π disp fInferIH gCheckIH dγ
agree-checkCompose-g ctx f g A C π (success B Ψg gE dg frg , wG) disp rGIH fCheckIH fInferIH gCheckIH dγ
  with E.checkElabV ctx f (B ⇒[ mk-kind Many π ] C) in eqf | disp
... | failure _ , _ | disp' = agree-checkCompose-f ctx f g A C π disp' fInferIH gCheckIH dγ
... | success Ψf fE df frf , wF | refl =
        binop-agree (SD.⟦ fE ⟧ˢ fmt E₁) (SD.⟦ realize wF ⟧ˢ fmt E₁)
                    (SD.⟦ gE ⟧ˢ fmt E₂) (SD.⟦ realize-d wG ⟧ˢ fmt E₂)
                    (λ vf vg → returnT (λ a → vg a >>=T vf)) (fCheckIH eqf E₁) (rGIH refl E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψf Ψg) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψf Ψg) dγ

-- Plan 0.52 (pure⊑eff): the `case` analogue of `agree-compose`, reasoning over
-- `checkCaseGo` (grade-poly, no clause-split) so it is immune to the eff-clause.
-- D127: `copair'` on both sides — the same congruence as compose.
agree-caseGo : ∀ (ctx : NamedCtx) (f_inner arg : RawExpr) (A B C : Type) (π : Purity)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ ((A + B) ⇒[ mk-kind Many π ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RResolved (gen "case")) f_inner) arg ∶ ((A + B) ⇒[ mk-kind Many π ] C) ⨾ Ψ}
  → E.checkCaseGo ctx f_inner arg A B C π ≡ (success Ψ se d fr , w)
  → (fIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ f_inner ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx f_inner T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → (gIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-caseGo ctx f_inner arg A B C π disp fIH gIH dγ
  with E.checkElabV ctx f_inner (A ⇒[ mk-kind Many π ] C) in eqf | disp
... | failure _ , _ | ()
... | success Ψf fE df frf , wF | disp'
      with E.checkElabV ctx arg (B ⇒[ mk-kind Many π ] C) in eqg | disp'
... | failure _ , _ | ()
... | success Ψg gE dg frg , wG | refl =
        binop-agree (SD.⟦ fE ⟧ˢ fmt E₁) (SD.⟦ realize wF ⟧ˢ fmt E₁)
                    (SD.⟦ gE ⟧ˢ fmt E₂) (SD.⟦ realize wG ⟧ˢ fmt E₂)
                    (λ vf vg → returnT (λ ab → [ vf , vg ]′ ab)) (fIH eqf E₁) (gIH eqg E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψf Ψg) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψf Ψg) dγ

-- eff-clause agreement for case. D226: the elaborator's pure fallback is gone —
-- `checkCase` at an eff arrow IS the eff `Go` — so the dispatch equation passes
-- straight to the grade-generic agreement.
agree-caseGo-eff : ∀ (ctx : NamedCtx) (f_inner arg : RawExpr) (A B C : Type)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ ((A + B) ⇒[ mk-kind Many eff ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RResolved (gen "case")) f_inner) arg ∶ ((A + B) ⇒[ mk-kind Many eff ] C) ⨾ Ψ}
  → E.checkCase ctx (Raw.RApp (Raw.RResolved (gen "case")) f_inner) arg ((A + B) ⇒[ mk-kind Many eff ] C)
      ≡ (success Ψ se d fr , w)
  → (fIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ f_inner ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx f_inner T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → (gIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-caseGo-eff ctx f_inner arg A B C disp fIH gIH dγ =
  agree-caseGo ctx f_inner arg A B C eff disp fIH gIH dγ

-- The agreement for the WHOLE `embedOrSubsume` combinator (every infer-then-check
-- site = `embedOrSubsume ctx e T (inferElabV ctx e)`). On `T' <:? T` = yes the
-- agreement is the infer IH under the conversion; otherwise the success-eq is
-- absurd. One lemma → every catch-all
-- check-agree clause is a one-liner, with NO proof-side `with T ≟T T'` alignment.
-- PLAN 0.73 F3: the infer result is a PARAMETER, `rInf`, not fixed to
-- `E.inferElabV ctx e`.
--
-- The neg dispatch is why. A proof that has with-abstracted `negOperandView e`
-- can no longer reduce `inferElabV ctx (RUnaryOp OpNeg e)` — that unfolds back
-- into the view, which is stuck under the abstraction — but it CAN name the
-- form the view already reduced to. `agree-RUnaryOp` was stated this way from
-- the start, over `inferElabV-RUnaryOp-aux ctx e rE`; this brings the
-- check-mode lemma into line so both can be used in the same branch.
--
-- Matching `rInf` directly rather than `with`-ing it is what keeps the two
-- ends definitionally connected at the call site.
agree-embedOrSubsume-at : ∀ {ctx : NamedCtx} {e : RawExpr} (T : Type)
    (rInf : VerifiedInferResult ctx e)
    {Ψ se d f} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ}
  → E.embedOrSubsume ctx e T rInf ≡ (success Ψ se d f , w)
  → (inferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ e ∶ T' ⨾ Ψ'}
       → rInf ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-embedOrSubsume-at T (failure _ , _) () inferIH
-- D226: ONE decision, `T' <:? T`. On `yes p` the elaborator emits `coerce p eE'`
-- and `realize (t-sub wᵢ p)` is `coerce p (realize-infer wᵢ)`: both map their
-- result along the same `⟦ p ⟧<:`, so agreement is the infer IH under `fmapT`.
agree-embedOrSubsume-at T (success T' Ψ' eE' d' fr' , wᵢ) eq inferIH dγ
  with T' <:? T | eq
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _  | ()

agree-embedOrSubsume : ∀ {ctx : NamedCtx} {e : RawExpr} (T : Type)
    {Ψ se d f} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ}
  → E.embedOrSubsume ctx e T (E.inferElabV ctx e) ≡ (success Ψ se d f , w)
  → (inferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ e ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx e ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-embedOrSubsume {ctx = ctx} {e = e} T eq inferIH dγ =
  agree-embedOrSubsume-at T (E.inferElabV ctx e) eq inferIH dγ

-- D136: CHECK-mode `RResolved` dispatches on `classifyGen cn`, so agreement
-- names the view. The seven point-free generators land in their own
-- `bbc-*-aux` (their infer FAILS, which is exactly the shape those lemmas are
-- stated at); `unit` and every other canonical name go through the ordinary
-- embed/subsume route.
check-agree-RResolved-view : ∀ (ctx : NamedCtx) (cn : CanonicalName) (T : Type)
    (gv : GenView cn) {Ψ se d f} {w : ctx ⊢ᶜ Raw.RResolved cn ∶ T ⨾ Ψ}
  → E.checkElabV-RResolved-dispatch ctx cn T gv (E.inferElabV ctx (Raw.RResolved cn))
      ≡ (success Ψ se d f , w)
  → (inferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ Raw.RResolved cn ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx (Raw.RResolved cn) ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
check-agree-RResolved-view ctx cn T gv-id eq IH dγ = check-agreeV-RVar-id ctx T eq dγ
check-agree-RResolved-view ctx cn T gv-fst eq IH dγ = check-agreeV-RVar-fst ctx T eq dγ
check-agree-RResolved-view ctx cn T gv-snd eq IH dγ = check-agreeV-RVar-snd ctx T eq dγ
check-agree-RResolved-view ctx cn T gv-terminal eq IH dγ = check-agreeV-RVar-terminal ctx T eq dγ
check-agree-RResolved-view ctx cn T gv-initial eq IH dγ = check-agreeV-RVar-initial ctx T eq dγ
check-agree-RResolved-view ctx cn T gv-inl eq IH dγ = check-agreeV-RVar-inl ctx T eq dγ
check-agree-RResolved-view ctx cn T gv-inr eq IH dγ = check-agreeV-RVar-inr ctx T eq dγ
check-agree-RResolved-view ctx cn T gv-unit eq IH dγ = agree-embedOrSubsume T eq IH dγ
check-agree-RResolved-view ctx cn T (gv-other _) eq IH dγ = agree-embedOrSubsume T eq IH dγ

------------------------------------------------------------------------
-- D127/D131: the cata denotational bridge is GONE.
--
-- `faithful-aux`, `extract-morph-eff-denotes`, `agree-cata-denotes` and
-- `algebra-morph-recover` all existed to show that the elaborator's
-- `Surface.cata wfF algE` denotes the same as `realize`'s
-- `lift-morphism (IR.Cata wfF (realize-morph mᵐ))` — two DIFFERENT nodes, one
-- carrying a surface algebra and the other an extracted IR algebra, reconciled
-- through `cata-fold-eq`. Under D131 `realize` emits `cata wfF (realize dalg)`:
-- the same node over the same algebra. The bridge has nothing left to bridge,
-- and the cata agreement is the algebra's agreement (`agree-checkCataGo`).
------------------------------------------------------------------------

-- Plan 0.55 D#2: bare-`μF` `In` agreement over `checkInGo` (`mw`/`eqW` explicit to
-- dodge the `wellFormedF? F` dependent-`with`, as for cata). Emits `morph-app (In
-- wfF Heap) argE`; `realize (t-In-app-check _ wArg) = morph-app (In wfF Heap)
-- (realize wArg)` — SAME morph-app congruence as `ahv-initial` (rewrite arg IH).
agree-checkInGo : ∀ (ctx : NamedCtx) (arg : RawExpr) (F : Functor)
    (mw : Maybe (WellFormedF F)) (eqW : wellFormedF? F ≡ mw)
    {Ψ : Usage (NamedCtx.size ctx)}
    {se : Expr (NamedCtx.debruijn ctx) Ψ (μ-type F)}
    {d fr : ℕ}
    {w : ctx ⊢ᶜ Raw.RApp (Raw.RResolved (gen "In")) arg ∶ μ-type F ⨾ Ψ}
  → E.checkInGo ctx arg F mw eqW ≡ (success Ψ se d fr , w)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-checkInGo ctx arg F nothing eqW ()
agree-checkInGo ctx arg F (just wfF) eqW disp argCheckIH dγ
  with E.checkElabV ctx arg (⟦ F ⟧T (μ-type F)) in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , wArg | refl rewrite argCheckIH aeq (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                     (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl

-- Plan 0.55 D#2: the cata agreement over `checkCataGo` (mirrors `agree-caseGo` /
-- `agree-compose`). `mw`/`eqW` are EXPLICIT so `checkCataGo` reduces on `just wfF`
-- WITHOUT the `wellFormedF? F` dependent-`with` hazard (the same device as
-- `checkCataGoV-pure-J`).
--
-- D127/D131: one rewrite. Both sides are `Surface.cata wfF <algebra>`, and
-- `⟦ cata wf alg ⟧ˢ dγ = ⟦ alg ⟧ˢ tt >>=T …` runs the algebra at the EMPTY
-- environment, so the IH is applied at `tt`. The algebra is checked in the
-- CLEARED context, which is why the IH is context-quantified (`SubCheckIH`).
agree-checkCataGo : ∀ (ctx : NamedCtx) (alg : RawExpr) (F : Functor) (A : Type) (π : Purity)
    (mw : Maybe (WellFormedF F)) (eqW : wellFormedF? F ≡ mw)
    {Ψ : Usage (NamedCtx.size ctx)}
    {se : Expr (NamedCtx.debruijn ctx) Ψ (μ-type F ⇒[ mk-kind Many π ] A)}
    {d fr : ℕ}
    {w : ctx ⊢ᶜ Raw.RApp (Raw.RResolved (gen "cata")) alg ∶ (μ-type F ⇒[ mk-kind Many π ] A) ⨾ Ψ}
  → E.checkCataGo ctx alg F A π mw eqW ≡ (success Ψ se d fr , w)
  → (algIH : ∀ {T' Ψ' eE' d' fr'}
       {w' : ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx) ⊢ᶜ alg ∶ T' ⨾ Ψ'}
       → E.checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg T'
           ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-checkCataGo ctx alg F A π nothing eqW () algIH
agree-checkCataGo ctx alg F A π (just wfF) eqW disp algIH dγ
  with E.checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
                    alg (⟦ F ⟧T A ⇒[ mk-kind Many π ] A) in eqAlg | disp
... | failure _ , _ | ()
... | success Surface.[] algE dA frA , wArg | refl
      rewrite algIH eqAlg tt = refl

-- D192: the ana mirror. ONE clause where the cata needs two, because
-- `checkAna` is grade-generic — there is no eff-then-pure fallback to follow.
agree-checkAnaGo : ∀ (ctx : NamedCtx) (coalg : RawExpr) (F : Functor) (A : Type) (π : Purity)
    (mw : Maybe (WellFormedF F)) (eqW : wellFormedF? F ≡ mw)
    {Ψ : Usage (NamedCtx.size ctx)}
    {se : Expr (NamedCtx.debruijn ctx) Ψ (A ⇒[ mk-kind Many π ] ν-type F)}
    {d fr : ℕ}
    {w : ctx ⊢ᶜ Raw.RApp (Raw.RResolved (gen "ana")) coalg ∶ (A ⇒[ mk-kind Many π ] ν-type F) ⨾ Ψ}
  → E.checkAnaGo ctx coalg F A π mw eqW ≡ (success Ψ se d fr , w)
  → (coalgIH : ∀ {T' Ψ' eE' d' fr'}
       {w' : ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx) ⊢ᶜ coalg ∶ T' ⨾ Ψ'}
       → E.checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) coalg T'
           ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-checkAnaGo ctx coalg F A π nothing eqW () coalgIH
agree-checkAnaGo ctx coalg F A π (just wfF) eqW disp coalgIH dγ
  with E.checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
                    coalg (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A) in eqCoalg | disp
... | failure _ , _ | ()
-- `⟦ ana ⟧ˢ` binds the coalgebra INSIDE the suspension's lambda —
-- deliberately, because that is what `evalᴰ (Ana …)` does and what
-- `FaithfulLemmas` relates it to. plan 0.98: the agreement is ONE equation of
-- computations, so the coalgebra IH is congruence'd in directly; the funext
-- over the budget it used to need is gone with the budget.
... | success Surface.[] coalgE dA frA , wArg | refl =
      cong (λ ac → (returnT (λ a → returnT (anaFᵈ F
              (λ a' → fmapT (coerce-functor-D F A) (ac >>=T λ clo → clo a')) a))))
           (coalgIH eqCoalg tt)

agree-inferOutGo ctx arg F Ψ argE d fr w nothing eqW ()
agree-inferOutGo ctx arg F Ψ argE d fr w (just wfF) eqW refl argAgree dγ
  rewrite argAgree (restrictᴰ {Γ = NamedCtx.debruijn ctx}
            (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
              (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl

agree-check-RApp : ∀ (ctx : NamedCtx) (f arg : RawExpr) (T : Type) {Ψ se d fr w}
  (vw : E.AppHeadView f) (veq : E.classifyAppHeadView f ≡ vw)
  → E.checkElabV-RApp-dispatch ctx f arg T vw veq ≡ (success Ψ se d fr , w)
  → (inferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ Raw.RApp f arg ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx (Raw.RApp f arg) ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize w' ⟧ˢ fmt dγ)
  → (argInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ arg ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx arg ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  -- Plan 0.94 §10: the domain-given IH on the argument (compose's `g`-route).
  → (argGivenIH : ∀ {A' π' B' Ψ' eE' d' fr'} {w' : ctx ⊢ᵈ arg ∶ A' ⇒[ π' ]↦ B' ⨾ Ψ'}
       → E.elabGivenV ctx arg A' π' ≡ (success B' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w' ⟧ˢ fmt dγ)
  -- D127: the ARM IH. A combinator arm is an ordinary term now, so its
  -- agreement is the recursion's; `μ`-bounded and CONTEXT-quantified (cata's
  -- algebra is checked in the cleared context).
  → (subIH : SubCheckIH (μ (Raw.RApp f arg)))
  -- ... and its INFER twin (compose's `f`-route synthesizes the inner arm).
  → (subInferIH : SubInferIH (μ (Raw.RApp f arg)))
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize w ⟧ˢ fmt dγ
agree-check-RApp ctx f arg T E.ahv-id veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T' <:? T | eq₁
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _ | ()
agree-check-RApp ctx f arg T E.ahv-fst veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T' <:? T | eq₁
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _ | ()
agree-check-RApp ctx f arg T E.ahv-snd veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T' <:? T | eq₁
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _ | ()
-- D194: `Out`'s CHECK is infer-then-check, so this is `terminal`'s verbatim.
agree-check-RApp ctx f arg T E.ahv-Out veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T' <:? T | eq₁
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _ | ()
agree-check-RApp ctx f arg T E.ahv-terminal veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T' <:? T | eq₁
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _ | ()
-- ahv-initial: arg checked at Void; se = morph-app initial argE (unary >>=T),
-- witness t-initial-app-check w, realize = morph-app initial (realize w) ⇒
-- rewrite the arg check IH.
agree-check-RApp ctx f arg T E.ahv-initial veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.checkElabV ctx arg Void in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | refl rewrite argCheckIH aeq (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                     (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
-- (Plan 0.52 M1: `ahv-arr` check-agree clauses retired with the surface `arr` builtin.)
-- ahv-inl/inr: direct sum target → morph-app (inl/inr Heap) argE (rewrite arg
-- check IH). D127: the pure-arrow→sum VALUE-LIFT targets are gone — `checkG` is
-- deleted and `inl e` at an arrow type is a type error the program writes as
-- `\_ -> inl e` — so those clauses reduce to `failure` and coverage prunes them.
-- ahv-In: bare μ target → morph-app In; the arrow target went the same way.
-- All other targets make the dispatch fail ⇒ Agda prunes them via `disp` clash.
agree-check-RApp ctx f arg (A + B) E.ahv-inl veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.checkElabV ctx arg A in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | refl rewrite argCheckIH aeq (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                     (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
agree-check-RApp ctx f arg (A + B) E.ahv-inr veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.checkElabV ctx arg B in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | refl rewrite argCheckIH aeq (restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-trans (Surface.⊑ᵘ-*Many Ψ)
                     (Surface.⊑ᵘ-+ʳ Surface.zeroUsage (Many Surface.*ᵘ Ψ))) dγ) = refl
-- ahv-In at a bare `μ-type F` target (Plan 0.55 D#2): checkInGo builds `morph-app
-- (In wfF Heap) argE` — delegate to agree-checkInGo (arg-check congruence).
agree-check-RApp ctx f arg (μ-type F) E.ahv-In veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ =
  agree-checkInGo ctx arg F (wellFormedF? F) refl disp argCheckIH dγ
-- ahv-curry: D127 — `checkCurry` emits `Surface.curry' argE` and `realize
-- (t-curry-check w) = curry' (realize w)`, so this is the ARM congruence:
-- rewrite the arg's check IH. Non-arrow-arrow targets ⇒ dispatch fails ⇒ pruned
-- by `disp`.
-- D222: ONE clause, with the two purities SEPARATED. The OUTER grade `π₀` is
-- matched and then ignored — `evalᴰ (curry f) a = returnT (…)`, so building the
-- closure emits nothing at any grade. The BODY is checked at the INNER arrow's
-- `π`, because that is the arrow `apply` runs.
--
-- The two clauses this replaces both fixed the INNER arrow (and the body) to
-- `pure` and varied the OUTER one, so `Eff Int (Int -> Int)` was covered and
-- `Int -> Eff Int Unit` was not. The coverage checker said so directly when the
-- rule was widened: "Missing cases: … (T₁ ⇒[pure] T₂ ⇒[eff] T₃)".
agree-check-RApp ctx f arg (A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)) E.ahv-curry veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.checkElabV ctx arg ((A * B) ⇒[ mk-kind Many π ] C) in eqarg | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | refl rewrite argCheckIH eqarg dγ = refl
-- ahv-pair-applied: D127 — `checkPair` emits `Surface.fork' fE gE` and
-- `realize (t-pair-morph-check wF wG) = fork' (realize wF) (realize wG)`. The
-- FIRST arm is `f_inner`, a sub-expression of the head, so its IH comes from
-- `subIH` (`argCheckIH` only covers `arg`).
-- D222: ONE clause, π-polymorphic, mirroring `checkPair`'s single grade-poly
-- clause. There used to be two — a pure one and an eff one that checked the arms
-- at `pure` and subsumed the result — and they collapse for the same reason the
-- elaborator's did: the arms' grade IS the result's.
agree-check-RApp ctx (Raw.RApp (Raw.RResolved (gen "pair")) f_inner) arg (A ⇒[ mk-kind Many π ] (B * C)) E.ahv-pair-applied veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.checkElabV ctx f_inner (A ⇒[ mk-kind Many π ] B) in eqf | disp
... | failure _ , _ | ()
... | success Ψf fE df frf , wF | disp'
      with E.checkElabV ctx arg (A ⇒[ mk-kind Many π ] C) in eqg | disp'
... | failure _ , _ | ()
... | success Ψg gE dg frg , wG | refl
          = binop-agree (SD.⟦ fE ⟧ˢ fmt E₁) (SD.⟦ realize wF ⟧ˢ fmt E₁)
                        (SD.⟦ gE ⟧ˢ fmt E₂) (SD.⟦ realize wG ⟧ˢ fmt E₂)
                        (λ vf vg → returnT (λ a → vf a >>=T λ x → vg a >>=T λ y → returnT (x , y))) (subIH ctx f_inner (inner-arm-< (Raw.RResolved (gen "pair")) f_inner arg) eqf E₁) (argCheckIH eqg E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψf Ψg) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψf Ψg) dγ
-- ahv-case-applied: checkCase emits `lift-morphism (case m_f m_g)`, witness
-- `t-morph-lift (m-case mFᵐ mGᵐ)`; rewrite both components.
-- Plan 0.52: case π (checkCase now has a separate eff-clause, so it no longer
-- reduces at abstract π). pure → checkCaseGo directly (agree-caseGo); eff → the
-- eff-clause (agree-caseGo-eff: passthrough or subsumed-pure).
agree-check-RApp ctx (Raw.RApp (Raw.RResolved (gen "case")) f_inner) arg ((A + B) ⇒[ mk-kind Many pure ] C) E.ahv-case-applied veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ =
  agree-caseGo ctx f_inner arg A B C pure disp
    (subIH ctx f_inner (inner-arm-< (Raw.RResolved (gen "case")) f_inner arg)) argCheckIH dγ
agree-check-RApp ctx (Raw.RApp (Raw.RResolved (gen "case")) f_inner) arg ((A + B) ⇒[ mk-kind Many eff ] C) E.ahv-case-applied veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ =
  agree-caseGo-eff ctx f_inner arg A B C disp
    (subIH ctx f_inner (inner-arm-< (Raw.RResolved (gen "case")) f_inner arg)) argCheckIH dγ
-- ahv-compose-applied: plan 0.94 §10 — `g`'s route first, `f`'s on its failure.
agree-check-RApp ctx (Raw.RApp (Raw.RResolved (gen "compose")) f_inner) arg (A ⇒[ mk-kind Many π ] C) E.ahv-compose-applied veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ =
  agree-checkCompose-g ctx f_inner arg A C π (E.elabGivenV ctx arg A π) disp argGivenIH
    (subIH ctx f_inner (inner-arm-< (Raw.RResolved (gen "compose")) f_inner arg))
    (subInferIH ctx f_inner (inner-arm-< (Raw.RResolved (gen "compose")) f_inner arg))
    argCheckIH dγ
-- ahv-apply (check): checkApply infers the arg; se = morph-app apply argE,
-- witness t-apply-check w, realize = morph-app apply (realize-infer w) ⇒ plain
-- morph-app congruence via the inferred-arg IH. Non-`(Many-pure-arrow * A)` args fail.
-- Plan 0.52: `apply p` now routes its check through the named embedOrSubsume
-- (infer the whole app, embed at T or subsume) — identical shape to ahv-other.
agree-check-RApp ctx f arg T E.ahv-apply veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | success T' Ψ eE d fr , w | eq₁ with T' <:? T | eq₁
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _ | ()
agree-check-RApp ctx f arg T E.ahv-apply veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  | failure _ , _ | ()
-- ahv-other (check): the dispatch first tries `inferElabV (RApp f arg)` and on
-- success matches `T` — that is the `t-embed` path (`realize (t-embed w) =
-- realize-infer w` ⇒ the supplied `inferIH`). D230: an application that does
-- not synthesize does not check either (the spine IS its inference), so the
-- infer-failure branch is absurd.
agree-check-RApp ctx f arg T E.ahv-other veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | success T' Ψ eE d fr , w | eq₁ with T' <:? T | eq₁
... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (inferIH refl dγ)
... | no _ | ()
agree-check-RApp ctx f arg T E.ahv-other veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ
  | failure errInfer , _ | ()
-- ahv-cata (Plan 0.55 D#2): the elaborated `se` is a `Surface.cata` node (a bare
-- morphism), so drive the agreement by the OUTPUT via `agree-checkCataGo` — no view
-- catch-all. pure: `checkCata` reduces DIRECTLY to `checkCataGo … pure`. eff: the
-- eff clause tries the eff-Go (genuine-eff algebra) then subsumes a pure-Go via
-- `arr'`/`t-subsume`; both `arr'` wrappers are denotationally transparent
-- (`⟦arr' x⟧ = ⟦x⟧`, `realize (t-subsume w) = arr' (realize w)`), so each branch is
-- the corresponding `agree-checkCataGo`.
agree-check-RApp ctx f arg (A ⇒[ mk-kind Many π ] ν-type F) E.ahv-ana veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ =
  agree-checkAnaGo ctx arg F A π (wellFormedF? F) refl disp
    (subIH (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) arg
           (μ<-r (μ f) (μ arg))) dγ
-- D226: one grade-generic clause (the elaborator's eff fallback is gone).
agree-check-RApp ctx f arg (μ-type F ⇒[ mk-kind Many π ] A) E.ahv-cata veq disp inferIH argCheckIH argInferIH argGivenIH subIH subInferIH dγ =
  agree-checkCataGo ctx arg F A π (wellFormedF? F) refl disp
    (subIH (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) arg
           (μ<-r (μ f) (μ arg))) dγ
-- Plan 0.55 D#2 (catch-all ELIMINATED): no `check-RApp-todo` catch-all. Every
-- (view × target) the dispatch can make SUCCEED now has an explicit agree clause
-- (id/fst/snd/terminal/apply/other via infer-embed; initial/inl/inr via morph-app or
-- checkG value-lift; In/curry/pair/case/compose/cata via the morphism/subsume
-- bridges). Every OTHER (view × target) makes the dispatch reduce to `failure`, so
-- `disp : … ≡ (success …)` is a constructor clash Agda's coverage checker prunes
-- automatically — no absurd (view × target) matrix. [[feedback_recurse_on_output_not_dispatch]]

------------------------------------------------------------------------
-- Well-founded measure for the infer/check mutual recursion. The same-size
-- `check-agreeV e → infer-agreeV e` (the t-embed fallback) together with the
-- strictly-smaller `infer-agreeV (RAnnot e T) → check-agreeV e` make the SCC
-- mutual, and foetus cannot see termination through the `with`-auxes. We make
-- it explicit via `Acc` on a lexicographic measure `(size, phase)` flattened to
-- `μe+μe` (infer, phase 0) / `suc (μe+μe)` (check, phase 1): check→infer at the
-- same `e` drops the phase (strictly <), infer→check is on a strictly smaller
-- subterm, and every other recursive call shrinks the subterm.
mInfer mCheck : RawExpr → ℕ
mInfer e = μ e +ℕ μ e
mCheck e = suc (μ e +ℕ μ e)

-- doubling is strictly monotone
dbl-< : ∀ {m n} → m < n → m +ℕ m < n +ℕ n
dbl-< h = +-mono-< h h

-- check-mode strictly dominates infer-mode at the same expression (phase drop)
infer<check : ∀ e → mInfer e < mCheck e
infer<check e = ≤-refl

-- `RAnnot e T` (infer) strictly dominates its checked body `e` (check)
check<infer-annot : ∀ e T → mCheck e < mInfer (Raw.RAnnot e T)
check<infer-annot e T = s≤s (≤-reflexive (sym (+-suc (μ e) (μ e))))

------------------------------------------------------------------------
-- Plan 0.94 §10: the DOMAIN-GIVEN mode's agreement. Each lemma mirrors one
-- elaborator helper with its decisions as arguments; the recursion supplies the
-- IHs (`given-agreeV`, in the mutual block below).
------------------------------------------------------------------------

-- Plan 0.94 §13: the emitted "evaluate, discard, continue" forms agree when
-- their parts do.
seq-agree : ∀ {n} {Γ : Surface.Ctx n} {Ψa Ψb : Usage n} {A B} {a a′ : Expr Γ Ψa A} {b b′ : Expr Γ Ψb B}
  → (∀ E → SD.⟦ a ⟧ˢ fmt E ≡ SD.⟦ a′ ⟧ˢ fmt E) → (∀ E → SD.⟦ b ⟧ˢ fmt E ≡ SD.⟦ b′ ⟧ˢ fmt E)
  → ∀ dγ → SD.⟦ seq a b ⟧ˢ fmt dγ ≡ SD.⟦ seq a′ b′ ⟧ˢ fmt dγ
seq-agree {Γ = Γ} {Ψa} {Ψb} {a = a} {a′} {b} {b′} ha hb dγ =
  cong (λ m → m >>=T λ v → returnT (proj₂ v))
       (binop-agree (SD.⟦ a ⟧ˢ fmt E₁) (SD.⟦ a′ ⟧ˢ fmt E₁) (SD.⟦ b ⟧ˢ fmt E₂) (SD.⟦ b′ ⟧ˢ fmt E₂)
                    (λ x y → returnT (x , y)) (ha E₁) (hb E₂))
  where
    E₁ = restrictᴰ {Γ = Γ} (Surface.⊑ᵘ-+ˡ Ψa Ψb) dγ
    E₂ = restrictᴰ {Γ = Γ} (Surface.⊑ᵘ-+ʳ Ψa Ψb) dγ

seq0-agree : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Usage n} {A B} {a a′ : Expr Γ Ψ A} {b : Expr Γ Surface.zeroUsage B}
  → (∀ E → SD.⟦ a ⟧ˢ fmt E ≡ SD.⟦ a′ ⟧ˢ fmt E)
  → ∀ dγ → SD.⟦ seq0 a b ⟧ˢ fmt dγ ≡ SD.⟦ seq0 a′ b ⟧ˢ fmt dγ
seq0-agree {Γ = Γ} {Ψ} {B = B} {a} {a′} {b} ha dγ =
  trans (SD-subst-usage′ (+ᵘ-identityʳ Ψ) {e = seq a b} dγ)
        (trans (seq-agree {a = a} {a′} {b} {b} ha (λ _ → refl) _)
               (sym (SD-subst-usage′ (+ᵘ-identityʳ Ψ) {e = seq a′ b} dγ)))

embed-agree : ∀ {n} {Γ : Surface.Ctx n} {A} {e e′ : Expr Surface.∅ Surface.[] A}
  → SD.⟦ e ⟧ˢ fmt tt ≡ SD.⟦ e′ ⟧ˢ fmt tt
  → ∀ dγ → SD.⟦ embedClosed {Γ = Γ} e ⟧ˢ fmt dγ ≡ SD.⟦ embedClosed {Γ = Γ} e′ ⟧ˢ fmt dγ
embed-agree {Γ = Γ} {A} {e} {e′} h dγ = trans (sd-embed e) (trans h (sym (sd-embed e′)))
  where
    sd-embed : ∀ (x : Expr Surface.∅ Surface.[] A) → SD.⟦ embedClosed {Γ = Γ} x ⟧ˢ fmt dγ ≡ SD.⟦ x ⟧ˢ fmt tt
    sd-embed x =
      trans (SD-subst-usage′ {Γ = Γ} {A = A} closed-usage-eq
               {e = Surface.morph-app {Γ = Γ} {Ψ = Surface.zeroUsage} {A = Once.Type.Unit} {B = A} (elaborate IR.Heap x) Surface.unit} dγ)
            (T-ext-at (faithful {Γ = Surface.∅} {Ψ = Surface.[]} {A = A} x tt))

-- D229 / plan 0.94 §13: `cata` given `Void` — the algebra is built, then `¡`.
agree-given-cata-void : ∀ {ctx : NamedCtx} {alg : RawExpr} {π : Purity}
  (r : VerifiedInferResult (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg)
  {B Ψ se d fr} {w : ctx ⊢ᵈ Raw.RApp (Raw.RResolved (gen "cata")) alg ∶ Void ⇒[ π ]↦ B ⨾ Ψ}
  → E.given-cata-void ctx alg π r ≡ (success B Ψ se d fr , w)
  → (∀ {T' Ψ' eE' d' fr'} {w' : ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx) ⊢ᵢ alg ∶ T' ⨾ Ψ'}
       → r ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w ⟧ˢ fmt dγ
agree-given-cata-void (failure _ , _) () rIH
agree-given-cata-void {ctx = ctx} {π = π} (success _ Surface.[] algE _ _ , w) refl rIH dγ =
  seq0-agree {Γ = NamedCtx.debruijn ctx} {a = embedClosed algE} {embedClosed (realize-infer w)} {Surface.lift-morphism {A = Void} {B = Void} {π = π} IR.initial}
    (embed-agree {Γ = NamedCtx.debruijn ctx} {e = algE} {realize-infer w} (rIH refl tt)) dγ

-- D229 / plan 0.94 §13: the operator dispatch with its `Void` cases in front.
-- One clause per leaf of the elaborator's case tree, so each reduces.
agree-RBinOp-void : ∀ {ctx : NamedCtx} (op : Raw.BinOp) {e₁ e₂ : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RBinOp op e₁ e₂ ∶ A ⨾ Ψ}
  (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
  → E.inferElabV-RBinOp-void ctx op e₁ e₂ r₁ r₂ ≡ (success A Ψ se d f , w)
  → (∀ {A₁ Ψ₁ e₁E d₁ f₁} {w₁ : ctx ⊢ᵢ e₁ ∶ A₁ ⨾ Ψ₁}
       → r₁ ≡ (success A₁ Ψ₁ e₁E d₁ f₁ , w₁) → ∀ dγ → SD.⟦ e₁E ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ)
  → (∀ {A₂ Ψ₂ e₂E d₂ f₂} {w₂ : ctx ⊢ᵢ e₂ ∶ A₂ ⨾ Ψ₂}
       → r₂ ≡ (success A₂ Ψ₂ e₂E d₂ f₂ , w₂) → ∀ dγ → SD.⟦ e₂E ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w₂ ⟧ˢ fmt dγ)
  → ∀ dγ → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-RBinOp-void op r₁@(failure _ , _) r₂ eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success Void _ _ _ _ , _) (failure _ , _) () s₁ s₂
agree-RBinOp-void op (success Void _ _ _ _ , _) (success _ _ _ _ _ , _) refl s₁ s₂ dγ = s₁ refl dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success Unit _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Unit _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success Int _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Int _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success Float _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Float _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success Str _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Str _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success Buffer _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success Buffer _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success (_ * _) _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ * _) _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success (_ + _) _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ + _) _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success (_ ⇒[ _ ] _) _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (_ ⇒[ _ ] _) _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success (μ-type _) _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (μ-type _) _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(failure _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op (success (ν-type _) _ e₁E _ _ , w₁) (success Void _ e₂E _ _ , w₂) refl s₁ s₂ dγ =
  seq-agree {a = e₁E} {realize-infer w₁} {e₂E} {realize-infer w₂} (s₁ refl) (s₂ refl) dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success Unit _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success Int _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success Float _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success Str _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success Buffer _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success (_ * _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success (_ + _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success (_ ⇒[ _ ] _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success (μ-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ
agree-RBinOp-void op r₁@(success (ν-type _) _ _ _ _ , _) r₂@(success (ν-type _) _ _ _ _ , _) eq s₁ s₂ dγ = agree-RBinOp op r₁ r₂ eq s₁ s₂ dγ

-- `d-infer`: the inferred term under its arrow conversion, on both sides.
agree-given-infer : ∀ {ctx : NamedCtx} {e : RawExpr} (A : Type) (π : Purity)
  (r : VerifiedInferResult ctx e) {B Ψ se d fr} {w : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ}
  → E.given-infer ctx e A π r ≡ (success B Ψ se d fr , w)
  → (rIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ e ∶ T' ⨾ Ψ'}
       → r ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w ⟧ˢ fmt dγ
agree-given-infer A π (failure _ , _) () rIH
agree-given-infer A π (success (A′ ⇒[ mk-kind Many π′ ] B) Ψ eE d fr , w) eq rIH dγ
  with A <:? A′ | π′ ⊑π? π | eq
... | yes a | yes g | refl = cong (fmapT ⟦ sub-arr {q = Many} a (<:-refl B) g ⟧<:) (rIH refl dγ)
... | yes _ | no _  | ()
... | no _  | _     | ()
agree-given-infer A π (success (_ ⇒[ mk-kind One _ ] _) _ _ _ _ , _) () rIH
agree-given-infer A π (success (_ ⇒[ mk-kind Zero _ ] _) _ _ _ _ , _) () rIH
agree-given-infer A π (success Unit _ _ _ _ , _) () rIH
agree-given-infer A π (success Void _ _ _ _ , _) () rIH
agree-given-infer A π (success Int _ _ _ _ , _) () rIH
agree-given-infer A π (success Float _ _ _ _ , _) () rIH
agree-given-infer A π (success Str _ _ _ _ , _) () rIH
agree-given-infer A π (success Buffer _ _ _ _ , _) () rIH
agree-given-infer A π (success (_ * _) _ _ _ _ , _) () rIH
agree-given-infer A π (success (_ + _) _ _ _ _ , _) () rIH
agree-given-infer A π (success (μ-type _) _ _ _ _ , _) () rIH
agree-given-infer A π (success (ν-type _) _ _ _ _ , _) () rIH

-- `d-cata`: the algebra synthesizes `⟦ F ⟧T A ⇒ A`; the fold node is the same.
agree-given-cata : ∀ (ctx : NamedCtx) (alg : RawExpr) (F : Functor) (π : Purity) (wfF : WellFormedF F)
  (r : VerifiedInferResult (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg)
  {B Ψ se d fr} {w : ctx ⊢ᵈ Raw.RApp (Raw.RResolved (gen "cata")) alg ∶ μ-type F ⇒[ π ]↦ B ⨾ Ψ}
  → E.given-cata ctx alg F π wfF r ≡ (success B Ψ se d fr , w)
  → (rIH : ∀ {T' Ψ' eE' d' fr'} {w' : (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) ⊢ᵢ alg ∶ T' ⨾ Ψ'}
       → r ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w ⟧ˢ fmt dγ
agree-given-cata ctx alg F π wfF (failure _ , _) () rIH
agree-given-cata ctx alg F π wfF (success (X ⇒[ k ] A) Surface.[] algE d fr , w) eq rIH dγ
  with (X ⇒[ k ] A) ≟T (⟦ F ⟧T A ⇒[ mk-kind Many π ] A) | eq
... | yes refl | refl rewrite rIH refl tt = refl
... | no _ | ()
agree-given-cata ctx alg F π wfF (success Unit _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success Void _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success Int _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success Float _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success Str _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success Buffer _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success (_ * _) _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success (_ + _) _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success (μ-type _) _ _ _ _ , _) () rIH
agree-given-cata ctx alg F π wfF (success (ν-type _) _ _ _ _ , _) () rIH

-- The generators: both sides are the same `lift-morphism`.
agree-given-leaf : ∀ (ctx : NamedCtx) (cn : CanonicalName) (A : Type) (π : Purity)
  (vw : E.AppHeadView (Raw.RResolved cn)) (r : VerifiedInferResult ctx (Raw.RResolved cn))
  {B Ψ se d fr} {w : ctx ⊢ᵈ Raw.RResolved cn ∶ A ⇒[ π ]↦ B ⨾ Ψ}
  → E.elabGivenLeaf ctx cn A π vw r ≡ (success B Ψ se d fr , w)
  → (rIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ (Raw.RResolved cn) ∶ T' ⨾ Ψ'}
       → r ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w ⟧ˢ fmt dγ
agree-given-leaf ctx ._ A π E.ahv-id r refl rIH dγ = refl
agree-given-leaf ctx ._ (_ * _) π E.ahv-fst r refl rIH dγ = refl
agree-given-leaf ctx ._ (_ * _) π E.ahv-snd r refl rIH dγ = refl
agree-given-leaf ctx ._ A π E.ahv-terminal r refl rIH dγ = refl
agree-given-leaf ctx ._ Void π E.ahv-initial r refl rIH dγ = refl
agree-given-leaf ctx ._ Unit π E.ahv-fst r () rIH
agree-given-leaf ctx ._ Void π E.ahv-fst r refl rIH dγ = refl
agree-given-leaf ctx ._ Int π E.ahv-fst r () rIH
agree-given-leaf ctx ._ Float π E.ahv-fst r () rIH
agree-given-leaf ctx ._ Str π E.ahv-fst r () rIH
agree-given-leaf ctx ._ Buffer π E.ahv-fst r () rIH
agree-given-leaf ctx ._ (_ + _) π E.ahv-fst r () rIH
agree-given-leaf ctx ._ (_ ⇒[ _ ] _) π E.ahv-fst r () rIH
agree-given-leaf ctx ._ (μ-type _) π E.ahv-fst r () rIH
agree-given-leaf ctx ._ (ν-type _) π E.ahv-fst r () rIH
agree-given-leaf ctx ._ Unit π E.ahv-snd r () rIH
agree-given-leaf ctx ._ Void π E.ahv-snd r refl rIH dγ = refl
agree-given-leaf ctx ._ Int π E.ahv-snd r () rIH
agree-given-leaf ctx ._ Float π E.ahv-snd r () rIH
agree-given-leaf ctx ._ Str π E.ahv-snd r () rIH
agree-given-leaf ctx ._ Buffer π E.ahv-snd r () rIH
agree-given-leaf ctx ._ (_ + _) π E.ahv-snd r () rIH
agree-given-leaf ctx ._ (_ ⇒[ _ ] _) π E.ahv-snd r () rIH
agree-given-leaf ctx ._ (μ-type _) π E.ahv-snd r () rIH
agree-given-leaf ctx ._ (ν-type _) π E.ahv-snd r () rIH
agree-given-leaf ctx ._ Unit π E.ahv-initial r () rIH
agree-given-leaf ctx ._ Int π E.ahv-initial r () rIH
agree-given-leaf ctx ._ Float π E.ahv-initial r () rIH
agree-given-leaf ctx ._ Str π E.ahv-initial r () rIH
agree-given-leaf ctx ._ Buffer π E.ahv-initial r () rIH
agree-given-leaf ctx ._ (_ * _) π E.ahv-initial r () rIH
agree-given-leaf ctx ._ (_ + _) π E.ahv-initial r () rIH
agree-given-leaf ctx ._ (_ ⇒[ _ ] _) π E.ahv-initial r () rIH
agree-given-leaf ctx ._ (μ-type _) π E.ahv-initial r () rIH
agree-given-leaf ctx ._ (ν-type _) π E.ahv-initial r () rIH
agree-given-leaf ctx ._ A π E.ahv-inl r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx ._ A π E.ahv-inr r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx ._ A π E.ahv-curry r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx ._ A π E.ahv-apply r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx ._ A π E.ahv-In r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx ._ A π E.ahv-cata r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx ._ A π E.ahv-ana r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx ._ A π E.ahv-Out r eq rIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-leaf ctx cn A π E.ahv-other r eq rIH dγ = agree-given-infer A π r eq rIH dγ

-- The combinators: each arm on the given IH, assembled by one congruence.
agree-given-app : ∀ (ctx : NamedCtx) (f g : RawExpr) (A : Type) (π : Purity)
  (vw : E.AppHeadView f) (r : VerifiedInferResult ctx (Raw.RApp f g))
  {B Ψ se d fr} {w : ctx ⊢ᵈ Raw.RApp f g ∶ A ⇒[ π ]↦ B ⨾ Ψ}
  → E.elabGivenApp ctx f g A π vw r ≡ (success B Ψ se d fr , w)
  → (rIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ (Raw.RApp f g) ∶ T' ⨾ Ψ'}
       → r ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ → SD.⟦ eE' ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ)
  → (gIH : SubGivenIH (μ (Raw.RApp f g)))
  → (iIH : SubInferIH (μ (Raw.RApp f g)))
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w ⟧ˢ fmt dγ
agree-given-app ctx ._ g A π (E.ahv-compose-applied {f}) r eq rIH gIH iIH dγ
  with E.elabGivenV ctx g A π in geq | eq
... | failure _ , _ | ()
... | success M Ψg gE dg frg , wG | eq₁ with E.elabGivenV ctx f M π in feq | eq₁
... | failure _ , _ | ()
... | success B Ψf fE df frf , wF | refl =
        binop-agree (SD.⟦ fE ⟧ˢ fmt E₁) (SD.⟦ realize-d wF ⟧ˢ fmt E₁)
                    (SD.⟦ gE ⟧ˢ fmt E₂) (SD.⟦ realize-d wG ⟧ˢ fmt E₂)
                    (λ vf vg → returnT (λ a → vg a >>=T vf))
                    (gIH ctx f (inner-arm-< (Raw.RResolved (gen "compose")) f g) feq E₁)
                    (gIH ctx g (μ<-r (μ (Raw.RApp (Raw.RResolved (gen "compose")) f)) (μ g)) geq E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψf Ψg) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψf Ψg) dγ
agree-given-app ctx ._ g (A + B) π (E.ahv-case-applied {f}) r eq rIH gIH iIH dγ
  with E.elabGivenV ctx f A π in feq | eq
... | failure _ , _ | ()
... | success C Ψf fE df frf , wF | eq₁ with E.elabGivenV ctx g B π in geq | eq₁
... | failure _ , _ | ()
... | success C′ Ψg gE dg frg , wG | eq₂ with C′ ≟T C | eq₂
... | no _ | ()
... | yes refl | refl =
        binop-agree (SD.⟦ fE ⟧ˢ fmt E₁) (SD.⟦ realize-d wF ⟧ˢ fmt E₁)
                    (SD.⟦ gE ⟧ˢ fmt E₂) (SD.⟦ realize-d wG ⟧ˢ fmt E₂)
                    (λ vf vg → returnT (λ ab → [ vf , vg ]′ ab))
                    (gIH ctx f (inner-arm-< (Raw.RResolved (gen "case")) f g) feq E₁)
                    (gIH ctx g (μ<-r (μ (Raw.RApp (Raw.RResolved (gen "case")) f)) (μ g)) geq E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψf Ψg) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψf Ψg) dγ
agree-given-app ctx ._ g Unit π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g Void π (E.ahv-case-applied {f}) r eq rIH gIH iIH dγ
  with E.elabGivenV ctx f Void π in feq | eq
... | failure _ , _ | ()
... | success C₁ Ψf fE df frf , wF | eq₁ with E.elabGivenV ctx g Void π in geq | eq₁
... | failure _ , _ | ()
... | success C₂ Ψg gE dg frg , wG | refl =
        seq-agree {Γ = NamedCtx.debruijn ctx} {a = fE} {realize-d wF}
                  {seq0 gE (Surface.lift-morphism {A = Void} {B = Void} {π = π} IR.initial)} {seq0 (realize-d wG) (Surface.lift-morphism {A = Void} {B = Void} {π = π} IR.initial)}
                  (gIH ctx f (inner-arm-< (Raw.RResolved (gen "case")) f g) feq)
                  (seq0-agree {Γ = NamedCtx.debruijn ctx} {a = gE} {realize-d wG} {Surface.lift-morphism {A = Void} {B = Void} {π = π} IR.initial}
                     (gIH ctx g (μ<-r (μ (Raw.RApp (Raw.RResolved (gen "case")) f)) (μ g)) geq))
                  dγ
agree-given-app ctx ._ g Int π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g Float π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g Str π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g Buffer π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g (_ * _) π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g (_ ⇒[ _ ] _) π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g (μ-type _) π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g (ν-type _) π (E.ahv-case-applied {f}) r () rIH gIH iIH
agree-given-app ctx ._ g A π (E.ahv-pair-applied {f}) r eq rIH gIH iIH dγ
  with E.elabGivenV ctx f A π in feq | eq
... | failure _ , _ | ()
... | success B Ψf fE df frf , wF | eq₁ with E.elabGivenV ctx g A π in geq | eq₁
... | failure _ , _ | ()
... | success C Ψg gE dg frg , wG | refl =
        binop-agree (SD.⟦ fE ⟧ˢ fmt E₁) (SD.⟦ realize-d wF ⟧ˢ fmt E₁)
                    (SD.⟦ gE ⟧ˢ fmt E₂) (SD.⟦ realize-d wG ⟧ˢ fmt E₂)
                    (λ vf vg → returnT (λ a → vf a >>=T λ x → vg a >>=T λ y → returnT (x , y)))
                    (gIH ctx f (inner-arm-< (Raw.RResolved (gen "pair")) f g) feq E₁)
                    (gIH ctx g (μ<-r (μ (Raw.RApp (Raw.RResolved (gen "pair")) f)) (μ g)) geq E₂)
  where
    E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψf Ψg) dγ
    E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψf Ψg) dγ
agree-given-app ctx ._ alg (μ-type F) π E.ahv-cata r eq rIH gIH iIH dγ
  with wellFormedF? F | eq
... | nothing | ()
... | just wfF | eq₁ =
        agree-given-cata ctx alg F π wfF (E.inferElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg) eq₁
          (λ p → iIH (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg (μ<-r 1 (μ alg)) p) dγ
agree-given-app ctx ._ alg Unit π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg Void π E.ahv-cata r eq rIH gIH iIH dγ =
  agree-given-cata-void (E.inferElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg) eq
    (λ p → iIH (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg (μ<-r 1 (μ alg)) p) dγ
agree-given-app ctx ._ alg Int π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg Float π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg Str π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg Buffer π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg (_ * _) π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg (_ + _) π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg (_ ⇒[ _ ] _) π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ alg (ν-type _) π E.ahv-cata r () rIH gIH iIH
agree-given-app ctx ._ g A π E.ahv-id r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-fst r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-snd r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-terminal r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-inl r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-inr r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-initial r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-curry r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-apply r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-In r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-ana r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx ._ g A π E.ahv-Out r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ
agree-given-app ctx f g A π E.ahv-other r eq rIH gIH iIH dγ = agree-given-infer A π r eq rIH dγ

-- D229 / plan 0.94 §13: a `Void` scrutinee — the branches are typed, never
-- run; the term is the scrutinee's.
agree-case-void : ∀ {ctx : NamedCtx} {scrut : RawExpr} {xL : String} {eL : RawExpr} {xR : String} {eR : RawExpr}
  {Ψs : Usage (NamedCtx.size ctx)} {scrutE : Expr (NamedCtx.debruijn ctx) Ψs Void} {ds fs : ℕ}
  {wS : ctx ⊢ᵢ scrut ∶ Void ⨾ Ψs}
  (rL : VerifiedInferResult (extendNamedCtx ctx xL Void) eL) {A Ψ se d fr}
  {w : ctx ⊢ᵢ Raw.RDestruct scrut xL eL xR eR ∶ A ⨾ Ψ}
  → E.inferElabV-RDestruct-voidL ctx scrut xL eL xR eR scrutE ds fs wS rL ≡ (success A Ψ se d fr , w)
  → (∀ dγ → SD.⟦ scrutE ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer wS ⟧ˢ fmt dγ)
  → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ
agree-case-void (failure _ , _) () h
agree-case-void {ctx = ctx} {xR = xR} {eR = eR} (success _ (_ ∷ᵘ _) _ _ _ , _) eq h
  with E.inferElabV (extendNamedCtx ctx xR Void) eR | eq
... | failure _ , _ | ()
... | success _ (_ ∷ᵘ _) _ _ _ , _ | refl = h

-- check→check on a strictly-smaller subterm: `μ sub < μ par` ⇒
-- `mCheck sub < mCheck par`. Stated over the ℕ measures (NOT the exprs — `μ` is
-- not injective, so expr indices wouldn't infer).
mC-sub : ∀ {m n : ℕ} → m < n → suc (m +ℕ m) < suc (n +ℕ n)
mC-sub h = s≤s (dbl-< h)

-- check→infer on a strictly-smaller subterm: `mInfer sub < mCheck par`.
mIC-sub : ∀ {m n : ℕ} → m < n → m +ℕ m < suc (n +ℕ n)
mIC-sub h = ≤-trans (dbl-< h) (n≤1+n _)

-- infer→check on a strictly-smaller subterm: `mCheck sub < mInfer par`. Used
-- when an INFER node (e.g. `RApp f arg`, ahv-other) drives a CHECK on a child
-- (`checkElabV ctx arg A`). From `m < n` (child μ < parent μ), `suc m + suc m ≤
-- n + n` (+-mono-≤), and `suc m + suc m ≡ suc (suc (m + m))` (+-suc) ⇒ goal.
mCI-sub : ∀ {m n : ℕ} → m < n → suc (m +ℕ m) < n +ℕ n
mCI-sub {m} {n} h = subst (_≤ n +ℕ n) (cong suc (+-suc m m)) (+-mono-≤ h h)

mutual
  infer-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (ac : Acc _<_ (mInfer e)) {A Ψ se d f w}
    (eq : E.inferElabV ctx e ≡ (success A Ψ se d f , w)) → InferAgreeV ctx e eq
  infer-agreeV ctx (Raw.RInt n) _ refl dγ = refl
  -- RFloat: K3 removed F4's decision, so there is nothing to name and this is
  -- the `RInt` clause verbatim. The absurd `nothing` branch went with it —
  -- a float literal can no longer fail to elaborate.
  infer-agreeV ctx (Raw.RFloat i f l _) _ refl dγ = refl
  infer-agreeV ctx (Raw.RStringLit s) _ refl dγ = refl
  infer-agreeV ctx Raw.RUnit _ refl dγ = refl
  -- RPair: with-free — delegate to the top-level `agree-RPair`, passing both
  -- sub-results + sub-IHs (each with a strictly-smaller `Acc` from `rec`).
  infer-agreeV ctx (Raw.RPair a b) (acc rec) eq dγ =
    agree-RPair (E.inferElabV ctx a) (E.inferElabV ctx b) eq
      (λ p → infer-agreeV ctx a (rec (dbl-< (μ<-l (μ a) (μ b)))) p)
      (λ p → infer-agreeV ctx b (rec (dbl-< (μ<-r (μ a) (μ b)))) p) dγ
  -- PLAN 0.74 J6 step 3. `- 5` now elaborates to the LITERAL `-5`, while
  -- `realize-infer` still reads `neg (int 5)` off the derivation
  -- `t-neg (t-int 5)` — the derivation is indexed by the RAW expression and
  -- did not change. So the two sides are no longer the same term and
  -- agreement is a real step: `⊝ (fromℤ n) ≡ fromℤ (- n)`.
  --
  -- That `realize-agrees` is stated OBSERVATIONALLY is what makes the fold
  -- affordable. A syntactic `se ≡ realize w` would have forced `realize` to
  -- fold too, and with it every proof that reads the derivation.
  infer-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) (acc rec) eq dγ
    with E.negOperandView e | eq
  ... | E.nov-int n | refl =
          cong returnT (sym (OnceWord.Width.⊝-fromℤ (int-bits fmt) n))
  -- PLAN 0.73 F3. `refl`, and the contrast with the `Int` branch above is the
  -- whole content: there `realize-infer` keeps `neg (int n)` and the two sides
  -- are reconciled by `⊝-fromℤ`; here `Surface.neg` is Int-typed, so the
  -- reference elaboration had no float negation to keep and folded to the same
  -- literal the elaborator produces. Nothing to reconcile — which is also why
  -- this branch checks NOTHING about `round`, and why the pins in
  -- `Once.Float.Decimal` are where that is checked (D117).
  ... | E.nov-float i f l p | refl = refl
  -- NAME the abstracted equation: in this branch its type has already reduced
  -- through `inferElabV-neg-aux … nothing` to the plain aux, which is what
  -- `agree-RUnaryOp` is stated over. The un-refined `eq` has not.
  ... | E.nov-other .e | eq′ =
          agree-RUnaryOp (E.inferElabV ctx e) eq′
            (λ p → infer-agreeV ctx e (rec (dbl-< ≤-refl)) p) dγ
  infer-agreeV ctx (Raw.RLet x e₁ e₂) (acc rec) eq dγ =
    agree-RLet (E.inferElabV ctx e₁) eq
      (λ p → infer-agreeV ctx e₁ (rec (dbl-< (μ<-l (μ e₁) (μ e₂)))) p)
      (λ {A} rE2 eqRE2 p → infer-agreeV (extendNamedCtx ctx x A) e₂ (rec (dbl-< (μ<-r (μ e₁) (μ e₂)))) (trans eqRE2 p)) dγ
  infer-agreeV ctx (Raw.RResolved cn) _ eq dγ =
    agree-RResolved-view ctx cn (classifyGen cn) eq dγ
  -- D136: no `x ≟ "unit"` dispatch left — a bare `RVar` goes straight to the
  -- lookup-aux.
  infer-agreeV ctx (Raw.RVar x) _ eq dγ =
    agree-RVar ctx x (lookupLocal ctx x) refl
               (lookupImport (NamedCtx.imports ctx) x) refl eq dγ
  -- RLam / RAna: `inferElabV` always fails (no infer rule), so the success
  -- equation is absurd.
  infer-agreeV ctx (Raw.RLam _ _) _ ()
  infer-agreeV ctx (Raw.RAna _ _) _ ()
  -- RBinOp: with-free — delegate to top-level `agree-RBinOp`, passing both
  -- operand results explicitly + their sub-IHs (mirrors RPair).
  infer-agreeV ctx (Raw.RBinOp op e₁ e₂) (acc rec) eq dγ =
    agree-RBinOp-void op (E.inferElabV ctx e₁) (E.inferElabV ctx e₂) eq
      (λ p → infer-agreeV ctx e₁ (rec (dbl-< (μ<-l (μ e₁) (μ e₂)))) p)
      (λ p → infer-agreeV ctx e₂ (rec (dbl-< (μ<-r (μ e₁) (μ e₂)))) p) dγ
  -- RQualified: dispatch on the dotted-path import-lookup (with-free top-level).
  infer-agreeV ctx (Raw.RQualified name alias) _ eq dγ =
    agree-RQualified ctx name alias
      (lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)) refl eq dγ
  -- RApp: dispatch on the app-head view. arg-infer / f-infer / arg-check IHs
  -- each carry a strictly-smaller `Acc` (dbl-</μ<-l/μ<-r/mCI-sub).
  infer-agreeV ctx (Raw.RApp f arg) (acc rec) eq dγ =
    agree-RApp ctx f arg (E.classifyAppHeadView f) refl eq
      (λ p → infer-agreeV ctx arg (rec (dbl-< (μ<-r (μ f) (μ arg)))) p)
      (λ p → infer-agreeV ctx f (rec (dbl-< (μ<-l (μ f) (μ arg)))) p)
      (λ {T'} p → check-agreeV ctx arg T' (rec (mCI-sub (μ<-r (μ f) (μ arg)))) p)
      (λ p → given-agreeV ctx f _ _ (rec (mCI-sub (μ<-l (μ f) (μ arg)))) p) dγ
  -- RAnnot: infers by CHECKING the body against the annotation; delegate to
  -- `check-agreeV` (phase drops to check, which is strictly < this infer node).
  infer-agreeV ctx (Raw.RAnnot e T₀) (acc rec) eq dγ =
    agree-RAnnot (E.checkElabV ctx e T₀) eq
      (λ p → check-agreeV ctx e T₀ (rec (check<infer-annot e T₀)) p) dγ
  -- RDestruct (case): mirror the de-withed elaborator auxes (scrutinee type;
  -- left branch in ctx,xL:A; right branch in ctx,xR:B; branch-type match). The
  -- emitted `case' scrutE eLE eRE` denotes `⟦scrutE⟧ >>=T copair-of-branches`;
  -- `realize-infer (t-case …)` is the SAME shape; close by `bind2-agree`
  -- with each sub-IH carrying a strictly-smaller `Acc`.
  infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) (acc rec) eq dγ
    with E.inferElabV ctx scrut in seq | eq
  ... | failure _ , _ | ()
  ... | success Unit _ _ _ _ , _ | ()
  ... | success Void Ψs scrutE ds fs , wS | eq₁ =
          agree-case-void (E.inferElabV (extendNamedCtx ctx xL Void) eL) eq₁
            (λ E → infer-agreeV ctx scrut (rec (dbl-< (μ<-d-s (μ scrut) (μ eL) (μ eR)))) seq E) dγ
  ... | success Int _ _ _ _ , _ | ()
  ... | success Float _ _ _ _ , _ | ()
  ... | success Str _ _ _ _ , _ | ()
  ... | success Buffer _ _ _ _ , _ | ()
  ... | success (_ * _) _ _ _ _ , _ | ()
  ... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
  ... | success (μ-type _) _ _ _ _ , _ | ()
  ... | success (ν-type _) _ _ _ _ , _ | ()
  ... | success (A + B) Ψs scrutE ds fs , wS | eq₁
        with E.inferElabV (extendNamedCtx ctx xL A) eL in leq | eq₁
  ... | failure _ , _ | ()
  ... | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , wL | eq₂
            with E.inferElabV (extendNamedCtx ctx xR B) eR in req | eq₂
  ... | failure _ , _ | ()
  ... | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , wR | eq₃
              with C₁ ≟T C₂ | eq₃
  ... | no _ | ()
  ... | yes refl | refl =
                bind2-agree (SD.⟦ scrutE ⟧ˢ fmt Es) (SD.⟦ realize-infer wS ⟧ˢ fmt Es)
                  (λ v → [ (λ a → SD.⟦ eLE ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qℓ Eₗ a))
                         , (λ b → SD.⟦ eRE ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qr Eᵣ b)) ]′ v)
                  (λ v → [ (λ a → SD.⟦ realize-infer wL ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qℓ Eₗ a))
                         , (λ b → SD.⟦ realize-infer wR ⟧ˢ fmt (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qr Eᵣ b)) ]′ v)
                  (infer-agreeV ctx scrut (rec (dbl-< (μ<-d-s (μ scrut) (μ eL) (μ eR)))) seq Es)
                  (λ { (inj₁ a) → infer-agreeV (extendNamedCtx ctx xL A) eL (rec (dbl-< (μ<-d-l (μ scrut) (μ eL) (μ eR)))) leq (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = A} qℓ Eₗ a)
                     ; (inj₂ b) → infer-agreeV (extendNamedCtx ctx xR B) eR (rec (dbl-< (μ<-d-r (μ scrut) (μ eL) (μ eR)))) req (bindᴰ {Γ = NamedCtx.debruijn ctx} {A = B} qr Eᵣ b) })

                where
                  Eall = restrictᴰ {Γ = NamedCtx.debruijn ctx}
                           (Surface.⊑ᵘ-+ʳ Ψs (Ψₗ Surface.⊔ᵘ Ψᵣ)) dγ
                  Es = restrictᴰ {Γ = NamedCtx.debruijn ctx}
                         (Surface.⊑ᵘ-+ˡ Ψs (Ψₗ Surface.⊔ᵘ Ψᵣ)) dγ
                  Eₗ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) Eall
                  Eᵣ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) Eall

  check-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) (ac : Acc _<_ (mCheck e)) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq
  -- Generic infer-and-match fallback (checkElabV's catch-all): the check
  -- witness is `t-embed w` over the infer witness `w`, `se` is the infer-
  -- elaborated `eE`, and `realize (t-embed w) = realize-infer w`, so agreement
  -- is EXACTLY `infer-agreeV` of the same expr (the phase drops, so the `Acc`
  -- is strictly smaller via `infer<check`). Mirror the fallback's two `with`s
  -- (inferElabV result; `T ≟T T'`), threading `eq` so it reduces.
  -- Infer-then-check (generic catch-all = `embedOrSubsume`): ONE bridge lemma.
  check-agreeV ctx (Raw.RBinOp op a b) T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RBinOp op a b) (rec (infer<check (Raw.RBinOp op a b))) p) dγ
  -- PLAN 0.73 F3: the neg node has a specialised check clause now, so this
  -- mirrors `checkElabV-neg-dispatch`'s three-way split — the `RInt`/`RFloat`
  -- branches like `check-agreeV`'s own literal clauses above, the rest like
  -- the generic fallback it used to be in full.
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T (acc rec) eq dγ
    with E.negOperandView e | eq
  ... | E.nov-int n | eq₁ with E.isRIntVliftTarget? T | eq₁
  -- D127: no value-lift. A literal at an ARROW target is a TypeMismatch now,
  -- so this column is absurd rather than a lift.
  ... | just (X , π , refl) | ()
  ... | nothing | eq₂ with Int <:? T | eq₂
  -- The SAME `⊝-fromℤ` step the infer branch spends: the elaborator folded to
  -- the literal `-n` while `realize (t-sub (t-neg (t-int n)) p)` still reads
  -- `neg (int n)` off the derivation; both sides carry the same conversion.
  ... | yes p | refl =
            cong (fmapT ⟦ p ⟧<:) (cong returnT (sym (OnceWord.Width.⊝-fromℤ (int-bits fmt) n)))
  ... | no _ | ()
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T (acc rec) eq dγ
    | E.nov-float i f l p | eq₁ with E.isRFloatVliftTarget? T | eq₁
  -- D127: no value-lift. A literal at an ARROW target is a TypeMismatch now,
  -- so this column is absurd rather than a lift.
  ... | just (X , π , refl) | ()
  ... | nothing | eq₂ with Float <:? T | eq₂
  -- Nothing to spend here: `realize-infer (t-neg-float …)` folded too, because
  -- `Surface.neg` is Int-typed and there was no float negation to keep.
  ... | yes _ | refl = refl
  ... | no _ | ()
  -- NOT a literal: the generic fallback, but named at the form the abstracted
  -- view has already reduced to — `inferElabV ctx (RUnaryOp OpNeg e)` would
  -- unfold back into the stuck view.
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T (acc rec) eq dγ
    | E.nov-other .e | eq₁ =
      agree-embedOrSubsume-at T (E.inferElabV-RUnaryOp-aux ctx e (E.inferElabV ctx e)) eq₁
        (λ p → agree-RUnaryOp (E.inferElabV ctx e) p
                 (λ q → infer-agreeV ctx e (rec (mIC-sub ≤-refl)) q))
        dγ
  check-agreeV ctx (Raw.RLet x e₁ e₂) T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RLet x e₁ e₂) (rec (infer<check (Raw.RLet x e₁ e₂))) p) dγ
  check-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) (rec (infer<check (Raw.RDestruct scrut xL eL xR eR))) p) dγ
  check-agreeV ctx (Raw.RAnnot e T₀) T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RAnnot e T₀) (rec (infer<check (Raw.RAnnot e T₀))) p) dγ
  check-agreeV ctx (Raw.RQualified name alias) T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RQualified name alias) (rec (infer<check (Raw.RQualified name alias))) p) dγ
  check-agreeV ctx (Raw.RResolved cn) T (acc rec) eq dγ =
    check-agree-RResolved-view ctx cn T (classifyGen cn) eq
      (λ p → infer-agreeV ctx (Raw.RResolved cn) (rec (infer<check (Raw.RResolved cn))) p) dγ
  -- RUnit / RStringLit: generic fallback over a literal whose inferred type is
  -- fixed (Unit / Str); case `T ≟T <that>` (the fallback's `T ≟T T'`), so `eq`
  -- reduces. `yes refl` delegates to `infer-agreeV` of the literal.
  check-agreeV ctx Raw.RUnit T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx Raw.RUnit (rec (infer<check Raw.RUnit)) p) dγ
  check-agreeV ctx (Raw.RStringLit s) T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RStringLit s) (rec (infer<check (Raw.RStringLit s))) p) dγ
  -- RInt: vlift target (X ⇒[Many,pure] Int) emits `lift-morphism (intLit n)`,
  -- witness `t-value-lift (g-int n)`; `realize-global (g-int n) = intLit n`, so
  -- the two `lift-morphism`s coincide ⇒ `refl`. Otherwise the generic fallback
  -- (inferred type Int) delegates to `infer-agreeV`.
  check-agreeV ctx (Raw.RInt n) T (acc rec) eq dγ with E.isRIntVliftTarget? T | eq
  -- D127: no value-lift (see above).
  ... | just (X , π , refl) | ()
  ... | nothing | eq' with Int <:? T | eq'
  ... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (infer-agreeV ctx (Raw.RInt n) (rec (infer<check (Raw.RInt n))) refl dγ)
  ... | no _ | ()
  -- RFloat mirrors it, with _ the acceptance decision as a THIRD scrutinee: the
  -- K3: only ONE scrutinee left. The acceptance decision used to be named in
  -- BOTH branches — the fallback runs `inferElabV`, which dispatched on the
  -- same decision, so leaving it unnamed left the equation stuck. There is no
  -- decision now, and the two absurd branches went with it.
  check-agreeV ctx (Raw.RFloat i f l _) T (acc rec) eq dγ
    with E.isRFloatVliftTarget? T | eq
  -- D127: no value-lift (see above).
  ... | just (X , π , refl) | ()
  ... | nothing | eq' with Float <:? T | eq'
  ... | yes _ | refl = refl
  ... | no _ | ()
  -- RPair: product target → bidirectional component check (pair denotation is
  -- fuel-`k`-pointwise, rewrite both component agreements); else the generic
  -- infer-and-match fallback.
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ with E.classifyRPairTarget T | eq
  ... | E.rpt-prod A B | eq'
        with E.checkElabV ctx a A in eqa | eq'
  ... | failure _ , _ | ()
  ... | success Ψ₁ aE da fa , wA | eq''
            with E.checkElabV ctx b B in eqb | eq''
  ... | failure _ , _ | ()
  ... | success Ψ₂ bE db fb , wB | refl
                = binop-agree (SD.⟦ aE ⟧ˢ fmt E₁) (SD.⟦ realize wA ⟧ˢ fmt E₁)
                              (SD.⟦ bE ⟧ˢ fmt E₂) (SD.⟦ realize wB ⟧ˢ fmt E₂)
                              (λ va vb → returnT (va , vb)) (check-agreeV ctx a A (rec (mC-sub (μ<-l (μ a) (μ b)))) eqa E₁)
                                (check-agreeV ctx b B (rec (mC-sub (μ<-r (μ a) (μ b)))) eqb E₂)
                where
                  E₁ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ
                  E₂ = restrictᴰ {Γ = NamedCtx.debruijn ctx} (Surface.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ
  -- D127: a pair literal at an ARROW type is no longer a value-lift — `checkG`
  -- is deleted and `checkElabV-RPair-aux` returns `TypeMismatch` — so the
  -- success equation is absurd.
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ | E.rpt-vlift X A B π | ()
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ | E.rpt-other T' | eq'
        with E.inferElabV ctx (Raw.RPair a b) in ieq | eq'
  ... | failure _ , _ | ()
  ... | success T'' Ψ eE d fr , w | eq₂ with T'' <:? T' | eq₂
  ... | yes p | refl = cong (fmapT ⟦ p ⟧<:) (infer-agreeV ctx (Raw.RPair a b) (rec (infer<check (Raw.RPair a b))) ieq dγ)
  ... | no _ | ()
  -- RLam: checks against ANY arrow (D226: `t-lam` is grade-poly); the body
  -- is checked in `ctx,x:A`. `se = lam q leq bodyE`, witness `t-lam leq wBody`,
  -- and `⟦lam q _ e⟧ = returnT (λ a → ⟦e⟧ (dγ,a))`, so agreement = the body
  -- `check-agreeV` lifted through the bound value (funext over `a` then fuel `j`).
  -- Every non-arrow target fails ⇒ absurd success-eq.
  check-agreeV ctx (Raw.RLam x body) (A ⇒[ mk-kind q π ] B) (acc rec) eq dγ
    with E.checkElabV (extendNamedCtx ctx x A) body B in eqBody | eq
  ... | failure _ , _ | ()
  ... | success (q' ∷ᵘ Ψ) bodyE d fr , wBody | eq₁ with E.decideLeq q' q | eq₁
  ... | just leq | refl =
          lam-agree {ctx = ctx} {A = A} {B = B} {π = π} q q' leq bodyE (realize wBody)
            (λ E → check-agreeV (extendNamedCtx ctx x A) body B (rec (mC-sub ≤-refl)) eqBody E)
            dγ
  ... | nothing | ()
  check-agreeV ctx (Raw.RLam x body) Unit _ ()
  check-agreeV ctx (Raw.RLam x body) Void _ ()
  check-agreeV ctx (Raw.RLam x body) Int _ ()
  check-agreeV ctx (Raw.RLam x body) Float _ ()
  check-agreeV ctx (Raw.RLam x body) Str _ ()
  check-agreeV ctx (Raw.RLam x body) Buffer _ ()
  check-agreeV ctx (Raw.RLam x body) (_ * _) _ ()
  check-agreeV ctx (Raw.RLam x body) (_ + _) _ ()
  check-agreeV ctx (Raw.RLam x body) (μ-type _) _ ()
  check-agreeV ctx (Raw.RLam x body) (ν-type _) _ ()
  -- RApp: dispatch on the app-head view; t-embed views delegate to infer,
  -- the rest route through agree-check-RApp (todo residual for now).
  check-agreeV ctx (Raw.RApp f arg) T (acc rec) eq dγ =
    agree-check-RApp ctx f arg T (E.classifyAppHeadView f) refl eq
      (λ p → infer-agreeV ctx (Raw.RApp f arg) (rec (infer<check (Raw.RApp f arg))) p)
      (λ {T'} p → check-agreeV ctx arg T' (rec (mC-sub (μ<-r (μ f) (μ arg)))) p)
      (λ p → infer-agreeV ctx arg (rec (mIC-sub (μ<-r (μ f) (μ arg)))) p)
      (λ p → given-agreeV ctx arg _ _ (rec (mC-sub (μ<-r (μ f) (μ arg)))) p)
      (λ ctx' e' h p → check-agreeV ctx' e' _ (rec (mC-sub h)) p)
      (λ ctx' e' h p → infer-agreeV ctx' e' (rec (mIC-sub h)) p) dγ
  -- RAna: no infer rule (`inferElabV` always fails) and no check rule either, so
  -- the generic `checkElabV` fallback (`with inferElabV ctx e`) is always
  -- `failure` ⇒ success-eq absurd.
  check-agreeV ctx (Raw.RAna a e) T (acc rec) eq dγ =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RAna a e) (rec (infer<check (Raw.RAna a e))) p) dγ
  -- RVar (the ONLY shape that reached the former catch-all). Infer-success bridges
  -- through the mode switch (`T' <:? T`, D226), exactly like `ahv-apply`. Infer-failure dispatches the bare builtins / poly to
  -- their PRECISE named obligations (each `refl` once navigated; poly = the gap).
  -- D136: a bare `RVar` has no builtin dispatch left. The eight-way
  -- `classifyBareBuiltin` split is gone; on infer-failure the elaborator goes
  -- straight to the poly fallback, which is the one residual that remains.
  check-agreeV ctx (Raw.RVar x) T (acc rec) eq dγ
    with E.inferElabV ctx (Raw.RVar x) in ieq | eq
  ... | success T' Ψ' eE' d' f' , wi | eq'
        with T' <:? T | eq'
  ... | yes p | refl =
            cong (fmapT ⟦ p ⟧<:) (infer-agreeV ctx (Raw.RVar x) (rec (infer<check (Raw.RVar x))) ieq dγ)
  ... | no _ | ()
  check-agreeV ctx (Raw.RVar x) T (acc rec) eq dγ
    | failure fe , snd | eq' = check-agreeV-RVar-poly-todo ctx x T eq' dγ


  -- Plan 0.94 §10: the domain-given mode, at the check measure (it synthesizes
  -- the SAME expression as its fallback, one phase down).
  given-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (A : Type) (π : Purity) (ac : Acc _<_ (mCheck e))
    {B Ψ se d fr} {w : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ}
    (eq : E.elabGivenV ctx e A π ≡ (success B Ψ se d fr , w))
    → ∀ (dγ : Env ctx Ψ) → SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize-d w ⟧ˢ fmt dγ
  given-agreeV ctx (Raw.RLam x body) A π (acc rec) eq dγ
    with E.inferElabV (extendNamedCtx ctx x A) body in eqBody | eq
  ... | failure _ , _ | ()
  ... | success B (q' ∷ᵘ Ψ) bodyE d fr , wBody | eq₁ with E.decideLeq q' Many | eq₁
  ... | nothing | ()
  ... | just leq | refl =
          lam-agree {ctx = ctx} {A = A} {B = B} {π = π} Many q' leq bodyE (realize-infer wBody)
            (λ E → infer-agreeV (extendNamedCtx ctx x A) body (rec (mIC-sub ≤-refl)) eqBody E)
            dγ
  given-agreeV ctx (Raw.RResolved cn) A π (acc rec) eq dγ =
    agree-given-leaf ctx cn A π (E.classifyAppHeadView (Raw.RResolved cn))
      (E.inferElabV ctx (Raw.RResolved cn)) eq
      (λ p → infer-agreeV ctx (Raw.RResolved cn) (rec (infer<check (Raw.RResolved cn))) p) dγ
  given-agreeV ctx (Raw.RApp f g) A π (acc rec) eq dγ =
    agree-given-app ctx f g A π (E.classifyAppHeadView f) (E.inferElabV ctx (Raw.RApp f g)) eq
      (λ p → infer-agreeV ctx (Raw.RApp f g) (rec (infer<check (Raw.RApp f g))) p)
      (λ ctx' e' h p → given-agreeV ctx' e' _ _ (rec (mC-sub h)) p)
      (λ ctx' e' h p → infer-agreeV ctx' e' (rec (mIC-sub h)) p) dγ
  given-agreeV ctx e@(Raw.RVar x) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RQualified n a) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RLet x e₁ e₂) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RPair a b) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RDestruct sc xl l xr r) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@Raw.RUnit A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RInt n) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RFloat i f′ l p) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RStringLit t) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RAnnot e′ T₀) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RBinOp op a b) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RUnaryOp op e′) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ
  given-agreeV ctx e@(Raw.RAna a e′) A π (acc rec) eq dγ =
    agree-given-infer A π (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e (rec (infer<check e)) p) dγ

------------------------------------------------------------------------
-- THE BRIDGE (Plan 0.50: de-island). `realize-agrees` of the EXACT type
-- `RealizeBridge`/`Compile.main-realize-agrees` consume. Mirrors `check-sound`'s
-- own case-split (`checkElab = proj₁ ∘ checkElabV`): casing `checkElabV` reduces
-- `cc` to a `success`/`failure` equation; `success` ⇒ the goal is `check-agreeV`'s
-- conclusion; `failure` is absurd. RealizeBridge re-exports this.
------------------------------------------------------------------------
realize-agrees : ∀ (ctx : NamedCtx) (e : RawExpr) (A : Type)
  {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  (cc : E.checkElab ctx e A ≡ success Ψ se d f)
  (dγ : Env ctx Ψ) →
  SD.⟦ se ⟧ˢ fmt dγ ≡ SD.⟦ realize (check-sound ctx e A cc) ⟧ˢ fmt dγ
realize-agrees ctx e A cc dγ with E.checkElabV ctx e A in eqV
... | success Ψ' eE' d' fr' , w' with cc
... | refl = check-agreeV ctx e A (<-wellFounded (mCheck e)) eqV dγ
realize-agrees ctx e A cc dγ | failure _ , _ with cc
... | ()
