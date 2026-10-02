-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Completeness
--
-- Plan 0.3, gap G2 (completeness direction): if the declarative
-- judgment derives `ctx ⊢ e ∶ A ⨾ Ψ`, the operational type-checker
-- succeeds with the matching type + usage.
--
-- Soundness (in `Once.TypeCheck.Soundness`) goes the other way:
-- if the elaborator succeeds, the judgment holds. Together they
-- give `inferElab-succeeds ⟺ judgment-derivable`.
--
-- Structure:
--   * `infer-complete`: for judgments whose outermost rule matches
--     an infer-mode clause (all rules except `t-lam`), show
--     `inferElab` succeeds. `t-lam`'s derivation has shape
--     `ctx ⊢ RLam x body ∶ (A ⇒[ q ] B) ⨾ Ψ`, and `inferElab`
--     rejects `RLam` regardless of its sub-derivation — so the
--     single `t-lam` case has to be excluded.
--   * `check-complete-lam`: for the `t-lam` rule, show `checkElab`
--     at the function type succeeds.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G2.
------------------------------------------------------------------------
module Once.TypeCheck.Completeness where
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.String using (String; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (∃; ∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
open import Data.String.Properties as StrProp using (_≟_)
open import Once.Type as T using (Type; Unit; Int; Str; Void; Float; Buffer;
                                  _*_; _+_; _⇒[_]_; Quantity; _≤q_;
                                  Zero; One; Many)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RResolved; RInt; RStringLit; RUnit; RAnnot; RPair;
         ClosedLiftShape; cls-var; cls-qual; cls-res; cls-let; cls-destr;
         cls-unit; cls-str; cls-annot; cls-binop)
open import Once.CanonicalName using (CanonicalName; showCanonical; gen; gen≢bare; NotGenerator; GenWord; genWord?; genWord?-no)
open import Once.TypeCheck.ElaborateProofs
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport; inferElabV; checkElabV;
         _≟T_; embedOrSubsume; VerifiedInferResult; isRIntVliftTarget?;
         classifyAppHead; classifyAppHeadView; ahv-other;
         classifyAppHead-nothing⇒view-other; AppHeadView; inspectWellFormedF;
         wfv-yes; wfv-no; classifyRPairTarget; rpt-vlift; rpt-other;
         via; apply-pure; apply-eff)
open import Once.TypeCheck.Judgment
import Once.TypeCheck.Elaborate as E
import Data.Unit
open import Once.Functor.Translate using (WellFormedF; IsConcrete; con-base; con-fun; IsBaseType)
-- PLAN 0.80 A: the rules carry PROPERTIES now, so completeness recovers the
-- decider's answer from the property here rather than reading it off a premise.
open import Once.TypeCheck.DeciderComplete
  using (isGround-complete-at; ¬Ground-isGround-inj₂; wellFormedF?-complete-at)
open import Once.Type.Rigid using (RigidFree; rigidFree?; rigidFree?-complete)
open import Once.Functor.Decide using (wellFormedF?; isConcrete?; isBaseType?;
  isConcrete?-complete; isBaseType?-complete)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys;
  inspectLookupLocal; inspectLookupImport; llv-found; llv-not-found; liv-found; liv-not-found)
open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_; [])
  renaming (Expr to SExpr)
-- Plan 0.49 / D063: morphism-completeness, proven by induction on ⊢ᵐ
-- (12/15 cases/m-cata/m-named are scoped postulates there).
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
import Data.String.Properties

-- Supplementary imports for the MERGED morph-elab/StrongElab/eff-complete block.
open import Data.Empty using (⊥)
open import Once.IR using (IR; Heap)
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Denotation.Realize using ()
open import Once.Surface.Syntax as Srf using (Expr; lift-morphism)
open import Once.Type using (Functor; μ-type; ⟦_⟧T)
open import Once.Type.Sub using (_<:_; _<:?_; <:-refl; _⊑π_; _⊑π?_; ⊑-pure; sub-int; sub-float; sub-str; sub-unit; sub-prod; sub-sum)
open import Once.Type.DecEq using (_≟T_; _≟F_)
open import Once.TypeCheck.Classify using (lookupLocal; lookupImport; lookupPolyPrefix⇒lookupPoly;
  inspectLookupLocal; inspectLookupImport; llv-found; llv-not-found; liv-found; liv-not-found;
  GenView; classifyGen; gv-id; gv-fst; gv-snd; gv-terminal; gv-initial; gv-inl; gv-inr;
  gv-unit; gv-other)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Once.TypeCheck.ModeAgreement using (mode-agree-ic; mode-agree-dc)
open import Once.TypeCheck.ElaborateProofs using (
  checkCaseGo; VerifiedCheckResult; checkElab-fallback-RUnaryOp-sub; checkElab-fallback-RApp-apply-infer;
  elabGivenV; elabGivenLeaf; elabGivenApp; given-infer; given-cata; checkCompose-g; checkCompose-f;
  inferSpine; VerifiedGivenResult; inferElabV-RVar-fail-bridge;
  inspectWellFormedF; wfv-no; wfv-yes;
  checkCataGo; cata-go-canonical; checkCataGo-J; checkCataGoV-pure-J; checkCataGo-just-success;
  checkAnaGo; checkAnaGo-J; checkAnaGoV-J; checkAnaGo-just-success;
  inferOutGo; inferOutGo-J;
  checkCata-eff-strong-hlp;
  -- the literal view the negation dispatch takes (plan 0.74 J6 step 3 for
  -- `RInt`, plan 0.73 F3 for `RFloat`)
  NegOperandView; nov-int; nov-float; nov-other; negOperandView)


-- The per-rule lemmas (split for the 30 s per-module check budget).
open import Once.TypeCheck.Completeness.Rules

------------------------------------------------------------------------
-- Plan 0.94 §10 / D230: the domain-given mode, the two compose routes and the
-- spine. Non-recursive helpers here; the recursion is in the mutual block.
------------------------------------------------------------------------

-- A synthesizing term reaches `given-infer` — its shape is not one the
-- domain-given mode takes apart. The generator leaves it could name are
-- exactly the ones `NotGenerator` rules out.
private
  leaf-route : ∀ (ctx : NamedCtx) (cn : CanonicalName) (A : Type) (π : T.Purity)
                 (r : VerifiedInferResult ctx (RResolved cn))
             → NotGenerator cn → (vw : AppHeadView (RResolved cn))
             → elabGivenLeaf ctx cn A π vw r ≡ given-infer ctx (RResolved cn) A π r
  leaf-route ctx ._ A π r (¬id ∷ᴬ _) Once.TypeCheck.ElaborateProofs.ahv-id = ⊥-elim (¬id refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ ¬fst ∷ᴬ _) Once.TypeCheck.ElaborateProofs.ahv-fst = ⊥-elim (¬fst refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ ¬snd ∷ᴬ _) Once.TypeCheck.ElaborateProofs.ahv-snd = ⊥-elim (¬snd refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ ¬t ∷ᴬ _) Once.TypeCheck.ElaborateProofs.ahv-terminal = ⊥-elim (¬t refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ ¬i ∷ᴬ _) Once.TypeCheck.ElaborateProofs.ahv-initial = ⊥-elim (¬i refl)
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-inl = refl
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-inr = refl
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-curry = refl
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-apply = refl
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-In = refl
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-cata = refl
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-ana = refl
  leaf-route ctx ._ A π r _ Once.TypeCheck.ElaborateProofs.ahv-Out = refl
  leaf-route ctx cn A π r _ ahv-other = refl

  app-other-route : ∀ (ctx : NamedCtx) (f x : RawExpr) (A : Type) (π : T.Purity)
                      (r : VerifiedInferResult ctx (Raw.RApp f x))
                  → classifyAppHeadView f ≡ ahv-other
                  → elabGivenApp ctx f x A π (classifyAppHeadView f) r ≡ given-infer ctx (Raw.RApp f x) A π r
  app-other-route ctx f x A π r eq rewrite eq = refl

-- Plan 0.103 phase 2b: the domain-given POLYMORPHIC head is elaborated as the
-- derivation says (`d-poly`): each de-withed stage reduces on its decided
-- premise, and the elaborator's codomain is the derivation's by determinacy.
module DPoly where
  open import Once.TypeCheck.Elaborate
    using (given-var; given-poly; given-poly-g; given-poly-a; given-poly-d; given-poly-m; given-poly-π;
           isGround-inj₂→¬Ground)
  open import Once.Type.Match using (instantiate; Subst)
  open import Once.Type.Instance using (instantiate-complete; instantiate-sound)
  open import Once.Type.Determined using (codVarsInDom?; cod-determined; arrowSchema?)
  open import Once.Type.Sub using (_⊑π?_)
  open import Once.Type.Rigid using (KindedInstance; kindedInstance?)
  open import Once.TypeCheck.Classify using (lookupPolyPrefix; PolyCtx)
  open import Relation.Nullary using (yes; no)
  open import Data.String using (String)
  open import Data.Sum using (inj₂)
  open import Data.Unit using (tt)
  open import Data.Empty using (⊥-elim)

  ⇒-parts : ∀ {a b c d : Type} {k k′} → (a T.⇒[ k ] b) ≡ (c T.⇒[ k′ ] d) → (a ≡ c) × (b ≡ d)
  ⇒-parts refl = refl , refl

  arrow-parts : ∀ {s sd sc : T.PolyType} {π′} {A B : Type} (θ : String → Type)
    → T.ArrowSchema s sd sc π′ → T.substPoly θ s ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)
    → (T.substPoly θ sd ≡ A) × (T.substPoly θ sc ≡ B)
  arrow-parts θ T.as-pure e = ⇒-parts e
  arrow-parts θ T.as-eff  e = ⇒-parts e

  gp-eq : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity) err ll eL li eI lp eP
    → given-poly ctx x A π err (lookupLocal ctx x) refl (lookupImport (NamedCtx.imports ctx) x) refl
        (lookupPolyPrefix (NamedCtx.polys ctx) x) refl
      ≡ given-poly ctx x A π err ll eL li eI lp eP
  gp-eq ctx x A π err .(lookupLocal ctx x) refl .(lookupImport (NamedCtx.imports ctx) x) refl
    .(lookupPolyPrefix (NamedCtx.polys ctx) x) refl = refl

  gg-eq : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity) err schema {body prefix} eL eI
    (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ig eG
    → given-poly-g ctx x A π err schema eL eI eP (T.isGround schema) refl ≡ given-poly-g ctx x A π err schema eL eI eP ig eG
  gg-eq ctx x A π err schema eL eI eP .(T.isGround schema) refl = refl

  gm-eq : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity) err {schema sd sc π′ body prefix} eL eI
    (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc) mσ eS
    → given-poly-m ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl
      ≡ given-poly-m ctx x A π err eL eI eP ¬g as inc mσ eS
  gm-eq ctx x A π err {sd = sd} eL eI eP ¬g as inc .(instantiate sd A) refl = refl

  -- The codomain the elaborator computes IS the derivation's.
  at-π : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity) err
    {B : Type} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc) (θ₀ : String → Type) (e₀ : T.substPoly θ₀ sd ≡ A)
    → T.substPoly θ₀ sc ≡ B → π′ ⊑π π → KindedInstance schema (A T.⇒[ T.mk-kind T.Many π′ ] B)
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly-π ctx x A π err eL eI eP ¬g as inc θ₀ e₀ (π′ ⊑π? π)) ≡ success B Surface.zeroUsage eE d f
  at-π ctx x A π err {π′ = π′} {schema = schema} {sc = sc} eL eI eP ¬g as inc θ₀ e₀ refl g ki with π′ ⊑π? π
  ... | no ¬g′ = ⊥-elim (¬g′ g)
  ... | yes _ with kindedInstance? schema (A T.⇒[ T.mk-kind T.Many π′ ] T.substPoly θ₀ sc)
  ...   | yes _ = _ , _ , _ , refl
  ...   | no ¬k = ⊥-elim (¬k ki)

  at-m : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity) err
    {B : Type} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Type) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly-m ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl) ≡ success B Surface.zeroUsage eE d f
  at-m ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g as inc θ eθ g ki =
    let (ed , ec) = arrow-parts θ as eθ
        (σ , eS)  = instantiate-complete sd A (θ , ed)
        θ₀        = proj₁ (instantiate-sound sd A eS)
        e₀        = proj₂ (instantiate-sound sd A eS)
        eB        = trans (cod-determined {sd} {sc} inc θ₀ θ (trans e₀ (sym ed))) ec
        (eE , d , f , r) = at-π ctx x A π err eL eI eP ¬g as inc θ₀ e₀ eB g ki
    in eE , d , f , trans (cong proj₁ (gm-eq ctx x A π err eL eI eP ¬g as inc (just σ) eS)) r

  from-arrow : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity) err
    {B : Type} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Type) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly-a ctx x A π err eL eI eP ¬g (arrowSchema? schema)) ≡ success B Surface.zeroUsage eE d f
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-pure inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-pure inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-eff inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-eff inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)

  -- The whole chain, from the lookups (the head's inference has failed).
  from-lookups : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity) err
    {B : Type} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix}
    (eL : lookupLocal ctx x ≡ nothing) (eI : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
    (eP : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) (¬g : ¬ T.Ground schema)
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Type) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly ctx x A π err (lookupLocal ctx x) refl (lookupImport (NamedCtx.imports ctx) x) refl
                 (lookupPolyPrefix (NamedCtx.polys ctx) x) refl) ≡ success B Surface.zeroUsage eE d f
  from-lookups ctx x A π err {schema = schema} eL eI eP ¬g as inc θ eθ g ki =
    let eG = ¬Ground-isGround-inj₂ schema ¬g
        (eE , d , f , r) = from-arrow ctx x A π err eL eI eP (isGround-inj₂→¬Ground schema eG) as inc θ eθ g ki
    in eE , d , f ,
       trans (cong proj₁ (gp-eq ctx x A π err nothing eL nothing eI (just _) eP))
         (trans (cong proj₁ (gg-eq ctx x A π err schema eL eI eP (inj₂ tt) eG)) r)

-- A non-ground telescope entry does not infer.
poly-head-fails : ∀ (ctx : NamedCtx) (x : String) {schema body prefix}
  → lookupLocal ctx x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → Once.TypeCheck.Classify.lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ T.Ground schema
  → inferElabV ctx (RVar x) ≡ (failure (Once.TypeCheck.ElaborateProofs.UnboundVariable x) , Data.Unit.tt)
poly-head-fails ctx x {schema} eL eI eP ¬g =
  Once.TypeCheck.ElaborateProofs.inferElabV-RVar-fail-bridge ctx x eL eI
    (Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground ctx x eL eI
       (Once.TypeCheck.Classify.lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x eP) (¬Ground-isGround-inj₂ schema ¬g))

-- Plan 0.103 phase 2b: a variable head that INFERS is given through `d-infer`.
var-route : ∀ (ctx : NamedCtx) (x : String) (A : Type) (π : T.Purity)
  (r : VerifiedInferResult ctx (RVar x)) {B Ψ eE d f}
  → proj₁ r ≡ success B Ψ eE d f
  → Once.TypeCheck.ElaborateProofs.given-var ctx x A π r ≡ given-infer ctx (RVar x) A π r
var-route ctx x A π (success _ _ _ _ _ , _) _ = refl
var-route ctx x A π (failure _ , _) ()

given-infer-route : ∀ {ctx : NamedCtx} {e : RawExpr} {T : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ e ∶ T ⨾ Ψ → ∀ (A : Type) (π : T.Purity)
  → ∃[ eE ] ∃[ d ] ∃[ f ] proj₁ (inferElabV ctx e) ≡ success T Ψ eE d f
  → elabGivenV ctx e A π ≡ given-infer ctx e A π (inferElabV ctx e)
given-infer-route (t-int _) A π _ = refl
given-infer-route (t-float _ _ _ _) A π _ = refl
given-infer-route (t-str _) A π _ = refl
given-infer-route t-unit A π _ = refl
given-infer-route t-unit-var A π _ = refl
given-infer-route {ctx} (t-var-local {x = x} _) A π (_ , _ , _ , ok) = var-route ctx x A π (inferElabV ctx (RVar x)) ok
given-infer-route (t-var-qualified _ _) A π _ = refl
given-infer-route {ctx} (t-var-resolved {cn = cn} ng _ _) A π _ =
  leaf-route ctx cn A π (inferElabV ctx (RResolved cn)) ng (classifyAppHeadView (RResolved cn))
given-infer-route {ctx} (t-var-import {x = x} _ _ _ _) A π (_ , _ , _ , ok) = var-route ctx x A π (inferElabV ctx (RVar x)) ok
given-infer-route {ctx} (t-var-poly-instantiate-infer {x = x} _ _ _ _ _) A π (_ , _ , _ , ok) = var-route ctx x A π (inferElabV ctx (RVar x)) ok
given-infer-route (t-annot _ _) A π _ = refl
given-infer-route (t-pair _ _) A π _ = refl
given-infer-route (t-neg _) A π _ = refl
given-infer-route (t-neg-float _ _ _ _) A π _ = refl
given-infer-route (t-let _ _) A π _ = refl
given-infer-route (t-case _ _ _) A π _ = refl
given-infer-route (t-binop-arith _ _ _) A π _ = refl
given-infer-route (t-binop-arith-float _ _ _) A π _ = refl
given-infer-route (t-binop-arith-float-il _ _ _) A π _ = refl
given-infer-route (t-binop-arith-float-ir _ _ _) A π _ = refl
given-infer-route (t-binop-cmp _ _ _) A π _ = refl
given-infer-route (t-id-app _) A π _ = refl
given-infer-route (t-fst-app _) A π _ = refl
given-infer-route (t-snd-app _) A π _ = refl
given-infer-route (t-terminal-app _) A π _ = refl
given-infer-route (t-apply-app-infer _) A π _ = refl
given-infer-route (t-apply-eff-app-infer _) A π _ = refl
given-infer-route (t-Out-app-infer _ _ _) A π _ = refl
given-infer-route (t-Out-eff-app-infer _ _ _) A π _ = refl
given-infer-route {ctx} (t-app {f = f} {x = x} eqAH _ _) A π _ =
  app-other-route ctx f x A π (inferElabV ctx (Raw.RApp f x)) (classifyAppHead-nothing⇒view-other eqAH)
given-infer-route {ctx} (t-effApp {f = f} {x = x} eqAH _ _) A π _ =
  app-other-route ctx f x A π (inferElabV ctx (Raw.RApp f x)) (classifyAppHead-nothing⇒view-other eqAH)
given-infer-route {ctx} (t-app-spine {f = f} {arg = x} eqAH _ _) A π _ =
  app-other-route ctx f x A π (inferElabV ctx (Raw.RApp f x)) (classifyAppHead-nothing⇒view-other eqAH)

-- `d-infer`: the inferred arrow's domain converts back, its grade up.
given-infer-complete : ∀ {ctx : NamedCtx} {e : RawExpr} {A A′ B : Type} {π π′ : T.Purity}
    {Ψ : Surface.Usage (NamedCtx.size ctx)} {eE : _} {d f : ℕ}
    (r : VerifiedInferResult ctx e)
  → proj₁ r ≡ success (A′ T.⇒[ T.mk-kind T.Many π′ ] B) Ψ eE d f
  → A <: A′ → π′ ⊑π π
  → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] proj₁ (given-infer ctx e A π r) ≡ success B Ψ eE′ d′ f′
given-infer-complete {A = A} {A′} {π = π} {π′} (success _ _ _ _ _ , _) refl a g
  with A <:? A′ | π′ ⊑π? π
... | yes _ | yes _ = _ , _ , _ , refl
... | no ¬a | _     = ⊥-elim (¬a a)
... | yes _ | no ¬g = ⊥-elim (¬g g)

-- `d-cata`: the algebra synthesizes the arrow the fold needs.
given-cata-complete : ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Functor} {A : Type} {π : T.Purity}
    (wfF : WellFormedF F) {eE : _} {d f : ℕ}
    (r : VerifiedInferResult (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg)
  → proj₁ r ≡ success (⟦ F ⟧T A T.⇒[ T.mk-kind T.Many π ] A) [] eE d f
  → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] proj₁ (given-cata ctx alg F π wfF r) ≡ success A zeroUsage eE′ d′ f′
given-cata-complete {F = F} {A} {π} wfF (success _ _ _ _ _ , _) refl
  with (⟦ F ⟧T A T.⇒[ T.mk-kind T.Many π ] A) ≟T (⟦ F ⟧T A T.⇒[ T.mk-kind T.Many π ] A)
... | yes refl = _ , _ , _ , refl
... | no ¬p = ⊥-elim (¬p refl)

-- compose, `f`'s route: `f` synthesizes, converts, and `g` is checked at the
-- middle it names.
compose-f-complete : ∀ {ctx : NamedCtx} (f g : RawExpr) (A B C C′ : Type) (π π′ : T.Purity)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)} {fE : _} {gE : _} {df ff dg fg : ℕ}
  → inferElab ctx f ≡ success (B T.⇒[ T.mk-kind T.Many π′ ] C′) Ψ₁ fE df ff
  → (B T.⇒[ T.mk-kind T.Many π′ ] C′) <: (B T.⇒[ T.mk-kind T.Many π ] C)
  → checkElab ctx g (A T.⇒[ T.mk-kind T.Many π ] B) ≡ success Ψ₂ gE dg fg
  → ∃[ eE ] ∃[ d ] ∃[ fr ] proj₁ (checkCompose-f ctx f g A C π) ≡ success (Ψ₁ +ᵘ (T.Many *ᵘ Ψ₂)) eE d fr
compose-f-complete {ctx} f g A B C C′ π π′ eqF p eqG
  with inferElabV ctx f | eqF
... | success _ _ _ _ _ , _ | refl
    with (B T.⇒[ T.mk-kind T.Many π′ ] C′) <:? (B T.⇒[ T.mk-kind T.Many π ] C)
...   | no ¬p = ⊥-elim (¬p p)
...   | yes _ with checkElabV ctx g (A T.⇒[ T.mk-kind T.Many π ] B) | eqG
...     | success _ _ _ _ , _ | refl = _ , _ , _ , refl

-- compose, the elaborator's order: `g`'s route first. Where it succeeds on a
-- derivation built on `f`'s route, the two agree because usage is the term's
-- (`ModeAgreement`), not the route's.
compose-g-complete : ∀ {ctx : NamedCtx} (f g : RawExpr) (A B C C′ : Type) (π π′ : T.Purity)
    (rG : VerifiedGivenResult ctx g A π)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)} {fE : _} {gE : _} {df ff dg fg : ℕ}
  → ctx ⊢ᵢ f ∶ (B T.⇒[ T.mk-kind T.Many π′ ] C′) ⨾ Ψ₁
  → ctx ⊢ᶜ g ∶ (A T.⇒[ T.mk-kind T.Many π ] B) ⨾ Ψ₂
  → inferElab ctx f ≡ success (B T.⇒[ T.mk-kind T.Many π′ ] C′) Ψ₁ fE df ff
  → (B T.⇒[ T.mk-kind T.Many π′ ] C′) <: (B T.⇒[ T.mk-kind T.Many π ] C)
  → checkElab ctx g (A T.⇒[ T.mk-kind T.Many π ] B) ≡ success Ψ₂ gE dg fg
  → ∃[ eE ] ∃[ d ] ∃[ fr ] proj₁ (checkCompose-g ctx f g A C π rG) ≡ success (Ψ₁ +ᵘ (T.Many *ᵘ Ψ₂)) eE d fr
compose-g-complete f g A B C C′ π π′ (failure _ , _) wf dg eqF p eqG =
  compose-f-complete f g A B C C′ π π′ eqF p eqG
compose-g-complete {ctx} f g A B C C′ π π′ (success B″ Ψg″ gE″ dg″ fg″ , wG) wf dg eqF p eqG
  with checkElabV ctx f (B″ T.⇒[ T.mk-kind T.Many π ] C)
... | failure _ , _ = compose-f-complete f g A B C C′ π π′ eqF p eqG
... | success Ψf″ fE″ df″ ff″ , wF
      with mode-agree-ic wf wF | mode-agree-dc wG dg
...   | refl | refl = _ , _ , _ , refl

-- The spine, once the head is known not to synthesize.
infer-complete-RApp-spine :
  ∀ {ctx : NamedCtx} (f x : RawExpr) {X B : Type} {err : _}
    {Ψf Ψx : Surface.Usage (NamedCtx.size ctx)} {fE : _} {xE : _} {df ff dx fx : ℕ}
  → Once.TypeCheck.ElaborateProofs.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ failure err
  → inferElab ctx x ≡ success X Ψx xE dx fx
  → proj₁ (elabGivenV ctx f X T.pure) ≡ success B Ψf fE df ff
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x) ≡ success B (Ψf +ᵘ (T.Many *ᵘ Ψx)) eE d f'

infer-complete-RApp-spine {ctx} f x {X} {B} eqAH eqF eqX eqG
  rewrite cong proj₁ (viewBridge {ctx} {f} {x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | cong proj₁ (otherBridge {ctx} {f} {x} nothing eqAH)
  with inferElabV ctx f | eqF
... | failure _ , _ | refl
    with inferElabV ctx x | eqX
...   | success _ _ _ _ _ , _ | refl
      with elabGivenV ctx f X T.pure | eqG
...     | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- Effectful RApp completeness
--
-- Same structure as `infer-complete-RApp-generic` but for the case
-- where `f : Eff A B`. After `classifyAppHead-nothing⇒view-other`
-- exposes the `ahv-other` branch, `asFun` sees `success (A ⇒[ mk-kind Many eff ] B) ...`
-- and takes the `isEff` case; the body mirrors `isFun` but emits
-- `Surface.effApp`. The check-mode fallback is
-- `checkElab-fallback-RApp-generic`, reusable as-is because its
-- statement only mentions the outer `inferElab (RApp f x)`, not the
-- inner function-vs-effect dispatch.
------------------------------------------------------------------------

-- (defined above with infer-complete-RApp-generic)

------------------------------------------------------------------------
-- Full-walk completeness — enabled by the G2(a) judgment split
--
-- With mutual ⊢ᵢ / ⊢ᶜ judgments and the `classifyAppHead f ≡ nothing`
-- premise on `t-app`, the two mismatches that previously blocked a
-- full walk are now structural invariants:
--   * t-lam lives only in ⊢ᶜ, so infer-mode sub-derivations can't
--     use it.
--   * t-app doesn't shadow the polymorphic-builtin specialisations.
--
-- The walk is a direct mutual structural recursion on derivations.
------------------------------------------------------------------------

-- (Judgment is already fully opened at the top of this file; the morphism realm
-- `_⊢ᵐ_∶_⇨_`, `t-morph-lift`, and the `m-*` constructors are in scope from there.
-- The former redundant `using`-list re-open was removed in the D063 collapse.)


------------------------------------------------------------------------
-- Mutual full walk (G2 completeness — both directions)
--
-- With the `AppHeadView` refactor unblocking `checkElab-fallback-RApp-
-- generic` and the removal of the specialised bare-builtin check-mode
-- clauses (G2 decision) eliminating the RVar-shadow impedance, the
-- walk now closes.
------------------------------------------------------------------------

open Once.TypeCheck.ElaborateProofs
  using (checkElab-fallback-RInt; checkElab-fallback-RFloat; checkElab-fallback-RStringLit;
         checkElab-fallback-RUnit; checkElab-fallback-RVar-unit;
         checkElab-fallback-RVar-id; checkElab-fallback-RVar-fst;
         checkElab-fallback-RVar-snd; checkElab-fallback-RVar-terminal; checkElab-fallback-RVar-terminalV;
         checkElab-fallback-RVar-initial; checkElab-fallback-RVar-inl;
         checkElab-fallback-RVar-inr;
         checkElab-fallback-RApp-In; checkElab-fallback-RApp-apply; checkElab-fallback-RApp-apply-effclosure;
         checkElab-fallback-RVar-poly; checkElab-fallback-RVar-poly-infer;
         checkElab-fallback-RQualified; checkElab-fallback-RResolved; checkElab-fallback-RAnnot;
         checkElab-fallback-RLet;
         checkElab-fallback-RDestruct; checkElab-fallback-RUnaryOp;
         checkElab-fallback-RBinOp;
         checkElab-fallback-RApp-id; checkElab-fallback-RApp-fst;
         checkElab-fallback-RApp-snd; checkElab-fallback-RApp-terminal; checkElab-fallback-RApp-Out;
         checkElab-fallback-RApp-generic)

-- RVar case: covers both local and import lookups (and "unit"). The
-- fallback lemma takes the inferElab-success equation uniformly.
--
-- Plan 0.6 Phase C.7: `checkElab-RVar` dispatches via
-- `classifyBareBuiltin x` to specialised clauses for each bare
-- polymorphic builtin. The proof mirrors this dispatch — each
-- specialised case rewrites by `eqInf` (pushing lookup-success
-- through), then discharges the `T ≟T T` guard. The proof is
-- uniform across all specialised names because each specialised
-- clause's lookup-success branch is identical in shape.
checkElab-fallback-RVar :
  ∀ {ctx : NamedCtx} {τ : Type} (x : String) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : _} {d f : ℕ}
  → inferElab ctx (Raw.RVar x) ≡ success T Ψ eE d f
  → T <: τ
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RVar x) τ ≡ success Ψ eE' d' f'
-- D136: the bare-`RVar` check path no longer dispatches on
-- `classifyBareBuiltin` (a generator is `RResolved (gen g)`, never a bare
-- name), so the nine-way split this proof used to mirror collapses to the
-- single `embedOrSubsume` reduction.
checkElab-fallback-RVar {ctx} {τ} x T eqInf sb
  with inferElabV ctx (Raw.RVar x) | eqInf
... | success _ _ _ _ _ , _ | refl with T <:? τ
...   | yes _    = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq sb)

-- Plan 0.4 T0 (2026-04-30): completeness gaps for t-embed of
-- t-arr-app-infer / t-apply-app-infer. The elaborator's check-mode
-- for these uses specialised dispatches that don't transport via
-- inferElab → checkElab catchall. The natural fix is recursion on
-- check-complete (t-embed d), which is structurally smaller — but
-- Agda's mutual termination checker rejects it. Soundness is fully
-- proven (sound-RApp-arr, sound-RApp-apply); this gap is on the
-- completeness side only.
-- Completeness-gap-* helpers (formerly postulates) — given a checkElab/
-- inferElab equation on the sub-expression(s), produce the outer
-- checkElab equation. The proofs walk checkElabV-RApp-dispatch at the
-- corresponding ahv-X branch.
completeness-gap-inl-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A}
    {d f : ℕ}
  → checkElab ctx arg A ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (Raw.RResolved (gen "inl")) arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inl-app-check-eq {ctx} arg A B eqC
  with checkElabV ctx arg A | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-inr-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ B}
    {d f : ℕ}
  → checkElab ctx arg B ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (Raw.RResolved (gen "inr")) arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inr-app-check-eq {ctx} arg A B eqC
  with checkElabV ctx arg B | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-initial-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T.Void}
    {d f : ℕ}
  → checkElab ctx arg T.Void ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (Raw.RResolved (gen "initial")) arg) T
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-initial-app-check-eq {ctx} arg T eqC
  with checkElabV ctx arg T.Void | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

-- (Plan 0.52 M1: `completeness-gap-arr-app-check-eq` retired with `t-arr-app-check`.)

-- The ONE bridge for every infer-then-check site (the generic `checkElabV`
-- catch-all is definitionally `embedOrSubsume … (inferElabV …)`): embed at the
-- pure target, SUBSUME at the eff target. (eff side: eff-arrow ≠ inferred
-- pure-arrow, then the A/B `≟T` are reflexive.)
-- CHECK-side J bridge + the resolved lift. Same shape as
-- `inferElabV-RResolved-J`: `checkElabV ctx (RResolved cn) T` dispatches on
-- `classifyGen cn`, so a `RResolved` head cannot reach `embedOrSubsume`
-- without first fixing the view. Under `NotGenerator cn` only `gv-other`
-- survives, and there the dispatch IS `embedOrSubsume`.
checkElabV-RResolved-J :
  ∀ (ctx : NamedCtx) (cn : CanonicalName) (T : Type) (gv : GenView cn)
  → classifyGen cn ≡ gv
  → checkElab ctx (RResolved cn) T
      ≡ proj₁ (Once.TypeCheck.ElaborateProofs.checkElabV-RResolved-dispatch
                 ctx cn T gv (inferElabV ctx (RResolved cn)))
checkElabV-RResolved-J ctx cn T .(classifyGen cn) refl = refl

private
  -- The `case` twin. No `mid` argument, so no `-J` bridge is needed.
  caseGo-success : ∀ {ctx f g A B C} {π : T.Purity}
    {Ψf Ψg : Surface.Usage (NamedCtx.size ctx)}
    {Ef : _} {Eg : _} {Wf : _} {Wg : _} {df ff dg fg : ℕ}
    → checkElabV ctx f (A T.⇒[ T.mk-kind T.Many π ] C)
        ≡ (success Ψf Ef df ff , Wf)
    → checkElabV ctx g (B T.⇒[ T.mk-kind T.Many π ] C)
        ≡ (success Ψg Eg dg fg , Wg)
    → Σ-syntax ℕ λ d → Σ-syntax ℕ λ fr →
        checkCaseGo ctx f g A B C π
          ≡ (success (Ψf Surface.+ᵘ Ψg) (Srf.copair' Ef Eg) d fr
            , t-case-copair-check Wf Wg)
  caseGo-success eqf eqg rewrite eqf | eqg = _ , _ , refl

  -- D127: `cgo-usage` / `ccgo-usage` DELETED. They said compose/case emit
  -- `zeroUsage`, which was true only while the arms were closed. The usage is
  -- now `Ψf +ᵘ Ψg` — that is the whole content of D130 — so the lemmas are not
  -- weakened but FALSE, and their only consumers were the eff-complete family
  -- that went with the realm.

  -- Plan 0.54: `checkCataGo` emits `success zeroUsage …` on its sole success leaf;
  -- recover that usage after a `with`-abstraction loses it (the eff-clause
  -- passthrough branch in `cata-eff-complete`). Mirrors `ccgo-usage`.
  ccatago-usage : ∀ {ctx alg F A} {π : T.Purity} {wfF : WellFormedF F}
    {eqW : wellFormedF? F ≡ just wfF}
    {Ψ : Srf.Usage (NamedCtx.size ctx)} {se d fr w}
    → checkCataGo ctx alg F A π (just wfF) eqW ≡ (success Ψ se d fr , w)
    → Ψ ≡ zeroUsage
  ccatago-usage {ctx} {alg} {F} {A} {π} eq
    with checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
                    alg (⟦ F ⟧T A T.⇒[ T.mk-kind T.Many π ] A) | eq
  ... | failure _ , _ | ()
  ... | success [] algE d fr , wArg | refl = refl

-- D127: the `StrongElab` postulate block that stood here is GONE with the
-- realm. It held the `m-named` follow-up — a bare import elaborating to a
-- closure rather than a direct `IR.SigOp` — which was a statement about
-- morphism EXTRACTION and has no analogue once arms are ordinary terms.
mutual
  check-completeV : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        Σ-syntax (ctx ⊢ᶜ e ∶ A ⨾ Ψ) (λ w →
          checkElabV ctx e A ≡ (success Ψ eE d f , w))
  check-completeV {ctx} {e} {A} d with checkElabV ctx e A | check-complete d
  ... | r , w0 | eE , d' , f , eq rewrite eq = eE , d' , f , w0 , refl

  -- The bidirectional SWITCH lemma `infer ⊆ check`, by structural recursion on the
  -- INFER derivation (genuine subterms — NO `t-embed` re-wrap). `check-complete
  -- (t-embed d)` is now ONE clause delegating here, so this is the single, uniform
  -- switch (was 24 scattered clauses + the `pair-lit` postulate). Neutral forms
  -- reduce via `infer-complete` + the `checkElab-fallback-*` switch; the INTRO form
  -- `t-pair` RECURSES (its components, synthesized in the derivation, must be
  -- re-CHECKED by `checkPairLit`) — the sub-derivations d₁/d₂ are genuine subterms,
  -- so the recursion is structural (this is what the postulate could not express).
  -- D226: the switch lands at any SUPERTYPE of the inferred type. Where the
  -- inferred type is concrete, matching the derivation `p` fixes the target;
  -- elsewhere the fallback lemmas take `p` and the elaborator's `A <:? B`
  -- decides yes.
  iFromInferSub : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ → A <: B
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e B ≡ success Ψ eE d f

  -- Strong (paired `checkElabV`) view of the switch — mirrors `check-completeV`
  -- over `check-complete`, but from the INFER derivation (so a pair's components
  -- are reached without a re-wrap). Feeds `checkPairLit`'s two scrutinees.
  check-completeV-from-infer : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ → A <: B
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        Σ-syntax (ctx ⊢ᶜ e ∶ B ⨾ Ψ) (λ w →
          checkElabV ctx e B ≡ (success Ψ eE d f , w))

  -- `checkElabV (RPair a b) (A * B)` reduces via `checkPairLit` (checkElabV a A /
  -- checkElabV b B). Given the two paired component equations, `rewrite` drives it
  -- to its `success` leaf. NON-recursive (the caller supplies the equations, so the
  -- recursion measure lives in the caller's structural descent, not here).
  pair-lit-reduce : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {aE da fa wA bE db fb wB}
    → checkElabV ctx a A ≡ (success Ψ₁ aE da fa , wA)
    → checkElabV ctx b B ≡ (success Ψ₂ bE db fb , wB)
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RPair a b) (A * B)
          ≡ success (Ψ₁ +ᵘ Ψ₂) eE d f

  check-completeV-from-infer {ctx} {e} {A} {B} d p
    with checkElabV ctx e B | iFromInferSub d p
  ... | r , w0 | eE , d' , f , eq rewrite eq = eE , d' , f , w0 , refl

  pair-lit-reduce eqA eqB rewrite eqA | eqB = _ , _ , _ , refl

  -- The reflexive instance (the former `t-embed` switch).
  iFromInfer : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e A ≡ success Ψ eE d f
  iFromInfer {A = A} d = iFromInferSub d (<:-refl A)

  -- Leaves.
  iFromInferSub {ctx} (t-int n) sub-int = checkElab-fallback-RInt {ctx} n
  iFromInferSub {ctx} (t-float i f l p) sub-float = checkElab-fallback-RFloat {ctx} i f l p
  iFromInferSub {ctx} (t-str s) sub-str = checkElab-fallback-RStringLit {ctx} s
  iFromInferSub {ctx} t-unit sub-unit = checkElab-fallback-RUnit {ctx}
  iFromInferSub {ctx} t-unit-var sub-unit = checkElab-fallback-RVar-unit {ctx}
  iFromInferSub {ctx} (t-var-local {x = x} {A = T} eqLocal) sb =
    let (_ , _ , _ , eqI) = infer-complete {ctx} (t-var-local eqLocal)
    in checkElab-fallback-RVar {ctx} x T eqI sb
  iFromInferSub {ctx} (t-var-qualified {name = n} {alias = a} {T = T} eqImp conc) sb =
    let (_ , _ , _ , eqI) = infer-complete {ctx} (t-var-qualified eqImp conc)
    in checkElab-fallback-RQualified {ctx} n a T eqI sb
  iFromInferSub {ctx} (t-var-resolved {cn = cn} {T = T} ng eqImp conc) sb =
    let (_ , _ , _ , eqI) = infer-complete {ctx} (t-var-resolved ng eqImp conc)
    in checkElab-fallback-RResolved {ctx} cn T eqI sb
  iFromInferSub {ctx} (t-var-import {x = x} {T = T} ¬gw eqLoc eqImp conc) sb =
    let (_ , _ , _ , eqI) = infer-complete {ctx} (t-var-import ¬gw eqLoc eqImp conc)
    in checkElab-fallback-RVar {ctx} x T eqI sb
  -- Plan 0.58 / D071: infer-mode ground telescope reference — same shape as
  -- t-var-import (infer at the declared type, embed at the same type).
  iFromInferSub {ctx} dd@(t-var-poly-instantiate-infer {x = x} {T = T} _ _ _ _ _) sb =
    let (_ , _ , _ , eqI) = infer-complete dd
    in checkElab-fallback-RVar {ctx} x T eqI sb
  iFromInferSub (t-annot {e = e} {T = T} rf d) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-annot rf d)
    in checkElab-fallback-RAnnot e T eqI sb
  -- INTRO form: pair components were synthesized (d₁/d₂ : ⊢ᵢ) but `checkPairLit`
  -- re-CHECKS them — recurse the SWITCH on the genuine sub-derivations.
  iFromInferSub (t-pair {a = a} {b = b} {A = A} {B = B} d₁ d₂) (sub-prod pa pb)
    with check-completeV-from-infer d₁ pa | check-completeV-from-infer d₂ pb
  ... | (_ , _ , _ , _ , eqA) | (_ , _ , _ , _ , eqB) = pair-lit-reduce eqA eqB
  iFromInferSub (t-neg {e = e} d) sub-int =
    let (_ , _ , _ , eqI) = infer-complete (t-neg d)
    in checkElab-fallback-RUnaryOp Raw.OpNeg e T.Int eqI
  -- PLAN 0.73 F3: the switch for `-3.14` is the generic infer→check fallback,
  -- at `Float` instead of `Int`. Nothing recurses — the rule has no premise,
  -- and the infer-side equation is `refl` outright: `negOperandView (RFloat …)`
  -- reduces, so `inferElab ctx (RUnaryOp OpNeg (RFloat i f l p))` is already
  -- the folded literal. Routing through `infer-complete` instead would leave
  -- its three existential witnesses as metas with nothing to solve them.
  iFromInferSub {ctx} (t-neg-float i f l p) sub-float =
    checkElab-fallback-RUnaryOp {ctx} Raw.OpNeg (Raw.RFloat i f l p) T.Float refl
  iFromInferSub (t-let {x = x} {e₁ = e₁} {e₂ = e₂} {B = B} d₁ d₂) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-let d₁ d₂)
    in checkElab-fallback-RLet x e₁ e₂ B eqI sb
  iFromInferSub (t-case {scrut = scrut} {eL = eL} {eR = eR}
                     {xL = xL} {xR = xR} {C = C} dS dL dR) =
    let (_ , _ , _ , eqI) = infer-complete (t-case dS dL dR)
    in checkElab-fallback-RDestruct scrut xL eL xR eR C eqI
  iFromInferSub (t-binop-arith {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Int eqI sb
  iFromInferSub (t-binop-arith-float {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith-float arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Float eqI sb
  iFromInferSub (t-binop-arith-float-il {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith-float-il arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Float eqI sb
  iFromInferSub (t-binop-arith-float-ir {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith-float-ir arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Float eqI sb
  iFromInferSub (t-binop-cmp {op = op} {e₁ = e₁} {e₂ = e₂} cmpEq d₁ d₂) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-cmp cmpEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ (Unit T.+ Unit) eqI sb
  iFromInferSub (t-id-app {e = e} {T = T} d) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-id-app d)
    in checkElab-fallback-RApp-id e T eqI sb
  iFromInferSub (t-fst-app {e = e} {A = A} d) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-fst-app d)
    in checkElab-fallback-RApp-fst e A eqI sb
  iFromInferSub (t-snd-app {e = e} {B = B} d) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-snd-app d)
    in checkElab-fallback-RApp-snd e B eqI sb
  iFromInferSub (t-terminal-app {e = e} d) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-terminal-app d)
    in checkElab-fallback-RApp-terminal e Unit eqI sb
  -- D194: `Out` is an infer head whose check routes through `embedOrSubsume`,
  -- so its switch is `terminal`'s.
  iFromInferSub (t-Out-app-infer {v = v} {F = F} wfF refl d) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-Out-app-infer wfF refl d)
    in checkElab-fallback-RApp-Out v (T.⟦ F ⟧T (T.ν-type F T.pure)) eqI sb
  iFromInferSub (t-Out-eff-app-infer {v = v} {F = F} wfF refl d) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-Out-eff-app-infer wfF refl d)
    in checkElab-fallback-RApp-Out v (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] T.⟦ F ⟧T (T.ν-type F T.eff)) eqI sb
  iFromInferSub (t-apply-app-infer {p = p} {A = A} {B = B} d) sb =
    let (_ , _ , _ , eqI) = infer-complete d
    in checkElab-fallback-RApp-apply p A B eqI sb
  iFromInferSub (t-apply-eff-app-infer {p = p} {A = A} {B = B} d) sb =
    let (_ , _ , _ , eqI) = infer-complete d
    in checkElab-fallback-RApp-apply-effclosure p A B eqI sb
  iFromInferSub (t-app {f = f} {x = x} {B = B} notPoly dF dX) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-app notPoly dF dX)
    in checkElab-fallback-RApp-generic f x B notPoly eqI sb
  iFromInferSub (t-effApp {f = f} {x = x} {B = B} notPoly dF dX) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-effApp notPoly dF dX)
    in checkElab-fallback-RApp-generic f x (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) notPoly eqI sb
  iFromInferSub (t-app-spine {f = f} {arg = x} {T = B} notPoly dX dF) sb =
    let (_ , _ , _ , eqI) = infer-complete (t-app-spine notPoly dX dF)
    in checkElab-fallback-RApp-generic f x B notPoly eqI sb

  infer-complete :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        inferElab ctx e ≡ success A Ψ eE d f

  infer-complete {ctx} (t-int n)   = infer-complete-RInt {ctx} n
  infer-complete {ctx} (t-float i f l p) = _ , _ , _ , refl
  infer-complete {ctx} (t-str s)   = infer-complete-RStringLit {ctx} s
  infer-complete {ctx} t-unit      = infer-complete-RUnit {ctx}
  infer-complete {ctx} t-unit-var  = infer-complete-RVar-unit {ctx}
  infer-complete {ctx} (t-var-local {x = x} eqLocal) =
    infer-complete-RVar-local {ctx} x eqLocal
  infer-complete {ctx} (t-var-qualified {name = name} {alias = alias} eqImp conc) =
    infer-complete-RQualified {ctx} {name} {alias} eqImp conc
  infer-complete {ctx} (t-var-resolved {cn = cn} ng eqImp conc) =
    infer-complete-RResolved {ctx} {cn} ng eqImp conc
  infer-complete {ctx} (t-var-import {x = x} ¬gw eqLoc eqImp conc) =
    infer-complete-RVar-import {ctx} x ¬gw eqLoc eqImp conc
  -- Plan 0.58 / D071: infer-mode ground telescope reference — matching the
  -- type-pin equation as `refl` aligns the conclusion `T` with the declared
  -- `extractGround schema g`, so the elaborator's poly-fallback success
  -- equation IS the obligation.
  infer-complete {ctx} (t-var-poly-instantiate-infer {x = x} {schema = schema} {g = g}
                        eqLoc eqImp polyE eqG refl) =
    checkElab-fallback-RVar-poly-infer {ctx} x eqLoc eqImp
      (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x polyE)
      (isGround-complete-at schema g)
  infer-complete (t-annot {e = e} {T = T} rf d) =
    let (_ , _ , _ , eqC) = check-complete d
    in infer-complete-RAnnot e T rf eqC
  infer-complete (t-pair {a = a} {b = b} d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RPair a b eq₁ eq₂
  infer-complete (t-neg {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RUnaryOp-neg e eqSub
  -- PLAN 0.73 F3. Immediate, exactly as the `RInt` fold's branch is:
  -- `negOperandView (RFloat i f l p)` reduces to `nov-float …`, so the
  -- dispatch reduces straight to the folded literal without consulting the
  -- operand's inference. There is no sub-derivation to recurse on.
  infer-complete (t-neg-float i f l p) = _ , _ , _ , refl
  infer-complete (t-let {x = x} {e₁ = e₁} {e₂ = e₂} d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RLet x e₁ e₂ eq₁ eq₂
  infer-complete
    (t-case {scrut = scrut} {eL = eL} {eR = eR} {xL = xL} {xR = xR} {C = C}
            dS dL dR) =
    let (_ , _ , _ , eqS) = infer-complete dS
        (_ , _ , _ , eqL) = infer-complete dL
        (_ , _ , _ , eqR) = infer-complete dR
    in infer-complete-RDestruct scrut xL eL xR eR C eqS eqL eqR
  infer-complete
    (t-binop-arith {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-arith-float {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith-float op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-arith-float-il {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith-float-il op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-arith-float-ir {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith-float-ir op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-cmp {op = op} {e₁ = e₁} {e₂ = e₂} cmpEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-cmp op cmpEq e₁ e₂ eq₁ eq₂
  infer-complete (t-id-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-id e eqSub
  infer-complete (t-fst-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-fst e eqSub
  infer-complete (t-snd-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-snd e eqSub
  infer-complete (t-terminal-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-terminal e eqSub
  infer-complete (t-Out-app-infer {v = v} {F = F} wfF refl d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-Out v wfF eqSub
  infer-complete (t-Out-eff-app-infer {v = v} {F = F} wfF refl d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-Out-eff v wfF eqSub
  infer-complete (t-apply-app-infer {p = p} {A = A} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-apply p A eqSub
  infer-complete (t-apply-eff-app-infer {p = p} {A = A} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-apply-eff p A eqSub
  -- Plan 0.4 T1, change 1: dX is now a check-mode derivation
  -- (per the t-app/t-effApp signature changes in Judgment).
  -- check-complete gives us the checkElab evidence directly.
  infer-complete (t-app {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = check-complete dX
    in infer-complete-RApp-generic f x A notPoly eqF eqX
  infer-complete (t-effApp {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = check-complete dX
    in infer-complete-RApp-eff f x A notPoly eqF eqX
  -- D230: the spine.
  infer-complete (t-app-spine {f = f} {arg = x} eqAH dX dF) = spine-complete f x eqAH dX dF

  -- The spine. A head that synthesizes is `t-app`'s case (its `⊢ᵈ` can only be
  -- `d-infer`, at the pure grade); any other head has no synthesized type (the
  -- elaborator's head inference fails by computation — `refl` below) and is
  -- taken apart given the argument's type.
  spine-complete : ∀ {ctx : NamedCtx} (f x : RawExpr) {X B : Type}
      {Ψf Ψx : Surface.Usage (NamedCtx.size ctx)}
    → Once.TypeCheck.ElaborateProofs.classifyAppHead f ≡ nothing
    → ctx ⊢ᵢ x ∶ X ⨾ Ψx
    → ctx ⊢ᵈ f ∶ X ⇒[ T.pure ]↦ B ⨾ Ψf
    → ∃[ eE ] ∃[ d ] ∃[ f' ]
        inferElab ctx (Raw.RApp f x) ≡ success B (Ψf +ᵘ (T.Many *ᵘ Ψx)) eE d f'
  spine-complete f x eqAH dX dF@(d-lam _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-complete dX)))) (proj₂ (proj₂ (proj₂ (given-complete dF))))
  spine-complete f x eqAH dX dF@(d-compose _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-complete dX)))) (proj₂ (proj₂ (proj₂ (given-complete dF))))
  spine-complete f x () dX d-id
  spine-complete f x () dX d-fst
  spine-complete f x () dX d-snd
  spine-complete f x () dX d-terminal
  spine-complete f x () dX d-initial
  spine-complete f x eqAH dX dF@(d-case _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-complete dX)))) (proj₂ (proj₂ (proj₂ (given-complete dF))))
  spine-complete f x eqAH dX dF@(d-pair _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-complete dX)))) (proj₂ (proj₂ (proj₂ (given-complete dF))))
  spine-complete f x eqAH dX dF@(d-cata _ _) =
    infer-complete-RApp-spine f x eqAH refl (proj₂ (proj₂ (proj₂ (infer-complete dX)))) (proj₂ (proj₂ (proj₂ (given-complete dF))))
  spine-complete {ctx} f x eqAH dX dF@(d-poly {x = y} ln li lp ¬g _ _ _ _) =
    infer-complete-RApp-spine f x eqAH (cong proj₁ (poly-head-fails ctx y ln li lp ¬g))
      (proj₂ (proj₂ (proj₂ (infer-complete dX)))) (proj₂ (proj₂ (proj₂ (given-complete dF))))
  spine-complete f x eqAH dX (d-infer {A′ = A′} w a ⊑-pure) =
    let (_ , _ , _ , eqF) = infer-complete w
        (_ , _ , _ , eqX) = iFromInferSub dX a
    in infer-complete-RApp-generic f x A′ eqAH eqF eqX

  -- Plan 0.94 §10: the domain-given mode is EXACT — the elaborator returns the
  -- derivation's output and usage.
  given-complete :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {π : T.Purity}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (elabGivenV ctx e A π) ≡ success B Ψ eE d f
  given-complete {ctx} {e} {A} {π = π} (d-infer w a g)
    rewrite given-infer-route w A π (infer-complete w) =
      given-infer-complete (inferElabV ctx e) (proj₂ (proj₂ (proj₂ (infer-complete w)))) a g
  -- Plan 0.103 phase 2b: a polymorphic head does not infer, so it is given
  -- through the polymorphic fallback.
  given-complete {ctx} (d-poly {x = x} {A = A} {π = π} ln li lp ¬g as inc ki@(θ , eθ , _) g)
    rewrite poly-head-fails ctx x ln li lp ¬g =
      DPoly.from-lookups ctx x A π (Once.TypeCheck.ElaborateProofs.UnboundVariable x) ln li lp ¬g as inc θ eθ g ki
  given-complete {ctx} (d-lam {x = x} {body = body} {A = A} {q' = q'} leq bd)
    with inferElabV (Once.TypeCheck.ElaborateProofs.extendNamedCtx ctx x A) body | infer-complete bd
  ... | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | (_ , _ , _ , refl)
      with Once.TypeCheck.ElaborateProofs.decideLeq q' T.Many | decideLeq-just q' T.Many leq
  ...   | just _ | _ , refl = _ , _ , _ , refl
  given-complete {ctx} (d-compose {f = f} {g = g} {A = A} {M = M} {π = π} dg df)
    with elabGivenV ctx g A π | given-complete dg
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with elabGivenV ctx f M π | given-complete df
  ...   | success _ _ _ _ _ , _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  given-complete d-id = _ , _ , _ , refl
  given-complete d-fst = _ , _ , _ , refl
  given-complete d-snd = _ , _ , _ , refl
  given-complete d-terminal = _ , _ , _ , refl
  given-complete d-initial = _ , _ , _ , refl
  given-complete {ctx} (d-case {f = f} {g = g} {A = A} {B = B} {C = C} {π = π} df dg)
    with elabGivenV ctx f A π | given-complete df
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with elabGivenV ctx g B π | given-complete dg
  ...   | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
        with C ≟T C
  ...     | yes refl = _ , _ , _ , refl
  ...     | no ¬p = ⊥-elim (¬p refl)
  given-complete {ctx} (d-pair {f = f} {g = g} {A = A} {π = π} df dg)
    with elabGivenV ctx f A π | given-complete df
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with elabGivenV ctx g A π | given-complete dg
  ...   | success _ _ _ _ _ , _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  given-complete {ctx} (d-cata {alg = alg} {F = F} {A = A} {π = π} wfF dalg)
    rewrite wellFormedF?-complete-at wfF =
      given-cata-complete wfF
        (inferElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)) alg)
        (proj₂ (proj₂ (proj₂ (infer-complete dalg))))

  -- Plan 0.49 / D063: the MORPHISM-COMPLETENESS theorem. A `⊢ᵐ` morphism
  -- check-elaborates at its arrow type (any grade π). TRUE — provable by
  -- induction on `⊢ᵐ` (bare builtins → `checkElab-fallback-RVar-*`; compose/
  -- case/pair/curry → the new fused `checkX` succeed on morphism arms; cata →
  -- `checkCataGo`; leaves m-const/m-named/m-lam → value/import/lambda paths).
  -- This SINGLE postulate REPLACES the three former false/dead postulates
  -- (`cata-check-complete`, `case-copair-eff-complete`, `compose-eff-complete`) —
  -- restoring consistency (the old eff ones were FALSE). Discharge = C3 follow-up.
  -- `morph-complete` (Plan 0.49 / D063) is now PROVEN in Once.TypeCheck.MorphComplete
  -- (imported above): induction on ⊢ᵐ, 12/15 cases discharged; m-const/m-cata/m-named
  -- remain scoped postulates there (the latter pending plan 0.50).
  -- (Plan 0.36 Phase 2a follow-up DISCHARGED: `pair-lit-check-complete` was the
  -- pair-literal check-mode completeness postulate — now proven via `pair-lit-reduce`
  -- + the `iFromInfer` switch / `check-completeV`, above. The proof is
  -- complete.)

  -- `nothing ≡ just _` is absurd — returns any goal type (no `⊥` import needed).
  nothing≢just : ∀ {ℓ} {A : Set ℓ} {x : A} {C : Set} → nothing ≡ just x → C
  nothing≢just ()

  -- Full ⊢ᶜ walk: handles t-lam recursively and delegates t-embed
  -- to the per-shape fallback lemma.
  check-complete :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e A ≡ success Ψ eE d f

  check-complete {ctx}
    (t-lam {x = x} {body = body} {A = A} {B = B} {q = q} {q' = q'}
           leq-eq bodyD) =
    let (_ , _ , _ , eqBody) = check-complete bodyD
    in check-complete-RLam ctx x body A q q' B leq-eq eqBody

  -- t-embed (infer ⊆ check): ONE clause — the switch is `iFromInfer`, which
  -- recurses structurally on the INFER derivation (the 22 former per-shape clauses
  -- moved there). Discharges the old `pair-lit` re-wrap: the pair's components are
  -- reached via `iFromInfer`'s genuine sub-derivations, not a re-embedded grandchild.
  check-complete (t-sub d sb) = iFromInferSub d sb
  -- D127: the seven POINT-FREE LEAVES. Each is the elaborator's own
  -- `RVar`-fallback lemma, which never depended on the purity — generalising
  -- those to any `π` is what lets these rules stay grade-poly.
  check-complete {ctx} (t-id-check {T = T}) =
    checkElab-fallback-RVar-id {ctx} T
  check-complete {ctx} (t-fst-check {A = A} {B = B}) =
    checkElab-fallback-RVar-fst {ctx} A B
  check-complete {ctx} (t-snd-check {A = A} {B = B}) =
    checkElab-fallback-RVar-snd {ctx} A B
  check-complete {ctx} (t-terminal-morph-check {A = A}) =
    checkElab-fallback-RVar-terminal {ctx} A
  check-complete {ctx} (t-initial-morph-check {A = A}) =
    checkElab-fallback-RVar-initial {ctx} A
  check-complete {ctx} (t-inl-morph-check {A = A} {B = B}) =
    checkElab-fallback-RVar-inl {ctx} A B
  check-complete {ctx} (t-inr-morph-check {A = A} {B = B}) =
    checkElab-fallback-RVar-inr {ctx} A B
  -- Plan 0.94 §10: compose's two routes. `g`'s is the elaborator's first, so
  -- a `g`-route derivation is followed step by step; an `f`-route derivation
  -- meets it through `compose-g-complete`.
  check-complete {ctx} (t-compose-check-g {f = f} {g = g} {A = A} {B = B} {C = C} {π = π} dg df)
    with elabGivenV ctx g A π | given-complete dg
  ... | success _ _ _ _ _ , _ | (_ , _ , _ , refl)
      with checkElabV ctx f (B T.⇒[ T.mk-kind T.Many π ] C) | check-complete df
  ...   | success _ _ _ _ , _ | (_ , _ , _ , refl) = _ , _ , _ , refl
  check-complete {ctx} (t-compose-check-f {f = f} {g = g} {A = A} {B = B} {C = C} {C′ = C′} {π = π} {π′ = π′} wf p dg) =
    let (_ , _ , _ , eqF) = infer-complete wf
        (_ , _ , _ , eqG) = check-complete dg
    in compose-g-complete f g A B C C′ π π′ (elabGivenV ctx g A π) wf dg eqF p eqG
  check-complete (t-case-copair-check {π = T.pure} df dg) =
    let (_ , _ , _ , Wf , eqf) = check-completeV df
        (_ , _ , _ , Wg , eqg) = check-completeV dg
        (d , fr , eqGo) = caseGo-success eqf eqg
    in _ , _ , _ , cong proj₁ eqGo
  check-complete (t-case-copair-check {π = T.eff} df dg)
    with check-completeV df | check-completeV dg
  ... | (_ , _ , _ , Wf , eqf) | (_ , _ , _ , Wg , eqg)
        with caseGo-success eqf eqg
  ...     | (d , fr , eqGo) rewrite eqGo = _ , _ , _ , refl
  -- `pair`/`curry` are PURE-FIXED, so no π split: only the pure clause of
  -- `checkPair`/`checkCurry` can apply, and rewriting by the arms' results
  -- reduces its `with`-tree to the success.
  check-complete (t-pair-morph-check df dg)
    with check-completeV df | check-completeV dg
  ... | (_ , _ , _ , Wf , eqf) | (_ , _ , _ , Wg , eqg)
        rewrite eqf | eqg = _ , _ , _ , refl
  check-complete (t-curry-check df)
    with check-completeV df
  ... | (_ , _ , _ , Wf , eqf) rewrite eqf = _ , _ , _ , refl
  -- cata: split on π like compose/case. `checkCataGoV-pure-J` is the dispatch
  -- bridge at pure; at eff the algebra IS an eff derivation so the eff `Go`
  -- succeeds and the first branch fires.
  check-complete {ctx} (t-cata-check {alg = alg} {F = F} {A = A} {π = T.pure} wfF dalg)
    -- PLAN 0.80 A1: the rule hands over the WITNESS; the elaborator still
    -- dispatches on the decider, so recover its equation here.
    with wellFormedF?-complete-at wfF
  ... | eqW
    with check-completeV dalg
  ... | (_ , _ , _ , W , eqA)
        with checkCataGo-just-success ctx alg F A T.pure wfF eqW eqA
  ...     | eqGo = _ , _ , _ ,
            cong proj₁ (trans (checkCataGoV-pure-J ctx alg F A (just wfF) eqW) eqGo)
  check-complete {ctx} (t-cata-check {alg = alg} {F = F} {A = A} {π = T.eff} wfF dalg)
    -- PLAN 0.80 A1: the rule hands over the WITNESS; the elaborator still
    -- dispatches on the decider, so recover its equation here.
    with wellFormedF?-complete-at wfF
  ... | eqW
    with check-completeV dalg
  ... | (_ , _ , _ , W , eqA)
        with checkCataGo-just-success ctx alg F A T.eff wfF eqW eqA
  ...     | eqGo
            rewrite trans (checkCataGo-J ctx alg F A T.eff (just wfF) eqW) eqGo =
            _ , _ , _ , refl
  -- D192: ana. One clause, not two: `checkAna` is grade-generic, so there is
  -- no pure/eff dispatch to bridge — the coalgebra's grade IS the unfold's.
  check-complete {ctx} (t-ana-check {coalg = coalg} {F = F} {A = A} {π₀ = π₀} {π = π} wfF dcoalg)
    with wellFormedF?-complete-at wfF
  ... | eqW
    with check-completeV dcoalg
  ... | (_ , _ , _ , W , eqA)
        with checkAnaGo-just-success ctx coalg F A π₀ π wfF eqW eqA
  ...     | eqGo = _ , _ , _ ,
            cong proj₁ (trans (checkAnaGoV-J ctx coalg F A π₀ π (just wfF) eqW) eqGo)
  check-complete (t-In-app-check {arg = arg} {F = F} wfF dArg) =
    let (_ , _ , _ , eqA) = check-complete dArg
    -- PLAN 0.80 A1: witness in, decider equation recovered (as for cata).
    in checkElab-fallback-RApp-In arg F (wellFormedF?-complete-at wfF) eqA
  -- Direct (bidirectional) pair check: components carry ⊢ᶜ derivations, so recurse
  -- the STRONG `check-completeV` on the genuine subterms dA/dB (no switch needed).
  check-complete (t-pair-lit-check {a = a} {b = b} {A = A} {B = B} dA dB)
    with check-completeV dA | check-completeV dB
  ... | (_ , _ , _ , _ , eqA) | (_ , _ , _ , _ , eqB) = pair-lit-reduce eqA eqB
  check-complete (t-apply-check {p = p} {A = A} {B = B} d) =
    let (_ , _ , _ , eq) = infer-complete d
    in checkElab-fallback-RApp-apply p A B eq (<:-refl B)
  -- Plan 0.4 T0 Phase F new check-mode rules — discharged by
  -- completeness-gap-*-eq helpers above (recursive check-complete on
  -- the sub-derivation produces the bridging checkElab equation).
  check-complete (t-inl-app-check {arg = arg} {A = A} {B = B} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-inl-app-check-eq arg A B eqC
  check-complete (t-inr-app-check {arg = arg} {A = A} {B = B} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-inr-app-check-eq arg A B eqC
  check-complete (t-initial-app-check {arg = arg} {T = T} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-initial-app-check-eq arg T eqC
  -- D243: a use at a kinded instance; the elaborator decides the instance.
  check-complete {ctx}
    (t-var-poly-instantiate {x = x} {T = T} {schema = schema}
                            localN importN polyE eqG inst) =
    checkElab-fallback-RVar-poly {ctx} x T localN importN polyE
      (¬Ground-isGround-inj₂ schema eqG) inst

-- STRONG check-complete: a trivial VIEW of the weak `check-complete`, not a
-- per-case rewrite. Abstract `checkElabV`, take the weak proj₁ equation, and
-- `rewrite` it to expose the REAL witness (proj₂ of the elaborator result — not
-- a subst-reconstruction, so downstream witness-extraction still reduces). This
-- is the strong-completeness primitive the migration needs; per-case strong
-- proofs are unnecessary.