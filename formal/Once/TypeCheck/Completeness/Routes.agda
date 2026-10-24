-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Completeness.Routes — how the checker's dispatch reaches a
-- rule's clause (plan 0.3 G2; plan 0.122 §5.6).
--
-- The derivation-free lemmas completeness (`TypeCheck.Completeness`) reads
-- the checker's run through, beside the per-rule ones (`Completeness.Rules`):
-- the domain-given mode's routes, a telescope head's lookups, the compose
-- `f`-route, the spine, and the bare-generator fallbacks.
------------------------------------------------------------------------
import Once.Type.Grade
module Once.TypeCheck.Completeness.Routes where

import Once.Surface.Syntax as Srf
open import Once.Internal.Type using (wk₀)
open import Once.Spec.Type using (⟦_⟧F)
import Once.Spec.Type as T
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.String.Properties as StrProp using ()
open import Once.Spec.Type as T using (Type; Unit; _*_)
import Once.Internal.Type as T
import Once.Type as T
import Once.Spec.Surface.Syntax as T
import Once.Internal.Type.Poly as T
import Once.Spec.Grade as T
open import Once.Spec.Surface.Syntax as Raw using (RVar; RResolved)
open import Once.Internal.Syntax as Raw using (RawExpr)
open import Once.Spec.Name using (CanonicalName; gen; own; NotGenerator)
open import Once.Internal.Name using (showCanonical)
open import Once.CanonicalName using (bare-NotGenerator)
open import Once.TypeCheck.Elaborate
  using (VerifiedInferResult; elabGivenLeaf; given-infer; elabGivenApp; success; inferElabV; failure; elabGivenV; given-cata; inferElab; checkElab; checkCompose-f; checkElabV; VerifiedGivenResult; checkCompose-g; checkCaseGo; checkLoop)
open import Once.TypeCheck.SpecWitness using (wt-case-copair-check)
import Once.Internal.Typing.Scope as Classify
import Once.TypeCheck.Error as Error
import Once.TypeCheck.Elaborate as E
open import Once.Internal.Type.Join using (join?-complete)
import Data.Unit
open import Once.Internal.Type.WellFormed using (WellFormedF; IsConcrete)
open import Once.Functor.Decide using (isConcrete?; isConcrete?-complete)
-- PLAN 0.80 A: the rules carry PROPERTIES now, so completeness recovers the
-- decider's answer from the property here rather than reading it off a premise.
open import Once.TypeCheck.DeciderComplete
  using (isGround-complete-at; ¬Ground-isGround-inj₂; wfFun?-complete-at)
import Once.Internal.Typing.Scope
import Once.TypeCheck.Classify
open import Once.Internal.Context as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
import Once.Spec.Context as SCx
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
import Data.String.Properties

-- Supplementary imports for the MERGED morph-elab/StrongElab/eff-complete block.
open import Once.Spec.Sub using (_<:_; sub-int; sub-float; sub-unit; sub-arr)
open import Once.Internal.Type.Sub using (sub-prod)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-pe; ⊑-pa)
open import Once.Type.Sub using (_<:?_; _⊑π?_)
open import Once.Internal.Type.Sub using (<:-refl)
open import Once.Internal.Type.DecEq using (_≟T_)
open import Once.Internal.Typing.Scope using (NamedCtx; AppHeadView; ahv-other; classifyAppHeadView; lookupLocal; lookupImport)
open import Once.TypeCheck.Classify using (lookupPolyPrefix⇒lookupPoly; GenView; classifyGen; gv-id; gv-fst; gv-snd; gv-terminal; gv-initial; gv-inl; gv-inr; gv-unit; gv-other; classifyAppHead-nothing⇒view-other)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Once.TypeCheck.ElaborateProofs using (checkCataGo-J; checkCataGoV-pure-J; checkCataGo-just-success; checkAnaGoV-J; checkAnaGo-just-success; checkLoopV-J; withUnit-elim)


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
  -- (a resolved head that infers is given through its inference)
  res-route : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (A : Ty m) (π : T.Purity)
                (r : VerifiedInferResult ctx (RResolved cn)) {B : Ty m} {Ψ eE d f}
            → proj₁ r ≡ success B Ψ eE d f
            → E.given-res ctx cn A π r ≡ given-infer ctx (RResolved cn) A π r
  res-route ctx cn A π (success _ _ _ _ _ , _) _ = refl
  res-route ctx cn A π (failure _ , _) ()

  leaf-route : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (A : Ty m) (π : T.Purity)
                 (r : VerifiedInferResult ctx (RResolved cn))
             → NotGenerator cn → (vw : AppHeadView (RResolved cn))
             → ∀ {B : Ty m} {Ψ eE d f} → proj₁ r ≡ success B Ψ eE d f
             → elabGivenLeaf ctx cn A π vw r ≡ given-infer ctx (RResolved cn) A π r
  leaf-route ctx ._ A π r (¬id ∷ᴬ _) Classify.ahv-id _ = ⊥-elim (¬id refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ ¬fst ∷ᴬ _) Classify.ahv-fst _ = ⊥-elim (¬fst refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ ¬snd ∷ᴬ _) Classify.ahv-snd _ = ⊥-elim (¬snd refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ ¬t ∷ᴬ _) Classify.ahv-terminal _ = ⊥-elim (¬t refl)
  leaf-route ctx ._ A π r (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ ¬i ∷ᴬ _) Classify.ahv-initial _ = ⊥-elim (¬i refl)
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-inl ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-inr ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-curry ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-apply ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-In ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-cata ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-ana ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx ._ A π r _ Classify.ahv-Out ok = res-route ctx _ A π r ok
  {-# CATCHALL #-}
  leaf-route ctx cn A π r _ ahv-other ok = res-route ctx cn A π r ok


  app-other-route : ∀ {m} (ctx : NamedCtx m) (f x : RawExpr) (A : Ty m) (π : T.Purity)
                      (r : VerifiedInferResult ctx (Raw.RApp f x))
                  → classifyAppHeadView f ≡ ahv-other
                  → elabGivenApp ctx f x A π (classifyAppHeadView f) r ≡ given-infer ctx (Raw.RApp f x) A π r
  app-other-route ctx f x A π r eq rewrite eq = refl

-- Plan 0.103 phase 2b: the domain-given POLYMORPHIC head is elaborated as the
-- derivation says (`d-poly`): each de-withed stage reduces on its decided
-- premise, and the elaborator's codomain is the derivation's by determinacy.
module DPoly where
  open import Once.TypeCheck.Elaborate
    using (given-poly; given-poly-g; given-poly-a; given-poly-m; given-poly-π; isGround-inj₂→¬Ground)
  open import Once.Type.Match using (instantiate)
  open import Once.Type.Instance using (instantiate-complete; instantiate-sound)
  open import Once.Type.Determined using (codVarsInDom?; cod-determined; arrowSchema?)
  open import Once.Type.Sub using (_⊑π?_)
  open import Once.Internal.Type.Instance using (KindedInstance)
  open import Once.Type.Rigid using (kindedInstance?)
  open import Once.Internal.Typing.Scope using (lookupPolyPrefix)
  open import Relation.Nullary using (yes; no)
  open import Data.String using (String)
  open import Data.Sum using (inj₂)
  open import Data.Unit using (tt)
  open import Data.Empty using (⊥-elim)

  ⇒-parts : ∀ {m} {a b c d : Ty m} {k k′} → (a T.⇒[ k ] b) ≡ (c T.⇒[ k′ ] d) → (a ≡ c) × (b ≡ d)
  ⇒-parts refl = refl , refl

  arrow-parts : ∀ {m} {s sd sc : T.PolyType} {π′} {A B : Ty m} (θ : String → Ty m)
    → T.ArrowSchema s sd sc π′ → T.substPoly θ s ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)
    → (T.substPoly θ sd ≡ A) × (T.substPoly θ sc ≡ B)
  arrow-parts θ T.as-pure e = ⇒-parts e
  arrow-parts θ T.as-eff  e = ⇒-parts e
  arrow-parts θ T.as-act  e = ⇒-parts e

  gp-eq : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err ll eL li eI lp eP
    → given-poly ctx x A π err (lookupImport (Classify.NamedCtx.sig ctx) x) refl (lookupImport (Classify.NamedCtx.imports ctx) x) refl
        (lookupPolyPrefix (Classify.NamedCtx.polys ctx) x) refl
      ≡ given-poly ctx x A π err ll eL li eI lp eP
  gp-eq ctx x A π err .(lookupImport (Classify.NamedCtx.sig ctx) x) refl .(lookupImport (Classify.NamedCtx.imports ctx) x) refl
    .(lookupPolyPrefix (Classify.NamedCtx.polys ctx) x) refl = refl

  gg-eq : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err schema {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ig eG
    → given-poly-g ctx x A π err schema eL eI eP (T.isGround schema) refl ≡ given-poly-g ctx x A π err schema eL eI eP ig eG
  gg-eq ctx x A π err schema eL eI eP .(T.isGround schema) refl = refl

  gm-eq : ∀ {mₜ} (ctx : NamedCtx mₜ) (x : String) (A : Ty mₜ) (π : T.Purity) err {schema sd sc π′ body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc) mσ eS
    → given-poly-m ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl
      ≡ given-poly-m ctx x A π err eL eI eP ¬g as inc mσ eS
  gm-eq ctx x A π err {sd = sd} eL eI eP ¬g as inc .(instantiate sd A) refl = refl

  -- The codomain the elaborator computes IS the derivation's.
  at-π : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc) (θ₀ : String → Ty m) (e₀ : T.substPoly θ₀ sd ≡ A)
    → T.substPoly θ₀ sc ≡ B → π′ ⊑π π → KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B)
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly-π ctx x A π err eL eI eP ¬g as inc θ₀ e₀ (π′ ⊑π? π)) ≡ success B Surface.zeroUsage eE d f
  at-π ctx x A π err {π′ = π′} {schema = schema} {sc = sc} eL eI eP ¬g as inc θ₀ e₀ refl g ki with π′ ⊑π? π
  ... | no ¬g′ = ⊥-elim (¬g′ g)
  ... | yes _ with kindedInstance? (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] T.substPoly θ₀ sc)
  ...   | yes _ = _ , _ , _ , refl
  ...   | no ¬k = ⊥-elim (¬k ki)

  at-m : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Ty m) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly-m ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl) ≡ success B Surface.zeroUsage eE d f
  at-m ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g as inc θ eθ g ki =
    let (ed , ec) = arrow-parts θ as eθ
        (σ , eS)  = instantiate-complete sd A (θ , ed)
        θ₀        = proj₁ (instantiate-sound sd A eS)
        e₀        = proj₂ (instantiate-sound sd A eS)
        eB        = trans (cod-determined {sd = sd} {sc = sc} inc θ₀ θ (trans e₀ (sym ed))) ec
        (eE , d , f , r) = at-π ctx x A π err eL eI eP ¬g as inc θ₀ e₀ eB g ki
    in eE , d , f , trans (cong proj₁ (gm-eq ctx x A π err eL eI eP ¬g as inc (just σ) eS)) r

  from-arrow : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix} eL eI
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) ¬g
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Ty m) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly-a ctx x A π err eL eI eP ¬g (arrowSchema? schema)) ≡ success B Surface.zeroUsage eE d f
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-pure inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-pure inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-eff inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-eff inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)
  from-arrow ctx x A π err {sd = sd} {sc = sc} eL eI eP ¬g T.as-act inc θ eθ g ki with codVarsInDom? sd sc
  ... | yes inc′ = at-m ctx x A π err eL eI eP ¬g T.as-act inc′ θ eθ g ki
  ... | no ¬inc = ⊥-elim (¬inc inc)

  -- The whole chain, from the lookups (the head's inference has failed).
  from-lookups : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : T.Purity) err
    {B : Ty m} {π′ : T.Purity} {schema sd sc : T.PolyType} {body prefix}
    (eL : lookupImport (Classify.NamedCtx.sig ctx) x ≡ nothing) (eI : lookupImport (Classify.NamedCtx.imports ctx) x ≡ nothing)
    (eP : lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)) (¬g : ¬ T.Ground schema)
    (as : T.ArrowSchema schema sd sc π′) (inc : T.CodVarsInDom sd sc)
    (θ : String → Ty m) (eθ : T.substPoly θ schema ≡ (A T.⇒[ T.mk-kind T.Many π′ ] B)) (g : π′ ⊑π π) (ki : KindedInstance (NamedCtx.kinds ctx) schema (A T.⇒[ T.mk-kind T.Many π′ ] B))
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        proj₁ (given-poly ctx x A π err (lookupImport (Classify.NamedCtx.sig ctx) x) refl (lookupImport (Classify.NamedCtx.imports ctx) x) refl
                 (lookupPolyPrefix (Classify.NamedCtx.polys ctx) x) refl) ≡ success B Surface.zeroUsage eE d f
  from-lookups ctx x A π err {schema = schema} eL eI eP ¬g as inc θ eθ g ki =
    let eG = ¬Ground-isGround-inj₂ schema ¬g
        (eE , d , f , r) = from-arrow ctx x A π err eL eI eP (isGround-inj₂→¬Ground schema eG) as inc θ eθ g ki
    in eE , d , f ,
       trans (cong proj₁ (gp-eq ctx x A π err nothing eL nothing eI (just _) eP))
         (trans (cong proj₁ (gg-eq ctx x A π err schema eL eI eP (inj₂ tt) eG)) r)

-- A non-ground telescope entry does not infer.
poly-head-fails : ∀ {m} (ctx : NamedCtx m) (x : String) {schema body prefix}
  → lookupImport (Classify.NamedCtx.sig ctx) x ≡ nothing → lookupImport (Classify.NamedCtx.imports ctx) x ≡ nothing
  → Once.Internal.Typing.Scope.lookupPolyPrefix (Classify.NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ T.Ground schema
  → inferElabV ctx (RResolved (own x)) ≡ (failure (Error.UnboundVariable x) , Data.Unit.tt)
poly-head-fails ctx x {schema} eS eI eP ¬g =
  Once.TypeCheck.ElaborateProofs.inferElabV-own-fail-bridge ctx x eS eI
    (Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground ctx x eS eI
       (Once.TypeCheck.Classify.lookupPolyPrefix⇒lookupPoly (Classify.NamedCtx.polys ctx) x eP) (¬Ground-isGround-inj₂ schema ¬g))

-- `d-infer`: the inferred arrow's domain converts back, its grade up.
given-infer-complete : ∀ {m} {ctx : NamedCtx m} {e : RawExpr} {A A′ B : Ty m} {π π′ : T.Purity}
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)} {eE : _} {d f : ℕ}
    (r : VerifiedInferResult ctx e)
  → proj₁ r ≡ success (A′ T.⇒[ T.mk-kind T.Many π′ ] B) Ψ eE d f
  → A <: A′ → π′ ⊑π π
  → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] proj₁ (given-infer ctx e A π r) ≡ success B Ψ eE′ d′ f′
given-infer-complete {A = A} {A′ = A′} {π = π} {π′ = π′} (success _ _ _ _ _ , _) refl a g
  with A <:? A′ | π′ ⊑π? π
... | yes _ | yes _ = _ , _ , _ , refl
... | no ¬a | _     = ⊥-elim (¬a a)
... | yes _ | no ¬g = ⊥-elim (¬g g)

-- `d-cata`: the algebra synthesizes the arrow the fold needs.
given-cata-complete : ∀ {m} {ctx : NamedCtx m} {alg : RawExpr} {F : Fun m} {A : Ty m} {π : T.Purity}
    (wfF : WFFun (Classify.NamedCtx.kinds ctx) F) {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)} {eE : _} {d f : ℕ}
    (u : T.pure ⊑π π) (r : VerifiedInferResult ctx alg)
  → proj₁ r ≡ success (⟦ F ⟧F A T.⇒[ T.mk-kind T.Many π ] A) Ψ eE d f
  → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] proj₁ (given-cata ctx alg F π wfF r) ≡ success A (T.Many *ᵘ Ψ) eE′ d′ f′   -- plan 0.113 B1
given-cata-complete {F = F} {A = A} {π = π} wfF {Ψ = Ψ} u (success _ _ _ _ _ , _) refl
  with (⟦ F ⟧F A T.⇒[ T.mk-kind T.Many π ] A) ≟T (⟦ F ⟧F A T.⇒[ T.mk-kind T.Many π ] A)
... | yes refl =
  withUnit-elim _ u _
    (λ res → ∃[ eE′ ] ∃[ d′ ] ∃[ f′ ] proj₁ res ≡ success A (T.Many *ᵘ Ψ) eE′ d′ f′) (λ u′ → _ , _ , _ , refl)
... | no ¬p = ⊥-elim (¬p refl)

-- compose, `f`'s route: `f` synthesizes, converts, and `g` is checked at the
-- middle it names.
compose-f-complete : ∀ {m} {ctx : NamedCtx m} (f g : RawExpr) (A B C C′ : Ty m) (π π′ : T.Purity)
    {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)} {fE : _} {gE : _} {df ff dg fg : ℕ}
  → inferElab ctx f ≡ success (B T.⇒[ T.mk-kind T.Many π′ ] C′) Ψ₁ fE df ff
  → (B T.⇒[ T.mk-kind T.Many π′ ] C′) <: (B T.⇒[ T.mk-kind T.Many π ] C)
  → checkElab ctx g (A T.⇒[ T.mk-kind T.Many π ] B) ≡ success Ψ₂ gE dg fg
  → ∃[ eE ] ∃[ d ] ∃[ fr ] proj₁ (checkCompose-f ctx f g A C π) ≡ success (Ψ₁ +ᵘ (T.Many *ᵘ Ψ₂)) eE d fr
compose-f-complete {ctx = ctx} f g A B C C′ π π′ eqF p eqG
  with inferElabV ctx f | eqF
... | success _ _ _ _ _ , _ | refl
    with (B T.⇒[ T.mk-kind T.Many π′ ] C′) <:? (B T.⇒[ T.mk-kind T.Many π ] C)
...   | no ¬p = ⊥-elim (¬p p)
...   | yes _ with checkElabV ctx g (A T.⇒[ T.mk-kind T.Many π ] B) | eqG
...     | success _ _ _ _ , _ | refl = _ , _ , _ , refl

-- The spine, once the head is known not to synthesize.
infer-complete-RApp-spine : ∀ {m} {ctx : NamedCtx m} (f x : RawExpr) {X B : Ty m} {err : _}
    {Ψf Ψx : Surface.Usage (Classify.NamedCtx.size ctx)} {fE : _} {xE : _} {df ff dx fx : ℕ}
  → Classify.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ failure err
  → inferElab ctx x ≡ success X Ψx xE dx fx
  → proj₁ (elabGivenV ctx f X T.pure) ≡ success B Ψf fE df ff
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x) ≡ success B (Ψf +ᵘ (T.Many *ᵘ Ψx)) eE d f'

infer-complete-RApp-spine {ctx = ctx} f x {X} {B} eqAH eqF eqX eqG
  rewrite cong proj₁ (viewBridge {ctx = ctx} {f = f} {x = x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | cong proj₁ (otherBridge {ctx = ctx} {f = f} {x = x} nothing eqAH)
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

open Once.TypeCheck.ElaborateProofs
  using (checkElab-fallback-RInt; checkElab-fallback-RFloat; checkElab-fallback-RUnit; checkElab-fallback-RVar-unit; checkElab-fallback-RVar-id; checkElab-fallback-RVar-fst; checkElab-fallback-RVar-snd; checkElab-fallback-RVar-terminal; checkElab-fallback-RVar-initial; checkElab-fallback-RVar-inl; checkElab-fallback-RVar-inr; checkElab-fallback-RApp-In; checkElab-fallback-RApp-apply; checkElab-fallback-RApp-apply-effclosure; checkElab-fallback-RApp-apply-actclosure; checkElab-fallback-RVar-poly; checkElab-fallback-RVar-poly-infer; checkElab-fallback-RResolved; checkElab-fallback-RAnnot; checkElab-fallback-RLet; checkElab-fallback-RDestruct; checkElab-fallback-RNeg; checkElab-fallback-RBinOp; checkElab-fallback-RApp-id; checkElab-fallback-RApp-fst; checkElab-fallback-RApp-snd; checkElab-fallback-RApp-terminal; checkElab-fallback-RApp-Out; checkElab-fallback-RApp-generic)

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
checkElab-fallback-RVar : ∀ {m} {ctx : NamedCtx m} {τ : Ty m} (x : String) (T : Ty m)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE : _} {d f : ℕ}
  → inferElab ctx (Raw.RVar x) ≡ success T Ψ eE d f
  → T <: τ
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RVar x) τ ≡ success Ψ eE' d' f'
-- D136: the bare-`RVar` check path no longer dispatches on
-- `classifyBareBuiltin` (a generator is `RResolved (gen g)`, never a bare
-- name), so the nine-way split this proof used to mirror collapses to the
-- single `embedOrSubsume` reduction.
checkElab-fallback-RVar {ctx = ctx} {τ = τ} x T eqInf sb
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
completeness-gap-inl-app-check-eq : ∀ {m} {ctx : NamedCtx m} (arg : RawExpr) (A B : Ty m)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ A}
    {d f : ℕ}
  → checkElab ctx arg A ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (Raw.RResolved (gen "inl")) arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inl-app-check-eq {ctx = ctx} arg A B eqC
  with checkElabV ctx arg A | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-inr-app-check-eq : ∀ {m} {ctx : NamedCtx m} (arg : RawExpr) (A B : Ty m)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ B}
    {d f : ℕ}
  → checkElab ctx arg B ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (Raw.RResolved (gen "inr")) arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inr-app-check-eq {ctx = ctx} arg A B eqC
  with checkElabV ctx arg B | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-initial-app-check-eq : ∀ {m} {ctx : NamedCtx m} (arg : RawExpr) (T : Ty m)
    {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
    {eE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T.Void}
    {d f : ℕ}
  → checkElab ctx arg T.Void ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (Raw.RResolved (gen "initial")) arg) T
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-initial-app-check-eq {ctx = ctx} arg T eqC
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
checkElabV-RResolved-J : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (T : Ty m) (gv : GenView cn)
  → classifyGen cn ≡ gv
  → checkElab ctx (RResolved cn) T
      ≡ proj₁ (E.checkElabV-RResolved-dispatch
                 ctx cn T gv (inferElabV ctx (RResolved cn)))
checkElabV-RResolved-J ctx cn T .(classifyGen cn) refl = refl

private
  -- The `case` twin. No `mid` argument, so no `-J` bridge is needed.
  caseGo-success : ∀ {m} {A B C : Ty m} {ctx f g} {π : T.Purity}
    {Ψf Ψg : Surface.Usage (Classify.NamedCtx.size ctx)}
    {Ef : _} {Eg : _} {Wf : _} {Wg : _} {df ff dg fg : ℕ}
    → checkElabV ctx f (A T.⇒[ T.mk-kind T.Many π ] C)
        ≡ (success Ψf Ef df ff , Wf)
    → checkElabV ctx g (B T.⇒[ T.mk-kind T.Many π ] C)
        ≡ (success Ψg Eg dg fg , Wg)
    → Σ-syntax ℕ λ d → Σ-syntax ℕ λ fr →
        checkCaseGo ctx f g A B C π
          ≡ (success (Ψf Surface.+ᵘ Ψg) (Srf.copair' Ef Eg) d fr
            , wt-case-copair-check Wf Wg)
  caseGo-success eqf eqg rewrite eqf | eqg = _ , _ , refl

  -- D127: `cgo-usage` / `ccgo-usage` DELETED. They said compose/case emit
  -- `zeroUsage`, which was true only while the arms were closed. The usage is
  -- now `Ψf +ᵘ Ψg` — that is the whole content of D130 — so the lemmas are not
  -- weakened but FALSE, and their only consumers were the eff-complete family
  -- that went with the realm.



-- `checkElabV (RPair a b) (A * B)` reduces via `checkPairLit` (checkElabV a A /
-- checkElabV b B). Given the two paired component equations, `rewrite` drives it
-- to its `success` leaf.
pair-lit-reduce : ∀ {m} {ctx : NamedCtx m} {a b : RawExpr} {A B : Ty m}
  {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
  {aE da fa wA bE db fb wB}
  → checkElabV ctx a A ≡ (success Ψ₁ aE da fa , wA)
  → checkElabV ctx b B ≡ (success Ψ₂ bE db fb , wB)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      checkElab ctx (Raw.RPair a b) (A * B)
        ≡ success (Ψ₁ +ᵘ Ψ₂) eE d f
pair-lit-reduce eqA eqB rewrite eqA | eqB = _ , _ , _ , refl
