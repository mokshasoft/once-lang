-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.WalkBack — the Spec's walk is a typed telescope
-- of the compiler's (plan 0.121 `complete`; the converse of `Walk`).
--
-- The compiler's telescope is built alongside the Spec's walk, in a scope
-- the walk keeps (`WalkState`). The Spec's definitions table agrees with the
-- translation of the compiler's up to the numbering of each schema's
-- variables (`Rel`, `SchemaRen`), which the Spec leaves free. A definition
-- with a signature (`step`): its body, moved to the compiler's numbering
-- (`TyRen`) and table (`DefsRen`), is the compiler's check (`Def.body-check←`);
-- and its type is principal for the compiler as for the Spec
-- (`Def.principal←`, reading a compiler check back the other way).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Lang.Contract using (ISig)
open import Once.Lang.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
open import Once.Spec.Numerics using (TargetNum)
import Once.Lang.Type as LT
import Once.Lang.Type.WellFormed as LW
import Once.Spec.Type as ST
open import Once.Lang.Typing.Scope using (Imports; lookupImport)
open import Once.Adequacy.SpecCore.Type using (TyR)
open import Once.Adequacy.SpecCore.Poly using (declS)

module Once.Adequacy.SpecFront.WalkBack
  (Σ : Signature) {Fs : ISig}
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) (ps : List String) (sg : Imports)
  (h-sig : ∀ {m} (Δ : ST.KCtx m) {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ LT.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ T ⌜ t ⌝ᵈ)
  (h-own-sig : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ))
  (h-psig : ∀ {x} → x ∈ ps → lookupImport sg x ≡ nothing)
  (h-word : ∀ {c t} → (c ∶ t) ∈ Σ → WordName c)
  where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)

import Once.Lang.Core.PolyTy as LP
import Once.Lang.Core.Telescope as TL
import Once.Lang.Context as LCx
import Once.Spec.Core.Syntax as SC
open SC.Schema using (arity; kinds; type)
import Once.Spec.Surface.Program as SPr
import Once.Spec.Grade as SG
import Once.Spec.Context as SCx
import Once.Spec.Sub as SS
import Once.Lang.Elaboration as E
open import Once.Lang.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.Lang.Principal using (PrincipalAt)
open import Once.Lang.Module using (Scope; scope; ctxOf)
open import Once.Lang.Core.Translate using (SigSig; ImpSig; TeleSig; SigCF; viewOf)
import Once.Lang.Core.Abstract as A
import Once.Lang.Core.PolyTyping
import Once.Spec.Surface.Typing
import Once.Spec.Core.Typing
open import Once.Adequacy.SpecCore.Schema using (defsS; kindsS)
open import Once.Adequacy.SpecCore.Poly using (module Translate)
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Adequacy.SpecFront.SchemaRen using (SchRen; ρ-of; ρ-inv; kinds-ren; schemaOf-ren)
import Once.Adequacy.SpecFront.DefsRen as DefsRen
import Once.Adequacy.SpecFront.TyRen as TyRen
import Once.Metatheory.TermModel.TySubst as TySubst
open import Once.Adequacy.SpecFront.WalkState {Fs} Σ ps using (WInv)
open import Once.Adequacy.SpecFront.Walk Σ sigop-S fmt ps sg h-sig h-own-sig h-psig h-word using (module AtState; noKinds-S; ground-A)

------------------------------------------------------------------------
-- The two definitions tables, up to numbering
------------------------------------------------------------------------

-- The Spec's table and (the translation of) the compiler's agree schema by
-- schema, each way.
record Rel {s} (S′ S₂ : SC.Defs s) : Set where
  field
    ρ⇒   : ∀ d → Fin (arity (S₂ SC.!! d)) → Fin (arity (S′ SC.!! d))
    ren⇒ : ∀ d → SchRen (S′ SC.!! d) (S₂ SC.!! d) (ρ⇒ d)
    ρ⇐   : ∀ d → Fin (arity (S′ SC.!! d)) → Fin (arity (S₂ SC.!! d))
    ren⇐ : ∀ d → SchRen (S₂ SC.!! d) (S′ SC.!! d) (ρ⇐ d)
open Rel

-- A definition read both ways extends it.
rel-▷ : ∀ {s} {S′ S₂ : SC.Defs s} {T sc sc₂} → Rel S′ S₂ → SPr.SchemaOf T sc → SPr.SchemaOf T sc₂
      → Rel (S′ SC.▷ sc) (S₂ SC.▷ sc₂)
rel-▷ r so so₂ = record
  { ρ⇒   = λ { zero → ρ-of so so₂ ; (suc d) → ρ⇒ r d }
  ; ren⇒ = λ { zero → schemaOf-ren so so₂ ; (suc d) → ren⇒ r d }
  ; ρ⇐   = λ { zero → ρ-of so₂ so ; (suc d) → ρ⇐ r d }
  ; ren⇐ = λ { zero → schemaOf-ren so₂ so ; (suc d) → ren⇐ r d }
  }

------------------------------------------------------------------------
-- A definition with a signature
------------------------------------------------------------------------

module Step {s} {S : LP.Sig Fs s} {imps tele} (ss : SigSig Fs sg) (is : ImpSig S imps) (ts : TeleSig S tele)
            (sgcf : SigCF S) (nm : Fin s → CanonicalName) (w : WInv S (scope sg imps tele) is ts nm)
            {S′ : SC.Defs s} (r : Rel S′ (defsS S)) where

  module At = AtState ss is ts sgcf nm w
  private
    module TR  = TyRen Σ S′ nm
    module TS  = TySubst Σ S′
    module DR⇒ = DefsRen Σ S′ (defsS S) nm (ρ⇒ r)
    module DR⇐ = DefsRen Σ (defsS S) S′ nm (ρ⇐ r)
    module TP′ = Translate S Σ sigop-S
    module PT  = Once.Lang.Core.PolyTyping S
    module SU₂ = Once.Spec.Surface.Typing Σ (defsS S) nm
    module SC₂ = Once.Spec.Core.Typing Σ (defsS S)

    -- (every usage over no locals is the empty one)
    u0 : ∀ {m} {Δ : LP.KCtx m} {Ψ : LCx.Usage 0} {t B π}
       → PT._⊩_⊢[_]_∷_!_ Δ PT.∅ Ψ t B π → PT._⊩_⊢[_]_∷_!_ Δ PT.∅ LCx.Usage.[] t B π
    u0 {Ψ = LCx.Usage.[]} d = d

  -- The body checks in the compiler, at its type, which is principal there.
  step : ∀ {a} (κ : LP.KCtx a) {T sc e e′ A A′}
       → TyR (kindsS κ) A A′ → SPr.SchemaOf T (SC.schema a (kindsS κ) A′) → SPr.SchemaOf T sc
       → SPr.Body Σ S′ nm sc e′ → SPr.Principal Σ S′ nm sc e′ → RX [] e e′
       → (Σ[ Ψ ∈ LCx.Usage 0 ] ctxOf (scope sg imps tele) ⊢ᶜ e ∶ A ⨾ Ψ) × PrincipalAt (ctxOf (scope sg imps tele)) e A
  step {a} κ {T} {sc} {e} {e′} {A} {A′} rA so₂ so b pr rx = chk , At.principal← κ rx rA typed pr₂
    where
      sc₂ = SC.schema a (kindsS κ) A′
      σ  = ρ-of so₂ so
      σ⁻ = ρ-of so so₂
      -- the Spec's numbering to the compiler's, and back
      module B  = TR.Bij σ σ⁻ (ρ-inv so₂ so) (ρ-inv so so₂) {Δ = kinds sc} {Δ′ = kindsS κ} (kinds-ren so₂ so)
      module B⁻ = TR.Bij σ⁻ σ (ρ-inv so so₂) (ρ-inv so₂ so) {Δ = kindsS κ} {Δ′ = kinds sc} (kinds-ren so so₂)

      to-A′ : type sc ST.⟨ B.sv ⟩ ≡ A′
      to-A′ = trans (SchRen.ty (schemaOf-ren so₂ so) ST.var) (TR.⟨⟩-id A′)

      to-sc : A′ ST.⟨ B⁻.sv ⟩ ≡ type sc
      to-sc = trans (SchRen.ty (schemaOf-ren so so₂) ST.var) (TR.⟨⟩-id (type sc))

      -- the body's term, renumbered and moved to the compiler's table
      tm = DR⇒.rn (SPr.Body.term b SC.⟪ B.sv ⟫ₜ)

      chk : Σ[ Ψ ∈ LCx.Usage 0 ] ctxOf (scope sg imps tele) ⊢ᶜ e ∶ A ⨾ Ψ
      chk = At.body-check← κ
              (subst (λ X → SU₂._⊢_⇐_↝_ (kindsS κ) SU₂.∅ e′ X tm) to-A′ (DR⇒.chk (ren⇒ r) (B.chk (SPr.Body.check b))))
              (subst (λ X → SC₂._⊩_⊢[_]_∷_!_ (kindsS κ) SCx.∅ SCx.[] tm X SG.pure) to-A′
                     (DR⇒.core (ren⇒ r) (TS.ty-subst-⊢ B.sv B.rσ (SPr.Body.typed b))))
              rx rA

      -- a compiler check, typed in the core
      typed : ∀ {X Ψ} (D : ctxOf (scope sg imps tele) ⊢ᶜ e ∶ X ⨾ Ψ) → _
      typed D = TP′.trD (u0 (A.abs-⊢ S κ sgcf (proj₂ (E.elabᶜ S (viewOf ss is ts) D))))

      -- the compiler's reading of the Spec's principality
      pr₂ : ∀ {X t} → X SS.<:ᶜ A′
          → SU₂._⊢_⇐_↝_ (kindsS κ) SU₂.∅ e′ X t
          → SC₂._⊩_⊢[_]_∷_!_ (kindsS κ) SCx.∅ SCx.[] t X SG.pure
          → X ≡ A′
      pr₂ {X} sub c T₀ =
        trans (sym (B⁻.back X))
              (trans (cong (ST._⟨ B.sv ⟩)
                       (pr (subst (X ST.⟨ B⁻.sv ⟩ SS.<:ᶜ_) to-sc (TR.<:ᶜ-⟨⟩ B⁻.sv sub))
                           (B⁻.chk (DR⇐.chk (ren⇐ r) c))
                           (TS.ty-subst-⊢ B⁻.sv B⁻.rσ (DR⇐.core (ren⇐ r) T₀))))
                     to-A′)

  private
    module SU′ = Once.Spec.Surface.Typing Σ S′ nm
    module SC′ = Once.Spec.Core.Typing Σ S′

  -- A definition without a signature: its body synthesizes in the compiler,
  -- at a related type, which is principal there.
  step-nosig : ∀ {e e′ A t}
             → SU′._⊢_⇒_↝_ ST.∅ₖ SU′.∅ e′ A t → SC′._⊩_⊢[_]_∷_!_ ST.∅ₖ SCx.∅ SCx.[] t A SG.pure
             → SPr.Principal Σ S′ nm (SC.schema 0 ST.∅ₖ A) e′ → RX [] e e′
             → Σ[ ty ∈ LT.Type ] TyR (kindsS TL.noKinds) ty A
                 × (Σ[ Ψ ∈ LCx.Usage 0 ] ctxOf (scope sg imps tele) ⊢ᵢ e ∶ ty ⨾ Ψ) × PrincipalAt (ctxOf (scope sg imps tele)) e ty
  step-nosig {e} {e′} {A} {t} syn typ pr rx =
    let (ty , rA , Ψ , D) = At.body-synth← TL.noKinds
                              (subst (λ Δ → SU₂._⊢_⇒_↝_ Δ SU₂.∅ e′ A (DR⇒.rn t)) (sym noKinds-S) (DR⇒.syn (ren⇒ r) syn))
                              (subst (λ Δ → SC₂._⊩_⊢[_]_∷_!_ Δ SCx.∅ SCx.[] (DR⇒.rn t) A SG.pure) (sym noKinds-S)
                                     (DR⇒.core (ren⇒ r) typ))
                              rx
    in ty , rA , (Ψ , D) , At.principal← TL.noKinds rx rA typed pr₂
    where
      typed : ∀ {X Ψ} (D : ctxOf (scope sg imps tele) ⊢ᶜ e ∶ X ⨾ Ψ) → _
      typed D = TP′.trD (u0 (A.abs-⊢ S TL.noKinds sgcf (proj₂ (E.elabᶜ S (viewOf ss is ts) D))))

      pr₂ : ∀ {X t′} → X SS.<:ᶜ A
          → SU₂._⊢_⇐_↝_ (kindsS TL.noKinds) SU₂.∅ e′ X t′
          → SC₂._⊩_⊢[_]_∷_!_ (kindsS TL.noKinds) SCx.∅ SCx.[] t′ X SG.pure
          → X ≡ A
      pr₂ {X} {t′} sub c T₀ =
        pr sub (subst (λ Δ → SU′._⊢_⇐_↝_ Δ SU′.∅ e′ X (DR⇐.rn t′)) noKinds-S (DR⇐.chk (ren⇐ r) c))
               (subst (λ Δ → SC′._⊩_⊢[_]_∷_!_ Δ SCx.∅ SCx.[] (DR⇐.rn t′) X SG.pure) noKinds-S (DR⇐.core (ren⇐ r) T₀))

------------------------------------------------------------------------
-- The walk
------------------------------------------------------------------------

open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Sum using (inj₂)
open import Data.Bool using (false)
open import Once.Lang.Module using (ModTele; []; ffi; mono; poly; addImp; addPoly)
open import Once.Lang.Core.Translate using (t-def; wkI; wkT; impDefs; monoDef; polyDef; monoSg; polySg; monoSchema)
open import Once.Lang.Core.Schema using (schemaOf; kindsOf; schemaOf-cf)
import Once.Lang.Type.Instance
import Once.Parser as Parser
import Once.Compile as C
import Once.TypeCheck.Elaborate as TE
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys)
open import Once.TypeCheck.Completeness using (infer-complete)
open import Once.Adequacy.SpecCore.Type using (TyR-uniqueˢ; r-unit; r-void; r-int; r-float; r-*; r-+; r-⇒; r-μ; r-ν; r-rigid;
                                               FunR; r-K; r-Id; r-⊕; r-⊗)
open import Once.Adequacy.SpecCore.Schema using (schS; ptyS)
open import Once.Adequacy.SpecFront.AbsR using (cf-R)
open import Once.Adequacy.SpecFront.SchemaRen using (ren-0)
open import Once.Adequacy.SpecFront.WalkState {Fs} Σ ps using (winv-mono; winv-poly; _∷ⁿ_)
open import Once.Adequacy.SpecFront.Walk Σ sigop-S fmt ps sg h-sig h-own-sig h-psig h-word using (EntriesOK; eok-mono; eok-poly)
open import Once.Adequacy.SpecFront.Align Σ using (Align; al-nil; al-skip; al-mono; al-nosig; al-poly)
open EntriesOK

private
  all-head : ∀ {X : Set} {P : X → Set} {x xs} → All P (x ∷ xs) → P x
  all-head (h ∷ _) = h

  -- a type with no variables in scope is free of them
  mutual
    tyR0-rf : ∀ {Δ : ST.KCtx 0} {A A′} → TyR Δ A A′ → LW.RigidFree A
    tyR0-rf r-unit         = LW.rf-Unit
    tyR0-rf r-void         = LW.rf-Void
    tyR0-rf r-int          = LW.rf-Int
    tyR0-rf r-float        = LW.rf-Float
    tyR0-rf (r-* a b)      = LW.rf-* (tyR0-rf a) (tyR0-rf b)
    tyR0-rf (r-+ a b)      = LW.rf-+ (tyR0-rf a) (tyR0-rf b)
    tyR0-rf (r-⇒ _ a b)    = LW.rf-⇒ (tyR0-rf a) (tyR0-rf b)
    tyR0-rf (r-μ f)        = LW.rf-μ (funR0-rf f)
    tyR0-rf (r-ν _ f)      = LW.rf-ν (funR0-rf f)
    tyR0-rf (r-rigid () _ _)

    funR0-rf : ∀ {Δ : ST.KCtx 0} {F F′} → FunR Δ F F′ → LW.RigidFreeF F
    funR0-rf (r-K a)   = LW.rf-K (tyR0-rf a)
    funR0-rf r-Id      = LW.rf-Id
    funR0-rf (r-⊕ f g) = LW.rf-⊕ (funR0-rf f) (funR0-rf g)
    funR0-rf (r-⊗ f g) = LW.rf-⊗ (funR0-rf f) (funR0-rf g)

  -- (mirrors `inferType`'s `with`)
  infer-ok : ∀ ctx polys body {A Ψ eE d f} → TE.inferElab (ctxWithImportsAndPolys ctx polys) body ≡ TE.success A Ψ eE d f
           → C.inferType ctx polys body ≡ inj₂ A
  infer-ok ctx polys body eq rewrite eq = refl

-- A definition without variables extends the relation.
rel-▷0 : ∀ {s} {S′ S₂ : SC.Defs s} {k₁ k₂ : ST.KCtx 0} {A A₂} → Rel S′ S₂ → A ≡ A₂
       → Rel (S′ SC.▷ SC.schema 0 k₁ A) (S₂ SC.▷ SC.schema 0 k₂ A₂)
rel-▷0 r refl = record
  { ρ⇒   = λ { zero → λ i → i ; (suc d) → ρ⇒ r d }
  ; ren⇒ = λ { zero → ren-0 ; (suc d) → ren⇒ r d }
  ; ρ⇐   = λ { zero → λ i → i ; (suc d) → ρ⇐ r d }
  ; ren⇐ = λ { zero → ren-0 ; (suc d) → ren⇐ r d }
  }

-- The Spec's walk, as the compiler's telescope.
walk← : ∀ {s} {S : LP.Sig Fs s} {imps tele es ds}
          (tl : TL.Tele S) (ss : SigSig Fs sg) (is : ImpSig S imps) (ts : TeleSig S tele) (sgcf : SigCF S) (nm : Fin s → CanonicalName)
          {S′ : SC.Defs s} {tl′ s″} {S″ : SC.Defs s″} {nm″ tl″}
        → Rel S′ (defsS S) → SPr.Walk Σ S′ nm tl′ ds S″ nm″ tl″ → Align ds es
        → WInv S (scope sg imps tele) is ts nm → EntriesOK (scope sg imps tele) es
        → ModTele (scope sg imps tele) es
walk← tl ss is ts sgcf nm r SPr.w-end al-nil w o = []
walk← tl ss is ts sgcf nm r (SPr.w-skip _ wk) (al-skip SPr.nd-sig al)    w o = walk← tl ss is ts sgcf nm r wk al w o
walk← tl ss is ts sgcf nm r (SPr.w-skip _ wk) (al-skip SPr.nd-alias al)  w o = walk← tl ss is ts sgcf nm r wk al w o
walk← tl ss is ts sgcf nm r (SPr.w-skip _ wk) (al-skip SPr.nd-import al) w o = walk← tl ss is ts sgcf nm r wk al w o
-- a monomorphic definition with a signature
walk← {S = S} {imps} {tele} tl ss is ts sgcf nm r (SPr.w-sig so b pr wk) (al-mono {x = x} {e = e} {ty = ty} so₂ g rx al) w o =
  mono refl refl P g D
    (walk← (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss
           (impDefs (x Data.String.== "main") is) (wkT ts) (monoSg sgcf g) (canonical (x ∷ []) ∷ⁿ nm) (rel-▷ r so so₂) wk al
           (winv-mono w g (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o))
  where
    fi = Parser.mkFunInfo x (just ty) e false
    st = Step.step ss is ts sgcf nm w r TL.noKinds (ground-A g) so₂ so b pr rx
    Ψ = proj₁ (proj₁ st)
    D = proj₂ (proj₁ st)
    P = proj₂ st
-- a telescope definition
walk← {S = S} {imps} {tele} tl ss is ts sgcf nm r (SPr.w-sig so b pr wk) (al-poly {x = x} {T = T} {e = e} so₂ rx al) w o =
  poly P D
    (walk← (polyDef {S = S} {sc = scope sg imps tele} {pfi = pfi} {Ψ = Ψ} tl ss is ts sgcf D) ss (wkI is) (t-def zero refl (wkT ts))
           (polySg sgcf pfi) (canonical (x ∷ []) ∷ⁿ nm) (rel-▷ r so so₂) wk al
           (winv-poly pfi w (all-head (kinds o)) (all-head (fresh o))) (eok-poly o))
  where
    pfi = Parser.mkPolyFunInfo x T e
    κ = kindsOf T
    st = Step.step ss is ts sgcf nm w r κ (cf-R κ (Once.Lang.Type.Instance.rigidOf T) (schemaOf-cf T)) so₂ so b pr rx
    Ψ = proj₁ (proj₁ st)
    D = proj₂ (proj₁ st)
    P = proj₂ st
-- one without a signature: the type its body synthesizes
walk← {S = S} {imps} {tele} tl ss is ts sgcf nm r (SPr.w-nosig syn typ pr wk) (al-nosig {x = x} {e = e} rx al) w o =
  mono refl (infer-ok _ _ e (proj₂ (proj₂ (proj₂ (infer-complete D))))) P g D
    (walk← (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss
           (impDefs (x Data.String.== "main") is) (wkT ts) (monoSg sgcf g) (canonical (x ∷ []) ∷ⁿ nm)
           (rel-▷0 r (TyR-uniqueˢ rA (ground-A g))) wk al
           (winv-mono w g (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o))
  where
    st = Step.step-nosig ss is ts sgcf nm w r syn typ pr rx
    ty = proj₁ st
    rA = proj₁ (proj₂ st)
    Ψ = proj₁ (proj₁ (proj₂ (proj₂ st)))
    D = proj₂ (proj₁ (proj₂ (proj₂ st)))
    P = proj₂ (proj₂ (proj₂ st))
    g = tyR0-rf rA
    fi = Parser.mkFunInfo x nothing e false
