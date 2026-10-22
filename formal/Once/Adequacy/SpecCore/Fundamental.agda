{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Fundamental — the fundamental lemma of the meaning
-- relation (plan 0.121 §3.5).
--
-- A compiler core derivation `D` (over its type variables) and its Spec
-- translation `trD D` mean related computations: at related instances of the
-- variables and related environments, the compiler's meaning of `D`
-- instantiated and the Spec's meaning of `trD D` are related at the related
-- types and grades (`Fund D`), given related definitions environments.
--
-- Both sides move their derivations along equations where the indices agree
-- only propositionally (`instantiate`'s `subst`, `trD`'s `atS`); each is
-- crossed by one lemma (`L-at`, `S-at`), the graphs having one proof each.
-- The rules whose meanings differ in representation more than this — the
-- recursion formers, coercions, the loop, the signature's declarations,
-- definitions and arithmetic — are the cases record `Cases`, discharged in
-- their own modules.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Internal.Contract using (ISig)
open import Once.Internal.Name using (showCanonical; WordName)
import Once.Internal.Core.PolyTy as LP
open import Once.Spec.Signature using (Signature; _∶_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Adequacy.SpecCore.Poly using (declS)

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Fundamental
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) where

open import Data.Unit using (⊤; tt)
import Data.Empty
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂) renaming ([_,_]′ to [_,_]′′)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Spec.Grade as LG
import Once.Internal.Type.Sub as LS
import Once.Spec.Sub as LS
import Once.Internal.Context as LC
import Once.Spec.Grade as SG
import Once.Spec.Type as ST
import Once.Spec.Context as SCx
import Once.Internal.Graded as LGr
import Once.Internal.Core.PolyTyping S as PT
import Once.Internal.Core.PolySub as PS
import Once.Internal.Core.Typing S as GT
import Once.Internal.Core.Meaning S as GM
open import Once.Adequacy.SpecCore.Schema using (defsS; kindsS)
open import Once.Adequacy.SpecCore.Context using (uS-zero)
open import Once.Adequacy.SpecCore.Type using (⊑π-S)
open import Once.Adequacy.SpecCore.Poly using (module Translate)
open Translate S Σ sigop-S
import Once.Spec.Core.Typing Σ S′ as S⊢
import Once.Spec.Core.Meaning Σ fmt S′ as SM
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Env S Σ fmt

------------------------------------------------------------------------
-- Contexts, canonically
------------------------------------------------------------------------

crΓ : ∀ {m n} (Γ : PT.PCtx m n) → CR S Γ (pctxS Γ)
crΓ PT.∅           = cr-∅
crΓ (Γ PT., A ^ q) = cr-▸ (crΓ Γ) (ptr A)

------------------------------------------------------------------------
-- The statement
------------------------------------------------------------------------

module _ (ρ : GM.DefSem) (ρ′ : SM.DefSem) where


  -- `D` and `trD D` mean related computations.
  Fund : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ t A π} → PT._⊩_⊢[_]_∷_!_ Δ Γ Ψ t A π → Set
  Fund {Δ = Δ} {Γ} {Ψ} {A = A} {π} D =
    ∀ {σ σ′} (r : LP.Respects Δ σ) (r′ : ST.Respects (kindsS Δ) ST.∅ₖ σ′) (g : InstG σ σ′) {γ γ′}
    → EnvR g (crΓ Γ) (ur Ψ) γ γ′
    → MR (pr π) (ValR (GR-inst (ptr A) g)) (GM.⟦ PT.instantiate σ r D ⟧ fmt ρ γ) (SM.⟦ trD D ⟧ ρ′ σ′ r′ γ′)

  ----------------------------------------------------------------------
  -- Crossing the equations
  ----------------------------------------------------------------------

  module _ {m} {σ : LP.GSub m} {σ′ : ST.TySub m 0} (g : InstG σ σ′) where

    -- the Spec side, along `atS`
    S-at : ∀ {n} {Δ′ : ST.KCtx m} {Γ : PT.PCtx m n} {Γ′ Ψ Φ₁ Φ₂ A₁ A₂ π π₁ π₂ t′ Y}
           (e₁ : Φ₁ ≡ Φ₂) (e₂ : A₁ ≡ A₂) (e₃ : π₁ ≡ π₂)
           (d′ : S⊢._⊩_⊢[_]_∷_!_ Δ′ Γ′ Φ₁ t′ A₁ π₁) {r′ : ST.Respects Δ′ ST.∅ₖ σ′}
           (c : CR S Γ Γ′) (u₁ : UR Ψ Φ₁) (u₂ : UR Ψ Φ₂)
           (g₁ : GR Y (A₁ ST.⟨ σ′ ⟩)) (g₂ : GR Y (A₂ ST.⟨ σ′ ⟩)) (p₁ : PR π π₁) (p₂ : PR π π₂)
           (L : GM.Env (Γ PT.⟪ σ ⟫ᶜ) Ψ → LGr.M π LGr.⟦ Y ⟧ᵛ)
         → (∀ {γ γ′} → EnvR g c u₁ γ γ′ → MR p₁ (ValR g₁) (L γ) (SM.⟦ d′ ⟧ ρ′ σ′ r′ γ′))
         → (∀ {γ γ′} → EnvR g c u₂ γ γ′ → MR p₂ (ValR g₂) (L γ) (SM.⟦ atS e₁ e₂ e₃ d′ ⟧ ρ′ σ′ r′ γ′))
    S-at refl refl refl d′ c u₁ u₂ g₁ g₂ p₁ p₂ L h =
      subst (λ u → ∀ {γ γ′} → EnvR g c u γ γ′ → MR p₂ (ValR g₂) (L γ) (SM.⟦ d′ ⟧ ρ′ σ′ _ γ′)) (UR-unique u₁ u₂)
        (subst (λ x → ∀ {γ γ′} → EnvR g c u₁ γ γ′ → MR p₂ (ValR x) (L γ) (SM.⟦ d′ ⟧ ρ′ σ′ _ γ′)) (GR-unique g₁ g₂)
          (subst (λ p → ∀ {γ γ′} → EnvR g c u₁ γ γ′ → MR p (ValR g₁) (L γ) (SM.⟦ d′ ⟧ ρ′ σ′ _ γ′)) (PR-unique p₁ p₂) h))

  -- the compiler side, along `subst` on the type
  L-at : ∀ {n} {Γ : LC.Ctx n} {Ψ t X Y π π′ B′} (e : X ≡ Y) (d : Γ GT.⊢[ Ψ ] t ∷ X ! π)
         (p : PR π π′) (gX : GR X B′) (gY : GR Y B′) {γ y}
       → MR p (ValR gX) (GM.⟦ d ⟧ fmt ρ γ) y
       → MR p (ValR gY) (GM.⟦ subst (λ Z → Γ GT.⊢[ Ψ ] t ∷ Z ! π) e d ⟧ fmt ρ γ) y
  L-at refl d p gX gY h = subst (λ g → MR p (ValR g) (GM.⟦ d ⟧ fmt ρ _) _) (GR-unique gX gY) h

  ----------------------------------------------------------------------
  -- The rules discharged elsewhere
  ----------------------------------------------------------------------

  -- (the judgment, briefly)
  private
    _⊩_⊢[_]_∷_!_ = PT._⊩_⊢[_]_∷_!_

  record Cases : Set where
    field
      c-roll   : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ π F t} (wf : LP.WFFun Δ F)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ LP.⟦ F ⟧F (LP.μ-type F) ! π) → Fund d → Fund (PT.⊢roll wf d)
      c-fold   : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψa Ψt π π₁ π₂ F A alg t}
                 (u : LG.pure Once.Spec.Grade.⊑π π) (wf : LP.WFFun Δ F)
                 (da : Δ ⊩ Γ ⊢[ Ψa ] alg ∷ LP.⟦ F ⟧F A LP.⇒[ LG.mk-kind LG.Many π ] A ! π₁)
                 (dt : Δ ⊩ Γ ⊢[ Ψt ] t ∷ LP.μ-type F ! π₂) → Fund da → Fund dt → Fund (PT.⊢fold u wf da dt)
      c-unfold : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψc Ψs φ π₁ π₂ F A c x} (wf : LP.WFFun Δ F)
                 (dc : Δ ⊩ Γ ⊢[ Ψc ] c ∷ A LP.⇒[ LG.mk-kind LG.Many (LG.fin φ) ] LP.⟦ F ⟧F A ! π₁)
                 (dx : Δ ⊩ Γ ⊢[ Ψs ] x ∷ A ! π₂) → Fund dc → Fund dx → Fund (PT.⊢unfold wf dc dx)
      c-out    : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ φ π₁ F t} (wf : LP.WFFun Δ F)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ LP.ν-type F φ ! π₁) → Fund d → Fund (PT.⊢out wf d)
      c-iter   : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψf Ψs π₁ π₂ A B f x}
                 (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ A LP.⇒[ LG.mk-kind LG.Many LG.act ] (B LP.+ A) ! π₁)
                 (dx : Δ ⊩ Γ ⊢[ Ψs ] x ∷ A ! π₂) → Fund df → Fund dx → Fund (PT.⊢iter df dx)
      c-coerce : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ π A B t} (p : A PS.<:ₚ B)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund d → Fund (PT.⊢coerce p d)
      c-lit-int   : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {i} → Fund (PT.⊢lit-int {Δ = Δ} {Γ = Γ} {i = i})
      c-lit-float : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {d} → Fund (PT.⊢lit-float {Δ = Δ} {Γ = Γ} {d = d})
      c-prim   : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ π t} (p : _)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ LP.⌈ _ ⌉ ! π) → Fund d → Fund (PT.⊢prim {Δ = Δ} {Γ = Γ} {Ψ = Ψ} {π = π} {t = t} p d)
      c-sigop  : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {A} c k h rf wn mem
                 → Fund (PT.⊢sigop {Δ = Δ} {Γ = Γ} {A = A} c k h rf wn mem)
      c-ref    : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} d τ rs → Fund (PT.⊢ref {Δ = Δ} {Γ = Γ} d τ rs)

  ----------------------------------------------------------------------
  -- The fundamental lemma
  ----------------------------------------------------------------------

  -- (a pure value of a sum, taken apart on both sides)
  private
    case-R : ∀ {A A′ B B′} (a : GR A A′) (b : GR B B′) {X Y : Set} {π π′} (p : PR π π′) {R : X → Y → Set}
             {l : LGr.⟦ A ⟧ᵛ → LGr.M π X} {r : LGr.⟦ B ⟧ᵛ → LGr.M π X} {l′ r′}
           → (∀ {x x′} → ValR a x x′ → MR p R (l x) (l′ x′))
           → (∀ {x x′} → ValR b x x′ → MR p R (r x) (r′ x′))
           → ∀ v v′ → ValR (g-+ a b) v v′
           → MR p R ([ l , r ]′′ v) ([ l′ , r′ ]′′ v′)
    case-R a b p kl kr (inj₁ x) (inj₁ x′) h = kl h
    case-R a b p kl kr (inj₂ x) (inj₂ x′) h = kr h
    case-R a b p kl kr (inj₁ x) (inj₂ x′) ()
    case-R a b p kl kr (inj₂ x) (inj₁ x′) ()

  module _ (cases : Cases) where
    open Cases cases

    fund : ∀ {m n} {Δ : LP.KCtx m} {Γ : PT.PCtx m n} {Ψ t A π} (D : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund D

    fund {Γ = Γ} (PT.⊢var i) {σ} {σ′} r r′ g e =
      L-at (PT.lookup-⟪⟫ Γ σ i) (GT.⊢var i) pr-pure gX (GR-inst (ptr (PT.lookupP Γ i)) g)
        (S-at g (eqᵘ-var i) (sym (lookupS Γ i)) refl (S⊢.⊢var i) (crΓ Γ) (ur-single i) (ur _) (GR-lookup g (crΓ Γ) i) gX pr-pure pr-pure
              (λ γ → GM.⟦ GT.⊢var {Γ = Γ PT.⟪ σ ⟫ᶜ} i ⟧ fmt ρ γ) (lookup-R g (crΓ Γ) i) e)
      where gX = subst (λ Z → GR Z _) (sym (PT.lookup-⟪⟫ Γ σ i)) (GR-inst (ptr (PT.lookupP Γ i)) g)

    fund (PT.⊢lam {q = LG.Zero} {q' = LG.Zero} le d) r r′ g e = fund d r r′ g e
    fund (PT.⊢lam {q = LG.One}  {q' = LG.Zero} le d) r r′ g e = λ _ → fund d r r′ g e
    fund (PT.⊢lam {q = LG.One}  {q' = LG.One}  le d) r r′ g e = λ v → fund d r r′ g (e , v)
    fund (PT.⊢lam {q = LG.Many} {q' = LG.Zero} le d) r r′ g e = λ v → fund d r r′ g e
    fund (PT.⊢lam {q = LG.Many} {q' = LG.One}  le d) r r′ g e = λ v → fund d r r′ g (e , v)
    fund (PT.⊢lam {q = LG.Many} {q' = LG.Many} le d) r r′ g e = λ v → fund d r r′ g (e , v)
    fund (PT.⊢lam {q = LG.Zero} {q' = LG.One}  () d)
    fund (PT.⊢lam {q = LG.Zero} {q' = LG.Many} () d)
    fund (PT.⊢lam {q = LG.One}  {q' = LG.Many} () d)

    fund PT.⊢unit r r′ g e = tt

    fund (PT.⊢sub-eff {π = π} {π′} x d) r r′ g e = sub-R x (⊑π-S x) (pr π) (pr π′) (fund d r r′ g e)
    fund {Γ = Γ} (PT.⊢sub-use {Ψ = Ψ} {Ψ′} x d) r r′ g e =
      fund d r r′ g (restrict-R g (crΓ Γ) x _ (ur Ψ′) (ur Ψ) e)

    fund (PT.⊢fst {π = π} d) r r′ g e = fmap-R (pr π) (fund d r r′ g e) proj₁
    fund (PT.⊢snd {π = π} d) r r′ g e = fmap-R (pr π) (fund d r r′ g e) proj₂
    fund (PT.⊢inl {π = π} d) r r′ g e = fmap-R (pr π) (fund d r r′ g e) (λ h → h)
    fund (PT.⊢inr {π = π} d) r r′ g e = fmap-R (pr π) (fund d r r′ g e) (λ h → h)
    fund (PT.⊢absurd {π = π} d) r r′ g e = bind-R (pr π) (fund d r r′ g e) (λ {x} _ → ⊥-elim′ x)
      where ⊥-elim′ : ∀ {X : Set} → Data.Empty.⊥ → X
            ⊥-elim′ ()

    fund {Γ = Γ} (PT.⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = LG.Zero} {π} {π₁} {π₂} {B = B} df dx) {σ} r r′ g e =
      S-at g (eqᵘ-app Ψ₁ LG.Zero Ψ₂) refl (eqᵍ-app π₁ LG.Zero π₂ π) (S⊢.⊢app (trD df) (trD dx)) (crΓ Γ) (ur-+ (ur Ψ₁) (ur-* qr-zero (ur Ψ₂))) (ur _) gB gB (pr-· (pr π₁) (pr π)) (pr _)
           _
           (λ e₀ → bindᵍ-R (pr π₁) (pr π) (fund df r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψ₁) e₀)) (λ vf → vf)) e
      where gB = GR-inst (ptr B) g
    fund {Γ = Γ} (PT.⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = LG.One} {π} {π₁} {π₂} {B = B} df dx) {σ} r r′ g e =
      S-at g (eqᵘ-app Ψ₁ LG.One Ψ₂) refl (eqᵍ-app π₁ LG.One π₂ π) (S⊢.⊢app (trD df) (trD dx)) (crΓ Γ) (ur-+ (ur Ψ₁) (ur-* qr-one (ur Ψ₂))) (ur _) gB gB
           (pr-· (pr π₁) (pr-· (pr π₂) (pr π))) (pr _)
           _
           (λ e₀ → bindᵍ-R (pr π₁) (pr-· (pr π₂) (pr π)) (fund df r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψ₁) e₀))
                     (λ vf → bindᵍ-R (pr π₂) (pr π) (fund dx r r′ g (env*One-envʳ-R g (crΓ Γ) _ _ (ur Ψ₂) e₀)) vf)) e
      where gB = GR-inst (ptr B) g
    fund {Γ = Γ} (PT.⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = LG.Many} {π} {π₁} {π₂} {B = B} df dx) {σ} r r′ g e =
      S-at g (eqᵘ-app Ψ₁ LG.Many Ψ₂) refl (eqᵍ-app π₁ LG.Many π₂ π) (S⊢.⊢app (trD df) (trD dx)) (crΓ Γ) (ur-+ (ur Ψ₁) (ur-* qr-many (ur Ψ₂))) (ur _) gB gB
           (pr-· (pr π₁) (pr-· (pr π₂) (pr π))) (pr _)
           _
           (λ e₀ → bindᵍ-R (pr π₁) (pr-· (pr π₂) (pr π)) (fund df r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψ₁) e₀))
                     (λ vf → bindᵍ-R (pr π₂) (pr π) (fund dx r r′ g (env*Many-envʳ-R g (crΓ Γ) _ _ (ur Ψ₂) e₀)) vf)) e
      where gB = GR-inst (ptr B) g

    fund {Γ = Γ} (PT.⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = LG.Zero} {π₁} {π₂} {B = B} de db) {σ} r r′ g e =
      S-at g (eqᵘ-app Ψ₂ LG.Zero Ψ₁) refl (eqᵍ-let LG.Zero π₁ π₂) (S⊢.⊢let (trD de) (trD db)) (crΓ Γ) (ur-+ (ur Ψ₂) (ur-* qr-zero (ur Ψ₁))) (ur _) gB gB (pr π₂) (pr _)
           _
           (λ e₀ → fund db r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψ₂) e₀)) e
      where gB = GR-inst (ptr B) g
    fund {Γ = Γ} (PT.⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = LG.One} {π₁} {π₂} {B = B} de db) {σ} r r′ g e =
      S-at g (eqᵘ-app Ψ₂ LG.One Ψ₁) refl (eqᵍ-let LG.One π₁ π₂) (S⊢.⊢let (trD de) (trD db)) (crΓ Γ) (ur-+ (ur Ψ₂) (ur-* qr-one (ur Ψ₁))) (ur _) gB gB (pr-· (pr π₁) (pr π₂)) (pr _)
           _
           (λ e₀ → bindᵍ-R (pr π₁) (pr π₂) (fund de r r′ g (env*One-envʳ-R g (crΓ Γ) _ _ (ur Ψ₁) e₀))
                     (λ v → fund db r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψ₂) e₀ , v))) e
      where gB = GR-inst (ptr B) g
    fund {Γ = Γ} (PT.⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = LG.Many} {π₁} {π₂} {B = B} de db) {σ} r r′ g e =
      S-at g (eqᵘ-app Ψ₂ LG.Many Ψ₁) refl (eqᵍ-let LG.Many π₁ π₂) (S⊢.⊢let (trD de) (trD db)) (crΓ Γ) (ur-+ (ur Ψ₂) (ur-* qr-many (ur Ψ₁))) (ur _) gB gB (pr-· (pr π₁) (pr π₂)) (pr _)
           _
           (λ e₀ → bindᵍ-R (pr π₁) (pr π₂) (fund de r r′ g (env*Many-envʳ-R g (crΓ Γ) _ _ (ur Ψ₁) e₀))
                     (λ v → fund db r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψ₂) e₀ , v))) e
      where gB = GR-inst (ptr B) g

    fund {Γ = Γ} (PT.⊢pair {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} {A} {B} da db) {σ} r r′ g e =
      S-at g (eqᵘ-+ Ψ₁ Ψ₂) refl (eqᵍ-· π₁ π₂) (S⊢.⊢pair (trD da) (trD db)) (crΓ Γ) (ur-+ (ur Ψ₁) (ur Ψ₂)) (ur _) gAB gAB (pr-· (pr π₁) (pr π₂)) (pr _)
           _
           (λ e₀ → bindᵍ-R (pr π₁) (pr π₂) (fund da r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψ₁) e₀))
                     (λ va → fmap-R (pr π₂) (fund db r r′ g (envʳ-R g (crΓ Γ) _ _ (ur Ψ₂) e₀)) (λ vb → va , vb))) e
      where gAB = GR-inst (ptr (A LP.* B)) g

    fund {Γ = Γ} (PT.⊢case {Ψs = Ψs} {Ψ} {qℓ} {qr₀} {π₁} {π₂} {A} {B} {C} ds dl dr) {σ} r r′ g e =
      S-at g (eqᵘ-+ Ψs Ψ) refl (eqᵍ-· π₁ π₂) (S⊢.⊢case (trD ds) (trD dl) (trD dr)) (crΓ Γ) (ur-+ (ur Ψs) (ur Ψ)) (ur _) gC gC (pr-· (pr π₁) (pr π₂)) (pr _)
           _
           (λ e₀ → bindᵍ-R (pr π₁) (pr π₂) (fund ds r r′ g (envˡ-R g (crΓ Γ) _ _ (ur Ψs) e₀))
                     (λ {v} {v′} h → case-R (GR-inst (ptr A) g) (GR-inst (ptr B) g) (pr π₂)
                        (λ ha → fund dl r r′ g (bind-env-R g (crΓ Γ) (ptr A) (ur Ψ) (qr qℓ) (envʳ-R g (crΓ Γ) _ _ (ur Ψ) e₀) ha))
                        (λ hb → fund dr r r′ g (bind-env-R g (crΓ Γ) (ptr B) (ur Ψ) (qr qr₀) (envʳ-R g (crΓ Γ) _ _ (ur Ψ) e₀) hb))
                        v v′ h)) e
      where gC = GR-inst (ptr C) g

    fund (PT.⊢roll wf d)            = c-roll wf d (fund d)
    fund (PT.⊢fold u wf da dt)      = c-fold u wf da dt (fund da) (fund dt)
    fund (PT.⊢unfold wf dc dx)      = c-unfold wf dc dx (fund dc) (fund dx)
    fund (PT.⊢out wf d)             = c-out wf d (fund d)
    fund (PT.⊢iter df dx)           = c-iter df dx (fund df) (fund dx)
    fund (PT.⊢coerce p d)           = c-coerce p d (fund d)
    fund PT.⊢lit-int                = c-lit-int
    fund PT.⊢lit-float              = c-lit-float
    fund (PT.⊢prim p d)             = c-prim p d (fund d)
    fund (PT.⊢sigop c k h rf wn mem)   = c-sigop c k h rf wn mem
    fund (PT.⊢ref d τ rs)           = c-ref d τ rs
