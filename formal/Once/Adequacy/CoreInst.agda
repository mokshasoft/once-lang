-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreInst — plan 0.104 E.2 (i): the core's rigid
-- substitution on derivations, and that instantiating an abstraction IS it.
--
-- `ρ̂ᶜ` maps a ground derivation whose types mention rigids to the derivation
-- at the substituted types, rule by rule (`ρ̂ = absTy Δ _ ⟪ τ ⟫`, the surface's
-- `RigidSubst.ρ̂`). Its term is `absTm Δ t ⟪ τ ⟫ₜ` definitionally, the term
-- `instantiate ∘ abs-⊢` produces. The round trip of CoreAbsSem (arity 0) is the
-- instance at `τ` of the empty context.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; KCtx; GSub; Respects)

module Once.Adequacy.CoreInst {s : ℕ} (S : Sig s) {m : ℕ} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import Once.Type as T
open T using (Type; mk-kind; Many; pure; μ-type; ν-type; ⟦_⟧T)
import Once.Surface.Context as C
open import Once.Spec.Core.PolyTy using (_⟪_⟫; _!!_; type; ⟨⟩-⟪⟫; ⌈⌉-⟪⟫; ⟦⟧F-⟪⟫)
import Once.Spec.Core.PolyTy as Ty
open import Once.Spec.Core.AbsTy using (absTy; absF; abs-⟪⟫; absTy-⟦⟧; absTy-ground)
import Once.Spec.Core.Syntax S as G
import Once.Spec.Core.Typing S as GT
open GT using (_⊢[_]_∷_!_)
import Once.Spec.Core.PolyTyping S as PT
open PT using (_⟪_⟫ᶜ; _⟪_⟫ₜ)
open import Once.Spec.Core.Abstract S using (SigGround; absCtx; absTm; abs-⊢; primDom-abs; primCod-abs; absCtx-lookup)
import Once.TypeCheck.RigidSubst Δ τ r as RS
open RS using (ρ̂; ρ̂F; ρ̂S; ρ̂-⟦⟧; ρ̂-wf; ρ̂-<:; ρ̂-rf; ρ̂-base; lookup-ρ̂)
open import Once.Adequacy.CoreAbsSem S using (tr; tr-subst; tr-lam; tr-app; tr-let; tr-unit; tr-pair; tr-fst; tr-snd;
  tr-inl; tr-inr; tr-case; tr-absurd; tr-roll; tr-fold; tr-unfold; tr-out; tr-coerce; tr-lit-int; tr-lit-float;
  tr-lit-str; tr-prim; tr-sigop; tr-sub-eff; tr-ref)

ρ̂ₜ : ∀ {n} → G.Tm n → G.Tm n
ρ̂ₜ t = absTm Δ t ⟪ τ ⟫ₜ

-- The primitives' types are ground.
ρ̂-dom : ∀ p → ρ̂ (G.primDom p) ≡ G.primDom p
ρ̂-dom p = trans (cong (_⟪ τ ⟫) (primDom-abs Δ p)) (⌈⌉-⟪⟫ (G.primDom p) τ)

ρ̂-cod : ∀ p → ρ̂ (G.primCod p) ≡ G.primCod p
ρ̂-cod p = trans (cong (_⟪ τ ⟫) (primCod-abs Δ p)) (⌈⌉-⟪⟫ (G.primCod p) τ)

module _ (sg : SigGround) where

  -- A definition's instance, substituted, is the substituted instance.
  ρ̂-ref : ∀ d (τ′ : GSub (Once.Spec.Core.PolyTy.arity (S !! d)))
        → ρ̂ (type (S !! d) ⟪ τ′ ⟫) ≡ type (S !! d) ⟪ (λ i → ρ̂ (τ′ i)) ⟫
  ρ̂-ref d τ′ = trans (cong (_⟪ τ ⟫) (abs-⟪⟫ Δ τ′ (sg d))) (⟨⟩-⟪⟫ (type (S !! d)) (λ i → absTy Δ (τ′ i)) τ)

  ρ̂ᶜ : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} → Γ ⊢[ Ψ ] t ∷ A ! π → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ t ∷ ρ̂ A ! π
  ρ̂ᶜ {Γ = Γ} (GT.⊢var i) = subst (λ X → ρ̂S Γ ⊢[ _ ] G.var i ∷ X ! pure) (lookup-ρ̂ Γ i) (GT.⊢var i)
  ρ̂ᶜ (GT.⊢lam le d)    = GT.⊢lam le (ρ̂ᶜ d)
  ρ̂ᶜ (GT.⊢app f x)     = GT.⊢app (ρ̂ᶜ f) (ρ̂ᶜ x)
  ρ̂ᶜ (GT.⊢let e b)     = GT.⊢let (ρ̂ᶜ e) (ρ̂ᶜ b)
  ρ̂ᶜ GT.⊢unit          = GT.⊢unit
  ρ̂ᶜ (GT.⊢pair a b)    = GT.⊢pair (ρ̂ᶜ a) (ρ̂ᶜ b)
  ρ̂ᶜ (GT.⊢fst p)       = GT.⊢fst (ρ̂ᶜ p)
  ρ̂ᶜ (GT.⊢snd p)       = GT.⊢snd (ρ̂ᶜ p)
  ρ̂ᶜ (GT.⊢inl a)       = GT.⊢inl (ρ̂ᶜ a)
  ρ̂ᶜ (GT.⊢inr b)       = GT.⊢inr (ρ̂ᶜ b)
  ρ̂ᶜ (GT.⊢case s l x)  = GT.⊢case (ρ̂ᶜ s) (ρ̂ᶜ l) (ρ̂ᶜ x)
  ρ̂ᶜ (GT.⊢absurd e)    = GT.⊢absurd (ρ̂ᶜ e)
  ρ̂ᶜ {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢roll {F = F} {t = t} wf d) =
    GT.⊢roll (ρ̂-wf wf) (subst (λ X → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ t ∷ X ! π) (ρ̂-⟦⟧ F (μ-type F)) (ρ̂ᶜ d))
  ρ̂ᶜ {Γ = Γ} {π = π} (GT.⊢fold {Ψa = Ψa} {F = F} {A = A} {alg = alg} wf a t) =
    GT.⊢fold (ρ̂-wf wf)
      (subst (λ X → ρ̂S Γ ⊢[ Ψa ] ρ̂ₜ alg ∷ X T.⇒[ mk-kind Many π ] ρ̂ A ! π) (ρ̂-⟦⟧ F A) (ρ̂ᶜ a))
      (ρ̂ᶜ t)
  ρ̂ᶜ {Γ = Γ} (GT.⊢unfold {Ψc = Ψc} {π = π} {π′ = π′} {F = F} {A = A} {c = c} wf k x) =
    GT.⊢unfold (ρ̂-wf wf)
      (subst (λ X → ρ̂S Γ ⊢[ Ψc ] ρ̂ₜ c ∷ ρ̂ A T.⇒[ mk-kind Many π ] X ! π′) (ρ̂-⟦⟧ F A) (ρ̂ᶜ k))
      (ρ̂ᶜ x)
  ρ̂ᶜ {Γ = Γ} {Ψ = Ψ} (GT.⊢out {π = π} {F = F} {t = t} wf d) =
    subst (λ X → ρ̂S Γ ⊢[ Ψ ] G.out (ρ̂ₜ t) ∷ X ! π) (sym (ρ̂-⟦⟧ F (ν-type F π))) (GT.⊢out (ρ̂-wf wf) (ρ̂ᶜ d))
  ρ̂ᶜ (GT.⊢coerce p d)  = GT.⊢coerce (ρ̂-<: p) (ρ̂ᶜ d)
  ρ̂ᶜ GT.⊢lit-int       = GT.⊢lit-int
  ρ̂ᶜ GT.⊢lit-float     = GT.⊢lit-float
  ρ̂ᶜ GT.⊢lit-str       = GT.⊢lit-str
  ρ̂ᶜ {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢prim {t = t} p d) =
    subst (λ X → ρ̂S Γ ⊢[ Ψ ] G.prim p (ρ̂ₜ t) ∷ X ! π) (sym (ρ̂-cod p))
      (GT.⊢prim p (subst (λ X → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ t ∷ X ! π) (ρ̂-dom p) (ρ̂ᶜ d)))
  ρ̂ᶜ {Γ = Γ} (GT.⊢sigop {A = A} c k h g) =
    subst (λ X → ρ̂S Γ ⊢[ C.zeroUsage ] G.sigop c A ∷ X ! pure) (sym (ρ̂-rf g)) (GT.⊢sigop c k h g)
  ρ̂ᶜ (GT.⊢sub-eff g d) = GT.⊢sub-eff g (ρ̂ᶜ d)
  ρ̂ᶜ {Γ = Γ} (GT.⊢ref d τ′ k) =
    subst (λ X → ρ̂S Γ ⊢[ C.zeroUsage ] G.ref d (λ i → ρ̂ (τ′ i)) ∷ X ! pure) (sym (ρ̂-ref d τ′))
      (GT.⊢ref d (λ i → ρ̂ (τ′ i)) (λ i e → ρ̂-base (k i e)))

  -- The context of the instantiated abstraction is the substituted context.
  ρ̂S-abs : ∀ {n} (Γ : C.Ctx n) → absCtx Δ Γ ⟪ τ ⟫ᶜ ≡ ρ̂S Γ
  ρ̂S-abs C.∅           = refl
  ρ̂S-abs (Γ C., A ^ q) = cong (λ G → G C., ρ̂ A ^ q) (ρ̂S-abs Γ)

  ----------------------------------------------------------------------
  -- THE ROUND TRIP AT AN INSTANCE: instantiating the abstraction is the
  -- substitution. CoreAbsSem's `RT-id` (arity 0) with `ρ̂ᶜ D` for `D`.
  ----------------------------------------------------------------------

  private
    IA : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} → Γ ⊢[ Ψ ] t ∷ A ! π
       → absCtx Δ Γ ⟪ τ ⟫ᶜ ⊢[ Ψ ] ρ̂ₜ t ∷ ρ̂ A ! π
    IA D = PT.instantiate τ r (abs-⊢ Δ sg D)

    -- An abstraction-side `subst` under `instantiate` (CoreAbsSem's, at any arity).
    tr-isubst′ : ∀ {n} {Γp : PT.PCtx m n} {Γ : C.Ctx n} {Ψ} {tp : PT.PTm m n} {t : G.Tm n} {A : Type} {π}
                   {Y : Set} {f : Y → Once.Spec.Core.PolyTy.Ty m} {y₁ y₂ : Y}
                   {eΓ : Γp ⟪ τ ⟫ᶜ ≡ Γ} {et : tp ⟪ τ ⟫ₜ ≡ t} {eA : f y₂ ⟪ τ ⟫ ≡ A} (e : y₁ ≡ y₂)
                   (D : PT._⊩_⊢[_]_∷_!_ Δ Γp Ψ tp (f y₁) π)
               → tr eΓ et eA (PT.instantiate τ r (subst (λ y → PT._⊩_⊢[_]_∷_!_ Δ Γp Ψ tp (f y) π) e D))
                 ≡ tr eΓ et (trans (cong (λ y → f y ⟪ τ ⟫) e) eA) (PT.instantiate τ r D)
    tr-isubst′ refl D = refl

    -- A transport of the instantiated side meets a `subst` of the substituted side.
    close : ∀ {n} {Γ' Γ : C.Ctx n} {Ψ t A₀ X π} (eΓ : Γ' ≡ Γ)
              {D : Γ' ⊢[ Ψ ] t ∷ A₀ ! π} {E : Γ ⊢[ Ψ ] t ∷ A₀ ! π} (E* e : A₀ ≡ X)
          → tr eΓ refl refl D ≡ E → tr eΓ refl E* D ≡ subst (λ Y → Γ ⊢[ Ψ ] t ∷ Y ! π) e E
    close refl refl refl refl = refl

    closeF : ∀ {n} {Γ' Γ : C.Ctx n} {Ψ t π} {Y : Set} (f : Y → Type) {y₀ y₁ : Y} (eΓ : Γ' ≡ Γ)
               {D : Γ' ⊢[ Ψ ] t ∷ f y₀ ! π} {E : Γ ⊢[ Ψ ] t ∷ f y₀ ! π} (E* : f y₀ ≡ f y₁) (e : y₀ ≡ y₁)
           → tr eΓ refl refl D ≡ E → tr eΓ refl E* D ≡ subst (λ y → Γ ⊢[ Ψ ] t ∷ f y ! π) e E
    closeF f refl refl refl refl = refl

    tr-var-subst : ∀ {n} {Γ' Γ : C.Ctx n} (i : _) (eΓ : Γ' ≡ Γ) {X} (eA : C.lookup Γ' i ≡ X) (e : C.lookup Γ i ≡ X)
                 → tr eΓ refl eA (GT.⊢var i) ≡ subst (λ Y → Γ ⊢[ C.singleUse i T.One ] G.var i ∷ Y ! pure) e (GT.⊢var i)
    tr-var-subst i refl refl refl = refl

  inst-abs : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} (D : Γ ⊢[ Ψ ] t ∷ A ! π)
           → tr (ρ̂S-abs Γ) refl refl (IA D) ≡ ρ̂ᶜ D
  inst-abs {Γ = Γ} (GT.⊢var i) =
    trans (tr-isubst′ (absCtx-lookup Δ Γ i) _)
          (trans (tr-subst (PT.lookup-⟪⟫ (absCtx Δ Γ) τ i) _) (tr-var-subst i (ρ̂S-abs Γ) _ (lookup-ρ̂ Γ i)))
  inst-abs (GT.⊢lam le d) = trans (tr-lam _ _ _ (IA d)) (cong (GT.⊢lam le) (inst-abs d))
  inst-abs (GT.⊢app f x) = trans (tr-app _ _ _ _ (IA f) (IA x)) (cong₂ GT.⊢app (inst-abs f) (inst-abs x))
  inst-abs (GT.⊢let e b) = trans (tr-let _ _ _ _ _ (IA e) (IA b)) (cong₂ GT.⊢let (inst-abs e) (inst-abs b))
  inst-abs GT.⊢unit = tr-unit
  inst-abs (GT.⊢pair a b) = trans (tr-pair _ _ _ _ (IA a) (IA b)) (cong₂ GT.⊢pair (inst-abs a) (inst-abs b))
  inst-abs (GT.⊢fst p) = trans (tr-fst _ _ (IA p)) (cong GT.⊢fst (inst-abs p))
  inst-abs (GT.⊢snd p) = trans (tr-snd _ _ (IA p)) (cong GT.⊢snd (inst-abs p))
  inst-abs (GT.⊢inl a) = trans (tr-inl _ _ (IA a)) (cong GT.⊢inl (inst-abs a))
  inst-abs (GT.⊢inr b) = trans (tr-inr _ _ (IA b)) (cong GT.⊢inr (inst-abs b))
  inst-abs (GT.⊢case s l x) =
    trans (tr-case _ _ _ _ _ _ _ _ (IA s) (IA l) (IA x)) (c3 (inst-abs s) (inst-abs l) (inst-abs x))
    where
      c3 : ∀ {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → GT.⊢case a b c ≡ GT.⊢case a′ b′ c′
      c3 refl refl refl = refl
  inst-abs (GT.⊢absurd e) = trans (tr-absurd refl (IA e)) (cong GT.⊢absurd (inst-abs e))
  inst-abs {Γ = Γ} (GT.⊢roll {F = F} wf d) =
    trans (tr-roll refl refl refl _)
          (cong (GT.⊢roll (ρ̂-wf wf))
            (trans (tr-subst (⟦⟧F-⟪⟫ (absF Δ F) (Ty.μ-type (absF Δ F)) τ) _)
              (trans (tr-isubst′ (absTy-⟦⟧ Δ F (μ-type F)) _)
                (close (ρ̂S-abs Γ) _ (ρ̂-⟦⟧ F (μ-type F)) (inst-abs d)))))
  inst-abs {Γ = Γ} (GT.⊢fold {π = π} {F = F} {A = A} wf a t) =
    trans (tr-fold refl refl refl refl refl refl _ (IA t))
          (cong₂ (GT.⊢fold (ρ̂-wf wf))
            (trans (tr-subst (⟦⟧F-⟪⟫ (absF Δ F) (absTy Δ A) τ) _)
              (trans (tr-isubst′ (absTy-⟦⟧ Δ F A) _)
                (closeF (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂S-abs Γ) _ (ρ̂-⟦⟧ F A) (inst-abs a))))
            (inst-abs t))
  inst-abs {Γ = Γ} (GT.⊢unfold {π = π} {F = F} {A = A} wf k x) =
    trans (tr-unfold refl refl refl refl refl refl _ (IA x))
          (cong₂ (GT.⊢unfold (ρ̂-wf wf))
            (trans (tr-subst (⟦⟧F-⟪⟫ (absF Δ F) (absTy Δ A) τ) _)
              (trans (tr-isubst′ (absTy-⟦⟧ Δ F A) _)
                (closeF (λ X → ρ̂ A T.⇒[ mk-kind Many π ] X) (ρ̂S-abs Γ) _ (ρ̂-⟦⟧ F A) (inst-abs k))))
            (inst-abs x))
  inst-abs {Γ = Γ} (GT.⊢out {π = π} {F = F} wf d) =
    trans (tr-isubst′ (sym (absTy-⟦⟧ Δ F (ν-type F π))) _)
      (trans (tr-subst (sym (⟦⟧F-⟪⟫ (absF Δ F) (Ty.ν-type (absF Δ F) π) τ)) _)
        (close (ρ̂S-abs Γ) _ (sym (ρ̂-⟦⟧ F (ν-type F π)))
          (trans (tr-out refl refl refl (IA d)) (cong (GT.⊢out (ρ̂-wf wf)) (inst-abs d)))))
  inst-abs (GT.⊢coerce p d) = trans (tr-coerce refl refl refl (IA d)) (cong (GT.⊢coerce (ρ̂-<: p)) (inst-abs d))
  inst-abs GT.⊢lit-int   = tr-lit-int
  inst-abs GT.⊢lit-float = tr-lit-float
  inst-abs GT.⊢lit-str   = tr-lit-str
  inst-abs {Γ = Γ} (GT.⊢prim p d) =
    trans (tr-isubst′ (sym (primCod-abs Δ p)) _)
      (trans (tr-subst (sym (⌈⌉-⟪⟫ (G.primCod p) τ)) _)
        (close (ρ̂S-abs Γ) _ (sym (ρ̂-cod p))
          (trans (tr-prim refl _)
            (cong (GT.⊢prim p)
              (trans (tr-subst (⌈⌉-⟪⟫ (G.primDom p) τ) _)
                (trans (tr-isubst′ (primDom-abs Δ p) _)
                  (close (ρ̂S-abs Γ) _ (ρ̂-dom p) (inst-abs d))))))))
  inst-abs {Γ = Γ} (GT.⊢sigop {A = A} c k h g) =
    trans (tr-isubst′ (sym (absTy-ground Δ g)) _)
      (trans (tr-subst (sym (⌈⌉-⟪⟫ A τ)) _) (close (ρ̂S-abs Γ) _ (sym (ρ̂-rf g)) tr-sigop))
  inst-abs (GT.⊢sub-eff g d) = trans (tr-sub-eff (IA d)) (cong (GT.⊢sub-eff g) (inst-abs d))
  inst-abs {Γ = Γ} (GT.⊢ref d τ′ k) =
    trans (tr-isubst′ (sym (abs-⟪⟫ Δ τ′ (sg d))) _)
      (trans (tr-subst (sym (⟨⟩-⟪⟫ (type (S !! d)) (λ i → absTy Δ (τ′ i)) τ)) _)
        (close (ρ̂S-abs Γ) _ (sym (ρ̂-ref d τ′)) (tr-ref refl)))
