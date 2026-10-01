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
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; ≡-subst-removable)
open import Once.Surface.Thinning using (_⊆_; done; skip; keep; thin-var; thin-usage; ⊆-refl; ⊆-wk)
open import Data.Fin using (Fin; zero; suc)
import Data.Bool
import Data.Nat
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
import Once.Spec.Core.Rename S as RN
import Once.Surface.Thinning as TH
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

  ----------------------------------------------------------------------
  -- ρ̂ᶜ COMMUTES WITH RENAMING (the combinators weaken their arms). Stated
  -- heterogeneously: the two sides differ only by index transports, which
  -- `_≅_` (with K) does not see.
  ----------------------------------------------------------------------

  -- The term substitution commutes with renaming.
  ρ̂ₜ-ren : ∀ {n k} (ρ : G.Ren n k) (t : G.Tm n) → ρ̂ₜ (G.ren ρ t) ≡ G.ren ρ (ρ̂ₜ t)
  ρ̂ₜ-ren ρ (G.var i)        = refl
  ρ̂ₜ-ren ρ (G.lam t)        = cong G.lam (ρ̂ₜ-ren (G.extR ρ) t)
  ρ̂ₜ-ren ρ (G.app t u)      = cong₂ G.app (ρ̂ₜ-ren ρ t) (ρ̂ₜ-ren ρ u)
  ρ̂ₜ-ren ρ (G.let′ t u)     = cong₂ G.let′ (ρ̂ₜ-ren ρ t) (ρ̂ₜ-ren (G.extR ρ) u)
  ρ̂ₜ-ren ρ G.unit           = refl
  ρ̂ₜ-ren ρ (G.pair t u)     = cong₂ G.pair (ρ̂ₜ-ren ρ t) (ρ̂ₜ-ren ρ u)
  ρ̂ₜ-ren ρ (G.fst t)        = cong G.fst (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.snd t)        = cong G.snd (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.inl t)        = cong G.inl (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.inr t)        = cong G.inr (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.case s l x)   = trans (cong₂ (λ a b → G.case a b _) (ρ̂ₜ-ren ρ s) (ρ̂ₜ-ren (G.extR ρ) l))
                                     (cong (G.case _ _) (ρ̂ₜ-ren (G.extR ρ) x))
  ρ̂ₜ-ren ρ (G.absurd t)     = cong G.absurd (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.roll t)       = cong G.roll (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.fold a t)     = cong₂ G.fold (ρ̂ₜ-ren ρ a) (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.unfold c t)   = cong₂ G.unfold (ρ̂ₜ-ren ρ c) (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.out t)        = cong G.out (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.coerce A B t) = cong (G.coerce _ _) (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.lit l)        = refl
  ρ̂ₜ-ren ρ (G.prim p t)     = cong (G.prim p) (ρ̂ₜ-ren ρ t)
  ρ̂ₜ-ren ρ (G.sigop c A)    = refl
  ρ̂ₜ-ren ρ (G.ref d τ′)     = refl

  -- The substitution on thinnings; it moves no position.
  ρ̂θ : ∀ {n k} {Γ : C.Ctx n} {D : C.Ctx k} → Γ ⊆ D → ρ̂S Γ ⊆ ρ̂S D
  ρ̂θ done     = done
  ρ̂θ (skip θ) = skip (ρ̂θ θ)
  ρ̂θ (keep θ) = keep (ρ̂θ θ)

  thin-var-ρ̂ : ∀ {n k} {Γ : C.Ctx n} {D : C.Ctx k} (θ : Γ ⊆ D) (i : Fin n) → thin-var (ρ̂θ θ) i ≡ thin-var θ i
  thin-var-ρ̂ (skip θ) i       = cong suc (thin-var-ρ̂ θ i)
  thin-var-ρ̂ (keep θ) zero    = refl
  thin-var-ρ̂ (keep θ) (suc i) = cong suc (thin-var-ρ̂ θ i)

  thin-usage-ρ̂ : ∀ {n k} {Γ : C.Ctx n} {D : C.Ctx k} (θ : Γ ⊆ D) (Ψ : C.Usage n) → thin-usage (ρ̂θ θ) Ψ ≡ thin-usage θ Ψ
  thin-usage-ρ̂ done     C.[]      = refl
  thin-usage-ρ̂ (skip θ) Ψ         = cong (T.Zero C.∷_) (thin-usage-ρ̂ θ Ψ)
  thin-usage-ρ̂ (keep θ) (q C.∷ Ψ) = cong (q C.∷_) (thin-usage-ρ̂ θ Ψ)

  ρ̂θ-refl : ∀ {n} (Γ : C.Ctx n) → ρ̂θ (⊆-refl {Γ = Γ}) ≡ ⊆-refl
  ρ̂θ-refl C.∅           = refl
  ρ̂θ-refl (Γ C., A ^ q) = cong keep (ρ̂θ-refl Γ)

  -- Transports are invisible to `_≅_`: a `subst` under ρ̂ᶜ or ren-⊢ is removable.
  module _ {n} {Γ : C.Ctx n} {π : T.Purity} where
    ρ̂ᶜ-sU : ∀ {Ψ₁ Ψ₂ t A} (e : Ψ₁ ≡ Ψ₂) {D : Γ ⊢[ Ψ₁ ] t ∷ A ! π} → ρ̂ᶜ (subst (λ U → Γ ⊢[ U ] t ∷ A ! π) e D) ≅ ρ̂ᶜ D
    ρ̂ᶜ-sU refl = H.refl
    ρ̂ᶜ-st : ∀ {Ψ t₁ t₂ A} (e : t₁ ≡ t₂) {D : Γ ⊢[ Ψ ] t₁ ∷ A ! π} → ρ̂ᶜ (subst (λ u → Γ ⊢[ Ψ ] u ∷ A ! π) e D) ≅ ρ̂ᶜ D
    ρ̂ᶜ-st refl = H.refl
    ρ̂ᶜ-sA : ∀ {Ψ t} {Y : Set} (f : Y → Type) {y₁ y₂} (e : y₁ ≡ y₂) {D : Γ ⊢[ Ψ ] t ∷ f y₁ ! π}
          → ρ̂ᶜ (subst (λ X → Γ ⊢[ Ψ ] t ∷ f X ! π) e D) ≅ ρ̂ᶜ D
    ρ̂ᶜ-sA f refl = H.refl
    ren-sA : ∀ {k} {D′ : C.Ctx k} (θ : Γ ⊆ D′) {Ψ t} {Y : Set} (f : Y → Type) {y₁ y₂} (e : y₁ ≡ y₂)
               {D : Γ ⊢[ Ψ ] t ∷ f y₁ ! π}
           → RN.ren-⊢ θ (subst (λ X → Γ ⊢[ Ψ ] t ∷ f X ! π) e D) ≅ RN.ren-⊢ θ D
    ren-sA θ f refl = H.refl
    rmU : ∀ {Ψ₁ Ψ₂ t A} (e : Ψ₁ ≡ Ψ₂) {D : Γ ⊢[ Ψ₁ ] t ∷ A ! π} → subst (λ U → Γ ⊢[ U ] t ∷ A ! π) e D ≅ D
    rmU refl = H.refl
    rmt : ∀ {Ψ t₁ t₂ A} (e : t₁ ≡ t₂) {D : Γ ⊢[ Ψ ] t₁ ∷ A ! π} → subst (λ u → Γ ⊢[ Ψ ] u ∷ A ! π) e D ≅ D
    rmt refl = H.refl
    rmA : ∀ {Ψ t} {Y : Set} (f : Y → Type) {y₁ y₂} (e : y₁ ≡ y₂) {D : Γ ⊢[ Ψ ] t ∷ f y₁ ! π}
        → subst (λ X → Γ ⊢[ Ψ ] t ∷ f X ! π) e D ≅ D
    rmA f refl = H.refl

  rm : ∀ {X : Set} (P : X → Set) {x y : X} (e : x ≡ y) (z : P x) → subst P e z ≅ z
  rm P e z = ≡-subst-removable P e z

  -- The index equations of a renamed sub-derivation.
  U≡ : ∀ {n k} {Γ : C.Ctx n} {D : C.Ctx k} (θ : Γ ⊆ D) (Ψ : C.Usage n) → thin-usage θ Ψ ≡ thin-usage (ρ̂θ θ) Ψ
  U≡ θ Ψ = sym (thin-usage-ρ̂ θ Ψ)

  T≡ : ∀ {n k} {Γ : C.Ctx n} {D : C.Ctx k} (θ : Γ ⊆ D) (t : G.Tm n)
     → ρ̂ₜ (G.ren (thin-var θ) t) ≡ G.ren (thin-var (ρ̂θ θ)) (ρ̂ₜ t)
  T≡ θ t = trans (ρ̂ₜ-ren (thin-var θ) t) (RN.ren-cong (λ i → sym (thin-var-ρ̂ θ i)) (ρ̂ₜ t))

  T≡e : ∀ {n k} {Γ : C.Ctx n} {D : C.Ctx k} (θ : Γ ⊆ D) (t : G.Tm (Data.Nat.suc n))
      → ρ̂ₜ (G.ren (G.extR (thin-var θ)) t) ≡ G.ren (G.extR (thin-var (ρ̂θ θ))) (ρ̂ₜ t)
  T≡e θ t = trans (ρ̂ₜ-ren (G.extR (thin-var θ)) t) (RN.ren-cong ex (ρ̂ₜ t))
    where
      ex : ∀ i → G.extR (thin-var θ) i ≡ G.extR (thin-var (ρ̂θ θ)) i
      ex zero    = refl
      ex (suc i) = cong suc (sym (thin-var-ρ̂ θ i))

  -- Constructor congruences (index equations explicit; K does the rest).
  module _ {n} {Γ : C.Ctx n} where
    ≅var : ∀ {i j : Fin n} → i ≡ j → GT.⊢var {Γ = Γ} i ≅ GT.⊢var {Γ = Γ} j
    ≅var refl = H.refl
    ≅1 : ∀ {m′} {Γ′ : C.Ctx m′} {B A′ : Type} {π π′ Ψ₁ Ψ₂ t₁ t₂}
           (W : C.Usage m′ → C.Usage n) (V : G.Tm m′ → G.Tm n)
           (f : ∀ {Ψ t} → Γ′ ⊢[ Ψ ] t ∷ A′ ! π′ → Γ ⊢[ W Ψ ] V t ∷ B ! π)
           {d₁ : Γ′ ⊢[ Ψ₁ ] t₁ ∷ A′ ! π′} {d₂ : Γ′ ⊢[ Ψ₂ ] t₂ ∷ A′ ! π′}
       → Ψ₁ ≡ Ψ₂ → t₁ ≡ t₂ → d₁ ≅ d₂ → f d₁ ≅ f d₂
    ≅1 W V f refl refl H.refl = H.refl
    ≅2 : ∀ {m₁ m₂} {Γ₁ : C.Ctx m₁} {Γ₂ : C.Ctx m₂} {B A₁ A₂ : Type} {π π₁ π₂ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ t₁ t₁′ t₂ t₂′}
           (W : C.Usage m₁ → C.Usage m₂ → C.Usage n) (V : G.Tm m₁ → G.Tm m₂ → G.Tm n)
           (f : ∀ {Ψ Ψ′ t t′} → Γ₁ ⊢[ Ψ ] t ∷ A₁ ! π₁ → Γ₂ ⊢[ Ψ′ ] t′ ∷ A₂ ! π₂ → Γ ⊢[ W Ψ Ψ′ ] V t t′ ∷ B ! π)
           {a₁ : Γ₁ ⊢[ Ψ₁ ] t₁ ∷ A₁ ! π₁} {a₂ : Γ₁ ⊢[ Ψ₂ ] t₂ ∷ A₁ ! π₁}
           {b₁ : Γ₂ ⊢[ Ψ₁′ ] t₁′ ∷ A₂ ! π₂} {b₂ : Γ₂ ⊢[ Ψ₂′ ] t₂′ ∷ A₂ ! π₂}
       → Ψ₁ ≡ Ψ₂ → t₁ ≡ t₂ → a₁ ≅ a₂ → Ψ₁′ ≡ Ψ₂′ → t₁′ ≡ t₂′ → b₁ ≅ b₂ → f a₁ b₁ ≅ f a₂ b₂
    ≅2 W V f refl refl H.refl refl refl H.refl = H.refl
    ≅lam : ∀ {A B q q′ π} {le : (q′ T.≤q q) ≡ Data.Bool.true} {Ψ₁ Ψ₂ t₁ t₂}
             {d₁ : (Γ C., A) ⊢[ q′ C.∷ Ψ₁ ] t₁ ∷ B ! π} {d₂ : (Γ C., A) ⊢[ q′ C.∷ Ψ₂ ] t₂ ∷ B ! π}
         → Ψ₁ ≡ Ψ₂ → t₁ ≡ t₂ → d₁ ≅ d₂ → GT.⊢lam le d₁ ≅ GT.⊢lam le d₂
    ≅lam refl refl H.refl = H.refl
    ≅let : ∀ {A B q π Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ e₁ e₂ b₁ b₂}
             {de₁ : Γ ⊢[ Ψ₁ ] e₁ ∷ A ! π} {de₂ : Γ ⊢[ Ψ₁′ ] e₂ ∷ A ! π}
             {db₁ : (Γ C., A) ⊢[ q C.∷ Ψ₂ ] b₁ ∷ B ! π} {db₂ : (Γ C., A) ⊢[ q C.∷ Ψ₂′ ] b₂ ∷ B ! π}
         → Ψ₁ ≡ Ψ₁′ → e₁ ≡ e₂ → de₁ ≅ de₂ → Ψ₂ ≡ Ψ₂′ → b₁ ≡ b₂ → db₁ ≅ db₂ → GT.⊢let de₁ db₁ ≅ GT.⊢let de₂ db₂
    ≅let refl refl H.refl refl refl H.refl = H.refl
    ≅case : ∀ {A B C′ qℓ qr π Ψs Ψs′ Ψₗ Ψₗ′ Ψᵣ Ψᵣ′ s₁ s₂ l₁ l₂ r₁ r₂}
              {ds₁ : Γ ⊢[ Ψs ] s₁ ∷ A T.+ B ! π} {ds₂ : Γ ⊢[ Ψs′ ] s₂ ∷ A T.+ B ! π}
              {dl₁ : (Γ C., A) ⊢[ qℓ C.∷ Ψₗ ] l₁ ∷ C′ ! π} {dl₂ : (Γ C., A) ⊢[ qℓ C.∷ Ψₗ′ ] l₂ ∷ C′ ! π}
              {dr₁ : (Γ C., B) ⊢[ qr C.∷ Ψᵣ ] r₁ ∷ C′ ! π} {dr₂ : (Γ C., B) ⊢[ qr C.∷ Ψᵣ′ ] r₂ ∷ C′ ! π}
          → Ψs ≡ Ψs′ → s₁ ≡ s₂ → ds₁ ≅ ds₂ → Ψₗ ≡ Ψₗ′ → l₁ ≡ l₂ → dl₁ ≅ dl₂ → Ψᵣ ≡ Ψᵣ′ → r₁ ≡ r₂ → dr₁ ≅ dr₂
          → GT.⊢case ds₁ dl₁ dr₁ ≅ GT.⊢case ds₂ dl₂ dr₂
    ≅case refl refl H.refl refl refl H.refl refl refl H.refl = H.refl

  -- THE LEMMA.
  ρ̂ᶜ-ren : ∀ {n k} {Γ : C.Ctx n} {D′ : C.Ctx k} (θ : Γ ⊆ D′) {Ψ t A π} (D : Γ ⊢[ Ψ ] t ∷ A ! π)
         → ρ̂ᶜ (RN.ren-⊢ θ D) ≅ RN.ren-⊢ (ρ̂θ θ) (ρ̂ᶜ D)
  ρ̂ᶜ-ren {Γ = Γ} {D′ = D′} θ (GT.⊢var i) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-singleUse θ i T.One)))
      (H.trans (ρ̂ᶜ-sA (λ X → X) (sym (TH.thin-var-lookup θ i)))
        (H.trans (rmA (λ X → X) (lookup-ρ̂ D′ (thin-var θ i)))
          (H.trans (≅var (sym (thin-var-ρ̂ θ i)))
            (H.sym (H.trans (ren-sA (ρ̂θ θ) (λ X → X) (lookup-ρ̂ Γ i))
                     (H.trans (rmU (sym (TH.thin-usage-singleUse (ρ̂θ θ) i T.One)))
                              (rmA (λ X → X) (sym (TH.thin-var-lookup (ρ̂θ θ) i)))))))))
  ρ̂ᶜ-ren θ (GT.⊢lam {Ψ = Ψ} {t = t} le d) =
    ≅lam (U≡ θ Ψ) (T≡e θ t)
      (H.trans (ρ̂ᶜ-st (RN.ren-cong (RN.keep-extR θ) t))
        (H.trans (ρ̂ᶜ-ren (keep θ) d) (H.sym (rmt (RN.ren-cong (RN.keep-extR (ρ̂θ θ)) (ρ̂ₜ t))))))
  ρ̂ᶜ-ren θ (GT.⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} {f = f} {x = x} df dx) =
    H.trans (ρ̂ᶜ-sU (sym (trans (TH.thin-usage-+ᵘ θ Ψ₁ (q C.*ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ C.+ᵘ_) (TH.thin-usage-*ᵘ θ q Ψ₂)))))
      (H.trans (≅2 _ _ GT.⊢app (U≡ θ Ψ₁) (T≡ θ f) (ρ̂ᶜ-ren θ df) (U≡ θ Ψ₂) (T≡ θ x) (ρ̂ᶜ-ren θ dx))
               (H.sym (rmU (sym (trans (TH.thin-usage-+ᵘ (ρ̂θ θ) Ψ₁ (q C.*ᵘ Ψ₂))
                                       (cong (thin-usage (ρ̂θ θ) Ψ₁ C.+ᵘ_) (TH.thin-usage-*ᵘ (ρ̂θ θ) q Ψ₂)))))))
  ρ̂ᶜ-ren θ (GT.⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} {e = e} {b = b} de db) =
    H.trans (ρ̂ᶜ-sU (sym (trans (TH.thin-usage-+ᵘ θ Ψ₂ (q C.*ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ C.+ᵘ_) (TH.thin-usage-*ᵘ θ q Ψ₁)))))
      (H.trans (≅let (U≡ θ Ψ₁) (T≡ θ e) (ρ̂ᶜ-ren θ de) (U≡ θ Ψ₂) (T≡e θ b)
                     (H.trans (ρ̂ᶜ-st (RN.ren-cong (RN.keep-extR θ) b))
                       (H.trans (ρ̂ᶜ-ren (keep θ) db) (H.sym (rmt (RN.ren-cong (RN.keep-extR (ρ̂θ θ)) (ρ̂ₜ b)))))))
               (H.sym (rmU (sym (trans (TH.thin-usage-+ᵘ (ρ̂θ θ) Ψ₂ (q C.*ᵘ Ψ₁))
                                       (cong (thin-usage (ρ̂θ θ) Ψ₂ C.+ᵘ_) (TH.thin-usage-*ᵘ (ρ̂θ θ) q Ψ₁)))))))
  ρ̂ᶜ-ren θ GT.⊢unit =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ))) (H.sym (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))
  ρ̂ᶜ-ren θ (GT.⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {b = b} da db) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-+ᵘ θ Ψ₁ Ψ₂)))
      (H.trans (≅2 _ _ GT.⊢pair (U≡ θ Ψ₁) (T≡ θ a) (ρ̂ᶜ-ren θ da) (U≡ θ Ψ₂) (T≡ θ b) (ρ̂ᶜ-ren θ db))
               (H.sym (rmU (sym (TH.thin-usage-+ᵘ (ρ̂θ θ) Ψ₁ Ψ₂)))))
  ρ̂ᶜ-ren θ (GT.⊢fst {Ψ = Ψ} {p = p} d) = ≅1 _ _ GT.⊢fst (U≡ θ Ψ) (T≡ θ p) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢snd {Ψ = Ψ} {p = p} d) = ≅1 _ _ GT.⊢snd (U≡ θ Ψ) (T≡ θ p) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢inl {Ψ = Ψ} {a = a} d) = ≅1 _ _ GT.⊢inl (U≡ θ Ψ) (T≡ θ a) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢inr {Ψ = Ψ} {b = b} d) = ≅1 _ _ GT.⊢inr (U≡ θ Ψ) (T≡ θ b) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢case {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {s = sc} {l = l} {r = x} ds dl dr) =
    H.trans (ρ̂ᶜ-sU (sym (trans (TH.thin-usage-+ᵘ θ Ψs (Ψₗ C.⊔ᵘ Ψᵣ)) (cong (thin-usage θ Ψs C.+ᵘ_) (TH.thin-usage-⊔ᵘ θ Ψₗ Ψᵣ)))))
      (H.trans (≅case (U≡ θ Ψs) (T≡ θ sc) (ρ̂ᶜ-ren θ ds)
                      (U≡ θ Ψₗ) (T≡e θ l)
                      (H.trans (ρ̂ᶜ-st (RN.ren-cong (RN.keep-extR θ) l))
                        (H.trans (ρ̂ᶜ-ren (keep θ) dl) (H.sym (rmt (RN.ren-cong (RN.keep-extR (ρ̂θ θ)) (ρ̂ₜ l))))))
                      (U≡ θ Ψᵣ) (T≡e θ x)
                      (H.trans (ρ̂ᶜ-st (RN.ren-cong (RN.keep-extR θ) x))
                        (H.trans (ρ̂ᶜ-ren (keep θ) dr) (H.sym (rmt (RN.ren-cong (RN.keep-extR (ρ̂θ θ)) (ρ̂ₜ x)))))))
               (H.sym (rmU (sym (trans (TH.thin-usage-+ᵘ (ρ̂θ θ) Ψs (Ψₗ C.⊔ᵘ Ψᵣ))
                                       (cong (thin-usage (ρ̂θ θ) Ψs C.+ᵘ_) (TH.thin-usage-⊔ᵘ (ρ̂θ θ) Ψₗ Ψᵣ)))))))
  ρ̂ᶜ-ren θ (GT.⊢absurd {Ψ = Ψ} {e = e} d) = ≅1 _ _ GT.⊢absurd (U≡ θ Ψ) (T≡ θ e) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢roll {Ψ = Ψ} {F = F} {t = t} wf d) =
    ≅1 _ _ (GT.⊢roll (ρ̂-wf wf)) (U≡ θ Ψ) (T≡ θ t)
       (H.trans (rmA (λ X → X) (ρ̂-⟦⟧ F (μ-type F)))
         (H.trans (ρ̂ᶜ-ren θ d) (H.sym (ren-sA (ρ̂θ θ) (λ X → X) (ρ̂-⟦⟧ F (μ-type F))))))
  ρ̂ᶜ-ren θ (GT.⊢fold {Ψa = Ψa} {Ψt = Ψt} {π = π} {F = F} {A = A} {alg = alg} {t = t} wf da dt) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-+ᵘ θ Ψa Ψt)))
      (H.trans (≅2 _ _ (GT.⊢fold (ρ̂-wf wf)) (U≡ θ Ψa) (T≡ θ alg)
                   (H.trans (rmA (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A))
                     (H.trans (ρ̂ᶜ-ren θ da) (H.sym (ren-sA (ρ̂θ θ) (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A)))))
                   (U≡ θ Ψt) (T≡ θ t) (ρ̂ᶜ-ren θ dt))
               (H.sym (rmU (sym (TH.thin-usage-+ᵘ (ρ̂θ θ) Ψa Ψt)))))
  ρ̂ᶜ-ren θ (GT.⊢unfold {Ψc = Ψc} {Ψs = Ψs} {π = π} {F = F} {A = A} {c = c} {s = sd} wf dc ds) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-+ᵘ θ Ψc Ψs)))
      (H.trans (≅2 _ _ (GT.⊢unfold (ρ̂-wf wf)) (U≡ θ Ψc) (T≡ θ c)
                   (H.trans (rmA (λ X → ρ̂ A T.⇒[ mk-kind Many π ] X) (ρ̂-⟦⟧ F A))
                     (H.trans (ρ̂ᶜ-ren θ dc) (H.sym (ren-sA (ρ̂θ θ) (λ X → ρ̂ A T.⇒[ mk-kind Many π ] X) (ρ̂-⟦⟧ F A)))))
                   (U≡ θ Ψs) (T≡ θ sd) (ρ̂ᶜ-ren θ ds))
               (H.sym (rmU (sym (TH.thin-usage-+ᵘ (ρ̂θ θ) Ψc Ψs)))))
  ρ̂ᶜ-ren θ (GT.⊢out {Ψ = Ψ} {π = π} {F = F} {t = t} wf d) =
    H.trans (rmA (λ X → X) (sym (ρ̂-⟦⟧ F (ν-type F π))))
      (H.trans (≅1 _ _ (GT.⊢out (ρ̂-wf wf)) (U≡ θ Ψ) (T≡ θ t) (ρ̂ᶜ-ren θ d))
               (H.sym (ren-sA (ρ̂θ θ) (λ X → X) (sym (ρ̂-⟦⟧ F (ν-type F π))))))
  ρ̂ᶜ-ren θ (GT.⊢coerce {Ψ = Ψ} {t = t} p d) = ≅1 _ _ (GT.⊢coerce (ρ̂-<: p)) (U≡ θ Ψ) (T≡ θ t) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ GT.⊢lit-int   = H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ))) (H.sym (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))
  ρ̂ᶜ-ren θ GT.⊢lit-float = H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ))) (H.sym (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))
  ρ̂ᶜ-ren θ GT.⊢lit-str   = H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ))) (H.sym (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))
  ρ̂ᶜ-ren θ (GT.⊢prim {Ψ = Ψ} {t = t} p d) =
    H.trans (rmA (λ X → X) (sym (ρ̂-cod p)))
      (H.trans (≅1 _ _ (GT.⊢prim p) (U≡ θ Ψ) (T≡ θ t)
                   (H.trans (rmA (λ X → X) (ρ̂-dom p)) (H.trans (ρ̂ᶜ-ren θ d) (H.sym (ren-sA (ρ̂θ θ) (λ X → X) (ρ̂-dom p))))))
               (H.sym (ren-sA (ρ̂θ θ) (λ X → X) (sym (ρ̂-cod p)))))
  ρ̂ᶜ-ren θ (GT.⊢sigop c k h g) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ)))
      (H.trans (rmA (λ X → X) (sym (ρ̂-rf g)))
        (H.sym (H.trans (ren-sA (ρ̂θ θ) (λ X → X) (sym (ρ̂-rf g))) (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))))
  ρ̂ᶜ-ren θ (GT.⊢sub-eff {Ψ = Ψ} {t = t} g d) = ≅1 _ _ (GT.⊢sub-eff g) (U≡ θ Ψ) (T≡ θ t) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢ref d τ′ k) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ)))
      (H.trans (rmA (λ X → X) (sym (ρ̂-ref d τ′)))
        (H.sym (H.trans (ren-sA (ρ̂θ θ) (λ X → X) (sym (ρ̂-ref d τ′))) (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))))
