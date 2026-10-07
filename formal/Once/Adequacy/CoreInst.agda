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

open import Once.Spec.Contract using (ISig)
module Once.Adequacy.CoreInst {Fs : ISig} {s : ℕ} (S : Sig Fs s) {m : ℕ} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where

open import Data.Product using (_,_)
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
import Once.Spec.Core.DerivedTyping S as DT
import Once.Type.Sub
open import Once.Functor.Translate using (WellFormedF)
open PT using (_⟪_⟫ᶜ; _⟪_⟫ₜ)
open import Once.Spec.Core.Abstract S using (SigGround; absCtx; absTm; abs-⊢; primDom-abs; primCod-abs; absCtx-lookup)
import Once.TypeCheck.RigidSubst Δ τ r as RS
open RS using (ρ̂; ρ̂S; ρ̂-⟦⟧; ρ̂-wf; ρ̂-<:; ρ̂-rf; ρ̂-base; lookup-ρ̂)
open import Once.Adequacy.CoreAbsSem S using (tr; tr-subst; tr-lam; tr-app; tr-let; tr-unit; tr-pair; tr-fst; tr-snd;
  tr-inl; tr-inr; tr-case; tr-absurd; tr-roll; tr-fold; tr-unfold; tr-out; tr-coerce; tr-lit-int; tr-lit-float; tr-prim; tr-sigop; tr-sub-eff; tr-sub-use; tr-ref)
open import Once.Denotation.EnvAlgebraV using (⊑ᵘ-unique)

ρ̂ₜ : ∀ {n} → G.Tm n → G.Tm n
ρ̂ₜ t = absTm Δ t ⟪ τ ⟫ₜ

-- The primitives' types are ground.
ρ̂-dom : ∀ p → ρ̂ (G.primDom p) ≡ G.primDom p
ρ̂-dom p = trans (cong (_⟪ τ ⟫) (primDom-abs Δ p)) (⌈⌉-⟪⟫ (G.primDom p) τ)

ρ̂-cod : ∀ p → ρ̂ (G.primCod p) ≡ G.primCod p
ρ̂-cod p = trans (cong (_⟪ τ ⟫) (primCod-abs Δ p)) (⌈⌉-⟪⟫ (G.primCod p) τ)

module WithSG (sg : SigGround) where

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
  ρ̂ᶜ {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢prim {t = t} p d) =
    subst (λ X → ρ̂S Γ ⊢[ Ψ ] G.prim p (ρ̂ₜ t) ∷ X ! π) (sym (ρ̂-cod p))
      (GT.⊢prim p (subst (λ X → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ t ∷ X ! π) (ρ̂-dom p) (ρ̂ᶜ d)))
  ρ̂ᶜ {Γ = Γ} (GT.⊢sigop {A = A} c k h g m) =
    subst (λ X → ρ̂S Γ ⊢[ C.zeroUsage ] G.sigop c A ∷ X ! pure) (sym (ρ̂-rf g)) (GT.⊢sigop c k h g m)
  ρ̂ᶜ (GT.⊢sub-eff g d) = GT.⊢sub-eff g (ρ̂ᶜ d)
  ρ̂ᶜ (GT.⊢sub-use p d) = GT.⊢sub-use p (ρ̂ᶜ d)
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
  inst-abs {Γ = Γ} (GT.⊢prim p d) =
    trans (tr-isubst′ (sym (primCod-abs Δ p)) _)
      (trans (tr-subst (sym (⌈⌉-⟪⟫ (G.primCod p) τ)) _)
        (close (ρ̂S-abs Γ) _ (sym (ρ̂-cod p))
          (trans (tr-prim refl _)
            (cong (GT.⊢prim p)
              (trans (tr-subst (⌈⌉-⟪⟫ (G.primDom p) τ) _)
                (trans (tr-isubst′ (primDom-abs Δ p) _)
                  (close (ρ̂S-abs Γ) _ (ρ̂-dom p) (inst-abs d))))))))
  inst-abs {Γ = Γ} (GT.⊢sigop {A = A} c k h g m) =
    trans (tr-isubst′ (sym (absTy-ground Δ g)) _)
      (trans (tr-subst (sym (⌈⌉-⟪⟫ A τ)) _) (close (ρ̂S-abs Γ) _ (sym (ρ̂-rf g)) tr-sigop))
  inst-abs (GT.⊢sub-eff g d) = trans (tr-sub-eff (IA d)) (cong (GT.⊢sub-eff g) (inst-abs d))
  inst-abs (GT.⊢sub-use p d) = trans (tr-sub-use (IA d)) (cong (GT.⊢sub-use p) (inst-abs d))
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
    ρ̂ᶜ-sUf : ∀ {k} (f : C.Usage k → C.Usage n) {Ψ₁ Ψ₂ t A} (e : Ψ₁ ≡ Ψ₂) {D : Γ ⊢[ f Ψ₁ ] t ∷ A ! π}
           → ρ̂ᶜ (subst (λ U → Γ ⊢[ f U ] t ∷ A ! π) e D) ≅ ρ̂ᶜ D
    ρ̂ᶜ-sUf f refl = H.refl
    rmUf : ∀ {k} (f : C.Usage k → C.Usage n) {Ψ₁ Ψ₂ t A} (e : Ψ₁ ≡ Ψ₂) {D : Γ ⊢[ f Ψ₁ ] t ∷ A ! π}
         → subst (λ U → Γ ⊢[ f U ] t ∷ A ! π) e D ≅ D
    rmUf f refl = H.refl
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
    ≅case : ∀ {A B C′ qℓ qr π Ψs Ψs′ Ψ Ψ′ s₁ s₂ l₁ l₂ r₁ r₂}
              {ds₁ : Γ ⊢[ Ψs ] s₁ ∷ A T.+ B ! π} {ds₂ : Γ ⊢[ Ψs′ ] s₂ ∷ A T.+ B ! π}
              {dl₁ : (Γ C., A) ⊢[ qℓ C.∷ Ψ ] l₁ ∷ C′ ! π} {dl₂ : (Γ C., A) ⊢[ qℓ C.∷ Ψ′ ] l₂ ∷ C′ ! π}
              {dr₁ : (Γ C., B) ⊢[ qr C.∷ Ψ ] r₁ ∷ C′ ! π} {dr₂ : (Γ C., B) ⊢[ qr C.∷ Ψ′ ] r₂ ∷ C′ ! π}
          → Ψs ≡ Ψs′ → s₁ ≡ s₂ → ds₁ ≅ ds₂ → Ψ ≡ Ψ′ → l₁ ≡ l₂ → dl₁ ≅ dl₂ → r₁ ≡ r₂ → dr₁ ≅ dr₂
          → GT.⊢case ds₁ dl₁ dr₁ ≅ GT.⊢case ds₂ dl₂ dr₂
    ≅case refl refl H.refl refl refl H.refl refl H.refl = H.refl
    -- …and the elaboration's `case`, whose arms are sub-used to the join (D276).
    ≅case⊔ : ∀ {A B C′ qℓ qr π Ψs Ψs′ Ψₗ Ψₗ′ Ψᵣ Ψᵣ′ s₁ s₂ l₁ l₂ r₁ r₂}
              {ds₁ : Γ ⊢[ Ψs ] s₁ ∷ A T.+ B ! π} {ds₂ : Γ ⊢[ Ψs′ ] s₂ ∷ A T.+ B ! π}
              {dl₁ : (Γ C., A) ⊢[ qℓ C.∷ Ψₗ ] l₁ ∷ C′ ! π} {dl₂ : (Γ C., A) ⊢[ qℓ C.∷ Ψₗ′ ] l₂ ∷ C′ ! π}
              {dr₁ : (Γ C., B) ⊢[ qr C.∷ Ψᵣ ] r₁ ∷ C′ ! π} {dr₂ : (Γ C., B) ⊢[ qr C.∷ Ψᵣ′ ] r₂ ∷ C′ ! π}
          → Ψs ≡ Ψs′ → s₁ ≡ s₂ → ds₁ ≅ ds₂ → Ψₗ ≡ Ψₗ′ → l₁ ≡ l₂ → dl₁ ≅ dl₂ → Ψᵣ ≡ Ψᵣ′ → r₁ ≡ r₂ → dr₁ ≅ dr₂
          → GT.⊢case⊔ ds₁ dl₁ dr₁ ≅ GT.⊢case⊔ ds₂ dl₂ dr₂
    ≅case⊔ refl refl H.refl refl refl H.refl refl refl H.refl = H.refl
    -- D276: the order is proof-irrelevant, so only the indices matter.
    ≅sub-use : ∀ {A π Ψ₁ Ψ₂ Ψ₁′ Ψ₂′ t₁ t₂} {p₁ : Ψ₁ C.⊑ᵘ Ψ₁′} {p₂ : Ψ₂ C.⊑ᵘ Ψ₂′}
                 {d₁ : Γ ⊢[ Ψ₁ ] t₁ ∷ A ! π} {d₂ : Γ ⊢[ Ψ₂ ] t₂ ∷ A ! π}
             → Ψ₁ ≡ Ψ₂ → Ψ₁′ ≡ Ψ₂′ → t₁ ≡ t₂ → d₁ ≅ d₂ → GT.⊢sub-use p₁ d₁ ≅ GT.⊢sub-use p₂ d₂
    ≅sub-use {p₁ = p₁} {p₂} refl refl refl H.refl = irr (⊑ᵘ-unique p₁ p₂)
      where irr : ∀ {d} → p₁ ≡ p₂ → GT.⊢sub-use p₁ d ≅ GT.⊢sub-use p₂ d
            irr refl = H.refl

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
  ρ̂ᶜ-ren θ (GT.⊢case {Ψs = Ψs} {Ψ = Ψ} {s = sc} {l = l} {r = x} ds dl dr) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-+ᵘ θ Ψs Ψ)))
      (H.trans (≅case (U≡ θ Ψs) (T≡ θ sc) (ρ̂ᶜ-ren θ ds)
                      (U≡ θ Ψ) (T≡e θ l)
                      (H.trans (ρ̂ᶜ-st (RN.ren-cong (RN.keep-extR θ) l))
                        (H.trans (ρ̂ᶜ-ren (keep θ) dl) (H.sym (rmt (RN.ren-cong (RN.keep-extR (ρ̂θ θ)) (ρ̂ₜ l))))))
                      (T≡e θ x)
                      (H.trans (ρ̂ᶜ-st (RN.ren-cong (RN.keep-extR θ) x))
                        (H.trans (ρ̂ᶜ-ren (keep θ) dr) (H.sym (rmt (RN.ren-cong (RN.keep-extR (ρ̂θ θ)) (ρ̂ₜ x)))))))
               (H.sym (rmU (sym (TH.thin-usage-+ᵘ (ρ̂θ θ) Ψs Ψ)))))
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
  ρ̂ᶜ-ren θ (GT.⊢prim {Ψ = Ψ} {t = t} p d) =
    H.trans (rmA (λ X → X) (sym (ρ̂-cod p)))
      (H.trans (≅1 _ _ (GT.⊢prim p) (U≡ θ Ψ) (T≡ θ t)
                   (H.trans (rmA (λ X → X) (ρ̂-dom p)) (H.trans (ρ̂ᶜ-ren θ d) (H.sym (ren-sA (ρ̂θ θ) (λ X → X) (ρ̂-dom p))))))
               (H.sym (ren-sA (ρ̂θ θ) (λ X → X) (sym (ρ̂-cod p)))))
  ρ̂ᶜ-ren θ (GT.⊢sigop c k h g m) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ)))
      (H.trans (rmA (λ X → X) (sym (ρ̂-rf g)))
        (H.sym (H.trans (ren-sA (ρ̂θ θ) (λ X → X) (sym (ρ̂-rf g))) (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))))
  ρ̂ᶜ-ren θ (GT.⊢sub-eff {Ψ = Ψ} {t = t} g d) = ≅1 _ _ (GT.⊢sub-eff g) (U≡ θ Ψ) (T≡ θ t) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢sub-use {Ψ = Ψ} {Ψ′ = Ψ′} {t = t} p d) = ≅sub-use (U≡ θ Ψ) (U≡ θ Ψ′) (T≡ θ t) (ρ̂ᶜ-ren θ d)
  ρ̂ᶜ-ren θ (GT.⊢ref d τ′ k) =
    H.trans (ρ̂ᶜ-sU (sym (TH.thin-usage-zeroUsage θ)))
      (H.trans (rmA (λ X → X) (sym (ρ̂-ref d τ′)))
        (H.sym (H.trans (ren-sA (ρ̂θ θ) (λ X → X) (sym (ρ̂-ref d τ′))) (rmU (sym (TH.thin-usage-zeroUsage (ρ̂θ θ)))))))

  ----------------------------------------------------------------------
  -- Weakening and closing, and the combinators that use them.
  ----------------------------------------------------------------------

  ren-θ≡ : ∀ {n k} {Γ : C.Ctx n} {D′ : C.Ctx k} {θ₁ θ₂ : Γ ⊆ D′} → θ₁ ≡ θ₂ → ∀ {Ψ t A π} (X : Γ ⊢[ Ψ ] t ∷ A ! π)
         → RN.ren-⊢ θ₁ X ≅ RN.ren-⊢ θ₂ X
  ren-θ≡ refl X = H.refl

  wk≅ : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} (B : Type) (d : Γ ⊢[ Ψ ] t ∷ A ! π)
      → ρ̂ᶜ (DT.wk-⊢′ B d) ≅ DT.wk-⊢′ (ρ̂ B) (ρ̂ᶜ d)
  wk≅ {Γ = Γ} {Ψ = Ψ} {t = t} B d =
    H.trans (ρ̂ᶜ-sUf (T.Zero C.∷_) (TH.thin-usage-refl {Γ = Γ} Ψ))
      (H.trans (ρ̂ᶜ-st (RN.ren-cong (λ i → cong suc (RN.thin-var-refl {Γ = Γ} i)) t))
        (H.trans (ρ̂ᶜ-ren (⊆-wk {Γ = Γ} {A = B} {q = Many}) d)
          (H.trans (ren-θ≡ (cong skip (ρ̂θ-refl Γ)) (ρ̂ᶜ d))
            (H.sym (H.trans (rmUf (T.Zero C.∷_) (TH.thin-usage-refl {Γ = ρ̂S Γ} Ψ))
                            (rmt (RN.ren-cong (λ i → cong suc (RN.thin-var-refl {Γ = ρ̂S Γ} i)) (ρ̂ₜ t))))))))

  ρ̂θ-∅ : ∀ {n} (Γ : C.Ctx n) → ρ̂θ (RN.∅⊆ {Γ = Γ}) ≡ RN.∅⊆ {Γ = ρ̂S Γ}
  ρ̂θ-∅ C.∅           = refl
  ρ̂θ-∅ (Γ C., A ^ q) = cong skip (ρ̂θ-∅ Γ)

  close≅ : ∀ {n} {Γ : C.Ctx n} {t A π} (d : C.∅ ⊢[ C.zeroUsage ] t ∷ A ! π)
         → ρ̂ᶜ (RN.⊢close {Γ = Γ} d) ≅ RN.⊢close {Γ = ρ̂S Γ} (ρ̂ᶜ d)
  close≅ {Γ = Γ} {t = t} d =
    H.trans (ρ̂ᶜ-st (RN.ren-cong {ρ = thin-var (RN.∅⊆ {Γ = Γ})} {ρ′ = λ ()} (λ ()) t))
      (H.trans (ρ̂ᶜ-sU (TH.thin-usage-zeroUsage (RN.∅⊆ {Γ = Γ})))
        (H.trans (ρ̂ᶜ-ren (RN.∅⊆ {Γ = Γ}) d)
          (H.trans (ren-θ≡ (ρ̂θ-∅ Γ) (ρ̂ᶜ d))
            (H.sym (H.trans (rmt (RN.ren-cong {ρ = thin-var (RN.∅⊆ {Γ = ρ̂S Γ})} {ρ′ = λ ()} (λ ()) (ρ̂ₜ t)))
                            (rmU (TH.thin-usage-zeroUsage (RN.∅⊆ {Γ = ρ̂S Γ}))))))))

  -- The combinators with arms.
  module _ {n} {Γ : C.Ctx n} where
    open import Once.Surface.Properties using (+ᵘ-identityˡ; *ᵘ-identityˡ; +ᵘ-identityʳ)

    c-compose : ∀ {Ψ₁ Ψ₂ A B C′ π f g}
                  (a : Γ ⊢[ Ψ₁ ] f ∷ B T.⇒[ mk-kind Many π ] C′ ! pure) (b : Γ ⊢[ Ψ₂ ] g ∷ A T.⇒[ mk-kind Many π ] B ! pure)
              → ρ̂ᶜ (DT.⊢composeᶜ a b) ≅ DT.⊢composeᶜ (ρ̂ᶜ a) (ρ̂ᶜ b)
    c-compose {Ψ₁} {Ψ₂} {B = B} {C′} {π} {g = g} a b =
      H.trans (ρ̂ᶜ-sU (DT.arms Many Ψ₁ Ψ₂ (trans (cong (C.zeroUsage C.+ᵘ_) (cong (Many C.*ᵘ_) (DT.z+qz Many))) (DT.z+qz Many))))
        (H.trans (≅let refl refl H.refl refl (cong (λ u → G.let′ u _) (ρ̂ₜ-ren suc g))
                       (≅let refl (ρ̂ₜ-ren suc g) (wk≅ (B T.⇒[ mk-kind Many π ] C′) b) refl refl H.refl))
          (H.sym (rmU (DT.arms Many Ψ₁ Ψ₂ (trans (cong (C.zeroUsage C.+ᵘ_) (cong (Many C.*ᵘ_) (DT.z+qz Many))) (DT.z+qz Many))))))

    c-pair : ∀ {Ψ₁ Ψ₂ A B C′ π f g}
               (a : Γ ⊢[ Ψ₁ ] f ∷ A T.⇒[ mk-kind Many π ] B ! pure) (b : Γ ⊢[ Ψ₂ ] g ∷ A T.⇒[ mk-kind Many π ] C′ ! pure)
           → ρ̂ᶜ (DT.⊢pairᶜ a b) ≅ DT.⊢pairᶜ (ρ̂ᶜ a) (ρ̂ᶜ b)
    c-pair {Ψ₁} {Ψ₂} {A} {B} {π = π} {g = g} a b =
      H.trans (ρ̂ᶜ-sU E)
        (H.trans (≅let refl refl H.refl refl (cong (λ u → G.let′ u _) (ρ̂ₜ-ren suc g))
                       (≅let refl (ρ̂ₜ-ren suc g) (wk≅ (A T.⇒[ mk-kind Many π ] B) b) refl refl H.refl))
          (H.sym (rmU E)))
      where E = trans (DT.arms T.One Ψ₁ Ψ₂ (trans (cong₂ C._+ᵘ_ (DT.z+qz Many) (DT.z+qz Many)) (+ᵘ-identityˡ C.zeroUsage)))
                      (cong (Ψ₁ C.+ᵘ_) (*ᵘ-identityˡ Ψ₂))

    c-case : ∀ {Ψ₁ Ψ₂ A B C′ π f g}
               (a : Γ ⊢[ Ψ₁ ] f ∷ A T.⇒[ mk-kind Many π ] C′ ! pure) (b : Γ ⊢[ Ψ₂ ] g ∷ B T.⇒[ mk-kind Many π ] C′ ! pure)
           → ρ̂ᶜ (DT.⊢caseᶜ a b) ≅ DT.⊢caseᶜ (ρ̂ᶜ a) (ρ̂ᶜ b)
    c-case {Ψ₁} {Ψ₂} {A} {B} {C′} {π} {g = g} a b =
      H.trans (ρ̂ᶜ-sU E)
        (H.trans (≅let refl refl H.refl refl (cong (λ u → G.let′ u _) (ρ̂ₜ-ren suc g))
                       (≅let refl (ρ̂ₜ-ren suc g) (wk≅ (A T.⇒[ mk-kind Many π ] C′) b) refl refl H.refl))
          (H.sym (rmU E)))
      where E = trans (DT.arms T.One Ψ₁ Ψ₂ (trans (cong (C.zeroUsage C.+ᵘ_) (trans (cong₂ C._⊔ᵘ_ (DT.z+qz Many) (DT.z+qz Many)) DT.z⊔z))
                                               (+ᵘ-identityˡ C.zeroUsage)))
                      (cong (Ψ₁ C.+ᵘ_) (*ᵘ-identityˡ Ψ₂))

    c-curry : ∀ {Ψ A B C′ π₀ π f} (a : Γ ⊢[ Ψ ] f ∷ (A T.* B) T.⇒[ mk-kind Many π ] C′ ! pure)
            → ρ̂ᶜ (DT.⊢curryᶜ {π₀ = π₀} a) ≅ DT.⊢curryᶜ {π₀ = π₀} (ρ̂ᶜ a)
    c-curry {Ψ} a = H.trans (ρ̂ᶜ-sU E) (H.sym (rmU E))
      where E = trans (cong₂ C._+ᵘ_ (trans (cong (C.zeroUsage C.+ᵘ_) (cong (Many C.*ᵘ_) (+ᵘ-identityˡ C.zeroUsage))) (DT.z+qz Many))
                                    (*ᵘ-identityˡ Ψ))
                      (+ᵘ-identityˡ Ψ)

    c-apply : ∀ {A B} → ρ̂ᶜ (DT.⊢applyᶜ {Γ = Γ} {A = A} {B = B}) ≅ DT.⊢applyᶜ {Γ = ρ̂S Γ} {A = ρ̂ A} {B = ρ̂ B}
    c-apply = H.trans (ρ̂ᶜ-sU (DT.z+qz Many)) (H.sym (rmU (DT.z+qz Many)))

    c-applyEff : ∀ {A B} → ρ̂ᶜ (DT.⊢applyEffᶜ {Γ = Γ} {A = A} {B = B}) ≅ DT.⊢applyEffᶜ {Γ = ρ̂S Γ} {A = ρ̂ A} {B = ρ̂ B}
    c-applyEff = H.trans (ρ̂ᶜ-sU (DT.z+qz Many)) (H.sym (rmU (DT.z+qz Many)))

    c-effApp : ∀ {Ψ₁ Ψ₂ A B f x} (a : Γ ⊢[ Ψ₁ ] f ∷ A T.⇒[ mk-kind Many T.eff ] B ! pure) (b : Γ ⊢[ Ψ₂ ] x ∷ A ! pure)
             → ρ̂ᶜ (DT.⊢effAppᶜ a b) ≅ DT.⊢effAppᶜ (ρ̂ᶜ a) (ρ̂ᶜ b)
    c-effApp {f = f} {x} a b =
      ≅lam refl (cong₂ G.app (ρ̂ₜ-ren suc f) (ρ̂ₜ-ren suc x))
        (≅2 _ _ GT.⊢app refl (ρ̂ₜ-ren suc f) (≅1 _ _ (GT.⊢sub-eff Once.Type.Sub.⊑-pe) refl (ρ̂ₜ-ren suc f) (wk≅ T.Unit a))
                        refl (ρ̂ₜ-ren suc x) (≅1 _ _ (GT.⊢sub-eff Once.Type.Sub.⊑-pe) refl (ρ̂ₜ-ren suc x) (wk≅ T.Unit b)))

  -- The functor combinators: the substituted combinator sits at `⟦ ρ̂F F ⟧T`,
  -- the image of the original at `ρ̂ (⟦ F ⟧T _)`; one J on that equation.
  module _ {n} {Γ : C.Ctx n} where
    private
      in-gen : ∀ {m₀} {Δ₀ : C.Ctx m₀} {G : T.Functor} (w : WellFormedF G) {X} (e : X ≡ ⟦ G ⟧T (μ-type G))
             → GT.⊢lam {Γ = Δ₀} {q = Many} refl (GT.⊢roll w (subst (λ Y → (Δ₀ C., X) ⊢[ C.singleUse zero T.One ] G.var zero ∷ Y ! pure) e (GT.⊢var zero)))
               ≅ DT.⊢inᶜ {Γ = Δ₀} w
      in-gen w refl = H.refl

      out-gen : ∀ {m₀} {Δ₀ : C.Ctx m₀} {G : T.Functor} (w : WellFormedF G) {X} (e : ⟦ G ⟧T (ν-type G pure) ≡ X)
              → GT.⊢lam {Γ = Δ₀} {q = Many} refl (subst (λ Y → (Δ₀ C., ν-type G pure) ⊢[ C.singleUse zero T.One ] G.out (G.var zero) ∷ Y ! pure) e
                                              (GT.⊢out w (GT.⊢var zero)))
                ≅ DT.⊢outᶜ {Γ = Δ₀} w
      out-gen w refl = H.refl

      outEff-gen : ∀ {m₀} {Δ₀ : C.Ctx m₀} {G : T.Functor} (w : WellFormedF G) {X} (e : ⟦ G ⟧T (ν-type G T.eff) ≡ X)
                 → GT.⊢lam {Γ = Δ₀} {q = Many} refl (GT.⊢lam {q = Many} refl
                     (subst (λ Y → ((Δ₀ C., ν-type G T.eff) C., T.Unit) ⊢[ T.Zero C.∷ C.singleUse zero T.One ] G.out (G.var (suc zero)) ∷ Y ! T.eff) e
                            (GT.⊢out w (DT.⊢var′ (suc zero) T.eff))))
                   ≅ DT.⊢outEffᶜ {Γ = Δ₀} w
      outEff-gen w refl = H.refl

    c-in : ∀ {F} (wf : WellFormedF F) → ρ̂ᶜ (DT.⊢inᶜ {Γ = Γ} wf) ≅ DT.⊢inᶜ {Γ = ρ̂S Γ} (ρ̂-wf wf)
    c-in {F} wf = in-gen (ρ̂-wf wf) (ρ̂-⟦⟧ F (μ-type F))

    c-out : ∀ {F} (wf : WellFormedF F) → ρ̂ᶜ (DT.⊢outᶜ {Γ = Γ} wf) ≅ DT.⊢outᶜ {Γ = ρ̂S Γ} (ρ̂-wf wf)
    c-out {F} wf = out-gen (ρ̂-wf wf) (sym (ρ̂-⟦⟧ F (ν-type F pure)))

    c-outEff : ∀ {F} (wf : WellFormedF F) → ρ̂ᶜ (DT.⊢outEffᶜ {Γ = Γ} wf) ≅ DT.⊢outEffᶜ {Γ = ρ̂S Γ} (ρ̂-wf wf)
    c-outEff {F} wf = outEff-gen (ρ̂-wf wf) (sym (ρ̂-⟦⟧ F (ν-type F T.eff)))

    private
      cata-gen : ∀ {m₀} {Δ₀ : C.Ctx m₀} {G : T.Functor} {R : Type} {Ψ t π} (w : WellFormedF G) {X} (e : X ≡ ⟦ G ⟧T R)
                   (D : Δ₀ ⊢[ Ψ ] t ∷ X T.⇒[ mk-kind Many π ] R ! pure)
               → GT.⊢let D (GT.⊢lam {q = Many} refl (GT.⊢fold w
                     (subst (λ Y → ((Δ₀ C., X T.⇒[ mk-kind Many π ] R) C., μ-type G) ⊢[ C.singleUse (suc zero) T.One ]
                                     G.var (suc zero) ∷ Y T.⇒[ mk-kind Many π ] R ! π) e (DT.⊢var′ (suc zero) π))
                     (DT.⊢var′ zero π)))
                 ≅ GT.⊢let (subst (λ Y → Δ₀ ⊢[ Ψ ] t ∷ Y T.⇒[ mk-kind Many π ] R ! pure) e D)
                           (GT.⊢lam {q = Many} refl (GT.⊢fold w (DT.⊢var′ (suc zero) π) (DT.⊢var′ zero π)))
      cata-gen w refl D = H.refl

      ana-gen : ∀ {m₀} {Δ₀ : C.Ctx m₀} {G : T.Functor} {R : Type} {Ψ c π π₀} (w : WellFormedF G) {X} (e : X ≡ ⟦ G ⟧T R)
                  (Y : Δ₀ ⊢[ Ψ ] c ∷ R T.⇒[ mk-kind Many π ] X ! pure)
              → GT.⊢unfold w (subst (λ Z → (Δ₀ C., R) ⊢[ T.Zero C.∷ Ψ ] G.wk c ∷ R T.⇒[ mk-kind Many π ] Z ! π₀) e
                                     (GT.⊢sub-eff (Once.Type.Sub.pure⊑ π₀) (DT.wk-⊢′ R Y)))
                             (DT.⊢var′ zero π₀)
                ≅ GT.⊢unfold w (GT.⊢sub-eff (Once.Type.Sub.pure⊑ π₀)
                                  (DT.wk-⊢′ R (subst (λ Z → Δ₀ ⊢[ Ψ ] c ∷ R T.⇒[ mk-kind Many π ] Z ! pure) e Y)))
                               (DT.⊢var′ zero π₀)
      ana-gen w refl Y = H.refl

    c-cata : ∀ {Ψ F A π alg} (wf : WellFormedF F) (da : Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧T A T.⇒[ mk-kind Many π ] A ! pure)
           → ρ̂ᶜ (DT.⊢cataᶜ wf da)
             ≅ DT.⊢cataᶜ (ρ̂-wf wf) (subst (λ X → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ alg ∷ X T.⇒[ mk-kind Many π ] ρ̂ A ! pure) (ρ̂-⟦⟧ F A) (ρ̂ᶜ da))
    c-cata {Ψ} {F} {A} wf da =
      H.trans (ρ̂ᶜ-sU E) (H.trans (cata-gen (ρ̂-wf wf) (ρ̂-⟦⟧ F A) (ρ̂ᶜ da)) (H.sym (rmU E)))
      where
        open import Once.Surface.Properties using (+ᵘ-identityˡ; *ᵘ-identityˡ)
        E = trans (cong₂ C._+ᵘ_ (+ᵘ-identityˡ C.zeroUsage) (*ᵘ-identityˡ Ψ)) (+ᵘ-identityˡ Ψ)

    c-ana : ∀ {Ψ F A π₀ π c} (wf : WellFormedF F) (dc : Γ ⊢[ Ψ ] c ∷ A T.⇒[ mk-kind Many π ] ⟦ F ⟧T A ! pure)
          → ρ̂ᶜ (DT.⊢anaᶜ {π₀ = π₀} wf dc)
            ≅ DT.⊢anaᶜ {π₀ = π₀} (ρ̂-wf wf) (subst (λ X → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ c ∷ ρ̂ A T.⇒[ mk-kind Many π ] X ! pure) (ρ̂-⟦⟧ F A) (ρ̂ᶜ dc))
    c-ana {Ψ} {F} {A} {π₀} {π} {c} wf dc =
      ≅lam refl (cong (λ u → G.unfold u (G.var zero)) (ρ̂ₜ-ren suc c))
        (H.trans (ρ̂ᶜ-sUf (T.One C.∷_) (+ᵘ-identityʳ Ψ))
          (H.trans (≅2 _ _ (GT.⊢unfold (ρ̂-wf wf)) refl (ρ̂ₜ-ren suc c)
                       (H.trans (rmA (λ Z → ρ̂ A T.⇒[ mk-kind Many π ] Z) (ρ̂-⟦⟧ F A))
                         (H.trans (≅1 _ _ (GT.⊢sub-eff (Once.Type.Sub.pure⊑ π₀)) refl (ρ̂ₜ-ren suc c) (wk≅ A dc))
                                  (H.sym (rmA (λ Z → ρ̂ A T.⇒[ mk-kind Many π ] Z) (ρ̂-⟦⟧ F A)))))
                       refl refl H.refl)
            (H.trans (ana-gen (ρ̂-wf wf) (ρ̂-⟦⟧ F A) (ρ̂ᶜ dc))
                     (H.sym (rmUf (T.One C.∷_) (+ᵘ-identityʳ Ψ))))))
      where open import Once.Surface.Properties using (+ᵘ-identityʳ)
