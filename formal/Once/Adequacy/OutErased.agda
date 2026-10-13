-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OutErased
--
-- D194: `liftFn-Out` — the combinator reduction for the ν DESTRUCTOR, the
-- mirror of `InErased.liftFn-In`.
--
-- Two things differ from the `In` side, and both come from the same place:
-- `In` CONSTRUCTS and `Out` FORCES.
--
--   * `In-ir`'s transport is on the DOMAIN (the layer type is the input), so
--     `InErased` peels it with `evalᴰ-subst-dom`. `Out-ir`'s is on the
--     CODOMAIN, which needs the mirror lemma `evalᴰ-subst-cod`.
--   * `In` emits nothing, so `in-trace` is `[]`. `Out` emits whatever forcing
--     the suspension emits, so there is no constant to prove — the trace half
--     is an EQUALITY between the two sides' traces, both of which are the
--     forced computation's own.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.OutErased (fmt : TargetNum) (ρ : CallEnv) where

open import Function using (id)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym)

open import Once.Spec.Word using (Carrier)
open import Once.Spec.Type.Grade using (Purity)
open import Once.Spec.Type using (Type; Functor; ν-type; ⟦_⟧T)
open import Once.Spec.Type.WellFormed using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseType; base-Unit; base-Int; base-Float; base-Prod; base-Sum)
open import Once.Spec.FunctorMeaning using (translateF)
open import Once.IRTy using (IRTy; eraseF; ⌈_⌉F; ⌈_⌉; ⌊_⌋; ⌊⟧T-commute; ⌈⟧TI-commute)
import Once.IRTy as IT
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉)
open import Once.Spec.Polynomial using (SFunctor; SK; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Machine using (tF-coh; base-coh; coerce-ν-out)
open import Once.Denotation.TraceMonad using (T; fmapT)
open import Once.Denotation.TraceMonadLaws using (fmapT-id; fmapT-∘; fmapT-cong; RelT′-refl)
open import Once.Denotation.ValueDomainLaws using (∼ᵈ-refl)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Data.Empty using (⊥-elim)
open import Once.Denotation.ValueDomain
  using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; νᵈ; cohᴰ; coerce-functor⁻¹-D; module νᵈ)
open νᵈ using (forceᵈ)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.Meaning using (out-sem)
open import Once.Adequacy.CataErased fmt ρ using (subst-T-fmap)
open import Once.Adequacy.AnaErased fmt ρ using (push-⊎fam₁; push-⊎fam₂; push-×fam; push⊎₁; push⊎₂; push×; push⊎₁⁻; push⊎₂⁻; push×⁻)
import Once.IR as IR

------------------------------------------------------------------------
-- The transported `Out` morphism `realize-infer` uses
------------------------------------------------------------------------

Out-ir : ∀ {F : Functor} {π : Purity} → WellFormedF F → IR.IR ⌊ ν-type F π ⌋ ⌊ ⟦ F ⟧T (ν-type F π) ⌋
Out-ir {F} {π} wfF = subst (λ o → IR.IR ⌊ ν-type F π ⌋ o)
                       (sym (⌊⟧T-commute F (ν-type F π)))
                       (IR.Out (wf-⌊⌋ wfF))

-- The CODOMAIN mirror of `CataErased.evalᴰ-subst-dom`. Match-to-refl.
evalᴰ-subst-cod : ∀ {A : IRTy} {o₁ o₂ : IRTy} (eq : o₁ ≡ o₂)
    (m : IR.IR A o₁) (z : ⟦ A ⟧ᴰᴵ)
  → evalᴰ fmt ρ (subst (λ o → IR.IR A o) eq m) z
    ≡ subst (λ o → T ⟦ o ⟧ᴰᴵ) eq (evalᴰ fmt ρ m z)
evalᴰ-subst-cod refl m z = refl

-- A transport of the IRTy-indexed computation maps its leaves (plan 0.105).
subst-TI-fmap : ∀ {o₁ o₂ : IRTy} (p : o₁ ≡ o₂) (h : T ⟦ o₁ ⟧ᴰᴵ)
  → subst (λ o → T ⟦ o ⟧ᴰᴵ) p h ≡ fmapT (subst ⟦_⟧ᴰᴵ p) h
subst-TI-fmap refl h = sym (fmapT-id h)

-- Forcing a ν transported BACKWARDS along the coherence maps the forced
-- tree's leaves the same way — `forceᵈ` is a field, so a transport of the
-- record is a transport of it.
force-subst-fmap : ∀ {H₁ H₂ : SFunctor} (p : H₁ ≡ H₂) (v : νᵈ H₂)
  → forceᵈ (subst id (sym (cong νᵈ p)) v)
    ≡ fmapT (subst (λ H → ⟦ H ⟧SF (νᵈ H)) (sym p)) (forceᵈ v)
force-subst-fmap refl v = sym (fmapT-id (forceᵈ v))

------------------------------------------------------------------------
-- Transport vocabulary the OUT direction needs and the IN direction did not
--
-- `AnaErased`'s `pushS⊕₁`/`pushS⊗` move a functor transport at a FIXED
-- carrier. Here the carrier moves WITH the functor (`νᵈ H` is indexed by the
-- same `H`), so the diagonal has to be split first — `InErased.subst-diag`
-- does this for `μS`, and this is its ν twin — and the pushes are needed in
-- the `sym` direction. All match-to-refl.
------------------------------------------------------------------------

subst-diag-ν⁻ : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) (z : ⟦ H₂ ⟧SF (νᵈ H₂))
  → subst (λ H → ⟦ H ⟧SF (νᵈ H)) (sym eq) z
    ≡ subst (λ H → ⟦ H ⟧SF (νᵈ H₁)) (sym eq)
        (subst (λ C → ⟦ H₂ ⟧SF C) (sym (cong νᵈ eq)) z)
subst-diag-ν⁻ refl z = refl

pushS⊕₁⁻ : ∀ {X : Set} {H₁ H₂ H₁' H₂' : SFunctor}
             (p : H₁ ≡ H₁') (q : H₂ ≡ H₂') (w : ⟦ H₁' ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊕_ p q)) (inj₁ w)
    ≡ inj₁ (subst (λ H → ⟦ H ⟧SF X) (sym p) w)
pushS⊕₁⁻ refl refl w = refl

pushS⊕₂⁻ : ∀ {X : Set} {H₁ H₂ H₁' H₂' : SFunctor}
             (p : H₁ ≡ H₁') (q : H₂ ≡ H₂') (w : ⟦ H₂' ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊕_ p q)) (inj₂ w)
    ≡ inj₂ (subst (λ H → ⟦ H ⟧SF X) (sym q) w)
pushS⊕₂⁻ refl refl w = refl

pushS⊗⁻ : ∀ {X : Set} {H₁ H₂ H₁' H₂' : SFunctor}
            (p : H₁ ≡ H₁') (q : H₂ ≡ H₂') (a : ⟦ H₁' ⟧SF X) (b : ⟦ H₂' ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊗_ p q)) (a , b)
    ≡ (subst (λ H → ⟦ H ⟧SF X) (sym p) a , subst (λ H → ⟦ H ⟧SF X) (sym q) b)
pushS⊗⁻ refl refl a b = refl

-- The `sym` forms. `sym (cong₂ f p q)` is not definitionally `cong₂ f (sym p)
-- (sym q)`, so the inverse direction needs its own statements rather than a
-- rewrite of the forward ones.
push-+ᴰ₁⁻ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (z : ⟦ A' ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Spec.Type._+_ p q)) (inj₁ z)
    ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym p) z)
push-+ᴰ₁⁻ refl refl z = refl

push-+ᴰ₂⁻ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (z : ⟦ B' ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Spec.Type._+_ p q)) (inj₂ z)
    ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym q) z)
push-+ᴰ₂⁻ refl refl z = refl

push-*ᴰ⁻ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰ) (b : ⟦ B' ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Spec.Type._*_ p q)) (a , b)
    ≡ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym p) a , subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym q) b)
push-*ᴰ⁻ refl refl a b = refl

-- The same at the IRTy interpretation, which is where `⌊⟧T-commute` lives.
push-+ᴵ₁⁻ : ∀ {A A' B B' : IRTy} (p : A ≡ A') (q : B ≡ B') (z : ⟦ A' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ IT._+_ p q)) (inj₁ z) ≡ inj₁ (subst ⟦_⟧ᴰᴵ (sym p) z)
push-+ᴵ₁⁻ refl refl z = refl

push-+ᴵ₂⁻ : ∀ {A A' B B' : IRTy} (p : A ≡ A') (q : B ≡ B') (z : ⟦ B' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ IT._+_ p q)) (inj₂ z) ≡ inj₂ (subst ⟦_⟧ᴰᴵ (sym q) z)
push-+ᴵ₂⁻ refl refl z = refl

push-*ᴵ⁻ : ∀ {A A' B B' : IRTy} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰᴵ) (b : ⟦ B' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ IT._*_ p q)) (a , b)
    ≡ (subst ⟦_⟧ᴰᴵ (sym p) a , subst ⟦_⟧ᴰᴵ (sym q) b)
push-*ᴵ⁻ refl refl a b = refl

-- The layer map, CARRIER-GENERIC. `out-layerᴵ` above is it at `A := ν-type G`,
-- which is all `evalᴰ (Out …)` ever needs; the induction needs the carrier
-- free, because at `⊕` the sub-functor changes while the carrier does not.
out-layer-gen : ∀ (G : Functor) (wfG : WellFormedF G) (A : Type)
    (layer : ⟦ translateF Carrier Carrier ⌈ eraseF G ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
  → ⟦ IT.⟦ eraseF G ⟧TI ⌊ A ⌋ ⟧ᴰᴵ
out-layer-gen G wfG A layer =
  subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute (eraseF G) ⌊ A ⌋))
    (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A ⌋ ⌉
      (coerce-ν-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ layer))

-- K-leaf transport vocabulary. `⟦ SK b ⟧SF` is carrier-blind, so a carrier
-- transport over it is the identity; and `tF-coh (K B)` is a `cong SK`, so the
-- functor transport collapses to the base one. `AnaErased` has the forward
-- forms (`subst-KF-const`, `pushSK`); these are the `sym` direction.
subst-SK-const : ∀ {b X Y : Set} (eq : X ≡ Y) (v : ⟦ SK b ⟧SF X)
  → subst (λ Z → ⟦ SK b ⟧SF Z) eq v ≡ v
subst-SK-const refl v = refl

pushSK⁻ : ∀ {X : Set} {b₁ b₂ : Set} (eq : b₁ ≡ b₂) (v : ⟦ SK b₂ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong SK eq)) v ≡ subst id (sym eq) v
pushSK⁻ refl v = refl

-- The layer map splits across an injection / pair: `coerce-ν-out` and
-- `coerce-functor⁻¹-D` are both structural there, so all that is left is
-- pushing the `⌈⟧TI-commute` transport through, which is `push-+ᴰ₁⁻`.
out-layer-gen-⊕₁ : ∀ (G₁ G₂ : Functor) (wfA : WellFormedF G₁) (wfB : WellFormedF G₂)
    (A : Type) (w : ⟦ translateF Carrier Carrier ⌈ eraseF G₁ ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
  → out-layer-gen (G₁ Once.Spec.Type.⊕ G₂) (wf-Sum wfA wfB) A (inj₁ w)
    ≡ inj₁ (out-layer-gen G₁ wfA A w)
out-layer-gen-⊕₁ G₁ G₂ wfA wfB A w =
  push-+ᴰ₁⁻ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋) _

out-layer-gen-⊕₂ : ∀ (G₁ G₂ : Functor) (wfA : WellFormedF G₁) (wfB : WellFormedF G₂)
    (A : Type) (w : ⟦ translateF Carrier Carrier ⌈ eraseF G₂ ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
  → out-layer-gen (G₁ Once.Spec.Type.⊕ G₂) (wf-Sum wfA wfB) A (inj₂ w)
    ≡ inj₂ (out-layer-gen G₂ wfB A w)
out-layer-gen-⊕₂ G₁ G₂ wfA wfB A w =
  push-+ᴰ₂⁻ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋) _

out-layer-gen-⊗ : ∀ (G₁ G₂ : Functor) (wfA : WellFormedF G₁) (wfB : WellFormedF G₂)
    (A : Type) (a : ⟦ translateF Carrier Carrier ⌈ eraseF G₁ ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                (b : ⟦ translateF Carrier Carrier ⌈ eraseF G₂ ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
  → out-layer-gen (G₁ Once.Spec.Type.⊗ G₂) (wf-Prod wfA wfB) A (a , b)
    ≡ (out-layer-gen G₁ wfA A a , out-layer-gen G₂ wfB A b)
out-layer-gen-⊗ G₁ G₂ wfA wfB A a b =
  push-*ᴰ⁻ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋) _ _

-- The K-leaf coherence — `AnaErased.base-in` read the other way, with
-- `coerce-base-to-full`/`inject` where that one has `coerce-full-to-base`/
-- `forget`. Induction on the base witness.
base-out : ∀ (B : Type) (ib : IsBaseType B) (A : Type)
    (ℓ : ⟦ translateF Carrier Carrier (Once.Spec.Type.K B) ⟧SF ⟦ A ⟧ᴰ)
  → subst id (cohᴰ (⟦ Once.Spec.Type.K B ⟧T A))
      (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Spec.Type.K B) A))
        (out-layer-gen (Once.Spec.Type.K B) (wf-K ib) A (subst id (sym (base-coh B)) ℓ)))
    ≡ coerce-functor⁻¹-D (wf-K ib) A (coerce-ν-out (wf-K ib) ⟦ A ⟧ᴰ ℓ)
base-out _ base-Unit   A ℓ = refl
base-out _ base-Int    A ℓ = refl
base-out _ base-Float  A ℓ = refl
base-out (X Once.Spec.Type.* Y) (base-Prod ibA ibB) A (a , b) =
  trans (cong (λ z → subst id (cohᴰ (X Once.Spec.Type.* Y))
                  (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Spec.Type.K (X Once.Spec.Type.* Y)) A))
                    (out-layer-gen (Once.Spec.Type.K (X Once.Spec.Type.* Y))
                                   (wf-K (base-Prod ibA ibB)) A z)))
              (push×⁻ (base-coh X) (base-coh Y) a b))
  (trans (push× (cohᴰ X) (cohᴰ Y) _ _)
         (cong₂ _,_ (base-out _ ibA A a) (base-out _ ibB A b)))
base-out (X Once.Spec.Type.+ Y) (base-Sum ibA ibB) A (inj₁ a) =
  trans (cong (λ z → subst id (cohᴰ (X Once.Spec.Type.+ Y))
                  (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Spec.Type.K (X Once.Spec.Type.+ Y)) A))
                    (out-layer-gen (Once.Spec.Type.K (X Once.Spec.Type.+ Y))
                                   (wf-K (base-Sum ibA ibB)) A z)))
              (push⊎₁⁻ (base-coh X) (base-coh Y) a))
  (trans (push⊎₁ (cohᴰ X) (cohᴰ Y) _)
         (cong inj₁ (base-out _ ibA A a)))
base-out (X Once.Spec.Type.+ Y) (base-Sum ibA ibB) A (inj₂ b) =
  trans (cong (λ z → subst id (cohᴰ (X Once.Spec.Type.+ Y))
                  (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Spec.Type.K (X Once.Spec.Type.+ Y)) A))
                    (out-layer-gen (Once.Spec.Type.K (X Once.Spec.Type.+ Y))
                                   (wf-K (base-Sum ibA ibB)) A z)))
              (push⊎₂⁻ (base-coh X) (base-coh Y) b))
  (trans (push⊎₂ (cohᴰ X) (cohᴰ Y) _)
         (cong inj₂ (base-out _ ibB A b)))

-- THE ONE REMAINING OBLIGATION, over an abstract layer AND an abstract
-- carrier — `AnaErased.coerce-νin-erase-D` inverted. Five clauses on `wfG`
-- (not on the raw functor: `coerce-ν-out` is indexed by the witness).
νout-erase-D : ∀ (G : Functor) (wfG : WellFormedF G) (A : Type)
    (ℓ : ⟦ translateF Carrier Carrier G ⟧SF ⟦ A ⟧ᴰ)
  → subst id (cohᴰ (⟦ G ⟧T A))
      (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute G A))
        (out-layer-gen G wfG A
          (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (sym (tF-coh G))
            (subst (λ C → ⟦ translateF Carrier Carrier G ⟧SF C) (sym (cohᴰ A)) ℓ))))
    ≡ coerce-functor⁻¹-D wfG A (coerce-ν-out wfG ⟦ A ⟧ᴰ ℓ)
νout-erase-D (Once.Spec.Type.K B) (wf-K ib) A ℓ =
  trans (cong (λ z → OUTK (out-layer-gen (Once.Spec.Type.K B) (wf-K ib) A
                            (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                   (sym (tF-coh (Once.Spec.Type.K B))) z)))
              (subst-SK-const (sym (cohᴰ A)) ℓ))
        (trans (cong (λ z → OUTK (out-layer-gen (Once.Spec.Type.K B) (wf-K ib) A z))
                     (pushSK⁻ (base-coh B) ℓ))
               (base-out B ib A ℓ))
  where
    OUTK : ⟦ IT.⟦ eraseF (Once.Spec.Type.K B) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ Once.Spec.Type.K B ⟧T A ⟧ᴰ
    OUTK z = subst id (cohᴰ (⟦ Once.Spec.Type.K B ⟧T A))
               (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Spec.Type.K B) A)) z)
νout-erase-D _ wf-Id              A ℓ        = subst-subst-sym (cohᴰ A)
νout-erase-D (F Once.Spec.Type.⊕ G) (wf-Sum wfA wfB) A (inj₁ x) =
  trans (cong (λ z → OUT (out-layer-gen (F Once.Spec.Type.⊕ G) (wf-Sum wfA wfB) A
                           (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                  (sym (tF-coh (F Once.Spec.Type.⊕ G))) z)))
              (push-⊎fam₁ (λ C → ⟦ translateF Carrier Carrier F ⟧SF C)
                          (λ C → ⟦ translateF Carrier Carrier G ⟧SF C)
                          (sym (cohᴰ A)) x))
 (trans (cong (λ z → OUT (out-layer-gen (F Once.Spec.Type.⊕ G) (wf-Sum wfA wfB) A z))
              (pushS⊕₁⁻ (tF-coh F) (tF-coh G) _))
 (trans (cong OUT (out-layer-gen-⊕₁ F G wfA wfB A _))
 (trans (cong (subst id (cohᴰ (⟦ F Once.Spec.Type.⊕ G ⟧T A)))
              (push-+ᴵ₁⁻ (⌊⟧T-commute F A) (⌊⟧T-commute G A) _))
 (trans (push⊎₁ (cohᴰ (⟦ F ⟧T A)) (cohᴰ (⟦ G ⟧T A)) _)
        (cong inj₁ (νout-erase-D F wfA A x))))))
  where
    OUT : ⟦ IT.⟦ eraseF (F Once.Spec.Type.⊕ G) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ F Once.Spec.Type.⊕ G ⟧T A ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F Once.Spec.Type.⊕ G ⟧T A))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (F Once.Spec.Type.⊕ G) A)) z)
νout-erase-D (F Once.Spec.Type.⊕ G) (wf-Sum wfA wfB) A (inj₂ y) =
  trans (cong (λ z → OUT (out-layer-gen (F Once.Spec.Type.⊕ G) (wf-Sum wfA wfB) A
                           (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                  (sym (tF-coh (F Once.Spec.Type.⊕ G))) z)))
              (push-⊎fam₂ (λ C → ⟦ translateF Carrier Carrier F ⟧SF C)
                          (λ C → ⟦ translateF Carrier Carrier G ⟧SF C)
                          (sym (cohᴰ A)) y))
 (trans (cong (λ z → OUT (out-layer-gen (F Once.Spec.Type.⊕ G) (wf-Sum wfA wfB) A z))
              (pushS⊕₂⁻ (tF-coh F) (tF-coh G) _))
 (trans (cong OUT (out-layer-gen-⊕₂ F G wfA wfB A _))
 (trans (cong (subst id (cohᴰ (⟦ F Once.Spec.Type.⊕ G ⟧T A)))
              (push-+ᴵ₂⁻ (⌊⟧T-commute F A) (⌊⟧T-commute G A) _))
 (trans (push⊎₂ (cohᴰ (⟦ F ⟧T A)) (cohᴰ (⟦ G ⟧T A)) _)
        (cong inj₂ (νout-erase-D G wfB A y))))))
  where
    OUT : ⟦ IT.⟦ eraseF (F Once.Spec.Type.⊕ G) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ F Once.Spec.Type.⊕ G ⟧T A ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F Once.Spec.Type.⊕ G ⟧T A))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (F Once.Spec.Type.⊕ G) A)) z)
νout-erase-D (F Once.Spec.Type.⊗ G) (wf-Prod wfA wfB) A (x , y) =
  trans (cong (λ z → OUT (out-layer-gen (F Once.Spec.Type.⊗ G) (wf-Prod wfA wfB) A
                           (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                  (sym (tF-coh (F Once.Spec.Type.⊗ G))) z)))
              (push-×fam (λ C → ⟦ translateF Carrier Carrier F ⟧SF C)
                         (λ C → ⟦ translateF Carrier Carrier G ⟧SF C)
                         (sym (cohᴰ A)) x y))
 (trans (cong (λ z → OUT (out-layer-gen (F Once.Spec.Type.⊗ G) (wf-Prod wfA wfB) A z))
              (pushS⊗⁻ (tF-coh F) (tF-coh G) _ _))
 (trans (cong OUT (out-layer-gen-⊗ F G wfA wfB A _ _))
 (trans (cong (subst id (cohᴰ (⟦ F Once.Spec.Type.⊗ G ⟧T A)))
              (push-*ᴵ⁻ (⌊⟧T-commute F A) (⌊⟧T-commute G A) _ _))
 (trans (push× (cohᴰ (⟦ F ⟧T A)) (cohᴰ (⟦ G ⟧T A)) _ _)
        (cong₂ _,_ (νout-erase-D F wfA A x) (νout-erase-D G wfB A y))))))
  where
    OUT : ⟦ IT.⟦ eraseF (F Once.Spec.Type.⊗ G) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ F Once.Spec.Type.⊗ G ⟧T A ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F Once.Spec.Type.⊗ G ⟧T A))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (F Once.Spec.Type.⊗ G) A)) z)

-- THE `Out` EQUATION (plan 0.105): the IR's `Out`, through the erasure
-- transports, IS the direct `out-sem` — one equation of trees. Each transport
-- maps the forced tree's leaves, the maps fuse (`fmapT-∘`), and the leaf maps
-- agree pointwise (`νout-erase-D`).
liftFn-Out : ∀ {F : Functor} {π : Purity} (wfF : WellFormedF F) (v : ⟦ ν-type F π ⟧ᴰ)
  → liftFn fmt ρ {ν-type F π} {⟦ F ⟧T (ν-type F π)} (Out-ir wfF) v ≡ out-sem {π = π} wfF v
liftFn-Out {F} {π} wfF v =
  trans (subst-T-fmap (cohᴰ (⟦ F ⟧T (ν-type F π))) (evalᴰ fmt ρ (Out-ir wfF) v′))
  (trans (cong (fmapT (subst id (cohᴰ (⟦ F ⟧T (ν-type F π)))))
               (trans (evalᴰ-subst-cod (sym (⌊⟧T-commute F (ν-type F π))) (IR.Out (wf-⌊⌋ wfF)) v′)
                      (subst-TI-fmap (sym (⌊⟧T-commute F (ν-type F π))) (evalᴰ fmt ρ (IR.Out (wf-⌊⌋ wfF)) v′))))
  (trans (fmapT-∘ (subst id (cohᴰ (⟦ F ⟧T (ν-type F π)))) (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute F (ν-type F π))))
                  (evalᴰ fmt ρ (IR.Out (wf-⌊⌋ wfF)) v′))
  (trans (fmapT-∘ OUT (out-layer-gen F wfF (ν-type F π)) (forceᵈ v′))
  (trans (cong (fmapT (λ ℓ → OUT (out-layer-gen F wfF (ν-type F π) ℓ))) (force-subst-fmap (tF-coh F) v))
  (trans (fmapT-∘ (λ ℓ → OUT (out-layer-gen F wfF (ν-type F π) ℓ))
                  (subst (λ H → ⟦ H ⟧SF (νᵈ H)) (sym (tF-coh F))) (forceᵈ v))
         (fmapT-cong (λ ℓ → trans (cong (λ z → OUT (out-layer-gen F wfF (ν-type F π) z))
                                         (subst-diag-ν⁻ (tF-coh F) ℓ))
                                   (νout-erase-D F wfF (ν-type F π) ℓ))
                     (forceᵈ v)))))))
  where
    v′ = subst id (sym (cohᴰ (ν-type F π))) v
    OUT : ⟦ IT.⟦ eraseF F ⟧TI ⌊ ν-type F π ⌋ ⟧ᴰᴵ → ⟦ ⟦ F ⟧T (ν-type F π) ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F ⟧T (ν-type F π)))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute F (ν-type F π))) z)

------------------------------------------------------------------------
-- The bridge's two halves, packaged
------------------------------------------------------------------------

