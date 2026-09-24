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

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.OutErased (fmt : TargetNum) where

open import Function using (id)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym)

open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ν-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum)
open import Once.IRTy using (IRTy; eraseF; ⌈_⌉F; ⌈_⌉; ⌊_⌋; ⌊⟧T-commute; ⌈⟧TI-commute)
import Once.IRTy as IT
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉)
open import Once.Semantics.Functor using (SFunctor; SK; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Machine using (coerce-functor⁻¹; coh; tF-coh; base-coh; ⟦_⟧F; coerce-ν-out)
open import Once.Res using (Res; stopped; returns; mapRes; mapRes-id; mapRes-∘; mapRes-cong; Res-rel)
open import Once.Denotation.TraceMonad using (T; fmapT; projTrace)
open import Once.Denotation.ValueDomain
open import Once.Denotation.ValueDomainLaws using (∼ᵈ-refl; _∼ᵈ_)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Data.Empty using (⊥-elim)
  using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; νᵈ; forceᵈ; cohᴰ; coerce-functor⁻¹-D)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.Meaning using (out-sem)
open import Once.Adequacy.CataErased fmt using (subst-T-projTrace; subst-T-resT; T-ext)
open import Once.Adequacy.MeaningRelation fmt using (RelV; RelT)
open import Once.Adequacy.CataBridge fmt using (base-refl)
open import Once.Adequacy.AnaErased fmt using (push-⊎fam₁; push-⊎fam₂; push-×fam; push⊎₁; push⊎₂; push×; push⊎₁⁻; push⊎₂⁻; push×⁻)
open import Once.Postulates using (extensionality)
import Once.IR as IR

------------------------------------------------------------------------
-- The transported `Out` morphism `realize-infer` uses
------------------------------------------------------------------------

Out-ir : ∀ {F : Functor} → WellFormedF F → IR.IR ⌊ ν-type F ⌋ ⌊ ⟦ F ⟧T (ν-type F) ⌋
Out-ir {F} wfF = subst (λ o → IR.IR ⌊ ν-type F ⌋ o)
                       (sym (⌊⟧T-commute F (ν-type F)))
                       (IR.Out (wf-⌊⌋ wfF))

-- The CODOMAIN mirror of `CataErased.evalᴰ-subst-dom`. Match-to-refl.
evalᴰ-subst-cod : ∀ {A : IRTy} {o₁ o₂ : IRTy} (eq : o₁ ≡ o₂)
    (m : IR.IR A o₁) (z : ⟦ A ⟧ᴰᴵ)
  → evalᴰ fmt (subst (λ o → IR.IR A o) eq m) z
    ≡ subst (λ o → T ⟦ o ⟧ᴰᴵ) eq (evalᴰ fmt m z)
evalᴰ-subst-cod refl m z = refl

-- `subst` over the IRTy-indexed computation leaves the trace alone.
subst-TI-projTrace : ∀ {o₁ o₂ : IRTy} (p : o₁ ≡ o₂) (h : T ⟦ o₁ ⟧ᴰᴵ) (n : ℕ)
  → projTrace (subst (λ o → T ⟦ o ⟧ᴰᴵ) p h) n ≡ projTrace h n
subst-TI-projTrace refl h n = refl

-- plan 0.98: the RESULT half of the same transport. It used to be stated with
-- `valueT`, which now demands a proof that there IS a value — unwritable for an
-- abstract `h`, and wrong to demand: a transport says nothing about whether the
-- computation returned. The transport moves the result by `mapRes`, and the
-- budget index disappears because the result never depended on it.
subst-TI-resT : ∀ {o₁ o₂ : IRTy} (p : o₁ ≡ o₂) (h : T ⟦ o₁ ⟧ᴰᴵ)
  → T.resT (subst (λ o → T ⟦ o ⟧ᴰᴵ) p h) ≡ mapRes (subst ⟦_⟧ᴰᴵ p) (T.resT h)
subst-TI-resT refl h = sym (mapRes-id (T.resT h))

-- `subst id (cong νᵈ p) = subst νᵈ p`, the ν twin of `InErased.subst-id-μS`.
subst-id-νᵈ : ∀ {H₁ H₂ : SFunctor} (p : H₁ ≡ H₂) (v : νᵈ H₁)
  → subst id (cong νᵈ p) v ≡ subst νᵈ p v
subst-id-νᵈ refl v = refl

-- Forcing a transported ν. Match-to-refl in both components.
forceᵈ-subst : ∀ {H₁ H₂ : SFunctor} (p : H₁ ≡ H₂) (v : νᵈ H₁)
  → forceᵈ (subst νᵈ p v)
    ≡ subst (λ H → T (⟦ H ⟧SF (νᵈ H))) p (forceᵈ v)
forceᵈ-subst refl v = refl

-- Forcing a ν transported BACKWARDS along the coherence: same trace, and the
-- value transported the same way. Both match-to-refl — the whole content is
-- that `forceᵈ` is a field, so a transport of the record is a transport of it.
force-subst-trace : ∀ {H₁ H₂ : SFunctor} (p : H₁ ≡ H₂) (v : νᵈ H₂) (n : ℕ)
  → projTrace (forceᵈ (subst id (sym (cong νᵈ p)) v)) n ≡ projTrace (forceᵈ v) n
force-subst-trace refl v n = refl

-- plan 0.98: the RESULT, not "the value at budget n". Forcing a ν may stop —
-- a halting coalgebra produces no layer — so the old statement, which named a
-- value on both sides, presumed the very thing `Res` now makes optional.
force-subst-res : ∀ {H₁ H₂ : SFunctor} (p : H₁ ≡ H₂) (v : νᵈ H₂)
  → T.resT (forceᵈ (subst id (sym (cong νᵈ p)) v))
    ≡ mapRes (subst (λ H → ⟦ H ⟧SF (νᵈ H)) (sym p)) (T.resT (forceᵈ v))
force-subst-res refl v = sym (mapRes-id (T.resT (forceᵈ v)))

-- The TRACE half.
out-trace : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ν-type F ⟧ᴰ) (n : ℕ)
  → projTrace (liftFn fmt {ν-type F} {⟦ F ⟧T (ν-type F)} (Out-ir wfF) v) n
    ≡ projTrace (forceᵈ v) n
out-trace {F} wfF v n =
  trans (subst-T-projTrace (cohᴰ (⟦ F ⟧T (ν-type F)))
          (evalᴰ fmt (Out-ir wfF) (subst id (sym (cohᴰ (ν-type F))) v)) n)
  (trans (cong (λ hh → projTrace hh n)
            (evalᴰ-subst-cod (sym (⌊⟧T-commute F (ν-type F))) (IR.Out (wf-⌊⌋ wfF))
              (subst id (sym (cohᴰ (ν-type F))) v)))
  (trans (subst-TI-projTrace (sym (⌊⟧T-commute F (ν-type F)))
            (evalᴰ fmt (IR.Out (wf-⌊⌋ wfF)) (subst id (sym (cohᴰ (ν-type F))) v)) n)
         (force-subst-trace (tF-coh F) v n)))

-- The ⌈⌉-side layer map that `evalᴰ (Out …)` applies, transcribed from
-- `DenotTrace`'s `Out` clause at `wf := wf-⌊⌋ wfG`. Naming it is what lets the
-- proof `cong` over the LAYER rather than over the whole computation.
out-layerᴵ : ∀ (G : Functor) (wfG : WellFormedF G)
    (layer : ⟦ translateF Carrier Carrier ⌈ eraseF G ⌉F ⟧SF ⟦ IT.ν-type (eraseF G) ⟧ᴰᴵ)
  → ⟦ IT.⟦ eraseF G ⟧TI (IT.ν-type (eraseF G)) ⟧ᴰᴵ
out-layerᴵ G wfG layer =
  subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute (eraseF G) (IT.ν-type (eraseF G))))
    (coerce-functor⁻¹-D ⌈ eraseF G ⌉F ⌈ IT.ν-type (eraseF G) ⌉
      (coerce-ν-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ layer))

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

-- Pushing a transport through an injection / pair at the ᴰ interpretation of
-- a Type-level sum or product. All match-to-refl; the `⟦_⟧ᴰ` motive is what
-- `AnaErased`'s `push⊎₁`/`push×` (stated at `id`) cannot serve.
push-+ᴰ₁ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (z : ⟦ A ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ Once.Type._+_ p q) (inj₁ z)
    ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p z)
push-+ᴰ₁ refl refl z = refl

push-+ᴰ₂ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (z : ⟦ B ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ Once.Type._+_ p q) (inj₂ z)
    ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) q z)
push-+ᴰ₂ refl refl z = refl

push-*ᴰ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A ⟧ᴰ) (b : ⟦ B ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ Once.Type._*_ p q) (a , b)
    ≡ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p a , subst (λ Ty → ⟦ Ty ⟧ᴰ) q b)
push-*ᴰ refl refl a b = refl

-- The `sym` forms. `sym (cong₂ f p q)` is not definitionally `cong₂ f (sym p)
-- (sym q)`, so the inverse direction needs its own statements rather than a
-- rewrite of the forward ones.
push-+ᴰ₁⁻ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (z : ⟦ A' ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Type._+_ p q)) (inj₁ z)
    ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym p) z)
push-+ᴰ₁⁻ refl refl z = refl

push-+ᴰ₂⁻ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (z : ⟦ B' ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Type._+_ p q)) (inj₂ z)
    ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym q) z)
push-+ᴰ₂⁻ refl refl z = refl

push-*ᴰ⁻ : ∀ {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰ) (b : ⟦ B' ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (cong₂ Once.Type._*_ p q)) (a , b)
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
    (coerce-functor⁻¹-D ⌈ eraseF G ⌉F ⌈ ⌊ A ⌋ ⌉
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
  → out-layer-gen (G₁ Once.Type.⊕ G₂) (wf-Sum wfA wfB) A (inj₁ w)
    ≡ inj₁ (out-layer-gen G₁ wfA A w)
out-layer-gen-⊕₁ G₁ G₂ wfA wfB A w =
  push-+ᴰ₁⁻ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋) _

out-layer-gen-⊕₂ : ∀ (G₁ G₂ : Functor) (wfA : WellFormedF G₁) (wfB : WellFormedF G₂)
    (A : Type) (w : ⟦ translateF Carrier Carrier ⌈ eraseF G₂ ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
  → out-layer-gen (G₁ Once.Type.⊕ G₂) (wf-Sum wfA wfB) A (inj₂ w)
    ≡ inj₂ (out-layer-gen G₂ wfB A w)
out-layer-gen-⊕₂ G₁ G₂ wfA wfB A w =
  push-+ᴰ₂⁻ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋) _

out-layer-gen-⊗ : ∀ (G₁ G₂ : Functor) (wfA : WellFormedF G₁) (wfB : WellFormedF G₂)
    (A : Type) (a : ⟦ translateF Carrier Carrier ⌈ eraseF G₁ ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                (b : ⟦ translateF Carrier Carrier ⌈ eraseF G₂ ⌉F ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
  → out-layer-gen (G₁ Once.Type.⊗ G₂) (wf-Prod wfA wfB) A (a , b)
    ≡ (out-layer-gen G₁ wfA A a , out-layer-gen G₂ wfB A b)
out-layer-gen-⊗ G₁ G₂ wfA wfB A a b =
  push-*ᴰ⁻ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋) _ _

-- The K-leaf coherence — `AnaErased.base-in` read the other way, with
-- `coerce-base-to-full`/`inject` where that one has `coerce-full-to-base`/
-- `forget`. Induction on the base witness.
base-out : ∀ (B : Type) (ib : IsBaseType B) (A : Type)
    (ℓ : ⟦ translateF Carrier Carrier (Once.Type.K B) ⟧SF ⟦ A ⟧ᴰ)
  → subst id (cohᴰ (⟦ Once.Type.K B ⟧T A))
      (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Type.K B) A))
        (out-layer-gen (Once.Type.K B) (wf-K ib) A (subst id (sym (base-coh B)) ℓ)))
    ≡ coerce-functor⁻¹-D (Once.Type.K B) A (coerce-ν-out (wf-K ib) ⟦ A ⟧ᴰ ℓ)
base-out _ base-Unit   A ℓ = refl
base-out _ base-Int    A ℓ = refl
base-out _ base-Float  A ℓ = refl
base-out _ base-Str    A ℓ = refl
base-out _ base-Buffer A ℓ = refl
base-out (X Once.Type.* Y) (base-Prod ibA ibB) A (a , b) =
  trans (cong (λ z → subst id (cohᴰ (X Once.Type.* Y))
                  (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Type.K (X Once.Type.* Y)) A))
                    (out-layer-gen (Once.Type.K (X Once.Type.* Y))
                                   (wf-K (base-Prod ibA ibB)) A z)))
              (push×⁻ (base-coh X) (base-coh Y) a b))
  (trans (push× (cohᴰ X) (cohᴰ Y) _ _)
         (cong₂ _,_ (base-out _ ibA A a) (base-out _ ibB A b)))
base-out (X Once.Type.+ Y) (base-Sum ibA ibB) A (inj₁ a) =
  trans (cong (λ z → subst id (cohᴰ (X Once.Type.+ Y))
                  (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Type.K (X Once.Type.+ Y)) A))
                    (out-layer-gen (Once.Type.K (X Once.Type.+ Y))
                                   (wf-K (base-Sum ibA ibB)) A z)))
              (push⊎₁⁻ (base-coh X) (base-coh Y) a))
  (trans (push⊎₁ (cohᴰ X) (cohᴰ Y) _)
         (cong inj₁ (base-out _ ibA A a)))
base-out (X Once.Type.+ Y) (base-Sum ibA ibB) A (inj₂ b) =
  trans (cong (λ z → subst id (cohᴰ (X Once.Type.+ Y))
                  (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Type.K (X Once.Type.+ Y)) A))
                    (out-layer-gen (Once.Type.K (X Once.Type.+ Y))
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
    ≡ coerce-functor⁻¹-D G A (coerce-ν-out wfG ⟦ A ⟧ᴰ ℓ)
νout-erase-D (Once.Type.K B) (wf-K ib) A ℓ =
  trans (cong (λ z → OUTK (out-layer-gen (Once.Type.K B) (wf-K ib) A
                            (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                   (sym (tF-coh (Once.Type.K B))) z)))
              (subst-SK-const (sym (cohᴰ A)) ℓ))
        (trans (cong (λ z → OUTK (out-layer-gen (Once.Type.K B) (wf-K ib) A z))
                     (pushSK⁻ (base-coh B) ℓ))
               (base-out B ib A ℓ))
  where
    OUTK : ⟦ IT.⟦ eraseF (Once.Type.K B) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ Once.Type.K B ⟧T A ⟧ᴰ
    OUTK z = subst id (cohᴰ (⟦ Once.Type.K B ⟧T A))
               (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (Once.Type.K B) A)) z)
νout-erase-D _ wf-Id              A ℓ        = subst-subst-sym (cohᴰ A)
νout-erase-D (F Once.Type.⊕ G) (wf-Sum wfA wfB) A (inj₁ x) =
  trans (cong (λ z → OUT (out-layer-gen (F Once.Type.⊕ G) (wf-Sum wfA wfB) A
                           (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                  (sym (tF-coh (F Once.Type.⊕ G))) z)))
              (push-⊎fam₁ (λ C → ⟦ translateF Carrier Carrier F ⟧SF C)
                          (λ C → ⟦ translateF Carrier Carrier G ⟧SF C)
                          (sym (cohᴰ A)) x))
 (trans (cong (λ z → OUT (out-layer-gen (F Once.Type.⊕ G) (wf-Sum wfA wfB) A z))
              (pushS⊕₁⁻ (tF-coh F) (tF-coh G) _))
 (trans (cong OUT (out-layer-gen-⊕₁ F G wfA wfB A _))
 (trans (cong (subst id (cohᴰ (⟦ F Once.Type.⊕ G ⟧T A)))
              (push-+ᴵ₁⁻ (⌊⟧T-commute F A) (⌊⟧T-commute G A) _))
 (trans (push⊎₁ (cohᴰ (⟦ F ⟧T A)) (cohᴰ (⟦ G ⟧T A)) _)
        (cong inj₁ (νout-erase-D F wfA A x))))))
  where
    OUT : ⟦ IT.⟦ eraseF (F Once.Type.⊕ G) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ F Once.Type.⊕ G ⟧T A ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F Once.Type.⊕ G ⟧T A))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (F Once.Type.⊕ G) A)) z)
νout-erase-D (F Once.Type.⊕ G) (wf-Sum wfA wfB) A (inj₂ y) =
  trans (cong (λ z → OUT (out-layer-gen (F Once.Type.⊕ G) (wf-Sum wfA wfB) A
                           (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                  (sym (tF-coh (F Once.Type.⊕ G))) z)))
              (push-⊎fam₂ (λ C → ⟦ translateF Carrier Carrier F ⟧SF C)
                          (λ C → ⟦ translateF Carrier Carrier G ⟧SF C)
                          (sym (cohᴰ A)) y))
 (trans (cong (λ z → OUT (out-layer-gen (F Once.Type.⊕ G) (wf-Sum wfA wfB) A z))
              (pushS⊕₂⁻ (tF-coh F) (tF-coh G) _))
 (trans (cong OUT (out-layer-gen-⊕₂ F G wfA wfB A _))
 (trans (cong (subst id (cohᴰ (⟦ F Once.Type.⊕ G ⟧T A)))
              (push-+ᴵ₂⁻ (⌊⟧T-commute F A) (⌊⟧T-commute G A) _))
 (trans (push⊎₂ (cohᴰ (⟦ F ⟧T A)) (cohᴰ (⟦ G ⟧T A)) _)
        (cong inj₂ (νout-erase-D G wfB A y))))))
  where
    OUT : ⟦ IT.⟦ eraseF (F Once.Type.⊕ G) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ F Once.Type.⊕ G ⟧T A ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F Once.Type.⊕ G ⟧T A))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (F Once.Type.⊕ G) A)) z)
νout-erase-D (F Once.Type.⊗ G) (wf-Prod wfA wfB) A (x , y) =
  trans (cong (λ z → OUT (out-layer-gen (F Once.Type.⊗ G) (wf-Prod wfA wfB) A
                           (subst (λ H → ⟦ H ⟧SF ⟦ ⌊ A ⌋ ⟧ᴰᴵ)
                                  (sym (tF-coh (F Once.Type.⊗ G))) z)))
              (push-×fam (λ C → ⟦ translateF Carrier Carrier F ⟧SF C)
                         (λ C → ⟦ translateF Carrier Carrier G ⟧SF C)
                         (sym (cohᴰ A)) x y))
 (trans (cong (λ z → OUT (out-layer-gen (F Once.Type.⊗ G) (wf-Prod wfA wfB) A z))
              (pushS⊗⁻ (tF-coh F) (tF-coh G) _ _))
 (trans (cong OUT (out-layer-gen-⊗ F G wfA wfB A _ _))
 (trans (cong (subst id (cohᴰ (⟦ F Once.Type.⊗ G ⟧T A)))
              (push-*ᴵ⁻ (⌊⟧T-commute F A) (⌊⟧T-commute G A) _ _))
 (trans (push× (cohᴰ (⟦ F ⟧T A)) (cohᴰ (⟦ G ⟧T A)) _ _)
        (cong₂ _,_ (νout-erase-D F wfA A x) (νout-erase-D G wfB A y))))))
  where
    OUT : ⟦ IT.⟦ eraseF (F Once.Type.⊗ G) ⟧TI ⌊ A ⌋ ⟧ᴰᴵ → ⟦ ⟦ F Once.Type.⊗ G ⟧T A ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F Once.Type.⊗ G ⟧T A))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute (F Once.Type.⊗ G) A)) z)

-- The RESULT half, at the concrete carrier `ν-type F`.
--
-- plan 0.98: this was "the two VALUES agree at budget `n`". Forcing a ν may
-- stop — a halting coalgebra produces no layer at all — so neither side has a
-- value to name, and the honest statement is that the two RESULTS agree. Both
-- sides are a `mapRes` of the forced suspension's own result, so the proof is
-- the old pointwise chain run under `mapRes-cong`, with `mapRes-∘` fusing the
-- transports that used to be applied one at a time. The budget index is gone:
-- only the trace ever depended on it.
out-coh : ∀ (F : Functor) (wfF : WellFormedF F) (v : ⟦ ν-type F ⟧ᴰ)
  → mapRes (λ z → subst id (cohᴰ (⟦ F ⟧T (ν-type F)))
                    (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute F (ν-type F))) z))
      (T.resT (evalᴰ fmt (IR.Out (wf-⌊⌋ wfF))
                (subst id (sym (cohᴰ (ν-type F))) v)))
    ≡ T.resT (out-sem wfF v)
out-coh F wfF v =
  trans (mapRes-∘ OUT (out-layer-gen F wfF (ν-type F))
          (T.resT (forceᵈ (subst id (sym (cohᴰ (ν-type F))) v))))
  (trans (cong (mapRes (λ ℓ → OUT (out-layer-gen F wfF (ν-type F) ℓ)))
               (force-subst-res (tF-coh F) v))
  (trans (mapRes-∘ (λ ℓ → OUT (out-layer-gen F wfF (ν-type F) ℓ))
                   (subst (λ H → ⟦ H ⟧SF (νᵈ H)) (sym (tF-coh F)))
                   (T.resT (forceᵈ v)))
         (mapRes-cong
            -- the old `out-coh` body, now the POINTWISE step: the diagonal
            -- transport `force-subst-res` leaves is split (`subst-diag-ν⁻`)
            -- into the carrier-then-functor form the carrier-generic lemma is
            -- stated in, and `νout-erase-D` closes it.
            (λ ℓ → trans (cong (λ z → OUT (out-layer-gen F wfF (ν-type F) z))
                               (subst-diag-ν⁻ (tF-coh F) ℓ))
                         (νout-erase-D F wfF (ν-type F) ℓ))
            (T.resT (forceᵈ v)))))
  where
    OUT : ⟦ IT.⟦ eraseF F ⟧TI ⌊ ν-type F ⌋ ⟧ᴰᴵ → ⟦ ⟦ F ⟧T (ν-type F) ⟧ᴰ
    OUT z = subst id (cohᴰ (⟦ F ⟧T (ν-type F)))
              (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute F (ν-type F))) z)

-- plan 0.98: an equation between the two RESULTS, with no budget. The old
-- statement (`valueT … n ≡ valueT … n`) cannot even be written now — `valueT`
-- demands a witness that the computation returned, and for a forced ν there is
-- none to give.
out-value : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ν-type F ⟧ᴰ)
  → T.resT (liftFn fmt {ν-type F} {⟦ F ⟧T (ν-type F)} (Out-ir wfF) v)
    ≡ T.resT (out-sem wfF v)
out-value {F} wfF v =
  trans (subst-T-resT (cohᴰ (⟦ F ⟧T (ν-type F)))
          (evalᴰ fmt (Out-ir wfF) (subst id (sym (cohᴰ (ν-type F))) v)))
  (trans (cong (λ hh → mapRes (subst id (cohᴰ (⟦ F ⟧T (ν-type F)))) (T.resT hh))
            (evalᴰ-subst-cod (sym (⌊⟧T-commute F (ν-type F))) (IR.Out (wf-⌊⌋ wfF))
              (subst id (sym (cohᴰ (ν-type F))) v)))
  (trans (cong (mapRes (subst id (cohᴰ (⟦ F ⟧T (ν-type F)))))
            (subst-TI-resT (sym (⌊⟧T-commute F (ν-type F)))
              (evalᴰ fmt (IR.Out (wf-⌊⌋ wfF)) (subst id (sym (cohᴰ (ν-type F))) v))))
  (trans (mapRes-∘ (subst id (cohᴰ (⟦ F ⟧T (ν-type F))))
                   (subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute F (ν-type F))))
                   (T.resT (evalᴰ fmt (IR.Out (wf-⌊⌋ wfF))
                             (subst id (sym (cohᴰ (ν-type F))) v))))
         (out-coh F wfF v))))

------------------------------------------------------------------------
-- The bridge's two halves, packaged
------------------------------------------------------------------------

-- `RelV` at a LAYER is structural, not `≡` — so even though both sides of the
-- bridge force the same value, the relation has to be rebuilt from it. At a
-- polynomial functor the leaves are base types (`base-refl`) and `Id`
-- positions (the carrier's own reflexivity, which at a ν is `refl`), so this
-- is a plain structural induction — no funext, and no arrow case, because
-- `IsBaseType` has none.
layer-refl : ∀ {A : Type} (G : Functor) (wfG : WellFormedF G)
             (rA : (x : ⟦ A ⟧ᴰ) → RelV A x x)
             (x : ⟦ ⟦ G ⟧T A ⟧ᴰ) → RelV (⟦ G ⟧T A) x x
layer-refl (Once.Type.K B) (wf-K ib) rA x = base-refl ib x
layer-refl Once.Type.Id    wf-Id     rA x = rA x
layer-refl (F Once.Type.⊕ G) (wf-Sum a b) rA (inj₁ x) = layer-refl F a rA x
layer-refl (F Once.Type.⊕ G) (wf-Sum a b) rA (inj₂ y) = layer-refl G b rA y
layer-refl (F Once.Type.⊗ G) (wf-Prod a b) rA (x , y) =
  layer-refl F a rA x , layer-refl G b rA y

-- D201: the DUAL of `AnaBridge.in-rel`, and the relational content that
-- `RelV (ν-type F) = _≡_` used to hide.
--
-- `out-sem` forces and then coerces, so relating two forces means pushing a
-- functor-lifted BISIMILARITY out through `coerce-ν-out` / `coerce-functor⁻¹-D`
-- — structurally, exactly as `in-rel` pushes one in. At a `K` position the
-- lifted relation is already an equality and the carrier is a base type
-- (`base-refl`); at an `Id` position it is bisimilarity, which is precisely
-- what `RelV` at a ν now is, so that clause is the identity.
out-rel : ∀ {A : Type} {G : Functor} (wf : WellFormedF G)
            {x y : ⟦ translateF Carrier Carrier G ⟧SF ⟦ A ⟧ᴰ}
        → ⟦ translateF Carrier Carrier G ⟧SF-rel (RelV A) x y
        → RelV (⟦ G ⟧T A)
            (coerce-functor⁻¹-D G A (coerce-ν-out wf ⟦ A ⟧ᴰ x))
            (coerce-functor⁻¹-D G A (coerce-ν-out wf ⟦ A ⟧ᴰ y))
out-rel (wf-K ib) rel rewrite rel = base-refl ib _
out-rel wf-Id     rel = rel
out-rel (wf-Sum wfF wfG) {x = inj₁ _} {y = inj₁ _} rel = out-rel wfF rel
out-rel (wf-Sum wfF wfG) {x = inj₂ _} {y = inj₂ _} rel = out-rel wfG rel
out-rel (wf-Sum wfF wfG) {x = inj₁ _} {y = inj₂ _} rel = ⊥-elim rel
out-rel (wf-Sum wfF wfG) {x = inj₂ _} {y = inj₁ _} rel = ⊥-elim rel
out-rel (wf-Prod wfF wfG) {x = _ , _} {y = _ , _} (rF , rG) =
  out-rel wfF rF , out-rel wfG rG

-- plan 0.98: reflexivity of the RESULT relation. A stopped force is related to
-- itself with nothing to relate; a returning one by the carrier's own
-- reflexivity. The split is forced: the old statement named a value on both
-- sides and so asserted that forcing produced one.
res-rel-refl : ∀ {X : Set} {R : X → X → Set} → (∀ x → R x x)
             → (r : Res X) → Res-rel R r r
res-rel-refl rr stopped     = tt
res-rel-refl rr (returns x) = rr x

-- The two halves, in the order `RelT` wants them.
liftFn-Out-pair : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ν-type F ⟧ᴰ) (n : ℕ)
-- Stated in the order `RelT` wants: DIRECT meaning first, IR second. `RelV` is
-- not symmetric (at an arrow it is a Π over related inputs), so the order is
-- not a cosmetic choice and `sym` is not available to fix it afterwards.
--
-- plan 0.98: the second component is `Res-rel`, matching `RelT`'s own shape —
-- the stop channel and the value channel were always one fact — and it no
-- longer mentions the budget, because the result does not depend on it.
  → (projTrace (out-sem wfF v) n
      ≡ projTrace (liftFn fmt {ν-type F} {⟦ F ⟧T (ν-type F)} (Out-ir wfF) v) n)
  × Res-rel (RelV (⟦ F ⟧T (ν-type F)))
      (T.resT (out-sem wfF v))
      (T.resT (liftFn fmt {ν-type F} {⟦ F ⟧T (ν-type F)} (Out-ir wfF) v))
liftFn-Out-pair {F} wfF v n =
    sym (out-trace wfF v n)
  , subst (λ z → Res-rel (RelV (⟦ F ⟧T (ν-type F))) (T.resT (out-sem wfF v)) z)
          (sym (out-value wfF v))
          -- D201: the carrier here is `ν-type F`, where the observational
          -- relation is BISIMILARITY — so the carrier's reflexivity is the
          -- coinductive `∼ᵈ-refl`, not `refl`.
          (res-rel-refl (layer-refl F wfF (λ z → ∼ᵈ-refl z))
                        (T.resT (out-sem wfF v)))
