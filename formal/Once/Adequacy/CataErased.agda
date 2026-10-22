-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CataErased
--
-- Plan 0.52 M2: the FUNCTOR-TRANSPORT lemma isolating the erasure round-trip
-- for the `Cata` recursion scheme. After M2 the IR's `Cata` folds the ERASED
-- functor `⌈eraseF F⌉F` at carrier `⟦⌊A⌋⟧ᴰᴵ` (`evalᴰ (Cata …)` via `wf-⌈⌉`),
-- while the surface/meaning fold runs over `F` at `⟦A⟧ᴰ`. This module proves
-- they are related (plan 0.119 D5: `RelS (RelD A)`, runs compared step for
-- step) once bridged by `liftFn` (grade-blind `cohᴰ` transport) and the
-- SET-level functor round-trip `tF-coh : translateF ⌈eraseF F⌉F ≡ translateF F`:
-- an IR algebra related to a semantic one folds every value to related runs
-- (`cata-erased-rel`).
--
-- Own module (minimal, distinct-suffix `⟦_⟧` imports) mirroring `CataFold`/
-- `CataRel`/`CataBridge`, to keep the transport proof clear of `⟦_⟧`-mixfix soup.
------------------------------------------------------------------------

open import Once.Spec.Type using (b-*; b-+)
open import Once.Spec.Numerics using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.CataErased (fmt : TargetNum) (ρ : CallEnv) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst-subst-sym; subst-sym-subst)

open import Once.Internal.Polynomial using (SFunctor; SK; _S⊕_; _S⊗_; μS; cataS; ⟦_⟧SF)
open import Once.Internal.Trace using (fmapT)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; embed; seqF∞)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelS-bind; relS-ret)
open import Once.Denotation.ValueRel using (RelD; SRel; RelS-mono; RelS-fmap; RelS-substˡ; cataS-rel)
open import Once.Denotation.ValueRel using () renaming (base-refl to base-reflᴰ)
open import Once.IRTy using (IRTy; IRFunctor; ⌊_⌋; ⌈_⌉; ⌈_⌉F; ⟦_⟧TI; ⌈⟧TI-commute)
open import Once.Denotation.DenotTrace
  using (evalᴰ; cata-ev-algᴰ)
open import Once.Denotation.Meaning using (cata-ev-algᴰ-D; cata-sem)
open import Once.Semantics.Machine
  using (⟦_⟧F; coerce-μ-out; tF-coh)
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Type using (Type)
open import Once.Internal.Type using (Functor; ⟦_⟧T; μ-type)
open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Internal.Type.WellFormed using (WellFormedF; wf-Sum; wf-Prod; IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum)
open import Once.Internal.FunctorMeaning using (translateF; ⟦_,_⟧-base)
open import Once.Denotation.DenotTrace using (liftFn; sigOpT; module CallEnv)
open CallEnv using (ffiE)
open import Once.Denotation.ValueDomain using (injectᵇ; forgetᵇ; ⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; cohᴰ; coerce-functor⁻¹-D)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (conB; baseA)
open import Once.IRTy using (eraseF; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉; base-⌊⌋; base-⌈⌉)
open import Once.Internal.Value Carrier Carrier using (coerce-base-to-full)
open import Once.Semantics.ValueIR Carrier Carrier using (base-coh)
open import Once.Postulates using (extensionality)
open import Data.Sum using (_⊎_)
import Once.Internal.Type as TT
import Once.Spec.Type as TT
import Once.Type as TT
import Once.IRTy as II
import Once.IR as IR

------------------------------------------------------------------------
-- Generic transport helpers (both by matching the equation to `refl`).
------------------------------------------------------------------------

subst-cong-μS : ∀ {G₁ G₂ : SFunctor} (eq : G₁ ≡ G₂) (x : μS G₁)
  → subst (λ z → z) (cong μS eq) x ≡ subst μS eq x
subst-cong-μS refl x = refl

-- A `cataS` fold over `G₂` equals the fold over an equal functor `G₁`, with the
-- algebra pre-composed by the (inverse) functor transport and the seed transported.
cataS-subst-functor : ∀ {G₁ G₂ : SFunctor} {A : Set}
    (eq : G₂ ≡ G₁) (alg : ⟦ G₂ ⟧SF A → A) (x : μS G₂)
  → cataS {G₂} alg x
    ≡ cataS {G₁} (λ y → alg (subst (λ G → ⟦ G ⟧SF A) (sym eq) y)) (subst μS eq x)
cataS-subst-functor refl alg x = refl

-- Naturality of `evalᴰ` under a DOMAIN transport: substituting the source
-- object of an IR morphism is the same as back-transporting its argument.
evalᴰ-subst-dom : ∀ {o₁ o₂ : IRTy} {B : IRTy} (eq : o₁ ≡ o₂)
    (m : IR.IR o₁ B) (z : ⟦ o₂ ⟧ᴰᴵ)
  → evalᴰ fmt ρ (subst (λ o → IR.IR o B) eq m) z ≡ evalᴰ fmt ρ m (subst ⟦_⟧ᴰᴵ (sym eq) z)
evalᴰ-subst-dom refl m z = refl

-- D131: the same naturality with a PAIRED domain — the transport moves only
-- the second component; the environment slot is untouched.
evalᴰ-subst-dom-pair : ∀ {E o₁ o₂ : IRTy} {B : IRTy} (eq : o₁ ≡ o₂)
    (m : IR.IR (E II.* o₁) B) (env : ⟦ E ⟧ᴰᴵ) (z : ⟦ o₂ ⟧ᴰᴵ)
  → evalᴰ fmt ρ (subst (λ o → IR.IR (E II.* o) B) eq m) (env , z)
    ≡ evalᴰ fmt ρ m (env , subst ⟦_⟧ᴰᴵ (sym eq) z)
evalᴰ-subst-dom-pair refl m env z = refl

-- …and the pair transport splits componentwise, so `liftFn` at a paired
-- domain reaches the algebra with the environment already back-transported.
pairᴰ-subst⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A') (b : B')
  → subst (λ z → z) (sym (cong₂ (λ x y → x × y) p q)) (a , b)
    ≡ (subst (λ z → z) (sym p) a , subst (λ z → z) (sym q) b)
pairᴰ-subst⁻ refl refl a b = refl

------------------------------------------------------------------------
-- `subst`-push helpers: a functor transport `sym (cong₂ _S⊕_/_S⊗_ …)` over a
-- `⟦_⟧SF` layer distributes into the injection / projection (all by `refl`).
------------------------------------------------------------------------

subst-S⊕-inj₁ : ∀ {F₁ F₂ G₁ G₂ : SFunctor} {X : Set}
    (p : F₁ ≡ G₁) (q : F₂ ≡ G₂) (a : ⟦ G₁ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊕_ p q)) (inj₁ a)
    ≡ inj₁ (subst (λ H → ⟦ H ⟧SF X) (sym p) a)
subst-S⊕-inj₁ refl refl a = refl

subst-S⊕-inj₂ : ∀ {F₁ F₂ G₁ G₂ : SFunctor} {X : Set}
    (p : F₁ ≡ G₁) (q : F₂ ≡ G₂) (b : ⟦ G₂ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊕_ p q)) (inj₂ b)
    ≡ inj₂ (subst (λ H → ⟦ H ⟧SF X) (sym q) b)
subst-S⊕-inj₂ refl refl b = refl

subst-S⊗ : ∀ {F₁ F₂ G₁ G₂ : SFunctor} {X : Set}
    (p : F₁ ≡ G₁) (q : F₂ ≡ G₂) (a : ⟦ G₁ ⟧SF X) (b : ⟦ G₂ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊗_ p q)) (a , b)
    ≡ (subst (λ H → ⟦ H ⟧SF X) (sym p) a , subst (λ H → ⟦ H ⟧SF X) (sym q) b)
subst-S⊗ refl refl a b = refl

------------------------------------------------------------------------
-- Value-level `subst`-push helpers for `layer-z` (all `refl`): a functor
-- transport distributes into `inj₁/inj₂/pair` through each interpretation.
------------------------------------------------------------------------

pushᴰᴵ-+₁ : ∀ {A B A' B' : IRTy} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ II._+_ p q)) (inj₁ a) ≡ inj₁ (subst ⟦_⟧ᴰᴵ (sym p) a)
pushᴰᴵ-+₁ refl refl a = refl

pushᴰᴵ-+₂ : ∀ {A B A' B' : IRTy} (p : A ≡ A') (q : B ≡ B') (b : ⟦ B' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ II._+_ p q)) (inj₂ b) ≡ inj₂ (subst ⟦_⟧ᴰᴵ (sym q) b)
pushᴰᴵ-+₂ refl refl b = refl

pushᴰᴵ-* : ∀ {A B A' B' : IRTy} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰᴵ) (b : ⟦ B' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ II._*_ p q)) (a , b)
    ≡ (subst ⟦_⟧ᴰᴵ (sym p) a , subst ⟦_⟧ᴰᴵ (sym q) b)
pushᴰᴵ-* refl refl a b = refl

pushᴰ-+₁ : ∀ {A B A' B' : Type} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰ)
  → subst ⟦_⟧ᴰ (sym (cong₂ TT._+_ p q)) (inj₁ a) ≡ inj₁ (subst ⟦_⟧ᴰ (sym p) a)
pushᴰ-+₁ refl refl a = refl

pushᴰ-+₂ : ∀ {A B A' B' : Type} (p : A ≡ A') (q : B ≡ B') (b : ⟦ B' ⟧ᴰ)
  → subst ⟦_⟧ᴰ (sym (cong₂ TT._+_ p q)) (inj₂ b) ≡ inj₂ (subst ⟦_⟧ᴰ (sym q) b)
pushᴰ-+₂ refl refl b = refl

pushᴰ-* : ∀ {A B A' B' : Type} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰ) (b : ⟦ B' ⟧ᴰ)
  → subst ⟦_⟧ᴰ (sym (cong₂ TT._*_ p q)) (a , b)
    ≡ (subst ⟦_⟧ᴰ (sym p) a , subst ⟦_⟧ᴰ (sym q) b)
pushᴰ-* refl refl a b = refl

push-⊎₁ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A')
  → subst (λ z → z) (sym (cong₂ _⊎_ p q)) (inj₁ a) ≡ inj₁ (subst (λ z → z) (sym p) a)
push-⊎₁ refl refl a = refl

push-⊎₂ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B')
  → subst (λ z → z) (sym (cong₂ _⊎_ p q)) (inj₂ b) ≡ inj₂ (subst (λ z → z) (sym q) b)
push-⊎₂ refl refl b = refl

push-× : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A') (b : B')
  → subst (λ z → z) (sym (cong₂ _×_ p q)) (a , b)
    ≡ (subst (λ z → z) (sym p) a , subst (λ z → z) (sym q) b)
push-× refl refl a b = refl

------------------------------------------------------------------------
-- `subst-SK` push + `base-z`: the K-node base-constant coherence (induction on
-- `IsBaseType`; atomic bases `refl`, Prod/Sum push+recurse). Discharges the K
-- case of `layer-z`.
------------------------------------------------------------------------

subst-SK : ∀ {S₁ S₂ X : Set} (e : S₁ ≡ S₂) (a : S₂)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong SK e)) a ≡ subst (λ z → z) (sym e) a
subst-SK refl a = refl

-- The K-node base-constant coherence (induction on `IsBaseType`): master's
-- `base-z`, at `injectᵇ` (plan 0.113 A2; D258 removed Str/Buffer).
base-z : ∀ {A} (ib : IsBaseType A) (y : ⟦ Carrier , Carrier ⟧-base A)
  → injectᵇ (base-⌈⌉ (base-⌊⌋ ib)) (coerce-base-to-full (base-⌈⌉ (base-⌊⌋ ib)) (subst (λ z → z) (sym (base-coh A)) y))
    ≡ subst (λ z → z) (sym (cohᴰ A)) (injectᵇ ib (coerce-base-to-full ib y))
base-z base-Unit   y = refl
base-z base-Void   ()
base-z base-Int    y = refl
base-z base-Float  y = refl
base-z (b-* {A = A} {B = B} pA pB) (a , b)
  rewrite push-× (base-coh A) (base-coh B) a b
        | push-× (cohᴰ A) (cohᴰ B) (injectᵇ pA (coerce-base-to-full pA a)) (injectᵇ pB (coerce-base-to-full pB b))
  = cong₂ _,_ (base-z pA a) (base-z pB b)
base-z (b-+ {A = A} {B = B} pA pB) (inj₁ a)
  rewrite push-⊎₁ (base-coh A) (base-coh B) a
        | push-⊎₁ (cohᴰ A) (cohᴰ B) (injectᵇ pA (coerce-base-to-full pA a))
  = cong inj₁ (base-z pA a)
base-z (b-+ {A = A} {B = B} pA pB) (inj₂ b)
  rewrite push-⊎₂ (base-coh A) (base-coh B) b
        | push-⊎₂ (cohᴰ A) (cohᴰ B) (injectᵇ pB (coerce-base-to-full pB b))
  = cong inj₂ (base-z pB b)

-- Forward pushes (the transports `cohᴰ` performs at a sum and a product).
push-⊎₁⁺ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A)
  → subst (λ z → z) (cong₂ _⊎_ p q) (inj₁ a) ≡ inj₁ (subst (λ z → z) p a)
push-⊎₁⁺ refl refl a = refl

push-⊎₂⁺ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B)
  → subst (λ z → z) (cong₂ _⊎_ p q) (inj₂ b) ≡ inj₂ (subst (λ z → z) q b)
push-⊎₂⁺ refl refl b = refl

push-×⁺ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A) (b : B)
  → subst (λ z → z) (cong₂ _×_ p q) (a , b) ≡ (subst (λ z → z) p a , subst (λ z → z) q b)
push-×⁺ refl refl a b = refl

-- A run transported along an equation of carriers, read back.
RelS-substˡ⁻ : ∀ {X X′ Y} {R : X′ → Y → Set} (E : X ≡ X′) {m : T∞ X} {n : T∞ Y}
             → RelS R (subst T∞ E m) n → RelS (λ a b → R (subst (λ Z → Z) E a) b) m n
RelS-substˡ⁻ refl h = h

module _ {A' : Type} where

  -- The fold's carrier is a run; an IR run and a meaning run are related when
  -- they are, step for step, with the IR value read across `cohᴰ`.
  RelC : T∞ ⟦ ⌊ A' ⌋ ⟧ᴰᴵ → T∞ ⟦ A' ⟧ᴰ → Set
  RelC = RelS (λ l r → RelD A' (subst (λ z → z) (cohᴰ A') l) r)

  -- A layer of the erased functor, read back into `⟦ G ⟧T A'`'s IR domain.
  L : ∀ {G : Functor} → WellFormedF G → ⟦ ⌈ eraseF G ⌉F ⟧F ⟦ ⌊ A' ⌋ ⟧ᴰᴵ → ⟦ ⌊ ⟦ G ⟧T A' ⌋ ⟧ᴰᴵ
  L {G} wfG l =
    subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute G A'))
      (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF G) ⌊ A' ⌋))
        (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l))

  -- An IR layer and a meaning layer are related when their values are.
  LayerRel : ∀ {G : Functor} → WellFormedF G → ⟦ ⌈ eraseF G ⌉F ⟧F ⟦ ⌊ A' ⌋ ⟧ᴰᴵ → ⟦ G ⟧F ⟦ A' ⟧ᴰ → Set
  LayerRel {G} wfG l r = RelD (⟦ G ⟧T A') (subst (λ z → z) (cohᴰ (⟦ G ⟧T A')) (L wfG l)) (coerce-functor⁻¹-D wfG A' r)

  private
    ≡ˡᴰ : ∀ X {u u′ w : ⟦ X ⟧ᴰ} → u ≡ u′ → RelD X u′ w → RelD X u w
    ≡ˡᴰ X refl r = r

  sum₁-step : ∀ {Fa Gb} (wfF : WellFormedF Fa) (wfG : WellFormedF Gb) l r
            → LayerRel wfF l r → LayerRel (wf-Sum wfF wfG) (inj₁ l) (inj₁ r)
  sum₁-step {Fa} {Gb} wfF wfG l r e =
    ≡ˡᴰ (⟦ Fa ⟧T A' TT.+ ⟦ Gb ⟧T A')
      (trans (cong (subst (λ z → z) (cohᴰ (⟦ Fa ⟧T A' TT.+ ⟦ Gb ⟧T A')))
                   (trans (cong (subst ⟦_⟧ᴰᴵ (sym (cong₂ II._+_ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A'))))
                                (pushᴰ-+₁ (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                                          (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ l)))
                          (pushᴰᴵ-+₁ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A') _)))
             (push-⊎₁⁺ (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A')) _))
      e

  sum₂-step : ∀ {Fa Gb} (wfF : WellFormedF Fa) (wfG : WellFormedF Gb) l r
            → LayerRel wfG l r → LayerRel (wf-Sum wfF wfG) (inj₂ l) (inj₂ r)
  sum₂-step {Fa} {Gb} wfF wfG l r e =
    ≡ˡᴰ (⟦ Fa ⟧T A' TT.+ ⟦ Gb ⟧T A')
      (trans (cong (subst (λ z → z) (cohᴰ (⟦ Fa ⟧T A' TT.+ ⟦ Gb ⟧T A')))
                   (trans (cong (subst ⟦_⟧ᴰᴵ (sym (cong₂ II._+_ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A'))))
                                (pushᴰ-+₂ (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                                          (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l)))
                          (pushᴰᴵ-+₂ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A') _)))
             (push-⊎₂⁺ (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A')) _))
      e

  prod-step : ∀ {Fa Gb} (wfF : WellFormedF Fa) (wfG : WellFormedF Gb) l r l′ r′
            → LayerRel wfF l r → LayerRel wfG l′ r′ → LayerRel (wf-Prod wfF wfG) (l , l′) (r , r′)
  prod-step {Fa} {Gb} wfF wfG l r l′ r′ e e′ =
    ≡ˡᴰ (⟦ Fa ⟧T A' TT.* ⟦ Gb ⟧T A')
      (trans (cong (subst (λ z → z) (cohᴰ (⟦ Fa ⟧T A' TT.* ⟦ Gb ⟧T A')))
                   (trans (cong (subst ⟦_⟧ᴰᴵ (sym (cong₂ II._*_ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A'))))
                                (pushᴰ-* (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                                         (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ l)
                                         (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l′)))
                          (pushᴰᴵ-* (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A') _ _)))
             (push-×⁺ (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A')) _ _))
      (e , e′)

  -- A constant layer: the IR value is the meaning's, read back (`base-z`).
  base-step : ∀ {B} (ib : IsBaseType B) (y : ⟦ Carrier , Carrier ⟧-base B)
            → RelD B (subst (λ z → z) (cohᴰ B)
                        (injectᵇ (base-⌈⌉ (base-⌊⌋ ib)) (coerce-base-to-full (base-⌈⌉ (base-⌊⌋ ib)) (subst (λ z → z) (sym (base-coh B)) y))))
                     (injectᵇ ib (coerce-base-to-full ib y))
  base-step {B} ib y =
    ≡ˡᴰ B (trans (cong (subst (λ z → z) (cohᴰ B)) (base-z ib y)) (subst-subst-sym {P = λ z → z} (cohᴰ B)))
          (base-reflᴰ ib _)

  layer-rel : ∀ {G} (wfG : WellFormedF G)
      {y₁ : ⟦ translateF Carrier Carrier G ⟧SF (T∞ ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)}
      {y₂ : ⟦ translateF Carrier Carrier G ⟧SF (T∞ ⟦ A' ⟧ᴰ)}
    → SRel RelC (translateF Carrier Carrier G) y₁ y₂
    → RelS (LayerRel wfG)
        (seqF∞ ⌈ eraseF G ⌉F
          (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _
            (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh G)) y₁)))
        (seqF∞ G (coerce-μ-out wfG _ y₂))
  layer-rel {TT.K B} (wf-K ib) {y} {.y} refl
    rewrite subst-SK {X = T∞ ⟦ ⌊ A' ⌋ ⟧ᴰᴵ} (base-coh B) y = relS-ret (base-step ib y)
  layer-rel wf-Id rc = rc
  layer-rel (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₁ x₁} {inj₁ x₂} rsf
    rewrite subst-S⊕-inj₁ (tF-coh Fa) (tF-coh Gb) x₁ =
    RelS-fmap (layer-rel wfF rsf) (λ {l} {r} → sum₁-step wfF wfG l r)
  layer-rel (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₂ y₁} {inj₂ y₂} rsf
    rewrite subst-S⊕-inj₂ (tF-coh Fa) (tF-coh Gb) y₁ =
    RelS-fmap (layer-rel wfG rsf) (λ {l} {r} → sum₂-step wfF wfG l r)
  layer-rel (wf-Sum wfF wfG) {inj₁ _} {inj₂ _} ()
  layer-rel (wf-Sum wfF wfG) {inj₂ _} {inj₁ _} ()
  layer-rel (wf-Prod {F = Fa} {G = Gb} wfF wfG) {x₁ , z₁} {x₂ , z₂} (rf , rg)
    rewrite subst-S⊗ (tF-coh Fa) (tF-coh Gb) x₁ z₁ =
    RelS-bind (layer-rel wfF rf) λ {l} {r} e →
    RelS-bind (layer-rel wfG rg) λ {l′} {r′} e′ →
    relS-ret (prod-step wfF wfG l r l′ r′ e e′)

  -- THE ERASED FOLD. An IR algebra related to a semantic one folds every value
  -- to a run related to the meaning's fold.
  cata-erased-rel : ∀ {F : Functor} {Eˢ : Type} (wfF : WellFormedF F)
      (mir : IR.IR (⌊ Eˢ ⌋ II.* ⌊ ⟦ F ⟧T A' ⌋) ⌊ A' ⌋) (env : ⟦ Eˢ ⟧ᴰ)
      (g : ⟦ ⟦ F ⟧T A' ⟧ᴰ → T∞ ⟦ A' ⟧ᴰ)
    → (∀ {z z′} → RelD (⟦ F ⟧T A') z z′ → RelS (RelD A') (liftFn fmt ρ {Eˢ TT.* ⟦ F ⟧T A'} {A'} mir (env , z)) (g z′))
    → ∀ (w : ⟦ μ-type F ⟧ᴰ)
    → RelS (RelD A') (liftFn fmt ρ {Eˢ TT.* μ-type F} {A'} (IR.Cata (wf-⌊⌋ wfF)
                        (subst (λ o → IR.IR (⌊ Eˢ ⌋ II.* o) ⌊ A' ⌋) (⌊⟧T-commute F A') mir))
                        (env , w))
                     (cata-sem wfF g w)
  cata-erased-rel {F} {Eˢ} wfF mir env g hg w =
    ≡ˢ (trans (cong (λ W → subst T∞ (cohᴰ A') (evalᴰ fmt ρ (IR.Cata (wf-⌊⌋ wfF) mir') W))
                    (pairᴰ-subst⁻ (cohᴰ Eˢ) (cohᴰ (μ-type F)) env w))
              (cong (subst T∞ (cohᴰ A')) Lr≡))
       (RelS-substˡ (cohᴰ A') (cataS-rel {R = RelC} algR w))
    where
      ≡ˢ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y} → m ≡ m′ → RelS R m′ n → RelS R m n
      ≡ˢ refl h = h

      mir' : IR.IR (⌊ Eˢ ⌋ II.* ⟦ eraseF F ⟧TI ⌊ A' ⌋) ⌊ A' ⌋
      mir' = subst (λ o → IR.IR (⌊ Eˢ ⌋ II.* o) ⌊ A' ⌋) (⌊⟧T-commute F A') mir

      env₀ = subst (λ t → t) (sym (cohᴰ Eˢ)) env

      w' : ⟦ ⌊ μ-type F ⌋ ⟧ᴰᴵ
      w' = subst (λ z → z) (sym (cohᴰ (μ-type F))) w

      seed-eq : subst μS (tF-coh F) w' ≡ w
      seed-eq = trans (sym (subst-cong-μS (tF-coh F) w'))
                      (subst-subst-sym {P = λ z → z} (cong μS (tF-coh F)))

      algL : ⟦ translateF Carrier Carrier (⌈ eraseF F ⌉F) ⟧SF (T∞ ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → T∞ ⟦ ⌊ A' ⌋ ⟧ᴰᴵ
      algL y = cata-ev-algᴰ fmt ρ (wf-⌊⌋ wfF) mir' env₀ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ y)

      algL' : ⟦ translateF Carrier Carrier F ⟧SF (T∞ ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → T∞ ⟦ ⌊ A' ⌋ ⟧ᴰᴵ
      algL' y = algL (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh F)) y)

      Lr≡ : evalᴰ fmt ρ (IR.Cata (wf-⌊⌋ wfF) mir') (env₀ , w') ≡ cataS {translateF Carrier Carrier F} algL' w
      Lr≡ = trans (cataS-subst-functor (tF-coh F) algL w')
                  (cong (cataS {translateF Carrier Carrier F} algL') seed-eq)

      -- the algebra's step, at a related layer
      step : ∀ x y → LayerRel wfF x y
           → RelC (evalᴰ fmt ρ mir' (env₀ , subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF F) ⌊ A' ⌋))
                                              (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ x)))
                  (g (coerce-functor⁻¹-D wfF A' y))
      step x y lr =
        ≡ˢ (evalᴰ-subst-dom-pair (⌊⟧T-commute F A') mir env₀ _)
           (RelS-substˡ⁻ (cohᴰ A')
             (≡ˢ (cong (λ W → subst T∞ (cohᴰ A') (evalᴰ fmt ρ mir W))
                       (sym (trans (pairᴰ-subst⁻ (cohᴰ Eˢ) (cohᴰ (⟦ F ⟧T A')) env _)
                                   (cong (env₀ ,_) (subst-sym-subst {P = λ z → z} (cohᴰ (⟦ F ⟧T A')))))))
                 (hg lr)))

      algR : ∀ {y₁ y₂} → SRel RelC (translateF Carrier Carrier F) y₁ y₂
           → RelC (algL' y₁) (cata-ev-algᴰ-D wfF g (coerce-μ-out wfF _ y₂))
      algR rsf = RelS-bind (layer-rel wfF rsf) (λ {x} {y} lr → step x y lr)

-- A SigOp's lifted meaning is its contract's computation at the first-order
-- argument, read into the value domain (plan 0.105: no emission rule, no
-- `semM` — the tree node IS the event).
liftFn-SigOp : ∀ {A B : Type} (info : SigOpInfo A B)
  → liftFn fmt ρ {A} {B} (IR.SigOp info)
    ≡ (λ arg → embed (fmapT (injectᵇ (conB info)) (sigOpT fmt (ffiE ρ) info (forgetᵇ (baseA info) arg))))
liftFn-SigOp {A} {B} info = extensionality λ arg →
  trans (cancel (cohᴰ B) (injectᵇ (conB info))
           (sigOpT fmt (ffiE ρ) info (forgetᵇ (baseA info)
              (subst (λ z → z) (cohᴰ A) (subst (λ z → z) (sym (cohᴰ A)) arg)))))
        (cong (λ w → embed (fmapT (injectᵇ (conB info)) (sigOpT fmt (ffiE ρ) info (forgetᵇ (baseA info) w))))
              (subst-subst-sym {P = λ z → z} (cohᴰ A)))
  where
    -- A transport that undoes the one inside a map cancels it.
    cancel : ∀ {X Y Z : Set} (eq : X ≡ Y) (f : Z → Y) m
           → subst T∞ eq (embed (fmapT (λ v → subst (λ z → z) (sym eq) (f v)) m)) ≡ embed (fmapT f m)
    cancel refl f m = refl
