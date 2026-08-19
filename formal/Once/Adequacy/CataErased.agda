-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CataErased
--
-- Plan 0.52 M2: the FUNCTOR-TRANSPORT lemma isolating the erasure round-trip
-- for the `Cata` recursion scheme. After M2 the IR's `Cata` folds the ERASED
-- functor `⌈eraseF F⌉F` at carrier `⟦⌊A⌋⟧ᴰᴵ` (`evalᴰ (Cata …)` via `wf-⌈⌉`),
-- while the surface/meaning fold runs over `F` at `⟦A⟧ᴰ`. This module proves
-- they coincide once bridged by `liftFn` (grade-blind `cohᴰ` transport) and the
-- SET-level functor round-trip `tF-coh : translateF ⌈eraseF F⌉F ≡ translateF F`.
--
-- The single export `evalᴰ-Cata-erased` lets the relational fold congruences
-- (`CataBridge.cata-bridge`, `CataFold.cata-fold-eq`) stay at the SAME functor
-- `F` and SAME carrier `⟦A⟧ᴰ` — their original proofs are reused unchanged,
-- with this lemma discharging the erasure round-trip up front.
--
-- Own module (minimal, distinct-suffix `⟦_⟧` imports) mirroring `CataFold`/
-- `CataRel`/`CataBridge`, to keep the transport proof clear of `⟦_⟧`-mixfix soup.
------------------------------------------------------------------------

module Once.Adequacy.CataErased where

open import Data.Nat using (ℕ)
open import Data.List using (List; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst-subst-sym; subst-sym-subst)

open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; μS; cataS; ⟦_⟧SF)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT)
open import Once.IRTy using (IRTy; IRFunctor; ⌊_⌋; ⌈_⌉; ⌈_⌉F; ⟦_⟧TI; ⌈⟧TI-commute)
open import Once.Denotation.DenotTrace
  using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; evalᴰ; cata-ev-algᴰ; coerce-functor⁻¹-D)
open import Once.Denotation.Meaning using (cata-ev-algᴰ-D; cata-sem)
open import Once.Semantics.Machine
  using (⟦_⟧F; sem-cata; sem-fmap; coerce-μ-out; tF-coh; base-coh; coh)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Type using (Type; Functor; ⟦_⟧T; μ-type)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum)
open import Once.Denotation.DenotTrace using (forget; liftFn; cohᴰ; inject; emit-D)
open import Once.SigOp.Info using (SigOpInfo; semM)
open import Once.Semantics.Machine using (coerce-base-to-full)
open import Once.Functor.Translate using (⟦_,_⟧-base)
open import Once.IRTy.WF using (base-⌈⌉; base-⌊⌋)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.IRTy using (eraseF; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Once.Postulates using (extensionality)
open import Data.Sum using (_⊎_)
import Once.Type as TT
import Once.IRTy as II
import Once.IR as IR

------------------------------------------------------------------------
-- Generic transport helpers (both by matching the equation to `refl`).
------------------------------------------------------------------------

-- Applying a `subst`-transported computation transports its VALUE half only.
subst-T-apply : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (n : ℕ)
  → subst T eq h n ≡ (proj₁ (h n) , subst (λ Z → Z) eq (proj₂ (h n)))
subst-T-apply refl h n = refl

subst-T-projTrace : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (n : ℕ)
  → projTrace (subst T eq h) n ≡ projTrace h n
subst-T-projTrace refl h n = refl

subst-T-valueT : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (n : ℕ)
  → valueT (subst T eq h) n ≡ subst (λ z → z) eq (valueT h n)
subst-T-valueT refl h n = refl

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
  → evalᴰ (subst (λ o → IR.IR o B) eq m) z ≡ evalᴰ m (subst ⟦_⟧ᴰᴵ (sym eq) z)
evalᴰ-subst-dom refl m z = refl

-- The IR-carrier cata trace-algebra is DEFINITIONALLY the Type-carrier one
-- (`cata-ev-algᴰ-D`) over the embedded functor `⌈F⌉F`, fed the algebra
-- `evalᴰ alg` pre-composed with the `⌈⟧TI-commute` re-embedding. Collapses the
-- IR-vs-meaning fold asymmetry so both sides become uniform `cata-sem` folds.
cata-ev-algᴰ-is-D : ∀ {F : IRFunctor} {C : IRTy} (n : ℕ)
    (alg : IR.IR (⟦ F ⟧TI C) C)
    (fc : ⟦ ⌈ F ⌉F ⟧F (List SigOpEvent × ⟦ C ⟧ᴰᴵ))
  → cata-ev-algᴰ {F} {C} n alg fc
    ≡ cata-ev-algᴰ-D {⌈ F ⌉F} {⌈ C ⌉} n
        (λ z → evalᴰ alg (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F C)) z)) fc
cata-ev-algᴰ-is-D n alg fc = refl

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

base-z : ∀ {A} (ib : IsBaseType A) (y : ⟦ Carrier , Carrier ⟧-base A)
  → inject (coerce-base-to-full (base-⌈⌉ (base-⌊⌋ ib)) (subst (λ z → z) (sym (base-coh A)) y))
    ≡ subst (λ z → z) (sym (cohᴰ A)) (inject (coerce-base-to-full ib y))
base-z base-Unit   y = refl
base-z base-Void   ()
base-z base-Int    y = refl
base-z base-Float  y = refl
base-z base-Str    y = refl
base-z base-Buffer y = refl
base-z (base-Prod {A} {B} pA pB) (a , b)
  rewrite push-× (base-coh A) (base-coh B) a b
        | push-× (cohᴰ A) (cohᴰ B) (inject (coerce-base-to-full pA a)) (inject (coerce-base-to-full pB b))
  = cong₂ _,_ (base-z pA a) (base-z pB b)
base-z (base-Sum {A} {B} pA pB) (inj₁ a)
  rewrite push-⊎₁ (base-coh A) (base-coh B) a
        | push-⊎₁ (cohᴰ A) (cohᴰ B) (inject (coerce-base-to-full pA a))
  = cong inj₁ (base-z pA a)
base-z (base-Sum {A} {B} pA pB) (inj₂ b)
  rewrite push-⊎₂ (base-coh A) (base-coh B) b
        | push-⊎₂ (cohᴰ A) (cohᴰ B) (inject (coerce-base-to-full pB b))
  = cong inj₂ (base-z pB b)

------------------------------------------------------------------------
-- The functor-structural layer lemma, fixed at result type `A'`. Two facts:
--   (A) `layer-events`: the per-layer CHILD TRACES coincide across the erasure
--       functor round-trip (given `RelSF`-related layers).
--   (B) `layer-z`: the assembled recursive ARGUMENT coincides after transport.
------------------------------------------------------------------------

module _ {A' : Type} where

  RelC : (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → (List SigOpEvent × ⟦ A' ⟧ᴰ) → Set
  RelC l r = (proj₁ l ≡ proj₁ r) × (subst (λ z → z) (cohᴰ A') (proj₂ l) ≡ proj₂ r)

  layer-events : ∀ {G} (wfG : WellFormedF G)
      {y₁ : ⟦ translateF Carrier Carrier G ⟧SF (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)}
      {y₂ : ⟦ translateF Carrier Carrier G ⟧SF (List SigOpEvent × ⟦ A' ⟧ᴰ)}
    → RelSF (translateF Carrier Carrier G) RelC y₁ y₂
    → events-F ⌈ eraseF G ⌉F proj₁
        (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh G)) y₁))
      ≡ events-F G proj₁ (coerce-μ-out wfG _ y₂)
  layer-events (wf-K ib)       _   = refl
  layer-events wf-Id           rc  = proj₁ rc
  layer-events (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₁ x₁} {inj₁ x₂} rsf
    rewrite subst-S⊕-inj₁ (tF-coh Fa) (tF-coh Gb) x₁ = layer-events wfF {x₁} {x₂} rsf
  layer-events (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₂ y₁} {inj₂ y₂} rsf
    rewrite subst-S⊕-inj₂ (tF-coh Fa) (tF-coh Gb) y₁ = layer-events wfG {y₁} {y₂} rsf
  layer-events (wf-Sum wfF wfG) {inj₁ _} {inj₂ _} ()
  layer-events (wf-Sum wfF wfG) {inj₂ _} {inj₁ _} ()
  layer-events (wf-Prod {F = Fa} {G = Gb} wfF wfG) {x₁ , z₁} {x₂ , z₂} (rf , rg)
    rewrite subst-S⊗ (tF-coh Fa) (tF-coh Gb) x₁ z₁ =
    cong₂ _++_ (layer-events wfF {x₁} {x₂} rf) (layer-events wfG {z₁} {z₂} rg)

  layer-z : ∀ {G} (wfG : WellFormedF G)
      {y₁ : ⟦ translateF Carrier Carrier G ⟧SF (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)}
      {y₂ : ⟦ translateF Carrier Carrier G ⟧SF (List SigOpEvent × ⟦ A' ⟧ᴰ)}
    → RelSF (translateF Carrier Carrier G) RelC y₁ y₂
    → subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute G A'))
        (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF G) ⌊ A' ⌋))
          (coerce-functor⁻¹-D ⌈ eraseF G ⌉F ⌈ ⌊ A' ⌋ ⌉
            (sem-fmap ⌈ eraseF G ⌉F proj₂
              (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh G)) y₁)))))
      ≡ subst (λ z → z) (sym (cohᴰ (⟦ G ⟧T A')))
          (coerce-functor⁻¹-D G A' (sem-fmap G proj₂ (coerce-μ-out wfG _ y₂)))
  layer-z wf-Id rc =
    trans (sym (subst-sym-subst (cohᴰ A')))
          (cong (subst (λ z → z) (sym (cohᴰ A'))) (proj₂ rc))
  layer-z (wf-K ib) {y} {.y} refl =
    trans (cong (λ v → inject (coerce-base-to-full (base-⌈⌉ (base-⌊⌋ ib)) v))
                (subst-SK (base-coh _) y))
          (base-z ib y)
  layer-z (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₁ x₁} {inj₁ x₂} rsf
    rewrite subst-S⊕-inj₁ (tF-coh Fa) (tF-coh Gb) x₁
          | pushᴰ-+₁ (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                     (coerce-functor⁻¹-D ⌈ eraseF Fa ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Fa ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Fa)) x₁))))
          | pushᴰᴵ-+₁ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A')
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋)) (coerce-functor⁻¹-D ⌈ eraseF Fa ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Fa ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Fa)) x₁)))))
          | push-⊎₁ (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A'))
                     (coerce-functor⁻¹-D Fa A' (sem-fmap Fa proj₂ (coerce-μ-out wfF _ x₂)))
    = cong inj₁ (layer-z wfF {x₁} {x₂} rsf)
  layer-z (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₂ y₁} {inj₂ y₂} rsf
    rewrite subst-S⊕-inj₂ (tF-coh Fa) (tF-coh Gb) y₁
          | pushᴰ-+₂ (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                     (coerce-functor⁻¹-D ⌈ eraseF Gb ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Gb ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Gb)) y₁))))
          | pushᴰᴵ-+₂ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A')
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)) (coerce-functor⁻¹-D ⌈ eraseF Gb ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Gb ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Gb)) y₁)))))
          | push-⊎₂ (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A'))
                     (coerce-functor⁻¹-D Gb A' (sem-fmap Gb proj₂ (coerce-μ-out wfG _ y₂)))
    = cong inj₂ (layer-z wfG {y₁} {y₂} rsf)
  layer-z (wf-Sum wfF wfG) {inj₁ _} {inj₂ _} ()
  layer-z (wf-Sum wfF wfG) {inj₂ _} {inj₁ _} ()
  layer-z (wf-Prod {F = Fa} {G = Gb} wfF wfG) {x₁ , z₁} {x₂ , z₂} (rf , rg)
    rewrite subst-S⊗ (tF-coh Fa) (tF-coh Gb) x₁ z₁
          | pushᴰ-* (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                     (coerce-functor⁻¹-D ⌈ eraseF Fa ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Fa ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Fa)) x₁))))
                     (coerce-functor⁻¹-D ⌈ eraseF Gb ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Gb ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Gb)) z₁))))
          | pushᴰᴵ-* (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A')
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋)) (coerce-functor⁻¹-D ⌈ eraseF Fa ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Fa ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Fa)) x₁)))))
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)) (coerce-functor⁻¹-D ⌈ eraseF Gb ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF Gb ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh Gb)) z₁)))))
          | push-× (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A'))
                     (coerce-functor⁻¹-D Fa A' (sem-fmap Fa proj₂ (coerce-μ-out wfF _ x₂)))
                     (coerce-functor⁻¹-D Gb A' (sem-fmap Gb proj₂ (coerce-μ-out wfG _ z₂)))
    = cong₂ _,_ (layer-z wfF {x₁} {x₂} rf) (layer-z wfG {z₁} {z₂} rg)

  ------------------------------------------------------------------------
  -- The functor-transport EQUALITY: the erased `Cata`'s `liftFn`-transported
  -- denotation equals the meaning fold `cata-sem` of the `liftFn`-transported
  -- algebra. Assembled from `cataS-rel` (over the `tF-coh`-unified functor `F`)
  -- with `algR-full` = `layer-events` (traces) + `layer-z` (values, via
  -- `evalᴰ-subst-dom` + `subst-T-apply`).
  ------------------------------------------------------------------------

  evalᴰ-Cata-erased : ∀ {F : Functor} (wfF : WellFormedF F)
      (mir : IR.IR ⌊ ⟦ F ⟧T A' ⌋ ⌊ A' ⌋) (w : ⟦ μ-type F ⟧ᴰ)
    → liftFn (IR.Cata (wf-⌊⌋ wfF) (subst (λ o → IR.IR o ⌊ A' ⌋) (⌊⟧T-commute F A') mir)) w
      ≡ cata-sem wfF (liftFn mir) w
  evalᴰ-Cata-erased {F} wfF mir w = extensionality goal
    where
      mir' : IR.IR (⟦ eraseF F ⟧TI ⌊ A' ⌋) ⌊ A' ⌋
      mir' = subst (λ o → IR.IR o ⌊ A' ⌋) (⌊⟧T-commute F A') mir

      w' : ⟦ ⌊ μ-type F ⌋ ⟧ᴰᴵ
      w' = subst (λ z → z) (sym (cohᴰ (μ-type F))) w

      seed-eq : subst μS (tF-coh F) (forget w') ≡ forget w
      seed-eq = trans (sym (subst-cong-μS (tF-coh F) w'))
                      (subst-subst-sym {P = λ z → z} (cong μS (tF-coh F)))

      goal : ∀ n → liftFn (IR.Cata (wf-⌊⌋ wfF) mir') w n ≡ cata-sem wfF (liftFn mir) w n
      goal n = trans (subst-T-apply (cohᴰ A') (evalᴰ (IR.Cata (wf-⌊⌋ wfF) mir') w') n)
                     (trans (cong (λ L → (proj₁ L , subst (λ z → z) (cohᴰ A') (proj₂ L))) Lr≡)
                            (cong₂ _,_ (proj₁ rc) (proj₂ rc)))
        where
          dalg_L : ⟦ ⟦ ⌈ eraseF F ⌉F ⟧T ⌈ ⌊ A' ⌋ ⌉ ⟧ᴰ → T ⟦ ⌈ ⌊ A' ⌋ ⌉ ⟧ᴰ
          dalg_L z = evalᴰ mir' (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF F) ⌊ A' ⌋)) z)

          algL : ⟦ translateF Carrier Carrier (⌈ eraseF F ⌉F) ⟧SF (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)
          algL y = cata-ev-algᴰ-D {⌈ eraseF F ⌉F} {⌈ ⌊ A' ⌋ ⌉} n dalg_L (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ y)

          algL' : ⟦ translateF Carrier Carrier F ⟧SF (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)
          algL' y = algL (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh F)) y)

          algM : ⟦ translateF Carrier Carrier F ⟧SF (List SigOpEvent × ⟦ A' ⟧ᴰ) → (List SigOpEvent × ⟦ A' ⟧ᴰ)
          algM y = cata-ev-algᴰ-D {F} {A'} n (liftFn mir) (coerce-μ-out wfF _ y)

          Lr≡ : evalᴰ (IR.Cata (wf-⌊⌋ wfF) mir') w' n ≡ cataS {translateF Carrier Carrier F} algL' (forget w)
          Lr≡ = trans (cataS-subst-functor (tF-coh F) algL (forget w'))
                      (cong (cataS {translateF Carrier Carrier F} algL') seed-eq)

          algR-full : ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) RelC y₁ y₂ → RelC (algL' y₁) (algM y₂)
          algR-full {y₁} {y₂} rsf = cong₂ _++_ (layer-events wfF rsf) trace-step , value-step
            where
              z_L = coerce-functor⁻¹-D ⌈ eraseF F ⌉F ⌈ ⌊ A' ⌋ ⌉ (sem-fmap ⌈ eraseF F ⌉F proj₂ (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh F)) y₁)))
              step-eq : subst T (cohᴰ A') (dalg_L z_L) ≡ liftFn mir (coerce-functor⁻¹-D F A' (sem-fmap F proj₂ (coerce-μ-out wfF _ y₂)))
              step-eq = trans (cong (subst T (cohᴰ A')) (evalᴰ-subst-dom (⌊⟧T-commute F A') mir (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF F) ⌊ A' ⌋)) z_L)))
                              (cong (λ Z → subst T (cohᴰ A') (evalᴰ mir Z)) (layer-z wfF rsf))
              trace-step = trans (sym (subst-T-projTrace (cohᴰ A') (dalg_L z_L) n)) (cong (λ t → projTrace t n) step-eq)
              value-step = trans (sym (subst-T-valueT (cohᴰ A') (dalg_L z_L) n)) (cong (λ t → valueT t n) step-eq)

          rc : RelC (cataS {translateF Carrier Carrier F} algL' (forget w)) (cataS {translateF Carrier Carrier F} algM (forget w))
          rc = cataS-rel RelC algR-full (forget w)

------------------------------------------------------------------------
-- `forget-coh`: the base-type coherence between `forget` and the `coh`/`cohᴰ`
-- transports — `subst (coh A) (forget (subst (sym cohᴰ A) arg)) ≡ forget arg`.
-- Discharges the SigOp-masquerade `refl`s that `liftFn`'s transports break
-- (RealizeAgrees `masq*`, MeaningBridge `bridge-m` SigOp leaves). Plan 0.52 M2.
------------------------------------------------------------------------

push-⊎₁' : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A)
  → subst (λ z → z) (cong₂ _⊎_ p q) (inj₁ a) ≡ inj₁ (subst (λ z → z) p a)
push-⊎₁' refl refl a = refl

push-⊎₂' : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B)
  → subst (λ z → z) (cong₂ _⊎_ p q) (inj₂ b) ≡ inj₂ (subst (λ z → z) q b)
push-⊎₂' refl refl b = refl

push-×' : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A) (b : B)
  → subst (λ z → z) (cong₂ _×_ p q) (a , b) ≡ (subst (λ z → z) p a , subst (λ z → z) q b)
push-×' refl refl a b = refl

forget-coh : ∀ {A} (ib : IsBaseType A) (arg : ⟦ A ⟧ᴰ)
  → subst (λ z → z) (coh A) (forget (subst (λ z → z) (sym (cohᴰ A)) arg)) ≡ forget arg
forget-coh base-Unit   arg = refl
forget-coh base-Void   ()
forget-coh base-Int    arg = refl
forget-coh base-Float  arg = refl
forget-coh base-Str    arg = refl
forget-coh base-Buffer arg = refl
forget-coh (base-Prod {A} {B} ibA ibB) (a , b)
  rewrite push-× (cohᴰ A) (cohᴰ B) a b
        | push-×' (coh A) (coh B) (forget (subst (λ z → z) (sym (cohᴰ A)) a)) (forget (subst (λ z → z) (sym (cohᴰ B)) b))
  = cong₂ _,_ (forget-coh ibA a) (forget-coh ibB b)
forget-coh (base-Sum {A} {B} ibA ibB) (inj₁ a)
  rewrite push-⊎₁ (cohᴰ A) (cohᴰ B) a
        | push-⊎₁' (coh A) (coh B) (forget (subst (λ z → z) (sym (cohᴰ A)) a))
  = cong inj₁ (forget-coh ibA a)
forget-coh (base-Sum {A} {B} ibA ibB) (inj₂ b)
  rewrite push-⊎₂ (cohᴰ A) (cohᴰ B) b
        | push-⊎₂' (coh A) (coh B) (forget (subst (λ z → z) (sym (cohᴰ B)) b))
  = cong inj₂ (forget-coh ibB b)

------------------------------------------------------------------------
-- `liftFn-SigOp`: the `liftFn` of a base-domain `SigOp` IS the direct
-- emit-D/semM Kleisli arrow (the `cohᴰ B` result-transport cancels via
-- `subst-subst-sym`; the arg-transport collapses via `forget-coh`). Discharges
-- every SigOp-masquerade `refl` (RealizeAgrees `masq*`). Plan 0.52 M2.
------------------------------------------------------------------------

liftFn-SigOp : ∀ {A B : Type} (info : SigOpInfo A B) (bA : IsBaseType A)
  → liftFn (IR.SigOp info)
    ≡ (λ arg → λ n → (emit-D info (forget arg) , inject (semM info (forget arg))))
liftFn-SigOp {A} {B} info bA = extensionality λ arg → extensionality λ n →
  trans (subst-T-apply (cohᴰ B) (evalᴰ (IR.SigOp info) (subst (λ z → z) (sym (cohᴰ A)) arg)) n)
        (cong₂ _,_ (cong (emit-D info) (forget-coh bA arg))
                   (trans (subst-subst-sym {P = λ z → z} (cohᴰ B))
                          (cong (λ w → inject (semM info w)) (forget-coh bA arg))))
