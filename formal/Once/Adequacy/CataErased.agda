-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; μS; cataS; ⟦_⟧SF)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT)
open import Once.IRTy using (IRTy; IRFunctor; ⌊_⌋; ⌈_⌉; ⌈_⌉F; ⟦_⟧TI; ⌈⟧TI-commute)
open import Once.Denotation.DenotTrace
  using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; evalᴰ; cata-ev-algᴰ; coerce-functor⁻¹-D)
open import Once.Denotation.Meaning using (cata-ev-algᴰ-D; cata-sem)
open import Once.Semantics.Machine
  using (⟦_⟧F; sem-cata; sem-fmap; coerce-μ-out; tF-coh)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ⟦_⟧T; μ-type)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum)
open import Once.Denotation.DenotTrace using (forget; liftFn; cohᴰ)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.IRTy using (eraseF; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Once.Postulates using (extensionality)
import Once.IR as IR

------------------------------------------------------------------------
-- Generic transport helpers (both by matching the equation to `refl`).
------------------------------------------------------------------------

-- Applying a `subst`-transported computation transports its VALUE half only.
subst-T-apply : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (n : ℕ)
  → subst T eq h n ≡ (proj₁ (h n) , subst (λ Z → Z) eq (proj₂ (h n)))
subst-T-apply refl h n = refl

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
-- The functor-structural layer lemma, fixed at result type `A'`. Two facts:
--   (A) `layer-events`: the per-layer CHILD TRACES coincide across the erasure
--       functor round-trip (given `RelSF`-related layers).
--   (B) `layer-z`: the assembled recursive ARGUMENT coincides after transport.
------------------------------------------------------------------------

module _ {A' : Type} where

  RelC : (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → (List SigOpEvent × ⟦ A' ⟧ᴰ) → Set
  RelC l r = (proj₁ l ≡ proj₁ r) × (subst (λ z → z) (cohᴰ A') (proj₂ l) ≡ proj₂ r)

  layer-events : ∀ {G} (wfG : WellFormedF G)
      {y₁ : ⟦ translateF Carrier G ⟧SF (List SigOpEvent × ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)}
      {y₂ : ⟦ translateF Carrier G ⟧SF (List SigOpEvent × ⟦ A' ⟧ᴰ)}
    → RelSF (translateF Carrier G) RelC y₁ y₂
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
