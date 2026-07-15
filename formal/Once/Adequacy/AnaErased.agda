-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.AnaErased
--
-- Plan 0.52 M2: the FUNCTOR-TRANSPORT lemma isolating the erasure round-trip
-- for the `Ana` recursion scheme — the coinductive dual of `CataErased`. After
-- M2 the IR's `Ana` unfolds the ERASED functor `⌈eraseF F⌉F` (`evalᴰ (Ana …)`
-- calls `sem-ana ⌈eraseF F⌉F`), while the surface/meaning value runs `sem-ana F`
-- at `F`. On the ν CODATA `inject`/`forget` are the identity, so the values must
-- genuinely coincide — a coinductive obligation.
--
-- The single export `sem-ana-erase-coh′` bridges the two via the SFunctor level,
-- where `tF-coh : translateF ⌈eraseF F⌉F ≡ translateF F` lives. The coinduction is
-- confined to ONE same-functor bisimulation `sem-ana-anaS` (mirroring the existing
-- `sem-ana-Out-bisim` template): `sem-ana` factors through the νS-level `anaS`.
-- The cross-functor transport `anaS-subst-nat` is then a cheap match-to-refl.
-- Uses the codebase's accepted `bisimS-to-eq` axiom (as `sem-ana-Out-id` does).
------------------------------------------------------------------------

module Once.Adequacy.AnaErased where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

open import Once.Word using (Carrier)
open import Once.Type using (Functor)
open import Once.Functor.Translate using (translateF)
open import Once.IRTy using (eraseF; ⌈_⌉F)
open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; νS; unfoldS; anaS; sfmapAna)
open import Once.Semantics.Functor.Laws
  using (_∼S_; ⟦_⟧SF-rel; unfoldS-∼; bisimS-to-eq)
open import Once.Semantics.Machine
  using (⟦_⟧F; sem-ana; sfmapSemAna; coerce-ν-in; tF-coh)

------------------------------------------------------------------------
-- `sem-ana` factors through the νS-level `anaS`: unfolding the raw functor
-- coalgebra `A → ⟦F⟧F A` equals unfolding its coerced SFunctor form
-- `A → ⟦translateF F⟧SF A`. SAME functor `F` on both sides — a clean
-- bisimulation mirroring `sem-ana-Out-bisim`/`sem-ana-Out-rel`.
------------------------------------------------------------------------

mutual
  sem-ana-anaS-bisim : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A) (a : A)
    → sem-ana F coalg a ∼S anaS {translateF Carrier F} (λ x → coerce-ν-in F A (coalg x)) a
  unfoldS-∼ (sem-ana-anaS-bisim {F} {A} coalg a) =
    sem-ana-anaS-rel coalg (translateF Carrier F) (coerce-ν-in F A (coalg a))

  sem-ana-anaS-rel : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A)
                       (H : SFunctor) (x : ⟦ H ⟧SF A)
    → ⟦ H ⟧SF-rel (_∼S_ {translateF Carrier F})
        (sfmapSemAna F H coalg x)
        (sfmapAna {translateF Carrier F} H (λ y → coerce-ν-in F A (coalg y)) x)
  sem-ana-anaS-rel coalg (SK _)      x        = refl
  sem-ana-anaS-rel coalg SId         x        = sem-ana-anaS-bisim coalg x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₁ x) = sem-ana-anaS-rel coalg H₁ x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₂ y) = sem-ana-anaS-rel coalg H₂ y
  sem-ana-anaS-rel coalg (H₁ S⊗ H₂) (x , y)  =
    sem-ana-anaS-rel coalg H₁ x , sem-ana-anaS-rel coalg H₂ y

sem-ana-anaS : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A) (a : A)
  → sem-ana F coalg a ≡ anaS {translateF Carrier F} (λ x → coerce-ν-in F A (coalg x)) a
sem-ana-anaS coalg a = bisimS-to-eq _ _ (sem-ana-anaS-bisim coalg a)

------------------------------------------------------------------------
-- Cross-functor transport of `anaS` over an SFunctor equality — cheap
-- (match the equation to `refl`). This is where `tF-coh` discharges.
------------------------------------------------------------------------

anaS-subst-nat : ∀ {H₁ H₂ : SFunctor} {A : Set} (eq : H₁ ≡ H₂)
                   (coalg : A → ⟦ H₁ ⟧SF A) (a : A)
  → subst νS eq (anaS coalg a) ≡ anaS (subst (λ H → A → ⟦ H ⟧SF A) eq coalg) a
anaS-subst-nat refl coalg a = refl

------------------------------------------------------------------------
-- The erasure round-trip: the `tF-coh`-transported erased-functor unfold
-- equals the surface-functor unfold, GIVEN the coalgebras correspond after
-- transport (discharged in `ana-body` from the coalgebra IH + coerce
-- round-trip). Value half of `ana`-faithfulness.
------------------------------------------------------------------------

sem-ana-erase-coh′ : ∀ {F : Functor} {A : Set}
    (cL : A → ⟦ ⌈ eraseF F ⌉F ⟧F A) (cR : A → ⟦ F ⟧F A) (a : A)
    (ceq : subst (λ H → A → ⟦ H ⟧SF A) (tF-coh F)
             (λ x → coerce-ν-in ⌈ eraseF F ⌉F A (cL x))
           ≡ (λ x → coerce-ν-in F A (cR x)))
  → subst νS (tF-coh F) (sem-ana ⌈ eraseF F ⌉F cL a) ≡ sem-ana F cR a
sem-ana-erase-coh′ {F} {A} cL cR a ceq =
  trans (cong (subst νS (tF-coh F)) (sem-ana-anaS cL a))
    (trans (anaS-subst-nat (tF-coh F) (λ x → coerce-ν-in ⌈ eraseF F ⌉F A (cL x)) a)
      (trans (cong (λ c → anaS c a) ceq)
             (sym (sem-ana-anaS cR a))))
