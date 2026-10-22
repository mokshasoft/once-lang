-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Types — the facts about related types the
-- surface typing translation needs (plan 0.121 §3.6, F4/F5).
--
-- `SpecCore.Type.TyR Δ A A′` relates a compiler type to the Spec's (plan
-- 0.122: the identity's graph). Every Spec type is related to one (`back`),
-- and a compiler type below a related one is related too (`below-R`). The
-- subtyping that keeps domains (`<:ᶜ`) crosses both ways, and so does a join.
-- The rest are the types surface rules read off: an annotation's, a
-- declaration's, a functor applied.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Once.Spec.Type as ST

import Once.Spec.Grade
module Once.Adequacy.SpecFront.Types {m : ℕ} (Δ : ST.KCtx m) where


open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat using (_<?_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Sub as LS
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as LW
import Once.Internal.Type.Honest as LH
import Once.Spec.Sub as SS
open import Once.Spec.Signature using (⌜_⌝; ⌜_⌝ᵈ)
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS; toTy; toFun)
open import Once.Adequacy.SpecCore.Type
open import Once.Internal.Core.Decl using (toB; declS)

------------------------------------------------------------------------
-- Every Spec type is a compiler one (itself)
------------------------------------------------------------------------

back : ∀ (D : ST.Ty m) → Σ[ D₀ ∈ ST.Ty m ] TyR Δ D₀ D
back D = D , tyR D

backF : ∀ (F : ST.Fun m) → Σ[ F₀ ∈ ST.Fun m ] FunR Δ F₀ F
backF F = F , funR F

------------------------------------------------------------------------
-- Keeping domains, both ways
------------------------------------------------------------------------

subᶜ-S : ∀ {A B A′ B′} → A SS.<:ᶜ B → TyR Δ A A′ → TyR Δ B B′ → A′ SS.<:ᶜ B′
subᶜ-S p ra rb = subst₂ SS._<:ᶜ_ (TyR-≡ ra) (TyR-≡ rb) p

subᶜ-L : ∀ {A B A′ B′} → A′ SS.<:ᶜ B′ → TyR Δ A A′ → TyR Δ B B′ → A SS.<:ᶜ B
subᶜ-L p ra rb = subst₂ SS._<:ᶜ_ (sym (TyR-≡ ra)) (sym (TyR-≡ rb)) p

------------------------------------------------------------------------
-- A type below a related one is related
------------------------------------------------------------------------

below-R : ∀ {A B B′} → A SS.<:ᶜ B → TyR Δ B B′ → Σ[ A′ ∈ ST.Ty m ] TyR Δ A A′
below-R {A} _ _ = A , tyR A

------------------------------------------------------------------------
-- Joins, both ways
------------------------------------------------------------------------

join-S : ∀ {A B C A′ B′} → A SS.⊔ B ≔ C → TyR Δ A A′ → TyR Δ B B′
       → Σ[ C′ ∈ ST.Ty m ] (TyR Δ C C′ × A′ SS.⊔ B′ ≔ C′)
join-S {C = C} J ra rb = C , tyR C , subst₂ (λ X Y → X SS.⊔ Y ≔ C) (TyR-≡ ra) (TyR-≡ rb) J

join-L : ∀ {A B A′ B′ C′} → A′ SS.⊔ B′ ≔ C′ → TyR Δ A A′ → TyR Δ B B′
       → Σ[ C ∈ ST.Ty m ] (TyR Δ C C′ × A SS.⊔ B ≔ C)
join-L {C′ = C′} J ra rb = C′ , tyR C′ , subst₂ (λ X Y → X SS.⊔ Y ≔ C′) (sym (TyR-≡ ra)) (sym (TyR-≡ rb)) J

------------------------------------------------------------------------
-- The types the surface rules read off
------------------------------------------------------------------------

-- A functor applied.
⟦⟧-R : ∀ {F F′ A A′} → FunR Δ F F′ → TyR Δ A A′ → TyR Δ (LT.⟦ F ⟧F A) (ST.⟦ F′ ⟧F A′)
⟦⟧-R (r-K b)   a = b
⟦⟧-R r-Id      a = a
⟦⟧-R (r-⊕ f g) a = r-+ (⟦⟧-R f a) (⟦⟧-R g a)
⟦⟧-R (r-⊗ f g) a = r-* (⟦⟧-R f a) (⟦⟧-R g a)

-- An annotation's type (a surface type, so ground: read at any instance).
mutual
  annot-R : ∀ {T} (σ : ST.TySub 0 m) → LW.RigidFree T → TyR Δ (LT.wk₀ T) (toTy T ST.⟨ σ ⟩)
  annot-R σ LW.rf-Unit   = r-unit
  annot-R σ LW.rf-Void   = r-void
  annot-R σ LW.rf-Int    = r-int
  annot-R σ LW.rf-Float  = r-float
  annot-R σ (LW.rf-* a b) = r-* (annot-R σ a) (annot-R σ b)
  annot-R σ (LW.rf-+ a b) = r-+ (annot-R σ a) (annot-R σ b)
  annot-R σ (LW.rf-⇒ a b) = r-⇒ refl (annot-R σ a) (annot-R σ b)
  annot-R σ (LW.rf-μ f)   = r-μ (annotF-R σ f)
  annot-R σ (LW.rf-ν f)   = r-ν refl (annotF-R σ f)

  annotF-R : ∀ {F} (σ : ST.TySub 0 m) → LW.RigidFreeF F → FunR Δ (LT.wk₀F F) (toFun F ST.⟨ σ ⟩F)
  annotF-R σ (LW.rf-K a)   = r-K (annot-R σ a)
  annotF-R σ LW.rf-Id      = r-Id
  annotF-R σ (LW.rf-⊕ f g) = r-⊕ (annotF-R σ f) (annotF-R σ g)
  annotF-R σ (LW.rf-⊗ f g) = r-⊗ (annotF-R σ f) (annotF-R σ g)

-- A declaration's type.
base-R : ∀ {A} → LW.IsBaseType A → LW.RigidFree A → TyR Δ (LT.wk₀ A) ⌜ toB A ⌝
base-R LW.base-Unit  _ = r-unit
base-R LW.base-Void  _ = r-void
base-R LW.base-Int   _ = r-int
base-R LW.base-Float _ = r-float
base-R (LW.base-Prod a b) (LW.rf-* ra rb) = r-* (base-R a ra) (base-R b rb)
base-R (LW.base-Sum a b)  (LW.rf-+ ra rb) = r-+ (base-R a ra) (base-R b rb)

decl-R : ∀ {A} → LW.IsConcrete A → LH.HonestFFI A → LW.RigidFree A → TyR Δ (LT.wk₀ A) ⌜ declS A ⌝ᵈ
decl-R {A LT.⇒[ LG.mk-kind q LG.pure ] B} (LW.con-fun a b) h (LW.rf-⇒ ra rb) = r-⇒ refl (base-R a ra) (base-R b rb)
decl-R {A LT.⇒[ LG.mk-kind q LG.act ] B}  (LW.con-fun a b) h (LW.rf-⇒ ra rb) = r-⇒ refl (base-R a ra) (base-R b rb)
decl-R {A LT.⇒[ LG.mk-kind LG.Zero LG.eff ] B} _ () _
decl-R {A LT.⇒[ LG.mk-kind LG.One  LG.eff ] B} _ () _
decl-R {A LT.⇒[ LG.mk-kind LG.Many LG.eff ] B} _ () _
decl-R (LW.con-base LW.base-Unit) () _
decl-R (LW.con-base LW.base-Void) () _
decl-R (LW.con-base LW.base-Int) _ _ = r-int
decl-R (LW.con-base LW.base-Float) _ _ = r-float
decl-R (LW.con-base b@(LW.base-Prod _ _)) _ r = base-R b r
decl-R (LW.con-base b@(LW.base-Sum _ _)) _ r = base-R b r

-- An effectful grade.
eff-S : ∀ {π} → LG.EffGrade π → SG.EffGrade (πS π)
eff-S g = g
