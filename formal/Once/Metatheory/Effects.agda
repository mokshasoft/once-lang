-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Effects — the meaning's effect structure
-- (`Spec.Metatheory.Effects`, plan 0.112 E and C4).
--
-- `M π` is one monad per grade (the identity monad at `pure`, the completely
-- iterative monad `T∞` at `eff`, D312), equal up to the grade's equality
-- (`EqM`: `≡`, or bisimilarity), and a
-- graded monad through `bindᵍ` (D311). The monad morphisms between them are
-- `subM` (subeffecting) and `toT∞` (every grade read as a tree of `T∞`); the
-- observation `events∞` respects bisimilarity and sees no event in a unit.
------------------------------------------------------------------------

module Once.Metatheory.Effects where

open import Data.List using (List; [])
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Type.Grade using (Purity; pure; eff⁺; eff; _·p_)
open import Once.Spec.Guarded using (forget⁺)
open import Once.Denotation.GuardedLaws using (forget-bind⁺; assoc⁺)
open import Once.Metatheory.Coherence.Relation using (toT∞-returnM; toT∞-bindM; toT∞-bindᵍ)
open import Once.Spec.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-g; ⊑-ge)
open import Once.Spec.Metatheory using (Effects)
open import Once.Spec.Event using (SigOpEvent)
open import Once.Spec.Trace using (T; returnT; _>>=T_; Interp; run; then)
open import Once.Spec.Graded using (M; returnM; bindM; subM; toT∞; bindᵍ; EqM; _>>=ᵖ_)
open import Once.Spec.Iterative using (T∞; return∞; _>>=∞_; TreeEq∞; ret≈∞; events∞)
open Once.Spec.Iterative.TreeEq∞ using (force≈)
open import Once.Denotation.TraceMonadInfLaws using (≈∞-refl; ≈∞-bind; ≈∞-rewrite; ≈∞-idˡ; ≈∞-idʳ; ≈∞-assoc; events∞-≈)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β; >>=ᵖ-assoc; >>=ᵖ-idʳ; bindM-idˡ)

M-identityʳ : ∀ {π} (u : pure ⊑π π) {X : Set} (m : M π X) → EqM π (bindM π m (returnM u)) m
M-identityʳ ⊑-pure m = >>=ᵖ-idʳ m
M-identityʳ ⊑-pe   m = ≈∞-idʳ m

M-assoc : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
        → EqM π (bindM π (bindM π m f) g) (bindM π m (λ x → bindM π (f x) g))
M-assoc pure m f g = >>=ᵖ-assoc m f g
M-assoc eff⁺ m f g = assoc⁺ m f g
M-assoc eff  m f g = ≈∞-assoc m f g

private
  retβ-≈ : ∀ {X Y} (m : X) (k : X → Y) → TreeEq∞ _≡_ (return∞ (m >>=ᵖ k)) (return∞ m >>=∞ λ x → return∞ (k x))
  force≈ (retβ-≈ m k) = ret≈∞ (>>=ᵖ-β m k)

subM-return : ∀ {π π′} (u : pure ⊑π π) (g : π ⊑π π′) (u′ : pure ⊑π π′) {X : Set} (x : X)
            → EqM π′ (subM g (returnM u x)) (returnM u′ x)
subM-return ⊑-pure ⊑-pure ⊑-pure x = refl
subM-return ⊑-pure ⊑-pe   ⊑-pe   x = ≈∞-refl (λ _ → refl) (return∞ x)
subM-return ⊑-pe   ⊑-eff  ⊑-pe   x = ≈∞-refl (λ _ → refl) (return∞ x)

subM-bind : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
          → EqM π′ (subM g (bindM π m k)) (bindM π′ (subM g m) (λ x → subM g (k x)))
subM-bind ⊑-pure m k = refl
subM-bind ⊑-eff  m k = ≈∞-refl (λ _ → refl) (m >>=∞ k)
subM-bind ⊑-pe   m k = retβ-≈ m k
subM-bind ⊑-g    m k = ≈∞-refl (λ _ → refl) _
subM-bind ⊑-ge   m k = forget-bind⁺ m (λ x → forget⁺ (k x))

open import Data.Nat using (zero; suc)

obs-return : ∀ (ι : Interp) (h : List SigOpEvent) {X : Set} (x : X) n → events∞ ι h (return∞ x) n ≡ []
obs-return ι h x zero    = refl
obs-return ι h x (suc n) = refl

effects : Effects
effects = record
  { M-identityˡ = bindM-idˡ
  ; M-identityʳ = M-identityʳ
  ; M-assoc     = M-assoc
  ; subM-return = subM-return
  ; subM-bind   = subM-bind
  ; toT∞-return = toT∞-returnM
  ; toT∞-bind   = toT∞-bindM
  ; toT∞-bindᵍ  = toT∞-bindᵍ
  ; obs-≈       = λ ι h e n → events∞-≈ ι h e n
  ; obs-return  = obs-return
  }
