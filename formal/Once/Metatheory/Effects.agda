-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Effects — the meaning's effect structure
-- (`Spec.Metatheory.Effects`, plan 0.112 E and C4).
--
-- `M π` is one monad per grade (the identity monad at `pure`, the interaction
-- tree `T` at `eff`, the completely iterative monad `T∞` at `prod`), equal up
-- to the grade's equality (`EqM`: `≡`, or bisimilarity at `prod`), and a
-- graded monad through `bindᵍ` (D311). The monad morphisms between them are
-- `subM` (subeffecting) and `toT∞` (every grade read as a tree of `T∞`); the
-- observation `run` respects `T`'s return and bind.
------------------------------------------------------------------------

module Once.Metatheory.Effects where

open import Data.List using (List; [])
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Type.Grade using (Purity; pure; eff; prod; _·p_)
open import Once.Spec.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-prod; ⊑-pp; ⊑-ep)
open import Once.Spec.Metatheory using (Effects)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; Interp; run; then)
open import Once.Denotation.TraceMonadLaws using (>>=T-identityʳ; >>=T-assoc; run-bind)
open import Once.Denotation.GradedDomain using (M; returnM; bindM; subM; toT∞; bindᵍ; EqM; _>>=ᵖ_)
open import Once.Spec.Iterative using (T∞; return∞; _>>=∞_; embed; TreeEq∞; ret≈∞)
open Once.Spec.Iterative.TreeEq∞ using (force≈)
open import Once.Denotation.TraceMonadInfLaws using (≈∞-refl; ≈∞-bind; ≈∞-rewrite; ≈∞-idˡ; ≈∞-idʳ; ≈∞-assoc; embed-bind)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β; >>=ᵖ-assoc; >>=ᵖ-idʳ; bindM-idˡ)

M-identityʳ : ∀ π {X : Set} (m : M π X) → EqM π (bindM π m (returnM π)) m
M-identityʳ pure m = >>=ᵖ-idʳ m
M-identityʳ eff  m = >>=T-identityʳ m
M-identityʳ prod m = ≈∞-idʳ m

M-assoc : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
        → EqM π (bindM π (bindM π m f) g) (bindM π m (λ x → bindM π (f x) g))
M-assoc pure m f g = >>=ᵖ-assoc m f g
M-assoc eff  m f g = >>=T-assoc m f g
M-assoc prod m f g = ≈∞-assoc m f g

-- Two trees that are the same, and two whose root is the same leaf.
private
  ≡→≈ : ∀ {X} {m m′ : T∞ X} → m ≡ m′ → TreeEq∞ _≡_ m m′
  ≡→≈ {m = m} refl = ≈∞-refl (λ _ → refl) m

  ret-≈ : ∀ {X} (x : X) → TreeEq∞ _≡_ (embed (returnT x)) (return∞ x)
  force≈ (ret-≈ x) = ret≈∞ refl

  retβ-≈ : ∀ {X Y} (m : X) (k : X → Y) → TreeEq∞ _≡_ (return∞ (m >>=ᵖ k)) (return∞ m >>=∞ λ x → return∞ (k x))
  force≈ (retβ-≈ m k) = ret≈∞ (>>=ᵖ-β m k)

subM-return : ∀ {π π′} (g : π ⊑π π′) {X : Set} (x : X) → EqM π′ (subM g (returnM π x)) (returnM π′ x)
subM-return ⊑-pure x = refl
subM-return ⊑-eff  x = refl
subM-return ⊑-pe   x = refl
subM-return ⊑-prod x = ≈∞-refl (λ _ → refl) (return∞ x)
subM-return ⊑-pp   x = ≈∞-refl (λ _ → refl) (return∞ x)
subM-return ⊑-ep   x = ret-≈ x

subM-bind : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
          → EqM π′ (subM g (bindM π m k)) (bindM π′ (subM g m) (λ x → subM g (k x)))
subM-bind ⊑-pure m k = refl
subM-bind ⊑-eff  m k = refl
subM-bind ⊑-pe   m k = cong returnT (>>=ᵖ-β m k)
subM-bind ⊑-prod m k = ≈∞-refl (λ _ → refl) (m >>=∞ k)
subM-bind ⊑-pp   m k = retβ-≈ m k
subM-bind ⊑-ep   m k = embed-bind m k

toT∞-return : ∀ π {X : Set} (x : X) → TreeEq∞ _≡_ (toT∞ π (returnM π x)) (return∞ x)
toT∞-return pure x = ≈∞-refl (λ _ → refl) (return∞ x)
toT∞-return eff  x = ret-≈ x
toT∞-return prod x = ≈∞-refl (λ _ → refl) (return∞ x)

toT∞-bind : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
          → TreeEq∞ _≡_ (toT∞ π (bindM π m k)) (toT∞ π m >>=∞ λ x → toT∞ π (k x))
toT∞-bind pure m k = retβ-≈ m k
toT∞-bind eff  m k = embed-bind m k
toT∞-bind prod m k = ≈∞-refl (λ _ → refl) (m >>=∞ k)

toT∞-bindᵍ : ∀ π₁ π₂ {X Y : Set} (m : M π₁ X) (k : X → M π₂ Y)
           → TreeEq∞ _≡_ (toT∞ (π₁ ·p π₂) (bindᵍ π₁ π₂ m k)) (toT∞ π₁ m >>=∞ λ x → toT∞ π₂ (k x))
toT∞-bindᵍ pure π₂ m k =
  ≈∞-rewrite (≡→≈ (cong (toT∞ π₂) (>>=ᵖ-β m k))) (≈∞-idˡ m (λ x → toT∞ π₂ (k x)))
             (≈∞-refl (λ _ → refl) (toT∞ π₂ (k m)))
toT∞-bindᵍ eff pure m k =
  ≈∞-rewrite (embed-bind m (λ x → returnT (k x))) (≈∞-refl (λ _ → refl) _)
             (≈∞-bind {R = _≡_} (≈∞-refl (λ _ → refl) (embed m)) λ { refl → ret-≈ _ })
toT∞-bindᵍ eff eff  m k = embed-bind m k
toT∞-bindᵍ eff prod m k = ≈∞-refl (λ _ → refl) (embed m >>=∞ k)
toT∞-bindᵍ prod π₂  m k = ≈∞-refl (λ _ → refl) (m >>=∞ λ x → toT∞ π₂ (k x))

run-return : ∀ (ι : Interp) (h : List SigOpEvent) {X Y : Set} (x : X) (f : X → T Y)
           → then ι h (run ι h (returnT x)) f ≡ run ι h (f x)
run-return ι h x f = cong (λ hh → run ι hh (f x)) (++-identityʳ h)

effects : Effects
effects = record
  { M-identityˡ = bindM-idˡ
  ; M-identityʳ = M-identityʳ
  ; M-assoc     = M-assoc
  ; subM-return = subM-return
  ; subM-bind   = subM-bind
  ; toT∞-return = toT∞-return
  ; toT∞-bind   = toT∞-bind
  ; toT∞-bindᵍ  = toT∞-bindᵍ
  ; run-return  = run-return
  ; run-bind    = λ ι h m f → run-bind ι h m f
  }
