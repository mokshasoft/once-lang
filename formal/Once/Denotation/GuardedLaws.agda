-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.GuardedLaws — forgetting the guard is a module morphism:
-- `T∞`'s actions on `T⁺` are `T∞`'s bind, up to bisimilarity (D311, D312).
------------------------------------------------------------------------

module Once.Denotation.GuardedLaws where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Lang.Iterative
  using (T∞; T∞F; ret∞; call∞; halt∞; _>>=∞_; bind∞F; TreeEq∞; NodeEq; call≈∞; halt≈∞; module T∞)
open T∞ using (force)
open Once.Lang.Iterative.TreeEq∞ using (force≈)
open import Once.Lang.Guarded using (T⁺; call⁺; halt⁺; root⁺; forget⁺; _>>=⁺_; _⁺=<<_; bindF⁺)
open import Once.Denotation.TraceMonadInfLaws using (≈∞-refl; ≈∞-reflF; ≈∞-bind; ≈∞-rewrite; ≈∞-assoc)

forget-bind⁺ : ∀ {X Y} (m : T⁺ X) (f : X → T∞ Y) → TreeEq∞ _≡_ (forget⁺ (m >>=⁺ f)) (forget⁺ m >>=∞ f)
force≈ (forget-bind⁺ (call⁺ o a k) f) = call≈∞ (λ b → ≈∞-refl (λ _ → refl) (k b >>=∞ f))
force≈ (forget-bind⁺ (halt⁺ o a)   f) = halt≈∞

forget-⁺bind  : ∀ {X Y} (m : T∞ X) (f : X → T⁺ Y) → TreeEq∞ _≡_ (forget⁺ (m ⁺=<< f)) (m >>=∞ λ x → forget⁺ (f x))
forget-⁺bindF : ∀ {X Y} (l : T∞F X (T∞ X)) (f : X → T⁺ Y)
              → NodeEq _≡_ (TreeEq∞ _≡_) (root⁺ (bindF⁺ l f)) (bind∞F l λ x → forget⁺ (f x))
force≈ (forget-⁺bind m f) = forget-⁺bindF (force m) f
forget-⁺bindF (ret∞ x)      f = ≈∞-reflF (λ _ → refl) (root⁺ (f x))
forget-⁺bindF (call∞ o a k) f = call≈∞ (λ b → ≈∞-refl (λ _ → refl) _)
forget-⁺bindF (halt∞ o a)   f = halt≈∞

open import Once.Lang.Guarded using (anaRoot⁺; anaTree⁺)
open import Once.Lang.Polynomial using (SFunctor; ⟦_⟧SF)

forget-anaRoot : ∀ (H : SFunctor) {A : Set} (c : A → T⁺ (⟦ H ⟧SF A)) (m : T⁺ (⟦ H ⟧SF A))
               → TreeEq∞ _≡_ (forget⁺ (anaRoot⁺ H c m)) (anaTree⁺ H c (forget⁺ m))
force≈ (forget-anaRoot H c (call⁺ o a k)) = call≈∞ (λ b → ≈∞-refl (λ _ → refl) _)
force≈ (forget-anaRoot H c (halt⁺ o a))   = halt≈∞

-- Associativity of the guarded bind, up to bisimilarity (`EqM eff⁺`).
assoc⁺ : ∀ {X Y Z : Set} (m : T⁺ X) (f : X → T⁺ Y) (g : Y → T⁺ Z)
       → TreeEq∞ _≡_ (forget⁺ ((m >>=⁺ λ x → forget⁺ (f x)) >>=⁺ λ y → forget⁺ (g y)))
                     (forget⁺ (m >>=⁺ λ x → forget⁺ (f x >>=⁺ λ y → forget⁺ (g y))))
force≈ (assoc⁺ (call⁺ o a k) f g) = call≈∞ λ b →
  ≈∞-rewrite (≈∞-assoc (k b) (λ x → forget⁺ (f x)) (λ y → forget⁺ (g y)))
             (≈∞-bind {R = _≡_} (≈∞-refl (λ _ → refl) (k b)) (λ { {x} refl → forget-bind⁺ (f x) (λ y → forget⁺ (g y)) }))
             (≈∞-refl (λ _ → refl) _)
force≈ (assoc⁺ (halt⁺ o a) f g) = halt≈∞
