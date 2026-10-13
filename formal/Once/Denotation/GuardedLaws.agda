-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.GuardedLaws — forgetting the guard is a module morphism:
-- `T`'s actions on `T⁺` are `T`'s bind (D311, plan 0.117 C2).
------------------------------------------------------------------------

module Once.Denotation.GuardedLaws where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Denotation.TraceMonad using (T; ret; call; halt; _>>=T_)
open import Once.Spec.Guarded using (T⁺; call⁺; halt⁺; forget⁺; _>>=⁺_; _⁺=<<_)

forget-bind⁺ : ∀ {X Y} (m : T⁺ X) (f : X → T Y) → forget⁺ (m >>=⁺ f) ≡ (forget⁺ m >>=T f)
forget-bind⁺ (call⁺ o a k) f = refl
forget-bind⁺ (halt⁺ o a)   f = refl

forget-⁺bind : ∀ {X Y} (m : T X) (f : X → T⁺ Y) → forget⁺ (m ⁺=<< f) ≡ (m >>=T λ x → forget⁺ (f x))
forget-⁺bind (ret x)      f = refl
forget-⁺bind (call o a k) f = refl
forget-⁺bind (halt o a)   f = refl

-- A guarded stream's forced layer, forgotten, is its tree.
open import Once.Spec.Guarded using (anaRoot⁺; anaTree⁺)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF)

forget-anaRoot : ∀ (H : SFunctor) {A : Set} (c : A → T⁺ (⟦ H ⟧SF A)) (m : T⁺ (⟦ H ⟧SF A))
               → forget⁺ (anaRoot⁺ H c m) ≡ anaTree⁺ H c (forget⁺ m)
forget-anaRoot H c (call⁺ o a k) = refl
forget-anaRoot H c (halt⁺ o a)   = refl

-- The guard's bind is associative (its monad laws are `T`'s, read through
-- `forget⁺`).
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Once.Postulates using (extensionality)
open import Once.Denotation.TraceMonadLaws using (>>=T-assoc)

assoc⁺ : ∀ {X Y Z : Set} (m : T⁺ X) (f : X → T⁺ Y) (g : Y → T⁺ Z)
       → ((m >>=⁺ λ x → forget⁺ (f x)) >>=⁺ λ y → forget⁺ (g y))
         ≡ (m >>=⁺ λ x → forget⁺ (f x >>=⁺ λ y → forget⁺ (g y)))
assoc⁺ (call⁺ o a k) f g =
  cong (call⁺ o a) (extensionality λ b →
    trans (>>=T-assoc (k b) (λ x → forget⁺ (f x)) (λ y → forget⁺ (g y)))
          (cong (k b >>=T_) (extensionality λ x → sym (forget-bind⁺ (f x) (λ y → forget⁺ (g y))))))
assoc⁺ (halt⁺ o a) f g = refl
