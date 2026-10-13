-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Iteration — guarded iteration is the UNIQUE solution of
-- its equation (`Spec.Metatheory.Recursion`, D311, plan 0.117 D2).
--
-- `iter∞ f` satisfies `x a ≈ [ return∞ , (λ m → m >>=∞ [ return∞ , x ]) ] (f a)`
-- (`iter-unfold`), and every `g` that does is bisimilar to it (`iter-unique`).
-- Uniqueness is where the guard is used: a step either ends at once or begins
-- with an event (D312 O2, the standard guard), so a solution's first node is
-- fixed by the equation before it has to look at itself again, and the
-- bisimulation is built one event at a time. Without the guard `x = x` would
-- be an instance, and every tree would solve it.
------------------------------------------------------------------------

module Once.Metatheory.Iteration where

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.Spec.Guarded using (T⁺; call⁺; halt⁺; root⁺; forget⁺; iter∞; iterRoot∞; iterTree∞; iterLayer∞; iterStart∞)
open import Once.Spec.Iterative
open T∞ using (force)
open TreeEq∞ using (force≈)

------------------------------------------------------------------------
-- Bisimilarity is reflexive and transitive (at `≡` on the leaves).
------------------------------------------------------------------------

≈refl : ∀ {X} (m : T∞ X) → TreeEq∞ _≡_ m m
≈reflN : ∀ {X} (l : T∞F X (T∞ X)) → NodeEq _≡_ (TreeEq∞ _≡_) l l
force≈ (≈refl m) = ≈reflN (force m)
≈reflN (ret∞ x)      = ret≈∞ refl
≈reflN (call∞ o a k) = call≈∞ (λ b → ≈refl (k b))
≈reflN (halt∞ o a)   = halt≈∞

≈trans : ∀ {X} {m m′ m″ : T∞ X} → TreeEq∞ _≡_ m m′ → TreeEq∞ _≡_ m′ m″ → TreeEq∞ _≡_ m m″
≈transN : ∀ {X} {l l′ l″ : T∞F X (T∞ X)}
        → NodeEq _≡_ (TreeEq∞ _≡_) l l′ → NodeEq _≡_ (TreeEq∞ _≡_) l′ l″ → NodeEq _≡_ (TreeEq∞ _≡_) l l″
force≈ (≈trans p q) = ≈transN (force≈ p) (force≈ q)
≈transN (ret≈∞ e)  (ret≈∞ e′) = ret≈∞ (trans e e′)
≈transN (call≈∞ h) (call≈∞ h′) = call≈∞ (λ b → ≈trans (h b) (h′ b))
≈transN halt≈∞     halt≈∞      = halt≈∞

------------------------------------------------------------------------
-- The equation.
------------------------------------------------------------------------

module _ {A B : Set} (f : A → B ⊎ T⁺ (B ⊎ A)) where

  -- One round, then stop or loop.
  K : (A → T∞ B) → B ⊎ A → T∞ B
  K x = [ return∞ , x ]′

  -- A step: end at once, or run a round then `K x`.
  E : (A → T∞ B) → B ⊎ T⁺ (B ⊎ A) → T∞ B
  E x = [ return∞ , (λ m → forget⁺ m >>=∞ K x) ]′

  -- `iter∞ f` solves it.
  iter-unfold : ∀ a → TreeEq∞ _≡_ (iter∞ f a) (E (iter∞ f) (f a))
  unfold-start : ∀ (s : B ⊎ T⁺ (B ⊎ A)) → NodeEq _≡_ (TreeEq∞ _≡_) (iterStart∞ f s) (force (E (iter∞ f) s))
  unfold-root : ∀ (m : T⁺ (B ⊎ A))
              → NodeEq _≡_ (TreeEq∞ _≡_) (iterRoot∞ f m) (bind∞F (root⁺ m) (K (iter∞ f)))
  unfold-tree : ∀ (t : T∞ (B ⊎ A)) → TreeEq∞ _≡_ (iterTree∞ f t) (t >>=∞ K (iter∞ f))
  unfold-layer : ∀ (l : T∞F (B ⊎ A) (T∞ (B ⊎ A)))
               → NodeEq _≡_ (TreeEq∞ _≡_) (iterLayer∞ f l) (bind∞F l (K (iter∞ f)))

  force≈ (iter-unfold a) = unfold-start (f a)
  unfold-start (inj₁ b) = ret≈∞ refl
  unfold-start (inj₂ m) = unfold-root m
  unfold-root (call⁺ o x k) = call≈∞ (λ b → unfold-tree (k b))
  unfold-root (halt⁺ o x)   = halt≈∞
  force≈ (unfold-tree t) = unfold-layer (force t)
  unfold-layer (ret∞ (inj₁ b)) = ret≈∞ refl
  unfold-layer (ret∞ (inj₂ a)) = ≈reflN (iterStart∞ f (f a))
  unfold-layer (call∞ o x k)   = call≈∞ (λ b → unfold-tree (k b))
  unfold-layer (halt∞ o x)     = halt≈∞

  -- Every solution is `iter∞ f`.
  module _ (g : A → T∞ B) (hg : ∀ a → TreeEq∞ _≡_ (g a) (E g (f a))) where
    -- A tree bisimilar to a round's rest, continued by `g`, is bisimilar to the
    -- iteration's rest.
    uniq-tree : ∀ (y : T∞ B) (t : T∞ (B ⊎ A)) → TreeEq∞ _≡_ y (t >>=∞ K g) → TreeEq∞ _≡_ y (iterTree∞ f t)
    uniq-layer : ∀ (l : T∞F B (T∞ B)) (lt : T∞F (B ⊎ A) (T∞ (B ⊎ A)))
               → NodeEq _≡_ (TreeEq∞ _≡_) l (bind∞F lt (K g))
               → NodeEq _≡_ (TreeEq∞ _≡_) l (iterLayer∞ f lt)
    uniq-start : ∀ (l : T∞F B (T∞ B)) (s : B ⊎ T⁺ (B ⊎ A))
               → NodeEq _≡_ (TreeEq∞ _≡_) l (force (E g s))
               → NodeEq _≡_ (TreeEq∞ _≡_) l (iterStart∞ f s)
    uniq-root : ∀ (l : T∞F B (T∞ B)) (m : T⁺ (B ⊎ A))
              → NodeEq _≡_ (TreeEq∞ _≡_) l (bind∞F (root⁺ m) (K g))
              → NodeEq _≡_ (TreeEq∞ _≡_) l (iterRoot∞ f m)

    force≈ (uniq-tree y t h) = uniq-layer (force y) (force t) (force≈ h)
    uniq-layer l (ret∞ (inj₁ b)) n          = n
    uniq-layer l (ret∞ (inj₂ a)) n          = uniq-start l (f a) (≈transN n (force≈ (hg a)))
    uniq-layer _ (call∞ o x k)   (call≈∞ h) = call≈∞ (λ b → uniq-tree _ (k b) (h b))
    uniq-layer _ (halt∞ o x)     halt≈∞     = halt≈∞
    uniq-start l (inj₁ b) n = n
    uniq-start l (inj₂ m) n = uniq-root l m n
    uniq-root _ (call⁺ o x k) (call≈∞ h) = call≈∞ (λ b → uniq-tree _ (k b) (h b))
    uniq-root _ (halt⁺ o x)   halt≈∞     = halt≈∞

    iter-unique : ∀ a → TreeEq∞ _≡_ (g a) (iter∞ f a)
    force≈ (iter-unique a) = uniq-start (force (g a)) (f a) (force≈ (hg a))
