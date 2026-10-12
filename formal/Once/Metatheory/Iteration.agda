-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Iteration — guarded iteration is the UNIQUE solution of
-- its equation (`Spec.Metatheory.Recursion`, D311, plan 0.117 D2).
--
-- `iter∞ f` satisfies `x a ≈ toT∞ (f a) >>=∞ [ return∞ , x ]` (`iter-unfold`),
-- and every `g` that does is bisimilar to it (`iter-unique`). Uniqueness is
-- where the guard is used: `f a` begins with an event, so a solution's first
-- node is fixed by the equation before it has to look at itself again, and the
-- bisimulation is built one event at a time. Without the guard `x = x` would
-- be an instance, and every tree would solve it.
------------------------------------------------------------------------

module Once.Metatheory.Iteration where

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.Denotation.TraceMonad using (T; ret; call; halt)
open import Once.Spec.Guarded using (T⁺; call⁺; halt⁺; forget⁺; iter∞; iterRoot∞; iterTree∞)
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

module _ {A B : Set} (f : A → T⁺ (B ⊎ A)) where

  -- One round, then stop or loop.
  K : (A → T∞ B) → B ⊎ A → T∞ B
  K x = [ return∞ , x ]′

  -- `iter∞ f` solves it.
  iter-unfold : ∀ a → TreeEq∞ _≡_ (iter∞ f a) (embed (forget⁺ (f a)) >>=∞ K (iter∞ f))
  unfold-root : ∀ (m : T⁺ (B ⊎ A))
              → NodeEq _≡_ (TreeEq∞ _≡_) (iterRoot∞ f m) (bind∞F (force (embed (forget⁺ m))) (K (iter∞ f)))
  unfold-tree : ∀ (t : T (B ⊎ A)) → TreeEq∞ _≡_ (iterTree∞ f t) (embed t >>=∞ K (iter∞ f))
  unfold-treeN : ∀ (t : T (B ⊎ A))
               → NodeEq _≡_ (TreeEq∞ _≡_) (force (iterTree∞ f t)) (force (embed t >>=∞ K (iter∞ f)))

  force≈ (iter-unfold a) = unfold-root (f a)
  unfold-root (call⁺ o x k) = call≈∞ (λ b → unfold-tree (k b))
  unfold-root (halt⁺ o x)   = halt≈∞
  force≈ (unfold-tree t) = unfold-treeN t
  unfold-treeN (ret (inj₁ b)) = ret≈∞ refl
  unfold-treeN (ret (inj₂ a)) = ≈reflN (iterRoot∞ f (f a))
  unfold-treeN (call o x k)   = call≈∞ (λ b → unfold-tree (k b))
  unfold-treeN (halt o x)     = halt≈∞

  -- Every solution is `iter∞ f`.
  module _ (g : A → T∞ B) (hg : ∀ a → TreeEq∞ _≡_ (g a) (embed (forget⁺ (f a)) >>=∞ K g)) where
    -- A tree bisimilar to a round's rest, continued by `g`, is bisimilar to the
    -- iteration's rest.
    uniq-tree : ∀ (y : T∞ B) (t : T (B ⊎ A)) → TreeEq∞ _≡_ y (embed t >>=∞ K g) → TreeEq∞ _≡_ y (iterTree∞ f t)
    uniq-treeN : ∀ (l : T∞F B (T∞ B)) (t : T (B ⊎ A))
               → NodeEq _≡_ (TreeEq∞ _≡_) l (force (embed t >>=∞ K g))
               → NodeEq _≡_ (TreeEq∞ _≡_) l (force (iterTree∞ f t))
    uniq-root : ∀ (l : T∞F B (T∞ B)) (m : T⁺ (B ⊎ A))
              → NodeEq _≡_ (TreeEq∞ _≡_) l (bind∞F (force (embed (forget⁺ m))) (K g))
              → NodeEq _≡_ (TreeEq∞ _≡_) l (iterRoot∞ f m)

    force≈ (uniq-tree y t h) = uniq-treeN (force y) t (force≈ h)
    uniq-treeN l (ret (inj₁ b)) n          = n
    uniq-treeN l (ret (inj₂ a)) n          = uniq-root l (f a) (≈transN n (force≈ (hg a)))
    uniq-treeN _ (call o x k)   (call≈∞ h) = call≈∞ (λ b → uniq-tree _ (k b) (h b))
    uniq-treeN _ (halt o x)     halt≈∞     = halt≈∞
    uniq-root _ (call⁺ o x k) (call≈∞ h) = call≈∞ (λ b → uniq-tree _ (k b) (h b))
    uniq-root _ (halt⁺ o x)   halt≈∞     = halt≈∞

    iter-unique : ∀ a → TreeEq∞ _≡_ (g a) (iter∞ f a)
    force≈ (iter-unique a) = uniq-root (force (g a)) (f a) (force≈ (hg a))
