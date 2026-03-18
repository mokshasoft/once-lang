------------------------------------------------------------------------
-- Once.Optimizer.Depth
--
-- Depth of Once IR terms.
-- Used to bound the completeness proof - we prove completeness
-- for all terms up to depth N.
------------------------------------------------------------------------

module Once.Optimizer.Depth where

open import Once.Type
open import Once.CCC.IR

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; _<_; _≤?_)
open import Data.Nat as ℕ using () renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ⊔-comm; ⊔-assoc; n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Depth: Structural depth of IR terms
------------------------------------------------------------------------

-- | Depth of an IR term
--
-- Measures the nesting depth of compositions and constructors.
-- Generators (id, fst, snd, inl, inr, etc.) have depth 0.
-- Compositions and compound forms add 1 to max subterm depth.
--
depth : ∀ {A B} → IR A B → ℕ
depth id            = 0
depth (g ∘ f)       = suc (depth g ⊔ depth f)
depth fst           = 0
depth snd           = 0
depth (⟨ f , g ⟩ _) = suc (depth f ⊔ depth g)
depth (inl _)       = 0
depth (inr _)       = 0
depth (case f g)     = suc (depth f ⊔ depth g)
depth terminal      = 0
depth initial       = 0
depth (curry f _)   = suc (depth f)
depth apply         = 0
depth (fold _)          = 0
depth unfold        = 0
depth arr           = 0
depth (Prim _)      = 0

------------------------------------------------------------------------
-- Bounded depth predicate
------------------------------------------------------------------------

-- | Term has depth at most n
Bounded : ∀ {A B} → ℕ → IR A B → Set
Bounded n t = depth t ≤ n

-- | Decidability of bounded depth
bounded? : ∀ {A B} (n : ℕ) (t : IR A B) → Dec (Bounded n t)
bounded? n t = depth t ≤? n

------------------------------------------------------------------------
-- Properties of depth
------------------------------------------------------------------------

-- | Generators have depth 0
depth-id : depth {A = Unit} id ≡ 0
depth-id = refl

depth-fst : ∀ {A B} → depth (fst {A} {B}) ≡ 0
depth-fst = refl

depth-snd : ∀ {A B} → depth (snd {A} {B}) ≡ 0
depth-snd = refl

-- | Subterms have smaller depth
depth-∘-left : ∀ {A B C} (g : IR B C) (f : IR A B) →
  depth g ≤ depth (g ∘ f)
depth-∘-left g f = ≤-trans (m≤m⊔n (depth g) (depth f)) (n≤1+n _)

depth-∘-right : ∀ {A B C} (g : IR B C) (f : IR A B) →
  depth f ≤ depth (g ∘ f)
depth-∘-right g f = ≤-trans (m≤n⊔m (depth g) (depth f)) (n≤1+n _)

depth-pair-left : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) →
  depth f ≤ depth (⟨ f , g ⟩ m)
depth-pair-left f g m = ≤-trans (m≤m⊔n (depth f) (depth g)) (n≤1+n _)

depth-pair-right : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) →
  depth g ≤ depth (⟨ f , g ⟩ m)
depth-pair-right f g m = ≤-trans (m≤n⊔m (depth f) (depth g)) (n≤1+n _)

depth-case-left : ∀ {A B C} (f : IR A C) (g : IR B C) →
  depth f ≤ depth (case f g)
depth-case-left f g = ≤-trans (m≤m⊔n (depth f) (depth g)) (n≤1+n _)

depth-case-right : ∀ {A B C} (f : IR A C) (g : IR B C) →
  depth g ≤ depth (case f g)
depth-case-right f g = ≤-trans (m≤n⊔m (depth f) (depth g)) (n≤1+n _)

depth-curry : ∀ {A B C q} (f : IR (A * B) C) (m : AllocMode) →
  depth f ≤ depth (curry {q = q} f m)
depth-curry f m = n≤1+n (depth f)
