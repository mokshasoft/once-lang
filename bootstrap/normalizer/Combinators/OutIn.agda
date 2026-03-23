------------------------------------------------------------------------
-- OutIn: Out/In composition lemmas and associativity helpers
--
-- This module provides reusable lemmas for working with Out/In
-- compositions and repeated associativity for chain proofs.
------------------------------------------------------------------------

module normalizer.Combinators.OutIn where

open import normalizer.Encoding.Catamorphisms public

------------------------------------------------------------------------
-- Out ∘ In composition helper
------------------------------------------------------------------------

-- Helper: reduce (f ∘ Out) ∘ (In ∘ body) to f ∘ body
-- This uses: assoc-r, out-in, id-left
out-in-compose : ∀ {F A B} (f : Term (⟦ F ⟧F (μ F)) B) (body : Term A (⟦ F ⟧F (μ F))) →
                 ((f ∘ Out) ∘ (In ∘ body)) ⟶* (f ∘ body)
out-in-compose {F} f body =
  ⟶*-trans (step assoc-r done)     -- f ∘ (Out ∘ (In ∘ body))
  (⟶*-trans (step (⟶-∘-r assoc-l) done)  -- f ∘ ((Out ∘ In) ∘ body)
  (⟶*-trans (step (⟶-∘-r (⟶-∘-l (out-in F))) done)  -- f ∘ (id ∘ body)
  (step (⟶-∘-r id-left) done)))  -- f ∘ body

------------------------------------------------------------------------
-- Repeated associativity helpers
------------------------------------------------------------------------

-- Helper: reassociate 3-term composition right
-- ((a ∘ b) ∘ c) ⟶* (a ∘ (b ∘ c))
abstract
  assoc-r3 : ∀ {A B C D} (a : Term C D) (b : Term B C) (c : Term A B) →
             ((a ∘ b) ∘ c) ⟶* (a ∘ (b ∘ c))
  assoc-r3 a b c = step assoc-r done

-- Helper: reassociate 4-term composition right
-- (((a ∘ b) ∘ c) ∘ d) ⟶* (a ∘ (b ∘ (c ∘ d)))
abstract
  assoc-r4 : ∀ {A B C D E} (a : Term D E) (b : Term C D) (c : Term B C) (d : Term A B) →
             (((a ∘ b) ∘ c) ∘ d) ⟶* (a ∘ (b ∘ (c ∘ d)))
  assoc-r4 a b c d =
    ⟶*-trans (step assoc-r done)   -- ((a ∘ b) ∘ c) ∘ d ⟶ (a ∘ b) ∘ (c ∘ d)
             (step assoc-r done)   -- (a ∘ b) ∘ (c ∘ d) ⟶ a ∘ (b ∘ (c ∘ d))

-- Helper: reassociate 5-term composition right
abstract
  assoc-r5 : ∀ {A B C D E F} (a : Term E F) (b : Term D E) (c : Term C D) (d : Term B C) (e : Term A B) →
             ((((a ∘ b) ∘ c) ∘ d) ∘ e) ⟶* (a ∘ (b ∘ (c ∘ (d ∘ e))))
  assoc-r5 a b c d e =
    ⟶*-trans (step assoc-r done)
    (⟶*-trans (step assoc-r done)
             (step assoc-r done))
