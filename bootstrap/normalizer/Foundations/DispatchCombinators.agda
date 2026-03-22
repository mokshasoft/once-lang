------------------------------------------------------------------------
-- DispatchCombinators: Proof combinators for TermF position dispatch
--
-- This module provides reusable combinators for the common patterns
-- in is-id-pos-N and nstep-at-N proofs:
--
--   1. assoc-l-under: Left-associate and apply a reduction under ∘
--   2. reassoc-inr: Reassociate under inr on the right
--   3. reassoc-inr-In: Reassociate under inr ∘ In on the right
--
-- These factor out the repetitive `⟶1 assoc-l >> ⟶1 (⟶-∘-l X)` and
-- `∘-cong-right' inr (⟶1 assoc-r >> ...)` patterns.
------------------------------------------------------------------------

module normalizer.Foundations.DispatchCombinators where

open import normalizer.Foundations.ReductionCombinators public
open import normalizer.Foundations.Catamorphisms
  using (∘-cong-right'; ∘-cong-left')

open import normalizer.Foundations.CCC
  using (_∘_; inl; inr; In; assoc-l; assoc-r; ⟶-∘-l; [_,_]; ⟦_⟧F; μ_)

------------------------------------------------------------------------
-- Left-association combinator
--
-- Common pattern: left-associate and apply a single-step reduction
-- under composition on the left side.
--
-- Given:  f ∘ (g ∘ h)   and   r : (f ∘ g) ⟶ f'
-- Result: f' ∘ h
--
--   f ∘ (g ∘ h)
--   ⟶ (f ∘ g) ∘ h      [assoc-l]
--   ⟶ f' ∘ h           [⟶-∘-l r]
------------------------------------------------------------------------

-- assoc-l : f ∘ (g ∘ h) ⟶ (f ∘ g) ∘ h
-- We want: after assoc-l, apply r : (f ∘ g) ⟶ f' under ∘ on the left
assoc-l-under : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} {f' : Term B D} →
                ((f ∘ g) ⟶ f') →
                (f ∘ (g ∘ h)) ⟶* (f' ∘ h)
assoc-l-under r = ⟶1 assoc-l >> ⟶1 (⟶-∘-l r)

------------------------------------------------------------------------
-- Right-congruence under inr
--
-- Common pattern: apply a reduction under `inr ∘ _` on the right.
--
-- Given:  g ⟶* g'
-- Result: (inr ∘ g) ⟶* (inr ∘ g')
--
-- Note: inr {A} {B} : Term B (A + B)
------------------------------------------------------------------------

under-inr : ∀ {X A B} {g g' : Term X B} →
            (g ⟶* g') →
            (inr {A} {B} ∘ g) ⟶* (inr ∘ g')
under-inr = ∘-cong-right' inr

------------------------------------------------------------------------
-- Right-congruence under In
------------------------------------------------------------------------

under-In : ∀ {F X} {h h' : Term X (⟦ F ⟧F (μ_ F))} →
           (h ⟶* h') →
           (In {F} ∘ h) ⟶* (In ∘ h')
under-In = ∘-cong-right' In

------------------------------------------------------------------------
-- Common proof step: navigate one level through case-inr
--
-- This encapsulates the very common pattern:
--   ⟶1 assoc-l >> ⟶1 (⟶-∘-l case-inr)
--
-- Which appears in every is-id-pos-N proof.
--
-- Given: [ f , g ] ∘ (inr ∘ t)
-- Result: g ∘ t
------------------------------------------------------------------------

open import normalizer.Foundations.CCC using (case-inr; case-inl)

-- [ f , g ] ∘ (inr ∘ t) ⟶* g ∘ t
step-case-inr : ∀ {A B C R} {f : Term B R} {g : Term C R} {t : Term A C} →
                ([ f , g ] ∘ (inr ∘ t)) ⟶* (g ∘ t)
step-case-inr = assoc-l-under case-inr

-- [ f , g ] ∘ (inl ∘ t) ⟶* f ∘ t
step-case-inl : ∀ {A B C R} {f : Term B R} {g : Term C R} {t : Term A B} →
                ([ f , g ] ∘ (inl ∘ t)) ⟶* (f ∘ t)
step-case-inl = assoc-l-under case-inl

------------------------------------------------------------------------
-- Associativity sandwich combinator
--
-- Very common pattern (118+ occurrences in RefoldIdempotent):
--   ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' t r) (step assoc-r done))
--
-- Given: (f ∘ g) ⟶* (h ∘ k)
-- Returns: f ∘ (g ∘ t) ⟶* h ∘ (k ∘ t)
--
-- Steps:
--   f ∘ (g ∘ t)
--   ⟶ (f ∘ g) ∘ t       [assoc-l]
--   ⟶* (h ∘ k) ∘ t      [∘-cong-left' t r]
--   ⟶ h ∘ (k ∘ t)       [assoc-r]
------------------------------------------------------------------------

assoc-sandwich : ∀ {A B C D E} {f : Term C D} {g : Term B C} {h : Term E D} {k : Term B E}
                 (t : Term A B) →
                 ((f ∘ g) ⟶* (h ∘ k)) →
                 (f ∘ (g ∘ t)) ⟶* (h ∘ (k ∘ t))
assoc-sandwich t r = ⟶*-trans (step assoc-l done) (⟶*-trans (∘-cong-left' t r) (step assoc-r done))

------------------------------------------------------------------------
-- Right-reassociation chain helpers
--
-- Pattern in is-id-pos-N proofs:
--   ⟶1 assoc-r >> ∘-cong-right' inr (⟶1 assoc-r >> ∘-cong-right' In (...))
--
-- reassoc-under-inr: Right-associate and continue under inr
-- reassoc-under-In: Right-associate and continue under In
------------------------------------------------------------------------

-- f ∘ (g ∘ h) ⟶* f ∘ result, where (g ∘ h) ⟶* result via assoc-r and inner reduction
reassoc-under-inr : ∀ {X A B C} {g : Term B C} {h : Term X B} {result : Term X C} →
                    ((g ∘ h) ⟶* result) →
                    (inr {A} ∘ (g ∘ h)) ⟶* (inr ∘ result)
reassoc-under-inr inner = ∘-cong-right' inr inner

reassoc-under-In : ∀ {F X} {g : Term X (⟦ F ⟧F (μ_ F))} {result : Term X (⟦ F ⟧F (μ_ F))} →
                   (g ⟶* result) →
                   (In {F} ∘ g) ⟶* (In ∘ result)
reassoc-under-In inner = ∘-cong-right' In inner
