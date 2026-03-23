------------------------------------------------------------------------
-- Correctness.Preserves: Semantic preservation proof
--
-- Parameterized by normalize, normalize-preserves-semantics, and confluence.
-- No heavy imports - type-checks fast.
------------------------------------------------------------------------

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Encoding.Encoding
  using (TermCode')
open import normalizer.Combinators.ReductionCombinators
  using (_>>_; done)

module normalizer.Theory.GeneralCorrectness.Preserves
  (normalize : Term TermCode' TermCode')
  (normalize-preserves-semantics : ∀ (t : Term Unit TermCode') →
                                   ((normalize ∘ t) ⟶* t) ⊎ (t ⟶* (normalize ∘ t)))
  (confluence : ∀ {A B} {t u v : Term A B} →
                t ⟶* u → t ⟶* v →
                ∃[ w ] ((u ⟶* w) × (v ⟶* w)))
  where

------------------------------------------------------------------------
-- Semantic preservation proof
------------------------------------------------------------------------

-- The normalized result is equivalent to the input.
-- Uses confluence and >> for flat proof composition.
abstract
  normalize-preserves : ∀ (t : Term Unit TermCode') →
                        ∀ {result} → (normalize ∘ t) ⟶* result →
                        ∃[ nf ] ((t ⟶* nf) × (result ⟶* nf))
  normalize-preserves t {result} reduction with normalize-preserves-semantics t
  ... | inj₁ norm→t with confluence reduction norm→t
    -- (normalize ∘ t) ⟶* t
    -- We have: (normalize ∘ t) ⟶* result and (normalize ∘ t) ⟶* t
    -- By confluence: result and t reduce to common w
  ...   | w , (result→w , t→w) = w , (t→w , result→w)
  normalize-preserves t {result} reduction | inj₂ t→norm =
    -- t ⟶* (normalize ∘ t)
    -- result is reachable from (normalize ∘ t), which is reachable from t
    -- Using >> for flat composition instead of nested ⟶*-trans
    result , ((t→norm >> reduction) , done)
