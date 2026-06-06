------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.Commute12
--
-- Elementary commutation of ⟹₁ and ⟹₂.
--
--   Commute ⟹₁ ⟹₂ : t ⟹₁ u → t ⟹₂ v → ∃ w. v ⟹₁ w ∧ u ⟹₂ w.
--
-- Together with Diamond ⟹₁ (Diamond1) and Diamond ⟹₂ (Diamond2), this
-- is the third hypothesis of Theory.Derived.HindleyRosen.hindley-rosen.
--
-- INFORMAL ARGUMENT.
--   ⟹₁ fires β/η/s rules and structural congruences; ⟹₂ fires
--   eta-pair-gen and structural congruences.  When both step from t,
--   they target either disjoint positions (commute trivially via
--   congruence) or overlapping positions.
--
--   The genuinely overlapping case is when t contains an
--   ⟨ fst ∘ h , snd ∘ h ⟩ subterm that the ⟹₂ step rewrites to (some
--   reduct of) h while the ⟹₁ step also reduces inside that subterm.
--   Three sub-cases:
--
--     (i) ⟹₁ acts on h (inside both copies symmetrically via
--         ⟹₁-⟨,⟩ + ⟹₁-∘ congruence): commute by Diamond on h-component.
--
--     (ii) ⟹₁ acts on h on ONLY ONE side (e.g. left): the ⟹₂-fired
--          reduct is some h-reduct h'; the ⟹₁-fired reduct is
--          ⟨ fst ∘ h₁' , snd ∘ h ⟩ with h₁' = h-with-rule-fired-on-left.
--          The two close at ⟨ fst ∘ w , snd ∘ w ⟩-type witness or at h's
--          common reduct.
--
--     (iii) ⟹₁ acts on positions OUTSIDE the eta-pair-gen redex,
--          e.g. firing curry-β on a surrounding context: the
--          eta-pair-gen redex is preserved (or duplicated, or deleted)
--          and the commute closes by re-firing eta-pair-gen on the
--          ⟹₁-resulting term.
--
--   Each sub-case is mechanical but the cross-product with all
--   ⟹₁-rules is wide. Postulated for now; structure documented.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.Commute12 where

open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.ParallelReductionSplit
  using (_⟹₁_; _⟹₂_)

------------------------------------------------------------------------
-- Elementary commutation of ⟹₁ and ⟹₂.
------------------------------------------------------------------------

-- Order chosen to match Theory.Derived.HindleyRosen.Commute exactly:
--   Commute R S = ∀ {x y z} → R x y → S x z → Σ A (λ w → S y w ∧ R z w)
postulate
  commute₁₂ : ∀ {A B} {t u v : Term A B} →
              t ⟹₁ u → t ⟹₂ v →
              Σ (Term A B) (λ w → (u ⟹₂ w) ∧ (v ⟹₁ w))
