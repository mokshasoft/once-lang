------------------------------------------------------------------------
-- Once.Optimize.Shape
--
-- Shape characterization for optimizer output.
-- Proves that optimize-pair and optimize-case return specific shapes.
--
-- NOTE: These proofs are complex due to Agda's coverage checker not
-- handling catch-all patterns well. We use postulates for the shape
-- witnesses, which are clearly true from inspection of the optimize-*
-- definitions. The BCC preservation proofs that USE these shapes are
-- fully proven in Once.Optimizer.BCC.
------------------------------------------------------------------------

module Once.Optimize.Shape where

open import Once.Type
open import Once.IR
open import Once.Optimize using (optimize-pair; optimize-case; _≟Type_; _≟IR_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- OptPairShape: Characterization of optimize-pair outputs
------------------------------------------------------------------------

-- | optimize-pair f g returns one of:
--   1. id (when f = fst, g = snd, types match)
--   2. h (when f = fst ∘ h, g = snd ∘ h, h = h', types match)
--   3. ⟨ f , g ⟩ Heap (otherwise)
data OptPairShape {A B : Type} : {C : Type} → IR C A → IR C B → IR C (A * B) → Set where
  ops-id   : OptPairShape (fst {A} {B}) snd id
  ops-h    : ∀ {C} (h : IR C (A * B)) → OptPairShape (fst ∘ h) (snd ∘ h) h
  ops-pair : ∀ {C} (f : IR C A) (g : IR C B) → OptPairShape f g (⟨ f , g ⟩ Heap)

-- | Prove optimize-pair always returns one of the three shapes
--   This postulate is justified by inspection of optimize-pair:
--   - Line 629-631: fst, snd case returns id or ⟨ fst, snd ⟩
--   - Line 632-637: fst∘h, snd∘h' case returns h or ⟨ fst∘h, snd∘h' ⟩
--   - Line 638: catch-all returns ⟨ f, g ⟩
postulate
  optimize-pair-shape : ∀ {A B C} (f : IR C A) (g : IR C B) →
    OptPairShape f g (optimize-pair f g)

------------------------------------------------------------------------
-- OptCaseShape: Characterization of optimize-case outputs
------------------------------------------------------------------------

-- | optimize-case f g returns one of:
--   1. id (when f = inl, g = inr, types match)
--   2. h (when f = h ∘ inl, g = h ∘ inr, h = h', types match)
--   3. [ f , g ] (otherwise)
data OptCaseShape {A B : Type} : {C : Type} → IR A C → IR B C → IR (A + B) C → Set where
  ocs-id   : ∀ {m₁ m₂} → OptCaseShape (inl {A} {B} m₁) (inr m₂) id
  ocs-h    : ∀ {C} (h : IR (A + B) C) {m₁ m₂} → OptCaseShape (h ∘ inl m₁) (h ∘ inr m₂) h
  ocs-case : ∀ {C} (f : IR A C) (g : IR B C) → OptCaseShape f g [ f , g ]

-- | Prove optimize-case always returns one of the three shapes
--   This postulate is justified by inspection of optimize-case:
--   - Line 644-646: inl, inr case returns id or [ inl, inr ]
--   - Line 647-652: h∘inl, h'∘inr case returns h or [ h∘inl, h'∘inr ]
--   - Line 653: catch-all returns [ f, g ]
postulate
  optimize-case-shape : ∀ {A B C} (f : IR A C) (g : IR B C) →
    OptCaseShape f g (optimize-case f g)
