------------------------------------------------------------------------
-- Once.Optimizer.CostAnalysis
--
-- Analysis of when the optimizer reduces cost.
--
-- KEY FINDING: The distribution rules can INCREASE syntactic cost!
--
--   ⟨ f , g ⟩ ∘ h  →  ⟨ f ∘ h , g ∘ h ⟩
--
-- This duplicates h, increasing cost from (1 + f + g + h) to (1 + f + g + 2h).
--
-- However, distribution ENABLES beta reductions:
--   ⟨ fst , snd ⟩ ∘ h  →  ⟨ fst ∘ h , snd ∘ h ⟩  →  h  (by eta)
--
-- So the net effect depends on whether reductions fire.
--
-- This module analyzes when cost is reduced vs increased.
------------------------------------------------------------------------

module Once.Optimizer.CostAnalysis where

open import Once.Type
open import Once.IR
open import Once.Optimize
open import Once.Semantics

open import Once.Optimizer.Cost

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat as ℕ using () renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-monoˡ-≤; +-monoʳ-≤)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Beta reductions ALWAYS reduce cost
------------------------------------------------------------------------

-- | fst ∘ ⟨ f , g ⟩ → f eliminates the pair allocation AND g
beta-fst-reduces : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) →
  cost f < cost (fst ∘ ⟨ f , g ⟩ m)
beta-fst-reduces f g m = s≤s (m≤m+n (cost f) (cost g))

-- | snd ∘ ⟨ f , g ⟩ → g eliminates the pair allocation AND f
beta-snd-reduces : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) →
  cost g < cost (snd ∘ ⟨ f , g ⟩ m)
beta-snd-reduces f g m = s≤s (≤-trans (m≤m+n (cost g) 0)
                                       (+-monoˡ-≤ (cost g) (n≤1+n (cost f))))

-- | [ f , g ] ∘ inl → f eliminates case overhead AND g AND inl allocation
beta-case-inl-reduces : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) →
  cost f < cost ([ f , g ] ∘ inl m)
beta-case-inl-reduces f g m = s≤s (m≤m+n (cost f) (cost g))

-- | [ f , g ] ∘ inr → g eliminates case overhead AND f AND inr allocation
beta-case-inr-reduces : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) →
  cost g < cost ([ f , g ] ∘ inr m)
beta-case-inr-reduces f g m = s≤s (≤-trans (m≤m+n (cost g) 0)
                                           (+-monoˡ-≤ (cost g) (n≤1+n (cost f))))

-- | fold ∘ unfold → id eliminates fold allocation
beta-fold-unfold-reduces : ∀ {F} →
  cost (id {Fix F}) < cost (fold {F} ∘ unfold)
beta-fold-unfold-reduces = s≤s z≤n

-- | terminal ∘ f → terminal eliminates all of f
terminal-reduces : ∀ {A B} (f : IR A B) →
  cost (terminal {A}) ≤ cost (terminal ∘ f)
terminal-reduces f = z≤n

-- | f ∘ initial → initial eliminates all of f
initial-reduces : ∀ {A B} (f : IR A B) →
  cost (initial {B}) ≤ cost (f ∘ initial)
initial-reduces f = z≤n

------------------------------------------------------------------------
-- Eta reductions ALWAYS reduce cost
------------------------------------------------------------------------

-- | ⟨ fst , snd ⟩ → id eliminates pair allocation
eta-pair-reduces : ∀ {A B} (m : AllocMode) →
  cost (id {A * B}) < cost (⟨ fst , snd ⟩ m)
eta-pair-reduces m = s≤s z≤n

-- | [ inl , inr ] → id eliminates case and two allocations
eta-case-reduces : ∀ {A B} (m₁ m₂ : AllocMode) →
  cost (id {A + B}) < cost [ inl m₁ , inr m₂ ]
eta-case-reduces m₁ m₂ = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Distribution is now CONDITIONAL (fixed!)
------------------------------------------------------------------------

-- | HISTORICAL NOTE: Distribution USED TO increase cost when no beta fires
--
-- ⟨ id , id ⟩ ∘ ⟨ id , id ⟩
--   cost = (1 + 0 + 0) + (1 + 0 + 0) = 2
--
-- OLD optimizer distributed unconditionally:
-- ⟨ id ∘ ⟨ id , id ⟩ , id ∘ ⟨ id , id ⟩ ⟩
--   = ⟨ ⟨ id , id ⟩ , ⟨ id , id ⟩ ⟩  (by id ∘ f = f)
--   cost = 1 + (1 + 0 + 0) + (1 + 0 + 0) = 3
--
-- Cost INCREASED from 2 to 3!
--
-- FIXED: The optimizer now only distributes when it enables a beta:
--   wants-pair id = false, so ⟨ id , id ⟩ ∘ h stays as ⟨ id , id ⟩ ∘ h
--
-- With the fix, optimize-once-cost-≤ IS provable!

------------------------------------------------------------------------
-- When does distribution help?
------------------------------------------------------------------------

-- Distribution helps when it ENABLES a beta reduction.
--
-- Example: ⟨ fst , snd ⟩ ∘ h
--   → ⟨ fst ∘ h , snd ∘ h ⟩
--   → h  (by eta, if optimize-pair recognizes the pattern)
--
-- But optimize-compose does distribution BEFORE optimize-pair runs!
-- So the eta doesn't fire in the same pass.
--
-- In optimize-once:
--   optimize-once (⟨ fst , snd ⟩ ∘ h)
--   = optimize-compose (optimize-once ⟨ fst , snd ⟩) (optimize-once h)
--   = optimize-compose (optimize-pair fst snd) h'
--   = optimize-compose id h'  (eta fires in optimize-pair!)
--   = h'
--
-- So the eta fires BEFORE distribution, avoiding the cost increase.

-- | When subterms are already optimal, distribution might not help
--
-- The key insight: distribution is only beneficial when it exposes
-- a beta reduction. If no beta reduction is possible, distribution
-- makes things worse.

------------------------------------------------------------------------
-- What we CAN prove
------------------------------------------------------------------------

-- 1. Beta reductions always reduce cost (proven above)
-- 2. Eta reductions always reduce cost (proven above)
-- 3. Identity elimination preserves cost
-- 4. Terminal/initial absorption reduces cost

-- What we CANNOT prove with current optimizer:
-- - optimize-once-cost-≤ : single pass never increases cost
--   (counterexample: distribution without beta)

-- What we MIGHT be able to prove:
-- - For terms in "beta-normal form", optimize preserves cost
-- - For BCC terms, optimize reaches a canonical form with minimal cost
--   (this requires coherence, not optimize-once-cost-≤)

------------------------------------------------------------------------
-- Alternative: Prove for beta-normal inputs
------------------------------------------------------------------------

-- | A term is beta-normal if no beta reductions apply
--   (no fst/snd composed with pairs, no case composed with inl/inr, etc.)
--
-- For beta-normal terms, the optimizer might still distribute,
-- but if no further reductions are possible, iterating will
-- eventually stabilize.

-- This is complex to formalize. For now, we note:
-- The BCC completeness proof via COHERENCE doesn't need optimize-once-cost-≤.
-- It only needs: equivalent BCC terms optimize to the same result.

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- The optimizer's distribution rules can increase syntactic cost.
-- This is intentional: distribution exposes beta reductions.
--
-- For completeness, we use coherence (not cost monotonicity):
--   1. Equivalent BCC terms have the same canonical form
--   2. The optimizer computes the canonical form
--   3. Therefore cost(optimize t) = cost(optimize t') for t ≈ t'
--   4. Combined with cost(optimize t') ≤ cost t' for CANONICAL t',
--      we get cost(optimize t) ≤ cost t'
--
-- The key is that canonical/normal forms don't get worse under optimize.
