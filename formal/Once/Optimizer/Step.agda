------------------------------------------------------------------------
-- Once.Optimizer.Step
--
-- One-step reduction relation for IR composition optimization.
-- Properties are proven for one step, then lifted to the reflexive-
-- transitive closure (star).
--
-- This approach avoids fuel-based recursion which causes type-level
-- dependencies that cascade through proofs.
------------------------------------------------------------------------

module Once.Optimizer.Step where

open import Once.Type
open import Once.IR
open import Once.Semantics using (eval; ⟦_⟧)
open import Once.Optimizer.Cost using (cost)

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat as ℕ using () renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m≤m+n; m≤n+m)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- One-Step Composition Reduction
--
-- Each constructor represents one rewrite rule for g ∘ f.
-- The result is the optimized term.
------------------------------------------------------------------------

data ComposeStep : ∀ {A B C} → IR B C → IR A B → IR A C → Set where
  -- Identity laws
  step-id-left  : ∀ {A B} {f : IR A B} →
                  ComposeStep id f f
  step-id-right : ∀ {A B} {g : IR A B} →
                  ComposeStep g id g

  -- Product beta
  step-fst-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                  ComposeStep fst (⟨ f , g ⟩ m) f
  step-snd-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                  ComposeStep snd (⟨ f , g ⟩ m) g

  -- Coproduct beta
  step-case-inl : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                  ComposeStep [ f , g ] (inl m) f
  step-case-inr : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                  ComposeStep [ f , g ] (inr m) g

  -- Exponential beta: apply ∘ ⟨ curry f , g ⟩ = f ∘ ⟨ id , g ⟩
  step-apply-curry : ∀ {A B C q} {f : IR (A * B) C} {g : IR A B} {m₁ m₂} →
                     ComposeStep apply (⟨ curry {q = q} f m₁ , g ⟩ m₂) (f ∘ ⟨ id , g ⟩ Heap)

  -- Fixed point laws
  step-fold-unfold : ∀ {F} →
                     ComposeStep (fold {F}) unfold id
  step-unfold-fold : ∀ {F} →
                     ComposeStep (unfold {F}) fold id
  step-fold-unfold-f : ∀ {A F} {f : IR A (Fix F)} →
                       ComposeStep fold (unfold ∘ f) f
  step-unfold-fold-f : ∀ {A F} {f : IR A (Fix F)} →
                       ComposeStep unfold (fold ∘ f) f

  -- Dead code elimination: terminal ∘ f = terminal
  step-terminal : ∀ {A B} {f : IR A B} →
                  ComposeStep terminal f terminal

  -- Initial absorption: g ∘ initial = initial
  step-initial : ∀ {B C} {g : IR B C} →
                 ComposeStep g initial initial

  -- Associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f)
  -- This allows nested compositions to be optimized
  step-assoc : ∀ {A B C D} {h : IR C D} {g : IR B C} {f : IR A B} {gf : IR A C} →
               ComposeStep g f gf →
               ComposeStep (h ∘ g) f (h ∘ gf)

------------------------------------------------------------------------
-- Reflexive-Transitive Closure (Star)
------------------------------------------------------------------------

mutual
  -- | Zero or more composition steps
  data ComposeSteps : ∀ {A B C} → IR B C → IR A B → IR A C → Set where
    -- Zero steps: just compose
    done : ∀ {A B C} {g : IR B C} {f : IR A B} →
           ComposeSteps g f (g ∘ f)

    -- One or more steps
    step : ∀ {A B C} {g : IR B C} {f : IR A B} {r r' : IR A C} →
           ComposeStep g f r →
           ComposeSteps′ r r' →
           ComposeSteps g f r'

  -- | Steps within a single term (for recursive optimization)
  data ComposeSteps′ : ∀ {A B} → IR A B → IR A B → Set where
    refl′ : ∀ {A B} {t : IR A B} → ComposeSteps′ t t

    -- Optimize within a composition
    in-compose : ∀ {A B C} {g : IR B C} {f : IR A B} {r : IR A C} →
                 ComposeSteps g f r →
                 ComposeSteps′ (g ∘ f) r

------------------------------------------------------------------------
-- Properties: One-Step Preserves Semantics
------------------------------------------------------------------------

step-preserves-semantics : ∀ {A B C} {g : IR B C} {f : IR A B} {r : IR A C} →
  ComposeStep g f r → (x : ⟦ A ⟧) → eval r x ≡ eval (g ∘ f) x

step-preserves-semantics step-id-left x = refl
step-preserves-semantics step-id-right x = refl
step-preserves-semantics step-fst-pair x = refl
step-preserves-semantics step-snd-pair x = refl
step-preserves-semantics step-case-inl x = refl
step-preserves-semantics step-case-inr x = refl
step-preserves-semantics step-apply-curry x = refl
step-preserves-semantics step-fold-unfold x = refl
step-preserves-semantics step-unfold-fold x = refl
step-preserves-semantics step-fold-unfold-f x = refl
step-preserves-semantics step-unfold-fold-f x = refl
step-preserves-semantics step-terminal x = refl
step-preserves-semantics step-initial x = ⊥-elim x
step-preserves-semantics (step-assoc {h = h} inner) x =
  cong (eval h) (step-preserves-semantics inner x)

------------------------------------------------------------------------
-- Properties: One-Step Reduces Cost
------------------------------------------------------------------------

-- Helper: a ≤ suc (a + b)
a≤suc-a+b : ∀ a b → a ≤ suc (a ℕ+ b)
a≤suc-a+b a b = ≤-trans (m≤m+n a b) (n≤1+n (a ℕ+ b))

-- Helper: b ≤ suc (a + b)
b≤suc-a+b : ∀ a b → b ≤ suc (a ℕ+ b)
b≤suc-a+b a b = ≤-trans (m≤n+m b a) (n≤1+n (a ℕ+ b))

step-reduces-cost : ∀ {A B C} {g : IR B C} {f : IR A B} {r : IR A C} →
  ComposeStep g f r → cost r ≤ cost g ℕ+ cost f

step-reduces-cost step-id-left = ≤-refl
step-reduces-cost (step-id-right {g = g}) =
  subst (cost g ≤_) (sym (Data.Nat.Properties.+-identityʳ (cost g))) ≤-refl
  where open import Data.Nat.Properties
step-reduces-cost (step-fst-pair {f = f} {g = g}) = a≤suc-a+b (cost f) (cost g)
step-reduces-cost (step-snd-pair {f = f} {g = g}) = b≤suc-a+b (cost f) (cost g)
step-reduces-cost (step-case-inl {f = f} {g = g}) =
  ≤-trans (m≤m+n (cost f) (cost g)) (m≤m+n (cost f ℕ+ cost g) 1)
step-reduces-cost (step-case-inr {f = f} {g = g}) =
  ≤-trans (m≤n+m (cost g) (cost f)) (m≤m+n (cost f ℕ+ cost g) 1)
step-reduces-cost (step-apply-curry {f = f} {g = g}) =
  -- cost (f ∘ ⟨ id , g ⟩) = cost f + 1 + cost g
  -- cost (apply ∘ ⟨ curry f , g ⟩) = 0 + 1 + (1 + cost f) + cost g = 2 + cost f + cost g
  let open Data.Nat.Properties
      eq : cost f ℕ+ suc (cost g) ≡ suc (cost f ℕ+ cost g)
      eq = trans (+-comm (cost f) (suc (cost g))) (cong suc (+-comm (cost g) (cost f)))
  in subst (_≤ suc (suc (cost f ℕ+ cost g))) (sym eq) (s≤s (n≤1+n (cost f ℕ+ cost g)))
step-reduces-cost step-fold-unfold = z≤n
step-reduces-cost step-unfold-fold = z≤n
step-reduces-cost (step-fold-unfold-f {f = f}) = n≤1+n (cost f)
step-reduces-cost (step-unfold-fold-f {f = f}) = n≤1+n (cost f)
step-reduces-cost step-terminal = z≤n
step-reduces-cost step-initial = z≤n
step-reduces-cost (step-assoc {h = h} {g = g} {f = f} {gf = gf} inner) =
  -- cost (h ∘ gf) = cost h + cost gf
  -- cost gf ≤ cost g + cost f (by IH)
  -- cost (h ∘ g) = cost h + cost g
  -- Need: cost h + cost gf ≤ (cost h + cost g) + cost f
  let ih = step-reduces-cost inner
      open Data.Nat.Properties
      -- cost h + cost gf ≤ cost h + (cost g + cost f) by IH
      step1 : cost h ℕ+ cost gf ≤ cost h ℕ+ (cost g ℕ+ cost f)
      step1 = +-monoʳ-≤ (cost h) ih
      -- cost h + (cost g + cost f) = (cost h + cost g) + cost f by assoc
      step2 : cost h ℕ+ (cost g ℕ+ cost f) ≡ (cost h ℕ+ cost g) ℕ+ cost f
      step2 = sym (+-assoc (cost h) (cost g) (cost f))
  in subst (cost h ℕ+ cost gf ≤_) step2 step1

------------------------------------------------------------------------
-- Properties: Star Preserves Semantics
------------------------------------------------------------------------

steps-preserves-semantics : ∀ {A B C} {g : IR B C} {f : IR A B} {r : IR A C} →
  ComposeSteps g f r → (x : ⟦ A ⟧) → eval r x ≡ eval (g ∘ f) x

steps′-preserves-semantics : ∀ {A B} {t t' : IR A B} →
  ComposeSteps′ t t' → (x : ⟦ A ⟧) → eval t' x ≡ eval t x

steps-preserves-semantics done x = refl
steps-preserves-semantics (step s rest) x =
  trans (steps′-preserves-semantics rest x) (step-preserves-semantics s x)

steps′-preserves-semantics refl′ x = refl
steps′-preserves-semantics (in-compose steps) x = steps-preserves-semantics steps x

------------------------------------------------------------------------
-- Properties: Star Reduces Cost
------------------------------------------------------------------------

steps-reduces-cost : ∀ {A B C} {g : IR B C} {f : IR A B} {r : IR A C} →
  ComposeSteps g f r → cost r ≤ cost g ℕ+ cost f

steps′-reduces-cost : ∀ {A B} {t t' : IR A B} →
  ComposeSteps′ t t' → cost t' ≤ cost t

steps-reduces-cost done = ≤-refl
steps-reduces-cost (step s rest) =
  ≤-trans (steps′-reduces-cost rest) (step-reduces-cost s)

steps′-reduces-cost refl′ = ≤-refl
steps′-reduces-cost (in-compose steps) = steps-reduces-cost steps

------------------------------------------------------------------------
-- Optimizer produces valid step sequence
--
-- This connects the declarative step relation to the actual optimizer.
-- We postulate this for now - it can be proven by case analysis on
-- optimize-compose matching the step constructors.
------------------------------------------------------------------------

open import Once.Optimize using (optimize-compose)

postulate
  optimize-compose-steps : ∀ {A B C} (g : IR B C) (f : IR A B) →
    ComposeSteps g f (optimize-compose g f)

------------------------------------------------------------------------
-- Main theorems derived from step properties
------------------------------------------------------------------------

-- | optimize-compose preserves semantics
optimize-compose-correct′ : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧) →
  eval (optimize-compose g f) x ≡ eval (g ∘ f) x
optimize-compose-correct′ g f x = steps-preserves-semantics (optimize-compose-steps g f) x

-- | optimize-compose reduces cost
optimize-compose-cost′ : ∀ {A B C} (g : IR B C) (f : IR A B) →
  cost (optimize-compose g f) ≤ cost g ℕ+ cost f
optimize-compose-cost′ g f = steps-reduces-cost (optimize-compose-steps g f)
