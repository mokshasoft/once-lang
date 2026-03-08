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
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m≤m+n; m≤n+m; +-identityˡ; +-identityʳ; +-assoc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool; true; false)

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
  step-unfold-fold-f : ∀ {A F} {f : IR A F} →
                       ComposeStep unfold (fold ∘ f) f

  -- Dead code elimination: terminal ∘ f = terminal
  step-terminal : ∀ {A B} {f : IR A B} →
                  ComposeStep terminal f terminal

  -- Initial absorption: g ∘ initial = initial
  step-initial : ∀ {B C} {g : IR B C} →
                 ComposeStep g initial initial

  -- Associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f)
  -- This is the pure associativity step (no inner reduction)
  step-assoc-pure : ∀ {A B C D} {h : IR C D} {g : IR B C} {f : IR A B} →
                    ComposeStep (h ∘ g) f (h ∘ (g ∘ f))

  -- Associativity with inner reduction
  step-assoc : ∀ {A B C D} {h : IR C D} {g : IR B C} {f : IR A B} {gf : IR A C} →
               ComposeStep g f gf →
               ComposeStep (h ∘ g) f (h ∘ gf)

  -- Default: no optimization, just compose
  step-default : ∀ {A B C} {g : IR B C} {f : IR A B} →
                 ComposeStep g f (g ∘ f)

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

    -- Pair distribution with recursive optimization (safe cases only)
    -- ⟨ f , g ⟩ ∘ h → ⟨ f' , g' ⟩ where f' = optimize(f ∘ h), g' = optimize(g ∘ h)
    -- Requires proof that cost bound is maintained (ensured by safe-pair-distrib)
    pair-distrib : ∀ {A B C D} {f : IR C A} {g : IR C B} {h : IR D C} {f' : IR D A} {g' : IR D B} {m} →
                   ComposeSteps f h f' →
                   ComposeSteps g h g' →
                   suc (cost f' ℕ+ cost g') ≤ suc (cost f ℕ+ cost g) ℕ+ cost h →
                   ComposeSteps (⟨ f , g ⟩ m) h (⟨ f' , g' ⟩ m)

  -- | Steps within a single term (for recursive optimization)
  data ComposeSteps′ : ∀ {A B} → IR A B → IR A B → Set where
    refl′ : ∀ {A B} {t : IR A B} → ComposeSteps′ t t

    -- Transitivity
    trans′ : ∀ {A B} {t t' t'' : IR A B} →
             ComposeSteps′ t t' → ComposeSteps′ t' t'' → ComposeSteps′ t t''

    -- Optimize within a composition
    in-compose : ∀ {A B C} {g : IR B C} {f : IR A B} {r : IR A C} →
                 ComposeSteps g f r →
                 ComposeSteps′ (g ∘ f) r

    -- Lift steps through the right side of a composition
    lift-right : ∀ {A B C} {h : IR B C} {f f' : IR A B} →
                 ComposeSteps′ f f' →
                 ComposeSteps′ (h ∘ f) (h ∘ f')

    -- Step inside a pair
    in-pair : ∀ {A B C} {f f' : IR C A} {g g' : IR C B} {m} →
              ComposeSteps′ f f' → ComposeSteps′ g g' →
              ComposeSteps′ (⟨ f , g ⟩ m) (⟨ f' , g' ⟩ m)

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
step-preserves-semantics step-assoc-pure x = refl
step-preserves-semantics (step-assoc {h = h} inner) x =
  cong (eval h) (step-preserves-semantics inner x)
step-preserves-semantics step-default x = refl

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
step-reduces-cost (step-assoc-pure {h = h} {g = g} {f = f}) =
  -- cost (h ∘ (g ∘ f)) = cost h + (cost g + cost f)
  -- cost (h ∘ g) + cost f = (cost h + cost g) + cost f
  -- These are equal by associativity
  let open Data.Nat.Properties
      eq : cost h ℕ+ (cost g ℕ+ cost f) ≡ (cost h ℕ+ cost g) ℕ+ cost f
      eq = sym (+-assoc (cost h) (cost g) (cost f))
  in subst (cost h ℕ+ (cost g ℕ+ cost f) ≤_) eq ≤-refl
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
step-reduces-cost step-default = ≤-refl

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
steps-preserves-semantics (pair-distrib {f = f} {g = g} {h = h} sf sg _) x =
  cong₂ _,_ (steps-preserves-semantics sf x) (steps-preserves-semantics sg x)

steps′-preserves-semantics refl′ x = refl
steps′-preserves-semantics (trans′ s1 s2) x =
  trans (steps′-preserves-semantics s2 x) (steps′-preserves-semantics s1 x)
steps′-preserves-semantics (in-compose steps) x = steps-preserves-semantics steps x
steps′-preserves-semantics (lift-right {h = h} s) x =
  cong (eval h) (steps′-preserves-semantics s x)
steps′-preserves-semantics (in-pair sf sg) x =
  cong₂ _,_ (steps′-preserves-semantics sf x) (steps′-preserves-semantics sg x)

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
steps-reduces-cost (pair-distrib _ _ bound) = bound

steps′-reduces-cost refl′ = ≤-refl
steps′-reduces-cost (trans′ s1 s2) = ≤-trans (steps′-reduces-cost s2) (steps′-reduces-cost s1)
steps′-reduces-cost (in-compose steps) = steps-reduces-cost steps
steps′-reduces-cost (lift-right {h = h} s) =
  let open Data.Nat.Properties
  in +-monoʳ-≤ (cost h) (steps′-reduces-cost s)
steps′-reduces-cost (in-pair {f = f} {f' = f'} {g = g} {g' = g'} sf sg) =
  let open Data.Nat.Properties
      sf-bound = steps′-reduces-cost sf
      sg-bound = steps′-reduces-cost sg
  in s≤s (+-mono-≤ sf-bound sg-bound)

------------------------------------------------------------------------
-- Optimizer produces valid step sequence
--
-- This connects the declarative step relation to the actual optimizer.
-- We postulate this for now - it can be proven by case analysis on
-- optimize-compose matching the step constructors.
------------------------------------------------------------------------

open import Once.Optimize using (optimize-compose; safe-pair-distrib; pair-distrib-opt)
open import Once.Optimizer.CostProof using (safe-distrib-inl-cost; safe-distrib-inr-cost;
                                             safe-distrib-unfold-cost; safe-distrib-fold-cost;
                                             safe-distrib-pair-cost)

------------------------------------------------------------------------
-- Proof: optimize-compose produces valid step sequence
--
-- This connects the declarative step relation to the actual optimizer.
-- Uses `with ... in eq` pattern to capture equality proofs from
-- optimizer's with-patterns (per lessons-learned.md).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Distribution target predicate
--
-- The optimizer only distributes pairs over these 5 h constructors.
-- By requiring this predicate, we make non-distribution cases impossible.
------------------------------------------------------------------------

data IsDistributionTarget : ∀ {A B} → IR A B → Set where
  is-pair   : ∀ {A B C m} (h₁ : IR A B) (h₂ : IR A C) → IsDistributionTarget (⟨ h₁ , h₂ ⟩ m)
  is-inl    : ∀ {A B m} → IsDistributionTarget (inl {A} {B} m)
  is-inr    : ∀ {A B m} → IsDistributionTarget (inr {A} {B} m)
  is-unfold : ∀ {F} → IsDistributionTarget (unfold {F})
  is-fold   : ∀ {F} → IsDistributionTarget (fold {F})

-- Pair distribution cost bound
-- When safe-pair-distrib f g = true, distribution maintains cost bound.
-- The IsDistributionTarget predicate ensures h is one of the 5 distribution cases.
safe-distrib-cost : ∀ {A B C D} (f : IR C A) (g : IR C B) (h : IR D C) (m : AllocMode) →
  IsDistributionTarget h →
  safe-pair-distrib f g ≡ true →
  suc (cost (optimize-compose f h) ℕ+ cost (optimize-compose g h)) ≤
  suc (cost f ℕ+ cost g) ℕ+ cost h
safe-distrib-cost f g .(⟨ h₁ , h₂ ⟩ _) m (is-pair h₁ h₂) eq = safe-distrib-pair-cost f g h₁ h₂ m _ eq
safe-distrib-cost f g .(inl _) m is-inl eq = safe-distrib-inl-cost f g m _ eq
safe-distrib-cost f g .(inr _) m is-inr eq = safe-distrib-inr-cost f g m _ eq
safe-distrib-cost f g .unfold m is-unfold eq = safe-distrib-unfold-cost f g m eq
safe-distrib-cost f g .fold m is-fold eq = safe-distrib-fold-cost f g m eq

-- Forward declaration
optimize-compose-steps : ∀ {A B C} (g : IR B C) (f : IR A B) →
  ComposeSteps g f (optimize-compose g f)

-- Associativity case: (h ∘ g) ∘ f → optimize h (optimize g f)
-- The optimizer reassociates and optimizes both compositions.
-- Proof: step-assoc-pure gives h ∘ (g ∘ f), then we optimize both parts.
optimize-compose-steps-assoc : ∀ {A B C D} (h : IR C D) (g : IR B C) (f : IR A B) →
  ComposeSteps (h ∘ g) f (optimize-compose (h ∘ g) f)
optimize-compose-steps-assoc h g f =
  step step-assoc-pure
       (trans′ (lift-right (in-compose (optimize-compose-steps g f)))
               (in-compose (optimize-compose-steps h (optimize-compose g f))))

-- Note: Remaining cases all fall through to optimizer's default clause:
--   optimize-compose g f = g ∘ f
-- so they all use `done : ComposeSteps g f (g ∘ f)`

-- Identity left: optimize-compose id f = f
optimize-compose-steps id f = step step-id-left refl′

-- Right identity cases (one case per g constructor)
optimize-compose-steps fst id = step step-id-right refl′
optimize-compose-steps snd id = step step-id-right refl′
optimize-compose-steps (⟨ f , g ⟩ m) id = step step-id-right refl′
optimize-compose-steps (inl m) id = step step-id-right refl′
optimize-compose-steps (inr m) id = step step-id-right refl′
optimize-compose-steps [ f , g ] id = step step-id-right refl′
optimize-compose-steps terminal id = step step-id-right refl′
optimize-compose-steps (curry f m) id = step step-id-right refl′
optimize-compose-steps apply id = step step-id-right refl′
optimize-compose-steps fold id = step step-id-right refl′
optimize-compose-steps unfold id = step step-id-right refl′
optimize-compose-steps arr id = step step-id-right refl′
optimize-compose-steps (Prim n) id = step step-id-right refl′
optimize-compose-steps (g ∘ f) id = step step-id-right refl′

-- Beta laws (products)
optimize-compose-steps fst (⟨ f , g ⟩ m) = step step-fst-pair refl′
optimize-compose-steps snd (⟨ f , g ⟩ m) = step step-snd-pair refl′

-- Beta laws (coproducts)
optimize-compose-steps [ f , g ] (inl m) = step step-case-inl refl′
optimize-compose-steps [ f , g ] (inr m) = step step-case-inr refl′

-- Beta law (exponentials)
optimize-compose-steps apply (⟨ curry f m₁ , g ⟩ m₂) = step step-apply-curry refl′

-- Fixed point laws
optimize-compose-steps fold unfold = step step-fold-unfold refl′
optimize-compose-steps unfold fold = step step-unfold-fold refl′
optimize-compose-steps fold (unfold ∘ f) = step step-fold-unfold-f refl′
optimize-compose-steps unfold (fold ∘ f) = step step-unfold-fold-f refl′

-- Dead code elimination (terminal ∘ f = terminal)
optimize-compose-steps terminal (_ ∘ _) = step step-terminal refl′
optimize-compose-steps terminal fst = step step-terminal refl′
optimize-compose-steps terminal snd = step step-terminal refl′
optimize-compose-steps terminal (⟨ _ , _ ⟩ _) = step step-terminal refl′
optimize-compose-steps terminal (inl _) = step step-terminal refl′
optimize-compose-steps terminal (inr _) = step step-terminal refl′
optimize-compose-steps terminal [ _ , _ ] = step step-terminal refl′
optimize-compose-steps terminal terminal = step step-terminal refl′
optimize-compose-steps terminal (curry _ _) = step step-terminal refl′
optimize-compose-steps terminal apply = step step-terminal refl′
optimize-compose-steps terminal fold = step step-terminal refl′
optimize-compose-steps terminal unfold = step step-terminal refl′
optimize-compose-steps terminal arr = step step-terminal refl′
optimize-compose-steps terminal (Prim _) = step step-terminal refl′

-- Initial absorption (g ∘ initial = initial)
optimize-compose-steps fst initial = step step-initial refl′
optimize-compose-steps snd initial = step step-initial refl′
optimize-compose-steps (⟨ _ , _ ⟩ _) initial = step step-initial refl′
optimize-compose-steps (inl _) initial = step step-initial refl′
optimize-compose-steps (inr _) initial = step step-initial refl′
optimize-compose-steps [ _ , _ ] initial = step step-initial refl′
optimize-compose-steps terminal initial = step step-initial refl′
optimize-compose-steps (curry _ _) initial = step step-initial refl′
optimize-compose-steps apply initial = step step-initial refl′
optimize-compose-steps fold initial = step step-initial refl′
optimize-compose-steps unfold initial = step step-initial refl′
optimize-compose-steps arr initial = step step-initial refl′
optimize-compose-steps (Prim _) initial = step step-initial refl′
optimize-compose-steps (_ ∘ _) initial = step step-initial refl′

-- initial ∘ f (no optimization)
optimize-compose-steps initial f = done

-- Pair distribution cases: use explicit helper that takes the Bool and equality proof
-- to ensure the goal type reduces when pattern matching.
-- The IsDistributionTarget proof ensures only valid h cases reach safe-distrib-cost.
optimize-compose-steps (⟨ f , g ⟩ m) (⟨ h₁ , h₂ ⟩ m') with safe-pair-distrib f g in eq
... | true  = pair-distrib (optimize-compose-steps f (⟨ h₁ , h₂ ⟩ m'))
                           (optimize-compose-steps g (⟨ h₁ , h₂ ⟩ m'))
                           (safe-distrib-cost f g (⟨ h₁ , h₂ ⟩ m') m (is-pair h₁ h₂) eq)
... | false = done

optimize-compose-steps (⟨ f , g ⟩ m) (inl m') with safe-pair-distrib f g in eq
... | true  = pair-distrib (optimize-compose-steps f (inl m'))
                           (optimize-compose-steps g (inl m'))
                           (safe-distrib-cost f g (inl m') m is-inl eq)
... | false = done

optimize-compose-steps (⟨ f , g ⟩ m) (inr m') with safe-pair-distrib f g in eq
... | true  = pair-distrib (optimize-compose-steps f (inr m'))
                           (optimize-compose-steps g (inr m'))
                           (safe-distrib-cost f g (inr m') m is-inr eq)
... | false = done

optimize-compose-steps (⟨ f , g ⟩ m) unfold with safe-pair-distrib f g in eq
... | true  = pair-distrib (optimize-compose-steps f unfold)
                           (optimize-compose-steps g unfold)
                           (safe-distrib-cost f g unfold m is-unfold eq)
... | false = done

optimize-compose-steps (⟨ f , g ⟩ m) fold with safe-pair-distrib f g in eq
... | true  = pair-distrib (optimize-compose-steps f fold)
                           (optimize-compose-steps g fold)
                           (safe-distrib-cost f g fold m is-fold eq)
... | false = done

-- Default pair cases (no distribution possible)
optimize-compose-steps (⟨ f , g ⟩ m) (_ ∘ _) = done
optimize-compose-steps (⟨ f , g ⟩ m) fst = done
optimize-compose-steps (⟨ f , g ⟩ m) snd = done
optimize-compose-steps (⟨ f , g ⟩ m) [ _ , _ ] = done
optimize-compose-steps (⟨ f , g ⟩ m) terminal = done
optimize-compose-steps (⟨ f , g ⟩ m) (curry _ _) = done
optimize-compose-steps (⟨ f , g ⟩ m) apply = done
optimize-compose-steps (⟨ f , g ⟩ m) arr = done
optimize-compose-steps (⟨ f , g ⟩ m) (Prim _) = done

-- Case distribution (optimizer doesn't distribute into cases)
-- NOTE: The optimizer has `optimize-compose h [ f , g ] = h ∘ [ f , g ]`
-- which matches ANY h (including compositions), so this must include
-- the composition case to prevent the associativity clause from capturing it.
optimize-compose-steps fst [ f , g ] = done
optimize-compose-steps snd [ f , g ] = done
optimize-compose-steps (inl _) [ f , g ] = done
optimize-compose-steps (inr _) [ f , g ] = done
optimize-compose-steps [ _ , _ ] [ f , g ] = done
optimize-compose-steps (curry _ _) [ f , g ] = done
optimize-compose-steps apply [ f , g ] = done
optimize-compose-steps fold [ f , g ] = done
optimize-compose-steps unfold [ f , g ] = done
optimize-compose-steps arr [ f , g ] = done
optimize-compose-steps (Prim _) [ f , g ] = done
optimize-compose-steps (_ ∘ _) [ f , g ] = done

-- Associativity: (h ∘ g) ∘ f → optimize h (optimize g f)
-- NOTE: This clause must come AFTER the case distribution clause above,
-- since the optimizer's case distribution clause catches `(h ∘ g) [ f , g ]` first.
optimize-compose-steps (h ∘ g) f = optimize-compose-steps-assoc h g f

-- Remaining default cases: optimizer returns g ∘ f (no optimization)
optimize-compose-steps g f = done

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
