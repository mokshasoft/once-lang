------------------------------------------------------------------------
-- Once.Optimizer.Rewrite
--
-- Single-step rewrite relation for Once IR.
-- Defines the rewrites that the optimizer applies.
--
-- Key property: each rewrite preserves semantics and reduces cost.
------------------------------------------------------------------------

module Once.Optimizer.Rewrite where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Optimizer.Cost
open import Once.Optimizer.Depth

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat as ℕ using () renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n; +-monoˡ-≤; +-monoʳ-≤; +-suc; +-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- Single-step rewrite relation
------------------------------------------------------------------------

-- | t ⟶ t' means t rewrites to t' in one step
--
-- Each constructor represents one optimization rule.
-- The rules are exactly those implemented in Once.Optimize.
--
data _⟶_ : ∀ {A B} → IR A B → IR A B → Set where

  -- Identity laws
  ⟶-id-left  : ∀ {A B} {f : IR A B} →
    (id ∘ f) ⟶ f

  ⟶-id-right : ∀ {A B} {f : IR A B} →
    (f ∘ id) ⟶ f

  -- Product beta
  ⟶-fst-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
    (fst ∘ ⟨ f , g ⟩ m) ⟶ f

  ⟶-snd-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
    (snd ∘ ⟨ f , g ⟩ m) ⟶ g

  -- Product eta
  ⟶-pair-eta : ∀ {A B} →
    ⟨ fst {A} {B} , snd ⟩ Heap ⟶ id

  -- Coproduct beta
  ⟶-case-inl : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
    ([ f , g ] ∘ inl m) ⟶ f

  ⟶-case-inr : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
    ([ f , g ] ∘ inr m) ⟶ g

  -- Coproduct eta
  ⟶-case-eta : ∀ {A B} {m₁ m₂} →
    [ inl {A} {B} m₁ , inr m₂ ] ⟶ id

  -- Fixed point
  ⟶-fold-unfold : ∀ {F} →
    (fold {F} ∘ unfold) ⟶ id

  ⟶-unfold-fold : ∀ {F} →
    (unfold {F} ∘ fold) ⟶ id

  -- Exponential beta
  ⟶-apply-curry : ∀ {A B C q} {f : IR (A * B) C} {g : IR A B} {m₁ m₂} →
    (apply ∘ ⟨ curry {q = q} f m₁ , g ⟩ m₂) ⟶ (f ∘ ⟨ id , g ⟩ Heap)

  -- Terminal fusion (dead code elimination)
  ⟶-terminal : ∀ {A B} {f : IR A B} →
    (terminal ∘ f) ⟶ terminal

  -- Initial absorption
  ⟶-initial : ∀ {A B} {f : IR A B} →
    (f ∘ initial) ⟶ initial

  -- Congruence rules (rewriting under constructors)
  ⟶-compose-left : ∀ {A B C} {g g' : IR B C} {f : IR A B} →
    g ⟶ g' →
    (g ∘ f) ⟶ (g' ∘ f)

  ⟶-compose-right : ∀ {A B C} {g : IR B C} {f f' : IR A B} →
    f ⟶ f' →
    (g ∘ f) ⟶ (g ∘ f')

  ⟶-pair-left : ∀ {A B C} {f f' : IR C A} {g : IR C B} {m} →
    f ⟶ f' →
    ⟨ f , g ⟩ m ⟶ ⟨ f' , g ⟩ m

  ⟶-pair-right : ∀ {A B C} {f : IR C A} {g g' : IR C B} {m} →
    g ⟶ g' →
    ⟨ f , g ⟩ m ⟶ ⟨ f , g' ⟩ m

  ⟶-case-left : ∀ {A B C} {f f' : IR A C} {g : IR B C} →
    f ⟶ f' →
    [ f , g ] ⟶ [ f' , g ]

  ⟶-case-right : ∀ {A B C} {f : IR A C} {g g' : IR B C} →
    g ⟶ g' →
    [ f , g ] ⟶ [ f , g' ]

  ⟶-curry : ∀ {A B C q} {f f' : IR (A * B) C} {m} →
    f ⟶ f' →
    curry {q = q} f m ⟶ curry f' m

------------------------------------------------------------------------
-- Reflexive-transitive closure
------------------------------------------------------------------------

-- | t ⟶* t' means t rewrites to t' in zero or more steps
data _⟶*_ : ∀ {A B} → IR A B → IR A B → Set where
  ⟶*-refl : ∀ {A B} {t : IR A B} →
    t ⟶* t

  ⟶*-step : ∀ {A B} {t t' t'' : IR A B} →
    t ⟶ t' →
    t' ⟶* t'' →
    t ⟶* t''

-- | Transitivity of ⟶*
⟶*-trans : ∀ {A B} {t₁ t₂ t₃ : IR A B} →
  t₁ ⟶* t₂ → t₂ ⟶* t₃ → t₁ ⟶* t₃
⟶*-trans ⟶*-refl q = q
⟶*-trans (⟶*-step p ps) q = ⟶*-step p (⟶*-trans ps q)

------------------------------------------------------------------------
-- Soundness: Rewrites preserve semantics
------------------------------------------------------------------------

-- Function extensionality (standard postulate)
postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
           (∀ x → f x ≡ g x) → f ≡ g

-- | Each single-step rewrite preserves semantics
⟶-sound : ∀ {A B} {t t' : IR A B} →
  t ⟶ t' →
  ∀ x → eval t x ≡ eval t' x
⟶-sound ⟶-id-left x = refl
⟶-sound ⟶-id-right x = refl
⟶-sound ⟶-fst-pair x = refl
⟶-sound ⟶-snd-pair x = refl
⟶-sound ⟶-pair-eta x = refl
⟶-sound ⟶-case-inl x = refl
⟶-sound ⟶-case-inr x = refl
⟶-sound ⟶-case-eta (inj₁ a) = refl
⟶-sound ⟶-case-eta (inj₂ b) = refl
⟶-sound ⟶-fold-unfold x = refl
⟶-sound ⟶-unfold-fold x = refl
⟶-sound ⟶-apply-curry x = refl
⟶-sound ⟶-terminal x = refl
⟶-sound (⟶-initial {f = f}) ()
⟶-sound (⟶-compose-left {g = g} {g' = g'} {f = f} step) x =
  ⟶-sound step (eval f x)
⟶-sound (⟶-compose-right {g = g} step) x =
  cong (eval g) (⟶-sound step x)
⟶-sound (⟶-pair-left {g = g} step) x =
  cong (λ a → (a , eval g x)) (⟶-sound step x)
⟶-sound (⟶-pair-right {f = f} step) x =
  cong (λ b → (eval f x , b)) (⟶-sound step x)
⟶-sound (⟶-case-left step) (inj₁ a) = ⟶-sound step a
⟶-sound (⟶-case-left step) (inj₂ b) = refl
⟶-sound (⟶-case-right step) (inj₁ a) = refl
⟶-sound (⟶-case-right step) (inj₂ b) = ⟶-sound step b
⟶-sound (⟶-curry {A = A} {B = B} {C = C} step) x =
  cong (λ sem → record { env-addr = encode x ; semantics = λ b → sem (x , b) })
       (funext (λ p → ⟶-sound step p))

-- | Multi-step rewriting preserves semantics
⟶*-sound : ∀ {A B} {t t' : IR A B} →
  t ⟶* t' →
  ∀ x → eval t x ≡ eval t' x
⟶*-sound ⟶*-refl x = refl
⟶*-sound (⟶*-step step steps) x = trans (⟶-sound step x) (⟶*-sound steps x)

------------------------------------------------------------------------
-- Cost properties of rewrites
------------------------------------------------------------------------

-- | Beta rewrites reduce or preserve cost
⟶-cost-≤ : ∀ {A B} {t t' : IR A B} →
  t ⟶ t' →
  cost t' ≤ cost t
⟶-cost-≤ ⟶-id-left = ≤-refl
⟶-cost-≤ (⟶-id-right {f = f}) = m≤m+n (cost f) 0
⟶-cost-≤ (⟶-fst-pair {f = f} {g = g}) =
  -- cost (fst ∘ ⟨ f , g ⟩ m) = 0 + (suc (cost f) + cost g) = suc (cost f) + cost g
  -- Need: cost f ≤ suc (cost f) + cost g
  ≤-trans (n≤1+n (cost f)) (m≤m+n (suc (cost f)) (cost g))
⟶-cost-≤ (⟶-snd-pair {f = f} {g = g}) =
  -- cost (snd ∘ ⟨ f , g ⟩ m) = 0 + (suc (cost f) + cost g) = suc (cost f) + cost g
  -- Need: cost g ≤ suc (cost f) + cost g
  m≤n+m (cost g) (suc (cost f))
⟶-cost-≤ ⟶-pair-eta = z≤n  -- cost id = 0, cost (⟨ fst , snd ⟩ Heap) = 1
⟶-cost-≤ (⟶-case-inl {f = f} {g = g}) =
  -- cost ([ f , g ] ∘ inl m) = (cost f + cost g) + 1
  -- Need: cost f ≤ cost f + cost g + 1
  ≤-trans (m≤m+n (cost f) (cost g)) (m≤m+n (cost f ℕ+ cost g) 1)
⟶-cost-≤ (⟶-case-inr {f = f} {g = g}) =
  -- cost ([ f , g ] ∘ inr m) = (cost f + cost g) + 1
  -- Need: cost g ≤ cost f + cost g + 1
  ≤-trans (m≤n+m (cost g) (cost f)) (m≤m+n (cost f ℕ+ cost g) 1)
⟶-cost-≤ ⟶-case-eta = z≤n  -- cost id = 0
⟶-cost-≤ ⟶-fold-unfold = z≤n  -- cost id = 0
⟶-cost-≤ ⟶-unfold-fold = z≤n  -- cost id = 0
⟶-cost-≤ (⟶-apply-curry {f = f} {g = g}) = apply-curry-cost-lemma (cost f) (cost g)
  where
    -- Apply-curry introduces a new pair but removes a closure.
    -- Net effect: cost may increase by 1 (closure cost 1, new pair cost 1, but we save the old pair)
    -- We prove: cost f + suc (cost g) ≤ suc (suc (cost f)) + cost g
    -- LHS = suc (cf + cg) by +-suc, RHS = suc (suc (cf + cg)) by definition
    -- So we need: suc (cf + cg) ≤ suc (suc (cf + cg)), which is n≤1+n
    apply-curry-cost-lemma : ∀ cf cg → cf ℕ+ suc cg ≤ suc (suc cf) ℕ+ cg
    apply-curry-cost-lemma cf cg = subst (_≤ suc (suc cf) ℕ+ cg) (sym (+-suc cf cg)) (n≤1+n (suc (cf ℕ+ cg)))
⟶-cost-≤ ⟶-terminal = z≤n
⟶-cost-≤ ⟶-initial = z≤n
⟶-cost-≤ (⟶-compose-left {f = f} step) =
  ≤-trans (+-monoˡ-≤ (cost f) (⟶-cost-≤ step)) ≤-refl
⟶-cost-≤ (⟶-compose-right {g = g} step) =
  ≤-trans (+-monoʳ-≤ (cost g) (⟶-cost-≤ step)) ≤-refl
⟶-cost-≤ (⟶-pair-left step) = s≤s (+-monoˡ-≤ _ (⟶-cost-≤ step))
⟶-cost-≤ (⟶-pair-right step) = s≤s (+-monoʳ-≤ _ (⟶-cost-≤ step))
⟶-cost-≤ (⟶-case-left step) = +-monoˡ-≤ _ (⟶-cost-≤ step)
⟶-cost-≤ (⟶-case-right step) = +-monoʳ-≤ _ (⟶-cost-≤ step)
⟶-cost-≤ (⟶-curry step) = s≤s (⟶-cost-≤ step)
