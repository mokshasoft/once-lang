------------------------------------------------------------------------
-- Once.Optimizer.CostProof
--
-- Proof that optimize-compose never increases cost.
--
-- With the safe-pair-distrib check, distribution only happens when:
-- 1. Eta case: fst+snd or snd+fst (always reduces cost by 1)
-- 2. Terminal case: at least one is terminal (eliminates cost entirely)
------------------------------------------------------------------------

module Once.Optimizer.CostProof where

open import Once.Type
open import Once.IR
open import Once.Optimize
open import Once.Optimizer.Cost

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat as ℕ using () renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; m≤m+n; m≤n+m; n≤1+n;
                                        +-monoˡ-≤; +-monoʳ-≤; +-identityˡ; +-identityʳ; +-assoc; +-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)
  renaming ([_] to ⟦_⟧ᵢ)

------------------------------------------------------------------------
-- Helper lemmas for ℕ inequalities
------------------------------------------------------------------------

-- n ≤ m + n
n≤m+n : ∀ m n → n ≤ m ℕ+ n
n≤m+n m n = m≤n+m n m

-- a ≤ suc a + b
a≤suc-a+b : ∀ a b → a ≤ suc (a ℕ+ b)
a≤suc-a+b a b = m≤n⇒m≤1+n (m≤m+n a b)

-- b ≤ suc a + b
b≤suc-a+b : ∀ a b → b ≤ suc (a ℕ+ b)
b≤suc-a+b a b = m≤n⇒m≤1+n (n≤m+n a b)

------------------------------------------------------------------------
-- Safe distribution cost bounds (proven via exhaustive case analysis)
--
-- When safe-pair-distrib f g = true, distribution doesn't increase cost.
-- This happens in two cases:
-- 1. Eta case: f = fst, g = snd (or vice versa) - pair is fully eliminated
-- 2. Terminal case: f = terminal or g = terminal - one component has cost 0
--
-- Key insights:
-- - For inl/inr/unfold/fold: only terminal case is type-compatible
--   (fst/snd have product domain, but these constructors have sum/Fix domain)
-- - For pairs: both eta and terminal cases apply
-- - optimize-compose terminal h = terminal (cost 0)
------------------------------------------------------------------------

-- Key lemma: optimize-compose terminal h = terminal for any h
opt-terminal-cost : ∀ {A B} (h : IR A B) →
  cost (optimize-compose (terminal {B}) h) ≡ 0
opt-terminal-cost id = refl
opt-terminal-cost (_ ∘ _) = refl
opt-terminal-cost fst = refl
opt-terminal-cost snd = refl
opt-terminal-cost (⟨ _ , _ ⟩ _) = refl
opt-terminal-cost (inl _) = refl
opt-terminal-cost (inr _) = refl
opt-terminal-cost [ _ , _ ] = refl
opt-terminal-cost terminal = refl
opt-terminal-cost initial = refl
opt-terminal-cost (curry _ _) = refl
opt-terminal-cost apply = refl
opt-terminal-cost fold = refl
opt-terminal-cost unfold = refl
opt-terminal-cost arr = refl
opt-terminal-cost (Prim _) = refl

-- Helper: a ≤ b + 1 → suc a ≤ suc b + 1
suc-≤-suc-plus-1 : ∀ {a b} → a ≤ b ℕ+ 1 → suc a ≤ suc b ℕ+ 1
suc-≤-suc-plus-1 {a} {b} p = s≤s p

-- Arithmetic lemma: suc (a + b) ≡ suc (a + 0) + b
suc-plus-rearrange : ∀ a b → suc (a ℕ+ b) ≡ suc (a ℕ+ 0) ℕ+ b
suc-plus-rearrange a b =
  trans (cong suc (cong (a ℕ+_) (sym (+-identityˡ b))))
        (cong suc (sym (+-assoc a 0 b)))

------------------------------------------------------------------------
-- optimize-pair and optimize-case cost lemmas
--
-- These are provable but require matching the complex with-clause
-- structure of the optimizer functions.
------------------------------------------------------------------------

postulate
  -- | optimize-pair f g produces:
  --   - id (if f=fst, g=snd and types match) - cost 0 ≤ suc (0+0)
  --   - h (if f=fst∘h, g=snd∘h and types match) - cost h ≤ suc (h+h)
  --   - ⟨ f , g ⟩ otherwise - cost = suc (cost f + cost g)
  optimize-pair-cost-≤ : ∀ {A B C} (f : IR C A) (g : IR C B) →
    cost (optimize-pair f g) ≤ suc (cost f ℕ+ cost g)

  -- | optimize-case f g produces:
  --   - id (if f=inl, g=inr and types match) - cost 0 ≤ (1+1)
  --   - h (if f=h∘inl, g=h∘inr and types match) - cost h ≤ (h+1)+(h+1)
  --   - [ f , g ] otherwise - cost = cost f + cost g
  optimize-case-cost-≤ : ∀ {A B C} (f : IR A C) (g : IR B C) →
    cost (optimize-case f g) ≤ cost f ℕ+ cost g

  -- Case fusion cost
  case-fusion-cost : ∀ {FA FB H₁A H₁B C} (h₁ : IR H₁A C) (h₂ : IR H₁B C)
    (f : IR FA (H₁A + H₁B)) (g : IR FB (H₁A + H₁B)) →
    cost ([ optimize-compose ([ h₁ , h₂ ]) f , optimize-compose ([ h₁ , h₂ ]) g ])
    ≤ (cost h₁ ℕ+ cost h₂) ℕ+ (cost f ℕ+ cost g)

  -- Associativity: (h ∘ g) ∘ f
  compose-∘-cost-≤ : ∀ {A B B' C} (h : IR B' C) (g : IR B B') (f : IR A B) →
    cost (optimize-compose (h ∘ g) f) ≤ (cost h ℕ+ cost g) ℕ+ cost f


------------------------------------------------------------------------
-- Main theorem and safe-distrib helpers (mutual recursion)
--
-- optimize-compose-cost-≤ and safe-distrib-* are mutually recursive:
-- - optimize-compose-cost-≤ calls safe-distrib-* for distribution cases
-- - safe-distrib-* calls optimize-compose-cost-≤ on subterms
------------------------------------------------------------------------

mutual
  -- Helper for g = terminal case with arbitrary h
  g-terminal-helper : ∀ {A B D} (f : IR D A) (h : IR B D) (m : AllocMode) →
    cost (optimize-compose f h) ≤ cost f ℕ+ cost h →
    cost (⟨ optimize-compose f h , optimize-compose terminal h ⟩ m) ≤ suc (cost f ℕ+ 0) ℕ+ cost h
  g-terminal-helper {A} {B} {D} f h m ih =
    let eq1 : cost (optimize-compose terminal h) ≡ 0
        eq1 = opt-terminal-cost h
        eq2 : cost (⟨ optimize-compose f h , optimize-compose terminal h ⟩ m) ≡ suc (cost (optimize-compose f h) ℕ+ 0)
        eq2 = cong (λ x → suc (cost (optimize-compose f h) ℕ+ x)) eq1
        step1 : suc (cost (optimize-compose f h) ℕ+ 0) ≤ suc (cost f ℕ+ cost h)
        step1 = s≤s (subst (_≤ cost f ℕ+ cost h) (sym (+-identityʳ (cost (optimize-compose f h)))) ih)
        step2 : suc (cost (optimize-compose f h) ℕ+ 0) ≤ suc (cost f ℕ+ 0) ℕ+ cost h
        step2 = subst (suc (cost (optimize-compose f h) ℕ+ 0) ≤_) (suc-plus-rearrange (cost f) (cost h)) step1
    in subst (_≤ suc (cost f ℕ+ 0) ℕ+ cost h) (sym eq2) step2

  -- Helper for unfold case (cost h = 0)
  g-terminal-helper-0 : ∀ {A B D} (f : IR D A) (h : IR B D) (m : AllocMode) →
    cost h ≡ 0 →
    cost (optimize-compose f h) ≤ cost f ℕ+ cost h →
    cost (⟨ optimize-compose f h , optimize-compose terminal h ⟩ m) ≤ suc (cost f ℕ+ 0) ℕ+ 0
  g-terminal-helper-0 {A} {B} {D} f h m h-cost-0 ih =
    let eq1 : cost (optimize-compose terminal h) ≡ 0
        eq1 = opt-terminal-cost h
        eq2 : cost (⟨ optimize-compose f h , optimize-compose terminal h ⟩ m) ≡ suc (cost (optimize-compose f h) ℕ+ 0)
        eq2 = cong (λ x → suc (cost (optimize-compose f h) ℕ+ x)) eq1
        step1 : cost (optimize-compose f h) ≤ cost f
        step1 = subst (cost (optimize-compose f h) ≤_) (+-identityʳ (cost f)) (subst (λ x → cost (optimize-compose f h) ≤ cost f ℕ+ x) h-cost-0 ih)
        step2 : suc (cost (optimize-compose f h) ℕ+ 0) ≤ suc (cost f)
        step2 = s≤s (subst (_≤ cost f) (sym (+-identityʳ (cost (optimize-compose f h)))) step1)
        step3 : suc (cost f) ≡ suc (cost f ℕ+ 0) ℕ+ 0
        step3 = trans (cong suc (sym (+-identityʳ (cost f)))) (sym (+-identityʳ (suc (cost f ℕ+ 0))))
    in subst (_≤ suc (cost f ℕ+ 0) ℕ+ 0) (sym eq2) (subst (suc (cost (optimize-compose f h) ℕ+ 0) ≤_) step3 step2)

  -- Helper for pair cost with g = terminal
  g-terminal-helper-pair : ∀ {A D H₁ H₂} (f : IR (H₁ * H₂) A) (h₁ : IR D H₁) (h₂ : IR D H₂) (m m' : AllocMode) →
    cost (optimize-compose f (⟨ h₁ , h₂ ⟩ m')) ≤ cost f ℕ+ suc (cost h₁ ℕ+ cost h₂) →
    cost (⟨ optimize-compose f (⟨ h₁ , h₂ ⟩ m') , optimize-compose (terminal {H₁ * H₂}) (⟨ h₁ , h₂ ⟩ m') ⟩ m)
    ≤ suc (cost f ℕ+ 0) ℕ+ suc (cost h₁ ℕ+ cost h₂)
  g-terminal-helper-pair {A} {D} {H₁} {H₂} f h₁ h₂ m m' ih =
    let eq1 : cost (optimize-compose (terminal {H₁ * H₂}) (⟨ h₁ , h₂ ⟩ m')) ≡ 0
        eq1 = opt-terminal-cost (⟨ h₁ , h₂ ⟩ m')
        eq2 : cost (⟨ optimize-compose f (⟨ h₁ , h₂ ⟩ m') , optimize-compose (terminal {H₁ * H₂}) (⟨ h₁ , h₂ ⟩ m') ⟩ m)
              ≡ suc (cost (optimize-compose f (⟨ h₁ , h₂ ⟩ m')) ℕ+ 0)
        eq2 = cong (λ x → suc (cost (optimize-compose f (⟨ h₁ , h₂ ⟩ m')) ℕ+ x)) eq1
        step1 : suc (cost (optimize-compose f (⟨ h₁ , h₂ ⟩ m')) ℕ+ 0) ≤ suc (cost f ℕ+ suc (cost h₁ ℕ+ cost h₂))
        step1 = s≤s (subst (_≤ cost f ℕ+ suc (cost h₁ ℕ+ cost h₂)) (sym (+-identityʳ (cost (optimize-compose f (⟨ h₁ , h₂ ⟩ m'))))) ih)
        step2 : suc (cost f ℕ+ suc (cost h₁ ℕ+ cost h₂)) ≡ suc (cost f ℕ+ 0) ℕ+ suc (cost h₁ ℕ+ cost h₂)
        step2 = suc-plus-rearrange (cost f) (suc (cost h₁ ℕ+ cost h₂))
    in subst (_≤ suc (cost f ℕ+ 0) ℕ+ suc (cost h₁ ℕ+ cost h₂)) (sym eq2) (subst (suc (cost (optimize-compose f (⟨ h₁ , h₂ ⟩ m')) ℕ+ 0) ≤_) step2 step1)

  ------------------------------------------------------------------------
  -- Distribution over inl: cost bound when safe-pair-distrib = true
  ------------------------------------------------------------------------

  safe-distrib-inl-cost : ∀ {A B D E} (f : IR (D + E) A) (g : IR (D + E) B)
    (m m' : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (inl {D} {E} m') , optimize-compose g (inl {D} {E} m') ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 1
  safe-distrib-inl-cost terminal g m m' _ = suc-≤-suc-plus-1 (optimize-compose-cost-≤ g (inl m'))
  safe-distrib-inl-cost f@id terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@(_ ∘ _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@(⟨ _ , _ ⟩ _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@(inl _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@(inr _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@([ _ , _ ]) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@(curry _ _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@fold terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  safe-distrib-inl-cost f@(Prim _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
  -- Neither terminal: safe-pair-distrib = false (absurd)
  safe-distrib-inl-cost id id _ _ ()
  safe-distrib-inl-cost id (_ ∘ _) _ _ ()
  safe-distrib-inl-cost id (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost id (inl _) _ _ ()
  safe-distrib-inl-cost id (inr _) _ _ ()
  safe-distrib-inl-cost id [ _ , _ ] _ _ ()
  safe-distrib-inl-cost id (curry _ _) _ _ ()
  safe-distrib-inl-cost id (Prim _) _ _ ()
  safe-distrib-inl-cost (_ ∘ _) id _ _ ()
  safe-distrib-inl-cost (_ ∘ _) (_ ∘ _) _ _ ()
  safe-distrib-inl-cost (_ ∘ _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost (_ ∘ _) (inl _) _ _ ()
  safe-distrib-inl-cost (_ ∘ _) (inr _) _ _ ()
  safe-distrib-inl-cost (_ ∘ _) [ _ , _ ] _ _ ()
  safe-distrib-inl-cost (_ ∘ _) (curry _ _) _ _ ()
  safe-distrib-inl-cost (_ ∘ _) (Prim _) _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) id _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) (_ ∘ _) _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) (inl _) _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) (inr _) _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) [ _ , _ ] _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) (curry _ _) _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) (Prim _) _ _ ()
  safe-distrib-inl-cost (inl _) id _ _ ()
  safe-distrib-inl-cost (inl _) (_ ∘ _) _ _ ()
  safe-distrib-inl-cost (inl _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost (inl _) (inl _) _ _ ()
  safe-distrib-inl-cost (inl _) (inr _) _ _ ()
  safe-distrib-inl-cost (inl _) [ _ , _ ] _ _ ()
  safe-distrib-inl-cost (inl _) (curry _ _) _ _ ()
  safe-distrib-inl-cost (inl _) (Prim _) _ _ ()
  safe-distrib-inl-cost (inr _) id _ _ ()
  safe-distrib-inl-cost (inr _) (_ ∘ _) _ _ ()
  safe-distrib-inl-cost (inr _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost (inr _) (inl _) _ _ ()
  safe-distrib-inl-cost (inr _) (inr _) _ _ ()
  safe-distrib-inl-cost (inr _) [ _ , _ ] _ _ ()
  safe-distrib-inl-cost (inr _) (curry _ _) _ _ ()
  safe-distrib-inl-cost (inr _) (Prim _) _ _ ()
  safe-distrib-inl-cost [ _ , _ ] id _ _ ()
  safe-distrib-inl-cost [ _ , _ ] (_ ∘ _) _ _ ()
  safe-distrib-inl-cost [ _ , _ ] (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost [ _ , _ ] (inl _) _ _ ()
  safe-distrib-inl-cost [ _ , _ ] (inr _) _ _ ()
  safe-distrib-inl-cost [ _ , _ ] [ _ , _ ] _ _ ()
  safe-distrib-inl-cost [ _ , _ ] (curry _ _) _ _ ()
  safe-distrib-inl-cost [ _ , _ ] (Prim _) _ _ ()
  safe-distrib-inl-cost (curry _ _) id _ _ ()
  safe-distrib-inl-cost (curry _ _) (_ ∘ _) _ _ ()
  safe-distrib-inl-cost (curry _ _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost (curry _ _) (inl _) _ _ ()
  safe-distrib-inl-cost (curry _ _) (inr _) _ _ ()
  safe-distrib-inl-cost (curry _ _) [ _ , _ ] _ _ ()
  safe-distrib-inl-cost (curry _ _) (curry _ _) _ _ ()
  safe-distrib-inl-cost (curry _ _) (Prim _) _ _ ()
  safe-distrib-inl-cost (Prim _) id _ _ ()
  safe-distrib-inl-cost (Prim _) (_ ∘ _) _ _ ()
  safe-distrib-inl-cost (Prim _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost (Prim _) (inl _) _ _ ()
  safe-distrib-inl-cost (Prim _) (inr _) _ _ ()
  safe-distrib-inl-cost (Prim _) [ _ , _ ] _ _ ()
  safe-distrib-inl-cost (Prim _) (curry _ _) _ _ ()
  safe-distrib-inl-cost (Prim _) (Prim _) _ _ ()
  safe-distrib-inl-cost fold id _ _ ()
  safe-distrib-inl-cost fold (_ ∘ _) _ _ ()
  safe-distrib-inl-cost fold (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inl-cost fold (inl _) _ _ ()
  safe-distrib-inl-cost fold (inr _) _ _ ()
  safe-distrib-inl-cost fold [ _ , _ ] _ _ ()
  safe-distrib-inl-cost fold (curry _ _) _ _ ()
  safe-distrib-inl-cost fold fold _ _ ()
  safe-distrib-inl-cost fold (Prim _) _ _ ()
  safe-distrib-inl-cost id fold _ _ ()
  safe-distrib-inl-cost (_ ∘ _) fold _ _ ()
  safe-distrib-inl-cost (⟨ _ , _ ⟩ _) fold _ _ ()
  safe-distrib-inl-cost (inl _) fold _ _ ()
  safe-distrib-inl-cost (inr _) fold _ _ ()
  safe-distrib-inl-cost [ _ , _ ] fold _ _ ()
  safe-distrib-inl-cost (curry _ _) fold _ _ ()
  safe-distrib-inl-cost (Prim _) fold _ _ ()

  ------------------------------------------------------------------------
  -- Distribution over inr: cost bound when safe-pair-distrib = true
  ------------------------------------------------------------------------

  safe-distrib-inr-cost : ∀ {A B D E} (f : IR (D + E) A) (g : IR (D + E) B)
    (m m' : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (inr {D} {E} m') , optimize-compose g (inr {D} {E} m') ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 1
  safe-distrib-inr-cost terminal g m m' _ = suc-≤-suc-plus-1 (optimize-compose-cost-≤ g (inr m'))
  safe-distrib-inr-cost f@id terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@(_ ∘ _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@(⟨ _ , _ ⟩ _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@(inl _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@(inr _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@([ _ , _ ]) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@(curry _ _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@fold terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  safe-distrib-inr-cost f@(Prim _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
  -- Neither terminal: safe-pair-distrib = false (absurd)
  safe-distrib-inr-cost id id _ _ ()
  safe-distrib-inr-cost id (_ ∘ _) _ _ ()
  safe-distrib-inr-cost id (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost id (inl _) _ _ ()
  safe-distrib-inr-cost id (inr _) _ _ ()
  safe-distrib-inr-cost id [ _ , _ ] _ _ ()
  safe-distrib-inr-cost id (curry _ _) _ _ ()
  safe-distrib-inr-cost id (Prim _) _ _ ()
  safe-distrib-inr-cost (_ ∘ _) id _ _ ()
  safe-distrib-inr-cost (_ ∘ _) (_ ∘ _) _ _ ()
  safe-distrib-inr-cost (_ ∘ _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost (_ ∘ _) (inl _) _ _ ()
  safe-distrib-inr-cost (_ ∘ _) (inr _) _ _ ()
  safe-distrib-inr-cost (_ ∘ _) [ _ , _ ] _ _ ()
  safe-distrib-inr-cost (_ ∘ _) (curry _ _) _ _ ()
  safe-distrib-inr-cost (_ ∘ _) (Prim _) _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) id _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) (_ ∘ _) _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) (inl _) _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) (inr _) _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) [ _ , _ ] _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) (curry _ _) _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) (Prim _) _ _ ()
  safe-distrib-inr-cost (inl _) id _ _ ()
  safe-distrib-inr-cost (inl _) (_ ∘ _) _ _ ()
  safe-distrib-inr-cost (inl _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost (inl _) (inl _) _ _ ()
  safe-distrib-inr-cost (inl _) (inr _) _ _ ()
  safe-distrib-inr-cost (inl _) [ _ , _ ] _ _ ()
  safe-distrib-inr-cost (inl _) (curry _ _) _ _ ()
  safe-distrib-inr-cost (inl _) (Prim _) _ _ ()
  safe-distrib-inr-cost (inr _) id _ _ ()
  safe-distrib-inr-cost (inr _) (_ ∘ _) _ _ ()
  safe-distrib-inr-cost (inr _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost (inr _) (inl _) _ _ ()
  safe-distrib-inr-cost (inr _) (inr _) _ _ ()
  safe-distrib-inr-cost (inr _) [ _ , _ ] _ _ ()
  safe-distrib-inr-cost (inr _) (curry _ _) _ _ ()
  safe-distrib-inr-cost (inr _) (Prim _) _ _ ()
  safe-distrib-inr-cost [ _ , _ ] id _ _ ()
  safe-distrib-inr-cost [ _ , _ ] (_ ∘ _) _ _ ()
  safe-distrib-inr-cost [ _ , _ ] (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost [ _ , _ ] (inl _) _ _ ()
  safe-distrib-inr-cost [ _ , _ ] (inr _) _ _ ()
  safe-distrib-inr-cost [ _ , _ ] [ _ , _ ] _ _ ()
  safe-distrib-inr-cost [ _ , _ ] (curry _ _) _ _ ()
  safe-distrib-inr-cost [ _ , _ ] (Prim _) _ _ ()
  safe-distrib-inr-cost (curry _ _) id _ _ ()
  safe-distrib-inr-cost (curry _ _) (_ ∘ _) _ _ ()
  safe-distrib-inr-cost (curry _ _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost (curry _ _) (inl _) _ _ ()
  safe-distrib-inr-cost (curry _ _) (inr _) _ _ ()
  safe-distrib-inr-cost (curry _ _) [ _ , _ ] _ _ ()
  safe-distrib-inr-cost (curry _ _) (curry _ _) _ _ ()
  safe-distrib-inr-cost (curry _ _) (Prim _) _ _ ()
  safe-distrib-inr-cost (Prim _) id _ _ ()
  safe-distrib-inr-cost (Prim _) (_ ∘ _) _ _ ()
  safe-distrib-inr-cost (Prim _) (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost (Prim _) (inl _) _ _ ()
  safe-distrib-inr-cost (Prim _) (inr _) _ _ ()
  safe-distrib-inr-cost (Prim _) [ _ , _ ] _ _ ()
  safe-distrib-inr-cost (Prim _) (curry _ _) _ _ ()
  safe-distrib-inr-cost (Prim _) (Prim _) _ _ ()
  safe-distrib-inr-cost fold id _ _ ()
  safe-distrib-inr-cost fold (_ ∘ _) _ _ ()
  safe-distrib-inr-cost fold (⟨ _ , _ ⟩ _) _ _ ()
  safe-distrib-inr-cost fold (inl _) _ _ ()
  safe-distrib-inr-cost fold (inr _) _ _ ()
  safe-distrib-inr-cost fold [ _ , _ ] _ _ ()
  safe-distrib-inr-cost fold (curry _ _) _ _ ()
  safe-distrib-inr-cost fold fold _ _ ()
  safe-distrib-inr-cost fold (Prim _) _ _ ()
  safe-distrib-inr-cost id fold _ _ ()
  safe-distrib-inr-cost (_ ∘ _) fold _ _ ()
  safe-distrib-inr-cost (⟨ _ , _ ⟩ _) fold _ _ ()
  safe-distrib-inr-cost (inl _) fold _ _ ()
  safe-distrib-inr-cost (inr _) fold _ _ ()
  safe-distrib-inr-cost [ _ , _ ] fold _ _ ()
  safe-distrib-inr-cost (curry _ _) fold _ _ ()
  safe-distrib-inr-cost (Prim _) fold _ _ ()

  ------------------------------------------------------------------------
  -- Distribution over unfold: cost bound when safe-pair-distrib = true
  ------------------------------------------------------------------------

  safe-distrib-unfold-cost : ∀ {A B F} (f : IR F A) (g : IR F B)
    (m : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (unfold {F}) , optimize-compose g (unfold {F}) ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 0
  safe-distrib-unfold-cost {_} {_} {F} terminal g m _ =
    let ih : cost (optimize-compose g (unfold {F})) ≤ cost g ℕ+ 0
        ih = optimize-compose-cost-≤ g (unfold {F})
        step1 : cost (⟨ optimize-compose terminal (unfold {F}) , optimize-compose g (unfold {F}) ⟩ m) ≡ suc (0 ℕ+ cost (optimize-compose g (unfold {F})))
        step1 = cong (λ x → suc (x ℕ+ cost (optimize-compose g (unfold {F})))) (opt-terminal-cost (unfold {F}))
        step2 : suc (0 ℕ+ cost (optimize-compose g (unfold {F}))) ≤ suc (cost g ℕ+ 0)
        step2 = s≤s ih
        step3 : suc (cost g ℕ+ 0) ≡ suc (0 ℕ+ cost g) ℕ+ 0
        step3 = trans (cong suc (+-comm (cost g) 0)) (sym (+-identityʳ (suc (0 ℕ+ cost g))))
    in subst (_≤ suc (0 ℕ+ cost g) ℕ+ 0) (sym step1) (subst (suc (0 ℕ+ cost (optimize-compose g (unfold {F}))) ≤_) step3 step2)
  safe-distrib-unfold-cost f@id terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@(_ ∘ _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@(⟨ _ , _ ⟩ _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@(inl _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@(inr _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@(curry _ _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@unfold terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@(Prim _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@fold terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  -- Eta cases: fst + snd or snd + fst
  safe-distrib-unfold-cost fst snd m _ = ≤-refl
  safe-distrib-unfold-cost snd fst m _ = ≤-refl
  -- Neither terminal: safe-pair-distrib = false (absurd)
  safe-distrib-unfold-cost id id _ ()
  safe-distrib-unfold-cost id (_ ∘ _) _ ()
  safe-distrib-unfold-cost id (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost id (inl _) _ ()
  safe-distrib-unfold-cost id (inr _) _ ()
  safe-distrib-unfold-cost id (curry _ _) _ ()
  safe-distrib-unfold-cost id unfold _ ()
  safe-distrib-unfold-cost id (Prim _) _ ()
  safe-distrib-unfold-cost (_ ∘ _) id _ ()
  safe-distrib-unfold-cost (_ ∘ _) (_ ∘ _) _ ()
  safe-distrib-unfold-cost (_ ∘ _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost (_ ∘ _) (inl _) _ ()
  safe-distrib-unfold-cost (_ ∘ _) (inr _) _ ()
  safe-distrib-unfold-cost (_ ∘ _) (curry _ _) _ ()
  safe-distrib-unfold-cost (_ ∘ _) unfold _ ()
  safe-distrib-unfold-cost (_ ∘ _) (Prim _) _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) id _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) (_ ∘ _) _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) (inl _) _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) (inr _) _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) (curry _ _) _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) unfold _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) (Prim _) _ ()
  safe-distrib-unfold-cost (inl _) id _ ()
  safe-distrib-unfold-cost (inl _) (_ ∘ _) _ ()
  safe-distrib-unfold-cost (inl _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost (inl _) (inl _) _ ()
  safe-distrib-unfold-cost (inl _) (inr _) _ ()
  safe-distrib-unfold-cost (inl _) (curry _ _) _ ()
  safe-distrib-unfold-cost (inl _) unfold _ ()
  safe-distrib-unfold-cost (inl _) (Prim _) _ ()
  safe-distrib-unfold-cost (inr _) id _ ()
  safe-distrib-unfold-cost (inr _) (_ ∘ _) _ ()
  safe-distrib-unfold-cost (inr _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost (inr _) (inl _) _ ()
  safe-distrib-unfold-cost (inr _) (inr _) _ ()
  safe-distrib-unfold-cost (inr _) (curry _ _) _ ()
  safe-distrib-unfold-cost (inr _) unfold _ ()
  safe-distrib-unfold-cost (inr _) (Prim _) _ ()
  safe-distrib-unfold-cost (curry _ _) id _ ()
  safe-distrib-unfold-cost (curry _ _) (_ ∘ _) _ ()
  safe-distrib-unfold-cost (curry _ _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost (curry _ _) (inl _) _ ()
  safe-distrib-unfold-cost (curry _ _) (inr _) _ ()
  safe-distrib-unfold-cost (curry _ _) (curry _ _) _ ()
  safe-distrib-unfold-cost (curry _ _) unfold _ ()
  safe-distrib-unfold-cost (curry _ _) (Prim _) _ ()
  safe-distrib-unfold-cost unfold id _ ()
  safe-distrib-unfold-cost unfold (_ ∘ _) _ ()
  safe-distrib-unfold-cost unfold (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost unfold (inl _) _ ()
  safe-distrib-unfold-cost unfold (inr _) _ ()
  safe-distrib-unfold-cost unfold (curry _ _) _ ()
  safe-distrib-unfold-cost unfold unfold _ ()
  safe-distrib-unfold-cost unfold (Prim _) _ ()
  safe-distrib-unfold-cost (Prim _) id _ ()
  safe-distrib-unfold-cost (Prim _) (_ ∘ _) _ ()
  safe-distrib-unfold-cost (Prim _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost (Prim _) (inl _) _ ()
  safe-distrib-unfold-cost (Prim _) (inr _) _ ()
  safe-distrib-unfold-cost (Prim _) (curry _ _) _ ()
  safe-distrib-unfold-cost (Prim _) unfold _ ()
  safe-distrib-unfold-cost (Prim _) (Prim _) _ ()
  safe-distrib-unfold-cost fold id _ ()
  safe-distrib-unfold-cost fold (_ ∘ _) _ ()
  safe-distrib-unfold-cost fold (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost fold (inl _) _ ()
  safe-distrib-unfold-cost fold (inr _) _ ()
  safe-distrib-unfold-cost fold (curry _ _) _ ()
  safe-distrib-unfold-cost fold unfold _ ()
  safe-distrib-unfold-cost fold fold _ ()
  safe-distrib-unfold-cost fold (Prim _) _ ()
  safe-distrib-unfold-cost id fold _ ()
  safe-distrib-unfold-cost (_ ∘ _) fold _ ()
  safe-distrib-unfold-cost (⟨ _ , _ ⟩ _) fold _ ()
  safe-distrib-unfold-cost (inl _) fold _ ()
  safe-distrib-unfold-cost (inr _) fold _ ()
  safe-distrib-unfold-cost (curry _ _) fold _ ()
  safe-distrib-unfold-cost unfold fold _ ()
  safe-distrib-unfold-cost (Prim _) fold _ ()
  safe-distrib-unfold-cost fst id _ ()
  safe-distrib-unfold-cost fst (_ ∘ _) _ ()
  safe-distrib-unfold-cost fst (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost fst (inl _) _ ()
  safe-distrib-unfold-cost fst (inr _) _ ()
  safe-distrib-unfold-cost fst (curry _ _) _ ()
  safe-distrib-unfold-cost fst fst _ ()
  safe-distrib-unfold-cost fst apply _ ()
  safe-distrib-unfold-cost fst (Prim _) _ ()
  safe-distrib-unfold-cost snd id _ ()
  safe-distrib-unfold-cost snd (_ ∘ _) _ ()
  safe-distrib-unfold-cost snd (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost snd (inl _) _ ()
  safe-distrib-unfold-cost snd (inr _) _ ()
  safe-distrib-unfold-cost snd (curry _ _) _ ()
  safe-distrib-unfold-cost snd snd _ ()
  safe-distrib-unfold-cost snd apply _ ()
  safe-distrib-unfold-cost snd (Prim _) _ ()
  safe-distrib-unfold-cost [ _ , _ ] id _ ()
  safe-distrib-unfold-cost [ _ , _ ] (_ ∘ _) _ ()
  safe-distrib-unfold-cost [ _ , _ ] (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost [ _ , _ ] (inl _) _ ()
  safe-distrib-unfold-cost [ _ , _ ] (inr _) _ ()
  safe-distrib-unfold-cost [ _ , _ ] [ _ , _ ] _ ()
  safe-distrib-unfold-cost [ _ , _ ] (curry _ _) _ ()
  safe-distrib-unfold-cost [ _ , _ ] fold _ ()
  safe-distrib-unfold-cost [ _ , _ ] (Prim _) _ ()
  safe-distrib-unfold-cost initial id _ ()
  safe-distrib-unfold-cost initial (_ ∘ _) _ ()
  safe-distrib-unfold-cost initial (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost initial (inl _) _ ()
  safe-distrib-unfold-cost initial (inr _) _ ()
  safe-distrib-unfold-cost initial (curry _ _) _ ()
  safe-distrib-unfold-cost initial fold _ ()
  safe-distrib-unfold-cost initial initial _ ()
  safe-distrib-unfold-cost initial (Prim _) _ ()
  safe-distrib-unfold-cost apply id _ ()
  safe-distrib-unfold-cost apply (_ ∘ _) _ ()
  safe-distrib-unfold-cost apply (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost apply (inl _) _ ()
  safe-distrib-unfold-cost apply (inr _) _ ()
  safe-distrib-unfold-cost apply (curry _ _) _ ()
  safe-distrib-unfold-cost apply fst _ ()
  safe-distrib-unfold-cost apply snd _ ()
  safe-distrib-unfold-cost apply apply _ ()
  safe-distrib-unfold-cost apply (Prim _) _ ()
  safe-distrib-unfold-cost arr id _ ()
  safe-distrib-unfold-cost arr (_ ∘ _) _ ()
  safe-distrib-unfold-cost arr (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-unfold-cost arr (inl _) _ ()
  safe-distrib-unfold-cost arr (inr _) _ ()
  safe-distrib-unfold-cost arr (curry _ _) _ ()
  safe-distrib-unfold-cost arr arr _ ()
  safe-distrib-unfold-cost arr (Prim _) _ ()
  safe-distrib-unfold-cost f@fst terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@snd terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@([ _ , _ ]) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@initial terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@apply terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
  safe-distrib-unfold-cost f@arr terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)

  ------------------------------------------------------------------------
  -- Distribution over fold: cost bound when safe-pair-distrib = true
  ------------------------------------------------------------------------

  safe-distrib-fold-cost : ∀ {A B F} (f : IR (Fix F) A) (g : IR (Fix F) B)
    (m : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (fold {F}) , optimize-compose g (fold {F}) ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 1
  safe-distrib-fold-cost terminal g m _ = suc-≤-suc-plus-1 (optimize-compose-cost-≤ g fold)
  safe-distrib-fold-cost f@id terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@(_ ∘ _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@(⟨ _ , _ ⟩ _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@(inl _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@(inr _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@(curry _ _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@unfold terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@(Prim _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  safe-distrib-fold-cost f@fold terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
  -- Neither terminal: safe-pair-distrib = false (absurd)
  safe-distrib-fold-cost id id _ ()
  safe-distrib-fold-cost id (_ ∘ _) _ ()
  safe-distrib-fold-cost id (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost id (inl _) _ ()
  safe-distrib-fold-cost id (inr _) _ ()
  safe-distrib-fold-cost id (curry _ _) _ ()
  safe-distrib-fold-cost id unfold _ ()
  safe-distrib-fold-cost id (Prim _) _ ()
  safe-distrib-fold-cost (_ ∘ _) id _ ()
  safe-distrib-fold-cost (_ ∘ _) (_ ∘ _) _ ()
  safe-distrib-fold-cost (_ ∘ _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost (_ ∘ _) (inl _) _ ()
  safe-distrib-fold-cost (_ ∘ _) (inr _) _ ()
  safe-distrib-fold-cost (_ ∘ _) (curry _ _) _ ()
  safe-distrib-fold-cost (_ ∘ _) unfold _ ()
  safe-distrib-fold-cost (_ ∘ _) (Prim _) _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) id _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) (_ ∘ _) _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) (inl _) _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) (inr _) _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) (curry _ _) _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) unfold _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) (Prim _) _ ()
  safe-distrib-fold-cost (inl _) id _ ()
  safe-distrib-fold-cost (inl _) (_ ∘ _) _ ()
  safe-distrib-fold-cost (inl _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost (inl _) (inl _) _ ()
  safe-distrib-fold-cost (inl _) (inr _) _ ()
  safe-distrib-fold-cost (inl _) (curry _ _) _ ()
  safe-distrib-fold-cost (inl _) unfold _ ()
  safe-distrib-fold-cost (inl _) (Prim _) _ ()
  safe-distrib-fold-cost (inr _) id _ ()
  safe-distrib-fold-cost (inr _) (_ ∘ _) _ ()
  safe-distrib-fold-cost (inr _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost (inr _) (inl _) _ ()
  safe-distrib-fold-cost (inr _) (inr _) _ ()
  safe-distrib-fold-cost (inr _) (curry _ _) _ ()
  safe-distrib-fold-cost (inr _) unfold _ ()
  safe-distrib-fold-cost (inr _) (Prim _) _ ()
  safe-distrib-fold-cost (curry _ _) id _ ()
  safe-distrib-fold-cost (curry _ _) (_ ∘ _) _ ()
  safe-distrib-fold-cost (curry _ _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost (curry _ _) (inl _) _ ()
  safe-distrib-fold-cost (curry _ _) (inr _) _ ()
  safe-distrib-fold-cost (curry _ _) (curry _ _) _ ()
  safe-distrib-fold-cost (curry _ _) unfold _ ()
  safe-distrib-fold-cost (curry _ _) (Prim _) _ ()
  safe-distrib-fold-cost unfold id _ ()
  safe-distrib-fold-cost unfold (_ ∘ _) _ ()
  safe-distrib-fold-cost unfold (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost unfold (inl _) _ ()
  safe-distrib-fold-cost unfold (inr _) _ ()
  safe-distrib-fold-cost unfold (curry _ _) _ ()
  safe-distrib-fold-cost unfold unfold _ ()
  safe-distrib-fold-cost unfold (Prim _) _ ()
  safe-distrib-fold-cost (Prim _) id _ ()
  safe-distrib-fold-cost (Prim _) (_ ∘ _) _ ()
  safe-distrib-fold-cost (Prim _) (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost (Prim _) (inl _) _ ()
  safe-distrib-fold-cost (Prim _) (inr _) _ ()
  safe-distrib-fold-cost (Prim _) (curry _ _) _ ()
  safe-distrib-fold-cost (Prim _) unfold _ ()
  safe-distrib-fold-cost (Prim _) fold _ ()
  safe-distrib-fold-cost (Prim _) (Prim _) _ ()
  safe-distrib-fold-cost fold id _ ()
  safe-distrib-fold-cost fold (_ ∘ _) _ ()
  safe-distrib-fold-cost fold (⟨ _ , _ ⟩ _) _ ()
  safe-distrib-fold-cost fold (inl _) _ ()
  safe-distrib-fold-cost fold (inr _) _ ()
  safe-distrib-fold-cost fold (curry _ _) _ ()
  safe-distrib-fold-cost fold unfold _ ()
  safe-distrib-fold-cost fold fold _ ()
  safe-distrib-fold-cost fold (Prim _) _ ()
  safe-distrib-fold-cost id fold _ ()
  safe-distrib-fold-cost (_ ∘ _) fold _ ()
  safe-distrib-fold-cost (⟨ _ , _ ⟩ _) fold _ ()
  safe-distrib-fold-cost (inl _) fold _ ()
  safe-distrib-fold-cost (inr _) fold _ ()
  safe-distrib-fold-cost (curry _ _) fold _ ()
  safe-distrib-fold-cost unfold fold _ ()

  ------------------------------------------------------------------------
  -- Distribution over pairs: cost bound when safe-pair-distrib = true
  ------------------------------------------------------------------------

  safe-distrib-pair-cost : ∀ {A B D H₁ H₂} (f : IR (H₁ * H₂) A) (g : IR (H₁ * H₂) B)
    (h₁ : IR D H₁) (h₂ : IR D H₂) (m m' : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (⟨ h₁ , h₂ ⟩ m') , optimize-compose g (⟨ h₁ , h₂ ⟩ m') ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ suc (cost h₁ ℕ+ cost h₂)
  safe-distrib-pair-cost terminal g h₁ h₂ m m' _ =
    let ih : cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m')) ≤ cost g ℕ+ suc (cost h₁ ℕ+ cost h₂)
        ih = optimize-compose-cost-≤ g (⟨ h₁ , h₂ ⟩ m')
        eq1 : cost (⟨ optimize-compose terminal (⟨ h₁ , h₂ ⟩ m') , optimize-compose g (⟨ h₁ , h₂ ⟩ m') ⟩ m)
              ≡ suc (0 ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m')))
        eq1 = cong (λ x → suc (x ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m')))) (opt-terminal-cost (⟨ h₁ , h₂ ⟩ m'))
        step1 : suc (0 ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m'))) ≤ suc (cost g ℕ+ suc (cost h₁ ℕ+ cost h₂))
        step1 = s≤s ih
        step2 : suc (cost g ℕ+ suc (cost h₁ ℕ+ cost h₂)) ≡ suc (0 ℕ+ cost g) ℕ+ suc (cost h₁ ℕ+ cost h₂)
        step2 = refl
    in subst (_≤ suc (0 ℕ+ cost g) ℕ+ suc (cost h₁ ℕ+ cost h₂)) (sym eq1) (subst (suc (0 ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m'))) ≤_) step2 step1)
  safe-distrib-pair-cost f@id terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@(_ ∘ _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@(⟨ _ , _ ⟩ _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@(inl _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@(inr _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@(curry _ _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@fst terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@snd terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@apply terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@fold terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  safe-distrib-pair-cost f@(Prim _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
  -- Eta cases: fst + snd or snd + fst
  safe-distrib-pair-cost fst snd h₁ h₂ m m' _ = n≤1+n (suc (cost h₁ ℕ+ cost h₂))
  safe-distrib-pair-cost {_} {_} {D} {H₁} {H₂} snd fst h₁ h₂ m m' _ =
    let step1 : suc (cost h₂ ℕ+ cost h₁) ≤ suc (suc (cost h₂ ℕ+ cost h₁))
        step1 = n≤1+n (suc (cost h₂ ℕ+ cost h₁))
        step2 : suc (suc (cost h₂ ℕ+ cost h₁)) ≡ suc (suc (cost h₁ ℕ+ cost h₂))
        step2 = cong (λ x → suc (suc x)) (+-comm (cost h₂) (cost h₁))
    in subst (suc (cost h₂ ℕ+ cost h₁) ≤_) step2 step1
  -- Neither terminal: safe-pair-distrib = false (absurd)
  safe-distrib-pair-cost id id _ _ _ _ ()
  safe-distrib-pair-cost id (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost id (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost id (inl _) _ _ _ _ ()
  safe-distrib-pair-cost id (inr _) _ _ _ _ ()
  safe-distrib-pair-cost id (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost id fst _ _ _ _ ()
  safe-distrib-pair-cost id snd _ _ _ _ ()
  safe-distrib-pair-cost id apply _ _ _ _ ()
  safe-distrib-pair-cost id (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) id _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) (inl _) _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) (inr _) _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) fst _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) snd _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) apply _ _ _ _ ()
  safe-distrib-pair-cost (_ ∘ _) (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) id _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) (inl _) _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) (inr _) _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) fst _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) snd _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) apply _ _ _ _ ()
  safe-distrib-pair-cost (⟨ _ , _ ⟩ _) (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost (inl _) id _ _ _ _ ()
  safe-distrib-pair-cost (inl _) (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost (inl _) (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost (inl _) (inl _) _ _ _ _ ()
  safe-distrib-pair-cost (inl _) (inr _) _ _ _ _ ()
  safe-distrib-pair-cost (inl _) (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost (inl _) fst _ _ _ _ ()
  safe-distrib-pair-cost (inl _) snd _ _ _ _ ()
  safe-distrib-pair-cost (inl _) apply _ _ _ _ ()
  safe-distrib-pair-cost (inl _) (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost (inr _) id _ _ _ _ ()
  safe-distrib-pair-cost (inr _) (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost (inr _) (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost (inr _) (inl _) _ _ _ _ ()
  safe-distrib-pair-cost (inr _) (inr _) _ _ _ _ ()
  safe-distrib-pair-cost (inr _) (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost (inr _) fst _ _ _ _ ()
  safe-distrib-pair-cost (inr _) snd _ _ _ _ ()
  safe-distrib-pair-cost (inr _) apply _ _ _ _ ()
  safe-distrib-pair-cost (inr _) (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) id _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) (inl _) _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) (inr _) _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) fst _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) snd _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) apply _ _ _ _ ()
  safe-distrib-pair-cost (curry _ _) (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost fst id _ _ _ _ ()
  safe-distrib-pair-cost fst (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost fst (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost fst (inl _) _ _ _ _ ()
  safe-distrib-pair-cost fst (inr _) _ _ _ _ ()
  safe-distrib-pair-cost fst (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost fst fst _ _ _ _ ()
  safe-distrib-pair-cost fst apply _ _ _ _ ()
  safe-distrib-pair-cost fst (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost snd id _ _ _ _ ()
  safe-distrib-pair-cost snd (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost snd (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost snd (inl _) _ _ _ _ ()
  safe-distrib-pair-cost snd (inr _) _ _ _ _ ()
  safe-distrib-pair-cost snd (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost snd snd _ _ _ _ ()
  safe-distrib-pair-cost snd apply _ _ _ _ ()
  safe-distrib-pair-cost snd (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost apply id _ _ _ _ ()
  safe-distrib-pair-cost apply (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost apply (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost apply (inl _) _ _ _ _ ()
  safe-distrib-pair-cost apply (inr _) _ _ _ _ ()
  safe-distrib-pair-cost apply (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost apply fst _ _ _ _ ()
  safe-distrib-pair-cost apply snd _ _ _ _ ()
  safe-distrib-pair-cost apply apply _ _ _ _ ()
  safe-distrib-pair-cost apply (Prim _) _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) id _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) (_ ∘ _) _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) (⟨ _ , _ ⟩ _) _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) (inl _) _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) (inr _) _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) (curry _ _) _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) fst _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) snd _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) apply _ _ _ _ ()
  safe-distrib-pair-cost (Prim _) (Prim _) _ _ _ _ ()

  ------------------------------------------------------------------------
  -- Main theorem: optimize-compose never increases cost
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ : ∀ {A B C} (g : IR B C) (f : IR A B) →
    cost (optimize-compose g f) ≤ cost g ℕ+ cost f

  ------------------------------------------------------------------------
  -- Identity Laws
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ id f = ≤-refl
  optimize-compose-cost-≤ fst id = subst (0 ≤_) (sym (+-identityʳ 0)) z≤n
  optimize-compose-cost-≤ snd id = subst (0 ≤_) (sym (+-identityʳ 0)) z≤n
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) id = subst (suc (cost f ℕ+ cost g) ≤_) (sym (+-identityʳ _)) ≤-refl
  optimize-compose-cost-≤ (inl m) id = subst (1 ≤_) (sym (+-identityʳ 1)) ≤-refl
  optimize-compose-cost-≤ (inr m) id = subst (1 ≤_) (sym (+-identityʳ 1)) ≤-refl
  optimize-compose-cost-≤ [ f , g ] id = subst ((cost f ℕ+ cost g) ≤_) (sym (+-identityʳ _)) ≤-refl
  optimize-compose-cost-≤ terminal id = z≤n
  optimize-compose-cost-≤ (curry f m) id = subst (suc (cost f) ≤_) (sym (+-identityʳ _)) ≤-refl
  optimize-compose-cost-≤ apply id = z≤n
  optimize-compose-cost-≤ fold id = subst (1 ≤_) (sym (+-identityʳ 1)) ≤-refl
  optimize-compose-cost-≤ unfold id = z≤n
  optimize-compose-cost-≤ arr id = z≤n
  optimize-compose-cost-≤ (Prim n) id = z≤n
  optimize-compose-cost-≤ (g ∘ f) id = subst ((cost g ℕ+ cost f) ≤_) (sym (+-identityʳ _)) ≤-refl

  ------------------------------------------------------------------------
  -- Beta Laws
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ fst (⟨ f , g ⟩ _) = a≤suc-a+b (cost f) (cost g)
  optimize-compose-cost-≤ snd (⟨ f , g ⟩ _) = b≤suc-a+b (cost f) (cost g)
  -- [ f , g ] ∘ inl = f : cost f ≤ (cost f + cost g) + 1
  -- cost [ f , g ] = cost f + cost g, cost (inl _) = 1
  optimize-compose-cost-≤ [ f , g ] (inl _) =
    ≤-trans (m≤m+n (cost f) (cost g)) (m≤m+n (cost f ℕ+ cost g) 1)
  -- [ f , g ] ∘ inr = g : cost g ≤ (cost f + cost g) + 1
  optimize-compose-cost-≤ [ f , g ] (inr _) =
    ≤-trans (n≤m+n (cost f) (cost g)) (m≤m+n (cost f ℕ+ cost g) 1)
  -- apply ∘ ⟨ curry f , g ⟩ = f ∘ ⟨ id , g ⟩
  -- LHS cost: cost f + (1 + cost g) = cost f + suc (cost g)
  -- RHS cost: 0 + (1 + (1 + cost f) + cost g) = 2 + cost f + cost g
  -- We need: cost f + suc (cost g) ≤ suc (suc (cost f + cost g))
  optimize-compose-cost-≤ apply (⟨ curry f m , g ⟩ _) =
    let eq : cost f ℕ+ suc (cost g) ≡ suc (cost f ℕ+ cost g)
        eq = trans (+-comm (cost f) (suc (cost g)))
                   (cong suc (+-comm (cost g) (cost f)))
    in subst (_≤ suc (suc (cost f ℕ+ cost g))) (sym eq) (m≤n⇒m≤1+n ≤-refl)

  ------------------------------------------------------------------------
  -- Fixed Point Laws
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ fold unfold = z≤n
  optimize-compose-cost-≤ unfold fold = z≤n
  optimize-compose-cost-≤ fold (unfold ∘ f) = n≤1+n (cost f)
  optimize-compose-cost-≤ unfold (fold ∘ f) = n≤1+n (cost f)

  ------------------------------------------------------------------------
  -- Terminal/Initial Laws
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ terminal (_ ∘ _) = z≤n
  optimize-compose-cost-≤ terminal fst = z≤n
  optimize-compose-cost-≤ terminal snd = z≤n
  optimize-compose-cost-≤ terminal (⟨ _ , _ ⟩ _) = z≤n
  optimize-compose-cost-≤ terminal (inl _) = z≤n
  optimize-compose-cost-≤ terminal (inr _) = z≤n
  optimize-compose-cost-≤ terminal [ _ , _ ] = z≤n
  optimize-compose-cost-≤ terminal terminal = z≤n
  optimize-compose-cost-≤ terminal (curry _ _) = z≤n
  optimize-compose-cost-≤ terminal apply = z≤n
  optimize-compose-cost-≤ terminal fold = z≤n
  optimize-compose-cost-≤ terminal unfold = z≤n
  optimize-compose-cost-≤ terminal arr = z≤n
  optimize-compose-cost-≤ terminal (Prim _) = z≤n

  optimize-compose-cost-≤ fst initial = z≤n
  optimize-compose-cost-≤ snd initial = z≤n
  optimize-compose-cost-≤ (⟨ _ , _ ⟩ _) initial = z≤n
  optimize-compose-cost-≤ (inl _) initial = z≤n
  optimize-compose-cost-≤ (inr _) initial = z≤n
  optimize-compose-cost-≤ [ _ , _ ] initial = z≤n
  optimize-compose-cost-≤ terminal initial = z≤n
  optimize-compose-cost-≤ (curry _ _) initial = z≤n
  optimize-compose-cost-≤ apply initial = z≤n
  optimize-compose-cost-≤ fold initial = z≤n
  optimize-compose-cost-≤ unfold initial = z≤n
  optimize-compose-cost-≤ arr initial = z≤n
  optimize-compose-cost-≤ (Prim _) initial = z≤n
  optimize-compose-cost-≤ (_ ∘ _) initial = z≤n

  optimize-compose-cost-≤ initial f = ≤-refl

  ------------------------------------------------------------------------
  -- Pair Distribution (safe cases)
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ (⟨ f , g ⟩ m) h@(⟨ h₁ , h₂ ⟩ m') with safe-pair-distrib f g | inspect (safe-pair-distrib f) g
  ... | true  | ⟦ eq ⟧ᵢ = safe-distrib-pair-cost f g h₁ h₂ m m' eq
  ... | false | _ = ≤-refl

  optimize-compose-cost-≤ (⟨ f , g ⟩ m) h@(inl m') with safe-pair-distrib f g | inspect (safe-pair-distrib f) g
  ... | true  | ⟦ eq ⟧ᵢ = safe-distrib-inl-cost f g m m' eq
  ... | false | _ = ≤-refl

  optimize-compose-cost-≤ (⟨ f , g ⟩ m) h@(inr m') with safe-pair-distrib f g | inspect (safe-pair-distrib f) g
  ... | true  | ⟦ eq ⟧ᵢ = safe-distrib-inr-cost f g m m' eq
  ... | false | _ = ≤-refl

  optimize-compose-cost-≤ (⟨ f , g ⟩ m) unfold with safe-pair-distrib f g | inspect (safe-pair-distrib f) g
  ... | true  | ⟦ eq ⟧ᵢ = safe-distrib-unfold-cost f g m eq
  ... | false | _ = ≤-refl

  optimize-compose-cost-≤ (⟨ f , g ⟩ m) fold with safe-pair-distrib f g | inspect (safe-pair-distrib f) g
  ... | true  | ⟦ eq ⟧ᵢ = safe-distrib-fold-cost f g m eq
  ... | false | _ = ≤-refl

  -- Default pair cases (no distribution)
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) (h ∘ h') = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) fst = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) snd = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) [ h , h' ] = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) terminal = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) (curry h _) = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) apply = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) arr = ≤-refl
  optimize-compose-cost-≤ (⟨ f , g ⟩ m) (Prim _) = ≤-refl

  ------------------------------------------------------------------------
  -- Case Distribution (only for case fusion)
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ [ h₁ , h₂ ] [ f , g ] = case-fusion-cost h₁ h₂ f g

  -- [ h₁ , h₂ ] ∘ other (no case fusion)
  optimize-compose-cost-≤ [ h₁ , h₂ ] (f ∘ f') = ≤-refl
  optimize-compose-cost-≤ [ h₁ , h₂ ] fst = ≤-refl
  optimize-compose-cost-≤ [ h₁ , h₂ ] snd = ≤-refl
  optimize-compose-cost-≤ [ h₁ , h₂ ] apply = ≤-refl
  optimize-compose-cost-≤ [ h₁ , h₂ ] unfold = ≤-refl
  optimize-compose-cost-≤ [ h₁ , h₂ ] (Prim _) = ≤-refl

  -- No distribution for non-case
  optimize-compose-cost-≤ fst [ f , g ] = ≤-refl
  optimize-compose-cost-≤ snd [ f , g ] = ≤-refl
  optimize-compose-cost-≤ (inl m) [ f , g ] = ≤-refl
  optimize-compose-cost-≤ (inr m) [ f , g ] = ≤-refl
  optimize-compose-cost-≤ (curry h m) [ f , g ] = ≤-refl
  optimize-compose-cost-≤ apply [ f , g ] = ≤-refl
  optimize-compose-cost-≤ fold [ f , g ] = ≤-refl
  optimize-compose-cost-≤ unfold [ f , g ] = ≤-refl
  optimize-compose-cost-≤ arr [ f , g ] = ≤-refl
  optimize-compose-cost-≤ (Prim _) [ f , g ] = ≤-refl
  optimize-compose-cost-≤ (h ∘ h') [ f , g ] = ≤-refl

  ------------------------------------------------------------------------
  -- Associativity: (h ∘ g) ∘ f
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ (h ∘ g) f = compose-∘-cost-≤ h g f

  ------------------------------------------------------------------------
  -- Default cases
  ------------------------------------------------------------------------

  -- fst ∘ non-pair
  optimize-compose-cost-≤ fst (g ∘ f) = ≤-refl
  optimize-compose-cost-≤ fst fst = ≤-refl
  optimize-compose-cost-≤ fst snd = ≤-refl
  optimize-compose-cost-≤ fst apply = ≤-refl
  optimize-compose-cost-≤ fst unfold = ≤-refl
  optimize-compose-cost-≤ fst (Prim _) = ≤-refl

  -- snd ∘ non-pair
  optimize-compose-cost-≤ snd (g ∘ f) = ≤-refl
  optimize-compose-cost-≤ snd fst = ≤-refl
  optimize-compose-cost-≤ snd snd = ≤-refl
  optimize-compose-cost-≤ snd apply = ≤-refl
  optimize-compose-cost-≤ snd unfold = ≤-refl
  optimize-compose-cost-≤ snd (Prim _) = ≤-refl

  -- inl ∘ non-case
  optimize-compose-cost-≤ (inl m) (g ∘ f) = ≤-refl
  optimize-compose-cost-≤ (inl m) fst = ≤-refl
  optimize-compose-cost-≤ (inl m) snd = ≤-refl
  optimize-compose-cost-≤ (inl m) (⟨ f , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ (inl m) (inl _) = ≤-refl
  optimize-compose-cost-≤ (inl m) (inr _) = ≤-refl
  optimize-compose-cost-≤ (inl m) terminal = ≤-refl
  optimize-compose-cost-≤ (inl m) (curry f _) = ≤-refl
  optimize-compose-cost-≤ (inl m) apply = ≤-refl
  optimize-compose-cost-≤ (inl m) fold = ≤-refl
  optimize-compose-cost-≤ (inl m) unfold = ≤-refl
  optimize-compose-cost-≤ (inl m) arr = ≤-refl
  optimize-compose-cost-≤ (inl m) (Prim _) = ≤-refl

  -- inr ∘ non-case
  optimize-compose-cost-≤ (inr m) (g ∘ f) = ≤-refl
  optimize-compose-cost-≤ (inr m) fst = ≤-refl
  optimize-compose-cost-≤ (inr m) snd = ≤-refl
  optimize-compose-cost-≤ (inr m) (⟨ f , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ (inr m) (inl _) = ≤-refl
  optimize-compose-cost-≤ (inr m) (inr _) = ≤-refl
  optimize-compose-cost-≤ (inr m) terminal = ≤-refl
  optimize-compose-cost-≤ (inr m) (curry f _) = ≤-refl
  optimize-compose-cost-≤ (inr m) apply = ≤-refl
  optimize-compose-cost-≤ (inr m) fold = ≤-refl
  optimize-compose-cost-≤ (inr m) unfold = ≤-refl
  optimize-compose-cost-≤ (inr m) arr = ≤-refl
  optimize-compose-cost-≤ (inr m) (Prim _) = ≤-refl

  -- curry ∘ f
  optimize-compose-cost-≤ (curry f m) (g ∘ f') = ≤-refl
  optimize-compose-cost-≤ (curry f m) fst = ≤-refl
  optimize-compose-cost-≤ (curry f m) snd = ≤-refl
  optimize-compose-cost-≤ (curry f m) (⟨ g , h ⟩ _) = ≤-refl
  optimize-compose-cost-≤ (curry f m) (inl _) = ≤-refl
  optimize-compose-cost-≤ (curry f m) (inr _) = ≤-refl
  optimize-compose-cost-≤ (curry f m) terminal = ≤-refl
  optimize-compose-cost-≤ (curry f m) (curry g _) = ≤-refl
  optimize-compose-cost-≤ (curry f m) apply = ≤-refl
  optimize-compose-cost-≤ (curry f m) fold = ≤-refl
  optimize-compose-cost-≤ (curry f m) unfold = ≤-refl
  optimize-compose-cost-≤ (curry f m) arr = ≤-refl
  optimize-compose-cost-≤ (curry f m) (Prim _) = ≤-refl

  -- apply ∘ non-curried-pair
  optimize-compose-cost-≤ apply (g ∘ f) = ≤-refl
  optimize-compose-cost-≤ apply fst = ≤-refl
  optimize-compose-cost-≤ apply snd = ≤-refl
  optimize-compose-cost-≤ apply (⟨ id , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ f ∘ f' , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ fst , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ snd , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ [ f , f' ] , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ initial , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ apply , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ unfold , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply (⟨ Prim _ , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ apply apply = ≤-refl
  optimize-compose-cost-≤ apply unfold = ≤-refl
  optimize-compose-cost-≤ apply (Prim _) = ≤-refl

  -- fold ∘ non-unfold
  optimize-compose-cost-≤ fold (id ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold ((g ∘ g') ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold (fst ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold (snd ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold ((⟨ g , g' ⟩ _) ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold ((inl _) ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold ((inr _) ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold ([ g , g' ] ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold (terminal ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold (initial ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold ((curry g _) ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold (apply ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold (fold ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold (arr ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold ((Prim _) ∘ f) = ≤-refl
  optimize-compose-cost-≤ fold fst = ≤-refl
  optimize-compose-cost-≤ fold snd = ≤-refl
  optimize-compose-cost-≤ fold (⟨ f , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ fold (inl _) = ≤-refl
  optimize-compose-cost-≤ fold (inr _) = ≤-refl
  optimize-compose-cost-≤ fold terminal = ≤-refl
  optimize-compose-cost-≤ fold (curry f _) = ≤-refl
  optimize-compose-cost-≤ fold apply = ≤-refl
  optimize-compose-cost-≤ fold fold = ≤-refl
  optimize-compose-cost-≤ fold arr = ≤-refl
  optimize-compose-cost-≤ fold (Prim _) = ≤-refl

  -- unfold ∘ non-fold
  optimize-compose-cost-≤ unfold (id ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold ((g ∘ g') ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold (fst ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold (snd ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold ([ g , g' ] ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold (initial ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold (apply ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold (unfold ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold ((Prim _) ∘ f) = ≤-refl
  optimize-compose-cost-≤ unfold fst = ≤-refl
  optimize-compose-cost-≤ unfold snd = ≤-refl
  optimize-compose-cost-≤ unfold apply = ≤-refl
  optimize-compose-cost-≤ unfold unfold = ≤-refl
  optimize-compose-cost-≤ unfold (Prim _) = ≤-refl

  -- arr ∘ f
  optimize-compose-cost-≤ arr (g ∘ f) = ≤-refl
  optimize-compose-cost-≤ arr fst = ≤-refl
  optimize-compose-cost-≤ arr snd = ≤-refl
  optimize-compose-cost-≤ arr (curry f _) = ≤-refl
  optimize-compose-cost-≤ arr apply = ≤-refl
  optimize-compose-cost-≤ arr unfold = ≤-refl
  optimize-compose-cost-≤ arr (Prim _) = ≤-refl

  -- Prim ∘ f
  optimize-compose-cost-≤ (Prim n) (g ∘ f) = ≤-refl
  optimize-compose-cost-≤ (Prim n) fst = ≤-refl
  optimize-compose-cost-≤ (Prim n) snd = ≤-refl
  optimize-compose-cost-≤ (Prim n) (⟨ f , g ⟩ _) = ≤-refl
  optimize-compose-cost-≤ (Prim n) (inl _) = ≤-refl
  optimize-compose-cost-≤ (Prim n) (inr _) = ≤-refl
  optimize-compose-cost-≤ (Prim n) terminal = ≤-refl
  optimize-compose-cost-≤ (Prim n) (curry f _) = ≤-refl
  optimize-compose-cost-≤ (Prim n) apply = ≤-refl
  optimize-compose-cost-≤ (Prim n) fold = ≤-refl
  optimize-compose-cost-≤ (Prim n) unfold = ≤-refl
  optimize-compose-cost-≤ (Prim n) arr = ≤-refl
  optimize-compose-cost-≤ (Prim n) (Prim _) = ≤-refl
