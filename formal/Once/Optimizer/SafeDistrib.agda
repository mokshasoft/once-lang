------------------------------------------------------------------------
-- Once.Optimizer.SafeDistrib
--
-- Proofs that safe distribution doesn't increase cost.
-- These are the tedious case analysis proofs for the safe-distrib-* lemmas.
------------------------------------------------------------------------

module Once.Optimizer.SafeDistrib where

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
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Forward declaration (from CostProof)
------------------------------------------------------------------------

postulate
  optimize-compose-cost-≤ : ∀ {A B C} (g : IR B C) (f : IR A B) →
    cost (optimize-compose g f) ≤ cost g ℕ+ cost f

------------------------------------------------------------------------
-- Key lemma: optimize-compose terminal h = terminal for any h
-- (This holds by pattern matching on h in optimize-compose)
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Distribution over inl: cost bound when safe-pair-distrib = true
--
-- For sum types (D + E), the only way safe-pair-distrib f g = true
-- is if is-terminal? f ∨ is-terminal? g = true.
-- (fst/snd have product domain, not sum domain, so eta case is impossible)
------------------------------------------------------------------------

-- Helper: a ≤ b + 1 → suc a ≤ suc b + 1
suc-≤-suc-plus-1 : ∀ {a b} → a ≤ b ℕ+ 1 → suc a ≤ suc b ℕ+ 1
suc-≤-suc-plus-1 {a} {b} p = s≤s p

-- Helper for g = terminal case
-- Goal: cost (⟨ opt f h , opt terminal h ⟩ m) ≤ suc (cost f + 0) + cost h
-- The pair cost = suc (cost (opt f h) + cost (opt terminal h))
-- Since opt-terminal-cost shows cost (opt terminal h) = 0, we have:
--   suc (cost (opt f h) + 0) ≤ suc (cost f + 0) + cost h
-- By IH: cost (opt f h) ≤ cost f + cost h
-- Arithmetic lemma: suc (a + b) ≡ suc (a + 0) + b
-- Proof: suc (a + b) = suc (a + (0 + b)) = suc ((a + 0) + b) = suc (a + 0) + b (def)
suc-plus-rearrange : ∀ a b → suc (a ℕ+ b) ≡ suc (a ℕ+ 0) ℕ+ b
suc-plus-rearrange a b =
  trans (cong suc (cong (a ℕ+_) (sym (+-identityˡ b))))
        (cong suc (sym (+-assoc a 0 b)))

g-terminal-helper : ∀ {A B D} (f : IR D A) (h : IR B D) (m : AllocMode) →
  cost (optimize-compose f h) ≤ cost f ℕ+ cost h →
  cost (⟨ optimize-compose f h , optimize-compose terminal h ⟩ m) ≤ suc (cost f ℕ+ 0) ℕ+ cost h
g-terminal-helper {A} {B} {D} f h m ih =
  let -- cost (opt terminal h) = 0
      eq1 : cost (optimize-compose terminal h) ≡ 0
      eq1 = opt-terminal-cost h
      -- cost (⟨ opt f h , opt terminal h ⟩ m) = suc (cost (opt f h) + 0)
      eq2 : cost (⟨ optimize-compose f h , optimize-compose terminal h ⟩ m) ≡ suc (cost (optimize-compose f h) ℕ+ 0)
      eq2 = cong (λ x → suc (cost (optimize-compose f h) ℕ+ x)) eq1
      -- By IH: cost (opt f h) ≤ cost f + cost h
      -- So: suc (cost (opt f h) + 0) ≤ suc (cost f + cost h)
      step1 : suc (cost (optimize-compose f h) ℕ+ 0) ≤ suc (cost f ℕ+ cost h)
      step1 = s≤s (subst (_≤ cost f ℕ+ cost h) (sym (+-identityʳ (cost (optimize-compose f h)))) ih)
      -- suc (cost f + cost h) = suc (cost f + 0) + cost h by arithmetic
      step2 : suc (cost (optimize-compose f h) ℕ+ 0) ≤ suc (cost f ℕ+ 0) ℕ+ cost h
      step2 = subst (suc (cost (optimize-compose f h) ℕ+ 0) ≤_) (suc-plus-rearrange (cost f) (cost h)) step1
  in subst (_≤ suc (cost f ℕ+ 0) ℕ+ cost h) (sym eq2) step2

safe-distrib-inl-cost : ∀ {A B D E} (f : IR (D + E) A) (g : IR (D + E) B)
  (m m' : AllocMode) →
  safe-pair-distrib f g ≡ true →
  cost (⟨ optimize-compose f (inl {D} {E} m') , optimize-compose g (inl {D} {E} m') ⟩ m)
  ≤ suc (cost f ℕ+ cost g) ℕ+ 1
-- f = terminal case
safe-distrib-inl-cost terminal g m m' _ = suc-≤-suc-plus-1 (optimize-compose-cost-≤ g (inl m'))
-- g = terminal case (f ≠ terminal)
safe-distrib-inl-cost f@id terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
safe-distrib-inl-cost f@(_ ∘ _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
safe-distrib-inl-cost f@(⟨ _ , _ ⟩ _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
safe-distrib-inl-cost f@(inl _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
safe-distrib-inl-cost f@(inr _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
safe-distrib-inl-cost f@([ _ , _ ]) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
safe-distrib-inl-cost f@(curry _ _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
safe-distrib-inl-cost f@fold terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
-- apply has product domain, unfold has Fix domain, arr has ⊤ domain, initial has Void - type impossible
safe-distrib-inl-cost f@(Prim _) terminal m m' _ = g-terminal-helper f (inl m') m (optimize-compose-cost-≤ f (inl m'))
-- Remaining: neither f nor g is terminal, so safe-pair-distrib = false
-- Note: initial, apply, fold, unfold, arr have type-impossible domains for (D + E)
-- Only valid sum-domain constructors are: id, ∘, ⟨,⟩, inl, inr, [,], curry, Prim
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
-- Fold cases: fold has domain F[Fix F] which CAN be a sum
-- is-terminal? fold = false, so need g = terminal (already covered above)
safe-distrib-inl-cost fold id _ _ ()
safe-distrib-inl-cost fold (_ ∘ _) _ _ ()
safe-distrib-inl-cost fold (⟨ _ , _ ⟩ _) _ _ ()
safe-distrib-inl-cost fold (inl _) _ _ ()
safe-distrib-inl-cost fold (inr _) _ _ ()
safe-distrib-inl-cost fold [ _ , _ ] _ _ ()
safe-distrib-inl-cost fold (curry _ _) _ _ ()
safe-distrib-inl-cost fold fold _ _ ()
safe-distrib-inl-cost fold (Prim _) _ _ ()
-- g = fold (f non-terminal) - fold can have sum domain
safe-distrib-inl-cost id fold _ _ ()
safe-distrib-inl-cost (_ ∘ _) fold _ _ ()
safe-distrib-inl-cost (⟨ _ , _ ⟩ _) fold _ _ ()
safe-distrib-inl-cost (inl _) fold _ _ ()
safe-distrib-inl-cost (inr _) fold _ _ ()
safe-distrib-inl-cost [ _ , _ ] fold _ _ ()
safe-distrib-inl-cost (curry _ _) fold _ _ ()
safe-distrib-inl-cost (Prim _) fold _ _ ()
-- Note: unfold, apply, arr, initial have domains that can't be sums (D + E)
-- - unfold: domain is Fix F
-- - apply: domain is (A ⇒ B) * A (product)
-- - arr: domain is ⊤
-- - initial: domain is Void
-- - fst, snd: domain is A * B (product)
-- These are type-impossible for IR (D + E) _ and don't need coverage

------------------------------------------------------------------------
-- Distribution over inr: cost bound when safe-pair-distrib = true
-- Identical structure to inl since cost (inl m) = cost (inr m) = 1
------------------------------------------------------------------------

safe-distrib-inr-cost : ∀ {A B D E} (f : IR (D + E) A) (g : IR (D + E) B)
  (m m' : AllocMode) →
  safe-pair-distrib f g ≡ true →
  cost (⟨ optimize-compose f (inr {D} {E} m') , optimize-compose g (inr {D} {E} m') ⟩ m)
  ≤ suc (cost f ℕ+ cost g) ℕ+ 1
-- f = terminal case
safe-distrib-inr-cost terminal g m m' _ = suc-≤-suc-plus-1 (optimize-compose-cost-≤ g (inr m'))
-- g = terminal case (f ≠ terminal)
safe-distrib-inr-cost f@id terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@(_ ∘ _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@(⟨ _ , _ ⟩ _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@(inl _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@(inr _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@([ _ , _ ]) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@(curry _ _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@fold terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
safe-distrib-inr-cost f@(Prim _) terminal m m' _ = g-terminal-helper f (inr m') m (optimize-compose-cost-≤ f (inr m'))
-- Remaining: neither f nor g is terminal, so safe-pair-distrib = false
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
-- Fold cases
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
-- For unfold domain (Fix F), only terminal case is possible since
-- fst/snd have product domain. cost unfold = 0.
------------------------------------------------------------------------

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
      -- cost (opt f h) ≤ cost f + cost h = cost f + 0 = cost f
      step1 : cost (optimize-compose f h) ≤ cost f
      step1 = subst (cost (optimize-compose f h) ≤_) (+-identityʳ (cost f)) (subst (λ x → cost (optimize-compose f h) ≤ cost f ℕ+ x) h-cost-0 ih)
      -- suc (cost (opt f h) + 0) ≤ suc cost f
      step2 : suc (cost (optimize-compose f h) ℕ+ 0) ≤ suc (cost f)
      step2 = s≤s (subst (_≤ cost f) (sym (+-identityʳ (cost (optimize-compose f h)))) step1)
      -- suc cost f = suc (cost f + 0) + 0
      step3 : suc (cost f) ≡ suc (cost f ℕ+ 0) ℕ+ 0
      step3 = trans (cong suc (sym (+-identityʳ (cost f)))) (sym (+-identityʳ (suc (cost f ℕ+ 0))))
  in subst (_≤ suc (cost f ℕ+ 0) ℕ+ 0) (sym eq2) (subst (suc (cost (optimize-compose f h) ℕ+ 0) ≤_) step3 step2)

safe-distrib-unfold-cost : ∀ {A B F} (f : IR F A) (g : IR F B)
  (m : AllocMode) →
  safe-pair-distrib f g ≡ true →
  cost (⟨ optimize-compose f (unfold {F}) , optimize-compose g (unfold {F}) ⟩ m)
  ≤ suc (cost f ℕ+ cost g) ℕ+ 0
-- f = terminal case
safe-distrib-unfold-cost {_} {_} {F} terminal g m _ =
  let ih : cost (optimize-compose g (unfold {F})) ≤ cost g ℕ+ 0  -- cost unfold = 0
      ih = optimize-compose-cost-≤ g (unfold {F})
      -- cost (⟨ opt terminal unfold , opt g unfold ⟩ m) = suc (0 + cost (opt g unfold))
      step1 : cost (⟨ optimize-compose terminal (unfold {F}) , optimize-compose g (unfold {F}) ⟩ m) ≡ suc (0 ℕ+ cost (optimize-compose g (unfold {F})))
      step1 = cong (λ x → suc (x ℕ+ cost (optimize-compose g (unfold {F})))) (opt-terminal-cost (unfold {F}))
      -- suc (0 + x) = suc x
      step2 : suc (0 ℕ+ cost (optimize-compose g (unfold {F}))) ≤ suc (cost g ℕ+ 0)
      step2 = s≤s ih
      -- suc (cost g + 0) = suc (0 + cost g) + 0
      step3 : suc (cost g ℕ+ 0) ≡ suc (0 ℕ+ cost g) ℕ+ 0
      step3 = trans (cong suc (+-comm (cost g) 0)) (sym (+-identityʳ (suc (0 ℕ+ cost g))))
  in subst (_≤ suc (0 ℕ+ cost g) ℕ+ 0) (sym step1) (subst (suc (0 ℕ+ cost (optimize-compose g (unfold {F}))) ≤_) step3 step2)
-- g = terminal case (f ≠ terminal)
safe-distrib-unfold-cost f@id terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@(_ ∘ _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@(⟨ _ , _ ⟩ _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@(inl _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@(inr _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@(curry _ _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@unfold terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@(Prim _) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
-- fst, snd, [,], initial, apply, arr: type-impossible domains for Fix F
-- fold: domain is F[Fix F] which can equal Fix G in rare cases - need coverage
safe-distrib-unfold-cost f@fold terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
-- Remaining: neither f nor g is terminal, so safe-pair-distrib = false
-- For Fix F domain: valid constructors are id, ∘, ⟨,⟩, inl, inr, curry, unfold, fold, Prim
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
-- fold cases
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
-- fst, snd, [,], initial, apply, arr - domains that can match F[Fix F] for appropriate F
-- is-terminal? returns false for all of these, so safe-pair-distrib = false for non-terminal g
-- fst has product domain A * B - only product-domain g's are compatible
-- Eta cases: fst + snd or snd + fst
-- cost (⟨ opt fst unfold , opt snd unfold ⟩ m) = suc (0 + 0) = 1
-- suc (cost fst + cost snd) + 0 = suc (0 + 0) + 0 = 1
-- So we need 1 ≤ 1 which is ≤-refl
safe-distrib-unfold-cost fst snd m _ = ≤-refl
safe-distrib-unfold-cost snd fst m _ = ≤-refl
-- Non-eta, non-terminal cases: absurd
safe-distrib-unfold-cost fst id _ ()
safe-distrib-unfold-cost fst (_ ∘ _) _ ()
safe-distrib-unfold-cost fst (⟨ _ , _ ⟩ _) _ ()
safe-distrib-unfold-cost fst (inl _) _ ()
safe-distrib-unfold-cost fst (inr _) _ ()
safe-distrib-unfold-cost fst (curry _ _) _ ()
safe-distrib-unfold-cost fst fst _ ()
safe-distrib-unfold-cost fst apply _ ()
safe-distrib-unfold-cost fst (Prim _) _ ()
-- snd has product domain
safe-distrib-unfold-cost snd id _ ()
safe-distrib-unfold-cost snd (_ ∘ _) _ ()
safe-distrib-unfold-cost snd (⟨ _ , _ ⟩ _) _ ()
safe-distrib-unfold-cost snd (inl _) _ ()
safe-distrib-unfold-cost snd (inr _) _ ()
safe-distrib-unfold-cost snd (curry _ _) _ ()
safe-distrib-unfold-cost snd snd _ ()
safe-distrib-unfold-cost snd apply _ ()
safe-distrib-unfold-cost snd (Prim _) _ ()
-- [,] has sum domain A + B
safe-distrib-unfold-cost [ _ , _ ] id _ ()
safe-distrib-unfold-cost [ _ , _ ] (_ ∘ _) _ ()
safe-distrib-unfold-cost [ _ , _ ] (⟨ _ , _ ⟩ _) _ ()
safe-distrib-unfold-cost [ _ , _ ] (inl _) _ ()
safe-distrib-unfold-cost [ _ , _ ] (inr _) _ ()
safe-distrib-unfold-cost [ _ , _ ] [ _ , _ ] _ ()
safe-distrib-unfold-cost [ _ , _ ] (curry _ _) _ ()
safe-distrib-unfold-cost [ _ , _ ] fold _ ()
safe-distrib-unfold-cost [ _ , _ ] (Prim _) _ ()
-- initial has Void domain
safe-distrib-unfold-cost initial id _ ()
safe-distrib-unfold-cost initial (_ ∘ _) _ ()
safe-distrib-unfold-cost initial (⟨ _ , _ ⟩ _) _ ()
safe-distrib-unfold-cost initial (inl _) _ ()
safe-distrib-unfold-cost initial (inr _) _ ()
safe-distrib-unfold-cost initial (curry _ _) _ ()
safe-distrib-unfold-cost initial fold _ ()
safe-distrib-unfold-cost initial initial _ ()
safe-distrib-unfold-cost initial (Prim _) _ ()
-- apply has product domain
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
-- arr has ⊤ domain
safe-distrib-unfold-cost arr id _ ()
safe-distrib-unfold-cost arr (_ ∘ _) _ ()
safe-distrib-unfold-cost arr (⟨ _ , _ ⟩ _) _ ()
safe-distrib-unfold-cost arr (inl _) _ ()
safe-distrib-unfold-cost arr (inr _) _ ()
safe-distrib-unfold-cost arr (curry _ _) _ ()
safe-distrib-unfold-cost arr arr _ ()
safe-distrib-unfold-cost arr (Prim _) _ ()
-- f = fst/snd/[]/initial/apply/arr with g = terminal (use helper)
safe-distrib-unfold-cost f@fst terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@snd terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@([ _ , _ ]) terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@initial terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@apply terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)
safe-distrib-unfold-cost f@arr terminal m _ = g-terminal-helper-0 f unfold m refl (optimize-compose-cost-≤ f unfold)

------------------------------------------------------------------------
-- Distribution over fold: cost bound when safe-pair-distrib = true
-- For Fix F domain, only terminal case is possible. cost fold = 1.
------------------------------------------------------------------------

safe-distrib-fold-cost : ∀ {A B F} (f : IR (Fix F) A) (g : IR (Fix F) B)
  (m : AllocMode) →
  safe-pair-distrib f g ≡ true →
  cost (⟨ optimize-compose f (fold {F}) , optimize-compose g (fold {F}) ⟩ m)
  ≤ suc (cost f ℕ+ cost g) ℕ+ 1
-- f = terminal case
safe-distrib-fold-cost terminal g m _ = suc-≤-suc-plus-1 (optimize-compose-cost-≤ g fold)
-- g = terminal case (f ≠ terminal)
safe-distrib-fold-cost f@id terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
safe-distrib-fold-cost f@(_ ∘ _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
safe-distrib-fold-cost f@(⟨ _ , _ ⟩ _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
safe-distrib-fold-cost f@(inl _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
safe-distrib-fold-cost f@(inr _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
safe-distrib-fold-cost f@(curry _ _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
safe-distrib-fold-cost f@unfold terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
safe-distrib-fold-cost f@(Prim _) terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
-- fold has domain F[Fix F] which may match Fix G in some cases
safe-distrib-fold-cost f@fold terminal m _ = g-terminal-helper f fold m (optimize-compose-cost-≤ f fold)
-- Remaining: neither f nor g is terminal, so safe-pair-distrib = false
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
-- fold cases
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
-- This is the main case with both eta (fst/snd) and terminal cases.
-- Domain is H₁ * H₂, so fst/snd/apply are valid, [,]/initial/arr are not.
------------------------------------------------------------------------

-- Helper for pair cost with g = terminal
-- Note: the result type uses ⊤ as codomain for terminal since terminal : IR A ⊤
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

safe-distrib-pair-cost : ∀ {A B D H₁ H₂} (f : IR (H₁ * H₂) A) (g : IR (H₁ * H₂) B)
  (h₁ : IR D H₁) (h₂ : IR D H₂) (m m' : AllocMode) →
  safe-pair-distrib f g ≡ true →
  cost (⟨ optimize-compose f (⟨ h₁ , h₂ ⟩ m') , optimize-compose g (⟨ h₁ , h₂ ⟩ m') ⟩ m)
  ≤ suc (cost f ℕ+ cost g) ℕ+ suc (cost h₁ ℕ+ cost h₂)
-- f = terminal case
safe-distrib-pair-cost terminal g h₁ h₂ m m' _ =
  let ih : cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m')) ≤ cost g ℕ+ suc (cost h₁ ℕ+ cost h₂)
      ih = optimize-compose-cost-≤ g (⟨ h₁ , h₂ ⟩ m')
      eq1 : cost (⟨ optimize-compose terminal (⟨ h₁ , h₂ ⟩ m') , optimize-compose g (⟨ h₁ , h₂ ⟩ m') ⟩ m)
            ≡ suc (0 ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m')))
      eq1 = cong (λ x → suc (x ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m')))) (opt-terminal-cost (⟨ h₁ , h₂ ⟩ m'))
      step1 : suc (0 ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m'))) ≤ suc (cost g ℕ+ suc (cost h₁ ℕ+ cost h₂))
      step1 = s≤s ih
      -- suc (cost g + suc (cost h₁ + cost h₂))
      -- = suc cost g + suc (cost h₁ + cost h₂) (by +-suc which is part of definition)
      -- Need to prove: suc (cost g + suc x) = suc (0 + cost g) + suc x
      -- suc (0 + cost g) + suc x = (1 + cost g) + (1 + x) = 2 + cost g + x
      -- suc (cost g + suc x) = 1 + cost g + 1 + x = 2 + cost g + x
      step2 : suc (cost g ℕ+ suc (cost h₁ ℕ+ cost h₂)) ≡ suc (0 ℕ+ cost g) ℕ+ suc (cost h₁ ℕ+ cost h₂)
      step2 = refl
  in subst (_≤ suc (0 ℕ+ cost g) ℕ+ suc (cost h₁ ℕ+ cost h₂)) (sym eq1) (subst (suc (0 ℕ+ cost (optimize-compose g (⟨ h₁ , h₂ ⟩ m'))) ≤_) step2 step1)
-- g = terminal case (f ≠ terminal)
safe-distrib-pair-cost f@id terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@(_ ∘ _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@(⟨ _ , _ ⟩ _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@(inl _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@(inr _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@(curry _ _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@fst terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@snd terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@apply terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
-- fold domain is F[Fix F] which can be a product if F is a product functor
safe-distrib-pair-cost f@fold terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
safe-distrib-pair-cost f@(Prim _) terminal h₁ h₂ m m' _ = g-terminal-helper-pair f h₁ h₂ m m' (optimize-compose-cost-≤ f (⟨ h₁ , h₂ ⟩ m'))
-- Eta cases: fst + snd or snd + fst
-- Beta reductions: opt fst ⟨ h₁ , h₂ ⟩ = h₁, opt snd ⟨ h₁ , h₂ ⟩ = h₂ (by definition in Optimize.agda)
-- For fst snd: result ⟨ h₁ , h₂ ⟩ has cost suc (cost h₁ + cost h₂)
-- For snd fst: result ⟨ h₂ , h₁ ⟩ has cost suc (cost h₂ + cost h₁)
-- Bound is suc (0 + 0) + suc (cost h₁ + cost h₂) = suc (suc (cost h₁ + cost h₂))
-- These definitionally reduce:
safe-distrib-pair-cost fst snd h₁ h₂ m m' _ = n≤1+n (suc (cost h₁ ℕ+ cost h₂))
safe-distrib-pair-cost {_} {_} {D} {H₁} {H₂} snd fst h₁ h₂ m m' _ =
  let -- cost (⟨ opt snd ⟨ h₁ , h₂ ⟩ , opt fst ⟨ h₁ , h₂ ⟩ ⟩ m) = cost (⟨ h₂ , h₁ ⟩ m) = suc (cost h₂ + cost h₁)
      -- This definitionally equals suc (cost h₂ + cost h₁), so:
      step1 : suc (cost h₂ ℕ+ cost h₁) ≤ suc (suc (cost h₂ ℕ+ cost h₁))
      step1 = n≤1+n (suc (cost h₂ ℕ+ cost h₁))
      -- suc (suc (cost h₂ + cost h₁)) = suc (suc (cost h₁ + cost h₂)) by +-comm
      step2 : suc (suc (cost h₂ ℕ+ cost h₁)) ≡ suc (suc (cost h₁ ℕ+ cost h₂))
      step2 = cong (λ x → suc (suc x)) (+-comm (cost h₂) (cost h₁))
  in subst (suc (cost h₂ ℕ+ cost h₁) ≤_) step2 step1
-- Remaining: neither f nor g is terminal, and not eta case
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
-- fold/unfold have non-product domains so are type-impossible here
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
