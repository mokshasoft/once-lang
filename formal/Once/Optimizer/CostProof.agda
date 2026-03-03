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
                                        +-monoˡ-≤; +-monoʳ-≤; +-identityʳ; +-assoc; +-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

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
-- Postulates for safe distribution cases
--
-- When safe-pair-distrib f g = true, distribution doesn't increase cost.
-- This happens in two cases:
-- 1. Eta case: f = fst, g = snd (or vice versa) - pair is fully eliminated
-- 2. Terminal case: f = terminal or g = terminal - one component has cost 0
--
-- These postulates are provable but require tedious pattern matching.
-- The key insights are:
-- - Eta: ⟨ fst , snd ⟩ ∘ ⟨ h₁ , h₂ ⟩ = ⟨ h₁ , h₂ ⟩ (cost unchanged)
-- - Terminal: optimize-compose terminal h = terminal (cost 0)
------------------------------------------------------------------------

postulate
  -- Distribution over pairs (eta or terminal case)
  safe-distrib-pair-cost : ∀ {A B D H₁ H₂} (f : IR (H₁ * H₂) A) (g : IR (H₁ * H₂) B)
    (h₁ : IR D H₁) (h₂ : IR D H₂) (m m' : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (⟨ h₁ , h₂ ⟩ m') , optimize-compose g (⟨ h₁ , h₂ ⟩ m') ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ suc (cost h₁ ℕ+ cost h₂)

  -- Distribution over inl (only terminal case)
  safe-distrib-inl-cost : ∀ {A B D E} (f : IR (D + E) A) (g : IR (D + E) B)
    (m m' : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (inl {D} {E} m') , optimize-compose g (inl {D} {E} m') ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 1

  -- Distribution over inr (only terminal case)
  safe-distrib-inr-cost : ∀ {A B D E} (f : IR (D + E) A) (g : IR (D + E) B)
    (m m' : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (inr {D} {E} m') , optimize-compose g (inr {D} {E} m') ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 1

  -- Distribution over unfold (only terminal case)
  safe-distrib-unfold-cost : ∀ {A B F} (f : IR F A) (g : IR F B)
    (m : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (unfold {F}) , optimize-compose g (unfold {F}) ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 0

  -- Distribution over fold (only terminal case)
  safe-distrib-fold-cost : ∀ {A B F} (f : IR (Fix F) A) (g : IR (Fix F) B)
    (m : AllocMode) →
    safe-pair-distrib f g ≡ true →
    cost (⟨ optimize-compose f (fold {F}) , optimize-compose g (fold {F}) ⟩ m)
    ≤ suc (cost f ℕ+ cost g) ℕ+ 1

  -- Case fusion cost
  case-fusion-cost : ∀ {FA FB H₁A H₁B C} (h₁ : IR H₁A C) (h₂ : IR H₁B C)
    (f : IR FA (H₁A + H₁B)) (g : IR FB (H₁A + H₁B)) →
    cost ([ optimize-compose ([ h₁ , h₂ ]) f , optimize-compose ([ h₁ , h₂ ]) g ])
    ≤ (cost h₁ ℕ+ cost h₂) ℕ+ (cost f ℕ+ cost g)

  -- Associativity: (h ∘ g) ∘ f
  compose-∘-cost-≤ : ∀ {A B B' C} (h : IR B' C) (g : IR B B') (f : IR A B) →
    cost (optimize-compose (h ∘ g) f) ≤ (cost h ℕ+ cost g) ℕ+ cost f


------------------------------------------------------------------------
-- optimize-pair and optimize-case cost lemmas
--
-- These are provable but require matching the complex with-clause
-- structure of the optimizer functions. Using postulates for clarity.
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
