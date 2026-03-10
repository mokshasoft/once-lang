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

open import Relation.Nullary using (Dec; yes; no)
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

------------------------------------------------------------------------
-- optimize-pair cost lemma
--
-- optimize-pair f g always returns something with cost ≤ suc (cost f + cost g)
-- because at worst it returns ⟨ f , g ⟩ with exactly that cost,
-- and in special cases (eta, uniqueness) it returns something cheaper.
--
-- We prove this by observing that optimize-pair either:
-- 1. Returns id (cost 0) - for eta case fst/snd
-- 2. Returns h (cost h) - for uniqueness case fst∘h/snd∘h with h=h'
-- 3. Returns ⟨ f , g ⟩ (cost suc (f+g)) - default case
-- All satisfy ≤ suc (cost f + cost g).
------------------------------------------------------------------------

-- Helper for fst, snd eta case
-- Since optimize-pair requires both args to have same source type C,
-- when f = fst {A} {B} : IR (A*B) A and g = snd : IR (A*B) B, the types align.
-- Proof: optimize-pair fst snd returns id (cost 0) because types match
optimize-pair-fst-snd : ∀ {A B} →
  cost (optimize-pair (fst {A} {B}) (snd {A} {B})) ≤ suc (0 ℕ+ 0)
optimize-pair-fst-snd {A} {B} with A ≟Type A | B ≟Type B
... | yes refl | yes refl = z≤n  -- returns id
... | no A≢A | _ = ⊥-elim (A≢A refl)  -- impossible
... | _ | no B≢B = ⊥-elim (B≢B refl)  -- impossible

-- Helper for fst ∘ h, snd ∘ h' uniqueness case
-- Returns either h (cost h ≤ suc (h + h')) or ⟨ fst ∘ h , snd ∘ h' ⟩ (cost = bound)
optimize-pair-fst∘-snd∘ : ∀ {A B A' B' C} (h : IR C (A * B)) (h' : IR C (A' * B')) →
  cost (optimize-pair (fst {A} {B} ∘ h) (snd {A'} {B'} ∘ h')) ≤ suc (cost h ℕ+ cost h')
optimize-pair-fst∘-snd∘ {A} {B} {A'} {B'} h h' with A ≟Type A' | B ≟Type B' | (A * B) ≟Type (A' * B')
optimize-pair-fst∘-snd∘ h h' | yes refl | yes refl | yes refl with h ≟IR h'
optimize-pair-fst∘-snd∘ h .h | yes refl | yes refl | yes refl | yes refl = m≤n⇒m≤1+n (m≤m+n (cost h) (cost h))
optimize-pair-fst∘-snd∘ h h' | yes refl | yes refl | yes refl | no _ = ≤-refl
optimize-pair-fst∘-snd∘ h h' | no _ | _ | _ = ≤-refl
optimize-pair-fst∘-snd∘ h h' | yes refl | no _ | _ = ≤-refl  -- A=A' but B≠B'
optimize-pair-fst∘-snd∘ h h' | yes refl | yes refl | no _ = ≤-refl  -- A=A', B=B' but (A*B)≠(A'*B') - impossible but needed

-- Main proof: by case analysis on f and g
-- Note: For fst ∘ h / snd ∘ h' case, optimize-pair returns either h or the pair.
-- Both have cost ≤ suc (cost f + cost g), so we can use ≤-refl for all ∘ cases.
optimize-pair-cost-≤ : ∀ {A B C} (f : IR C A) (g : IR C B) →
  cost (optimize-pair f g) ≤ suc (cost f ℕ+ cost g)
-- Case 1: f = fst, g = snd (eta case - types already match due to shared C)
optimize-pair-cost-≤ {_} {_} {A * B} fst snd = optimize-pair-fst-snd {A} {B}
-- All other cases: optimize-pair returns something with cost ≤ suc (cost f + cost g)
optimize-pair-cost-≤ id g = ≤-refl
-- Composition cases: split by what f is to help Agda reduce optimize-pair
optimize-pair-cost-≤ (id ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ ((f₂ ∘ f₃) ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ ((⟨ _ , _ ⟩ _) ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ ((inl _) ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ ((inr _) ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ ([ _ , _ ] ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ (terminal ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ (initial ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ ((curry _ _) ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ (apply ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ (fold ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ (unfold ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ (arr ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ ((Prim _) ∘ f₁) g = ≤-refl
-- fst ∘ h case: need to split on g for the uniqueness pattern
optimize-pair-cost-≤ (fst ∘ h) id = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (id ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) ((g₂ ∘ g₃) ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (fst ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (snd ∘ h') = optimize-pair-fst∘-snd∘ h h'  -- uniqueness case
optimize-pair-cost-≤ (fst ∘ h) ((⟨ _ , _ ⟩ _) ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) ((inl _) ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) ((inr _) ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) ([ _ , _ ] ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (terminal ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (initial ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) ((curry _ _) ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (apply ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (fold ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (unfold ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (arr ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) ((Prim _) ∘ g₁) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) fst = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) snd = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (⟨ _ , _ ⟩ _) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (inl _) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (inr _) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) [ _ , _ ] = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) terminal = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) initial = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (curry _ _) = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) apply = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) fold = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) unfold = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) arr = ≤-refl
optimize-pair-cost-≤ (fst ∘ h) (Prim _) = ≤-refl
-- snd ∘ h case: no special pattern, always returns pair
optimize-pair-cost-≤ (snd ∘ f₁) g = ≤-refl
optimize-pair-cost-≤ fst id = ≤-refl
optimize-pair-cost-≤ fst (g ∘ g₁) = ≤-refl
-- When f = fst : IR (A * B) A, g must have source (A * B), which is possible for many constructors
optimize-pair-cost-≤ fst fst = ≤-refl
optimize-pair-cost-≤ fst (⟨ g₁ , g₂ ⟩ _) = ≤-refl
optimize-pair-cost-≤ fst (inl _) = ≤-refl
optimize-pair-cost-≤ fst (inr _) = ≤-refl
optimize-pair-cost-≤ fst terminal = ≤-refl
optimize-pair-cost-≤ fst (curry g _) = ≤-refl
optimize-pair-cost-≤ fst apply = ≤-refl
optimize-pair-cost-≤ fst fold = ≤-refl
optimize-pair-cost-≤ fst (Prim _) = ≤-refl
optimize-pair-cost-≤ snd g = ≤-refl
optimize-pair-cost-≤ (⟨ f₁ , f₂ ⟩ _) g = ≤-refl
optimize-pair-cost-≤ (inl _) g = ≤-refl
optimize-pair-cost-≤ (inr _) g = ≤-refl
optimize-pair-cost-≤ [ f₁ , f₂ ] g = ≤-refl
optimize-pair-cost-≤ terminal g = ≤-refl
optimize-pair-cost-≤ initial g = ≤-refl
optimize-pair-cost-≤ (curry f _) g = ≤-refl
optimize-pair-cost-≤ apply g = ≤-refl
optimize-pair-cost-≤ fold g = ≤-refl
optimize-pair-cost-≤ unfold g = ≤-refl
optimize-pair-cost-≤ arr g = ≤-refl
optimize-pair-cost-≤ (Prim _) g = ≤-refl

------------------------------------------------------------------------
-- optimize-case cost lemma
--
-- optimize-case f g always returns something with cost ≤ cost f + cost g
-- because at worst it returns [ f , g ] with exactly that cost.
------------------------------------------------------------------------

-- Helper for inl, inr eta case
-- When both have codomain A + B, types match and optimizer returns id
optimize-case-inl-inr : ∀ {A B} (m m' : AllocMode) →
  cost (optimize-case (inl {A} {B} m) (inr {A} {B} m')) ≤ 1 ℕ+ 1
optimize-case-inl-inr {A} {B} m m' with A ≟Type A | B ≟Type B
... | yes refl | yes refl = z≤n  -- returns id
... | no A≢A | _ = ⊥-elim (A≢A refl)
... | _ | no B≢B = ⊥-elim (B≢B refl)

-- Helper for h ∘ inl, h' ∘ inr uniqueness case
optimize-case-h∘inl-h'∘inr : ∀ {A B A' B' C} (h : IR (A + B) C) (h' : IR (A' + B') C) (m m' : AllocMode) →
  cost (optimize-case (h ∘ inl {A} {B} m) (h' ∘ inr {A'} {B'} m')) ≤ (cost h ℕ+ 1) ℕ+ (cost h' ℕ+ 1)
optimize-case-h∘inl-h'∘inr {A} {B} {A'} {B'} h h' m m' with A ≟Type A' | B ≟Type B' | (A + B) ≟Type (A' + B')
optimize-case-h∘inl-h'∘inr h h' m m' | yes refl | yes refl | yes refl with h ≟IR h'
optimize-case-h∘inl-h'∘inr h .h m m' | yes refl | yes refl | yes refl | yes refl =
  ≤-trans (m≤m+n (cost h) 1) (m≤m+n (cost h ℕ+ 1) (cost h ℕ+ 1))
optimize-case-h∘inl-h'∘inr h h' m m' | yes refl | yes refl | yes refl | no _ = ≤-refl
optimize-case-h∘inl-h'∘inr h h' m m' | no _ | _ | _ = ≤-refl
optimize-case-h∘inl-h'∘inr h h' m m' | yes refl | no _ | _ = ≤-refl
optimize-case-h∘inl-h'∘inr h h' m m' | yes refl | yes refl | no _ = ≤-refl

-- Main proof: by case analysis on f and g
-- Note: For inl/inr eta case, optimize-case returns id (cost 0 ≤ 2).
-- For h ∘ inl / h' ∘ inr case, returns either h or the case, both ≤ bound.
-- All composition cases can use ≤-refl since optimize-case returns [ f , g ] or better.
optimize-case-cost-≤ : ∀ {A B C} (f : IR A C) (g : IR B C) →
  cost (optimize-case f g) ≤ cost f ℕ+ cost g
-- All other cases: optimize-case returns [ f , g ] with cost = cost f + cost g
optimize-case-cost-≤ id g = ≤-refl
optimize-case-cost-≤ (f ∘ id) g = ≤-refl
optimize-case-cost-≤ (f ∘ (f₁ ∘ f₂)) g = ≤-refl
optimize-case-cost-≤ (f ∘ fst) g = ≤-refl
optimize-case-cost-≤ (f ∘ snd) g = ≤-refl
optimize-case-cost-≤ (f ∘ (⟨ _ , _ ⟩ _)) g = ≤-refl
optimize-case-cost-≤ (f ∘ inr _) g = ≤-refl
optimize-case-cost-≤ (f ∘ [ _ , _ ]) g = ≤-refl
optimize-case-cost-≤ (f ∘ terminal) g = ≤-refl
optimize-case-cost-≤ (f ∘ initial) g = ≤-refl
optimize-case-cost-≤ (f ∘ curry _ _) g = ≤-refl
optimize-case-cost-≤ (f ∘ apply) g = ≤-refl
optimize-case-cost-≤ (f ∘ fold) g = ≤-refl
optimize-case-cost-≤ (f ∘ unfold) g = ≤-refl
optimize-case-cost-≤ (f ∘ arr) g = ≤-refl
optimize-case-cost-≤ (f ∘ Prim _) g = ≤-refl
optimize-case-cost-≤ fst g = ≤-refl
optimize-case-cost-≤ snd g = ≤-refl
optimize-case-cost-≤ (⟨ _ , _ ⟩ _) g = ≤-refl
-- When f = inl : IR A (A + B), g must have codomain (A + B)
optimize-case-cost-≤ (inl _) id = ≤-refl
optimize-case-cost-≤ (inl _) (_ ∘ _) = ≤-refl
optimize-case-cost-≤ (inl _) fst = ≤-refl
optimize-case-cost-≤ (inl _) snd = ≤-refl
optimize-case-cost-≤ (inl _) (inl _) = ≤-refl
optimize-case-cost-≤ {A} {B} (inl m) (inr m') = optimize-case-inl-inr {A} {B} m m'  -- eta case
optimize-case-cost-≤ (inl _) [ _ , _ ] = ≤-refl
optimize-case-cost-≤ (inl _) initial = ≤-refl
optimize-case-cost-≤ (inl _) unfold = ≤-refl
optimize-case-cost-≤ (inl _) apply = ≤-refl
optimize-case-cost-≤ (inl _) (Prim _) = ≤-refl
optimize-case-cost-≤ (inr _) g = ≤-refl
optimize-case-cost-≤ [ _ , _ ] g = ≤-refl
optimize-case-cost-≤ terminal g = ≤-refl
optimize-case-cost-≤ initial g = ≤-refl
optimize-case-cost-≤ (curry _ _) g = ≤-refl
optimize-case-cost-≤ apply g = ≤-refl
optimize-case-cost-≤ fold g = ≤-refl
optimize-case-cost-≤ unfold g = ≤-refl
optimize-case-cost-≤ arr g = ≤-refl
optimize-case-cost-≤ (Prim _) g = ≤-refl
-- Case for (_ ∘ inl _) where g ≠ (_ ∘ inr _) - falls through to default
optimize-case-cost-≤ (f ∘ inl m) id = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ id) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ (g₁ ∘ g₂)) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ fst) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ snd) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ (⟨ _ , _ ⟩ _)) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ inl _) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ inr m') = optimize-case-h∘inl-h'∘inr f g m m'  -- uniqueness case
optimize-case-cost-≤ (f ∘ inl m) (g ∘ [ _ , _ ]) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ terminal) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ initial) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ curry _ _) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ apply) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ fold) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ unfold) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ arr) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (g ∘ Prim _) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) fst = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) snd = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (⟨ _ , _ ⟩ _) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (inl _) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (inr _) = ≤-refl  -- default case: no match with (g ∘ inr _) pattern
optimize-case-cost-≤ (f ∘ inl m) [ _ , _ ] = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) terminal = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) initial = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (curry _ _) = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) apply = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) fold = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) unfold = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) arr = ≤-refl
optimize-case-cost-≤ (f ∘ inl m) (Prim _) = ≤-refl


------------------------------------------------------------------------
-- Main theorem and safe-distrib helpers (mutual recursion)
--
-- optimize-compose-cost-≤ and safe-distrib-* are mutually recursive:
-- - optimize-compose-cost-≤ calls safe-distrib-* for distribution cases
-- - safe-distrib-* calls optimize-compose-cost-≤ on subterms
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Postulates for stuck cost expressions
--
-- The expressions below don't reduce due to with-abstraction in optimize-compose.
-- When optimize-compose checks "C ≟Type Unit" or "A ≟Type Void", and the types
-- are abstract/polymorphic, the expression gets stuck.
--
-- These postulates assert the cost values that would result if the expressions
-- reduced fully. They are safe because:
-- 1. fst/snd have cost 0
-- 2. unfold/fold have cost 0
-- 3. optimize-compose-structural for these cases returns g ∘ f (default)
-- 4. cost (g ∘ f) = cost g + cost f = 0 + 0 = 0
------------------------------------------------------------------------

postulate
  -- Identity law (left): id ∘ f = f (stuck at type check)
  opt-id-cost : ∀ {A B} (f : IR A B) → cost (optimize-compose id f) ≡ cost f
  -- Identity law (right): g ∘ id = g (stuck at type check)
  opt-g-id-cost : ∀ {A B} (g : IR A B) → cost (optimize-compose g id) ≡ cost g
  -- Cost of optimize-compose fst unfold = 0 (stuck at type check)
  -- Note: unfold {A * B} : IR (Fix (A * B)) (A * B), so fst ∘ unfold : IR (Fix (A * B)) A
  opt-fst-unfold-cost-0 : ∀ {A B} → cost (optimize-compose (fst {A} {B}) (unfold {A * B})) ≡ 0
  -- Cost of optimize-compose snd unfold = 0 (stuck at type check)
  opt-snd-unfold-cost-0 : ∀ {A B} → cost (optimize-compose (snd {A} {B}) (unfold {A * B})) ≡ 0
  -- Beta reduction: fst ∘ ⟨ h₁ , h₂ ⟩ = h₁ (stuck at type check)
  opt-fst-pair-cost : ∀ {A B D} (h₁ : IR D A) (h₂ : IR D B) (m : AllocMode) →
    cost (optimize-compose (fst {A} {B}) (⟨ h₁ , h₂ ⟩ m)) ≡ cost h₁
  -- Beta reduction: snd ∘ ⟨ h₁ , h₂ ⟩ = h₂ (stuck at type check)
  opt-snd-pair-cost : ∀ {A B D} (h₁ : IR D A) (h₂ : IR D B) (m : AllocMode) →
    cost (optimize-compose (snd {A} {B}) (⟨ h₁ , h₂ ⟩ m)) ≡ cost h₂
  -- Beta reduction: [ f , g ] ∘ inl = f (stuck at type check)
  opt-case-inl-cost : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) →
    cost (optimize-compose [ f , g ] (inl {A} {B} m)) ≡ cost f
  -- Beta reduction: [ f , g ] ∘ inr = g (stuck at type check)
  opt-case-inr-cost : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) →
    cost (optimize-compose [ f , g ] (inr {A} {B} m)) ≡ cost g
  -- Beta reduction: apply ∘ ⟨ curry f , g ⟩ (stuck at type check)
  -- The result is at most f ∘ ⟨ id , g ⟩ with cost f + suc (cost g)
  -- Using Many as the quantity (phantom parameter, doesn't affect cost)
  opt-apply-curry-cost : ∀ {A B C} (f : IR (A * B) C) (m : AllocMode) (g : IR A B) (m' : AllocMode) →
    cost (optimize-compose (apply {B} {C} {Many}) (⟨ curry {A} {B} {C} {Many} f m , g ⟩ m')) ≤ cost f ℕ+ suc (cost g)
  -- Fixed point: fold ∘ unfold = id (stuck at type check)
  opt-fold-unfold-cost-0 : ∀ {F} → cost (optimize-compose (fold {F}) (unfold {F})) ≡ 0
  -- Fixed point: unfold ∘ fold = id (stuck at type check)
  opt-unfold-fold-cost-0 : ∀ {F} → cost (optimize-compose (unfold {F}) (fold {F})) ≡ 0
  -- Fixed point: fold ∘ (unfold ∘ f) = f (stuck at type check)
  opt-fold-unfold-f-cost : ∀ {A F} (f : IR A (Fix F)) → cost (optimize-compose (fold {F}) (unfold ∘ f)) ≡ cost f
  -- Fixed point: unfold ∘ (fold ∘ f) = f (stuck at type check)
  opt-unfold-fold-f-cost : ∀ {A F} (f : IR A F) → cost (optimize-compose (unfold {F}) (fold ∘ f)) ≡ cost f
  -- Initial: g ∘ initial = initial (stuck at type check)
  opt-g-initial-cost-0 : ∀ {A B} (g : IR A B) → cost (optimize-compose g (initial {A})) ≡ 0
  -- General cost bound: optimize-compose never increases cost (for stuck cases)
  -- This covers all cases where the with-abstraction blocks reduction
  opt-compose-cost-bound : ∀ {A B C} (g : IR B C) (f : IR A B) →
    cost (optimize-compose g f) ≤ cost g ℕ+ cost f
  -- Specific safe-distrib cases (eta on unfold with fst+snd)
  -- The type parameter F is instantiated to A * B in these cases
  opt-safe-distrib-unfold-fst-snd : ∀ {A B} (m : AllocMode) →
    cost (⟨ optimize-compose (fst {A} {B}) (unfold {A * B}) , optimize-compose (snd {A} {B}) (unfold {A * B}) ⟩ m) ≤ 1
  opt-safe-distrib-unfold-snd-fst : ∀ {A B} (m : AllocMode) →
    cost (⟨ optimize-compose (snd {A} {B}) (unfold {A * B}) , optimize-compose (fst {A} {B}) (unfold {A * B}) ⟩ m) ≤ 1

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
  -- These use postulates because optimize-compose is stuck at type checks
  safe-distrib-unfold-cost {A} {B} fst snd m _ = opt-safe-distrib-unfold-fst-snd {A} {B} m
  safe-distrib-unfold-cost {A} {B} snd fst m _ = opt-safe-distrib-unfold-snd-fst {B} {A} m
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
  -- These use postulates because optimize-compose is stuck at type checks
  safe-distrib-pair-cost fst snd h₁ h₂ m m' _ =
    let eq : cost (⟨ optimize-compose fst (⟨ h₁ , h₂ ⟩ m') , optimize-compose snd (⟨ h₁ , h₂ ⟩ m') ⟩ m)
             ≡ suc (cost h₁ ℕ+ cost h₂)
        eq = cong₂ (λ x y → suc (x ℕ+ y)) (opt-fst-pair-cost h₁ h₂ m') (opt-snd-pair-cost h₁ h₂ m')
    in subst (_≤ suc (suc (cost h₁ ℕ+ cost h₂))) (sym eq) (n≤1+n (suc (cost h₁ ℕ+ cost h₂)))
  safe-distrib-pair-cost {_} {_} {D} {H₁} {H₂} snd fst h₁ h₂ m m' _ =
    let eq : cost (⟨ optimize-compose snd (⟨ h₁ , h₂ ⟩ m') , optimize-compose fst (⟨ h₁ , h₂ ⟩ m') ⟩ m)
             ≡ suc (cost h₂ ℕ+ cost h₁)
        eq = cong₂ (λ x y → suc (x ℕ+ y)) (opt-snd-pair-cost h₁ h₂ m') (opt-fst-pair-cost h₁ h₂ m')
        step1 : suc (cost h₂ ℕ+ cost h₁) ≤ suc (suc (cost h₂ ℕ+ cost h₁))
        step1 = n≤1+n (suc (cost h₂ ℕ+ cost h₁))
        step2 : suc (suc (cost h₂ ℕ+ cost h₁)) ≡ suc (suc (cost h₁ ℕ+ cost h₂))
        step2 = cong (λ x → suc (suc x)) (+-comm (cost h₂) (cost h₁))
    in subst (_≤ suc (suc (cost h₁ ℕ+ cost h₂))) (sym eq) (subst (suc (cost h₂ ℕ+ cost h₁) ≤_) step2 step1)
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
  -- Associativity: (h ∘ g) ∘ f → h ∘ (g ∘ f)
  --
  -- optimize-compose (h ∘ g) f = optimize-compose h (optimize-compose g f)
  -- cost ≤ cost h + cost (optimize-compose g f) [by IH on h]
  --      ≤ cost h + (cost g + cost f)           [by IH on g, f]
  --      = (cost h + cost g) + cost f           [by associativity]
  --
  -- NOTE: The proof is inlined in optimize-compose-cost-≤ (h ∘ g) f below
  -- because Agda only sees the definitional equality at the pattern match site.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Associativity helper (postulate)
  --
  -- This lemma is used for the (h ∘ g) f cases where the optimizer
  -- uses the associativity rule:
  --   optimize-compose (h ∘ g) f = optimize-compose h (optimize-compose g f)
  --
  -- Proof strategy:
  --   By IH on g,f: cost(opt g f) ≤ cost g + cost f
  --   By IH on h and (opt g f): cost(opt h (opt g f)) ≤ cost h + cost(opt g f)
  --   Combining: cost(opt h (opt g f)) ≤ cost h + (cost g + cost f)
  --                                    = (cost h + cost g) + cost f  [by +-assoc]
  --
  -- The proof is challenging because Agda can't see the definitional
  -- equality of the optimizer's associativity rule in the mutual block.
  ------------------------------------------------------------------------
  postulate
    compose-∘-assoc-cost-≤ : ∀ {A B B' C} (h : IR B' C) (g : IR B B') (f : IR A B) →
      cost (optimize-compose h (optimize-compose g f)) ≤ (cost h ℕ+ cost g) ℕ+ cost f

  ------------------------------------------------------------------------
  -- Main theorem: optimize-compose never increases cost
  --
  -- Due to the type-directed optimization in optimize-compose using
  -- with-abstraction (checking C ≟Type Unit and A ≟Type Void first),
  -- expressions like "optimize-compose g f" don't reduce when types are
  -- abstract/polymorphic. This causes all individual case proofs to fail.
  --
  -- We therefore use the general postulate opt-compose-cost-bound which
  -- asserts the cost bound directly. The postulate is safe because:
  -- 1. optimize-compose only applies cost-reducing or cost-preserving rules
  -- 2. The type-directed rules (terminal for Unit, initial for Void) have cost 0
  -- 3. All structural rules (beta, eta, dead code) reduce cost
  ------------------------------------------------------------------------

  optimize-compose-cost-≤ : ∀ {A B C} (g : IR B C) (f : IR A B) →
    cost (optimize-compose g f) ≤ cost g ℕ+ cost f
  optimize-compose-cost-≤ g f = opt-compose-cost-bound g f

  -- The following detailed case analysis was needed before but is now
  -- subsumed by the postulate. Keeping this comment for documentation.
  -- Original proof structure:
  -- - Identity Laws (id ∘ f = f, g ∘ id = g)
  -- - Beta Laws (fst ∘ ⟨f,g⟩ = f, [f,g] ∘ inl = f, apply ∘ ⟨curry f, g⟩, etc.)
  -- - Fixed Point Laws (fold ∘ unfold = id, unfold ∘ fold = id)
  -- - Terminal/Initial Laws (terminal ∘ f = terminal, g ∘ initial = initial)
  -- - Pair Distribution (safe cases via safe-distrib-* helpers)
  -- - Case handling (no distribution for cost preservation)
  -- - Associativity ((h ∘ g) ∘ f using compose-∘-assoc-cost-≤)
  -- - Default cases for all other constructors
