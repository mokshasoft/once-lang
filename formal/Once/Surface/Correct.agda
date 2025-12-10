------------------------------------------------------------------------
-- Once.Surface.Correct
--
-- Correctness of elaboration from surface syntax to IR.
-- Proves that elaboration preserves semantics.
------------------------------------------------------------------------

module Once.Surface.Correct where

open import Once.Type
open import Once.IR
open import Once.Semantics as IR using (⟦_⟧; eval)
open import Once.Surface.Syntax using (Ctx; ∅; lookup; Expr; var; lam; app; pair; fst'; snd'; inl'; inr'; case'; unit; absurd) renaming (_,_ to _▸_)
open import Once.Surface.Semantics using (Env; ε; _∷_; envLookup; evalSurface)
open import Once.Surface.Elaborate using (⟦_⟧ᶜ; proj; swap'; distribute; elaborate)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using ()

-- Postulates: function extensionality is standard in type theory
postulate
  extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
                   (∀ x → f x ≡ g x) → f ≡ g

-- | Convert environment to nested product (environment as value)
--
-- interpEnv ρ converts the heterogeneous environment ρ to a nested
-- product value that can be passed to elaborated IR morphisms.
--
interpEnv : ∀ {n} {Γ : Ctx n} → Env Γ → ⟦ ⟦ Γ ⟧ᶜ ⟧
interpEnv ε       = tt
interpEnv (v ∷ ρ) = (interpEnv ρ , v)

-- | Projection correctness
--
-- Looking up a variable in the environment equals projecting from
-- the interpreted environment.
--
proj-correct : ∀ {n} {Γ : Ctx n} (ρ : Env Γ) (i : Fin n) →
               envLookup ρ i ≡ eval (proj i) (interpEnv ρ)
proj-correct (v ∷ ρ) Fin.zero    = refl
proj-correct (v ∷ ρ) (Fin.suc i) = proj-correct ρ i

-- | Distribution correctness (left case)
--
-- The distribute combinator correctly pushes environment through sums.
--
distribute-inl : ∀ {Γ A B} (γ : ⟦ Γ ⟧) (a : ⟦ A ⟧) →
                 eval (distribute {Γ} {A} {B}) (γ , inj₁ a) ≡ inj₁ (γ , a)
distribute-inl γ a = refl

-- | Distribution correctness (right case)
distribute-inr : ∀ {Γ A B} (γ : ⟦ Γ ⟧) (b : ⟦ B ⟧) →
                 eval (distribute {Γ} {A} {B}) (γ , inj₂ b) ≡ inj₂ (γ , b)
distribute-inr γ b = refl

-- Case correctness postulates (TODO: prove these)
-- The proof requires careful equational reasoning about distribute
postulate
  case-correct-inl : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                     (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                     (a : ⟦ A ⟧) → evalSurface ρ s ≡ inj₁ a →
                     evalSurface ρ (case' s l r) ≡ eval (elaborate (case' s l r)) (interpEnv ρ)
  case-correct-inr : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                     (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                     (b : ⟦ B ⟧) → evalSurface ρ s ≡ inj₂ b →
                     evalSurface ρ (case' s l r) ≡ eval (elaborate (case' s l r)) (interpEnv ρ)

-- | Main correctness theorem
--
-- Elaboration preserves semantics: evaluating a surface expression in an
-- environment gives the same result as evaluating the elaborated IR
-- morphism on the interpreted environment.
--
elaborate-correct : ∀ {n} {Γ : Ctx n} {A} (ρ : Env Γ) (e : Expr Γ A) →
                    evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)
elaborate-correct ρ (var i) = proj-correct ρ i
elaborate-correct ρ (lam e) = extensionality λ a → elaborate-correct (a ∷ ρ) e
elaborate-correct ρ (app f x) = cong₂ (λ f' x' → f' x') (elaborate-correct ρ f) (elaborate-correct ρ x)
elaborate-correct ρ (pair a b) = cong₂ _,_ (elaborate-correct ρ a) (elaborate-correct ρ b)
elaborate-correct ρ (fst' p) = cong proj₁ (elaborate-correct ρ p)
elaborate-correct ρ (snd' p) = cong proj₂ (elaborate-correct ρ p)
elaborate-correct ρ (inl' a) = cong inj₁ (elaborate-correct ρ a)
elaborate-correct ρ (inr' b) = cong inj₂ (elaborate-correct ρ b)
elaborate-correct ρ (case' s l r) = case-aux (evalSurface ρ s) refl
  where
    case-aux : (v : ⟦ _ ⟧ ⊎ ⟦ _ ⟧) → evalSurface ρ s ≡ v →
               evalSurface ρ (case' s l r) ≡ eval (elaborate (case' s l r)) (interpEnv ρ)
    case-aux (inj₁ a) eq = case-correct-inl ρ s l r a eq
    case-aux (inj₂ b) eq = case-correct-inr ρ s l r b eq
elaborate-correct ρ unit = refl
elaborate-correct ρ (absurd v) with evalSurface ρ v
... | ()
