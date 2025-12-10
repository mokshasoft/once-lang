------------------------------------------------------------------------
-- Once.Surface.Semantics
--
-- Denotational semantics for surface expressions.
-- Interprets expressions in an environment.
------------------------------------------------------------------------

module Once.Surface.Semantics where

open import Once.Type
open import Once.Semantics using (⟦_⟧)
open import Once.Surface.Syntax using (Ctx; ∅; lookup; Expr; var; lam; app; pair; fst'; snd'; inl'; inr'; case'; unit; absurd) renaming (_,_ to _▸_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- | Environment: maps variables to values
--
-- Env Γ is a heterogeneous vector of values matching context Γ.
--
data Env : ∀ {n} → Ctx n → Set where
  ε   : Env ∅
  _∷_ : ∀ {n} {Γ : Ctx n} {A} → ⟦ A ⟧ → Env Γ → Env (Γ ▸ A)

infixr 5 _∷_

-- | Lookup value at position in environment
--
envLookup : ∀ {n} {Γ : Ctx n} → Env Γ → (i : Fin n) → ⟦ lookup Γ i ⟧
envLookup (v ∷ ρ) Fin.zero    = v
envLookup (_ ∷ ρ) (Fin.suc i) = envLookup ρ i

-- | Evaluate surface expression in environment
--
-- evalSurface ρ e evaluates expression e in environment ρ.
-- This is the reference semantics that elaboration must preserve.
--
evalSurface : ∀ {n} {Γ : Ctx n} {A} → Env Γ → Expr Γ A → ⟦ A ⟧

evalSurface ρ (var i)        = envLookup ρ i
evalSurface ρ (lam e)        = λ a → evalSurface (a ∷ ρ) e
evalSurface ρ (app f x)      = (evalSurface ρ f) (evalSurface ρ x)
evalSurface ρ (pair a b)     = (evalSurface ρ a , evalSurface ρ b)
evalSurface ρ (fst' p)       = proj₁ (evalSurface ρ p)
evalSurface ρ (snd' p)       = proj₂ (evalSurface ρ p)
evalSurface ρ (inl' a)       = inj₁ (evalSurface ρ a)
evalSurface ρ (inr' b)       = inj₂ (evalSurface ρ b)
evalSurface ρ (case' s l r)  with evalSurface ρ s
... | inj₁ a                 = evalSurface (a ∷ ρ) l
... | inj₂ b                 = evalSurface (b ∷ ρ) r
evalSurface ρ unit           = tt
evalSurface ρ (absurd v)     = ⊥-elim (evalSurface ρ v)
