------------------------------------------------------------------------
-- Once.Surface.Semantics
--
-- Denotational semantics for surface expressions.
-- Interprets expressions in an environment.
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.Surface.Semantics (MI : MachineInterface) where

open import Once.Type
open import Once.SemanticBaseMachine MI
open import Once.Surface.Syntax using (Ctx; ∅; lookup; Expr; var; lam; app; pair; fst'; snd'; inl'; inr'; case'; unit; absurd; let'; int; str; add; sub; mul; div; mod'; neg; lt; le; gt; ge; eq; ne) renaming (_,_ to _▸_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer as ℤ using (ℤ; ∣_∣)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false; not)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _*_; _≤ᵇ_; _≟_)
open import Relation.Nullary using (does)

-- TECHNICAL DEBT: Unsafe division/modulus (returns 0 for division by 0)
-- Should be replaced with proper error handling or contracts
postulate
  unsafeDiv : ℕ → ℕ → ℕ
  unsafeMod : ℕ → ℕ → ℕ

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
-- Create explicit Closure for lambda (env-addr is placeholder, code-ptr is compilation artifact)
-- Quantity q is ignored in semantics (type-level only)
evalSurface ρ (lam q e)      = record { env-addr = 0; semantics = λ a → evalSurface (a ∷ ρ) e }
-- Apply closure using semantics field
evalSurface ρ (app f x)      = Closure.semantics (evalSurface ρ f) (evalSurface ρ x)
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
-- Let: evaluate e1, extend environment, evaluate e2
evalSurface ρ (let' e1 e2)   = evalSurface (evalSurface ρ e1 ∷ ρ) e2

-- Integer literal (convert from ℤ to ℕ using absolute value)
-- TECHNICAL DEBT: Loses sign information, need proper signed/unsigned handling
evalSurface ρ (int n)        = ∣ n ∣
-- String literal
evalSurface ρ (str s)        = s

-- Arithmetic operations (using ℕ operations)
evalSurface ρ (add e₁ e₂)    = (evalSurface ρ e₁) ℕ.+ (evalSurface ρ e₂)
evalSurface ρ (sub e₁ e₂)    = (evalSurface ρ e₁) ∸ (evalSurface ρ e₂)
evalSurface ρ (mul e₁ e₂)    = (evalSurface ρ e₁) ℕ.* (evalSurface ρ e₂)
evalSurface ρ (div e₁ e₂)    = unsafeDiv (evalSurface ρ e₁) (evalSurface ρ e₂)
evalSurface ρ (mod' e₁ e₂)   = unsafeMod (evalSurface ρ e₁) (evalSurface ρ e₂)
-- Negation (TECHNICAL DEBT: ℕ has no proper negation, returns 0)
evalSurface ρ (neg e)        = 0

-- Comparison operations (Bool → Unit + Unit)
-- true maps to inj₁ tt, false maps to inj₂ tt
-- x < y  ≡  ¬(y ≤ x)
evalSurface ρ (lt e₁ e₂)     = toSum (not (evalSurface ρ e₂ ≤ᵇ evalSurface ρ e₁))
  where toSum : Bool → ⊤ ⊎ ⊤
        toSum true  = inj₁ tt
        toSum false = inj₂ tt
evalSurface ρ (le e₁ e₂)     = toSum (evalSurface ρ e₁ ≤ᵇ evalSurface ρ e₂)
  where toSum : Bool → ⊤ ⊎ ⊤
        toSum true  = inj₁ tt
        toSum false = inj₂ tt
-- x > y  ≡  ¬(x ≤ y)
evalSurface ρ (gt e₁ e₂)     = toSum (not (evalSurface ρ e₁ ≤ᵇ evalSurface ρ e₂))
  where toSum : Bool → ⊤ ⊎ ⊤
        toSum true  = inj₁ tt
        toSum false = inj₂ tt
-- x ≥ y  ≡  y ≤ x
evalSurface ρ (ge e₁ e₂)     = toSum (evalSurface ρ e₂ ≤ᵇ evalSurface ρ e₁)
  where toSum : Bool → ⊤ ⊎ ⊤
        toSum true  = inj₁ tt
        toSum false = inj₂ tt
-- x ≡ y  uses decidable equality
evalSurface ρ (eq e₁ e₂)     = toSum (does (evalSurface ρ e₁ ≟ evalSurface ρ e₂))
  where toSum : Bool → ⊤ ⊎ ⊤
        toSum true  = inj₁ tt
        toSum false = inj₂ tt
evalSurface ρ (ne e₁ e₂)     = toSum (not (does (evalSurface ρ e₁ ≟ evalSurface ρ e₂)))
  where toSum : Bool → ⊤ ⊎ ⊤
        toSum true  = inj₁ tt
        toSum false = inj₂ tt
