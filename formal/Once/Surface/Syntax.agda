------------------------------------------------------------------------
-- Once.Surface.Syntax
--
-- Surface syntax for Once programs (before elaboration to IR).
-- Includes variables, lambdas, and applications.
------------------------------------------------------------------------

module Once.Surface.Syntax where

open import Once.Type

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

-- | Typing context (de Bruijn indexed with quantities)
--
-- Ctx n represents a context with n variables.
-- Variables are indexed by Fin n (0 to n-1).
-- Each variable has a type and a quantity (usage annotation).
--
data Ctx : ℕ → Set where
  ∅   : Ctx 0
  _,_^_ : ∀ {n} → Ctx n → Type → Quantity → Ctx (ℕ.suc n)

infixl 5 _,_^_

-- | Smart constructor: extend context with unrestricted quantity
_,_ : ∀ {n} → Ctx n → Type → Ctx (ℕ.suc n)
Γ , A = Γ , A ^ Many

infixl 5 _,_

-- | Lookup type at position in context
--
-- lookup ctx i returns the type at position i
--
lookup : ∀ {n} → Ctx n → Fin n → Type
lookup (Γ , A ^ q) Fin.zero    = A
lookup (Γ , _ ^ _) (Fin.suc i) = lookup Γ i

-- | Lookup quantity at position in context
--
-- lookupQuantity ctx i returns the quantity annotation at position i
--
lookupQuantity : ∀ {n} → Ctx n → Fin n → Quantity
lookupQuantity (Γ , A ^ q) Fin.zero    = q
lookupQuantity (Γ , _ ^ _) (Fin.suc i) = lookupQuantity Γ i

------------------------------------------------------------------------
-- Usage Vectors (QTT)
------------------------------------------------------------------------

-- | Usage vector: tracks how many times each variable is used
--
-- A usage vector Ψ of size n assigns a quantity to each variable in context.
-- Ψ[i] represents the usage of variable i.
--
data Usage : ℕ → Set where
  []  : Usage 0
  _∷_ : ∀ {n} → Quantity → Usage n → Usage (ℕ.suc n)

infixr 5 _∷_

-- | Zero usage vector (all variables unused)
zeroUsage : ∀ {n} → Usage n
zeroUsage {0} = []
zeroUsage {ℕ.suc n} = Zero ∷ zeroUsage

-- | Single variable usage (one variable used with quantity q, rest unused)
singleUse : ∀ {n} → Fin n → Quantity → Usage n
singleUse {ℕ.suc n} Fin.zero    q = q ∷ zeroUsage
singleUse {ℕ.suc n} (Fin.suc i) q = Zero ∷ singleUse i q

-- | Add two usage vectors (combine usage from different branches)
_+ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[] +ᵘ [] = []
(q₁ ∷ ψ₁) +ᵘ (q₂ ∷ ψ₂) = (q₁ +q q₂) ∷ (ψ₁ +ᵘ ψ₂)

infixl 60 _+ᵘ_

-- | Scale usage vector by quantity (usage in a context scaled by q)
_*ᵘ_ : ∀ {n} → Quantity → Usage n → Usage n
q *ᵘ [] = []
q *ᵘ (q' ∷ ψ) = (q *q q') ∷ (q *ᵘ ψ)

infixl 70 _*ᵘ_

-- | Check if usage respects declared quantities
-- ψ ≤ᵘ Γ means all actual usages are within declared bounds
_≤ᵘ_ : ∀ {n} → Usage n → Ctx n → Set
[] ≤ᵘ ∅ = ⊤
  where
    open import Data.Unit using (⊤)
(q ∷ ψ) ≤ᵘ (Γ , A ^ q') = (q ≤q q' ≡ true) × (ψ ≤ᵘ Γ)
  where
    open import Data.Bool using (true)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Data.Product using (_×_)

-- | Surface expressions (well-typed by construction)
--
-- Expr Γ A represents a well-typed expression of type A in context Γ.
-- Uses de Bruijn indices for variables.
--
data Expr : ∀ {n} → Ctx n → Type → Set where
  -- Variable reference (de Bruijn index)
  var   : ∀ {n} {Γ : Ctx n} (i : Fin n) → Expr Γ (lookup Γ i)

  -- Lambda abstraction: λx.e becomes lam e where x is index 0
  lam   : ∀ {n} {Γ : Ctx n} {A B} → Expr (Γ , A) B → Expr Γ (A ⇒ B)

  -- Application
  app   : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ (A ⇒ B) → Expr Γ A → Expr Γ B

  -- Pair introduction
  pair  : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ A → Expr Γ B → Expr Γ (A * B)

  -- Pair elimination
  fst'  : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ (A * B) → Expr Γ A
  snd'  : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ (A * B) → Expr Γ B

  -- Sum introduction
  inl'  : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ A → Expr Γ (A + B)
  inr'  : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ B → Expr Γ (A + B)

  -- Sum elimination (case)
  case' : ∀ {n} {Γ : Ctx n} {A B C}
        → Expr Γ (A + B) → Expr (Γ , A) C → Expr (Γ , B) C → Expr Γ C

  -- Unit introduction
  unit  : ∀ {n} {Γ : Ctx n} → Expr Γ Unit

  -- Void elimination (absurd)
  absurd : ∀ {n} {Γ : Ctx n} {A} → Expr Γ Void → Expr Γ A

  -- Let binding: let x = e1 in e2
  -- e1 computes a value of type A, e2 uses it (at de Bruijn index 0)
  let'  : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ A → Expr (Γ , A) B → Expr Γ B
