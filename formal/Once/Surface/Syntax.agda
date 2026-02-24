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
open import Data.Bool using (Bool; true; _∧_)
open import Data.Integer using (ℤ)
open import Data.String using (String)

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

-- | Boolean version of subusaging check (for validation)
-- Returns true if all usages respect declared quantities
_≤ᵘ?_ : ∀ {n} → Usage n → Ctx n → Bool
[] ≤ᵘ? ∅ = true
(q ∷ ψ) ≤ᵘ? (Γ , A ^ q') = (q ≤q q') ∧ (ψ ≤ᵘ? Γ)

-- | Lookup quantity at specific index in usage vector
lookupUsage : ∀ {n} → Usage n → Fin n → Quantity
lookupUsage (q ∷ ψ) Fin.zero    = q
lookupUsage (q ∷ ψ) (Fin.suc i) = lookupUsage ψ i

-- | Drop first element from usage vector (for removing bound variable)
tailUsage : ∀ {n} → Usage (ℕ.suc n) → Usage n
tailUsage (q ∷ ψ) = ψ

-- | Surface expressions (well-typed by construction)
--
-- Expr Γ A represents a well-typed expression of type A in context Γ.
-- Uses de Bruijn indices for variables.
--
data Expr : ∀ {n} → Ctx n → Type → Set where
  -- Variable reference (de Bruijn index)
  var   : ∀ {n} {Γ : Ctx n} (i : Fin n) → Expr Γ (lookup Γ i)

  -- Lambda abstraction with quantity annotation
  -- lam q e represents λ^q x. e where q is the usage quantity for x
  lam   : ∀ {n} {Γ : Ctx n} {A B} (q : Quantity) → Expr (Γ , A) B → Expr Γ (A ⇒[ q ] B)

  -- Application (pure function)
  app   : ∀ {n} {Γ : Ctx n} {A B} {q : Quantity} → Expr Γ (A ⇒[ q ] B) → Expr Γ A → Expr Γ B

  -- Effect application (effectful morphism)
  effApp : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ (Eff A B) → Expr Γ A → Expr Γ B

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

  -- Integer literal
  int   : ∀ {n} {Γ : Ctx n} → ℤ → Expr Γ Int

  -- String literal
  str   : ∀ {n} {Γ : Ctx n} → String → Expr Γ Str

  -- Arithmetic operations (Int → Int → Int)
  add   : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ Int
  sub   : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ Int
  mul   : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ Int
  div   : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ Int
  mod'  : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ Int

  -- Unary negation (Int → Int)
  neg   : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int

  -- Comparison operations (Int → Int → Bool, where Bool = Unit + Unit)
  lt    : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ (Unit + Unit)
  le    : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ (Unit + Unit)
  gt    : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ (Unit + Unit)
  ge    : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ (Unit + Unit)
  eq    : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ (Unit + Unit)
  ne    : ∀ {n} {Γ : Ctx n} → Expr Γ Int → Expr Γ Int → Expr Γ (Unit + Unit)

  -- Effect lifting (arr combinator from arrow-based effects)
  -- Lifts a pure function to an effectful morphism
  arr'  : ∀ {n} {Γ : Ctx n} {A B} → Expr Γ (A ⇒ B) → Expr Γ (Eff A B)

  -- Fixed point constructors (for recursive types)
  -- roll wraps one layer: F → Fix F
  roll'   : ∀ {n} {Γ : Ctx n} {F} → Expr Γ F → Expr Γ (Fix F)
  -- unroll unwraps one layer: Fix F → F
  unroll' : ∀ {n} {Γ : Ctx n} {F} → Expr Γ (Fix F) → Expr Γ F

  -- Primitive reference (imported functions)
  -- Used for qualified imports like exit0@S → prim "S.exit0"
  -- The type A is determined by the import
  prim    : ∀ {n} {Γ : Ctx n} {A} → String → Expr Γ A
