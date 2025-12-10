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

-- | Typing context (de Bruijn indexed)
--
-- Ctx n represents a context with n variables.
-- Variables are indexed by Fin n (0 to n-1).
--
data Ctx : ℕ → Set where
  ∅   : Ctx 0
  _,_ : ∀ {n} → Ctx n → Type → Ctx (ℕ.suc n)

infixl 5 _,_

-- | Lookup type at position in context
--
-- ∈-lookup ctx i returns the type at position i
--
lookup : ∀ {n} → Ctx n → Fin n → Type
lookup (Γ , A) Fin.zero    = A
lookup (Γ , _) (Fin.suc i) = lookup Γ i

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
