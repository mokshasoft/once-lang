------------------------------------------------------------------------
-- Once.TypeCheck.Error
--
-- Type error representation for the verified type checker.
-- Mirrors Once.TypeCheck.TypeError from Haskell.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Error where

open import Data.String using (String)
open import Data.Nat using (ℕ)

open import Once.Type using (Type)
open import Once.TypeCheck.Context using (Quantity)

------------------------------------------------------------------------
-- Type Errors
------------------------------------------------------------------------

-- | Type errors that can occur during type checking
-- Mirrors Once.TypeCheck.TypeError from Haskell
data TypeError : Set where
  -- Variable not in scope
  UnboundVariable : String → TypeError

  -- Type mismatch: expected vs actual
  TypeMismatch : Type → Type → TypeError

  -- Tried to apply something that isn't a function
  NotAFunction : Type → TypeError

  -- Tried to project from something that isn't a product
  NotAProduct : Type → TypeError

  -- Tried to case on something that isn't a sum
  NotASum : Type → TypeError

  -- Occurs check failed (infinite type)
  OccursCheck : String → Type → TypeError

  -- General unification failure
  UnificationError : Type → Type → TypeError

  -- Wrong number of arguments
  ArityMismatch : String → ℕ → ℕ → TypeError

  -- Type signature doesn't match inferred type (structural)
  SignatureMismatch : Type → Type → TypeError

  -- Linear variable used more than once
  LinearUsedMultiple : String → ℕ → TypeError

  -- Linear variable not used
  LinearUnused : String → TypeError

  -- Erased (zero) variable used at runtime
  ErasedUsedAtRuntime : String → TypeError

  -- Quantity mismatch: expected vs actual
  QuantityMismatch : String → Quantity → Quantity → TypeError

  -- Arithmetic operator applied to non-integer
  ArithNonInteger : Type → TypeError

  -- Comparison operator applied to non-integer
  CompareNonInteger : Type → TypeError

------------------------------------------------------------------------
-- Error Messages (for debugging/display)
------------------------------------------------------------------------

-- | Convert error to human-readable string
-- (Useful for debugging, though MAlonzo extraction will use Haskell Show)
errorMessage : TypeError → String
errorMessage (UnboundVariable x) = "Unbound variable: " Data.String.++ x
  where open import Data.String using (_++_)
errorMessage (TypeMismatch _ _) = "Type mismatch"
errorMessage (NotAFunction _) = "Not a function"
errorMessage (NotAProduct _) = "Not a product"
errorMessage (NotASum _) = "Not a sum"
errorMessage (OccursCheck _ _) = "Infinite type (occurs check)"
errorMessage (UnificationError _ _) = "Cannot unify types"
errorMessage (ArityMismatch _ _ _) = "Wrong number of arguments"
errorMessage (SignatureMismatch _ _) = "Signature doesn't match inferred type"
errorMessage (LinearUsedMultiple _ _) = "Linear variable used multiple times"
errorMessage (LinearUnused _) = "Linear variable not used"
errorMessage (ErasedUsedAtRuntime _) = "Erased variable used at runtime"
errorMessage (QuantityMismatch _ _ _) = "Quantity mismatch"
errorMessage (ArithNonInteger _) = "Arithmetic operator requires integer operands"
errorMessage (CompareNonInteger _) = "Comparison operator requires integer operands"

------------------------------------------------------------------------
-- Error Result Type
------------------------------------------------------------------------

-- | Either a type error or a successful result
data Result (A : Set) : Set where
  ok   : A → Result A
  fail : TypeError → Result A

-- | Functor instance for Result
mapResult : ∀ {A B : Set} → (A → B) → Result A → Result B
mapResult f (ok x)   = ok (f x)
mapResult f (fail e) = fail e

-- | Monad bind for Result
bindResult : ∀ {A B : Set} → Result A → (A → Result B) → Result B
bindResult (ok x)   f = f x
bindResult (fail e) f = fail e

-- | Syntax for do-notation style
infixl 1 _>>=_
_>>=_ : ∀ {A B : Set} → Result A → (A → Result B) → Result B
_>>=_ = bindResult

-- | Return for Result monad
return : ∀ {A : Set} → A → Result A
return = ok
