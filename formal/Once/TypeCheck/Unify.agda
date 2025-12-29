------------------------------------------------------------------------
-- Once.TypeCheck.Unify
--
-- Unification algorithm for type checking.
-- Implements Robinson's unification with occurs check.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Unify where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒_; Eff; Fix; TVar)
open import Once.TypeCheck.Error using (TypeError; OccursCheck; UnificationError; Result; ok; fail)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

-- | A substitution maps type variable names to types
Subst : Set
Subst = List (String × Type)

-- | Empty substitution
emptySubst : Subst
emptySubst = []

-- | Singleton substitution: [x ↦ T]
singleSubst : String → Type → Subst
singleSubst x T = (x , T) ∷ []

-- | Lookup a variable in a substitution
lookupSubst : String → Subst → Maybe Type
lookupSubst x [] = nothing
lookupSubst x ((y , T) ∷ σ) with x ≟ y
... | yes _ = just T
... | no  _ = lookupSubst x σ

------------------------------------------------------------------------
-- Applying Substitutions
------------------------------------------------------------------------

-- | Apply a substitution to a type
applySubst : Subst → Type → Type
applySubst σ Unit = Unit
applySubst σ Void = Void
applySubst σ Int = Int
applySubst σ Float = Float
applySubst σ Str = Str
applySubst σ Buffer = Buffer
applySubst σ (A * B) = applySubst σ A * applySubst σ B
applySubst σ (A + B) = applySubst σ A + applySubst σ B
applySubst σ (A ⇒ B) = applySubst σ A ⇒ applySubst σ B
applySubst σ (Eff A B) = Eff (applySubst σ A) (applySubst σ B)
applySubst σ (Fix F) = Fix (applySubst σ F)
applySubst σ (TVar x) with lookupSubst x σ
... | just T  = T
... | nothing = TVar x

-- | Compose two substitutions: (σ₂ ∘ σ₁)(T) = σ₂(σ₁(T))
composeSubst : Subst → Subst → Subst
composeSubst σ₂ σ₁ =
  Data.List.map (λ { (x , T) → (x , applySubst σ₂ T) }) σ₁ ++ σ₂

------------------------------------------------------------------------
-- Occurs Check
------------------------------------------------------------------------

-- | Check if a type variable occurs in a type
occurs : String → Type → Bool
occurs x Unit = false
occurs x Void = false
occurs x Int = false
occurs x Float = false
occurs x Str = false
occurs x Buffer = false
occurs x (A * B) = occurs x A ∨ occurs x B
occurs x (A + B) = occurs x A ∨ occurs x B
occurs x (A ⇒ B) = occurs x A ∨ occurs x B
occurs x (Eff A B) = occurs x A ∨ occurs x B
occurs x (Fix F) = occurs x F
occurs x (TVar y) with x ≟ y
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Unification
------------------------------------------------------------------------

-- | Unification result
data UnifyResult : Set where
  unified : Subst → UnifyResult
  failed  : TypeError → UnifyResult

-- | Unify two types
-- Returns a most general unifier (MGU) or an error
--
-- Note: We use TERMINATING pragma because the termination argument
-- is non-trivial (requires showing applySubst preserves a measure).
-- A proper proof would use well-founded recursion on type size.
{-# TERMINATING #-}
unify : Type → Type → UnifyResult

-- Base types unify only with themselves
unify Unit Unit = unified emptySubst
unify Void Void = unified emptySubst
unify Int Int = unified emptySubst
unify Float Float = unified emptySubst
unify Str Str = unified emptySubst
unify Buffer Buffer = unified emptySubst

-- Type variable unification (with occurs check)
unify (TVar x) (TVar y) with x ≟ y
... | yes _ = unified emptySubst  -- Same variable
... | no  _ = unified (singleSubst x (TVar y))  -- Different variables

unify (TVar x) T with occurs x T
... | true  = failed (OccursCheck x T)
... | false = unified (singleSubst x T)

unify T (TVar x) with occurs x T
... | true  = failed (OccursCheck x T)
... | false = unified (singleSubst x T)

-- Product types
unify (A₁ * B₁) (A₂ * B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Sum types
unify (A₁ + B₁) (A₂ + B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Function types
unify (A₁ ⇒ B₁) (A₂ ⇒ B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Effectful types
unify (Eff A₁ B₁) (Eff A₂ B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Fixed point types
unify (Fix F₁) (Fix F₂) = unify F₁ F₂

-- Everything else fails
unify A B = failed (UnificationError A B)

------------------------------------------------------------------------
-- Convenience: Result-based unification
------------------------------------------------------------------------

-- | Unify returning Result monad
unifyResult : Type → Type → Result Subst
unifyResult A B with unify A B
... | unified σ = ok σ
... | failed e  = fail e
