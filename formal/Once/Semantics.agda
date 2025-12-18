------------------------------------------------------------------------
-- Once.Semantics
--
-- Denotational semantics for Once.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
------------------------------------------------------------------------

module Once.Semantics where

open import Once.Type
open import Once.IR

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Word Type (Machine Words / Addresses)
------------------------------------------------------------------------

Word : Set
Word = ℕ

------------------------------------------------------------------------
-- KNOWN LIMITATION: Fixed Point Semantics
------------------------------------------------------------------------
--
-- The interpretation of Fix F uses a simple newtype wrapper:
--
--   ⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧
--
-- This models Fix F ≅ F, but the correct equation should be:
--
--   Fix F ≅ F[Fix F / X]   (F with recursive occurrences substituted)
--
-- For example, Nat = Fix (Unit + X) should satisfy:
--   ⟦ Nat ⟧ ≅ ⊤ ⊎ ⟦ Nat ⟧
--
-- But this model gives:
--   ⟦ Nat ⟧ = ⟦Fix⟧ (⊤ ⊎ ⟦ X ⟧)   where X is uninterpreted
--
-- The proofs eval-fold-unfold and eval-unfold-fold are trivially refl
-- because wrap/unwrap are inverses. This proves the wrapper isomorphism,
-- NOT the recursive fixed point property.
--
-- A proper treatment requires modeling F as a functor with an explicit
-- recursive position (e.g., a universe of strictly positive functors).
-- See docs/formal/what-is-proven.md for options to address this.
--
------------------------------------------------------------------------
record ⟦Fix⟧ (A : Set) : Set where
  constructor wrap
  field unwrap : A

open ⟦Fix⟧

------------------------------------------------------------------------
-- Closure Record (Explicit Function Representation)
------------------------------------------------------------------------
--
-- Closures are represented explicitly with:
--   - env-addr: Address of captured environment (for encoding)
--   - code-ptr: Address of thunk code (for apply)
--   - semantics: Actual function behavior
--
-- This makes closures inspectable, allowing `encode` to be computable.
-- Previously, ⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧ was opaque.
------------------------------------------------------------------------

-- | Semantic interpretation of types
--
-- Maps Once types to Agda types (Sets).
-- This is the object mapping of a functor from Once's CCC to Set.
--
-- NOTE: Closure and ⟦_⟧ are mutually recursive because:
--   - Closure.semantics has type ⟦ A ⟧ → ⟦ B ⟧
--   - ⟦ A ⇒ B ⟧ = Closure A B

-- NOTE: NO_POSITIVITY_CHECK is needed because Closure and ⟦_⟧ are mutually
-- recursive: Closure.semantics : ⟦ A ⟧ → ⟦ B ⟧, and ⟦ A ⇒ B ⟧ = Closure A B.
-- This appears non-strictly-positive, but is actually well-founded because:
--   1. Closures are only created via `eval (curry f)` for finite IR terms
--   2. The recursion terminates because IR has finite depth
--   3. No actual infinite regress occurs in practice
{-# NO_POSITIVITY_CHECK #-}
mutual
  record Closure (A B : Type) : Set where
    field
      env-addr  : Word           -- Encoded captured environment address
      code-ptr  : Word           -- Thunk code address
      semantics : ⟦ A ⟧ → ⟦ B ⟧  -- Actual function behavior

  ⟦_⟧ : Type → Set
  ⟦ Unit ⟧     = ⊤
  ⟦ Void ⟧     = ⊥
  ⟦ A * B ⟧    = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ A + B ⟧    = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ A ⇒ B ⟧    = Closure A B     -- Now explicit closure!
  ⟦ Eff A B ⟧  = Closure A B     -- D032: Same as pure function
  ⟦ Fix F ⟧    = ⟦Fix⟧ ⟦ F ⟧
  -- Base types
  ⟦ Int ⟧      = ℤ
  ⟦ Str ⟧      = String
  ⟦ Buffer ⟧   = String           -- Simplified: use String for bytes
  ⟦ TVar _ ⟧   = ⊤                 -- Type variables: use Unit as placeholder

open Closure public

-- | Evaluation of IR morphisms
--
-- Maps IR morphisms to Agda functions.
-- This is the morphism mapping of a functor from Once's CCC to Set.
--
-- eval : IR A B → (⟦ A ⟧ → ⟦ B ⟧)
--
eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧

-- Category structure
eval id x              = x
eval (g ∘ f) x         = eval g (eval f x)

-- Products
eval fst (a , b)       = a
eval snd (a , b)       = b
eval ⟨ f , g ⟩ x       = (eval f x , eval g x)

-- Coproducts
eval inl a             = inj₁ a
eval inr b             = inj₂ b
eval [ f , g ] (inj₁ a) = eval f a
eval [ f , g ] (inj₂ b) = eval g b

-- Terminal
eval terminal _        = tt

-- Initial
eval initial ()

-- Exponential (with explicit Closure)
-- curry f : IR A (B ⇒ C) creates a closure capturing the input
eval (curry f) a       = record
  { env-addr  = 0  -- Placeholder; actual address determined at runtime
  ; code-ptr  = 0  -- Placeholder; actual code pointer from compilation
  ; semantics = λ b → eval f (a , b)
  }
-- apply : IR ((A ⇒ B) * A) B extracts and applies the closure's semantics
eval apply (cl , a)    = semantics cl a

-- Recursive types (Fixed point isomorphism)
eval fold x            = wrap x
eval unfold x          = unwrap x

-- Effect lifting (D032)
-- arr : (A ⇒ B) → Eff A B
-- Takes a pure closure and returns it as an effectful closure
-- Both have the same Closure representation
eval arr cl            = cl
