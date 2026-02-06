------------------------------------------------------------------------
-- Once.Semantics
--
-- Denotational semantics for Once IR.
-- Parameterized by MachineInterface (for ⟦_⟧) and ContractInterface.
--
-- Part of OCP-0003: Orthogonal IR design.
--
-- KEY DESIGN:
--   Prim embeds semantics directly - no ContractSemantics needed.
--   eval for Prim just uses the embedded semantic function.
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.Semantics (MI : MachineInterface) where

open import Once.Type
open import Once.SemanticBaseMachine MI
open import Once.Contract
open import Once.IR ⟦_⟧

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Propositional η-equality for Closure records
------------------------------------------------------------------------

-- Records in mutual blocks lack definitional η-equality in Agda.
-- We prove propositional η by pattern matching: after destructuring,
-- both sides are definitionally equal.
Closure-η : ∀ {A B} (cl : Closure A B) →
  record { env-addr = env-addr cl
         ; semantics = semantics cl } ≡ cl
Closure-η record { env-addr = _ ; semantics = _ } = refl

------------------------------------------------------------------------
-- Semantics Module (parameterized by ContractInterface)
------------------------------------------------------------------------

module SemanticsDef (CI : ContractInterface) where
  open IRDef CI

  ------------------------------------------------------------------------
  -- Evaluation of IR morphisms
  ------------------------------------------------------------------------

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
  eval (curry {A} f) a   = record
    { env-addr  = encode {A} a
    ; semantics = λ b → eval f (a , b)
    }
  eval apply (cl , a)    = semantics cl a

  -- Recursive types
  eval fold x            = wrap x
  eval unfold x          = unwrap x

  -- Effect lifting
  eval arr cl            = cl

  -- Primitives: use embedded semantics (no ContractSemantics needed!)
  eval (Prim _ sem _) x  = sem x
