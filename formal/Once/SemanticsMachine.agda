------------------------------------------------------------------------
-- Once.SemanticsMachine
--
-- Denotational semantics for Once, parameterized by MachineInterface.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- PORTABILITY:
--   This module works with any MachineInterface instantiation:
--   - Word64Interface for x86-64, AArch64
--   - Word32Interface for x86-32, RISC-V 32
--
-- Unlike Once.Semantics (which uses ℤ for Int), this module uses
-- machine word semantics directly - no encode gap for arithmetic.
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.SemanticsMachine (MI : MachineInterface) where

open import Once.Type
open import Once.SemanticBaseMachine MI
open import Once.Backend.ContractInterfaceMachine ⟦_⟧
open import Once.IRMachine ⟦_⟧

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Propositional η-equality for Closure records
------------------------------------------------------------------------

-- Records in mutual blocks lack definitional η-equality in Agda.
-- This postulate provides propositional η.
postulate
  Closure-η : ∀ {A B} (cl : Closure A B) →
    record { env-addr = env-addr cl
           ; semantics = semantics cl } ≡ cl

------------------------------------------------------------------------
-- Parameterized Semantics Module
------------------------------------------------------------------------

-- | Semantics parameterized by ContractInterface
--
module SemanticsDef (CI : ContractInterface) where
  open IRDef CI

  ------------------------------------------------------------------------
  -- Evaluation of IR morphisms
  ------------------------------------------------------------------------

  -- | Evaluation of IR morphisms
  --
  -- Maps IR morphisms to Agda functions.
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

  -- Primitives (explicit semantic function - no evalPrim postulate!)
  eval (Prim _ sem _) x  = sem x
