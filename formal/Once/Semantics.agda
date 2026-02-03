------------------------------------------------------------------------
-- Once.Semantics
--
-- Denotational semantics for Once IR.
-- Parameterized by MachineInterface (for ⟦_⟧) and ContractSemantics.
--
-- Part of OCP-0003: Orthogonal IR design.
--
-- KEY DESIGN:
--   IR is machine-independent.
--   Semantics brings in machine-dependence via:
--     1. MachineInterface → ⟦_⟧ (type interpretation)
--     2. ContractSemantics → contract-eval (Prim semantics)
------------------------------------------------------------------------

open import Once.Backend.MachineInterface
open import Once.Contract

module Once.Semantics
  (MI : MachineInterface)
  (CI : ContractInterface)
  where

open import Once.Type
open import Once.SemanticBaseMachine MI
open import Once.Arith.ExprSemantics MI using (evalArith)
open import Once.IR
open IRDef CI

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Semantics Module (parameterized by ContractSemantics)
------------------------------------------------------------------------

module SemanticsDef (CS : ContractSemantics CI ⟦_⟧) where
  private
    prim-eval : ∀ {A B} → ContractInterface.Contract CI A B → ⟦ A ⟧ → ⟦ B ⟧
    prim-eval = ContractSemantics.contract-eval CS

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

  -- Primitives: use contract semantics
  eval (Prim _ c) x      = prim-eval c x

  -- Domain expressions: use ArithExpr semantics
  eval (Domain e) x      = evalArith e x
