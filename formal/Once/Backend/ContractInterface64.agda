------------------------------------------------------------------------
-- Once.Backend.ContractInterface64
--
-- Contract interface using Word64 semantics.
-- This is the concrete instantiation for 64-bit backends.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
------------------------------------------------------------------------

module Once.Backend.ContractInterface64 where

open import Once.Type
open import Once.Backend.Word64 using (Word64)
open import Once.Memory as Mem using () renaming (Word to MemWord)

open import Data.Nat using (ℕ)
open import Data.List using (List; [])
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Float using () renaming (Float to AgdaFloat)

------------------------------------------------------------------------
-- Type Interpretation with Word64 for Int
------------------------------------------------------------------------

-- Define ⟦_⟧ directly here to avoid parameterized module issues
{-# NO_POSITIVITY_CHECK #-}
mutual
  record Closure64 (A B : Type) : Set where
    field
      env-addr  : MemWord
      semantics : ⟦ A ⟧ → ⟦ B ⟧

  -- Fixed point wrapper
  record Fix64 (A : Set) : Set where
    constructor wrap64
    field unwrap64 : A

  ⟦_⟧ : Type → Set
  ⟦ Unit ⟧         = ⊤
  ⟦ Void ⟧         = ⊥
  ⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ A ⇒[ q ] B ⟧   = Closure64 A B
  ⟦ Eff A B ⟧      = Closure64 A B
  ⟦ Fix F ⟧        = Fix64 ⟦ F ⟧
  ⟦ Int ⟧          = Word64          -- KEY: Word64 instead of ℤ
  ⟦ Float ⟧        = AgdaFloat
  ⟦ Str ⟧          = String
  ⟦ Buffer ⟧       = String
  ⟦ TVar _ ⟧       = ⊤

------------------------------------------------------------------------
-- Contract Interface for Word64
------------------------------------------------------------------------

record ContractInterface64 : Set₁ where
  field
    Contract : {A B : Type} → (⟦ A ⟧ → ⟦ B ⟧) → Set
    contract-length : {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} → Contract sem → ℕ
    contract-assembly : {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} → Contract sem → List String

open ContractInterface64 public

------------------------------------------------------------------------
-- Trivial Contract
------------------------------------------------------------------------

record TrivialContract64 {A B : Type} (sem : ⟦ A ⟧ → ⟦ B ⟧) : Set where
  constructor trivial

TrivialInterface64 : ContractInterface64
TrivialInterface64 = record
  { Contract = TrivialContract64
  ; contract-length = λ _ → 0
  ; contract-assembly = λ _ → []
  }

------------------------------------------------------------------------
-- Encoding (identity for Word64)
------------------------------------------------------------------------

encode-int64 : Word64 → MemWord
encode-int64 n = n  -- Identity! Word64 = ℕ = MemWord
