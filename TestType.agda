module TestType where

open import Data.String using (String)

data Type : Set where
  Unit : Type
  Int  : Type

data PolyType : Set where
  Unit : PolyType
  Int  : PolyType
  TVar : String → PolyType

-- This should fail because Type has no TVar constructor
test : Type → Type
test (TVar x) = Unit
test _ = Int
