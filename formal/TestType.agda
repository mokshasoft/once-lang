module TestType where

postulate String : Set

data Type : Set where
  Unit : Type
  Int  : Type

data PolyType : Set where
  PUnit : PolyType
  PInt  : PolyType
  TVar : String → PolyType

-- This should fail because Type has no TVar constructor
test : Type → Type
test (TVar x) = Unit
test _ = Int
