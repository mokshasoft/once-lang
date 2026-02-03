------------------------------------------------------------------------
-- Once.Arith.Contracts
--
-- Contract interface for arithmetic operations.
-- This defines what any backend must provide to compile arithmetic.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   ArithContracts CI is a record of contracts for each arithmetic operation.
--   Each backend (X86, AArch64, etc.) provides an instance.
--   The Primitives module uses this to create Prim IR terms.
------------------------------------------------------------------------

module Once.Arith.Contracts where

open import Once.Type using (Type; Int; Unit; _*_)
open import Once.Type using () renaming (Float to FloatTy)
-- Note: Semantic functions use raw Agda types (ℤ, F.Float, ⊤)
-- which match ⟦ Int ⟧, ⟦ Float ⟧, ⟦ Unit ⟧ respectively
open import Once.Backend.ContractInterface

open import Data.Integer as ℤ using (ℤ; +_; _+_; _-_; _*_; -_)
open import Data.Float as F using (Float)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Integer.Properties using (_≟_; _<?_)

------------------------------------------------------------------------
-- Type Mapping: NumType → Once.Type
------------------------------------------------------------------------

open import Once.Arith.Type using (NumType; I8; I16; I32; I64; F32; F64)

-- | Map arithmetic numeric types to Once types
NumToType : NumType → Type
NumToType I8  = Int
NumToType I16 = Int
NumToType I32 = Int
NumToType I64 = Int
NumToType F32 = FloatTy
NumToType F64 = FloatTy

------------------------------------------------------------------------
-- Semantic Functions for Arithmetic Operations
------------------------------------------------------------------------

-- These define the mathematical meaning of each operation.
-- They are shared across all backends.

-- Integer operations
add-int-sem : ℤ × ℤ → ℤ
add-int-sem (a , b) = a ℤ.+ b

sub-int-sem : ℤ × ℤ → ℤ
sub-int-sem (a , b) = a ℤ.- b

mul-int-sem : ℤ × ℤ → ℤ
mul-int-sem (a , b) = a ℤ.* b

neg-int-sem : ℤ → ℤ
neg-int-sem x = ℤ.- x

-- Division and modulo are postulated because Agda's div/mod require NonZero proofs.
-- The proper solution is in MachineContracts which uses Word64 with explicit zero handling.
postulate
  div-int-sem : ℤ × ℤ → ℤ
  mod-int-sem : ℤ × ℤ → ℤ

-- Comparisons return 1 if true, 0 if false (standard C/x86 convention)
lt-int-sem : ℤ × ℤ → ℤ
lt-int-sem (a , b) with a <? b
... | yes _ = + 1
... | no  _ = + 0

eq-int-sem : ℤ × ℤ → ℤ
eq-int-sem (a , b) with a ≟ b
... | yes _ = + 1
... | no  _ = + 0

-- Float operations (postulated - Agda's Float support is limited)
postulate
  add-float-sem : F.Float × F.Float → F.Float
  sub-float-sem : F.Float × F.Float → F.Float
  mul-float-sem : F.Float × F.Float → F.Float
  div-float-sem : F.Float × F.Float → F.Float
  mod-float-sem : F.Float × F.Float → F.Float
  neg-float-sem : F.Float → F.Float
  lt-float-sem : F.Float × F.Float → F.Float
  eq-float-sem : F.Float × F.Float → F.Float

-- Cross-domain conversions
postulate
  int-to-float-sem : ℤ → F.Float
  float-to-int-sem : F.Float → ℤ

-- Constant loading (parameterized by the value)
-- Note: ⟦ Unit ⟧ = ⊤, so we use ⊤ directly for clarity
const-int-sem : ℤ → ⊤ → ℤ
const-int-sem n _ = n

const-float-sem : F.Float → ⊤ → F.Float
const-float-sem f _ = f

------------------------------------------------------------------------
-- ArithContracts: What a backend must provide
------------------------------------------------------------------------

-- | Record of contracts for all arithmetic operations.
-- Each backend instantiates this with its own contract type.
--
record ArithContracts (CI : ContractInterface) : Set₁ where
  open ContractInterface CI

  field
    -- Integer binary operations
    add-int-contract : Contract add-int-sem
    sub-int-contract : Contract sub-int-sem
    mul-int-contract : Contract mul-int-sem
    div-int-contract : Contract div-int-sem
    mod-int-contract : Contract mod-int-sem

    -- Integer unary operations
    neg-int-contract : Contract neg-int-sem

    -- Integer comparisons
    lt-int-contract : Contract lt-int-sem
    eq-int-contract : Contract eq-int-sem

    -- Float binary operations
    add-float-contract : Contract add-float-sem
    sub-float-contract : Contract sub-float-sem
    mul-float-contract : Contract mul-float-sem
    div-float-contract : Contract div-float-sem
    mod-float-contract : Contract mod-float-sem

    -- Float unary operations
    neg-float-contract : Contract neg-float-sem

    -- Float comparisons
    lt-float-contract : Contract lt-float-sem
    eq-float-contract : Contract eq-float-sem

    -- Cross-domain conversions
    int-to-float-contract : Contract int-to-float-sem
    float-to-int-contract : Contract float-to-int-sem

    -- Constant loading (parameterized)
    -- Need explicit type parameters since Agda can't infer them
    const-int-contract : ∀ (n : ℤ) → Contract {Unit} {Int} (const-int-sem n)
    const-float-contract : ∀ (f : F.Float) → Contract {Unit} {FloatTy} (const-float-sem f)

open ArithContracts public

------------------------------------------------------------------------
-- Trivial Contracts (for pure semantics, no compilation)
------------------------------------------------------------------------

-- | Trivial implementation for semantic reasoning only.
-- Uses TrivialContract (= ⊤) for all operations.
--
TrivialArithContracts : ArithContracts TrivialInterface
TrivialArithContracts = record
  { add-int-contract = trivial
  ; sub-int-contract = trivial
  ; mul-int-contract = trivial
  ; div-int-contract = trivial
  ; mod-int-contract = trivial
  ; neg-int-contract = trivial
  ; lt-int-contract = trivial
  ; eq-int-contract = trivial
  ; add-float-contract = trivial
  ; sub-float-contract = trivial
  ; mul-float-contract = trivial
  ; div-float-contract = trivial
  ; mod-float-contract = trivial
  ; neg-float-contract = trivial
  ; lt-float-contract = trivial
  ; eq-float-contract = trivial
  ; int-to-float-contract = trivial
  ; float-to-int-contract = trivial
  ; const-int-contract = λ _ → trivial
  ; const-float-contract = λ _ → trivial
  }
