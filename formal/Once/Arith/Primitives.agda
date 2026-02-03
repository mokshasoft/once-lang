------------------------------------------------------------------------
-- Once.Arith.Primitives
--
-- Arithmetic primitive IR terms, parameterized by ContractInterface.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   This module creates Prim IR terms for each arithmetic operation.
--   It is parameterized by:
--     1. ContractInterface - determines the contract type
--     2. ArithContracts - provides the actual contracts
--
--   Usage:
--     open import Once.Arith.Primitives X86ContractInterface X86ArithContracts
--     -- Now prim-add-int : IR (Int * Int) Int with real X86 proofs
--
--     open import Once.Arith.Primitives TrivialInterface TrivialArithContracts
--     -- Now prim-add-int : IR (Int * Int) Int with trivial contracts
------------------------------------------------------------------------

open import Once.Backend.ContractInterface
open import Once.Arith.Contracts

module Once.Arith.Primitives (CI : ContractInterface) (contracts : ArithContracts CI) where

open import Once.Type as T using (Type; Int; Unit; _*_)
open import Once.Type as T using () renaming (Float to FloatTy)

-- Open IR with the given ContractInterface
open import Once.IR as IR using ()
open IR using (module IRDef)
open IRDef CI

open import Data.Integer as ℤ using (ℤ)
open import Data.Float as F using (Float)

------------------------------------------------------------------------
-- Integer Binary Operations
------------------------------------------------------------------------

prim-add-int : IR (Int T.* Int) Int
prim-add-int = Prim "arith.add.int" add-int-sem (add-int-contract contracts)

prim-sub-int : IR (Int T.* Int) Int
prim-sub-int = Prim "arith.sub.int" sub-int-sem (sub-int-contract contracts)

prim-mul-int : IR (Int T.* Int) Int
prim-mul-int = Prim "arith.mul.int" mul-int-sem (mul-int-contract contracts)

prim-div-int : IR (Int T.* Int) Int
prim-div-int = Prim "arith.div.int" div-int-sem (div-int-contract contracts)

prim-mod-int : IR (Int T.* Int) Int
prim-mod-int = Prim "arith.mod.int" mod-int-sem (mod-int-contract contracts)

------------------------------------------------------------------------
-- Integer Unary Operations
------------------------------------------------------------------------

prim-neg-int : IR Int Int
prim-neg-int = Prim "arith.neg.int" neg-int-sem (neg-int-contract contracts)

------------------------------------------------------------------------
-- Integer Comparisons
------------------------------------------------------------------------

prim-lt-int : IR (Int T.* Int) Int
prim-lt-int = Prim "arith.lt.int" lt-int-sem (lt-int-contract contracts)

prim-eq-int : IR (Int T.* Int) Int
prim-eq-int = Prim "arith.eq.int" eq-int-sem (eq-int-contract contracts)

------------------------------------------------------------------------
-- Float Binary Operations
------------------------------------------------------------------------

prim-add-float : IR (T.Float T.* T.Float) T.Float
prim-add-float = Prim "arith.add.float" add-float-sem (add-float-contract contracts)

prim-sub-float : IR (T.Float T.* T.Float) T.Float
prim-sub-float = Prim "arith.sub.float" sub-float-sem (sub-float-contract contracts)

prim-mul-float : IR (T.Float T.* T.Float) T.Float
prim-mul-float = Prim "arith.mul.float" mul-float-sem (mul-float-contract contracts)

prim-div-float : IR (T.Float T.* T.Float) T.Float
prim-div-float = Prim "arith.div.float" div-float-sem (div-float-contract contracts)

prim-mod-float : IR (T.Float T.* T.Float) T.Float
prim-mod-float = Prim "arith.mod.float" mod-float-sem (mod-float-contract contracts)

------------------------------------------------------------------------
-- Float Unary Operations
------------------------------------------------------------------------

prim-neg-float : IR T.Float T.Float
prim-neg-float = Prim "arith.neg.float" neg-float-sem (neg-float-contract contracts)

------------------------------------------------------------------------
-- Float Comparisons
------------------------------------------------------------------------

prim-lt-float : IR (T.Float T.* T.Float) T.Float
prim-lt-float = Prim "arith.lt.float" lt-float-sem (lt-float-contract contracts)

prim-eq-float : IR (T.Float T.* T.Float) T.Float
prim-eq-float = Prim "arith.eq.float" eq-float-sem (eq-float-contract contracts)

------------------------------------------------------------------------
-- Cross-Domain Conversions
------------------------------------------------------------------------

prim-int-to-float : IR Int T.Float
prim-int-to-float = Prim "arith.conv.int-to-float" int-to-float-sem (int-to-float-contract contracts)

prim-float-to-int : IR T.Float Int
prim-float-to-int = Prim "arith.conv.float-to-int" float-to-int-sem (float-to-int-contract contracts)

------------------------------------------------------------------------
-- Constant Loading
------------------------------------------------------------------------

prim-const-int : ℤ → IR Unit Int
prim-const-int n = Prim ("arith.const.int." Data.String.++ showℤ n) (const-int-sem n) (const-int-contract contracts n)
  where
    open import Data.String using (_++_)
    open import Data.Integer.Show as ℤShow using () renaming (show to showℤ)

prim-const-float : Float → IR Unit T.Float
prim-const-float f = Prim ("arith.const.float." Data.String.++ showFloat f) (const-float-sem f) (const-float-contract contracts f)
  where
    open import Data.String using (_++_)
    open import Data.Float using () renaming (show to showFloat)

------------------------------------------------------------------------
-- Type-Directed Selection Helpers
------------------------------------------------------------------------

open import Once.Arith.Type as N using (NumType; I8; I16; I32; I64; F32; F64)

-- NumToType is imported from Contracts (shared definition)

-- | Select binary operation primitive by type
selectBinOp : (IR (Int T.* Int) Int) → (IR (T.Float T.* T.Float) T.Float)
            → (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
selectBinOp int-op _        I8  = int-op
selectBinOp int-op _        I16 = int-op
selectBinOp int-op _        I32 = int-op
selectBinOp int-op _        I64 = int-op
selectBinOp _      float-op F32 = float-op
selectBinOp _      float-op F64 = float-op

-- | Select unary operation primitive by type
selectUnaryOp : (IR Int Int) → (IR T.Float T.Float)
              → (τ : NumType) → IR (NumToType τ) (NumToType τ)
selectUnaryOp int-op _        I8  = int-op
selectUnaryOp int-op _        I16 = int-op
selectUnaryOp int-op _        I32 = int-op
selectUnaryOp int-op _        I64 = int-op
selectUnaryOp _      float-op F32 = float-op
selectUnaryOp _      float-op F64 = float-op

-- | Type-selected primitives
prim-add : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
prim-add = selectBinOp prim-add-int prim-add-float

prim-sub : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
prim-sub = selectBinOp prim-sub-int prim-sub-float

prim-mul : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
prim-mul = selectBinOp prim-mul-int prim-mul-float

prim-div : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
prim-div = selectBinOp prim-div-int prim-div-float

prim-mod : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
prim-mod = selectBinOp prim-mod-int prim-mod-float

prim-neg : (τ : NumType) → IR (NumToType τ) (NumToType τ)
prim-neg = selectUnaryOp prim-neg-int prim-neg-float

prim-lt : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
prim-lt = selectBinOp prim-lt-int prim-lt-float

prim-eq : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
prim-eq = selectBinOp prim-eq-int prim-eq-float
