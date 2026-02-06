------------------------------------------------------------------------
-- Once.Arith.Contracts
--
-- Arithmetic contracts using non-indexed Contract type.
-- Semantics are passed to Prim explicitly, not indexed in Contract.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
------------------------------------------------------------------------

module Once.Arith.Contracts where

open import Once.Type using (Type; Int; Unit; _*_)
open import Once.Type using () renaming (Float to FloatTy)
open import Once.Contract using (ContractInterface; module ContractInterface)
open import Once.Backend.MachineInterface using (MachineInterface)
open import Once.Memory using (Word)

open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Type Mapping: NumType → Once.Type
------------------------------------------------------------------------

open import Once.Arith.Type using (NumType; I8; I16; I32; I64; F32; F64)

NumToType : NumType → Type
NumToType I8  = Int
NumToType I16 = Int
NumToType I32 = Int
NumToType I64 = Int
NumToType F32 = FloatTy
NumToType F64 = FloatTy

------------------------------------------------------------------------
-- Parameterized Semantic Functions
------------------------------------------------------------------------

-- | Semantic functions parameterized by MachineInterface
-- These ARE the machine operations - no encode gap!

module Semantics (MI : MachineInterface) where
  open MachineInterface MI
  open import Data.Nat using (_∸_; _+_)

  -- Integer binary operations
  add-int-sem : Word × Word → Word
  add-int-sem = word-add

  sub-int-sem : Word × Word → Word
  sub-int-sem = word-sub

  mul-int-sem : Word × Word → Word
  mul-int-sem = word-mul

  div-int-sem : Word × Word → Word
  div-int-sem = word-div

  mod-int-sem : Word × Word → Word
  mod-int-sem = word-mod

  -- Integer unary operations
  neg-int-sem : Word → Word
  neg-int-sem = word-neg

  -- Integer comparisons (return word-one or word-zero)
  lt-int-sem : Word × Word → Word
  lt-int-sem = word-lt

  eq-int-sem : Word × Word → Word
  eq-int-sem = word-eq

  -- Constant loading
  const-int-sem : Word → ⊤ → Word
  const-int-sem n _ = n

------------------------------------------------------------------------
-- ArithContracts: Non-indexed contract requirements for arithmetic
------------------------------------------------------------------------

-- | Record of contracts for arithmetic operations.
-- Uses NON-INDEXED contracts - semantics passed to Prim, not in Contract type.

module ArithContracts (CI : ContractInterface) where
  open ContractInterface CI

  -- Contract types are NOT indexed by semantics
  BinOpContract : Set
  BinOpContract = Contract (Int * Int) Int

  UnaryOpContract : Set
  UnaryOpContract = Contract Int Int

  ConstContract : Set
  ConstContract = Contract Unit Int

  record ArithContractsRecord : Set where
    field
      -- Integer binary operations
      add-int-contract : BinOpContract
      sub-int-contract : BinOpContract
      mul-int-contract : BinOpContract
      div-int-contract : BinOpContract
      mod-int-contract : BinOpContract

      -- Integer comparisons
      lt-int-contract : BinOpContract
      eq-int-contract : BinOpContract

      -- Integer unary operations
      neg-int-contract : UnaryOpContract

      -- Constant loading (same contract for all constants)
      const-int-contract : ConstContract

  open ArithContractsRecord public
