------------------------------------------------------------------------
-- Once.Arith.Boundary
--
-- Arith compiler using non-indexed contracts.
-- Semantics are passed to Prim explicitly, not indexed in Contract.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   This module is PARAMETERIZED by MachineInterface for portability.
--   Word size is a backend detail, not visible to this module.
--
--   Instantiation happens at the EDGES:
--     open import Once.Arith.Boundary Word64Interface  -- x86-64
--     open import Once.Arith.Boundary Word32Interface  -- 32-bit
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.Arith.Boundary (MI : MachineInterface) where

open import Once.Type as T using (Type; Int; Float; Unit; _*_)
open import Once.Contract using (ContractInterface; module ContractInterface)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)

-- Import SemanticBaseMachine MI - defines ⟦_⟧ for this word size
open import Once.SemanticBaseMachine MI using (⟦_⟧)

-- Import non-indexed contracts
open import Once.Arith.Contracts using (module Semantics; module ArithContracts; NumToType)

------------------------------------------------------------------------
-- Parameterized Embedding Module
------------------------------------------------------------------------

module EmbedDef (CI : ContractInterface) (contracts : ArithContracts.ArithContractsRecord CI) where

  -- Use the non-indexed IR
  open import Once.IR ⟦_⟧ as IR using ()
  open IR using (module IRDef)
  open IRDef CI
  open ContractInterface CI

  -- Open machine semantics (using the parameterized MI)
  open MachineInterface MI using (word-from-ℤ)
  open Semantics MI

  -- Open contract record
  open ArithContracts CI using (ArithContractsRecord)
  open ArithContractsRecord contracts

  -- Arith IR
  open import Once.Arith.Type as N using (NumType; I8; I16; I32; I64; F32; F64)
  open import Once.Arith.IR as A

  -- Standard library
  open import Data.List using (List; []; _∷_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.Unit using (⊤; tt)
  open import Data.Float as F using (Float)
  open import Once.Memory using (Word)

  ----------------------------------------------------------------------
  -- Context Mapping
  ----------------------------------------------------------------------

  EnvType : A.Ctx → Type
  EnvType [] = Unit
  EnvType (b ∷ bs) = NumToType (A.Binding.type b) T.* EnvType bs

  ----------------------------------------------------------------------
  -- Variable Projection
  ----------------------------------------------------------------------

  projectVar : ∀ {b Γ} → b A.∈ Γ → IR (EnvType Γ) (NumToType (A.Binding.type b))
  projectVar A.here      = fst
  projectVar (A.there p) = projectVar p ∘ snd

  ----------------------------------------------------------------------
  -- Environment Splitting
  ----------------------------------------------------------------------

  splitEnvIR : ∀ (Γ₁ Γ₂ : A.Ctx) → IR (EnvType (Γ₁ A.⊕ Γ₂)) (EnvType Γ₁ T.* EnvType Γ₂)
  splitEnvIR [] Γ₂ = ⟨ terminal , id ⟩
  splitEnvIR (b ∷ Γ₁) Γ₂ =
    let rest-split = splitEnvIR Γ₁ Γ₂
    in ⟨ ⟨ fst , fst ∘ rest-split ∘ snd ⟩ , snd ∘ rest-split ∘ snd ⟩

  ----------------------------------------------------------------------
  -- Primitive Construction Helpers
  -- Prim takes (name, semantics, contract) - semantics explicit!
  ----------------------------------------------------------------------

  -- Binary operation primitives using machine semantics
  prim-add : IR (Int T.* Int) Int
  prim-add = Prim "arith.add" add-int-sem add-int-contract

  prim-sub : IR (Int T.* Int) Int
  prim-sub = Prim "arith.sub" sub-int-sem sub-int-contract

  prim-mul : IR (Int T.* Int) Int
  prim-mul = Prim "arith.mul" mul-int-sem mul-int-contract

  prim-div : IR (Int T.* Int) Int
  prim-div = Prim "arith.div" div-int-sem div-int-contract

  prim-mod : IR (Int T.* Int) Int
  prim-mod = Prim "arith.mod" mod-int-sem mod-int-contract

  prim-neg : IR Int Int
  prim-neg = Prim "arith.neg" neg-int-sem neg-int-contract

  prim-lt : IR (Int T.* Int) Int
  prim-lt = Prim "arith.lt" lt-int-sem lt-int-contract

  prim-eq : IR (Int T.* Int) Int
  prim-eq = Prim "arith.eq" eq-int-sem eq-int-contract

  -- Constant loading - same contract, different semantics
  prim-const : Word → IR Unit Int
  prim-const n = Prim "arith.const" (const-int-sem n) const-int-contract

  ----------------------------------------------------------------------
  -- Type-directed operation selection
  ----------------------------------------------------------------------

  selectBinOp : IR (Int T.* Int) Int → IR (T.Float T.* T.Float) T.Float
              → (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  selectBinOp int-op _        I8  = int-op
  selectBinOp int-op _        I16 = int-op
  selectBinOp int-op _        I32 = int-op
  selectBinOp int-op _        I64 = int-op
  selectBinOp _      float-op F32 = float-op
  selectBinOp _      float-op F64 = float-op

  selectUnaryOp : IR Int Int → IR T.Float T.Float
                → (τ : NumType) → IR (NumToType τ) (NumToType τ)
  selectUnaryOp int-op _        I8  = int-op
  selectUnaryOp int-op _        I16 = int-op
  selectUnaryOp int-op _        I32 = int-op
  selectUnaryOp int-op _        I64 = int-op
  selectUnaryOp _      float-op F32 = float-op
  selectUnaryOp _      float-op F64 = float-op

  -- Float operations (postulated for now)
  postulate
    prim-add-float : IR (T.Float T.* T.Float) T.Float
    prim-sub-float : IR (T.Float T.* T.Float) T.Float
    prim-mul-float : IR (T.Float T.* T.Float) T.Float
    prim-div-float : IR (T.Float T.* T.Float) T.Float
    prim-mod-float : IR (T.Float T.* T.Float) T.Float
    prim-neg-float : IR T.Float T.Float
    prim-lt-float : IR (T.Float T.* T.Float) T.Float
    prim-eq-float : IR (T.Float T.* T.Float) T.Float
    prim-const-float : F.Float → IR Unit T.Float

  typed-add : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  typed-add = selectBinOp prim-add prim-add-float

  typed-sub : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  typed-sub = selectBinOp prim-sub prim-sub-float

  typed-mul : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  typed-mul = selectBinOp prim-mul prim-mul-float

  typed-div : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  typed-div = selectBinOp prim-div prim-div-float

  typed-mod : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  typed-mod = selectBinOp prim-mod prim-mod-float

  typed-neg : (τ : NumType) → IR (NumToType τ) (NumToType τ)
  typed-neg = selectUnaryOp prim-neg prim-neg-float

  typed-lt : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  typed-lt = selectBinOp prim-lt prim-lt-float

  typed-eq : (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  typed-eq = selectBinOp prim-eq prim-eq-float

  ----------------------------------------------------------------------
  -- Main Embedding Function
  ----------------------------------------------------------------------

  embedArith : ∀ {Γ τ} → A.ArithIR Γ τ → IR (EnvType Γ) (NumToType τ)

  -- Literal: use machine word constant
  embedArith (A.Lit {τ = I8} n)  = prim-const (MachineInterface.word-from-ℤ MI n) ∘ terminal
  embedArith (A.Lit {τ = I16} n) = prim-const (MachineInterface.word-from-ℤ MI n) ∘ terminal
  embedArith (A.Lit {τ = I32} n) = prim-const (MachineInterface.word-from-ℤ MI n) ∘ terminal
  embedArith (A.Lit {τ = I64} n) = prim-const (MachineInterface.word-from-ℤ MI n) ∘ terminal
  embedArith (A.Lit {τ = F32} f) = prim-const-float f ∘ terminal
  embedArith (A.Lit {τ = F64} f) = prim-const-float f ∘ terminal

  -- Variable: project from environment
  embedArith (A.Var p) = projectVar p

  -- Binary operations
  embedArith (A.Add {Γ} {Δ} {τ} e₁ e₂) =
    typed-add τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Sub {Γ} {Δ} {τ} e₁ e₂) =
    typed-sub τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Mul {Γ} {Δ} {τ} e₁ e₂) =
    typed-mul τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Div {Γ} {Δ} {τ} e₁ e₂) =
    typed-div τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Mod {Γ} {Δ} {τ} e₁ e₂) =
    typed-mod τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  -- Unary operations
  embedArith (A.Neg {Γ} {τ} e) =
    typed-neg τ ∘ embedArith e

  -- Comparisons
  embedArith (A.Cmp {Γ} {Δ} {τ} A.CmpLt e₁ e₂) =
    typed-lt τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ
  embedArith (A.Cmp {Γ} {Δ} {τ} A.CmpEq e₁ e₂) =
    typed-eq τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ
  -- Other comparisons would need additional primitives
  embedArith (A.Cmp {Γ} {Δ} {τ} _ e₁ e₂) =
    typed-lt τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ  -- placeholder

  -- Type conversion (identity at machine level for same-domain)
  embedArith (A.Conv {Γ} {τ₁} τ₂ e) = conv τ₁ τ₂ ∘ embedArith e
    where
      conv : (τ₁ τ₂ : NumType) → IR (NumToType τ₁) (NumToType τ₂)
      conv I8  I8  = id
      conv I8  I16 = id
      conv I8  I32 = id
      conv I8  I64 = id
      conv I16 I8  = id
      conv I16 I16 = id
      conv I16 I32 = id
      conv I16 I64 = id
      conv I32 I8  = id
      conv I32 I16 = id
      conv I32 I32 = id
      conv I32 I64 = id
      conv I64 I8  = id
      conv I64 I16 = id
      conv I64 I32 = id
      conv I64 I64 = id
      conv F32 F32 = id
      conv F32 F64 = id
      conv F64 F32 = id
      conv F64 F64 = id
      -- Cross-domain conversions need proper primitives
      conv I8  F32 = cross-conv where postulate cross-conv : IR Int T.Float
      conv I8  F64 = cross-conv where postulate cross-conv : IR Int T.Float
      conv I16 F32 = cross-conv where postulate cross-conv : IR Int T.Float
      conv I16 F64 = cross-conv where postulate cross-conv : IR Int T.Float
      conv I32 F32 = cross-conv where postulate cross-conv : IR Int T.Float
      conv I32 F64 = cross-conv where postulate cross-conv : IR Int T.Float
      conv I64 F32 = cross-conv where postulate cross-conv : IR Int T.Float
      conv I64 F64 = cross-conv where postulate cross-conv : IR Int T.Float
      conv F32 I8  = cross-conv where postulate cross-conv : IR T.Float Int
      conv F32 I16 = cross-conv where postulate cross-conv : IR T.Float Int
      conv F32 I32 = cross-conv where postulate cross-conv : IR T.Float Int
      conv F32 I64 = cross-conv where postulate cross-conv : IR T.Float Int
      conv F64 I8  = cross-conv where postulate cross-conv : IR T.Float Int
      conv F64 I16 = cross-conv where postulate cross-conv : IR T.Float Int
      conv F64 I32 = cross-conv where postulate cross-conv : IR T.Float Int
      conv F64 I64 = cross-conv where postulate cross-conv : IR T.Float Int
