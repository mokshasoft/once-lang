------------------------------------------------------------------------
-- Once.Arith.BoundaryMachine
--
-- Arith compiler using machine word semantics.
-- NO ENCODE POSTULATES - machine operations ARE the semantics.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   This module is PARAMETERIZED by MachineInterface for portability.
--   Word size is a backend detail, not visible to this module.
--
--   Key difference from old Boundary:
--     Boundary:        ⟦ Int ⟧ = ℤ,    needs encode postulates
--     BoundaryMachine: ⟦ Int ⟧ = Word, encode is identity
--
--   Instantiation happens at the EDGES:
--     open import Once.Arith.BoundaryMachine Word64Interface  -- x86-64
--     open import Once.Arith.BoundaryMachine Word32Interface  -- 32-bit
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.Arith.BoundaryMachine (MI : MachineInterface) where

open import Once.Type as T using (Type; Int; Float; Unit; _*_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)

-- Import SemanticBaseMachine MI - defines ⟦_⟧ for this word size
-- NOTE: ArithContracts MI also imports SemanticBaseMachine MI.
-- Since both use the same MI parameter, Agda treats them as the
-- same module instance, giving the same ⟦_⟧.
open import Once.SemanticBaseMachine MI using (⟦_⟧)

-- ContractInterfaceMachine needs ⟦_⟧ passed explicitly
open import Once.Backend.ContractInterfaceMachine ⟦_⟧

-- ArithContracts imports SemanticBaseMachine MI internally (same MI = same ⟦_⟧)
open import Once.Arith.MachineContracts using (module Semantics; module ArithContracts; NumToType)
open ArithContracts MI using (ArithMachineContracts; module ArithMachineContracts)

------------------------------------------------------------------------
-- Parameterized Embedding Module
------------------------------------------------------------------------

-- Define IntWord for contract specialization
-- IntWord = ℕ (since ⟦ Int ⟧ = ℕ from SemanticBaseMachine)
private
  IntWord : Set
  IntWord = ℕ

-- Specialize contract types from ContractInterface to Word types.
-- This works because ⟦ Int ⟧ = IntWord (from SemanticBaseMachine MI).
module _ (CI : ContractInterface) where
  open ContractInterface CI

  BinOpContract : (IntWord × IntWord → IntWord) → Set
  BinOpContract = Contract {Int T.* Int} {Int}

  UnaryOpContract : (IntWord → IntWord) → Set
  UnaryOpContract = Contract {Int} {Int}

  ConstContract : IntWord → (⊤ → IntWord) → Set
  ConstContract _ = Contract {Unit} {Int}

module EmbedDef (CI : ContractInterface) (contracts : ArithMachineContracts (BinOpContract CI) (UnaryOpContract CI) (ConstContract CI)) where

  -- Pass ⟦_⟧ to IRMachine
  open import Once.IRMachine ⟦_⟧ as IR using ()
  open IR using (module IRDef)
  open IRDef CI
  open ContractInterface CI

  -- Re-open machine semantics (using the parameterized MI)
  -- Note: use module-level IntWord to avoid shadowing
  open MachineInterface MI using (word-from-ℤ)
  open Semantics MI

  -- Arith IR
  open import Once.Arith.Type as N using (NumType; I8; I16; I32; I64; F32; F64)
  open import Once.Arith.IR as A

  -- Standard library
  open import Data.List using (List; []; _∷_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.Unit using (⊤; tt)
  open import Data.Float as F using (Float)

  ----------------------------------------------------------------------
  -- Type Mapping (imported from MachineContracts)
  ----------------------------------------------------------------------

  -- NumToType is imported from Once.Arith.MachineContracts

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
  ----------------------------------------------------------------------

  -- Get contracts from the ArithMachineContracts record
  private
    MC = ArithMachineContracts.add-int-contract contracts

  -- Binary operation primitives using machine semantics
  prim-add : IR (Int T.* Int) Int
  prim-add = Prim "arith.add" add-int-sem (ArithMachineContracts.add-int-contract contracts)

  prim-sub : IR (Int T.* Int) Int
  prim-sub = Prim "arith.sub" sub-int-sem (ArithMachineContracts.sub-int-contract contracts)

  prim-mul : IR (Int T.* Int) Int
  prim-mul = Prim "arith.mul" mul-int-sem (ArithMachineContracts.mul-int-contract contracts)

  prim-div : IR (Int T.* Int) Int
  prim-div = Prim "arith.div" div-int-sem (ArithMachineContracts.div-int-contract contracts)

  prim-mod : IR (Int T.* Int) Int
  prim-mod = Prim "arith.mod" mod-int-sem (ArithMachineContracts.mod-int-contract contracts)

  prim-neg : IR Int Int
  prim-neg = Prim "arith.neg" neg-int-sem (ArithMachineContracts.neg-int-contract contracts)

  prim-lt : IR (Int T.* Int) Int
  prim-lt = Prim "arith.lt" lt-int-sem (ArithMachineContracts.lt-int-contract contracts)

  prim-eq : IR (Int T.* Int) Int
  prim-eq = Prim "arith.eq" eq-int-sem (ArithMachineContracts.eq-int-contract contracts)

  -- Constant loading
  prim-const : IntWord → IR Unit Int
  prim-const n = Prim "arith.const" (const-int-sem n) (ArithMachineContracts.const-int-contract contracts n)

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
      -- Cross-domain conversions need proper primitives (TODO: OCP-0003 Phase 4)
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

------------------------------------------------------------------------
-- Key Benefit: No Encode Postulates!
------------------------------------------------------------------------

-- With ⟦ Int ⟧ = Word (from MachineInterface):
--   add-int-sem : Word × Word → Word = word-add
--   The machine ADD instruction computes word-add.
--   encode-int : Word → MemWord is identity.
--
-- Therefore: NO encode-add, encode-sub, etc. postulates needed!
-- The semantic function IS the machine operation.
--
-- PORTABILITY: Same module works for any MachineInterface:
--   Word64Interface → x86-64, AArch64
--   Word32Interface → x86-32, RISC-V 32-bit
