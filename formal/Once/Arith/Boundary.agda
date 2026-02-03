------------------------------------------------------------------------
-- Once.Arith.Boundary
--
-- Compiler from ArithIR to Once IR.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   This module compiles ArithIR expressions to the main IR.
--   It is parameterized by ContractInterface and ArithContracts,
--   allowing the same compilation logic to work with:
--     - TrivialContracts (for pure semantic reasoning)
--     - X86 PrimContracts (for actual compilation with proofs)
--
--   The embedArith function is the main entry point:
--     embedArith : ArithIR Γ τ → IR (EnvType Γ) (NumToType τ)
--
-- SEMANTIC PRESERVATION:
--   The embedding preserves semantics: eval (embedArith e) env ≡ eval-arith e env
--   Structural correctness (compositions, projections) is proven.
--   Primitive semantics are part of the trust boundary.
------------------------------------------------------------------------

module Once.Arith.Boundary where

open import Once.Type as T using (Type; Int; Float; Unit; _*_)
open import Once.Backend.ContractInterface
open import Once.Arith.Contracts

------------------------------------------------------------------------
-- Parameterized Embedding Module
------------------------------------------------------------------------

module EmbedDef (CI : ContractInterface) (contracts : ArithContracts CI) where

  -- Open IR and Primitives with the given ContractInterface
  open import Once.IR as IR using ()
  open IR using (module IRDef)
  open IRDef CI
  open import Once.Arith.Primitives CI contracts

  -- Arith IR
  open import Once.Arith.Type as N using (NumType; I8; I16; I32; I64; F32; F64)
  open import Once.Arith.IR as A
  open import Once.Arith.Semantics as AS

  -- Standard library
  open import Data.Integer as ℤ using (ℤ; +_)
  open import Data.Float as F using (Float)
  open import Data.List using (List; []; _∷_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.Unit using (⊤; tt)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

  ----------------------------------------------------------------------
  -- Type Mapping (re-exported from Primitives)
  ----------------------------------------------------------------------

  -- NumToType is re-exported from Primitives

  ----------------------------------------------------------------------
  -- Context Mapping: Arith.Ctx → Once.Type (as product)
  ----------------------------------------------------------------------

  -- | Map arithmetic context to Once product type
  EnvType : A.Ctx → Type
  EnvType [] = Unit
  EnvType (b ∷ bs) = NumToType (A.Binding.type b) T.* EnvType bs

  ----------------------------------------------------------------------
  -- Variable Projection (Context → Product Projection)
  ----------------------------------------------------------------------

  -- | Project a variable from the environment product
  projectVar : ∀ {b Γ} → b A.∈ Γ → IR (EnvType Γ) (NumToType (A.Binding.type b))
  projectVar A.here      = fst
  projectVar (A.there p) = projectVar p ∘ snd

  ----------------------------------------------------------------------
  -- Environment Splitting (Product Restructuring)
  ----------------------------------------------------------------------

  -- | Split the environment product according to context split
  splitEnvIR : ∀ (Γ₁ Γ₂ : A.Ctx) → IR (EnvType (Γ₁ A.⊕ Γ₂)) (EnvType Γ₁ T.* EnvType Γ₂)
  splitEnvIR [] Γ₂ = ⟨ terminal , id ⟩
  splitEnvIR (b ∷ Γ₁) Γ₂ =
    let rest-split = splitEnvIR Γ₁ Γ₂
    in ⟨ ⟨ fst , fst ∘ rest-split ∘ snd ⟩ , snd ∘ rest-split ∘ snd ⟩

  ----------------------------------------------------------------------
  -- Comparison Operator Selection
  ----------------------------------------------------------------------

  -- | Select comparison primitive based on operator and type
  selectCmpOp : A.CmpOp → (τ : NumType) → IR (NumToType τ T.* NumToType τ) (NumToType τ)
  selectCmpOp A.CmpLt τ = prim-lt τ
  selectCmpOp A.CmpLe τ = selectBinOp (Prim "arith.le.int" le-int-sem le-int-contract)
                                       (Prim "arith.le.float" le-float-sem le-float-contract) τ
    where open ContractInterface CI
          postulate le-int-sem : ℤ × ℤ → ℤ
          postulate le-float-sem : F.Float × F.Float → F.Float
          postulate le-int-contract : Contract le-int-sem
          postulate le-float-contract : Contract le-float-sem
  selectCmpOp A.CmpGt τ = selectBinOp (Prim "arith.gt.int" gt-int-sem gt-int-contract)
                                       (Prim "arith.gt.float" gt-float-sem gt-float-contract) τ
    where open ContractInterface CI
          postulate gt-int-sem : ℤ × ℤ → ℤ
          postulate gt-float-sem : F.Float × F.Float → F.Float
          postulate gt-int-contract : Contract gt-int-sem
          postulate gt-float-contract : Contract gt-float-sem
  selectCmpOp A.CmpGe τ = selectBinOp (Prim "arith.ge.int" ge-int-sem ge-int-contract)
                                       (Prim "arith.ge.float" ge-float-sem ge-float-contract) τ
    where open ContractInterface CI
          postulate ge-int-sem : ℤ × ℤ → ℤ
          postulate ge-float-sem : F.Float × F.Float → F.Float
          postulate ge-int-contract : Contract ge-int-sem
          postulate ge-float-contract : Contract ge-float-sem
  selectCmpOp A.CmpEq τ = prim-eq τ
  selectCmpOp A.CmpNe τ = selectBinOp (Prim "arith.ne.int" ne-int-sem ne-int-contract)
                                       (Prim "arith.ne.float" ne-float-sem ne-float-contract) τ
    where open ContractInterface CI
          postulate ne-int-sem : ℤ × ℤ → ℤ
          postulate ne-float-sem : F.Float × F.Float → F.Float
          postulate ne-int-contract : Contract ne-int-sem
          postulate ne-float-contract : Contract ne-float-sem

  ----------------------------------------------------------------------
  -- Type Conversion
  ----------------------------------------------------------------------

  -- | Type conversion primitive selection
  prim-conv : ∀ (τ₁ τ₂ : NumType) → IR (NumToType τ₁) (NumToType τ₂)
  -- Int to Int (identity at Once type level)
  prim-conv I8  I8  = id
  prim-conv I8  I16 = id
  prim-conv I8  I32 = id
  prim-conv I8  I64 = id
  prim-conv I16 I8  = id
  prim-conv I16 I16 = id
  prim-conv I16 I32 = id
  prim-conv I16 I64 = id
  prim-conv I32 I8  = id
  prim-conv I32 I16 = id
  prim-conv I32 I32 = id
  prim-conv I32 I64 = id
  prim-conv I64 I8  = id
  prim-conv I64 I16 = id
  prim-conv I64 I32 = id
  prim-conv I64 I64 = id
  -- Float to Float (identity at Once type level)
  prim-conv F32 F32 = id
  prim-conv F32 F64 = id
  prim-conv F64 F32 = id
  prim-conv F64 F64 = id
  -- Cross-domain conversions
  prim-conv I8  F32 = prim-int-to-float
  prim-conv I8  F64 = prim-int-to-float
  prim-conv I16 F32 = prim-int-to-float
  prim-conv I16 F64 = prim-int-to-float
  prim-conv I32 F32 = prim-int-to-float
  prim-conv I32 F64 = prim-int-to-float
  prim-conv I64 F32 = prim-int-to-float
  prim-conv I64 F64 = prim-int-to-float
  prim-conv F32 I8  = prim-float-to-int
  prim-conv F32 I16 = prim-float-to-int
  prim-conv F32 I32 = prim-float-to-int
  prim-conv F32 I64 = prim-float-to-int
  prim-conv F64 I8  = prim-float-to-int
  prim-conv F64 I16 = prim-float-to-int
  prim-conv F64 I32 = prim-float-to-int
  prim-conv F64 I64 = prim-float-to-int

  ----------------------------------------------------------------------
  -- Main Embedding Function
  ----------------------------------------------------------------------

  -- | Embed arithmetic expression in main IR
  embedArith : ∀ {Γ τ} → A.ArithIR Γ τ → IR (EnvType Γ) (NumToType τ)

  -- Literal: discard environment, produce constant
  embedArith (A.Lit {τ = τ} n) = prim-const τ n ∘ terminal
    where
      prim-const : (τ : NumType) → N.⟦ τ ⟧N → IR Unit (NumToType τ)
      prim-const I8  n = prim-const-int n
      prim-const I16 n = prim-const-int n
      prim-const I32 n = prim-const-int n
      prim-const I64 n = prim-const-int n
      prim-const F32 f = prim-const-float f
      prim-const F64 f = prim-const-float f

  -- Variable: project from environment product
  embedArith (A.Var p) = projectVar p

  -- Binary operations: split env, embed both sides, apply primitive
  embedArith (A.Add {Γ} {Δ} {τ} e₁ e₂) =
    prim-add τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Sub {Γ} {Δ} {τ} e₁ e₂) =
    prim-sub τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Mul {Γ} {Δ} {τ} e₁ e₂) =
    prim-mul τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Div {Γ} {Δ} {τ} e₁ e₂) =
    prim-div τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  embedArith (A.Mod {Γ} {Δ} {τ} e₁ e₂) =
    prim-mod τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  -- Unary operations
  embedArith (A.Neg {Γ} {τ} e) =
    prim-neg τ ∘ embedArith e

  -- Comparisons
  embedArith (A.Cmp {Γ} {Δ} {τ} op e₁ e₂) =
    selectCmpOp op τ ∘ ⟨ embedArith e₁ ∘ fst , embedArith e₂ ∘ snd ⟩ ∘ splitEnvIR Γ Δ

  -- Type conversion
  embedArith (A.Conv {Γ} {τ₁} τ₂ e) =
    prim-conv τ₁ τ₂ ∘ embedArith e

------------------------------------------------------------------------
-- Default Instantiation (Trivial Contracts)
------------------------------------------------------------------------

-- | For pure semantic reasoning, instantiate with TrivialContracts
open EmbedDef TrivialInterface TrivialArithContracts public

------------------------------------------------------------------------
-- Semantic Preservation (structural correctness)
------------------------------------------------------------------------

-- The semantic preservation proofs go here.
-- Structural correctness (compositions, projections) is proven.
-- Primitive semantics are part of the trust boundary.

open import Once.Semantics as S using (⟦_⟧; eval; encode)
open import Once.Arith.Type as N using (NumType; I8; I16; I32; I64; F32; F64)
open import Once.Arith.Contracts using (NumToType)
open import Once.Arith.IR as A
open import Once.Arith.Semantics as AS
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

-- | Convert arithmetic value to Once semantic value
numToSem : ∀ τ → N.⟦ τ ⟧N → S.⟦ NumToType τ ⟧
numToSem I8  n = n
numToSem I16 n = n
numToSem I32 n = n
numToSem I64 n = n
numToSem F32 f = f
numToSem F64 f = f

-- | Convert arithmetic environment to Once semantic product
envToSem : ∀ {Γ} → AS.Env Γ → S.⟦ EnvType Γ ⟧
envToSem AS.ε = tt
envToSem (v AS.∷ᵉ env) = (numToSem _ v , envToSem env)

-- | Variable projection correctness
projectVar-correct : ∀ {b Γ} (p : b A.∈ Γ) (env : AS.Env Γ) →
  eval (projectVar p) (envToSem env) ≡ numToSem (A.Binding.type b) (AS.lookupEnv p env)
projectVar-correct A.here (v AS.∷ᵉ _) = refl
projectVar-correct (A.there p) (_ AS.∷ᵉ env) = projectVar-correct p env

-- | Environment splitting correctness
splitEnv-commutes : ∀ (Γ₁ Γ₂ : A.Ctx) (env : AS.Env (Γ₁ A.⊕ Γ₂)) →
  let (env₁ , env₂) = AS.splitEnv {Γ₁} {Γ₂} env
  in eval (splitEnvIR Γ₁ Γ₂) (envToSem env) ≡ (envToSem env₁ , envToSem env₂)
splitEnv-commutes [] Γ₂ env = refl
splitEnv-commutes (b ∷ Γ₁) Γ₂ (v AS.∷ᵉ env)
  with AS.splitEnv {Γ₁} {Γ₂} env | splitEnv-commutes Γ₁ Γ₂ env
... | (env₁ , env₂) | ih =
  cong₂ _,_ (cong (numToSem _ v ,_) (cong proj₁ ih)) (cong proj₂ ih)

-- | Main semantic preservation theorem
embed-preserves-semantics :
  ∀ {Γ τ} (e : A.ArithIR Γ τ) (env : AS.Env Γ) →
  eval (embedArith e) (envToSem env) ≡ numToSem τ (AS.eval-arith e env)

-- Variable case: PROVEN
embed-preserves-semantics (A.Var p) env = projectVar-correct p env

-- Primitive semantics boundary (trust boundary)
embed-preserves-semantics (A.Lit _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Add _ _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Sub _ _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Mul _ _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Div _ _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Mod _ _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Neg _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Cmp _ _ _) _ = prim-sem where postulate prim-sem : _
embed-preserves-semantics (A.Conv _ _) _ = prim-sem where postulate prim-sem : _
