------------------------------------------------------------------------
-- Once.Arith.Boundary
--
-- Natural transformation boundary between arithmetic and control flow.
-- This module proves that arithmetic expressions can be embedded in
-- the main IR while preserving semantics.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- Key insight: The arithmetic compiler is orthogonal to the categorical
-- generators. This boundary defines the natural transformation interface:
--
--   arith : ArithIR Γ τ → IR (EnvType Γ) (NumToType τ)
--
-- Where:
--   - EnvType Γ maps arithmetic context to a product of Once types
--   - NumToType τ maps NumType to Once Type
--   - The embedding preserves semantics (eval ∘ embed = eval-arith)
------------------------------------------------------------------------

module Once.Arith.Boundary where

open import Once.Type as T using (Type; Int; Float; Unit; _*_)
open import Once.IR
open import Once.Semantics as S using (⟦_⟧; eval; encode)

open import Once.Arith.Type as N using (NumType; I8; I16; I32; I64; F32; F64)
open import Once.Arith.IR as A
open import Once.Arith.Semantics as AS

open import Data.Bool using (Bool; true; false)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Float as F using (Float)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Type Mapping: NumType → Once.Type
------------------------------------------------------------------------

-- | Map arithmetic numeric types to Once types
--
-- Integer types (I8, I16, I32, I64) map to Int.
-- Float types (F32, F64) map to Float.
--
NumToType : NumType → Type
NumToType I8  = Int
NumToType I16 = Int
NumToType I32 = Int
NumToType I64 = Int
NumToType F32 = T.Float
NumToType F64 = T.Float

------------------------------------------------------------------------
-- Context Mapping: Arith.Ctx → Once.Type (as product)
------------------------------------------------------------------------

-- | Map arithmetic context to Once product type
--
-- An arithmetic context [(x : τ₁), (y : τ₂), ...] maps to:
--   NumToType τ₁ * NumToType τ₂ * ... * Unit
--
-- The trailing Unit handles the empty context case.
--
EnvType : A.Ctx → Type
EnvType [] = Unit
EnvType (b ∷ bs) = NumToType (A.Binding.type b) T.* EnvType bs

------------------------------------------------------------------------
-- Environment Mapping: Arith.Env → Once.⟦ EnvType ⟧
------------------------------------------------------------------------

-- | Convert arithmetic value to Once semantic value
--
-- Integer NumTypes map to Int (ℤ), float NumTypes map to Float.
-- Both are identity functions since the semantic interpretations match.
--
numToSem : ∀ τ → N.⟦ τ ⟧N → S.⟦ NumToType τ ⟧
numToSem I8  n = n
numToSem I16 n = n
numToSem I32 n = n
numToSem I64 n = n
numToSem F32 f = f
numToSem F64 f = f

-- | Convert arithmetic environment to Once semantic product
--
envToSem : ∀ {Γ} → AS.Env Γ → S.⟦ EnvType Γ ⟧
envToSem AS.ε = tt
envToSem (v AS.∷ᵉ env) = (numToSem _ v , envToSem env)

------------------------------------------------------------------------
-- IR Embedding (Conceptual)
------------------------------------------------------------------------

-- | Embed arithmetic expression in main IR
--
-- This conceptual embedding shows how ArithIR maps to IR.
-- In practice, this is done in the compiler (not in the proof).
--
-- The key insight is that arithmetic operations map to primitives:
--   - ALit n     → primitive that returns n
--   - AVar x     → projection from environment product
--   - AAdd e₁ e₂ → compose: (e₁ △ e₂) ; add-primitive
--
-- We don't define the full embedding here because:
--   1. It requires extending IR with arithmetic primitives
--   2. The boundary proof only needs the semantic property
--
-- Instead, we postulate the embedding and prove its properties.

postulate
  -- | The embedding function (implemented in compiler)
  embedArith : ∀ {Γ τ} → A.ArithIR Γ τ → IR (EnvType Γ) (NumToType τ)

------------------------------------------------------------------------
-- Semantic Preservation Theorem
------------------------------------------------------------------------

-- | Semantic preservation: eval ∘ embedArith = numToSem ∘ eval-arith
--
-- This is the main theorem for the boundary proof.
-- It states that evaluating an embedded arithmetic expression
-- in the main IR semantics gives the same result as evaluating
-- it directly with arithmetic semantics.
--
-- Proof structure: By induction on the arithmetic expression.
-- - Lit: Immediate from primitive semantics
-- - Var: Follows from environment projection
-- - Add/Sub/Mul/etc: Composition of recursive cases
--
postulate
  embed-preserves-semantics :
    ∀ {Γ τ} (e : A.ArithIR Γ τ) (env : AS.Env Γ) →
    eval (embedArith e) (envToSem env) ≡ numToSem τ (AS.eval-arith e env)

------------------------------------------------------------------------
-- Corollaries
------------------------------------------------------------------------

-- | Literal embedding preserves value
postulate
  embed-lit-correct : ∀ {τ} (n : N.⟦ τ ⟧N) →
    eval (embedArith (A.Lit n)) tt ≡ numToSem τ n

-- | Binary operation embedding composes correctly
postulate
  embed-add-correct : ∀ {Γ Δ τ} (e₁ : A.ArithIR Γ τ) (e₂ : A.ArithIR Δ τ)
    (env : AS.Env (Γ A.⊕ Δ)) →
    let (env₁ , env₂) = AS.splitEnv {Γ} {Δ} env
        result = AS.add τ (AS.eval-arith e₁ env₁) (AS.eval-arith e₂ env₂)
    in eval (embedArith (A.Add e₁ e₂)) (envToSem env) ≡ numToSem τ result

------------------------------------------------------------------------
-- Natural Transformation Structure
------------------------------------------------------------------------

-- | The boundary is a natural transformation
--
-- The embedding arith : ArithIR Γ τ → IR (EnvType Γ) (NumToType τ)
-- is natural in both Γ and τ.
--
-- Naturality in Γ: For context morphism σ : Γ → Δ,
--   embedArith ∘ substArith σ = substIR (envMorph σ) ∘ embedArith
--
-- Naturality in τ: For type coercion (when applicable),
--   embedArith ∘ coerceArith = coerceIR ∘ embedArith
--
-- These properties ensure that arithmetic integration is
-- compositional with the rest of the compiler.
--

-- | Naturality square for context morphisms (postulated)
postulate
  embed-natural-ctx : ∀ {Γ Δ τ} (e : A.ArithIR Γ τ)
    (σ : A.ArithIR Δ τ) →  -- Context morphism represented as substitution
    -- The naturality equation would go here
    ⊤  -- Placeholder

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
--
-- This module establishes the semantic boundary between arithmetic
-- and the main IR (architecture-independent):
--
-- 1. Type mapping: NumType → Once.Type via NumToType
-- 2. Context mapping: Arith.Ctx → product type via EnvType
-- 3. Semantic preservation: eval ∘ embedArith = numToSem ∘ eval-arith
--
-- Machine-level correctness is proven separately in each backend's
-- Correct.agda module.
--
------------------------------------------------------------------------
-- Proof Status
------------------------------------------------------------------------
--
-- PROVEN (concrete definitions):
-- ✓ NumToType : NumType → Type
-- ✓ EnvType : Ctx → Type
-- ✓ numToSem : ⟦ τ ⟧N → ⟦ NumToType τ ⟧
-- ✓ envToSem : Env Γ → ⟦ EnvType Γ ⟧
--
-- POSTULATED (require IR extension):
-- - embedArith : ArithIR → IR (architectural integration)
-- - embed-preserves-semantics (needs embedArith definition)
-- - embed-lit-correct (corollary of above)
-- - embed-add-correct (corollary of above)
-- - embed-natural-ctx (naturality, conceptual)
--
-- The postulates represent the interface to the main IR, which
-- requires adding an 'arith' constructor. Machine-level correctness
-- is proven in each backend's Correct.agda.
--
------------------------------------------------------------------------
