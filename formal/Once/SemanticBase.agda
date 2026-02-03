------------------------------------------------------------------------
-- Once.SemanticBase
--
-- Shared semantic interpretation of types.
-- Used by both Once.Semantics (unsized) and Once.SemanticsS (sized).
--
-- Contains:
--   - Closure record
--   - ⟦_⟧ type interpretation
--   - Encoding postulates
--   - encode function
--
-- NOTE: This module uses ℤ for integer semantics (mathematical integers).
-- For machine-word semantics (no encode gap), see Once.SemanticBase64
-- which uses Word64 from MachineInterface.
------------------------------------------------------------------------

module Once.SemanticBase where

open import Once.Type
open import Once.Memory using (Word)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer using (ℤ)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)

------------------------------------------------------------------------
-- Fixed Point Wrapper
------------------------------------------------------------------------

record ⟦Fix⟧ (A : Set) : Set where
  constructor wrap
  field unwrap : A

open ⟦Fix⟧ public

------------------------------------------------------------------------
-- Closure Record and Type Interpretation
------------------------------------------------------------------------

-- NOTE: NO_POSITIVITY_CHECK needed for mutual recursion between
-- Closure.semantics : ⟦ A ⟧ → ⟦ B ⟧ and ⟦ A ⇒ B ⟧ = Closure A B
--
-- NOTE: code-ptr is NOT part of the semantic Closure record.
-- It's a compilation artifact determined by CodeGen, not a semantic property.
-- Runtime code-ptr is tracked in ClosureAtS (memory layout) and
-- ClosureWellFormed (links code-ptr to program location).
{-# NO_POSITIVITY_CHECK #-}
mutual
  record Closure (A B : Type) : Set where
    field
      env-addr  : Word           -- encoded environment address
      semantics : ⟦ A ⟧ → ⟦ B ⟧  -- the function behavior

  ⟦_⟧ : Type → Set
  ⟦ Unit ⟧         = ⊤
  ⟦ Void ⟧         = ⊥
  ⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ A ⇒[ q ] B ⟧   = Closure A B
  ⟦ Eff A B ⟧      = Closure A B
  ⟦ Fix F ⟧        = ⟦Fix⟧ ⟦ F ⟧
  ⟦ Int ⟧          = ℤ
  ⟦ Float ⟧        = AgdaFloat
  ⟦ Str ⟧          = String
  ⟦ Buffer ⟧       = String
  ⟦ TVar _ ⟧       = ⊤

open Closure public

------------------------------------------------------------------------
-- Encoding Functions (DEFINITIONS, not postulates)
--
-- These return placeholder addresses (0) for compound types.
-- X86 proofs use ValidAt which tracks actual allocated addresses,
-- so these placeholder values are never used in correctness proofs.
--
-- The AllocatorSemantics module provides the semantic guarantee that
-- ANY encode function produces heap addresses (via alloc-encode).
------------------------------------------------------------------------

-- Compound types: return placeholder (actual addresses tracked by ValidAt)
encode-pair-addr    : ∀ {A B : Type} → ⟦ A ⟧ → ⟦ B ⟧ → Word
encode-pair-addr _ _ = 0

encode-inl-addr     : ∀ {A B : Type} → ⟦ A ⟧ → Word
encode-inl-addr _ = 0

encode-inr-addr     : ∀ {A B : Type} → ⟦ B ⟧ → Word
encode-inr-addr _ = 0

encode-closure-addr : ∀ {A B : Type} → Closure A B → Word
encode-closure-addr _ = 0

-- Primitive types: direct conversion where possible
open import Data.Integer using (∣_∣) renaming (ℤ to ℤ-import)

encode-int          : ℤ → Word
encode-int n = ∣ n ∣  -- absolute value as Word

encode-float        : AgdaFloat → Word
encode-float _ = 0  -- placeholder (IEEE 754 conversion would go here)

encode-str          : String → Word
encode-str _ = 0  -- placeholder (string interning address)

encode-buffer       : String → Word
encode-buffer _ = 0  -- placeholder (buffer allocation address)

-- NOTE: evalPrim postulate has been ELIMINATED!
-- Primitive semantics are now carried directly in the IR constructor:
--   Prim : String → (⟦ A ⟧ → ⟦ B ⟧) → IR A B
-- This makes primitive behavior explicit and eliminates a trust boundary.

------------------------------------------------------------------------
-- Encode Function
------------------------------------------------------------------------

{-# TERMINATING #-}
encode : ∀ {A} → ⟦ A ⟧ → Word
encode {Unit} tt = 0
encode {Void} ()
encode {A * B} (a , b) = encode-pair-addr {A} {B} a b
encode {A + B} (inj₁ a) = encode-inl-addr {A} {B} a
encode {A + B} (inj₂ b) = encode-inr-addr {A} {B} b
encode {A ⇒[ q ] B} cl = encode-closure-addr cl
encode {Eff A B} cl = encode-closure-addr cl
encode {Fix F} (wrap x) = encode {F} x
encode {Int} n = encode-int n
encode {Float} f = encode-float f
encode {Str} s = encode-str s
encode {Buffer} b = encode-buffer b
encode {TVar _} _ = 0

------------------------------------------------------------------------
-- Proven Encoding Properties
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

encode-unit : encode {Unit} tt ≡ 0
encode-unit = refl

encode-fix-wrap : ∀ {F} (x : ⟦ F ⟧) → encode {F} x ≡ encode {Fix F} (wrap x)
encode-fix-wrap x = refl

encode-fix-unwrap : ∀ {F} (x : ⟦ Fix F ⟧) → encode {Fix F} x ≡ encode {F} (unwrap x)
encode-fix-unwrap (wrap x) = refl

encode-arr-identity : ∀ {A B} (cl : Closure A B) → encode {A ⇒ B} cl ≡ encode {Eff A B} cl
encode-arr-identity cl = refl
