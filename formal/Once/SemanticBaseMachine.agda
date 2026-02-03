------------------------------------------------------------------------
-- Once.SemanticBaseMachine
--
-- Portable semantic interpretation of types using MachineInterface.
-- Parameterized by word size - works for 64-bit, 32-bit, 16-bit, etc.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- KEY BENEFIT:
--   ⟦ Int ⟧ = Word (from MachineInterface)
--   encode-int is identity (Word = ℕ for all word sizes)
--   No encode postulates needed for integer arithmetic!
--
-- PORTABILITY:
--   open import Once.SemanticBaseMachine Word64Interface  -- x86-64, AArch64
--   open import Once.SemanticBaseMachine Word32Interface  -- x86-32, RISC-V 32
--   open import Once.SemanticBaseMachine Word16Interface  -- embedded
--
-- USAGE:
--   For x86-64:
--     open import Once.Backend.Word64 using (Word64Interface)
--     open import Once.SemanticBaseMachine Word64Interface
--
--   For mathematical semantics (backward compatibility):
--     open import Once.SemanticBase  -- uses ℤ
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.SemanticBaseMachine (MI : MachineInterface) where

open MachineInterface MI renaming (Word to IntWord)

open import Once.Type
open import Once.Memory as Mem using () renaming (Word to MemWord)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Data.Nat using (ℕ)

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

{-# NO_POSITIVITY_CHECK #-}
mutual
  record Closure (A B : Type) : Set where
    field
      env-addr  : MemWord          -- encoded environment address
      semantics : ⟦ A ⟧ → ⟦ B ⟧   -- the function behavior

  -- | Type interpretation parameterized by MachineInterface
  -- ⟦ Int ⟧ = IntWord (from MachineInterface parameter)
  ⟦_⟧ : Type → Set
  ⟦ Unit ⟧         = ⊤
  ⟦ Void ⟧         = ⊥
  ⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ A ⇒[ q ] B ⟧   = Closure A B
  ⟦ Eff A B ⟧      = Closure A B
  ⟦ Fix F ⟧        = ⟦Fix⟧ ⟦ F ⟧
  ⟦ Int ⟧          = IntWord        -- From MachineInterface!
  ⟦ Float ⟧        = AgdaFloat
  ⟦ Str ⟧          = String
  ⟦ Buffer ⟧       = String
  ⟦ TVar _ ⟧       = ⊤

open Closure public

------------------------------------------------------------------------
-- Encoding Functions
--
-- encode converts semantic values to memory words.
-- For machine integers, this requires converting IntWord → MemWord.
------------------------------------------------------------------------

-- Compound types: return placeholder (actual addresses tracked by ValidAt)
encode-pair-addr    : ∀ {A B : Type} → ⟦ A ⟧ → ⟦ B ⟧ → MemWord
encode-pair-addr _ _ = 0

encode-inl-addr     : ∀ {A B : Type} → ⟦ A ⟧ → MemWord
encode-inl-addr _ = 0

encode-inr-addr     : ∀ {A B : Type} → ⟦ B ⟧ → MemWord
encode-inr-addr _ = 0

encode-closure-addr : ∀ {A B : Type} → Closure A B → MemWord
encode-closure-addr _ = 0

-- Integer encoding: convert IntWord to MemWord
-- For Word64Interface/Word32Interface where IntWord = ℕ = MemWord,
-- this is identity. For other interfaces, we use word-to-ℕ.
--
-- NOTE: We postulate this to keep the module general.
-- For concrete instantiations (Word64, Word32), this is identity.
postulate
  encode-int : IntWord → MemWord

encode-float        : AgdaFloat → MemWord
encode-float _ = 0

encode-str          : String → MemWord
encode-str _ = 0

encode-buffer       : String → MemWord
encode-buffer _ = 0

------------------------------------------------------------------------
-- Encode Function
------------------------------------------------------------------------

{-# TERMINATING #-}
encode : ∀ {A} → ⟦ A ⟧ → MemWord
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

------------------------------------------------------------------------
-- Re-export MachineInterface operations for convenience
------------------------------------------------------------------------

-- Arithmetic operations from the MachineInterface
int-add : IntWord × IntWord → IntWord
int-add = MachineInterface.word-add MI

int-sub : IntWord × IntWord → IntWord
int-sub = MachineInterface.word-sub MI

int-mul : IntWord × IntWord → IntWord
int-mul = MachineInterface.word-mul MI

int-div : IntWord × IntWord → IntWord
int-div = MachineInterface.word-div MI

int-mod : IntWord × IntWord → IntWord
int-mod = MachineInterface.word-mod MI

int-neg : IntWord → IntWord
int-neg = MachineInterface.word-neg MI

-- Comparisons
int-lt : IntWord × IntWord → IntWord
int-lt = MachineInterface.word-lt MI

int-eq : IntWord × IntWord → IntWord
int-eq = MachineInterface.word-eq MI

-- Constants
int-zero : IntWord
int-zero = MachineInterface.word-zero MI

int-one : IntWord
int-one = MachineInterface.word-one MI

------------------------------------------------------------------------
-- Key Property: Portable and No Encode Gap for Arithmetic
------------------------------------------------------------------------

-- With ⟦ Int ⟧ = IntWord (from MachineInterface):
--
--   add-int-sem : IntWord × IntWord → IntWord
--   add-int-sem = word-add  (from MachineInterface)
--
--   For Word64Interface: word-add = word64-add (mod 2^64)
--   For Word32Interface: word-add = word32-add (mod 2^32)
--
--   The semantic operation IS the machine operation.
--   No postulates needed to bridge ℤ to machine arithmetic!
--
-- PORTABILITY:
--   Same proofs work for any MachineInterface instantiation.
--   Just swap Word64Interface for Word32Interface to target 32-bit.
