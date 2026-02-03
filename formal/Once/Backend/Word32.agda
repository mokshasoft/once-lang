------------------------------------------------------------------------
-- Once.Backend.Word32
--
-- 32-bit word type and MachineInterface instantiation.
-- Used by x86-32, RISC-V 32, and ARM32 backends.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- TRUST BOUNDARY:
--   Same pattern as Word64.agda - we trust that these operations
--   match the corresponding 32-bit CPU instructions.
------------------------------------------------------------------------

module Once.Backend.Word32 where

open import Once.Backend.MachineInterface

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _*_; _<ᵇ_; _≡ᵇ_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Word32: 32-bit unsigned machine word
------------------------------------------------------------------------

Word32 : Set
Word32 = ℕ

-- 2^32 (for modular arithmetic)
2^32 : ℕ
2^32 = 4294967296

------------------------------------------------------------------------
-- Modular Arithmetic Operations
------------------------------------------------------------------------

word32-add : Word32 × Word32 → Word32
word32-add (a , b) = (a + b) ℕ.% 2^32
  where open import Data.Nat.DivMod using (_%_)

word32-sub : Word32 × Word32 → Word32
word32-sub (a , b) = (a ∸ b + 2^32) ℕ.% 2^32
  where open import Data.Nat.DivMod using (_%_)

word32-mul : Word32 × Word32 → Word32
word32-mul (a , b) = (a * b) ℕ.% 2^32
  where open import Data.Nat.DivMod using (_%_)

word32-div : Word32 × Word32 → Word32
word32-div (a , zero) = 0
word32-div (a , suc b) = a ℕ./ suc b
  where
    open import Data.Nat.DivMod using (_/_)
    instance _ = ℕ.nonZero

word32-mod : Word32 × Word32 → Word32
word32-mod (a , zero) = 0
word32-mod (a , suc b) = a ℕ.% suc b
  where
    open import Data.Nat.DivMod using (_%_)
    instance _ = ℕ.nonZero

word32-neg : Word32 → Word32
word32-neg zero = zero
word32-neg n = 2^32 ∸ n

------------------------------------------------------------------------
-- Comparison Operations
------------------------------------------------------------------------

bool-to-word : Bool → Word32
bool-to-word true  = 1
bool-to-word false = 0

word32-lt : Word32 × Word32 → Word32
word32-lt (a , b) = bool-to-word (a <ᵇ b)

word32-le : Word32 × Word32 → Word32
word32-le (a , b) = bool-to-word (a <ᵇ suc b)

word32-gt : Word32 × Word32 → Word32
word32-gt (a , b) = bool-to-word (b <ᵇ a)

word32-ge : Word32 × Word32 → Word32
word32-ge (a , b) = bool-to-word (b <ᵇ suc a)

word32-eq : Word32 × Word32 → Word32
word32-eq (a , b) = bool-to-word (a ≡ᵇ b)

word32-ne : Word32 × Word32 → Word32
word32-ne (a , b) = bool-to-word (Data.Bool.not (a ≡ᵇ b))

------------------------------------------------------------------------
-- Conversion to/from Mathematical Integers
------------------------------------------------------------------------

word32-from-ℤ : ℤ → Word32
word32-from-ℤ (+ n) = n ℕ.% 2^32
  where open import Data.Nat.DivMod using (_%_)
word32-from-ℤ (-[1+ n ]) = 2^32 ∸ (suc n ℕ.% 2^32)
  where open import Data.Nat.DivMod using (_%_)

word32-to-ℤ : Word32 → ℤ
word32-to-ℤ n = + n

-- Convert Word32 to ℕ (identity since Word32 = ℕ)
word32-to-ℕ : Word32 → ℕ
word32-to-ℕ n = n

-- Convert Word32 to Bool for semantic branching
-- 0 → false, non-zero → true
word32-to-bool : Word32 → Bool
word32-to-bool zero    = false
word32-to-bool (suc _) = true

------------------------------------------------------------------------
-- Word32Interface: MachineInterface for 32-bit backends
------------------------------------------------------------------------

Word32Interface : MachineInterface
Word32Interface = record
  { Word = Word32
  ; word-add = word32-add
  ; word-sub = word32-sub
  ; word-mul = word32-mul
  ; word-div = word32-div
  ; word-mod = word32-mod
  ; word-neg = word32-neg
  ; word-lt = word32-lt
  ; word-le = word32-le
  ; word-gt = word32-gt
  ; word-ge = word32-ge
  ; word-eq = word32-eq
  ; word-ne = word32-ne
  ; word-zero = 0
  ; word-one = 1
  ; word-from-ℤ = word32-from-ℤ
  ; word-to-ℤ = word32-to-ℤ
  ; word-to-ℕ = word32-to-ℕ
  ; word-to-bool = word32-to-bool
  }

------------------------------------------------------------------------
-- Trust Statement
------------------------------------------------------------------------

-- We trust that the above Word32 operations match 32-bit CPU behavior:
--
--   word32-add  ≡  result of: ADD (32-bit, mod 2^32)
--   word32-sub  ≡  result of: SUB (32-bit, mod 2^32)
--   word32-mul  ≡  result of: IMUL (32-bit, low 32 bits)
--   word32-neg  ≡  result of: NEG (32-bit, two's complement)
--   etc.
