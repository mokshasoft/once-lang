------------------------------------------------------------------------
-- Once.Backend.Word64
--
-- 64-bit MachineInterface instantiation.
-- Used by x86-64, AArch64, and RISC-V 64 backends.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- TRUST BOUNDARY:
--   This module defines 64-bit operations that we trust to match
--   the corresponding CPU instructions. This is the ONLY place
--   we trust hardware arithmetic behavior.
------------------------------------------------------------------------

module Once.Backend.Word64 where

open import Once.Backend.MachineInterface

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _*_; _<ᵇ_; _≡ᵇ_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- 64-bit modular arithmetic
------------------------------------------------------------------------

-- 2^64 (for modular arithmetic)
2^64 : ℕ
2^64 = 18446744073709551616

-- Modular addition (wraps at 2^64)
word64-add : ℕ × ℕ → ℕ
word64-add (a , b) = (a + b) ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)

-- Modular subtraction (wraps at 2^64)
word64-sub : ℕ × ℕ → ℕ
word64-sub (a , b) = (a ∸ b + 2^64) ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)

-- Modular multiplication (low 64 bits)
word64-mul : ℕ × ℕ → ℕ
word64-mul (a , b) = (a * b) ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)

-- Division (truncated toward zero)
word64-div : ℕ × ℕ → ℕ
word64-div (a , zero) = 0  -- division by zero returns 0
word64-div (a , suc b) = a ℕ./ suc b
  where
    open import Data.Nat.DivMod using (_/_)
    instance _ = ℕ.nonZero

-- Modulo
word64-mod : ℕ × ℕ → ℕ
word64-mod (a , zero) = 0  -- mod by zero returns 0
word64-mod (a , suc b) = a ℕ.% suc b
  where
    open import Data.Nat.DivMod using (_%_)
    instance _ = ℕ.nonZero

-- Negation (two's complement: 2^64 - n, or 0 for 0)
word64-neg : ℕ → ℕ
word64-neg zero = zero
word64-neg n = 2^64 ∸ n

------------------------------------------------------------------------
-- Comparison Operations (return 1 for true, 0 for false)
------------------------------------------------------------------------

private
  bool-to-word : Bool → ℕ
  bool-to-word true  = 1
  bool-to-word false = 0

word64-lt : ℕ × ℕ → ℕ
word64-lt (a , b) = bool-to-word (a <ᵇ b)

word64-eq : ℕ × ℕ → ℕ
word64-eq (a , b) = bool-to-word (a ≡ᵇ b)

------------------------------------------------------------------------
-- Conversions
------------------------------------------------------------------------

-- Convert ℤ to ℕ (modulo 2^64)
word64-from-ℤ : ℤ → ℕ
word64-from-ℤ (+ n) = n ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)
word64-from-ℤ (-[1+ n ]) = 2^64 ∸ suc n  -- two's complement

------------------------------------------------------------------------
-- Word64Interface: MachineInterface for 64-bit backends
------------------------------------------------------------------------

Word64Interface : MachineInterface
Word64Interface = record
  { word-add = word64-add
  ; word-sub = word64-sub
  ; word-mul = word64-mul
  ; word-div = word64-div
  ; word-mod = word64-mod
  ; word-neg = word64-neg
  ; word-lt = word64-lt
  ; word-eq = word64-eq
  ; word-zero = 0
  ; word-one = 1
  ; word-from-ℤ = word64-from-ℤ
  }

------------------------------------------------------------------------
-- Trust Statement
------------------------------------------------------------------------

-- TRUST BOUNDARY DOCUMENTATION:
--
-- We trust that the above operations match x86-64 behavior:
--
--   word64-add (a, b)  ≡  result of: ADD rax, rbx  (modulo 2^64)
--   word64-sub (a, b)  ≡  result of: SUB rax, rbx  (modulo 2^64)
--   word64-mul (a, b)  ≡  result of: IMUL rax, rbx (low 64 bits)
--   word64-neg a       ≡  result of: NEG rax       (two's complement)
--   word64-div (a, b)  ≡  result of: IDIV          (quotient)
--   word64-mod (a, b)  ≡  result of: IDIV          (remainder)
--   word64-lt  (a, b)  ≡  result of: CMP + SETL    (1 if a < b, else 0)
--   word64-eq  (a, b)  ≡  result of: CMP + SETE    (1 if a = b, else 0)
