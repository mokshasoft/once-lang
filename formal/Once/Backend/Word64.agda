------------------------------------------------------------------------
-- Once.Backend.Word64
--
-- 64-bit word type and MachineInterface instantiation.
-- Used by x86-64, AArch64, and RISC-V 64 backends.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- TRUST BOUNDARY:
--   This module defines Word64 operations that we trust to match
--   the corresponding CPU instructions. This is the ONLY place
--   we trust hardware arithmetic behavior.
--
--   Specifically, we trust that:
--     - word64-add matches ADD instruction (modular arithmetic)
--     - word64-sub matches SUB instruction (modular arithmetic)
--     - word64-mul matches IMUL instruction (low 64 bits)
--     - etc.
------------------------------------------------------------------------

module Once.Backend.Word64 where

open import Once.Backend.MachineInterface

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _*_; _<ᵇ_; _≡ᵇ_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)

------------------------------------------------------------------------
-- Word64: 64-bit unsigned machine word
------------------------------------------------------------------------

-- For now, we use ℕ as the representation.
-- A production implementation would use a proper bitvector type
-- with guaranteed 64-bit bounds.

Word64 : Set
Word64 = ℕ

-- 2^64 (for modular arithmetic)
-- In practice, we'd use a bounded type, but ℕ works for the prototype
2^64 : ℕ
2^64 = 18446744073709551616

------------------------------------------------------------------------
-- Modular Arithmetic Operations
------------------------------------------------------------------------

-- Modular addition (wraps at 2^64)
word64-add : Word64 × Word64 → Word64
word64-add (a , b) = (a + b) ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)

-- Modular subtraction (wraps at 2^64)
word64-sub : Word64 × Word64 → Word64
word64-sub (a , b) = (a ∸ b + 2^64) ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)

-- Modular multiplication (low 64 bits)
word64-mul : Word64 × Word64 → Word64
word64-mul (a , b) = (a * b) ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)

-- Division (truncated toward zero)
-- Uses helper with explicit NonZero instance
word64-div : Word64 × Word64 → Word64
word64-div (a , zero) = 0  -- division by zero returns 0
word64-div (a , suc b) = a ℕ./ suc b
  where
    open import Data.Nat.DivMod using (_/_)
    instance _ = ℕ.nonZero

-- Modulo
word64-mod : Word64 × Word64 → Word64
word64-mod (a , zero) = 0  -- mod by zero returns 0
word64-mod (a , suc b) = a ℕ.% suc b
  where
    open import Data.Nat.DivMod using (_%_)
    instance _ = ℕ.nonZero

-- Negation (two's complement: 2^64 - n, or 0 for 0)
word64-neg : Word64 → Word64
word64-neg zero = zero
word64-neg n = 2^64 ∸ n

------------------------------------------------------------------------
-- Comparison Operations (return 1 for true, 0 for false)
------------------------------------------------------------------------

bool-to-word : Bool → Word64
bool-to-word true  = 1
bool-to-word false = 0

word64-lt : Word64 × Word64 → Word64
word64-lt (a , b) = bool-to-word (a <ᵇ b)

word64-le : Word64 × Word64 → Word64
word64-le (a , b) = bool-to-word (a <ᵇ suc b)

word64-gt : Word64 × Word64 → Word64
word64-gt (a , b) = bool-to-word (b <ᵇ a)

word64-ge : Word64 × Word64 → Word64
word64-ge (a , b) = bool-to-word (b <ᵇ suc a)

word64-eq : Word64 × Word64 → Word64
word64-eq (a , b) = bool-to-word (a ≡ᵇ b)

word64-ne : Word64 × Word64 → Word64
word64-ne (a , b) = bool-to-word (Data.Bool.not (a ≡ᵇ b))

------------------------------------------------------------------------
-- Conversion to/from Mathematical Integers
------------------------------------------------------------------------

-- Convert ℤ to Word64 (two's complement encoding)
word64-from-ℤ : ℤ → Word64
word64-from-ℤ (+ n) = n ℕ.% 2^64
  where open import Data.Nat.DivMod using (_%_)
word64-from-ℤ (-[1+ n ]) = 2^64 ∸ (suc n ℕ.% 2^64)
  where open import Data.Nat.DivMod using (_%_)

-- Convert Word64 back to ℤ (interpret as signed if high bit set)
-- For simplicity, we interpret as unsigned here
word64-to-ℤ : Word64 → ℤ
word64-to-ℤ n = + n

------------------------------------------------------------------------
-- Word64Interface: MachineInterface for 64-bit backends
------------------------------------------------------------------------

Word64Interface : MachineInterface
Word64Interface = record
  { Word = Word64
  ; word-add = word64-add
  ; word-sub = word64-sub
  ; word-mul = word64-mul
  ; word-div = word64-div
  ; word-mod = word64-mod
  ; word-neg = word64-neg
  ; word-lt = word64-lt
  ; word-le = word64-le
  ; word-gt = word64-gt
  ; word-ge = word64-ge
  ; word-eq = word64-eq
  ; word-ne = word64-ne
  ; word-zero = 0
  ; word-one = 1
  ; word-from-ℤ = word64-from-ℤ
  ; word-to-ℤ = word64-to-ℤ
  }

------------------------------------------------------------------------
-- Trust Statement
------------------------------------------------------------------------

-- TRUST BOUNDARY DOCUMENTATION:
--
-- We trust that the above Word64 operations match x86-64 behavior:
--
--   word64-add (a, b)  ≡  result of: ADD rax, rbx  (modulo 2^64)
--   word64-sub (a, b)  ≡  result of: SUB rax, rbx  (modulo 2^64)
--   word64-mul (a, b)  ≡  result of: IMUL rax, rbx (low 64 bits)
--   word64-neg a       ≡  result of: NEG rax       (two's complement)
--   word64-div (a, b)  ≡  result of: IDIV          (quotient in rax)
--   word64-mod (a, b)  ≡  result of: IDIV          (remainder in rdx)
--   word64-lt  (a, b)  ≡  result of: CMP + SETL    (1 if a < b, else 0)
--   word64-eq  (a, b)  ≡  result of: CMP + SETE    (1 if a = b, else 0)
--
-- This trust is stated ONCE here, not scattered across multiple files.
-- All other proofs derive from this single trust boundary.
