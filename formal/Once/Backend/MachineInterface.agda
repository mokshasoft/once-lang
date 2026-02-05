------------------------------------------------------------------------
-- Once.Backend.MachineInterface
--
-- Interface for machine word operations.
-- All word sizes use ℕ - the difference is in modular arithmetic.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   ⟦ Int ⟧ = ℕ always. No abstract Word type, no ℤ conversions.
--   Different word sizes (64-bit, 32-bit) provide different modular
--   arithmetic operations on ℕ.
--
--   The trust boundary: we trust that Word64Interface.word-add
--   matches the x86 ADD instruction (mod 2^64 arithmetic).
--
-- PORTABILITY:
--   - x86-64, AArch64, RISC-V 64: use Word64Interface (mod 2^64)
--   - x86-32, RISC-V 32: use Word32Interface (mod 2^32)
------------------------------------------------------------------------

module Once.Backend.MachineInterface where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_)

------------------------------------------------------------------------
-- MachineInterface: What a backend must provide for machine words
------------------------------------------------------------------------

record MachineInterface : Set where
  field
    --------------------------------------------------------------------
    -- Integer Arithmetic Operations (modular arithmetic on ℕ)
    --------------------------------------------------------------------

    word-add : ℕ × ℕ → ℕ
    word-sub : ℕ × ℕ → ℕ
    word-mul : ℕ × ℕ → ℕ
    word-div : ℕ × ℕ → ℕ
    word-mod : ℕ × ℕ → ℕ
    word-neg : ℕ → ℕ

    --------------------------------------------------------------------
    -- Comparison Operations (return 1 for true, 0 for false)
    --------------------------------------------------------------------

    word-lt : ℕ × ℕ → ℕ
    word-eq : ℕ × ℕ → ℕ

    --------------------------------------------------------------------
    -- Constants
    --------------------------------------------------------------------

    word-zero : ℕ
    word-one  : ℕ

    --------------------------------------------------------------------
    -- Conversions (for literals)
    --------------------------------------------------------------------

    word-from-ℤ : ℤ → ℕ

open MachineInterface public

------------------------------------------------------------------------
-- Derived operations
------------------------------------------------------------------------

-- Convert word (0/nonzero) to Bool for branching
word-to-bool : ℕ → Bool
word-to-bool 0 = false
word-to-bool _ = true
