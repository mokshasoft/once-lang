------------------------------------------------------------------------
-- Once.Backend.MachineInterface
--
-- Parameterized interface for machine word types and operations.
-- Each backend instantiates this with its word size (32-bit, 64-bit).
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   This interface eliminates the "encode gap" between mathematical
--   integers (ℤ) and machine words. Instead of:
--
--     ⟦ Int ⟧ = ℤ  and  postulate encode-add : encode a + encode b ≡ encode (a + b)
--
--   We have:
--
--     ⟦ Int ⟧ = Word  and  word-add IS the semantic operation
--
--   The trust boundary moves to the MachineInterface instantiation:
--   we trust that Word64Interface.word-add matches the x86 ADD instruction.
--
-- PORTABILITY:
--   - x86-64, AArch64, RISC-V 64: use Word64Interface
--   - x86-32, RISC-V 32: use Word32Interface
--   - The IR and proofs are parameterized, working across all backends
------------------------------------------------------------------------

module Once.Backend.MachineInterface where

open import Data.Bool using (Bool; true; false)
open import Data.Integer as ℤ using (ℤ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Level using (Level; _⊔_)

------------------------------------------------------------------------
-- MachineInterface: What a backend must provide for machine words
------------------------------------------------------------------------

record MachineInterface : Set₁ where
  field
    -- The machine word type (e.g., Word64, Word32)
    Word : Set

    --------------------------------------------------------------------
    -- Integer Arithmetic Operations
    -- These ARE the semantics - no encode gap!
    --------------------------------------------------------------------

    word-add : Word × Word → Word
    word-sub : Word × Word → Word
    word-mul : Word × Word → Word
    word-div : Word × Word → Word
    word-mod : Word × Word → Word
    word-neg : Word → Word

    --------------------------------------------------------------------
    -- Comparison Operations (return 1 for true, 0 for false)
    --------------------------------------------------------------------

    word-lt : Word × Word → Word
    word-le : Word × Word → Word
    word-gt : Word × Word → Word
    word-ge : Word × Word → Word
    word-eq : Word × Word → Word
    word-ne : Word × Word → Word

    --------------------------------------------------------------------
    -- Constants
    --------------------------------------------------------------------

    word-zero : Word
    word-one  : Word

    -- Load a mathematical integer as a word (with truncation/overflow)
    word-from-ℤ : ℤ → Word

    -- Convert word back to mathematical integer (for observing results)
    word-to-ℤ : Word → ℤ

    -- Convert word to natural number (for memory encoding)
    -- This is identity for Word64/Word32 where Word = ℕ
    word-to-ℕ : Word → ℕ

    --------------------------------------------------------------------
    -- Branching support
    --------------------------------------------------------------------

    -- Convert word to Bool for semantic branching
    -- 0 → false, non-zero → true
    -- This bridges machine comparison results (Word) to Agda decisions
    word-to-bool : Word → Bool

    --------------------------------------------------------------------
    -- Properties (optional, for proofs)
    --------------------------------------------------------------------

    -- Round-trip for values in range
    -- word-to-ℤ (word-from-ℤ n) ≡ n  (when n is in representable range)

open MachineInterface public
