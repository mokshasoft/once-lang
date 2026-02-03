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
    -- Properties (optional, for proofs)
    --------------------------------------------------------------------

    -- Round-trip for values in range
    -- word-to-ℤ (word-from-ℤ n) ≡ n  (when n is in representable range)

open MachineInterface public

------------------------------------------------------------------------
-- TrivialMachineInterface: For pure semantics (uses ℤ directly)
------------------------------------------------------------------------

-- For modules that don't need machine-level details,
-- we can use ℤ as the "Word" type. This maintains compatibility
-- with the existing semantic reasoning.

open import Data.Integer as ℤ using (+_; -[1+_])
open import Data.Integer.Properties using ()

open import Relation.Nullary using (yes; no)
open import Data.Integer.Properties using (_≟_; _<?_; _≤?_)
open import Data.Product using (proj₁; proj₂)

private
  pair-add : ℤ × ℤ → ℤ
  pair-add p = proj₁ p ℤ.+ proj₂ p

  pair-sub : ℤ × ℤ → ℤ
  pair-sub p = proj₁ p ℤ.- proj₂ p

  pair-mul : ℤ × ℤ → ℤ
  pair-mul p = proj₁ p ℤ.* proj₂ p

  -- Division and modulo for TrivialMachineInterface
  -- Handle division-by-zero by returning 0
  open import Data.Integer.DivMod as ℤDiv using (_/_; _%_)

  pair-div : ℤ × ℤ → ℤ
  pair-div p with proj₂ p
  ... | + 0 = + 0
  ... | + ℕ.suc n = (proj₁ p) ℤDiv./ (+ ℕ.suc n)
  ... | -[1+ n ] = (proj₁ p) ℤDiv./ -[1+ n ]

  pair-mod : ℤ × ℤ → ℤ
  pair-mod p with proj₂ p
  ... | + 0 = + 0
  ... | + ℕ.suc n = + ((proj₁ p) ℤDiv.% (+ ℕ.suc n))
  ... | -[1+ n ] = + ((proj₁ p) ℤDiv.% -[1+ n ])

  if-lt : ℤ × ℤ → ℤ
  if-lt p with proj₁ p <? proj₂ p
  ... | yes _ = + 1
  ... | no  _ = + 0

  if-le : ℤ × ℤ → ℤ
  if-le p with proj₁ p ≤? proj₂ p
  ... | yes _ = + 1
  ... | no  _ = + 0

  if-gt : ℤ × ℤ → ℤ
  if-gt p with proj₂ p <? proj₁ p
  ... | yes _ = + 1
  ... | no  _ = + 0

  if-ge : ℤ × ℤ → ℤ
  if-ge p with proj₂ p ≤? proj₁ p
  ... | yes _ = + 1
  ... | no  _ = + 0

  if-eq : ℤ × ℤ → ℤ
  if-eq p with proj₁ p ≟ proj₂ p
  ... | yes _ = + 1
  ... | no  _ = + 0

  if-ne : ℤ × ℤ → ℤ
  if-ne p with proj₁ p ≟ proj₂ p
  ... | yes _ = + 0
  ... | no  _ = + 1

TrivialMachineInterface : MachineInterface
TrivialMachineInterface = record
  { Word = ℤ
  ; word-add = pair-add
  ; word-sub = pair-sub
  ; word-mul = pair-mul
  ; word-div = pair-div
  ; word-mod = pair-mod
  ; word-neg = ℤ.-_
  ; word-lt = if-lt
  ; word-le = if-le
  ; word-gt = if-gt
  ; word-ge = if-ge
  ; word-eq = if-eq
  ; word-ne = if-ne
  ; word-zero = + 0
  ; word-one = + 1
  ; word-from-ℤ = λ n → n
  ; word-to-ℤ = λ n → n
  ; word-to-ℕ = ℤ.∣_∣
  }
