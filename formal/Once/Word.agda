-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Word
--
-- Plan 0.23 — the machine integer type for Once's `Int` (D054).
--
-- Once's `Int` means "whatever the CPU's `add` computes": modular
-- arithmetic on a fixed-width machine word, NOT mathematical ℤ. The
-- carrier is ℕ in `[0, modulus)` (CompCert's residue representation —
-- a flat carrier with modular ops, keeping ℕ/ℤ ring algebra available
-- for proofs; no `Fin`/`BitVec` subst tax).
--
-- Wraparound is the *defined* meaning, not an error: `255 ⊕ 1 = 0` at
-- width 8 is correct Once semantics. There is no overflow side
-- condition.
--
-- The arithmetic is parameterised by bit width (`Width`). A top-level
-- Agda module can't take a `ℕ` parameter (the parameter type must be
-- in scope before the module's imports), so width lives on a nested
-- module. `Word64` is the instantiation for the 64-bit targets
-- (x86-64, RISC-V64); a 32-bit instantiation lands when a real
-- x86-32 backend needs it.
--
-- NOTE (D054 residue caveat): since the carrier is ℕ regardless of
-- width, `Width 32 .Word` and `Width 64 .Word` are the *same* Agda
-- type — width is not type-enforced. Mixing widths is a latent error
-- the typechecker won't catch. Type-enforced width would need a
-- wrapper/`Fin`, i.e. the subst tax D054 deliberately avoids.
--
-- Division / remainder (D055, RISC-V total semantics) are NOT defined
-- here yet; they land with the division guard in the bridge phase.
------------------------------------------------------------------------

module Once.Word where

import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc; _∸_; _^_)
open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Integer using (ℤ; +_; -[1+_])

module Width (bits : ℕ) where

  modulus : ℕ
  modulus = 2 ^ bits

  instance
    modulus≢0 : ℕ.NonZero modulus
    modulus≢0 = m^n≢0 2 bits

  -- | A machine word. Represented as ℕ; the modular operations below
  -- maintain the `[0, modulus)` invariant by construction.
  Word : Set
  Word = ℕ

  -- | Reduce a natural into the residue range.
  norm : ℕ → Word
  norm n = n % modulus

  -- | Interpret a ℤ literal as a machine word. Non-negative literals
  -- reduce directly; negative literals take two's complement
  -- (`modulus − |z|`), with an outer `norm` to fold the
  -- `|z| ≡ 0 (mod m)` edge back into range.
  fromℤ : ℤ → Word
  fromℤ (+ n)      = norm n
  fromℤ (-[1+ n ]) = norm (modulus ∸ norm (suc n))

  infixl 6 _⊕_ _⊖_
  infixl 7 _⊗_

  _⊕_ : Word → Word → Word
  x ⊕ y = norm (x ℕ.+ y)

  -- | Modular subtraction via two's complement: `x + (modulus − y)`.
  -- Total and wrapping (`x ⊖ 0 = x`, `0 ⊖ 1 = modulus − 1`).
  _⊖_ : Word → Word → Word
  x ⊖ y = norm (x ℕ.+ (modulus ∸ y))

  _⊗_ : Word → Word → Word
  x ⊗ y = norm (x ℕ.* y)

  -- | Modular negation: `modulus − x` (so `⊝ 0 = 0`, `⊝ 1 = modulus−1`).
  ⊝_ : Word → Word
  ⊝ x = norm (modulus ∸ x)

------------------------------------------------------------------------
-- Standard instantiations
------------------------------------------------------------------------

-- | 64-bit words: x86-64, RISC-V64.
module Word64 = Width 64
