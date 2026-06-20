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
-- Division / remainder (D055, RISC-V total semantics) and signed
-- comparisons (D054) are defined below: division is TOTAL (a/0 = -1,
-- a%0 = a, INT_MIN/-1 = INT_MIN, INT_MIN%-1 = 0) and comparisons are
-- SIGNED (two's complement). No trap, no side condition.
------------------------------------------------------------------------

module Once.Word where

import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc; _∸_; _^_)
open import Data.Nat.DivMod using (_%_; _/_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣; sign; _◃_; _-_)
open import Data.Integer.Properties using (_<?_)
import Data.Sign as Sign
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Relation.Nullary using (does)

-- | The machine-word carrier, SHARED BY ALL WIDTHS (D054 residue
-- representation): a value in `[0, 2^bits)`, represented as ℕ. The
-- bounding width is an OPERATIONAL parameter — it lives in `Width bits`
-- (the modular ops) and is threaded from the target architecture (D059,
-- "width threaded from the architecture, never hard-coded"), NEVER baked
-- into the carrier type. So the value-level denotation of `Int` is this
-- width-agnostic carrier (`⟦ Int ⟧ = Carrier`), not `Word64.Word` (which
-- would hard-code 64) and not bare `ℕ` (which would promise unbounded
-- arithmetic). `ℕ` here is only the residue representation, never the
-- promise — CompCert's model.
Carrier : Set
Carrier = ℕ

module Width (bits : ℕ) where

  modulus : ℕ
  modulus = 2 ^ bits

  instance
    modulus≢0 : ℕ.NonZero modulus
    modulus≢0 = m^n≢0 2 bits

  -- | A machine word at this width. Definitionally the shared,
  -- width-agnostic `Carrier`; `bits` drives only the modular operations
  -- below (which maintain the `[0, modulus)` invariant), NOT the type.
  Word : Set
  Word = Carrier

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

  ----------------------------------------------------------------------
  -- Signed view (D054: `Int` is SIGNED — two's complement).
  ----------------------------------------------------------------------

  -- | `2^(bits−1)` — the most-negative word `intMin` (signed −2^(bits−1)).
  half : ℕ
  half = 2 ^ (bits ∸ 1)

  -- | Signed interpretation: `[0, half)` is non-negative; `[half, modulus)`
  -- is negative (value − modulus). Two's complement.
  toℤ : Word → ℤ
  toℤ w = if w ℕ.<ᵇ half then + w else (+ w) - (+ modulus)

  intMin : Word           -- signed −2^(bits−1)
  intMin = half

  negOne : Word           -- all-ones; signed −1
  negOne = modulus ∸ 1

  ----------------------------------------------------------------------
  -- Signed comparisons (D054). Bool-valued; the SigOp layer maps Bool to
  -- the `Unit + Unit` comparison codomain.
  ----------------------------------------------------------------------

  infix 4 _<ˢ_ _≡ʷ_

  _<ˢ_ : Word → Word → Bool          -- signed less-than
  x <ˢ y = does (toℤ x <? toℤ y)

  _≡ʷ_ : Word → Word → Bool          -- bit-equality (sign-agnostic)
  x ≡ʷ y = x ℕ.≡ᵇ y

  ----------------------------------------------------------------------
  -- Total signed division / remainder (D055, RISC-V — NO trap):
  --   a / 0 = −1 ;  a % 0 = a ;  INT_MIN / −1 = INT_MIN ;  INT_MIN % −1 = 0 ;
  -- otherwise truncated-toward-zero signed division.
  ----------------------------------------------------------------------

  private
    -- total ℕ div/mod (zero divisor returns a dummy; guarded away below)
    _divℕ_ _modℕ_ : ℕ → ℕ → ℕ
    n divℕ zero    = zero
    n divℕ (suc d) = n / suc d
    n modℕ zero    = n
    n modℕ (suc d) = n % suc d

    -- truncated-toward-zero signed div/mod on ℤ (divisor ≠ 0 by guard)
    tdivℤ tmodℤ : ℤ → ℤ → ℤ
    tdivℤ a b = (sign a Sign.* sign b) ◃ (∣ a ∣ divℕ ∣ b ∣)
    tmodℤ a b = sign a ◃ (∣ a ∣ modℕ ∣ b ∣)

  infixl 7 _/ˢ_ _%ˢ_

  _/ˢ_ : Word → Word → Word
  a /ˢ b = if b ℕ.≡ᵇ 0 then negOne
           else if (a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne) then intMin
           else fromℤ (tdivℤ (toℤ a) (toℤ b))

  _%ˢ_ : Word → Word → Word
  a %ˢ b = if b ℕ.≡ᵇ 0 then a
           else if (a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne) then 0
           else fromℤ (tmodℤ (toℤ a) (toℤ b))

------------------------------------------------------------------------
-- Standard instantiations
------------------------------------------------------------------------

-- | 64-bit words: x86-64, RISC-V64.
module Word64 = Width 64
