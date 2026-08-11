-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open ℕ using (ℕ; zero; suc; _∸_; _^_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.DivMod using (_%_; _/_; n%1≡0; n/1≡n; n%n≡0; m<n⇒m%n≡m; m%n<n;
   %-distribˡ-*; m%n%n≡m%n)
open import Data.Nat.Properties using
  (m^n≢0; m^n>0; +-identityʳ; +-comm;
   +-mono-≤; +-monoʳ-≤; +-monoʳ-<; ∸-monoˡ-≤; m+n∸n≡m; m∸n+n≡m; m∸[m∸n]≡n;
   ≤-refl; ≡ᵇ⇒≡; <ᵇ⇒<; ≤⇒≯)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣; sign; _◃_; _-_; -_)
open import Data.Integer.Properties using (_<?_; m-n≡m⊖n; ⊖-<; +◃n≡+n; -◃n≡-n; neg-involutive)
import Data.Sign as Sign
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

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

  ----------------------------------------------------------------------
  -- Power-of-two strength reduction (multiply / divide by `2^j`).
  --
  -- `shlᵂ x j` is the FAITHFUL model of a left shift by `j`: the same
  -- modular value the hardware `shl $j` computes (for an in-range `j`),
  -- `norm (x * 2^j)`. The identity `⊗-pow2` shows a multiply by the
  -- literal `2^j` denotes exactly that shift — a plain modular-distribution
  -- fact, valid at EVERY width (no `bits ≥ 1` hypothesis). The per-arch
  -- Emit renders `shl`/`slli`; `compile-go` fires it only for a positive
  -- power-of-two literal in the in-range window (`j ≤ 30`), so the asm
  -- shift count is always valid.
  --
  -- `sdiv2ᵏ x j` is the truncated signed division by the constant `2^j`
  -- (`x /ˢ fromℤ (+ 2^j)`; for the in-range window `2^j` is a genuine
  -- positive divisor ∉ {0,−1}, so `/ˢ` takes its truncate-toward-zero
  -- branch). The per-arch Emit renders the biased arithmetic-shift-right
  -- sequence (`sar`/`srai`, sign-corrected) — the TRUSTED printer seam,
  -- exactly like `idivq` for `_/ˢ_`.
  ----------------------------------------------------------------------

  shlᵂ : Word → ℕ → Word
  shlᵂ x j = norm (x ℕ.* (2 ^ j))

  sdiv2ᵏ : Word → ℕ → Word
  sdiv2ᵏ x j = x /ˢ fromℤ (+ (2 ^ j))

  -- Multiply by the literal `2^j` ≡ a left shift by `j`. Near-definitional:
  -- `(x * (2^j % m)) % m ≡ (x * 2^j) % m` via `%-distribˡ-*` + `%`-idempotence.
  ⊗-pow2 : ∀ x j → x ⊗ fromℤ (+ (2 ^ j)) ≡ shlᵂ x j
  ⊗-pow2 x j =
    trans (%-distribˡ-* x (2 ^ j % modulus) modulus)
          (trans (cong (λ w → ((x % modulus) ℕ.* w) % modulus)
                       (m%n%n≡m%n (2 ^ j) modulus))
                 (sym (%-distribˡ-* x (2 ^ j) modulus)))

  -- Divide by the literal `2^j` ≡ `sdiv2ᵏ` (definitional).
  /ˢ-pow2 : ∀ x j → x /ˢ fromℤ (+ (2 ^ j)) ≡ sdiv2ᵏ x j
  /ˢ-pow2 x j = refl

  ----------------------------------------------------------------------
  -- Degenerate-divisor identities (division-guard ELISION, Part A).
  --
  -- These justify the sound source-to-source folds that remove the idiv
  -- (and its D055 guard) entirely for a degenerate literal divisor:
  --   x /ˢ 0 = negOne ;  x %ˢ 0 = x ;  x /ˢ negOne = ⊝ x ;  x %ˢ negOne = 0.
  -- The `0` cases are `refl` (they hit the `b ≡ᵇ 0` branch). The `negOne`
  -- cases are real proofs (they need bits ≥ 1, given as `bits ≡ suc b`, and
  -- the dividend in range `x < modulus`).
  ----------------------------------------------------------------------

  -- positivity of the powers of two (no width hypothesis needed)
  0<modulus : 0 < modulus
  0<modulus = m^n>0 2 bits

  0<half : 0 < half
  0<half = m^n>0 2 (bits ∸ 1)

  -- fromℤ of the two degenerate literals
  fromℤ-0 : fromℤ (+ 0) ≡ 0
  fromℤ-0 = m<n⇒m%n≡m 0<modulus

  -- every `fromℤ` lands in range (it ends in `norm`, i.e. `_ % modulus`).
  fromℤ-in-range : ∀ z → fromℤ z < modulus
  fromℤ-in-range (+ n)      = m%n<n n modulus
  fromℤ-in-range (-[1+ n ]) = m%n<n (modulus ∸ norm (suc n)) modulus

  /ˢ-zero : ∀ x → x /ˢ 0 ≡ negOne
  /ˢ-zero x = refl

  %ˢ-zero : ∀ x → x %ˢ 0 ≡ x
  %ˢ-zero x = refl

  -- small Bool helpers
  ≡ᵇ-refl : ∀ n → (n ℕ.≡ᵇ n) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

  ≡ᵇ0-false : ∀ {n} → 0 < n → (n ℕ.≡ᵇ 0) ≡ false
  ≡ᵇ0-false {suc _} _ = refl

  ≤⇒<ᵇfalse : ∀ m n → n ≤ m → (m ℕ.<ᵇ n) ≡ false
  ≤⇒<ᵇfalse m n n≤m with m ℕ.<ᵇ n | <ᵇ⇒< m n
  ... | false | _ = refl
  ... | true  | p = ⊥-elim (≤⇒≯ n≤m (p tt))

  -- `x /ˢ b` with the two guard branches decided away.
  /ˢ-else : ∀ a b → (b ℕ.≡ᵇ 0) ≡ false →
            ((a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne)) ≡ false →
            a /ˢ b ≡ fromℤ (tdivℤ (toℤ a) (toℤ b))
  /ˢ-else a b e1 e2 rewrite e1 | e2 = refl

  /ˢ-mid : ∀ a b → (b ℕ.≡ᵇ 0) ≡ false →
           ((a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne)) ≡ true →
           a /ˢ b ≡ intMin
  /ˢ-mid a b e1 e2 rewrite e1 | e2 = refl

  %ˢ-else : ∀ a b → (b ℕ.≡ᵇ 0) ≡ false →
            ((a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne)) ≡ false →
            a %ˢ b ≡ fromℤ (tmodℤ (toℤ a) (toℤ b))
  %ˢ-else a b e1 e2 rewrite e1 | e2 = refl

  %ˢ-mid : ∀ a b → (b ℕ.≡ᵇ 0) ≡ false →
           ((a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne)) ≡ true →
           a %ˢ b ≡ 0
  %ˢ-mid a b e1 e2 rewrite e1 | e2 = refl

  -- `tdivℤ z (-1) ≡ - z` and `tmodℤ z (-1) ≡ + 0`.
  tdiv-neg1 : ∀ z → tdivℤ z (-[1+ 0 ]) ≡ - z
  tdiv-neg1 (+ n)      = trans (cong (Sign.- ◃_) (n/1≡n n)) (-◃n≡-n n)
  tdiv-neg1 (-[1+ n ]) = trans (cong (Sign.+ ◃_) (n/1≡n (suc n))) (+◃n≡+n (suc n))

  tmod-neg1 : ∀ z → tmodℤ z (-[1+ 0 ]) ≡ + 0
  tmod-neg1 z = cong (sign z ◃_) (n%1≡0 ∣ z ∣)

  -- Facts that need bits ≥ 1 (supplied as `bits ≡ suc b`).
  module _ (b : ℕ) (eqb : bits ≡ suc b) where

    half≡2^b : half ≡ 2 ^ b
    half≡2^b = cong (λ β → 2 ^ (β ∸ 1)) eqb

    2*n≡n+n : ∀ n → 2 ℕ.* n ≡ n ℕ.+ n
    2*n≡n+n n = cong (n ℕ.+_) (+-identityʳ n)

    mod≡half+half : modulus ≡ half ℕ.+ half
    mod≡half+half =
      trans (cong (2 ^_) eqb) (trans (cong (2 ℕ.*_) (sym half≡2^b)) (2*n≡n+n half))

    2≤modulus : 2 ≤ modulus
    2≤modulus = subst (2 ≤_) (sym mod≡half+half) (+-mono-≤ 0<half 0<half)

    0<negOne : 0 < negOne
    0<negOne = ∸-monoˡ-≤ 1 2≤modulus

    negOne≢0 : (negOne ℕ.≡ᵇ 0) ≡ false
    negOne≢0 = ≡ᵇ0-false 0<negOne

    half<modulus : half < modulus
    half<modulus =
      subst (half <_) (sym mod≡half+half)
            (subst (_< half ℕ.+ half) (+-identityʳ half) (+-monoʳ-< half 0<half))

    -- negOne = modulus ∸ 1 is < modulus and modulus ∸ negOne ≡ 1.
    sucNegOne≡mod : suc negOne ≡ modulus
    sucNegOne≡mod = trans (sym (+-comm negOne 1)) (m∸n+n≡m 0<modulus)

    negOne<modulus : negOne < modulus
    negOne<modulus = subst (suc negOne ≤_) sucNegOne≡mod ≤-refl

    modulus∸negOne≡1 : modulus ∸ negOne ≡ 1
    modulus∸negOne≡1 = m∸[m∸n]≡n 0<modulus

    -- ⊝ intMin ≡ intMin  (negation fixes the most-negative word).
    mod∸half≡half : modulus ∸ half ≡ half
    mod∸half≡half = trans (cong (_∸ half) mod≡half+half) (m+n∸n≡m half half)

    ⊝-intMin : ⊝ intMin ≡ intMin
    ⊝-intMin = trans (cong norm mod∸half≡half) (m<n⇒m%n≡m half<modulus)

    -- toℤ negOne ≡ -1.
    half≤negOne : half ≤ negOne
    half≤negOne =
      subst (λ M → half ≤ M ∸ 1) (sym mod≡half+half)
            (∸-monoˡ-≤ 1
              (subst (_≤ half ℕ.+ half) (+-comm half 1) (+-monoʳ-≤ half 0<half)))

    toℤ-negOne : toℤ negOne ≡ -[1+ 0 ]
    toℤ-negOne rewrite ≤⇒<ᵇfalse negOne half half≤negOne =
      trans (m-n≡m⊖n negOne modulus)
            (trans (⊖-< negOne<modulus) (cong (λ w → - (+ w)) modulus∸negOne≡1))

    -- fromℤ (-1) ≡ negOne.
    fromℤ-neg1 : fromℤ (-[1+ 0 ]) ≡ negOne
    fromℤ-neg1 = trans (cong (λ w → norm (modulus ∸ w)) (m<n⇒m%n≡m 2≤modulus))
                       (m<n⇒m%n≡m negOne<modulus)

    -- Roundtrip core: fromℤ (- toℤ x) ≡ ⊝ x for an in-range dividend.
    fromℤ-neg-toℤ : ∀ x → x < modulus → fromℤ (- toℤ x) ≡ ⊝ x
    fromℤ-neg-toℤ x x<mod with x ℕ.<ᵇ half
    fromℤ-neg-toℤ zero     x<mod | true  =
      trans (m<n⇒m%n≡m 0<modulus) (sym (n%n≡0 modulus))
    fromℤ-neg-toℤ (suc x') x<mod | true  =
      cong (λ w → norm (modulus ∸ w)) (m<n⇒m%n≡m x<mod)
    fromℤ-neg-toℤ x        x<mod | false =
      trans (cong (λ z → fromℤ (- z)) toℤ-x-hi)
            (cong fromℤ (neg-involutive (+ (modulus ∸ x))))
      where
        toℤ-x-hi : (+ x) - (+ modulus) ≡ - (+ (modulus ∸ x))
        toℤ-x-hi = trans (m-n≡m⊖n x modulus) (⊖-< x<mod)

    -- %ˢ negOne ≡ 0  (no in-range hypothesis needed).  Decide the guards
    -- (`negOne≢0`, `≡ᵇ-refl negOne`) first, then case the residual `x ≡ᵇ intMin`.
    %ˢ-negOne : ∀ x → x %ˢ negOne ≡ 0
    %ˢ-negOne x rewrite negOne≢0 | ≡ᵇ-refl negOne with x ℕ.≡ᵇ intMin
    ... | true  = refl
    ... | false = trans (cong fromℤ tmod-toℤ-negOne) fromℤ-0
      where
        tmod-toℤ-negOne : tmodℤ (toℤ x) (toℤ negOne) ≡ + 0
        tmod-toℤ-negOne = trans (cong (tmodℤ (toℤ x)) toℤ-negOne) (tmod-neg1 (toℤ x))

    -- /ˢ negOne ≡ ⊝ x  for an in-range dividend.
    /ˢ-negOne : ∀ x → x < modulus → x /ˢ negOne ≡ ⊝ x
    /ˢ-negOne x x<mod rewrite negOne≢0 | ≡ᵇ-refl negOne with x ℕ.≡ᵇ intMin in eqx
    ... | true  = trans (sym ⊝-intMin) (cong ⊝_ (sym x≡intMin))
      where
        x≡intMin : x ≡ intMin
        x≡intMin = ≡ᵇ⇒≡ x intMin (subst T (sym eqx) tt)
    ... | false = trans (cong (λ d → fromℤ (tdivℤ (toℤ x) d)) toℤ-negOne)
                        (trans (cong fromℤ (tdiv-neg1 (toℤ x)))
                               (fromℤ-neg-toℤ x x<mod))

    -- `/ˢ`/`%ˢ` results are in range (used by `eval-in-range`).
    /ˢ-in-range : ∀ a c → (a /ˢ c) < modulus
    /ˢ-in-range a c with c ℕ.≡ᵇ 0
    ... | true  = negOne<modulus
    ... | false with (a ℕ.≡ᵇ intMin) ∧ (c ℕ.≡ᵇ negOne)
    ...   | true  = half<modulus
    ...   | false = fromℤ-in-range (tdivℤ (toℤ a) (toℤ c))

    %ˢ-in-range : ∀ a c → a < modulus → (a %ˢ c) < modulus
    %ˢ-in-range a c a<mod with c ℕ.≡ᵇ 0
    ... | true  = a<mod
    ... | false with (a ℕ.≡ᵇ intMin) ∧ (c ℕ.≡ᵇ negOne)
    ...   | true  = 0<modulus
    ...   | false = fromℤ-in-range (tmodℤ (toℤ a) (toℤ c))

------------------------------------------------------------------------
-- Standard instantiations
------------------------------------------------------------------------

-- | 64-bit words: x86-64, RISC-V64.
module Word64 = Width 64
