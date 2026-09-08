------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `𝔹` AS 0/1, AND `∨` AS `max`.
--
--     b2n   : 𝔹 → ℕ
--     b2n-∨ : b2n (a ∨ b) ≡ maxℕ (b2n a) (b2n b)
--
-- ★ WHY: an object-level fold answers a NUMERAL, and `Spec/Variance`'s
--   `occTy`/`occTm` answer a BOOLEAN.  Any agreement between the two
--   needs this bridge, and every MULTI-FIELD row needs the `∨` half —
--   the meta side combines children with `∨`, the fold with
--   `Lib/IOcc`'s `op = max`.
--
-- ★ IT IS FOUR CASES AND NO ARITHMETIC, because `maxℕ a b` is
--   `a + monusℕ b a` (`Lib/NatMaxNum`), which on 0/1 computes to `∨`
--   on the nose.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.BoolNum where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; _∨_ )
open import DirectedHoTT.Lib.NatMaxNum using ( maxℕ )

b2n : 𝔹 → ℕ
b2n true  = suc zero
b2n false = zero

b2n-∨ : (a b : 𝔹) → b2n (a ∨ b) ≡ maxℕ (b2n a) (b2n b)
b2n-∨ true  true  = refl
b2n-∨ true  false = refl
b2n-∨ false true  = refl
b2n-∨ false false = refl
