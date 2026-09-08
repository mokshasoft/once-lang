------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `max` ON NUMERALS, the `maxTm` companion to
-- `Lib/NatNum.plus-num`.
--
--     plus-num  : plusTm  (num a) (num b) ⟶* num (a + b)        (NatNum)
--     monus-num : monusTm (num a) (num b) ⟶* num (monusℕ a b)   ← here
--     max-num   : maxTm   (num a) (num b) ⟶* num (maxℕ a b)     ← here
--
-- ★ WHY IT EXISTS: `occK`'s fold runs at `nd = id`, `op = max`
--   (`Lib/IOcc`), so the `occ` analogue of `Lib/ISzRed.szsStep-red`
--   needs `max` on numerals exactly as `sz`'s needs `plus-num`.  Nothing
--   in the tree had it, and `Lib/NatMax` carried only `maxTm` and `⊢max`.
--
-- ★ IT IS CHEAP because `Lib/Monus` already proves the object-level
--   reduction steps (`pred-zero`, `pred-suc`, `monus-zero`, `monus-suc`),
--   so these are inductions on the NUMERAL, not on the reduction.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.NatMaxNum where

open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; nzero; nsuc )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-natrecᶻ; ⟶*-natrecⁿ )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.NatNum using ( num; plus-num )
open import DirectedHoTT.Lib.Monus
  using ( predTm; monusTm; pred-zero; pred-suc; monus-zero; monus-suc )
open import DirectedHoTT.Lib.ArithMonus using ( pred* )
open import DirectedHoTT.Lib.NatMax using ( maxTm )

-- ★ `pred` on ℕ, written out: `Agda.Builtin.Nat` has no `pred`.
predℕ : ℕ → ℕ
predℕ zero    = zero
predℕ (suc n) = n

pred-num : {Γ : Cx} (n : ℕ) → predTm {Γ} (num n) ⟶* num (predℕ n)
pred-num zero    = pred-zero
pred-num (suc n) = pred-suc (num n)

-- ⚠ `monusℕ` IS DEFINED TO MATCH `monusTm`, NOT REUSED FROM
--   `Agda.Builtin.Nat._-_`.  Builtin `_-_` recurses on its FIRST
--   argument, `monusTm m n = natrec m (predTm (var vz)) n` on its
--   SECOND, so `predℕ (a - b)` and `a - suc b` are propositionally but
--   NOT definitionally equal — reusing `_-_` costs a bridging lemma at
--   every step.  Matching the object-level recursion makes `monus-num`
--   definitional instead.
monusℕ : ℕ → ℕ → ℕ
monusℕ a zero    = a
monusℕ a (suc b) = predℕ (monusℕ a b)

monus-num : {Γ : Cx} (a b : ℕ) → monusTm {Γ} (num a) (num b) ⟶* num (monusℕ a b)
monus-num a zero    = monus-zero (num a)
monus-num a (suc b) =
  monus-suc (num a) (num b) » pred* (monus-num a b) » pred-num (monusℕ a b)

-- ★ `max a b = a + (b ∸ a)` — which is what `maxTm a b = plusTm a
--   (monusTm b a)` computes, so the ℕ side is written the same way
--   rather than via a separate `⊔` that would need its own agreement.
maxℕ : ℕ → ℕ → ℕ
maxℕ a b = a + monusℕ b a

max-num : {Γ : Cx} (a b : ℕ) → maxTm {Γ} (num a) (num b) ⟶* num (maxℕ a b)
max-num a b = ⟶*-natrecᶻ (monus-num b a) » plus-num a (monusℕ b a)

maxTm-red : {Γ : Cx} {a b : RTm Γ} (p q : ℕ) →
            a ⟶* num p → b ⟶* num q →
            maxTm a b ⟶* num (maxℕ p q)
maxTm-red p q ha hb =
  ⟶*-natrecᶻ (⟶*-natrecᶻ hb) »   -- `b`: the inner monus's zero branch
  ⟶*-natrecⁿ ha »                -- `a`: the outer plus's scrutinee
  ⟶*-natrecᶻ (⟶*-natrecⁿ ha) »   -- `a` AGAIN: the inner monus's scrutinee
  max-num p q
