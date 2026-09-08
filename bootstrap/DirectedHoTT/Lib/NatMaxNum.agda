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
open import normalizer.Syntax.Types using ( _≡_; refl; cong; trans; sym )

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


------------------------------------------------------------------------
-- ★★★ `maxℕ`'s ALGEBRAIC LAWS — it had none, and `occK` needs one.
--
-- ⚠ WHY: `Spec/Variance._∨_` is `infixr 5`, so a row with three children
--   nests its META side RIGHT — `A ∨ (t ∨ u)` — while
--   `Lib/IOccRed.AllIH` accumulates LEFT: `maxℕ (maxℕ A t) u`.  THIRTEEN
--   of `occK`'s 53 rows have three or more recursive fields
--   (`cTm-ordtr` has five), and every one of them needs associativity.
--
-- ★ NOT PROVED DIRECTLY ON `maxℕ a b = a + monusℕ b a`, which is real
--   arithmetic.  Via a case-defined `max'`: it associates by a
--   three-case induction with no `+`/`∸`, and the bridge `maxℕ ≡ max'`
--   is where the three non-definitional steps are paid, once.
--
-- ⚠ THOSE THREE STEPS ARE THE WHOLE CONTENT, and each is a different
--   recursion direction biting:
--     `_+_`    recurses on its FIRST  argument ⇒ `a + zero` is stuck
--     `monusℕ` recurses on its SECOND argument ⇒ `monusℕ zero (suc n)`
--       is stuck, and so is stepping BOTH arguments down at once
------------------------------------------------------------------------
max' : ℕ → ℕ → ℕ
max' zero    b       = b
max' (suc a) zero    = suc a
max' (suc a) (suc b) = suc (max' a b)

max'-assoc : (a b c : ℕ) → max' (max' a b) c ≡ max' a (max' b c)
max'-assoc zero    b       c       = refl
max'-assoc (suc a) zero    c       = refl
max'-assoc (suc a) (suc b) zero    = refl
max'-assoc (suc a) (suc b) (suc c) = cong suc (max'-assoc a b c)

-- ⚠ TWO STEPS THAT ARE NOT DEFINITIONAL, and both bite at `b = zero`:
--   `_+_` recurses on its FIRST argument so `a + zero` is stuck, and
--   `monusℕ` on its SECOND so `monusℕ zero (suc n)` is stuck.
+-zeroʳ : (a : ℕ) → (a + zero) ≡ a
+-zeroʳ zero    = refl
+-zeroʳ (suc a) = cong suc (+-zeroʳ a)

monusℕ-zeroˡ : (n : ℕ) → monusℕ zero n ≡ zero
monusℕ-zeroˡ zero    = refl
monusℕ-zeroˡ (suc n) = cong predℕ (monusℕ-zeroˡ n)

-- ⚠ AND A THIRD: `monusℕ` recurses on its SECOND argument, so stepping
--   BOTH down at once is a lemma, not a computation.
monusℕ-suc : (a b : ℕ) → monusℕ (suc a) (suc b) ≡ monusℕ a b
monusℕ-suc a zero    = refl
monusℕ-suc a (suc b) = cong predℕ (monusℕ-suc a b)

-- ★ the bridge: `maxℕ a b = a + monusℕ b a` computes to `max'`.
maxℕ≡max' : (a b : ℕ) → maxℕ a b ≡ max' a b
maxℕ≡max' zero    b       = refl
maxℕ≡max' (suc a) zero    =
  trans (cong (λ z → suc a + z) (monusℕ-zeroˡ (suc a)))
        (+-zeroʳ (suc a))
maxℕ≡max' (suc a) (suc b) =
  cong suc (trans (cong (λ z → a + z) (monusℕ-suc b a))
                  (maxℕ≡max' a b))

------------------------------------------------------------------------
-- ★★★ WHAT THE 13 ROWS NEED.  `_∨_` is `infixr 5` so a three-child row's
--   META side nests RIGHT, while `Lib/IOccRed.AllIH` accumulates LEFT.
------------------------------------------------------------------------
maxℕ-assoc : (a b c : ℕ) → maxℕ (maxℕ a b) c ≡ maxℕ a (maxℕ b c)
maxℕ-assoc a b c =
  trans (maxℕ≡max' (maxℕ a b) c)
  (trans (cong (λ z → max' z c) (maxℕ≡max' a b))
  (trans (max'-assoc a b c)
  (trans (sym (cong (max' a) (maxℕ≡max' b c)))
         (sym (maxℕ≡max' a (maxℕ b c))))))
