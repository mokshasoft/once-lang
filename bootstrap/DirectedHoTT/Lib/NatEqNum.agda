------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ WHAT `eqNatTm` COMPUTES, the `Lib/NatEq`
-- companion in exactly the sense `Lib/NatMaxNum` is `Lib/NatMax`'s.
--
--     monusTm-red : a ⟶* num p → b ⟶* num q →
--                   monusTm a b ⟶* num (monusℕ p q)
--     eqNat-red   : a ⟶* num p → b ⟶* num q →
--                   eqNatTm a b ⟶* num (b2n (eqℕ p q))
--
-- ⚠⚠ WHY IT DID NOT EXIST.  `Lib/NatEq` shipped `⊢eqNat` — a TYPING law
--   — and nothing about the VALUE.  That is the shape the 2026-09-09
--   library audit measured across the whole of `Lib/`: 57 law-carrying
--   parameters, every one of them a typing or stability law, and exactly
--   one semantic law in the tree.  ⇒ `eqNatTm` had a name and no
--   evidence behind it until its first reducing caller appeared.
--
-- ★ THAT CALLER IS `occK`.  `Knot/Occ`'s `occVz` is the one row spliced
--   into the method tuple rather than folded, and its body IS
--   `eqNatTm k (fst p)` — so `Knot/OccAgree`'s `cVar-vz` row cannot be
--   proved without knowing what `eqNatTm` reduces to.
--
-- ⚠⚠ AND IT MUST BE STATED OVER REDUCTIONS, NOT NUMERALS.  A caller has
--   `fst p` after three binders, which only REDUCES to a numeral, and
--   the numeral-only form CANNOT be patched at the call site:
--
--       eqNatTm a b = isZeroTm (maxTm (monusTm a b) (monusTm b a))
--
--   mentions BOTH arguments TWICE, so no single congruence rewrites one
--   of them.  Same duplication `Lib/NatMaxNum.maxTm-red` exists to
--   absorb, one level up.  `eqNat-num` is the `done done` instance.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.NatEqNum where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; natrec-zero; natrec-suc )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-natrecⁿ; ⟶*-natrecᶻ )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.BoolNum using ( b2n )
open import DirectedHoTT.Lib.IFold using ( eqℕ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Lib.Monus using ( monusTm )
open import DirectedHoTT.Lib.NatEq using ( isZeroTm; eqNatTm )
open import DirectedHoTT.Lib.NatMaxNum
  using ( maxℕ; monusℕ; monus-num; maxTm-red; monusℕ-zeroˡ; monusℕ-suc
        ; maxℕ≡max'; max' )

isZeroℕ : ℕ → ℕ
isZeroℕ zero    = suc zero
isZeroℕ (suc _) = zero

-- `isZeroTm n = natrec (num 1) nzero n` — the two ι-rules, nothing else.
isZero-num : {Γ : Cx} (n : ℕ) → isZeroTm {Γ} (num n) ⟶* num (isZeroℕ n)
isZero-num zero    = step (natrec-zero _ _) done
isZero-num (suc k) = step (natrec-suc _ _ _) done

-- ★ `monusTm m n = natrec m (predTm (var vz)) n` — the ZERO branch is
--   `m` and the SCRUTINEE is `n`, so the two arguments reduce through
--   different congruences.
monusTm-red : {Γ : Cx} {a b : RTm Γ} (p q : ℕ) →
              a ⟶* num p → b ⟶* num q →
              monusTm a b ⟶* num (monusℕ p q)
monusTm-red p q ha hb = ⟶*-natrecᶻ ha » ⟶*-natrecⁿ hb » monus-num p q

-- ★★★ THE META-LEVEL FACT `eqNatTm` IS COMPUTING: `a ∸ b` and `b ∸ a`
--   are both zero exactly when `a ≡ b`.
--
-- ⚠ EACH CASE IS A DIFFERENT RECURSION DIRECTION BITING, and they are
--   the three `Lib/NatMaxNum` already isolated: `monusℕ` recurses on its
--   SECOND argument (so `monusℕ zero (suc b)` is stuck — `monusℕ-zeroˡ`),
--   stepping both at once is a lemma (`monusℕ-suc`), and `maxℕ m zero`
--   is real arithmetic rather than a computation (`maxℕ≡max'`).
eqAux : (a b : ℕ) → isZeroℕ (maxℕ (monusℕ a b) (monusℕ b a)) ≡ b2n (eqℕ a b)
eqAux zero    zero    = refl
eqAux zero    (suc b) =
  cong (λ z → isZeroℕ (maxℕ z (suc b))) (monusℕ-zeroˡ (suc b))
eqAux (suc a) zero    =
  trans (cong (λ z → isZeroℕ (maxℕ (suc a) z)) (monusℕ-zeroˡ (suc a)))
        (cong isZeroℕ (maxℕ≡max' (suc a) zero))
eqAux (suc a) (suc b) =
  trans (cong₂ (λ p q → isZeroℕ (maxℕ p q))
               (monusℕ-suc a b) (monusℕ-suc b a))
        (eqAux a b)

-- ★★★ THE FORM CALLERS NEED.
eqNat-red : {Γ : Cx} {a b : RTm Γ} (p q : ℕ) →
            a ⟶* num p → b ⟶* num q →
            eqNatTm a b ⟶* num (b2n (eqℕ p q))
eqNat-red p q ha hb =
  ⟶*-castᵣ (cong num (eqAux p q))
    (⟶*-natrecⁿ (maxTm-red (monusℕ p q) (monusℕ q p)
                           (monusTm-red p q ha hb) (monusTm-red q p hb ha))
     » isZero-num (maxℕ (monusℕ p q) (monusℕ q p)))

eqNat-num : {Γ : Cx} (a b : ℕ) →
            eqNatTm {Γ} (num a) (num b) ⟶* num (b2n (eqℕ a b))
eqNat-num a b = eqNat-red a b done done
