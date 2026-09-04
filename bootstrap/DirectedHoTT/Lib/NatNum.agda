------------------------------------------------------------------------
-- OCP-0009 · LIB — NUMERALS, AND THE ONE FACT THAT MAKES THEM USEFUL:
-- `plusTm` ON TWO NUMERALS REDUCES TO A NUMERAL.
--
--     num a         = nsucᵃ nzero
--     plus-num a b  : plusTm (num a) (num b) ⟶* num (a + b)
--
-- ★ WHY THIS IS NOT FOLKLORE.  `plusTm m n = natrec n (nsuc (var vz)) m`
--   recurses on `m`, so `plusTm c x` is STUCK on `c` and TRANSPARENT in
--   `x` (see `Lib/Arith`'s header).  On two NUMERALS neither stays
--   stuck, but getting there costs `a` `natrec-suc` steps — this lemma
--   is that induction, done once.
--
-- ⚠ `num` USED TO LIVE IN `Examples/Knot/Sorts`, which is above `Lib`.
--   The lemma belongs next to `plusTm`, so the definition moved down
--   and `Sorts` re-exports it; there is still exactly ONE `num`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.NatNum where
open import normalizer.Syntax.Types using ( _≡_; refl; cong )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; Ren; Sub; renTm; subTm; nzero; nsuc; natrec; var; vz; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢nzero; ⊢nsuc
        ; _⟶*_; done; step; natrec-zero; natrec-suc )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-nsuc )
open import DirectedHoTT.Lib.Nat using ( plusTm )

num : {Γ : Cx} → ℕ → RTm Γ
num zero    = nzero
num (suc n) = nsuc (num n)

⊢num : {Δ : Ctx} (n : ℕ) → Δ ⊢ num n ∷ Nat
⊢num zero    = ⊢nzero
⊢num (suc n) = ⊢nsuc (⊢num n)

-- ★ a numeral is FIXED by every renaming and every substitution.  Two
--   inductions, two lines each, and they absorb an ARBITRARY action —
--   which is what keeps the chains that use them from growing with
--   position.
num-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (n : ℕ) → renTm ρ (num n) ≡ num n
num-ren ρ zero    = refl
num-ren ρ (suc n) = cong nsuc (num-ren ρ n)

num-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (n : ℕ) → subTm σ (num n) ≡ num n
num-sub σ zero    = refl
num-sub σ (suc n) = cong nsuc (num-sub σ n)

------------------------------------------------------------------------
-- ★★★ ADDITION OF NUMERALS.
--
-- ⚠ THE TWO SUBSTITUTIONS IN `natrec-suc` VANISH DEFINITIONALLY HERE,
--   and only because the step body is `nsuc (var vz)`: `extS (single n)`
--   leaves `vz` alone, and `single (natrec …)` then puts the recursive
--   call in its place.  For any other body they would not, and this
--   proof would need `subTm` lemmas rather than `refl`.
------------------------------------------------------------------------

plus-num : {Γ : Cx} (a b : ℕ) → plusTm {Γ} (num a) (num b) ⟶* num (a + b)
plus-num zero    b = step (natrec-zero (num b) (nsuc (var vz))) done
plus-num (suc a) b =
  step (natrec-suc (num b) (nsuc (var vz)) (num a))
       (⟶*-nsuc (plus-num a b))
