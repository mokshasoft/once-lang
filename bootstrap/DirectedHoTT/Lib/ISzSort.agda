------------------------------------------------------------------------
-- OCP-0009 · LIB — `szs` = `Lib/IFold` AT THE SUM ALGEBRA, COUNTING
-- **SAME-SORT** CHILDREN ONLY.
--
--     z = 0    op = +    nd = suc        (the algebra, as in `Lib/ISz`)
--     R = Maybeℕ    rsum = rowSort    pick = sameSortAt
--
-- ★★★ WHY THIS FILE EXISTS.  `Lib/ISz` is the honest size of a term in
--   the ENCODED syntax: the knot is one `IMu` over seven sorts, so its
--   fold descends into all of them and counts every child.
--   `Metatheory/Canonicity`'s `szb` is a function on `RTm` and the other
--   six sorts are separate Agda types, so it treats them as ATOMS.  Two
--   different measures, both correct.
--
--   But the agreement the judgement layer needs,
--
--       szTm ⌈ t ⌉ ⟶* ⌜ sz t ⌝
--
--   is between the ENCODED measure and the META-LEVEL one — so they
--   have to be the SAME measure.  ⚠ Measured: on all 53 rows the gap is
--   exactly the cross-sort children, and `Examples/Knot/SzProbe` checks
--   in Agda that "count same-sort" reproduces `szb` on all eleven `RTm`
--   rows.  This instance is that measure.
--
-- ⚠ THE COUNTERPART OF `Lib/ISz`, NOT A REPLACEMENT.  `Lib/ISz` stays
--   the measure for anything whose recursion is over the encoded term —
--   `Lib/IDepth` likewise.  Use THIS one only where the claim is about
--   agreement with a meta-level function on one sort.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.ISzSort where
open import DirectedHoTT.Spec.Syntax using ( nzero; nsuc )
open import DirectedHoTT.Spec.Typing using ( ⊢nzero; ⊢nsuc )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
import DirectedHoTT.Lib.IFold as IF
open IF using ( Maybeℕ; rowSort; sameSortAt )

open IF.Fold Maybeℕ rowSort sameSortAt nzero plusTm nsuc ⊢nzero ⊢plus ⊢nsuc public
  renaming ( ifTail   to szsTail   ; ⊢ifTail   to ⊢szsTail
           ; ifSum    to szsSum    ; ⊢ifSum    to ⊢szsSum
           ; ifMethod to szsMethod ; ⊢ifMethod to ⊢szsMethod
           ; ifMeths  to szsMeths  ; ⊢ifMeths  to ⊢szsMeths
           ; ifMeths-sel to szsMeths-sel )
