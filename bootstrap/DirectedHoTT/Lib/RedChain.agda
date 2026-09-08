------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `_»_`, THE REDUCTION CHAIN, DEFINED ONCE.
--
--     p » q  =  ⟶*-trans p q
--
-- ★★★ FIFTEEN MODULES HAD THIS, AND FOURTEEN OF THEM RE-IMPLEMENTED IT.
--   Only `Knot/SzAgree` wrote `_»_ = ⟶*-trans`; the other fourteen spelled
--   out the two clauses again, verbatim against `Metatheory/RedCong`:
--
--       done       » q = q
--       (step r p) » q = step r (p » q)
--
--   Same fixity (`infixr 5`) and same type in all fifteen, so this is a
--   pure duplication of a KERNEL function, not fifteen deliberate local
--   conventions.
--
-- ★ THE NOTATION IS WORTH KEEPING, WHICH IS WHY THIS MODULE EXISTS AT ALL
--   RATHER THAN THE CALL SITES MOVING TO `⟶*-trans`.  These proofs ARE
--   chains of reduction steps — `a » b » c` reads as the sequence a row
--   performs, where nested `⟶*-trans` calls hide it.  The redundancy was
--   the fourteen re-implementations, never the operator.
--
-- ⚠ AND IT LIVES IN `Lib/`, NOT IN `Metatheory/RedCong` BESIDE
--   `⟶*-trans`.  The kernel states the LEMMA; convenience notation for
--   its clients is not kernel content, and `Spec/`+`Metatheory/` are the
--   two trees `tools/check-trust.sh` keeps free of everything else.
--   Adding sugar there would not break the invariant, but it would blur
--   what the invariant is protecting.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.RedChain where

open import DirectedHoTT.Spec.Syntax using ( Cx; RTm )
open import DirectedHoTT.Spec.Typing using ( _⟶*_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
_»_ = ⟶*-trans
