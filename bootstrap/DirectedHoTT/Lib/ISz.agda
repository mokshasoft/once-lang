------------------------------------------------------------------------
-- OCP-0009 · LIB — `sz` = `Lib/IFold` AT THE SUM ALGEBRA.
--
--     z = 0    op = +    nd = suc
--
-- i.e. a node's size is ONE MORE than the sum of its children's, and a
-- constructor with no recursive fields has size 1.  Everything of
-- substance is in `Lib/IFold`; this file only picks the algebra.
--
-- ⚠ THE FOLD NOW EMITS NO TRAILING `+ 0` — see `IFold`'s header for why
--   that is a complexity fact and not a tidiness one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.ISz where
open import DirectedHoTT.Spec.Syntax using ( nzero; nsuc )
open import DirectedHoTT.Spec.Typing using ( ⊢nzero; ⊢nsuc )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true )
import DirectedHoTT.Lib.IFold as IF

open IF.Fold 𝔹 (λ _ → true) (λ b _ → b) nzero plusTm nsuc ⊢nzero ⊢plus ⊢nsuc public
  renaming ( ifTail   to szTail   ; ⊢ifTail   to ⊢szTail
           ; ifSum    to szSum    ; ⊢ifSum    to ⊢szSum
           ; ifMethod to szMethod ; ⊢ifMethod to ⊢szMethod
           ; ifMeths  to szMeths  ; ⊢ifMeths  to ⊢szMeths
           ; ifMeths-sel to szMeths-sel )
