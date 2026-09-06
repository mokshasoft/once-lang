------------------------------------------------------------------------
-- OCP-0009 · LIB — `depth` = `Lib/IFold` AT THE MAX ALGEBRA.
--
--     z = 0    op = max    nd = suc
--
-- ★★ THE POINT OF THIS FILE IS THAT IT IS FOUR LINES.  `Lib/IFold` was
--   generalised out of `Lib/ISz` on the claim that a second algebra would
--   then be free; this is that claim discharged, and `depth` differs from
--   `sz` in exactly one parameter.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IDepth where
open import DirectedHoTT.Spec.Syntax using ( nzero; nsuc; Nat )
open import DirectedHoTT.Spec.Typing using ( ⊢nzero; ⊢nsuc; ty-Nat )
open import normalizer.Syntax.Types using ( refl )
open import DirectedHoTT.Lib.NatMax using ( maxTm; ⊢max )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true )
import DirectedHoTT.Lib.IFold as IF

-- ★ the THIRD instantiation — `Lib/IFold` at `Nat` with `op = max`.
open IF.Fold 𝔹 (λ _ → true) (λ b _ → b)
             Nat ty-Nat refl refl
             nzero maxTm nsuc ⊢nzero ⊢max ⊢nsuc public
  renaming ( ifTail   to dpTail   ; ⊢ifTail   to ⊢dpTail
           ; ifSum    to dpSum    ; ⊢ifSum    to ⊢dpSum
           ; ifMethod to dpMethod ; ⊢ifMethod to ⊢dpMethod
           ; ifMeths  to dpMeths  ; ⊢ifMeths  to ⊢dpMeths )
