------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — THE PAIR CARRIER'S LEXREC IH TYPES.
--
-- `NbEPDirDBLibPair` ships the carrier and its descents; this bridges it
-- to `NbEPDirDBLibLexrec` by proving the two recursor types WELL-FORMED
-- at that carrier, at an ARBITRARY pair of bounds.
--
-- ⚠ SEPARATE FROM `LibPair` ON PURPOSE.  `LibPair` is used by AMREC
--   callers too (`NbEPDirDBExamplesGcdLib`), and it must not drag the lexicographic
--   recursor in behind them.  The bridge pays for itself only where both
--   are already wanted.
--
-- ★ D8 IS WHY BOTH ARE "…Tat" FORMS.  `natrec` needs a ℕ, so at a non-ℕ
--   carrier the case split lands on the MEASURE and the IH's bound is the
--   natrec VARIABLE rather than `μ x`.  Both `NbEPDirDBExamplesLexPair` (one split) and
--   `NbEPDirDBExamplesAckLib` (two) need exactly that.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.PairLex where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; RTy; Nat; ⌜Nat⌝ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢nsuc; ⊢⌜Nat⌝
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Rec using ( aIHTat )
open import DirectedHoTT.Lib.Pair using ( PairT; ⊢PairT; msr₁; msr₂; ⊢msr₁; ⊢msr₂ )
open import DirectedHoTT.Negative.Lexrec using ( rec2Tat )

-- rec₁ at an arbitrary μ₁-bound
⊢rec1Tat : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
           Γ ⊢ty aIHTat PairT ⌜Nat⌝ msr₁ b
⊢rec1Tat db =
  ty-Π ⊢PairT (ty-Π (ty-Hom ty-Nat (⊢nsuc ⊢msr₁) (⊢wk db)) (ty-El ⊢⌜Nat⌝))

-- rec₂ at an arbitrary PAIR of bounds — ★ both must be nameable (D8)
⊢rec2Tat : {Γ : Ctx} {b₁ b₂ : RTm ⌊ Γ ⌋} → Γ ⊢ b₁ ∷ Nat → Γ ⊢ b₂ ∷ Nat →
           Γ ⊢ty rec2Tat PairT ⌜Nat⌝ msr₁ msr₂ b₁ b₂
⊢rec2Tat db₁ db₂ =
  ty-Π ⊢PairT
    (ty-Π (ty-Hom ty-Nat ⊢msr₁ (⊢wk db₁))
      (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢wk ⊢msr₂)) (⊢wk (⊢wk db₂)))
            (ty-El ⊢⌜Nat⌝)))
