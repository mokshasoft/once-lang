------------------------------------------------------------------------
-- BRANCH (S,S), rec₁ — THE OUTER DESCENT.
--
-- Calls the OUTER IH (`lexAuxMot` variable, vs⁸) with FOUR arguments:
--   n₂ := μ₂ y   the RESET — dropping n₁ buys an arbitrary n₂;
--   x  := y
--   μ₁ y ≤ n₁'   by `⊢strong-step` — n₁ STRICTLY DOWN;
--   μ₂ y ≤ μ₂ y  by `⊢le-refl`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexSS1 where
open import normalizer.Syntax.Types using ( refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; Unit
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import DirectedHoTT.Lib.Strong using ( ⊢le-refl; reflTm )
open import DirectedHoTT.Lib.Ord
  using ( ⊢strong-base'; ⊢strong-step )
open import DirectedHoTT.Negative.Lex using ( REC1T )
open import DirectedHoTT.Negative.LexSSData
  using ( ΓSS; lexSSrec1; REC1TSS )

⊢lexSSrec1 : ΓSS ⊢ lexSSrec1 ∷ REC1TSS
⊢lexSSrec1 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢var (here refl)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢var (there (there (there (here refl) refl) refl) refl)))) (⊢app (⊢app (⊢app (⊢app (⊢var (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢var (there (here refl) refl)))) (⊢var (there (here refl) refl))) (⊢strong-step (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢var (there (here refl) refl))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢var (there (there (there (there (here refl) refl) refl) refl) refl))) (⊢var (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢var (here refl)) (⊢var (there (there (there (here refl) refl) refl) refl)))) (⊢le-refl (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (here refl) refl) refl) refl) refl) refl) refl) refl) refl) refl) refl)) (⊢var (there (here refl) refl))))))
