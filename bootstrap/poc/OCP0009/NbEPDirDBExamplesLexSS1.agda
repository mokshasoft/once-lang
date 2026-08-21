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
module poc.OCP0009.NbEPDirDBExamplesLexSS1 where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; Unit
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLex using ( REC1T )
open import poc.OCP0009.NbEPDirDBExamplesLexSSData
  using ( ΓSS; lexSSrec1; REC1TSS )

⊢lexSSrec1 : ΓSS ⊢ lexSSrec1 ∷ REC1TSS
⊢lexSSrec1 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var here))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there (there (there here)))))) (⊢app (⊢app (⊢app (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there here)))) (⊢var (there here))) (⊢strong-step (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) (⊢var (there (there (there (there here)))))) (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var here) (⊢var (there (there (there here)))))) (⊢le-refl (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there here))))))
