------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (S,S) ASSEMBLED:  n₁ = suc n₁', n₂ = suc m.
--
-- ★ THE ONLY BRANCH WHERE BOTH RECURSOR ARGUMENTS ARE LIVE — the case the
--   whole file exists to reach.  Both are `Def`s from LexSS1/LexSS2, so
--   this module is small.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexSS where
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
open import DirectedHoTT.Negative.Lex
  using ( Γ₅; M1lex; LStepT; lexAuxMot; lexSS )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Negative.LexSS1 using ( ⊢lexSSrec1 )
open import DirectedHoTT.Negative.LexSS2 using ( ⊢lexSSrec2 )

⊢lexSS : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
         (((((Γ₅ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ Nat) ▹ M1lex) ⊢ lexSS stpTm ∷ subTy nrs M1lex
⊢lexSS stpTm dstp =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there here)))))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here)) (⊢nsuc (⊢var (there (there (there (there (there here)))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there here))) (⊢nsuc (⊢var (there (there (there here)))))) (⊢app (⊢app (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dstp))))))))) (⊢var (there (there here)))) ⊢lexSSrec1) ⊢lexSSrec2)))
