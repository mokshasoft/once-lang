------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (S,S) ASSEMBLED:  n₁ = suc n₁', n₂ = suc m.
--
-- ★ THE ONLY BRANCH WHERE BOTH RECURSOR ARGUMENTS ARE LIVE — the case the
--   whole file exists to reach.  Both are `Def`s from LexSS1/LexSS2, so
--   this module is small.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexSS where

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
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLex
  using ( Γ₅; M1lex; lexAuxMot; lexSS )
open import poc.OCP0009.NbEPDirDBExamplesLexSS1 using ( ⊢lexSSrec1 )
open import poc.OCP0009.NbEPDirDBExamplesLexSS2 using ( ⊢lexSSrec2 )

⊢lexSS : (((((Γ₅ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ Nat) ▹ M1lex) ⊢ lexSS ∷ subTy nrs M1lex
⊢lexSS =
  ⊢lam ty-Nat
    (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var here)) (⊢nsuc (⊢var (there (there (there (there (there here))))))))
      (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there here))) (⊢nsuc (⊢var (there (there (there here))))))
        (⊢app (⊢app (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there here))))
              ⊢lexSSrec1)
              ⊢lexSSrec2)))
