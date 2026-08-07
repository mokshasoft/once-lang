------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (0,0) ASSEMBLED:  n₁ = 0, n₂ = 0.
--
-- BOTH obligations are vacuous at (0,0): `rec₁` gets μ₁ y < μ₁ x ≤ 0 and
-- `rec₂` gets μ₂ y < μ₂ x ≤ 0, so each is `ordtr` into `⊢strong-base'`.
--
-- ⚠ WHY FIVE MODULES.  Not taste — RAM, and much more of it than at the ℕ
--   carrier, where this whole branch was ONE 39s / 2.1 GB module.  See
--   LexZZData for the measurements and the peel recipe.  Three `⊢lam`s and
--   a three-fold `⊢app` spine are all that is left here; both recursor
--   arguments arrive as `Def`s, so this module is small.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZZ where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBExamplesLex
  using ( Γ₅; M0lex; lexZZ )
open import poc.OCP0009.NbEPDirDBExamplesLexZZ1 using ( ⊢lexZZrec1 )
open import poc.OCP0009.NbEPDirDBExamplesLexZZ2 using ( ⊢lexZZrec2 )

⊢lexZZ : (Γ₅ ▹ Nat) ⊢ lexZZ ∷ subTy (single nzero) M0lex
⊢lexZZ =
  ⊢lam (ty-El (⊢var (there (there (there (there (there here)))))))
    (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there here))))) (⊢var (here))) ⊢nzero)
      (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there here))))) (⊢var (there here))) ⊢nzero)
        (⊢app (⊢app (⊢app (⊢var (there (there (there (there here))))) (⊢var (there (there here))))
              ⊢lexZZrec1)
              ⊢lexZZrec2)))
