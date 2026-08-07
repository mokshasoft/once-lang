------------------------------------------------------------------------
-- OCP-0009 — BRANCH (0,0), rec₂:
--     `(y : A) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`.
--
-- Just the outer `⊢lam` over LexZZ2a's `Def`.  See LexZZData/LexZZ2a for
-- why the peel is needed at all.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZZ2 where

open import poc.OCP0009.NbEPDirDBType
  using ( _⊢_∷_; ⊢var; ⊢lam; ty-El )
open import poc.OCP0009.NbEPDirDBExamplesLexZZData
  using ( ΓZZ; ∋A; lexZZrec2; REC2TZZ )
open import poc.OCP0009.NbEPDirDBExamplesLexZZ2a using ( ⊢lexZZrec2in )

⊢lexZZrec2 : ΓZZ ⊢ lexZZrec2 ∷ REC2TZZ
⊢lexZZrec2 = ⊢lam (ty-El (⊢var ∋A)) ⊢lexZZrec2in
