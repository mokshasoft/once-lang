------------------------------------------------------------------------
-- OCP-0009 — BRANCH (0,0), rec₂ UNDER ITS `y` BINDER:
--     `μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`.
--
-- One `⊢lam` (the `le` binder) over LexZZ2b's `Def`.  See LexZZData for
-- why rec₂ is one `⊢lam` per module at the generic carrier.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZZ2a where

open import poc.OCP0009.NbEPDirDBPi
  using ( vz; vs; Nat; var; app )
open import poc.OCP0009.NbEPDirDBType
  using ( _▹_; _⊢_∷_; ⊢var; here; there
        ; ⊢lam; ⊢app; ty-Nat; ty-Hom )
open import poc.OCP0009.NbEPDirDBExamplesLexZZData
  using ( ΓZZ; AZZ; ∋μ₁¹; lexZZrec2in; REC2TZZin )
open import poc.OCP0009.NbEPDirDBExamplesLexZZ2b using ( ⊢lexZZrec2in2 )

⊢lexZZrec2in : (ΓZZ ▹ AZZ) ⊢ lexZZrec2in ∷ REC2TZZin
⊢lexZZrec2in =
  ⊢lam (ty-Hom ty-Nat (⊢app (⊢var ∋μ₁¹) (⊢var here))
                      (⊢app (⊢var ∋μ₁¹) (⊢var (there (there (there here))))))
    ⊢lexZZrec2in2
