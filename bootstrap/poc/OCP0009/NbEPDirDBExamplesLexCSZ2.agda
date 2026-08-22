------------------------------------------------------------------------
-- BRANCH (S,0), rec₂ — VACUOUS: μ₂ y < μ₂ x ≤ 0, so `⊢strong-base'`.
--
-- Structurally (0,0)'s rec₂ at two more weakenings; it needs NO cast at
-- all, exactly as branch (0,0) predicted for the recursor derivations.
-- ⚠ 24.6 s / 2.46 GB even so — own module.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCSZ2 where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; wk-single )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLexC
open import poc.OCP0009.NbEPDirDBExamplesLexCSZData using ( module SZD )

module SZ2 (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SZD Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  ⊢lexSZrec2 : ΓSZ ⊢ lexSZrec2
             ∷ rec2T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (w (w (w (w (w (w μ₂)))))) (var (vs (vs vz)))
  ⊢lexSZrec2 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcA))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var here)) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))) (⊢var (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))) (⊢var (there (there (there (there here))))))) (⊢strong-base' (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcP))))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))))))) (⊢var (there (there (there (there (there here))))))) (⊢var here) (⊢var (there (there (there here)))))))
