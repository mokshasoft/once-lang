------------------------------------------------------------------------
-- OCP-0009 — SPIKE: `⊢amrecΠ` AT THE ℕ CARRIER — THE PLUMBING.
--
-- ★ FIRST USE SITE of the re-packaged combinator.  `div` is chosen over
--   `gcd` deliberately: `⊢div` ALREADY EXISTS built raw from nested
--   `natrec` (NbEPDirDBExamplesDiv), so building the same function
--   through `⊢amrecΠ` is a same-function A/B.  gcd has no raw
--   counterpart and could only show that the abstraction WORKS, not that
--   it is BETTER.
--
-- THIS FILE IS THE PLUMBING ONLY: it wires the ℕ-carrier instantiation
-- into `AmΠ` with a TRIVIAL step (constant zero), to establish that the
-- use site costs nothing before the real `div` step goes in.  What it
-- measures is exactly the boilerplate a caller pays.
--
-- ⚠ Not `div` yet — `divStp` below returns 0 for everything.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeDivC where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app
        ; Π; renTy; renTm; subTy; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π
        ; _≅ᵀ_; csymᵀ )
open import poc.OCP0009.NbEPDirDBExamplesLexC using ( w; rec1T )
open import poc.OCP0009.NbEPDirDBExamplesAmrecC using ( aStepT; module AmΠ )
-- ★ the ℕ-carrier instantiation package, reused verbatim from the
--   instantiation spike — the data are CONTEXT-POLYMORPHIC, so the same
--   four terms and derivations serve at any Δ.
open import poc.OCP0009.SpikeAmrecInst
  using ( cAt; cPt; μt; dcA; dcP; dμ; elNat; elCP )

-- the ambient context: the divisor's predecessor `k`, exactly `Γ₃` in
-- NbEPDirDBExamplesDiv, so the comparison is like-for-like.
Γ₃ : Ctx
Γ₃ = ◇ ▹ Nat

------------------------------------------------------------------------
-- ★ THE IH TYPE IS WELL-FORMED.  Note `w μt ≡ μt` DEFINITIONALLY — the
--   instantiation data are CLOSED, so weakening is the identity on them
--   and `dμ`/`dcP` apply at every depth with no ⊢wk and no cast.  That
--   is the pay-off of making them context-polymorphic.
------------------------------------------------------------------------

⊢ihT : {Γ : Ctx} → (Γ ▹ El cAt) ⊢ty rec1T (w cAt) (w cPt) (w μt) (var vz)
⊢ihT =
  ty-Π (ty-El dcA)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢app dμ (⊢var here)))
                         (⊢app dμ (⊢var (there here))))
          (ty-El (⊢app dcP (⊢var (there here)))))

------------------------------------------------------------------------
-- the STUB step: ignores both the argument and the IH.
------------------------------------------------------------------------

divStp : RTm ⌊ Γ₃ ⌋
divStp = lam (lam nzero)

⊢divStp : Γ₃ ⊢ divStp ∷ aStepT cAt cPt μt
⊢divStp =
  ⊢lam (ty-El dcA)
    (⊢lam ⊢ihT (⊢conv ⊢nzero (csymᵀ (elCP (var (vs vz))))))

------------------------------------------------------------------------
-- ★★ THE USE SITE.  One `open`, and the recursor exists as a CLOSED
--    Π-typed term, plus the pointwise form, both for free.
------------------------------------------------------------------------

open AmΠ Γ₃ cAt cPt μt divStp dcA dcP dμ ⊢divStp
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt )

-- the recursor, as a term of a Π type
divC : RTm ⌊ Γ₃ ⌋
divC = amrecTm

⊢divC : Γ₃ ⊢ divC ∷ Π (El cAt) (El (app (w cPt) (var vz)))
⊢divC = ⊢amrecΠ

-- …and applied at a concrete argument, via the DERIVED pointwise form.
⊢divC-at : {m : RTm ⌊ Γ₃ ⌋} → Γ₃ ⊢ m ∷ El cAt →
           Γ₃ ⊢ app divC m ∷ El (app cPt m)
⊢divC-at dm = ⊢amrecPt dm
