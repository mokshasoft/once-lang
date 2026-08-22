------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (S,0) under option C, SHARED DATA: the
-- context and the two recursor arguments as raw terms.
--
-- ⚠ SPLIT FOUR WAYS (data / rec₁ / rec₂ / assembly), the way option B had
--   to split (S,S).  MEASURED: as one module this branch OOMs at the
--   5.5 GB cap.  Split:  data 3.1 s / 0.39 GB, rec₁ 35.2 s / 4.19 GB,
--   rec₂ 24.6 s / 2.46 GB, assembly 6.2 s / 0.50 GB.
--   Cheap here — types and terms elaborate small; the DERIVATIONS are the
--   expense.
--
-- ★ THAT IS THE HEADLINE FOR THIS BRANCH.  Option B fit (S,0) in ONE
--   module at 5.16 GB.  Option C does not.  See NbEPDirDBExamplesLexCSZ.
--
-- ctx: vz = lt, vs = le, vs² = x, vs³ = n₂, vs⁴ = IH₁, vs⁵ = n₁', then Δ
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexCSZData where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Strong using ( ⊢le-refl; reflTm )
open import DirectedHoTT.Lib.Ord
  using ( ⊢strong-base'; ⊢strong-step )
open import DirectedHoTT.Negative.LexC

module SZD (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  ΓSZ : Ctx
  ΓSZ =
    (((((Δ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ El (w (w (w cA))))
       ▹ Hom Nat (app (w (w (w (w μ₁)))) (var vz)) (nsuc (var (vs (vs (vs vz))))))
       ▹ Hom Nat (app (w (w (w (w (w μ₂))))) (var (vs vz))) nzero

  -- ★ THE OTHER HALF OF THE ORDER.  `rec₁` calls the OUTER IH with FOUR
  --   arguments: n₂ := μ₂ y — THE RESET — then y, then μ₁ y ≤ n₁' by
  --   ⊢strong-step (n₁ STRICTLY DOWN), then μ₂ y ≤ μ₂ y by ⊢le-refl.
  --   Dropping n₁ buys an arbitrary n₂; this is where that is cashed.
  nSZ : RTm (⌊ ΓSZ ⌋ ∙ ∙)
  nSZ = app (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs vz))

  ltSZ : RTm (⌊ ΓSZ ⌋ ∙ ∙)
  ltSZ = ordtr (nsuc (app (w (w (w (w (w (w (w (w μ₁)))))))) (var (vs vz)))) (app (w (w (w (w (w (w (w (w μ₁)))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))

  lexSZrec1 : RTm ⌊ ΓSZ ⌋
  lexSZrec1 =
    lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) nSZ) (var (vs vz))) ltSZ) (reflTm nSZ)))

  -- `rec₂` is vacuous here: μ₂ y < μ₂ x ≤ 0.
  lexSZrec2 : RTm ⌊ ΓSZ ⌋
  lexSZrec2 =
    lam (lam (lam (absurd (app (w (w (w (w (w (w (w (w (w cP))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w (w μ₂))))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (w (w μ₂))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))
