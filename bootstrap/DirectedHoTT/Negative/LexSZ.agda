------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (S,0):  n₁ = suc n₁', n₂ = 0.
--
-- Mirror image of (0,S).  Here `rec₂` collapses (μ₂ y < μ₂ x ≤ 0) and
-- `rec₁` is the live one — and it is the OTHER half of the lexicographic
-- order: it calls the OUTER IH, dropping n₁ to n₁' and RESETTING n₂ to
-- μ₂ y, discharged by `⊢le-refl`.
--
-- ⚠ own module for RAM; see NbEPDirDBExamplesLexZZ for why.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexSZ where
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
  using ( Γ₅; REC1T; REC2T; LStepT; M1lex; lexAuxMot; lexSZ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )

------------------------------------------------------------------------
-- ctx after the three ⊢lams: vz=lt, vs=le, vs²=x, vs³=n₂, vs⁴=IH₁,
--                            vs⁵=n₁', vs⁶=stp, vs⁷=μ₂, vs⁸=μ₁, vs⁹=cP
------------------------------------------------------------------------

ΓSZ : Ctx
ΓSZ =
  ((((((Γ₅ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ subTy (single nzero) (El (var (vs (vs (vs (vs (vs (vs (vs vz))))))))))
      ▹ subTy (extS (single nzero))
          (Hom Nat (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var vz))
                   (nsuc (var (vs (vs (vs (vs vz)))))))) 
      ▹ subTy (extS (extS (single nzero)))
          (Hom Nat (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs vz)))
                   (var (vs (vs vz)))))

-- ★ THE OTHER HALF OF THE LEXICOGRAPHIC ORDER.  `rec₁` calls the OUTER IH
--   (`lexAuxMot` variable, vs⁶) with FOUR arguments: n₂ := μ₂ y — the
--   RESET — then y, then μ₁ y ≤ n₁' by `⊢strong-step` (n₁ strictly down),
--   then μ₂ y ≤ μ₂ y by `⊢le-refl`.  Dropping n₁ buys an arbitrary n₂.
lexSZrec1 : RTm ⌊ ΓSZ ⌋
lexSZrec1 =
  lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz)))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz)))))) (natrec unit (var vz) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz))))))

REC1TSZ : RTy ⌊ ΓSZ ⌋
REC1TSZ =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) REC1T))))))

⊢lexSZrec1 : ΓSZ ⊢ lexSZrec1 ∷ REC1TSZ
⊢lexSZrec1 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there (there here))))))))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var here))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there here)))))) (⊢app (⊢app (⊢app (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there here)))) (⊢var (there here))) (⊢strong-step (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there (there (there (there here)))))) (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here) (⊢var (there (there (there here)))))) (⊢le-refl (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there here))))))

-- `rec₂` is vacuous here: μ₂ y < μ₂ x ≤ 0.
lexSZrec2 : RTm ⌊ ΓSZ ⌋
lexSZrec2 =
  lam (lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))

REC2TSZ : RTy ⌊ ΓSZ ⌋
REC2TSZ =
  subTy (single lexSZrec1)
    (subTy (extS (single (var (vs (vs vz)))))
      (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) REC2T)))))))

⊢lexSZrec2 : ΓSZ ⊢ lexSZrec2 ∷ REC2TSZ
⊢lexSZrec2 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there (there here))))))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var here)) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there (there here))))))) (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there (there (there (there (there here))))))) (⊢var here) (⊢var (there (there (there here)))))))

------------------------------------------------------------------------
-- BRANCH (S,0) ASSEMBLED.
------------------------------------------------------------------------

⊢lexSZ : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
         (((Γ₅ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ⊢ lexSZ stpTm ∷ subTy (single nzero) M1lex
⊢lexSZ stpTm dstp =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there here)))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var here)) (⊢nsuc (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var (there here))) ⊢nzero) (⊢app (⊢app (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dstp))))))) (⊢var (there (there here)))) ⊢lexSZrec1) ⊢lexSZrec2)))
