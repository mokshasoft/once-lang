{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexZS where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import DirectedHoTT.Lib.Ord
  using ( ⊢strong-base'; ⊢strong-step )
open import DirectedHoTT.Negative.Lex
  using ( Γ₅; REC1T; REC2T; LStepT; M0lex; lexZS )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )

------------------------------------------------------------------------
-- BRANCH (0,S).  n₁ = 0 still collapses `rec₁`, but n₂ = suc m now makes
-- `rec₂` REAL: it calls the inner IH at the smaller μ₂-bound.
--
-- ctx after the three ⊢lams: vz=lt, vs=le, vs²=x, vs³=IH, vs⁴=m,
--                            vs⁵=n₂, vs⁶=stp, vs⁷=μ₂, vs⁸=μ₁, vs⁹=cP
------------------------------------------------------------------------

ΓZS : Ctx
ΓZS =
  ((((((Γ₅ ▹ Nat) ▹ Nat) ▹ M0lex) ▹ subTy nrs (El (var (vs (vs (vs (vs (vs vz))))))))
      ▹ subTy (extS nrs)
          (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var vz)) nzero))
      ▹ subTy (extS (extS nrs))
          (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))
                   (var (vs (vs vz)))))

lexZSrec1 : RTm ⌊ ΓZS ⌋
lexZSrec1 =
  lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

REC1TZS : RTy ⌊ ΓZS ⌋
REC1TZS =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) REC1T))))))

⊢lexZSrec1 : ΓZS ⊢ lexZSrec1 ∷ REC1TZS
⊢lexZSrec1 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there (there here))))))))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var here))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there here)))))) (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there (there (there (there here)))))) (⊢var here) (⊢var (there (there (there here))))))

-- ★ THE FIRST REAL RECURSIVE CALL in this file.  `rec₂` here is not
--   vacuous: it invokes the inner IH (`M0lex` variable, vs⁶) at `y`, and
--   must discharge TWO obligations to do so —
--     μ₁ y ≤ 0      by plain `⊢ordtr`: μ₁ y ≤ μ₁ x and μ₁ x ≤ 0;
--     μ₂ y ≤ m      by `⊢strong-step`: μ₂ y < μ₂ x and μ₂ x ≤ suc m.
--   That second one IS the lexicographic descent — n₁ held fixed, n₂
--   strictly down — and it is the move `⊢strong-step` already proves.
--
-- ctx at the body: vz=ltY, vs=leY, vs²=y, vs³=lt, vs⁴=le, vs⁵=x,
--                  vs⁶=IH, vs⁷=m, vs⁸=n₂, vs⁹=stp, vs¹⁰=μ₂, vs¹¹=μ₁, vs¹²=cP

lexZSrec2 : RTm ⌊ ΓZS ⌋
lexZSrec2 =
  lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (ordtr (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var (vs vz)) (var (vs (vs (vs (vs vz))))))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))))))

REC2TZS : RTy ⌊ ΓZS ⌋
REC2TZS =
  subTy (single lexZSrec1)
    (subTy (extS (single (var (vs (vs vz)))))
      (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) REC2T)))))))

⊢lexZSrec2 : ΓZS ⊢ lexZSrec2 ∷ REC2TZS
⊢lexZSrec2 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there (there here))))))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var here)) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there (there here))))))) (⊢app (⊢app (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var (there (there here)))) (⊢ordtr (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there (there (there (there (there here))))))) ⊢nzero (⊢var (there here)) (⊢var (there (there (there (there here))))))) (⊢strong-step (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there (there (there (there (there here))))))) (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here) (⊢var (there (there (there here))))))))

------------------------------------------------------------------------
-- BRANCH (0,S) ASSEMBLED.
------------------------------------------------------------------------

⊢lexZS : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
         (((Γ₅ ▹ Nat) ▹ Nat) ▹ M0lex) ⊢ lexZS stpTm ∷ subTy nrs M0lex
⊢lexZS stpTm dstp =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there here)))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var here)) ⊢nzero) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var (there here))) (⊢nsuc (⊢var (there (there (there here)))))) (⊢app (⊢app (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dstp))))))) (⊢var (there (there here)))) ⊢lexZSrec1) ⊢lexZSrec2)))
