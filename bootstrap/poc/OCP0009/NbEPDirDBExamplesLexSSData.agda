------------------------------------------------------------------------
-- OCP-0009 — BRANCH (S,S), SHARED DATA:  context, the two recursor
-- arguments as raw terms, and their expected types.
--
-- ⚠ SPLIT FOUR WAYS (data / rec₁ / rec₂ / assembly), not the two used for
--   the other branches.  (S,0) alone reached 4.98 GB against a 5.5 GB cap,
--   and (S,S) is the branch where BOTH recursor arguments are live, so its
--   two derivations cannot share a module.  Cheap here: types and terms
--   elaborate small; it is the DERIVATIONS that are expensive.
--
-- ctx after the three ⊢lams: vz=lt, vs=le, vs²=x, vs³=IH₂, vs⁴=m,
--            vs⁵=n₂, vs⁶=IH₁, vs⁷=n₁', vs⁸=stp, vs⁹=μ₂, vs¹⁰=μ₁, vs¹¹=cP
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexSSData where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; Unit
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLex
  using ( Γ₅; REC1T; REC2T; M1lex; lexAuxMot )

ΓSS : Ctx
ΓSS =
  ((((((((Γ₅ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ Nat) ▹ M1lex) ▹ subTy nrs Nat)
      ▹ subTy (extS nrs)
          (Hom Nat (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var vz))
                   (nsuc (var (vs (vs (vs (vs vz)))))))) 
      ▹ subTy (extS (extS nrs))
          (Hom Nat (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs vz)))
                   (var (vs (vs vz)))))

lexSSrec1 : RTm ⌊ ΓSS ⌋
lexSSrec1 =
  lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz)))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var vz) (var (vs (vs (vs vz)))))) (natrec unit (var vz) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz))))))

REC1TSS : RTy ⌊ ΓSS ⌋
REC1TSS = subTy (single (var (vs (vs vz)))) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) REC1T)))))))))

lexSSrec2 : RTm ⌊ ΓSS ⌋
lexSSrec2 =
  lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (ordtr (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))) (var (vs (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz)) (var (vs (vs (vs (vs vz))))))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))))))

REC2TSS : RTy ⌊ ΓSS ⌋
REC2TSS =
  subTy (single lexSSrec1) (subTy (extS (single (var (vs (vs vz))))) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs)) REC2T))))))))))
