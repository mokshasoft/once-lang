------------------------------------------------------------------------
-- OCP-0009 — BRANCH (0,S), SHARED DATA:  context, the two recursor
-- arguments as raw terms (rec₂ peeled binder by binder), and their types.
--
-- n₁ = 0 still collapses `rec₁`, but n₂ = suc m makes `rec₂` REAL: it
-- calls the inner IH at the smaller μ₂-bound.
--
-- ⚠ SPLIT, and rec₂ split ONE `⊢lam` PER MODULE — see LexZZData for the
--   measurements.  The carrier costs ~6× in elaborated term size and each
--   `⊢lam` layer is worth ~2.5–3 GB against a 5.5 GB cap.
--
-- ctx after the three ⊢lams: vz=lt, vs=le, vs²=x, vs³=IH, vs⁴=m,
--            vs⁵=n₂, vs⁶=stp, vs⁷=μ₂, vs⁸=μ₁, vs⁹=cP, vs¹⁰=A
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZSData where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs; _∋_∷_; here; there )
open import poc.OCP0009.NbEPDirDBExamplesLex
  using ( Γ₅; M0lex; REC1T; REC2T; REC2Tbody; REC2Tbody2 )

ΓZS : Ctx
ΓZS =
  ((((((Γ₅ ▹ Nat) ▹ Nat) ▹ M0lex)
      ▹ subTy nrs (El (var (vs (vs (vs (vs (vs (vs vz)))))))))
      ▹ subTy (extS nrs)
          (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var vz)) nzero))
      ▹ subTy (extS (extS nrs))
          (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))
                   (var (vs (vs vz)))))

-- the carrier at ΓZS — the `x`/`y` binder of every recursor argument
AZS : RTy ⌊ ΓZS ⌋
AZS = El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))

∋A : ΓZS ∋ vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) ∷ U
∋A = there (there (there (there (there (there (there (there (there (there here)))))))))

-- ctx: vz=y, vs=lt, …, vs⁹=μ₁, vs¹⁰=cP, vs¹¹=A   — shared by rec₁ and rec₂
∋μ₁¹ : (ΓZS ▹ AZS) ∋ vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) ∷
       Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) ) Nat
∋μ₁¹ = there (there (there (there (there (there (there (there (there here))))))))

------------------------------------------------------------------------
-- rec₁ — vacuous, `ordtr` into `⊢strong-base'`.
------------------------------------------------------------------------

lexZSrec1 : RTm ⌊ ΓZS ⌋
lexZSrec1 =
  lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

REC1TZS : RTy ⌊ ΓZS ⌋
REC1TZS =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs)
      (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) REC1T)))))))

------------------------------------------------------------------------
-- rec₂ — THE FIRST REAL RECURSIVE CALL.  It invokes the inner IH
-- (`M0lex` variable) at `y`, and must discharge TWO obligations:
--     μ₁ y ≤ 0    by plain `⊢ordtr`:      μ₁ y ≤ μ₁ x and μ₁ x ≤ 0;
--     μ₂ y ≤ m    by `⊢strong-step`:      μ₂ y < μ₂ x and μ₂ x ≤ suc m.
-- The second IS the lexicographic descent — n₁ held, n₂ strictly down.
------------------------------------------------------------------------

lexZSrec2in2 : RTm ((⌊ ΓZS ⌋ ∙) ∙)
lexZSrec2in2 =
  lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (ordtr (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var (vs vz)) (var (vs (vs (vs (vs vz))))))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))))

lexZSrec2in : RTm (⌊ ΓZS ⌋ ∙)
lexZSrec2in = lam lexZSrec2in2

lexZSrec2 : RTm ⌊ ΓZS ⌋
lexZSrec2 = lam lexZSrec2in

-- `le : μ₁ y ≤ μ₁ x`, rec₂'s second binder, in REDUCED form
HOMleZS : RTy ⌊ ΓZS ▹ AZS ⌋
HOMleZS =
  Hom Nat (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var vz))
          (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs (vs vz)))))

REC2TZS : RTy ⌊ ΓZS ⌋
REC2TZS =
  subTy (single lexZSrec1)
    (subTy (extS (single (var (vs (vs vz)))))
      (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs))
        (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs))
          (renTy (extR (extR vs)) REC2T))))))))

REC2TZSin : RTy ⌊ ΓZS ▹ AZS ⌋
REC2TZSin =
  subTy (extS (single lexZSrec1))
    (subTy (extS (extS (single (var (vs (vs vz))))))
      (renTy (extR (extR (extR vs))) (renTy (extR (extR (extR vs))) (renTy (extR (extR (extR vs)))
        (renTy (extR (extR (extR vs))) (renTy (extR (extR (extR vs))) (renTy (extR (extR (extR vs)))
          (renTy (extR (extR (extR vs))) REC2Tbody))))))))

REC2TZSin2 : RTy ⌊ (ΓZS ▹ AZS) ▹ HOMleZS ⌋
REC2TZSin2 =
  subTy (extS (extS (single lexZSrec1)))
    (subTy (extS (extS (extS (single (var (vs (vs vz)))))))
      (renTy (extR (extR (extR (extR vs)))) (renTy (extR (extR (extR (extR vs)))) (renTy (extR (extR (extR (extR vs))))
        (renTy (extR (extR (extR (extR vs)))) (renTy (extR (extR (extR (extR vs)))) (renTy (extR (extR (extR (extR vs))))
          (renTy (extR (extR (extR (extR vs)))) REC2Tbody2))))))))
