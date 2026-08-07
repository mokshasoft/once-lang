------------------------------------------------------------------------
-- OCP-0009 — BRANCH (0,0), rec₂ UNDER `y` AND `le`:
--     `μ₂ y < μ₂ x → P y`.
--
-- The innermost peel: one `⊢lam` and the `⊢strong-base'` body.  VACUOUS —
-- `rec₂` gets μ₂ y < μ₂ x ≤ 0, so it is `ordtr` into `⊢strong-base'`.
-- See LexZZData for why rec₂ is one `⊢lam` per module.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZZ2b where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _∋_∷_; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base' )
open import poc.OCP0009.NbEPDirDBExamplesLexZZData
  using ( ΓZZ; AZZ; HOMleZZ; lexZZrec2in2; REC2TZZin2 )

-- ctx after `le : μ₁ y ≤ μ₁ x`: vz=le, vs=y, vs²=lt, vs³=le', vs⁴=x,
--   vs⁵=n₂, vs⁶=stp, vs⁷=μ₂, vs⁸=μ₁, vs⁹=cP, vs¹⁰=A
∋μ₂² : ((ΓZZ ▹ AZZ) ▹ HOMleZZ) ∋ vs (vs (vs (vs (vs (vs (vs vz)))))) ∷
       Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) ) Nat
∋μ₂² = there (there (there (there (there (there (there here))))))

-- ctx after `lt : μ₂ y < μ₂ x`: vz=lt, vs=le, vs²=y, vs³=lt', vs⁴=le',
--   vs⁵=x, vs⁶=n₂, vs⁷=stp, vs⁸=μ₂, vs⁹=μ₁, vs¹⁰=cP, vs¹¹=A
∋cP³ : (((ΓZZ ▹ AZZ) ▹ HOMleZZ)
          ▹ Hom Nat (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs vz))))
                    (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs (vs vz)))))))
       ∋ vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) ∷
       Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) ) U
∋cP³ = there (there (there (there (there (there (there (there (there (there here)))))))))

∋μ₂³ : (((ΓZZ ▹ AZZ) ▹ HOMleZZ)
          ▹ Hom Nat (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs vz))))
                    (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs (vs vz)))))))
       ∋ vs (vs (vs (vs (vs (vs (vs (vs vz))))))) ∷
       Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) ) Nat
∋μ₂³ = there (there (there (there (there (there (there (there here)))))))

⊢lexZZrec2in2 : ((ΓZZ ▹ AZZ) ▹ HOMleZZ) ⊢ lexZZrec2in2 ∷ REC2TZZin2
⊢lexZZrec2in2 =
  ⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var ∋μ₂²) (⊢var (there here))))
                      (⊢app (⊢var ∋μ₂²) (⊢var (there (there (there (there here)))))))
    (⊢strong-base' (⊢app (⊢var ∋cP³) (⊢var (there (there here))))
                   (⊢app (⊢var ∋μ₂³) (⊢var (there (there here))))
                   (⊢app (⊢var ∋μ₂³) (⊢var (there (there (there (there (there here)))))))
                   (⊢var here)
                   (⊢var (there (there (there here)))))
