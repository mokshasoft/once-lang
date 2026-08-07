------------------------------------------------------------------------
-- OCP-0009 — BRANCH (0,0), rec₁:  `(y : A) → μ₁ y < μ₁ x → P y`.
--
-- VACUOUS: `rec₁` gets μ₁ y < μ₁ x ≤ 0, so it is `ordtr` into
-- `⊢strong-base'`.  Its own module for RAM — see LexZZData for why.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZZ1 where

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
  using ( ΓZZ; AZZ; ∋A; ∋μ₁¹; lexZZrec1; REC1TZZ )

-- ctx after `le`: vz=le, vs=y, …, vs⁸=μ₁, vs⁹=cP, vs¹⁰=A
∋cP² : ((ΓZZ ▹ AZZ)
         ▹ Hom Nat (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var vz)))
                   (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs vz))))))
       ∋ vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) ∷
       Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) ) U
∋cP² = there (there (there (there (there (there (there (there (there here))))))))

∋μ₁² : ((ΓZZ ▹ AZZ)
         ▹ Hom Nat (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var vz)))
                   (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs vz))))))
       ∋ vs (vs (vs (vs (vs (vs (vs (vs vz))))))) ∷
       Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) ) Nat
∋μ₁² = there (there (there (there (there (there (there (there here)))))))

⊢lexZZrec1 : ΓZZ ⊢ lexZZrec1 ∷ REC1TZZ
⊢lexZZrec1 =
  ⊢lam (ty-El (⊢var ∋A))
    (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var ∋μ₁¹) (⊢var here)))
                         (⊢app (⊢var ∋μ₁¹) (⊢var (there (there (there here))))))
      (⊢strong-base' (⊢app (⊢var ∋cP²) (⊢var (there here)))
                     (⊢app (⊢var ∋μ₁²) (⊢var (there here)))
                     (⊢app (⊢var ∋μ₁²) (⊢var (there (there (there (there here))))))
                     (⊢var here)
                     (⊢var (there (there (there here))))))
