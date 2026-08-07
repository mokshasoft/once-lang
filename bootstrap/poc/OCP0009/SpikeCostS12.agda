{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeCostS12 where

-- ABLATION S12: identical to S1 (generic carrier), except the `stp`
-- slot is GONE from Γ₅ — 4 slots instead of 5.  ⊢lexZZrec1 never
-- references stp, so this is exactly fix #1's payoff, on a REAL slot
-- rather than the dummy U slot of S5/S6.  Every index crossing stp's
-- old position drops by one.

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _∋_∷_; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base' )

REC1T : RTy (ε ∙ ∙ ∙ ∙ ∙)
REC1T = Π (El (var (vs (vs (vs (vs vz))))))
          (Π (Hom Nat (nsuc (app (var (vs (vs (vs vz)))) (var vz)))
                      (app (var (vs (vs (vs vz)))) (var (vs vz))))
             (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))))

-- ★ NO `stp` SLOT.
Γ₅ : Ctx
Γ₅ = (((◇ ▹ U) ▹ Π (El (var vz)) U) ▹ Π (El (var (vs vz))) Nat)
       ▹ Π (El (var (vs (vs vz)))) Nat

ΓZZ : Ctx
ΓZZ =
  (((Γ₅ ▹ Nat) ▹ subTy (single nzero) (El (var (vs (vs (vs (vs (vs vz))))))))
     ▹ subTy (extS (single nzero))
         (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var vz)) nzero))
     ▹ subTy (extS (extS (single nzero)))
         (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) (var (vs (vs vz))))

lexZZrec1 : RTm ⌊ ΓZZ ⌋
lexZZrec1 =
  lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

REC1TZZ : RTy ⌊ ΓZZ ⌋
REC1TZZ =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) REC1T))))

⊢lexZZrec1 : ΓZZ ⊢ lexZZrec1 ∷ REC1TZZ
⊢lexZZrec1 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there here)))))))))
    (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var here))) (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var (there (there (there here))))))
      (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there here)))))))))  (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there (there (there here)))))) (⊢var here) (⊢var (there (there (there here)))))) 
