{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeCostS5 where

-- ABLATION S5: carrier is a CLOSED code El ⌜Nat⌝, 4 context slots (no A slot).

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app; ⌜Nat⌝
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _∋_∷_; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBLibOrd using ( ⊢strong-base' )

REC1T : RTy (ε ∙ ∙ ∙ ∙)
REC1T = Π (El ⌜Nat⌝)
          (Π (Hom Nat (nsuc (app (var (vs (vs (vs vz)))) (var vz))) (app (var (vs (vs (vs vz)))) (var (vs vz))))
             (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))))

REC2T : RTy (ε ∙ ∙ ∙ ∙ ∙)
REC2T = Π (El ⌜Nat⌝)
          (Π (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var vz)) (app (var (vs (vs (vs (vs vz))))) (var (vs (vs vz)))))
             (Π (Hom Nat (nsuc (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))) (app (var (vs (vs (vs (vs vz))))) (var (vs (vs (vs vz))))))
                (El (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs vz)))))))

LStepT : RTy (ε ∙ ∙ ∙)
LStepT = Π (El ⌜Nat⌝) (Π REC1T (Π REC2T (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs (vs vz)))))))

Γ₅ : Ctx
Γ₅ = (((◇ ▹ Π (El ⌜Nat⌝) U) ▹ Π (El ⌜Nat⌝) Nat) ▹ Π (El ⌜Nat⌝) Nat) ▹ LStepT

ΓZZ : Ctx
ΓZZ =
  (((Γ₅ ▹ Nat) ▹ subTy (single nzero) (El ⌜Nat⌝))
     ▹ subTy (extS (single nzero))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var vz)) nzero))
     ▹ subTy (extS (extS (single nzero)))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz))) (var (vs (vs vz))))

lexZZrec1 : RTm ⌊ ΓZZ ⌋
lexZZrec1 =
  lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

REC1TZZ : RTy ⌊ ΓZZ ⌋
REC1TZZ =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs)
      (renTy (extR vs) (renTy (extR vs) REC1T)))))

⊢lexZZrec1 : ΓZZ ⊢ lexZZrec1 ∷ REC1TZZ
⊢lexZZrec1 =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (here))))))))) (⊢var here))) (⊢app (⊢var (there (there (there (there (there (there (there (here))))))))) (⊢var (there (there (there (here)))))))
      (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there (there (here))))))))))) (⊢var (there (here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (here)))))))))) (⊢var (there (here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (here)))))))))) (⊢var (there (there (there (there (here))))))) (⊢var here) (⊢var (there (there (there (here)))))))
