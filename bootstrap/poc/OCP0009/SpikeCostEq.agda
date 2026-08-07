{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeCostEq where
-- Is the hand-reduced REC1TZZ actually equal to the subTy/renTy chain?
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType using ( Ctx; ◇; _▹_; ⌊_⌋; single )
open import poc.OCP0009.SpikeCostS1 using ( Γ₅; REC1T )

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

ΓZZ : Ctx
ΓZZ =
  (((Γ₅ ▹ Nat) ▹ subTy (single nzero) (El (var (vs (vs (vs (vs (vs (vs vz)))))))))
     ▹ subTy (extS (single nzero))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var vz)) nzero))
     ▹ subTy (extS (extS (single nzero)))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz))) (var (vs (vs vz))))

ctxSlotsReduced :
  ΓZZ ≡ ((((Γ₅ ▹ Nat) ▹ El (var (vs (vs (vs (vs (vs vz)))))))
            ▹ Hom Nat (app (var (vs (vs (vs (vs vz))))) (var vz)) nzero)
            ▹ Hom Nat (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) nzero)
ctxSlotsReduced = refl

rec1Reduced :
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs)
      (renTy (extR vs) (renTy (extR vs) REC1T)))))
  ≡
  Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
    (Π (Hom Nat (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var vz)))
                (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs vz))))))
       (El (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
                (var (vs vz)))))
rec1Reduced = refl
