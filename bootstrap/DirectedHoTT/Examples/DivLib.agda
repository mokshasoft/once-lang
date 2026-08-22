------------------------------------------------------------------------
-- OCP-0009 — `div` THROUGH `⊢amrecTΠ`: THE D4 USE SITE.
--
-- The same function as `SpikeDivC`, against the D4 interface instead of
-- the AmrecC one.  Both are kept so the A/B survives.
--
-- ★ THE INSTANTIATION IS NOW TRIVIAL, and that is the headline:
--
--     A  := Nat        the carrier is a TYPE — no code, no `El`, no ⌜Nat⌝
--     cM := ⌜Nat⌝      the motive, a constant code family
--     m  := var vz     the measure IS the carrier variable
--
--   with derivations `ty-Nat`, `⊢⌜Nat⌝`, `⊢var here`.  Under AmrecC these
--   were `lam ⌜Nat⌝` and `lam (var vz)` — object-language FUNCTIONS —
--   each needing a `⊢lam` derivation and a β-conversion at every use.
--
-- ★★ AND THE IH TYPE READS AS THE MATHEMATICS:
--
--     aIHT Nat ⌜Nat⌝ (var vz)
--       = Π Nat (Π (Hom Nat (nsuc (var vz)) (var (vs vz))) (El ⌜Nat⌝))
--       = (y : Nat) → y < x → P y
--
--   Not one `app` in it.  Under AmrecC the same type carried three.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.DivLib where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; natrec; lam; app; ⌜Nat⌝
        ; Π; renTy; renTm; subTy; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢⌜Nat⌝; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π
        ; _≅ᵀ_; csymᵀ; El-⌜Nat⌝ )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Lib.Monus
  using ( monusTm; ⊢monus )
open import DirectedHoTT.Examples.Div
  using ( monusStep; ⊢div-descend )
open import DirectedHoTT.Lib.Strong using ( reflTm )
open import DirectedHoTT.Lib.Rec   using ( aIHT )
open import DirectedHoTT.Lib.Amrec using ( aStepT; module AmTΠ )

-- the divisor's predecessor, exactly `Γ₃` in NbEPDirDBExamplesDiv
Γ₃ : Ctx
Γ₃ = ◇ ▹ Nat

------------------------------------------------------------------------
-- ★ THE ONLY CONVERSION IN THE FILE.  The motive must be a CODE (⊢absurd
--   is code-indexed), so `P x` is `El ⌜Nat⌝` and every `Nat` result
--   crosses once.  That is the whole β tax under D4.
------------------------------------------------------------------------

elNat : {Γ : Cx} → El (⌜Nat⌝ {Γ}) ≅ᵀ Nat
elNat = red→≅ᵀ (stepᵀ El-⌜Nat⌝ doneᵀ)

asP : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
asP d = ⊢conv d (csymᵀ elNat)

------------------------------------------------------------------------
-- THE STEP — the whole of `div`, and nothing else.
--
--   div m = case m of
--     0     → 0
--     suc j → case (suc j) ∸ k of
--       0     → 0
--       suc _ → suc (ih (j ∸ k) ⊢div-descend)
------------------------------------------------------------------------

-- ★ the motive for the case split on the dividend.  Note it is the SAME
--   expression at every depth — everything in it is either closed or the
--   carrier variable — so `subTy (single x)` on it is DEFINITIONAL and no
--   fitting lemma is needed at all.
divMot : RTy (⌊ Γ₃ ⌋ ∙ ∙)
divMot = Π (aIHT Nat ⌜Nat⌝ (var vz)) (El ⌜Nat⌝)

-- ★ ONE lemma covers the IH type at EVERY bound the file needs — and it
--   reads as the mathematics: `(y : Nat) → y < b → P y`.
⊢ihTat : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
         Γ ⊢ty Π Nat (Π (Hom Nat (nsuc (var vz)) (renTm vs b)) (El ⌜Nat⌝))
⊢ihTat db =
  ty-Π ty-Nat
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢var here)) (⊢wk db)) (ty-El ⊢⌜Nat⌝))

⊢divMot : ((Γ₃ ▹ Nat) ▹ Nat) ⊢ty divMot
⊢divMot = ty-Π (⊢ihTat (⊢var here)) (ty-El ⊢⌜Nat⌝)

divZ : RTm (⌊ Γ₃ ⌋ ∙)
divZ = lam nzero

⊢divZ : (Γ₃ ▹ Nat) ⊢ divZ ∷ subTy (single nzero) divMot
⊢divZ = ⊢lam (⊢ihTat ⊢nzero) (asP ⊢nzero)

divS : RTm (⌊ Γ₃ ⌋ ∙ ∙ ∙)
divS =
  lam (natrec nzero
        (nsuc (app (app (var (vs (vs vz))) (monusTm (var (vs (vs (vs (vs vz))))) (var (vs (vs (vs (vs (vs (vs vz)))))))))
                   (natrec (reflTm (var (vs (vs (vs (vs vz)))))) (monusStep (vs (vs (vs (vs vz))))) (var (vs (vs (vs (vs (vs (vs vz))))))))))
        (monusTm (nsuc (var (vs (vs vz)))) (var (vs (vs (vs (vs vz)))))))

divStp : RTm ⌊ Γ₃ ⌋
divStp = lam (natrec divZ divS (var vz))

-- ★ the inner test's motive is CONSTANT — `El ⌜Nat⌝` either way.  Under
--   AmrecC it had to mention `app cPt (nsuc j)`.
⊢divSMot : {Γ : Ctx} → Γ ⊢ty El ⌜Nat⌝
⊢divSMot = ty-El ⊢⌜Nat⌝

⊢divS : (((Γ₃ ▹ Nat) ▹ Nat) ▹ divMot) ⊢ divS ∷ subTy nrs divMot
⊢divS =
  ⊢lam (⊢ihTat (⊢nsuc (⊢var (there here))))
    (⊢natrec ⊢divSMot (asP ⊢nzero)
      (asP (⊢nsuc (⊢conv (⊢app (⊢app (⊢var (there (there here))) dArg) dDesc) elNat)))
      (⊢monus (⊢nsuc (⊢var (there (there here)))) (⊢var (there (there (there (there here)))))))
  where
    dj = ⊢var (there (there (there (there here))))
    dk = ⊢var (there (there (there (there (there (there here))))))
    dArg = ⊢monus dj dk
    dDesc = ⊢div-descend dj dk

⊢divStp : Γ₃ ⊢ divStp ∷ aStepT Nat ⌜Nat⌝ (var vz)
⊢divStp = ⊢lam ty-Nat (⊢natrec ⊢divMot ⊢divZ ⊢divS (⊢var here))

------------------------------------------------------------------------
-- ★★ THE USE SITE.  One `open`, and the instantiation data are three
--    ATOMS with three one-token derivations.
------------------------------------------------------------------------

open AmTΠ Γ₃ Nat ⌜Nat⌝ (var vz) divStp ty-Nat ⊢⌜Nat⌝ (⊢var here) ⊢divStp
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt; amrec-unfold-z )

divT : RTm ⌊ Γ₃ ⌋
divT = amrecTm

⊢divT : Γ₃ ⊢ divT ∷ Π Nat (El ⌜Nat⌝)
⊢divT = ⊢amrecΠ

-- ★ the pointwise form, with NO cast at the use site either.
⊢divT-at : {n : RTm ⌊ Γ₃ ⌋} → Γ₃ ⊢ n ∷ Nat →
           Γ₃ ⊢ app divT n ∷ subTy (single n) (El ⌜Nat⌝)
⊢divT-at dn = ⊢amrecPt dn
