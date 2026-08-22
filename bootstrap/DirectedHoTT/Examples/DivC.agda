-- OCP-0009 · EXAMPLES — `⊢amrecΠ` AT THE ℕ CARRIER — THE PLUMBING.
--
-- ⚠ PROMOTED FROM A SPIKE 2026-08-21.  Standing rule: finished library AND
--   finished EXAMPLES material does not live in a `Spike*` module.
--
-- ⚠⚠ AND IT WAS NOT MERELY MISNAMED — IT WAS UNGUARDED.  `sweep.sh` gathers
--   `Spike*` as PROBES and, at target `all` (kernel + libs + examples),
--   does not build them at all.  This file was green when moved, but
--   nothing had been checking that.  ⇒ a result kept in a Spike is a result
--   nobody is watching.
--
-- ★ FIRST USE SITE of the re-packaged combinator.  `div` is chosen over
--   `gcd` deliberately: `⊢div` ALREADY EXISTS built raw from nested
--   `natrec` (NbEPDirDBExamplesDiv), so building the same function
--   through `⊢amrecΠ` is a same-function A/B.  gcd has no raw
--   counterpart and could only show that the abstraction WORKS, not that
--   it is BETTER.
--
-- THIS FILE IS THE PLUMBING ONLY: it wires the ℕ-carrier instantiation
-- into `AmΠ` with a TRIVIAL step (constant zero), to establish that the
-- use site costs nothing before the real `div` step goes in.  What it
-- measures is exactly the boilerplate a caller pays.
--
-- ⚠ THE STEP IS THE ONLY CONTENT.  Everything the bounded auxiliary used
--   to require — divAuxMot/divZBr/divInnerMot/divSBr/⊢divAux — is now
--   supplied by `⊢amrecΠ`.  What is left is the algorithm itself: split
--   the dividend, test `m ∸ k`, recurse once with `⊢div-descend`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.DivC where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Lib.Wk using ( w )
open import DirectedHoTT.Lib.Rec using ( rec1T )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; natrec; lam; app
        ; Π; renTy; renTm; subTy; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⟶*_; done; step; natrec-zero; ξ-appˡ
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π
        ; _≅ᵀ_; csymᵀ; ctrnᵀ
        ; _⟶_; β; ξ-nsuc; ξ-Homˡ; ξ-Homʳ )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ )
open import DirectedHoTT.Lib.Monus
  using ( monusTm; ⊢monus )
open import DirectedHoTT.Examples.Div
  using ( monusStep; ⊢div-descend )
open import DirectedHoTT.Lib.Strong using ( reflTm )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.AmrecC using ( aStepT; module AmΠ )
-- ★ the ℕ-carrier instantiation package, reused verbatim from the
--   instantiation spike — the data are CONTEXT-POLYMORPHIC, so the same
--   four terms and derivations serve at any Δ.
open import DirectedHoTT.Examples.AmrecInst
  using ( cAt; cPt; μt; dcA; dcP; dμ; elNat; elCP )

-- the ambient context: the divisor's predecessor `k`, exactly `Γ₃` in
-- NbEPDirDBExamplesDiv, so the comparison is like-for-like.
Γ₃ : Ctx
Γ₃ = ◇ ▹ Nat

------------------------------------------------------------------------
-- ★ THE IH TYPE IS WELL-FORMED.  Note `w μt ≡ μt` DEFINITIONALLY — the
--   instantiation data are CLOSED, so weakening is the identity on them
--   and `dμ`/`dcP` apply at every depth with no ⊢wk and no cast.  That
--   is the pay-off of making them context-polymorphic.
------------------------------------------------------------------------

-- ★ ONE lemma covers every IH type the file needs, at any `x`.
⊢ihTat : {Γ : Ctx} {x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ El cAt → Γ ⊢ty rec1T cAt cPt μt x
⊢ihTat dx =
  ty-Π (ty-El dcA)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢app dμ (⊢var here))) (⊢app dμ (⊢wk dx)))
          (ty-El (⊢app dcP (⊢var (there here)))))

-- `nzero` and `nsuc _` as carrier elements: the carrier IS ℕ, one conv.
asA : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El cAt
asA dt = ⊢conv dt (csymᵀ elNat)

⊢ihT : {Γ : Ctx} → (Γ ▹ El cAt) ⊢ty rec1T cAt cPt μt (var vz)
⊢ihT = ⊢ihTat (⊢var here)

------------------------------------------------------------------------
-- ★ THE β TAX, in full.  The instantiated measure is `lam (var vz)`, so
--   `app μt t` is a β-REDEX, not `t`.  Two named conversions cover every
--   use, and they are the only cost the ℕ-carrier package imposes.
------------------------------------------------------------------------

homμ : {Γ : Cx} (a b : RTm Γ) →
       Hom Nat (nsuc (app μt a)) (app μt b) ≅ᵀ Hom Nat (nsuc a) b
homμ a b =
  red→≅ᵀ (stepᵀ (ξ-Homˡ (ξ-nsuc (β (var vz) a)))
                (stepᵀ (ξ-Homʳ (β (var vz) b)) doneᵀ))

------------------------------------------------------------------------
-- THE STEP — the whole of `div`.
--
--   div m = case m of
--     0     → 0
--     suc j → case (suc j) ∸ k of        -- k is the divisor's predecessor
--       0     → 0                        -- suc j < suc k
--       suc _ → suc (ih (j ∸ k) ⊢div-descend)
--
-- ⚠ THE DIVIDEND MUST BE SPLIT FIRST, before the test: the descent
--   `j ∸ k < suc j` holds UNCONDITIONALLY once `m = suc j` is known,
--   whereas `m ∸ suc k < m` needs `m > 0`, which the test does not give
--   in a form the types can use.  Same reason `⊢div` splits first.
--
-- ★ THE MOTIVE ABSTRACTS THE IH.  `ih`'s type mentions `x`, so splitting
--   `x` must carry it: the motive is `λ x. IH(x) → P x`, and the branches
--   take the IH as an argument.  This is `⊢div`'s own trick (there it
--   carried the `≤` premise) and needs nothing new.
------------------------------------------------------------------------

divMot : RTy (⌊ Γ₃ ⌋ ∙ ∙)
divMot = Π (rec1T cAt cPt μt (var vz)) (El (app cPt (var (vs vz))))

⊢divMot : ((Γ₃ ▹ El cAt) ▹ Nat) ⊢ty divMot
⊢divMot =
  ty-Π (ty-Π (ty-El dcA)
             (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢app dμ (⊢var here)))
                                  (⊢app dμ (⊢conv (⊢var (there here)) (csymᵀ elNat))))
                   (ty-El (⊢app dcP (⊢var (there here))))))
       (ty-El (⊢app dcP (⊢conv (⊢var (there here)) (csymᵀ elNat))))

-- m = 0: the quotient is 0, and the IH is discarded.
divZ : RTm (⌊ Γ₃ ⌋ ∙)
divZ = lam nzero

⊢divZ : (Γ₃ ▹ El cAt) ⊢ divZ ∷ subTy (single nzero) divMot
⊢divZ = ⊢lam (⊢ihTat (asA ⊢nzero)) (⊢conv ⊢nzero (csymᵀ (elCP nzero)))

-- m = suc j: test, then one recursive call at `j ∸ k`.
divS : RTm (⌊ Γ₃ ⌋ ∙ ∙ ∙)
divS =
  lam (natrec nzero
        (nsuc (app (app (var (vs (vs vz))) (monusTm (var (vs (vs (vs (vs vz))))) (var (vs (vs (vs (vs (vs (vs vz)))))))))
                   (natrec (reflTm (var (vs (vs (vs (vs vz)))))) (monusStep (vs (vs (vs (vs vz))))) (var (vs (vs (vs (vs (vs (vs vz))))))))))
        (monusTm (nsuc (var (vs (vs vz)))) (var (vs (vs (vs (vs vz)))))))

-- the inner test's motive is CONSTANT in the test variable — the result
-- is `P (suc j)` either way.
divSMot : RTy (⌊ Γ₃ ⌋ ∙ ∙ ∙ ∙ ∙)
divSMot = El (app cPt (nsuc (var (vs (vs (vs vz))))))

⊢divSMot : (((((Γ₃ ▹ El cAt) ▹ Nat) ▹ divMot)
              ▹ rec1T cAt cPt μt (nsuc (var (vs vz)))) ▹ Nat) ⊢ty divSMot
⊢divSMot =
  ty-El (⊢app dcP (⊢conv (⊢nsuc (⊢var (there (there (there here))))) (csymᵀ elNat)))

⊢divS : (((Γ₃ ▹ El cAt) ▹ Nat) ▹ divMot) ⊢ divS ∷ subTy nrs divMot
⊢divS =
  ⊢lam ⊢ihTS
    (⊢natrec ⊢divSMot
      (⊢conv ⊢nzero (csymᵀ (elCP (nsuc (var (vs (vs vz)))))))
      (⊢conv (⊢nsuc (⊢conv (⊢app (⊢app (⊢var (there (there here))) dArg) dDesc)
                           (elCP (monusTm (var (vs (vs (vs (vs vz)))))
                                          (var (vs (vs (vs (vs (vs (vs vz)))))))))))
             (csymᵀ (elCP (nsuc (var (vs (vs (vs (vs vz))))))))) 
      (⊢monus (⊢nsuc (⊢var (there (there here)))) (⊢var (there (there (there (there here)))))))
  where
    ⊢ihTS = ⊢ihTat (asA (⊢nsuc (⊢var (there here))))
    dj = ⊢var (there (there (there (there here))))
    dk = ⊢var (there (there (there (there (there (there here))))))
    dArg = asA (⊢monus dj dk)
    dDesc =
      ⊢conv (⊢div-descend dj dk)
            (csymᵀ (homμ (monusTm (var (vs (vs (vs (vs vz))))) (var (vs (vs (vs (vs (vs (vs vz))))))))
                         (nsuc (var (vs (vs (vs (vs vz))))))))

divStp : RTm ⌊ Γ₃ ⌋
divStp = lam (natrec divZ divS (var vz))

⊢divStp : Γ₃ ⊢ divStp ∷ aStepT cAt cPt μt
⊢divStp =
  ⊢lam (ty-El dcA)
    (⊢natrec ⊢divMot ⊢divZ ⊢divS (⊢conv (⊢var here) elNat))

------------------------------------------------------------------------
-- ★★ THE USE SITE.  One `open`, and the recursor exists as a CLOSED
--    Π-typed term, plus the pointwise form, both for free.
------------------------------------------------------------------------

open AmΠ Γ₃ cAt cPt μt divStp dcA dcP dμ ⊢divStp
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt )

-- the recursor, as a term of a Π type
divC : RTm ⌊ Γ₃ ⌋
divC = amrecTm

⊢divC : Γ₃ ⊢ divC ∷ Π (El cAt) (El (app (w cPt) (var vz)))
⊢divC = ⊢amrecΠ

-- …and applied at a concrete argument, via the DERIVED pointwise form.
⊢divC-at : {m : RTm ⌊ Γ₃ ⌋} → Γ₃ ⊢ m ∷ El cAt →
           Γ₃ ⊢ app divC m ∷ El (app cPt m)
⊢divC-at dm = ⊢amrecPt dm

------------------------------------------------------------------------
-- ★★ AND IT COMPUTES.  Type-correct is not the same as "is div" — this
--    session found `⊢gcd-descend` certifying a recursion that is NOT gcd,
--    so the same standard applies here.
--
-- ⚠ NOTE: the RAW `⊢div` has never been evaluated either.  There is no
--   `div-computes` anywhere in the POC — only `monus-computes` — so
--   ARCHITECTURE's "a closed, well-typed DIVISION" rests on types alone,
--   exactly the standard this file used to meet.  The debt was the
--   project's, not just this file's.
------------------------------------------------------------------------

-- the step's ZERO equation: `div 0 = 0`, whatever the IH is.
div-step-zero : (ih : RTm ⌊ Γ₃ ⌋) → app (app divStp nzero) ih ⟶* nzero
div-step-zero ih =
  step (ξ-appˡ (β _ nzero))
    (step (ξ-appˡ (natrec-zero _ _))
      (step (β _ ih) done))

-- ★ END TO END, through `⊢amrecΠ`'s whole machinery: the outer lam, the
--   measure's β-redex, the bounded auxiliary's `natrec` on the bound, the
--   zero branch, and the step.  `div 0 ⟶* 0`.
divC-computes-zero : app divC nzero ⟶* nzero
divC-computes-zero =
  step (β _ nzero)
    (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-natrecⁿ (step (β _ nzero) done))))
      (⟶*-trans (⟶*-appˡ (⟶*-appˡ (step (natrec-zero _ _) done)))
        (⟶*-trans (⟶*-appˡ (step (β _ nzero) done))
          (step (β _ _) (div-step-zero _)))))
