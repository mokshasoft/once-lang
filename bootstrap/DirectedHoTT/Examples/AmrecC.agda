------------------------------------------------------------------------
-- OCP-0009 — ★★ MEASURE RECURSION, RE-PACKAGED.  `⊢amrec` with the data
-- as PARAMETERS and the conclusion Π-TYPED.
--
-- WHY.  `NbEPDirDBExamplesDogfood`'s `⊢amrec` cannot be applied.  Its
-- premise is `Γ₄ ⊢ x ∷ El cA` — `El` of a CONTEXT VARIABLE — and all four
-- of Γ₄'s slots CONSUME an `El cA` while none produces one, so no such
-- `x` exists.  Extending Γ₄ does not help either: the statement is fixed
-- AT Γ₄, so an extended context needs it re-derived.  `SpikeAmrecInst`
-- instantiates Γ₄ and confirms the other half — `sub-lemma` can only ever
-- supply CLOSED bounds, so the auxiliary cannot be re-used at `μ x` for a
-- bound `x` either.
--
-- ★ THE FIX IS TWO CHANGES, both to the STATEMENT, neither to the proof:
--
--   1. DATA AS PARAMETERS over an arbitrary ambient `Δ` (option C's `Lx`
--      style).  This is what makes the combinator CONTEXT-POLYMORPHIC,
--      and context-polymorphism is the property that was actually
--      missing — Π-vs-pointwise is downstream of it.
--   2. CONCLUSION Π-TYPED: a closed `Δ ⊢ amrecTm ∷ Π (El cA) …`, not a
--      pointwise `… → Δ ⊢ amrecTm x ∷ …`.
--
-- ★★ AND Π IS THE PRIMITIVE, not a matter of taste.  Two things in this
--   POC consume only TERMS, never Agda-level functions: a context SLOT
--   (the step slot is Π-typed, and `⊢lexrec`'s own branches already pass
--   `rec₁`/`rec₂` into `⊢app` as terms), and `sub-lemma` (a `σ` maps
--   variables to `RTm`s).  So the Π form must exist.  The pointwise form
--   is then ONE `⊢app` plus one `wk-single` away — see `⊢amrecPt` at the
--   bottom.  The converse does not hold without (1).
--
-- ⚠ The recursion, the `natrec` on the bound, and the `ordtr` descent are
--   Dogfood's, UNCHANGED.  Only the packaging moved.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AmrecC where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Lib.Wk using ( cong₄; nrs-w; ren-w; ren-w²; sub-w; sub-w²; w )
open import DirectedHoTT.Lib.Rec using ( rec1T; rec1T-ren; rec1T-sub )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Strong using ( ⊢le-refl; reflTm )
open import DirectedHoTT.Lib.Ord using ( ⊢strong-base'; ⊢strong-step )
-- ★ REUSE: the naturality kit built for lexrec is not lexrec-specific.
--   `rec1T` IS this combinator's IH type, and `sub-w`/`ren-w`/`cong₄` are
--   the whole toolkit.  Nothing new was needed here.
  using ( w; cong₄; sub-w; sub-w²; ren-w; ren-w²
        ; nrs-w; rec1T; rec1T-sub; rec1T-ren )

------------------------------------------------------------------------
-- THE TYPES, as combinators over the data.
------------------------------------------------------------------------

-- `(x : A) → μ x ≤ n → P x` — the bounded auxiliary's type.
aAuxB' : {Γ : Cx} (cA : RTm Γ) (m n : RTm (Γ ∙)) (cp : RTm ((Γ ∙) ∙)) → RTy Γ
aAuxB' cA m n cp =
  Π (El cA) (Π (Hom Nat (app m (var vz)) n) (El (app cp (var (vs vz)))))

aAuxB : {Γ : Cx} (cA cP μ n : RTm Γ) → RTy Γ
aAuxB cA cP μ n = aAuxB' cA (w μ) (w n) (w (w cP))

aAuxB-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (cA cP μ n : RTm Γ) →
            subTy σ (aAuxB cA cP μ n)
          ≡ aAuxB (subTm σ cA) (subTm σ cP) (subTm σ μ) (subTm σ n)
aAuxB-sub cA cP μ n = cong₄ aAuxB' refl (sub-w μ) (sub-w n) (sub-w² cP)

aAuxB-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ n : RTm Γ) →
            renTy ρ (aAuxB cA cP μ n)
          ≡ aAuxB (renTm ρ cA) (renTm ρ cP) (renTm ρ μ) (renTm ρ n)
aAuxB-ren cA cP μ n = cong₄ aAuxB' refl (ren-w μ) (ren-w n) (ren-w² cP)

-- `(x : A) → ((y : A) → μ y < μ x → P y) → P x` — the step's type.
--   ★ the IH slot is exactly lexrec's `rec1T`.
cong₃ : {A B C D : Set} (f : A → B → C → D)
        {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

-- pre-weakened, so `subTy`/`renTy` distribute into it by `refl`
aStepT' : {Γ : Cx} (cA : RTm Γ) (r : RTy (Γ ∙)) (cp : RTm ((Γ ∙) ∙)) → RTy Γ
aStepT' cA r cp = Π (El cA) (Π r (El (app cp (var (vs vz)))))

aStepT : {Γ : Cx} (cA cP μ : RTm Γ) → RTy Γ
aStepT cA cP μ = aStepT' cA (rec1T (w cA) (w cP) (w μ) (var vz)) (w (w cP))

aStepT-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ : RTm Γ) →
             renTy ρ (aStepT cA cP μ)
           ≡ aStepT (renTm ρ cA) (renTm ρ cP) (renTm ρ μ)
aStepT-ren cA cP μ =
  cong₃ aStepT' refl
    (trans (rec1T-ren (w cA) (w cP) (w μ) (var vz))
           (cong₄ rec1T (ren-w cA) (ren-w cP) (ren-w μ) refl))
    (ren-w² cP)

------------------------------------------------------------------------
-- THE COMBINATOR, over an arbitrary ambient context.
------------------------------------------------------------------------

module Am (Δ : Ctx) (cA cP μ stp : RTm ⌊ Δ ⌋)
          (dcA  : Δ ⊢ cA  ∷ U)
          (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
          (dμ   : Δ ⊢ μ   ∷ Π (El cA) Nat)
          (dstp : Δ ⊢ stp ∷ aStepT cA cP μ)
          where

  -- the natrec motive: the bound `n` is the recursion variable.
  aAuxMot : RTy (⌊ Δ ⌋ ∙)
  aAuxMot = aAuxB (w cA) (w cP) (w μ) (var vz)

  ⊢aAuxMot : (Δ ▹ Nat) ⊢ty aAuxMot
  ⊢aAuxMot =
    ty-Π (ty-El (⊢wk dcA))
      (ty-Π (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk dμ)) (⊢var here)) (⊢var (there here)))
            (ty-El (⊢app (⊢wk (⊢wk (⊢wk dcP))) (⊢var (there here)))))

  -- ★ the ⊢wk'd step, reassociated.  `⊢wk` leaves `renTy vs` OUTSIDE the
  --   combinator and Agda pushes it into the Π-chain instead; without
  --   this the spine's substitutions have nothing to cancel against.
  --   Exactly the obstruction the lexrec branches hit (`stp-w⁴` there).
  stp-w² : renTy vs (renTy vs (aStepT cA cP μ))
         ≡ aStepT (w (w cA)) (w (w cP)) (w (w μ))
  stp-w² = trans (cong (renTy vs) (aStepT-ren cA cP μ))
                 (aStepT-ren (w cA) (w cP) (w μ))

  stp-w⁴ : renTy vs (renTy vs (renTy vs (renTy vs (aStepT cA cP μ))))
         ≡ aStepT (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ))))
  stp-w⁴ =
    trans (cong (renTy vs) (cong (renTy vs) stp-w²))
          (trans (cong (renTy vs) (aStepT-ren (w (w cA)) (w (w cP)) (w (w μ))))
                 (aStepT-ren (w (w (w cA))) (w (w (w cP))) (w (w (w μ)))))

  ------------------------------------------------------------------------
  -- the two motive boundaries: `⊢natrec` demands the motive at `nzero`
  -- and at `nrs`, and the ⊢lams build the `aAuxB` form.
  ------------------------------------------------------------------------

  -- ★ the motive at ANY bound — `mot-z` is just its `nzero` instance, and
  --   the Π-form below needs it at `μ x`.
  mot-at : (n : RTm ⌊ Δ ⌋) → subTy (single n) aAuxMot ≡ aAuxB cA cP μ n
  mot-at n =
    trans (aAuxB-sub {σ = single n} (w cA) (w cP) (w μ) (var vz))
          (cong₄ aAuxB (wk-single {v = n} cA) (wk-single {v = n} cP)
                       (wk-single {v = n} μ) refl)

  mot-z : subTy (single nzero) aAuxMot ≡ aAuxB cA cP μ nzero
  mot-z = mot-at nzero

  mot-s : subTy nrs aAuxMot
        ≡ aAuxB (w (w cA)) (w (w cP)) (w (w μ)) (nsuc (var (vs vz)))
  mot-s =
    trans (aAuxB-sub {σ = nrs} (w cA) (w cP) (w μ) (var vz))
          (cong₄ aAuxB (nrs-w cA) (nrs-w cP) (nrs-w μ) refl)

  ------------------------------------------------------------------------
  -- n = 0: `μ x ≤ 0` kills every recursive call, so the IH is `absurd`.
  ------------------------------------------------------------------------

  ihZ : RTm (⌊ Δ ⌋ ∙ ∙)
  ihZ = lam (lam (absurd (app (w (w (w (w cP)))) (var (vs vz))) (ordtr (nsuc (app (w (w (w (w μ)))) (var (vs vz)))) (app (w (w (w (w μ)))) (var (vs (vs (vs vz))))) nzero (var vz) (var (vs (vs vz))))))

  aZBr : RTm ⌊ Δ ⌋
  aZBr = lam (lam (app (app (w (w stp)) (var (vs vz))) ihZ))

  ⊢ihZ : ((Δ ▹ El cA) ▹ Hom Nat (app (w μ) (var vz)) nzero)
           ⊢ ihZ ∷ rec1T (w (w cA)) (w (w cP)) (w (w μ)) (var (vs vz))
  ⊢ihZ =
    ⊢lam (ty-El (⊢wk (⊢wk dcA))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk dμ))) (⊢var here))) (⊢app (⊢wk (⊢wk (⊢wk dμ))) (⊢var (there (there here))))) (⊢strong-base' (⊢app (⊢wk (⊢wk (⊢wk (⊢wk dcP)))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk dμ)))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk dμ)))) (⊢var (there (there (there here))))) (⊢var here) (⊢var (there (there here)))))

  -- the IH argument's expected type is the `rec1T` slot already
  -- substituted by the argument before it.
  rec1-fitZ : subTy (single (var (vs vz))) (rec1T (w (w (w cA))) (w (w (w cP))) (w (w (w μ))) (var vz))
            ≡ rec1T (w (w cA)) (w (w cP)) (w (w μ)) (var (vs vz))
  rec1-fitZ =
    trans (rec1T-sub (w (w (w cA))) (w (w (w cP))) (w (w (w μ))) (var vz))
          (cong₄ rec1T (wk-single {v = var (vs vz)} (w (w cA)))
                       (wk-single {v = var (vs vz)} (w (w cP)))
                       (wk-single {v = var (vs vz)} (w (w μ))) refl)

  cPcancelZ : subTm (single ihZ) (subTm (extS (single (var (vs vz)))) (w (w (w (w cP)))))
            ≡ w (w cP)
  cPcancelZ =
    trans (cong (subTm (single ihZ))
                (trans (sub-w {σ = single (var (vs vz))} (w (w (w cP))))
                       (cong w (wk-single {v = var (vs vz)} (w (w cP))))))
          (wk-single {v = ihZ} (w (w cP)))

  ⊢aZBr : Δ ⊢ aZBr ∷ subTy (single nzero) aAuxMot
  ⊢aZBr =
    ⊢-cast (sym mot-z)
      (⊢lam (ty-El dcA) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk dμ) (⊢var here)) ⊢nzero) (⊢-cast (cong (λ z → El (app z (var (vs vz)))) cPcancelZ) (⊢app (⊢app (⊢-cast stp-w² (⊢wk (⊢wk dstp))) (⊢var (there here))) (⊢-cast (sym rec1-fitZ) ⊢ihZ)))))

  ------------------------------------------------------------------------
  -- n = suc n': the IH at n' is a CONTEXT VARIABLE, applied at `y`.  This
  -- is the branch where the recursion is real, and `⊢strong-step` is the
  -- descent: μ y < μ x and μ x ≤ suc n' give μ y ≤ n'.
  ------------------------------------------------------------------------

  -- ★ the IH's own type, reassociated: five ⊢wk's worth of `renTy` sitting
  --   outside the combinator.
  ihMot-w⁵ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (aAuxMot)))))
           ≡ aAuxB (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ)))))) (var (vs (vs (vs (vs (vs vz))))))
  ihMot-w⁵ =
    trans (cong (renTy vs) (cong (renTy vs) (cong (renTy vs) (cong (renTy vs) (aAuxB-ren (w cA) (w cP) (w μ) (var vz))))))
    (trans (cong (renTy vs) (cong (renTy vs) (cong (renTy vs) (aAuxB-ren (w (w cA)) (w (w cP)) (w (w μ)) (var (vs vz))))))
    (trans (cong (renTy vs) (cong (renTy vs) (aAuxB-ren (w (w (w cA))) (w (w (w cP))) (w (w (w μ))) (var (vs (vs vz))))))
    (trans (cong (renTy vs) (aAuxB-ren (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ)))) (var (vs (vs (vs vz))))))
           (aAuxB-ren (w (w (w (w (w cA))))) (w (w (w (w (w cP))))) (w (w (w (w (w μ))))) (var (vs (vs (vs (vs vz)))))))))

  ltS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)
  ltS = ordtr (nsuc (app (w (w (w (w (w (w μ)))))) (var (vs vz)))) (app (w (w (w (w (w (w μ)))))) (var (vs (vs (vs vz))))) (nsuc (var (vs (vs (vs (vs (vs vz))))))) (var vz) (var (vs (vs vz)))

  ihS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙)
  ihS = lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) ltS))

  aSBr : RTm (⌊ Δ ⌋ ∙ ∙)
  aSBr = lam (lam (app (app (w (w (w (w stp)))) (var (vs vz))) ihS))

  -- the IH spine's two fits
  μ-fitS : subTm (single (var (vs vz))) (w (w (w (w (w (w (w μ))))))) ≡ (w (w (w (w (w (w μ))))))
  μ-fitS = wk-single {v = (var (vs vz))} (w (w (w (w (w (w μ))))))

  cP-fitS : subTm (single ltS) (subTm (extS (single (var (vs vz)))) (w (w (w (w (w (w (w (w cP))))))))) ≡ (w (w (w (w (w (w cP))))))
  cP-fitS =
    trans (cong (subTm (single ltS))
                (trans (sub-w {σ = single (var (vs vz))} (w (w (w (w (w (w (w cP))))))))
                       (cong w (wk-single {v = (var (vs vz))} (w (w (w (w (w (w cP))))))))))
          (wk-single {v = ltS} (w (w (w (w (w (w cP)))))))

  ⊢ihS : ((((Δ ▹ Nat) ▹ aAuxMot) ▹ El (w (w cA)))
            ▹ Hom Nat (app (w (w (w μ))) (var vz)) (nsuc (var (vs (vs vz)))))
           ⊢ ihS ∷ rec1T (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ)))) (var (vs vz))
  ⊢ihS =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk dcA))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ))))) (⊢var here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ))))) (⊢var (there (there here))))) (⊢-cast (cong (λ z → El (app z (var (vs vz)))) cP-fitS) (⊢app (⊢app (⊢-cast ihMot-w⁵ (⊢var (there (there (there (there here)))))) (⊢var (there here))) (⊢-cast (sym (cong (λ z → Hom Nat (app z (var (vs vz))) (var (vs (vs (vs (vs (vs vz))))))) μ-fitS)) (⊢strong-step (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ)))))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ)))))) (⊢var (there (there (there here))))) (⊢var (there (there (there (there (there here)))))) (⊢var here) (⊢var (there (there here))))))))

  rec1-fitS : subTy (single (var (vs vz))) (rec1T (w (w (w (w (w cA))))) (w (w (w (w (w cP))))) (w (w (w (w (w μ))))) (var vz))
            ≡ rec1T (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ)))) (var (vs vz))
  rec1-fitS =
    trans (rec1T-sub (w (w (w (w (w cA))))) (w (w (w (w (w cP))))) (w (w (w (w (w μ))))) (var vz))
          (cong₄ rec1T (wk-single {v = (var (vs vz))} (w (w (w (w cA))))) (wk-single {v = (var (vs vz))} (w (w (w (w cP)))))
                       (wk-single {v = (var (vs vz))} (w (w (w (w μ))))) refl)

  cPcancelS : subTm (single ihS) (subTm (extS (single (var (vs vz)))) (w (w (w (w (w (w cP))))))) ≡ (w (w (w (w cP))))
  cPcancelS =
    trans (cong (subTm (single ihS))
                (trans (sub-w {σ = single (var (vs vz))} (w (w (w (w (w cP))))))
                       (cong w (wk-single {v = (var (vs vz))} (w (w (w (w cP))))))))
          (wk-single {v = ihS} (w (w (w (w cP)))))

  ⊢aSBr : ((Δ ▹ Nat) ▹ aAuxMot) ⊢ aSBr ∷ subTy nrs aAuxMot
  ⊢aSBr =
    ⊢-cast (sym mot-s)
      (⊢lam (ty-El (⊢wk (⊢wk dcA))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk dμ))) (⊢var here)) (⊢nsuc (⊢var (there (there here))))) (⊢-cast (cong (λ z → El (app z (var (vs vz)))) cPcancelS) (⊢app (⊢app (⊢-cast stp-w⁴ (⊢wk (⊢wk (⊢wk (⊢wk dstp))))) (⊢var (there here))) (⊢-cast (sym rec1-fitS) ⊢ihS)))))

  aAuxTm : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  aAuxTm n = natrec aZBr aSBr n

  -- ★ the bounded auxiliary, at an arbitrary bound.
  ⊢aAux : {n : RTm ⌊ Δ ⌋} → Δ ⊢ n ∷ Nat →
          Δ ⊢ aAuxTm n ∷ subTy (single n) aAuxMot
  ⊢aAux dn = ⊢natrec ⊢aAuxMot ⊢aZBr ⊢aSBr dn

------------------------------------------------------------------------
-- ★★★ THE COMBINATOR ITSELF, Π-TYPED.
--
-- `Am` is instantiated at `Δ ▹ El cA` — i.e. the module APPLIES TO ITSELF
-- at a deeper context, which is exactly what parameterising over `Δ` buys
-- and what the `Γ₄` packaging made impossible.  The step's type needs one
-- cast on the way in (`aStepT-ren`); everything else is `⊢wk`.
------------------------------------------------------------------------

module AmΠ (Δ : Ctx) (cA cP μ stp : RTm ⌊ Δ ⌋)
           (dcA  : Δ ⊢ cA  ∷ U)
           (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
           (dμ   : Δ ⊢ μ   ∷ Π (El cA) Nat)
           (dstp : Δ ⊢ stp ∷ aStepT cA cP μ)
           where

  open Am (Δ ▹ El cA) (w cA) (w cP) (w μ) (w stp)
          (⊢wk dcA) (⊢wk dcP) (⊢wk dμ)
          (⊢-cast (aStepT-ren cA cP μ) (⊢wk dstp))

  -- the bound is the measure AT the bound variable: `μ x`.
  μx : RTm (⌊ Δ ⌋ ∙)
  μx = app (w μ) (var vz)

  dμx : (Δ ▹ El cA) ⊢ μx ∷ Nat
  dμx = ⊢app (⊢wk dμ) (⊢var here)

  amrecTm : RTm ⌊ Δ ⌋
  amrecTm = lam (app (app (aAuxTm μx) (var vz)) (reflTm μx))

  -- the spine's two substitutions, w³ cP → w cP
  cP-fit : subTm (single (reflTm μx))
             (subTm (extS (single (var vz))) (w (w (w cP))))
         ≡ w cP
  cP-fit =
    trans (cong (subTm (single (reflTm μx)))
                (trans (sub-w {σ = single (var vz)} (w (w cP)))
                       (cong w (wk-single {v = var vz} (w cP)))))
          (wk-single {v = reflTm μx} (w cP))

  -- the ⊢le-refl argument's expected type is the `≤` slot already
  -- substituted by `x`; both components peel with `wk-single`.
  le-fit : subTy (single (var vz)) (Hom Nat (app (w (w μ)) (var vz)) (w μx))
         ≡ Hom Nat μx μx
  le-fit = cong₂ (λ m u → Hom Nat (app m (var vz)) u)
                 (wk-single {v = var vz} (w μ))
                 (wk-single {v = var vz} μx)

  -- ★★ THE Π FORM.  A closed term of a Π type — so it can be handed to a
  --    context SLOT, substituted by `sub-lemma`, or applied.
  ⊢amrecΠ : Δ ⊢ amrecTm ∷ Π (El cA) (El (app (w cP) (var vz)))
  ⊢amrecΠ =
    ⊢lam (ty-El dcA)
      (⊢-cast (cong (λ z → El (app z (var vz))) cP-fit)
        (⊢app (⊢app (⊢-cast (mot-at μx) (⊢aAux dμx)) (⊢var here))
              (⊢-cast (sym le-fit) (⊢le-refl dμx))))

  -- ★ …and the POINTWISE form, DERIVED.  One ⊢app, one wk-single.
  --   This is the direction that works; the converse needs the statement
  --   to be context-polymorphic, which the Γ₄ packaging was not.
  ⊢amrecPt : {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ El cA →
             Δ ⊢ app amrecTm x ∷ El (app cP x)
  ⊢amrecPt {x = x} dx =
    ⊢-cast (cong (λ z → El (app z x)) (wk-single {v = x} cP))
           (⊢app ⊢amrecΠ dx)
