------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (0,0) at an ABSTRACT AMBIENT CONTEXT.
--
-- Option C: there is no Γ₅.  `Δ`, the carrier, the motive, the measures
-- and the step are all PARAMETERS.  See NbEPDirDBExamplesLexC.
--
-- ★ 9.5 s / 0.96 GB, against 20.7 s / 2.22 GB for the same branch under
--   option B (NbEPDirDBExamplesLexZZ).  2.2× faster, 2.3× lighter, WITH
--   the transports included — which is the number SPIKE-COST §8 warned was
--   unmeasured, because SpikeCostS13 was a LEAF and never crossed a motive
--   boundary.  It survives.
--
-- ★★ AND THE EXPENSIVE HALF IS FREE.  Both recursor derivations — the ones
--   that cost 2–5 GB under Γ₅ — needed NO transports at all.  Every cast
--   below is in the ASSEMBLY, which is the cheap module.  That is the right
--   way round, and it is why option C is worth the plumbing.
--
-- THE FOUR CASTS, in the order the other branches will hit them:
--   `M0lex-sub`  the motive boundary — `subTy (single nzero) M0lex` vs the
--                `auxBody` form the ⊢lams build.  auxBody-sub + wk-single.
--   `stp-w⁴`     Agda pushes `renTy vs⁴ (lStepT …)` INTO the Π-chain rather
--                than reassociating it, so cP arrives as
--                `renTm (extR³ vs)ⁿ (w³ cP)` and nothing cancels.  ⊢-cast
--                through `lStepT-ren`, one level at a time.
--   `rec1-fit` / `rec2-fit`   each ⊢app argument's expected type is the
--                `lStepT` slot ALREADY SUBSTITUTED by the arguments before
--                it.  rec₂'s inner substitution is UNDER A BINDER, so it
--                peels with `sub-w`; the outer one with `wk-single`.
--   `cPcancel`   the spine's three substitutions, w⁷ cP → w⁴ cP.
--
-- ⚠ PIN `wk-single`'s IMPLICIT `{v = …}`.  It is the term being
--   substituted and it DIFFERS per step — x, then rec₁, then rec₂.  Agda
--   cannot always infer it, and when it guesses wrong the error points at
--   the lemma rather than at the guess.  This cost two rounds.
--
-- BOTH obligations are vacuous at (0,0): `rec₁` gets μ₁ y < μ₁ x ≤ 0 and
-- `rec₂` gets μ₂ y < μ₂ x ≤ 0, so each is `ordtr` into `⊢strong-base'`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexCZZ where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Ord using ( ⊢strong-base' )
open import DirectedHoTT.Negative.LexC

module _ (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂)
         where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  -- ctx: vz = lt, vs = le, vs² = x, vs³ = n₂, then Δ
  ΓZZ : Ctx
  ΓZZ =
    (((Δ ▹ Nat) ▹ El (w cA))
       ▹ Hom Nat (app (w (w μ₁)) (var vz)) nzero)
       ▹ Hom Nat (app (w (w (w μ₂))) (var (vs vz))) nzero

  lexZZrec1 : RTm ⌊ ΓZZ ⌋
  lexZZrec1 =
    lam (lam (absurd (app (w (w (w (w (w (w (cP))))))) (var (vs vz))) (ordtr (nsuc (app (w (w (w (w (w (w (μ₁))))))) (var (vs vz)))) (app (w (w (w (w (w (w (μ₁))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

  lexZZrec2 : RTm ⌊ ΓZZ ⌋
  lexZZrec2 =
    lam (lam (lam (absurd (app (w (w (w (w (w (w (w (cP)))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (w (w (w (w (w (w (w (μ₂)))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (μ₂)))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))

  ⊢lexZZrec1 : ΓZZ ⊢ lexZZrec1
             ∷ rec1T (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ₁))))
                     (var (vs (vs vz)))
  ⊢lexZZrec1 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (dcA)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₁)))))) (⊢var here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₁)))))) (⊢var (there (there (there here)))))) (⊢strong-base' (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dcP))))))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₁))))))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₁))))))) (⊢var (there (there (there (there here)))))) (⊢var here) (⊢var (there (there (there here))))))

  ⊢lexZZrec2 : ΓZZ ⊢ lexZZrec2
             ∷ rec2T (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ₁))))
                     (w (w (w (w μ₂)))) (var (vs (vs vz)))
  ⊢lexZZrec2 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (dcA)))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₁)))))) (⊢var here)) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₁)))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₂))))))) (⊢var (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₂))))))) (⊢var (there (there (there (there here))))))) (⊢strong-base' (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dcP)))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₂)))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₂)))))))) (⊢var (there (there (there (there (there here))))))) (⊢var here) (⊢var (there (there (there here)))))))

  ------------------------------------------------------------------------
  -- ★ THE MOTIVE BOUNDARY.  `⊢natrec` will demand `subTy (single nzero)
  --   M0lex`; the three `⊢lam`s naturally build the `auxBody` form.  With
  --   Γ₅ these were the same term up to computation; with abstract data
  --   they are only PROPOSITIONALLY equal, which is what the kit is for.
  ------------------------------------------------------------------------

  M0lex-sub : subTy (single nzero) M0lex
            ≡ auxBody (w cA) (w cP) (w μ₁) (w μ₂) nzero nzero
  M0lex-sub =
    trans (auxBody-sub (w (w cA)) (w (w cP)) (w (w μ₁)) (w (w μ₂)) nzero (var vz))
          (cong₆ auxBody (wk-single (w cA)) (wk-single (w cP))
                         (wk-single (w μ₁)) (wk-single (w μ₂)) refl refl)


  -- ★ reassociate `renTy vs⁴ (lStepT …)` into `lStepT (w⁴ …)`, one level at
  --   a time, so the ⊢app spine's substitutions have something to cancel.
  stp-w⁴ : renTy vs (renTy vs (renTy vs (renTy vs (lStepT cA cP μ₁ μ₂))))
         ≡ lStepT (w (w (w (w (cA))))) (w (w (w (w (cP))))) (w (w (w (w (μ₁))))) (w (w (w (w (μ₂)))))
  stp-w⁴ =
    trans (cong (renTy vs) (cong (renTy vs) (cong (renTy vs) (lStepT-ren cA cP μ₁ μ₂))))
    (trans (cong (renTy vs) (cong (renTy vs) (lStepT-ren (w (cA)) (w (cP)) (w (μ₁)) (w (μ₂)))))
    (trans (cong (renTy vs) (lStepT-ren (w (w (cA))) (w (w (cP))) (w (w (μ₁))) (w (w (μ₂)))))
           (lStepT-ren (w (w (w (cA)))) (w (w (w (cP)))) (w (w (w (μ₁)))) (w (w (w (μ₂)))))))


  -- ★ the ⊢app spine substitutes three times; each cancels one weakening,
  --   w⁷ cP → w⁴ cP.  With Γ₅ this computed; here it is `sub-w`/`wk-single`.
  cPcancel : subTm (single lexZZrec2)
               (subTm (extS (single lexZZrec1))
                 (subTm (extS (extS (single (var (vs (vs vz)))))) (w (w (w (w (w (w (w (cP))))))))))
           ≡ (w (w (w (w (cP)))))
  cPcancel =
    trans (cong (λ z → subTm (single lexZZrec2) (subTm (extS (single lexZZrec1)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (w (w (w (w (w (cP)))))))
                       (cong (λ z → w (w z)) (wk-single {v = var (vs (vs vz))} (w (w (w (w (cP)))))))))
    (trans (cong (subTm (single lexZZrec2))
                 (trans (sub-w {σ = single lexZZrec1} (w (w (w (w (w (cP)))))))
                        (cong w (wk-single {v = lexZZrec1} (w (w (w (w (cP)))))))))
           (wk-single {v = lexZZrec2} (w (w (w (w (cP)))))))


  ------------------------------------------------------------------------
  -- ★ THE FITTING LEMMAS.  Each ⊢app argument's expected type is the
  --   `lStepT` slot ALREADY SUBSTITUTED by the arguments before it, so the
  --   recursor derivations — which are stated in the clean `w⁴` form —
  --   have to be cast into it.  With Γ₅ this was definitional.
  ------------------------------------------------------------------------

  rec1-fit : subTy (single (var (vs (vs vz)))) (rec1T (w (w (w (w (w (cA)))))) (w (w (w (w (w (cP)))))) (w (w (w (w (w (μ₁)))))) (var vz))
           ≡ rec1T (w (w (w (w (cA))))) (w (w (w (w (cP))))) (w (w (w (w (μ₁))))) (var (vs (vs vz)))
  rec1-fit =
    trans (rec1T-sub (w (w (w (w (w (cA)))))) (w (w (w (w (w (cP)))))) (w (w (w (w (w (μ₁)))))) (var vz))
          (cong₄ rec1T (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (cA)))))) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (cP))))))
                       (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (μ₁)))))) refl)

  -- two substitutions this time: the inner one is UNDER A BINDER, so it
  -- peels with `sub-w`; the outer one with `wk-single`.
  rec2-fit : subTy (single lexZZrec1)
               (subTy (extS (single (var (vs (vs vz)))))
                 (rec2T (w (w (w (w (w (w (cA))))))) (w (w (w (w (w (w (cP))))))) (w (w (w (w (w (w (μ₁))))))) (w (w (w (w (w (w (μ₂))))))) (var (vs vz))))
           ≡ rec2T (w (w (w (w (cA))))) (w (w (w (w (cP))))) (w (w (w (w (μ₁))))) (w (w (w (w (μ₂))))) (var (vs (vs vz)))
  rec2-fit =
    trans (cong (subTy (single lexZZrec1))
            (trans (rec2T-sub (w (w (w (w (w (w (cA))))))) (w (w (w (w (w (w (cP))))))) (w (w (w (w (w (w (μ₁))))))) (w (w (w (w (w (w (μ₂))))))) (var (vs vz)))
                   (cong₅ rec2T (trans (sub-w (w (w (w (w (w (cA))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (cA))))))))
                                (trans (sub-w (w (w (w (w (w (cP))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (cP))))))))
                                (trans (sub-w (w (w (w (w (w (μ₁))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (μ₁))))))))
                                (trans (sub-w (w (w (w (w (w (μ₂))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (μ₂))))))))
                                refl)))
          (trans (rec2T-sub (w (w (w (w (w (cA)))))) (w (w (w (w (w (cP)))))) (w (w (w (w (w (μ₁)))))) (w (w (w (w (w (μ₂)))))) (w (var (vs (vs vz)))))
                 (cong₅ rec2T (wk-single {v = lexZZrec1} (w (w (w (w (cA)))))) (wk-single {v = lexZZrec1} (w (w (w (w (cP))))))
                              (wk-single {v = lexZZrec1} (w (w (w (w (μ₁)))))) (wk-single {v = lexZZrec1} (w (w (w (w (μ₂))))))
                              (wk-single {v = lexZZrec1} (var (vs (vs vz))))))

  ⊢lexZZ : (Δ ▹ Nat) ⊢ lexZZ ∷ subTy (single nzero) M0lex
  ⊢lexZZ =
    ⊢-cast (sym M0lex-sub)
      (⊢lam (ty-El (⊢wk (dcA))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (dμ₁))) (⊢var here)) ⊢nzero) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (dμ₂)))) (⊢var (there here))) ⊢nzero) (⊢-cast (cong (λ z → El (app z (var (vs (vs vz))))) cPcancel) (⊢app (⊢app (⊢app (⊢-cast stp-w⁴ (⊢wk (⊢wk (⊢wk (⊢wk dstp))))) (⊢var (there (there here)))) (⊢-cast (sym rec1-fit) ⊢lexZZrec1)) (⊢-cast (sym rec2-fit) ⊢lexZZrec2))))))
