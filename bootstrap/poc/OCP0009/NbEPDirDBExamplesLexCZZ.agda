------------------------------------------------------------------------
-- ⚠⚠ WORK IN PROGRESS — THIS FILE DOES NOT COMPILE YET, DELIBERATELY.
--   It is `#10`'s first branch, checkpointed mid-flight because the shape
--   of the remaining work is now known exactly and is worth recording.
--   Everything ABOVE `⊢lexZZ` is green; only the assembly is open.
--   ⚠ Do not "fix" this in a sweep — see HANDOFF-2026-08-07 §5.
--
-- WHAT IS ALREADY WORKING HERE (each was an obstruction, each is closed):
--   * both recursor derivations, ported by `renum.py` in OPTION_C mode —
--     these are the EXPENSIVE ones and they needed NO transports at all,
--     exactly as SpikeCostS13 predicted;
--   * `M0lex-sub`, the motive boundary, via `auxBody-sub` + `wk-single`;
--   * `stp-w⁴`, reassociating `renTy vs⁴ (lStepT …)` into `lStepT (w⁴ …)`
--     via `lStepT-ren` — without it the motive arrives as
--     `renTm (extR³ vs)ⁿ (w³ cP)` and nothing cancels;
--   * `cPcancel`, the three ⊢app substitutions peeling w⁷ cP → w⁴ cP.
--
-- ★ WHAT IS LEFT: one FITTING LEMMA per ⊢app argument, because each
--   argument's expected type is the lStepT slot already substituted:
--
--     rec1-fit : subTy (single x) (rec1T (w⁵ cA) (w⁵ cP) (w⁵ μ₁) (var vz))
--              ≡ rec1T (w⁴ cA) (w⁴ cP) (w⁴ μ₁) x
--     rec1-fit = trans (rec1T-sub …)
--                      (cong₄ rec1T (wk-single (w⁴ cA)) (wk-single (w⁴ cP))
--                                   (wk-single (w⁴ μ₁)) refl)
--
--     rec2-fit : subTy (single rec₁) (subTy (extS (single x)) (rec2T (w⁶ …)))
--              ≡ rec2T (w⁴ cA) (w⁴ cP) (w⁴ μ₁) (w⁴ μ₂) x
--       — same shape, `rec2T-sub` twice: the inner substitution peels with
--         `sub-w` (it is under a binder), the outer with `wk-single`.
--
--   Then `⊢-cast (sym rec1-fit)` / `⊢-cast (sym rec2-fit)` at the two
--   argument positions and (0,0) closes.  The other three branches and
--   LexAsm are the same recipe with different weakening counts.
--
------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (0,0) at an ABSTRACT AMBIENT CONTEXT.
--
-- Option C: there is no Γ₅.  `Δ`, the carrier, the motive, the measures
-- and the step are all PARAMETERS.  See NbEPDirDBExamplesLexC.
--
-- BOTH obligations are vacuous at (0,0): `rec₁` gets μ₁ y < μ₁ x ≤ 0 and
-- `rec₂` gets μ₂ y < μ₂ x ≤ 0, so each is `ordtr` into `⊢strong-base'`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCZZ where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base' )
open import poc.OCP0009.NbEPDirDBExamplesLexC

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
                (trans (sub-w² (w (w (w (w (w (cP))))))) (cong (λ z → w (w z)) (wk-single (w (w (w (w (cP)))))))))
    (trans (cong (subTm (single lexZZrec2))
                 (trans (sub-w (w (w (w (w (w (cP))))))) (cong w (wk-single (w (w (w (w (cP)))))))))
           (wk-single (w (w (w (w (cP)))))))

  ⊢lexZZ : (Δ ▹ Nat) ⊢ lexZZ ∷ subTy (single nzero) M0lex
  ⊢lexZZ =
    ⊢-cast (sym M0lex-sub)
      (⊢lam (ty-El (⊢wk (dcA))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (dμ₁))) (⊢var here)) ⊢nzero) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (dμ₂)))) (⊢var (there here))) ⊢nzero) (⊢-cast (cong (λ z → El (app z (var (vs (vs vz))))) cPcancel) (⊢app (⊢app (⊢app (⊢-cast stp-w⁴ (⊢wk (⊢wk (⊢wk (⊢wk dstp))))) (⊢var (there (there here)))) ⊢lexZZrec1) ⊢lexZZrec2)))))
