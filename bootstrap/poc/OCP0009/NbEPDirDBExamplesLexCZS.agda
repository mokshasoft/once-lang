------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (0,S) at an ABSTRACT AMBIENT CONTEXT.
--
-- Option C: there is no Γ₅.  `Δ`, the carrier, the motive, the measures
-- and the step are all PARAMETERS.  See NbEPDirDBExamplesLexC.
--
-- ⚠ 47.2 s / 4.43 GB, against 56.6 s / 4.88 GB for the same branch under
--   option B (NbEPDirDBExamplesLexZS).  Only 1.20×/1.10× — NOT the
--   2.2×/2.3× branch (0,0) got.  The win SHRINKS with depth: (0,0)'s
--   ΓZZ is 4 slots, this ΓZS is 6, and at ~1.7× per slot those two extra
--   slots eat most of what dropping Γ₅ bought.  Do not quote (0,0)'s
--   factor as "option C's speedup" — it is the SHALLOWEST branch.
--
-- ★ THE FIRST OPTION-C BRANCH WITH A REAL RECURSIVE CALL.  n₁ = 0 still
--   collapses `rec₁` into `absurd`, but n₂ = suc m makes `rec₂` invoke
--   the inner IH, and under option C that IH is a CONTEXT VARIABLE whose
--   type is `renTy vs⁷ M0lex` — seven `⊢wk`s' worth of `renTy` sitting
--   OUTSIDE the Π-chain.  Reassociating it is `auxBody-w⁷`, and it is the
--   one obstruction branch (0,0) never had to pay: there `rec₂` was
--   vacuous, so no IH was ever applied.
--
-- THE CASTS, outward from the motive boundary:
--   `M0lex-nrs`  the motive boundary is `subTy nrs M0lex` this time, not
--                `subTy (single nzero) M0lex`.  auxBody-sub + `nrs-w`,
--                the third weakening flavour (LexC).
--   `IH-w⁷`      the inner IH's own type — auxBody-w⁷.
--   `μ₁-fit` / `μ₂-fit` / `ihPcancel`   the IH spine: each argument's
--                expected type is the `auxBody` slot already substituted
--                by the arguments before it, exactly as in the outer
--                spine.  μ₂'s peels with `sub-w` (it is under a binder).
--   `stp-w⁶`     the step, six levels rather than four (lStepT-w⁶).
--   `rec1-fit` / `rec2-fit` / `cPcancel`   (0,0)'s outer spine verbatim,
--                at two more weakenings.
--
-- ⚠ `wk-single`'s implicit `{v = …}` is PINNED throughout, per (0,0)'s
--   header: it is the term being substituted and it differs per step.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCZS where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLexC

module _ (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂)
         where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  -- ctx: vz = lt, vs = le, vs² = x, vs³ = IH, vs⁴ = m, vs⁵ = n₂, then Δ
  ΓZS : Ctx
  ΓZS =
    (((((Δ ▹ Nat) ▹ Nat) ▹ M0lex) ▹ El (w (w (w cA))))
       ▹ Hom Nat (app (w (w (w (w μ₁)))) (var vz)) nzero)
       ▹ Hom Nat (app (w (w (w (w (w μ₂))))) (var (vs vz))) (nsuc (var (vs (vs (vs vz)))))

  lexZSrec1 : RTm ⌊ ΓZS ⌋
  lexZSrec1 =
    lam (lam (absurd (app (w (w (w (w (w (w (w (w cP)))))))) (var (vs vz))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w μ₁)))))))) (var (vs vz)))) (app (w (w (w (w (w (w (w (w μ₁)))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

  -- ★ THE TWO OBLIGATIONS `rec₂` discharges to make the recursive call:
  --     μ₁ y ≤ 0   plain ⊢ordtr — μ₁ y ≤ μ₁ x and μ₁ x ≤ 0;
  --     μ₂ y ≤ m   ⊢strong-step — μ₂ y < μ₂ x and μ₂ x ≤ suc m.
  --   The second one IS the lexicographic descent: n₁ held fixed, n₂
  --   strictly down.  Named, because both appear inside the spine's
  --   substitutions and the cancellation lemmas have to mention them.
  ltZS₁ : RTm (⌊ ΓZS ⌋ ∙ ∙ ∙)
  ltZS₁ = ordtr (app (w (w (w (w (w (w (w (w (w μ₁))))))))) (var (vs (vs vz)))) (app (w (w (w (w (w (w (w (w (w μ₁))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var (vs vz)) (var (vs (vs (vs (vs vz)))))

  ltZS₂ : RTm (⌊ ΓZS ⌋ ∙ ∙ ∙)
  ltZS₂ = ordtr (nsuc (app (w (w (w (w (w (w (w (w (w μ₂))))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (w (w μ₂))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))

  lexZSrec2 : RTm ⌊ ΓZS ⌋
  lexZSrec2 =
    lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) ltZS₁) ltZS₂)))

  ------------------------------------------------------------------------
  -- `rec₁` — vacuous, exactly as at (0,0): μ₁ y < μ₁ x ≤ 0.
  ------------------------------------------------------------------------

  ⊢lexZSrec1 : ΓZS ⊢ lexZSrec1
             ∷ rec1T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (var (vs (vs vz)))
  ⊢lexZSrec1 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcA))))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var (there (there (there here)))))) (⊢strong-base' (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcP)))))))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))))) (⊢var (there (there (there (there here)))))) (⊢var here) (⊢var (there (there (there here))))))

  ------------------------------------------------------------------------
  -- ★ `rec₂` — REAL.  The IH is `var (vs⁶ vz)`, whose type is
  --   `renTy vs⁷ M0lex`; `⊢app` cannot fire until that is back in
  --   `auxBody` form, and then each of the three arguments has to be cast
  --   into the slot the previous arguments have already substituted.
  ------------------------------------------------------------------------

  IH-w⁷ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (M0lex)))))))
        ≡ auxBody (w (w (w (w (w (w (w (w (w cA))))))))) (w (w (w (w (w (w (w (w (w cP))))))))) (w (w (w (w (w (w (w (w (w μ₁))))))))) (w (w (w (w (w (w (w (w (w μ₂))))))))) nzero (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  IH-w⁷ = auxBody-w⁷ (w (w cA)) (w (w cP)) (w (w μ₁)) (w (w μ₂)) nzero (var vz)

  μ₁-fit : subTm (single (var (vs (vs vz)))) (w (w (w (w (w (w (w (w (w (w μ₁)))))))))) ≡ (w (w (w (w (w (w (w (w (w μ₁)))))))))
  μ₁-fit = wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w μ₁)))))))))

  -- under a binder, so the inner one peels with `sub-w`
  μ₂-fit : subTm (single ltZS₁) (subTm (extS (single (var (vs (vs vz))))) (w (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))) ≡ (w (w (w (w (w (w (w (w (w μ₂)))))))))
  μ₂-fit =
    trans (cong (subTm (single ltZS₁))
                (trans (sub-w {σ = single (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))
                       (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w μ₂)))))))))))))
          (wk-single {v = ltZS₁} (w (w (w (w (w (w (w (w (w μ₂))))))))))

  -- the IH spine's three substitutions, w¹² cP → w⁹ cP
  ihPcancel : subTm (single ltZS₂)
                (subTm (extS (single ltZS₁))
                  (subTm (extS (extS (single (var (vs (vs vz)))))) (w (w (w (w (w (w (w (w (w (w (w (w cP))))))))))))))
            ≡ (w (w (w (w (w (w (w (w (w cP)))))))))
  ihPcancel =
    trans (cong (λ z → subTm (single ltZS₂) (subTm (extS (single ltZS₁)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w (w cP)))))))))))
                       (cong (λ z → w (w z)) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w cP)))))))))))))
    (trans (cong (subTm (single ltZS₂))
                 (trans (sub-w {σ = single ltZS₁} (w (w (w (w (w (w (w (w (w (w cP)))))))))))
                        (cong w (wk-single {v = ltZS₁} (w (w (w (w (w (w (w (w (w cP)))))))))))))
           (wk-single {v = ltZS₂} (w (w (w (w (w (w (w (w (w cP)))))))))))

  ⊢lexZSrec2 : ΓZS ⊢ lexZSrec2
             ∷ rec2T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (w (w (w (w (w (w μ₂)))))) (var (vs (vs vz)))
  ⊢lexZSrec2 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcA))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var here)) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))) (⊢var (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))) (⊢var (there (there (there (there here))))))) (⊢-cast (cong (λ z → El (app z (var (vs (vs vz))))) ihPcancel) (⊢app (⊢app (⊢app (⊢-cast IH-w⁷ (⊢var (there (there (there (there (there (there here)))))))) (⊢var (there (there here)))) (⊢-cast (sym (cong (λ z → Hom Nat (app z (var (vs (vs vz)))) nzero) μ₁-fit)) (⊢ordtr (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))) (⊢var (there (there (there (there (there here))))))) ⊢nzero (⊢var (there here)) (⊢var (there (there (there (there here)))))))) (⊢-cast (sym (cong (λ z → Hom Nat (app z (var (vs (vs vz)))) (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) μ₂-fit)) (⊢strong-step (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))))))) (⊢var (there (there (there (there (there here))))))) (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here) (⊢var (there (there (there here))))))))))

  ------------------------------------------------------------------------
  -- ★ THE MOTIVE BOUNDARY.  `⊢natrec`'s STEP wants `subTy nrs M0lex`;
  --   the three `⊢lam`s build the `auxBody` form.  `nrs` on a weakened
  --   term is one more weakening (`nrs-w`), and on `var vz` it is
  --   `nsuc (var (vs vz))` — the successor bound, definitionally.
  ------------------------------------------------------------------------

  M0lex-nrs : subTy nrs M0lex
            ≡ auxBody (w (w (w cA))) (w (w (w cP))) (w (w (w μ₁))) (w (w (w μ₂))) nzero (nsuc (var (vs vz)))
  M0lex-nrs =
    trans (auxBody-sub {σ = nrs} (w (w cA)) (w (w cP)) (w (w μ₁)) (w (w μ₂)) nzero (var vz))
          (cong₆ auxBody (nrs-w (w cA)) (nrs-w (w cP))
                         (nrs-w (w μ₁)) (nrs-w (w μ₂)) refl refl)

  -- ★ reassociate `renTy vs⁶ (lStepT …)` into `lStepT (w⁶ …)`
  stp-w⁶ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (lStepT cA cP μ₁ μ₂))))))
         ≡ lStepT (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (w (w (w (w (w (w μ₂))))))
  stp-w⁶ = lStepT-w⁶ cA cP μ₁ μ₂

  -- the outer spine's three substitutions, w⁹ cP → w⁶ cP
  cPcancel : subTm (single lexZSrec2)
               (subTm (extS (single lexZSrec1))
                 (subTm (extS (extS (single (var (vs (vs vz)))))) (w (w (w (w (w (w (w (w (w cP)))))))))))
           ≡ (w (w (w (w (w (w cP))))))
  cPcancel =
    trans (cong (λ z → subTm (single lexZSrec2) (subTm (extS (single lexZSrec1)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (w (w (w (w (w (w (w cP))))))))
                       (cong (λ z → w (w z)) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cP))))))))))
    (trans (cong (subTm (single lexZSrec2))
                 (trans (sub-w {σ = single lexZSrec1} (w (w (w (w (w (w (w cP))))))))
                        (cong w (wk-single {v = lexZSrec1} (w (w (w (w (w (w cP))))))))))
           (wk-single {v = lexZSrec2} (w (w (w (w (w (w cP))))))))

  ------------------------------------------------------------------------
  -- ★ THE FITTING LEMMAS — (0,0)'s, at two more weakenings.
  ------------------------------------------------------------------------

  rec1-fit : subTy (single (var (vs (vs vz)))) (rec1T (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (var vz))
           ≡ rec1T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (var (vs (vs vz)))
  rec1-fit =
    trans (rec1T-sub (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (var vz))
          (cong₄ rec1T (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cA))))))) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cP)))))))
                       (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w μ₁))))))) refl)

  rec2-fit : subTy (single lexZSrec1)
               (subTy (extS (single (var (vs (vs vz)))))
                 (rec2T (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs vz))))
           ≡ rec2T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (w (w (w (w (w (w μ₂)))))) (var (vs (vs vz)))
  rec2-fit =
    trans (cong (subTy (single lexZSrec1))
            (trans (rec2T-sub (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs vz)))
                   (cong₅ rec2T (trans (sub-w (w (w (w (w (w (w (w cA)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cA)))))))))
                                (trans (sub-w (w (w (w (w (w (w (w cP)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cP)))))))))
                                (trans (sub-w (w (w (w (w (w (w (w μ₁)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w μ₁)))))))))
                                (trans (sub-w (w (w (w (w (w (w (w μ₂)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w μ₂)))))))))
                                refl)))
          (trans (rec2T-sub (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (w (w (w (w (w (w (w μ₂))))))) (w (var (vs (vs vz)))))
                 (cong₅ rec2T (wk-single {v = lexZSrec1} (w (w (w (w (w (w cA))))))) (wk-single {v = lexZSrec1} (w (w (w (w (w (w cP)))))))
                              (wk-single {v = lexZSrec1} (w (w (w (w (w (w μ₁))))))) (wk-single {v = lexZSrec1} (w (w (w (w (w (w μ₂)))))))
                              (wk-single {v = lexZSrec1} (var (vs (vs vz))))))

  ------------------------------------------------------------------------
  -- BRANCH (0,S) ASSEMBLED.
  ------------------------------------------------------------------------

  ⊢lexZS : (((Δ ▹ Nat) ▹ Nat) ▹ M0lex) ⊢ lexZS ∷ subTy nrs M0lex
  ⊢lexZS =
    ⊢-cast (sym M0lex-nrs)
      (⊢lam (ty-El (⊢wk (⊢wk (⊢wk dcA)))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))) (⊢var here)) ⊢nzero) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))) (⊢var (there here))) (⊢nsuc (⊢var (there (there (there here)))))) (⊢-cast (cong (λ z → El (app z (var (vs (vs vz))))) cPcancel) (⊢app (⊢app (⊢app (⊢-cast stp-w⁶ (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dstp))))))) (⊢var (there (there here)))) (⊢-cast (sym rec1-fit) ⊢lexZSrec1)) (⊢-cast (sym rec2-fit) ⊢lexZSrec2))))))
