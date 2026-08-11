------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — MEASURE RECURSION.
--
--     amrec : ((x : A) → ((y : A) → μ y < μ x → P y) → P x)
--           → (x : A) → P x
--
-- Data as PARAMETERS over an arbitrary ambient `Δ`, carrier a TYPE, motive
-- and measure PRE-APPLIED families.  At the binder where the carrier
-- variable is `x`, `μ x` IS `m` and `P x` IS `El cM` — no application, no
-- β-redex.  See WF-LIBRARY.md for the measurements behind that choice.
--
-- Ships THREE things, and a caller needs all three:
--   * `⊢amrecΠ`  the combinator as a closed Π-typed TERM;
--   * `⊢amrecPt` the pointwise form, DERIVED — one `⊢app`, no cast;
--   * `amrec-β` / `amrec-unfold-z` / `amrec-unfold-s`, the COMPUTATION
--     rule, so a caller never re-derives how `amrecTm` unfolds (D7).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibAmrec where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTy-renTy; subTy-id; subTm-renTm; subTm-id; subTm-cong
        ; renTm-renTm; renTy-renTy; renTm-cong; renTy-cong; idₛ
        ; renTy-subTy; renTm-subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; _⟶*_; done; step; β; natrec-zero; natrec-suc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ren-ty; ren-lemma; Ren⊢; Ren⊢-ext )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base'; ⊢strong-step )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; ⊢wkᶠ; cong₃; cong₄; sub-w; ren-w; wk-singleTy; wᶠ-single
        ; wᶠ¹-single; wᶠ²-single; nrs-wTy; wᶠ-nrs; ren-wTy; ren-wᶠ
        ; _∙^_; w^; wTy^; wᶠ^ )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat; aIHT; aIHT-ren; aIHT-fit )
open import poc.OCP0009.NbEPDirDBLibNatVal using ( NatVal; nv-zero; nv-suc; natEval )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢[] )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ )

------------------------------------------------------------------------
-- ★ `wᶠ` — weaken a FAMILY under a new binder, keeping the family's own
--   variable in place.  This is the one new piece of plumbing D4 needs,
--   and `ren-w` already covers its naturality.
------------------------------------------------------------------------

-- ★ `⊢wkᶠ` is to `wᶠ` what `⊢wk` is to `w`: it inserts a slot BELOW the
--   family's own variable, so the family keeps pointing at the carrier.
--   ⚠ Reach for this, not `⊢wk`, whenever the subject is a FAMILY — the
--   two produce terms that look interchangeable and are not (P1).
------------------------------------------------------------------------
-- THE THREE TYPES — and there is not one `app` in them.
------------------------------------------------------------------------

-- ★ the IH at an EXPLICIT `μ x`.  `aIHT` is its instance where the
--   carrier variable is `x`, so `μ x` is `m` itself — which is the whole
--   point of pre-applying the measure.
-- `(y : A) → μ y < μ x → P y`, at the binder where `x` is the carrier var
-- `(x : A) → ((y : A) → μ y < μ x → P y) → P x`

aStepT : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) → RTy Γ
aStepT A cM m = Π A (Π (aIHT A cM m) (El (w cM)))

-- `(x : A) → μ x ≤ n → P x`, via the pre-weakened form so `subTy`/`renTy`
-- distribute into it by `refl` — the same shape the rest of the kit uses.
aAuxB' : {Γ : Cx} (A : RTy Γ) (m n : RTm (Γ ∙)) (cm : RTm ((Γ ∙) ∙)) → RTy Γ
aAuxB' A m n cm = Π A (Π (Hom Nat m n) (El cm))

aAuxB : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) → RTy Γ
aAuxB A cM m n = aAuxB' A m (w n) (w cM)

-- ★ TWO `sub-w`s, and that is the whole naturality of the auxiliary's
--   type.  `A`, `cM` and `m` ride through untouched because they are
--   already at the depth they are used — which is what pre-applying them
--   bought.
aAuxB-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (A : RTy Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) →
            subTy σ (aAuxB A cM m n)
          ≡ aAuxB (subTy σ A) (subTm (extS σ) cM) (subTm (extS σ) m) (subTm σ n)
aAuxB-sub {σ = σ} A cM m n =
  cong₄ aAuxB' refl refl (sub-w n) (sub-w {σ = extS σ} cM)

aAuxB-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) →
            renTy ρ (aAuxB A cM m n)
          ≡ aAuxB (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m) (renTm ρ n)
aAuxB-ren {ρ = ρ} A cM m n =
  cong₄ aAuxB' refl refl (ren-w n) (ren-w {ρ = extR ρ} cM)

------------------------------------------------------------------------
-- ★ THE NATURALITY LAYER — D4's BUILD-SIDE COST, in full.
--
-- Four lemmas, and each is a two-step `trans` in the house style: fuse the
-- renaming into the substitution, observe the composite is the identity
-- (or one more weakening), and appeal to `*-cong` + `*-id`.
------------------------------------------------------------------------

-- the type-level `wk-single` — substituting into a weakened TYPE
-- ★ THE FAMILY VERSION.  `extS (single v) ₛ∘ᵣ extR vs` is the IDENTITY:
--   the family's own variable is held in place by both, and everything
--   below it is weakened then immediately substituted back.
-- `nrs` on a weakened type / family: one more weakening, as for `nrs-w`
-- ⚠ this one needs a pointwise BRIDGE: `extS nrs ₛ∘ᵣ extR vs` and
--   `extR vs ∘ᵣ extR vs` agree, but only after casing on the variable —
--   eta alone does not see it, unlike `sub-w`/`ren-w`.
-- ⚠ bridge: the family under TWO `extR vs` then `single (var (vs vz))`
--   collapses to a single weakening.  This is the spine's cancellation.
-- ⚠ bridge: one `wᶠ` then `single (var vz)` is the IDENTITY — the family's
--   variable is put back exactly where it came from.
-- the renaming twins the step's reassociation needs
-- ⚠ bridge again: `extR (extR ρ) ∘ᵣ extR vs` and `extR vs ∘ᵣ extR ρ`
--   agree only after casing, exactly as in `wᶠ-nrs`.
aStepT-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m : RTm (Γ ∙)) →
             renTy ρ (aStepT A cM m)
           ≡ aStepT (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
aStepT-ren {ρ = ρ} A cM m =
  cong₂ (λ r c → Π (renTy ρ A) (Π r (El c)))
        (aIHT-ren A cM m) (ren-w {ρ = extR ρ} cM)

-- ★★ THE FITTING LEMMA, and it is the ONLY one an ⊢app argument needs.
--    Applying the step to `x` instantiates the IH's `μ x` slot; with the
--    measure pre-applied that slot is just `subTm (single x) m`, and the
--    other three arguments peel with the family lemmas.
-- ★ the `⊢wk` ladder (D5: these are iterates of ONE lemma and should be
--   indexed, not listed — recorded, not fixed).

------------------------------------------------------------------------
-- ★★ D5 — THE LADDER, INDEXED.  Three lines each, covering every depth,
--    where the old modules listed one definition per rung across four
--    different combinators.
------------------------------------------------------------------------

aAuxB-w^ : {Γ : Cx} (n : ℕ) (A : RTy Γ) (cM m : RTm (Γ ∙)) (b : RTm Γ) →
           wTy^ n (aAuxB A cM m b)
         ≡ aAuxB (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m) (w^ n b)
aAuxB-w^ zero    A cM m b = refl
aAuxB-w^ (suc n) A cM m b =
  trans (cong (renTy vs) (aAuxB-w^ n A cM m b))
        (aAuxB-ren (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m) (w^ n b))

aStepT-w^ : {Γ : Cx} (n : ℕ) (A : RTy Γ) (cM m : RTm (Γ ∙)) →
            wTy^ n (aStepT A cM m)
          ≡ aStepT (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m)
aStepT-w^ zero    A cM m = refl
aStepT-w^ (suc n) A cM m =
  trans (cong (renTy vs) (aStepT-w^ n A cM m))
        (aStepT-ren (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m))

------------------------------------------------------------------------
-- THE COMBINATOR, over an arbitrary ambient context.
------------------------------------------------------------------------

module AmT (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
           (dA   : Δ ⊢ty A)
           (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
           (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
           (dstp : Δ ⊢ stp ∷ aStepT A cM m)
           where

  -- the natrec motive: the bound `n` is the recursion variable.
  aAuxMot : RTy (⌊ Δ ⌋ ∙)
  aAuxMot = aAuxB (renTy vs A) (wᶠ cM) (wᶠ m) (var vz)

  ⊢aAuxMot : (Δ ▹ Nat) ⊢ty aAuxMot
  ⊢aAuxMot =
    ty-Π (ren-ty dA there)
      (ty-Π (ty-Hom ty-Nat (ren-lemma dm (Ren⊢-ext there)) (⊢var (there here)))
            (ty-El (⊢wk (ren-lemma dcM (Ren⊢-ext there)))))

  -- ★ the motive at ANY bound.  Four peels, one per argument, and three of
  --   them are the family lemmas — no `app`, so no β anywhere.
  mot-at : (n : RTm ⌊ Δ ⌋) → subTy (single n) aAuxMot ≡ aAuxB A cM m n
  mot-at n =
    trans (aAuxB-sub {σ = single n} (renTy vs A) (wᶠ cM) (wᶠ m) (var vz))
          (cong₄ aAuxB (wk-singleTy A) (wᶠ-single cM) (wᶠ-single m) refl)

  mot-s : subTy nrs aAuxMot
        ≡ aAuxB (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m))
                (nsuc (var (vs vz)))
  mot-s =
    trans (aAuxB-sub {σ = nrs} (renTy vs A) (wᶠ cM) (wᶠ m) (var vz))
          (cong₄ aAuxB (nrs-wTy A) (wᶠ-nrs cM) (wᶠ-nrs m) refl)

  ------------------------------------------------------------------------
  -- the ⊢wk'd step, reassociated (the obstruction every branch hits)
  ------------------------------------------------------------------------

  stp-w² : renTy vs (renTy vs (aStepT A cM m))
         ≡ aStepT (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m))
  stp-w² = aStepT-w^ 2 A cM m

  ------------------------------------------------------------------------
  -- n = 0: `μ x ≤ 0` kills every recursive call, so the IH is EX FALSO.
  -- ★ this is where `⊢absurd`'s CODE-indexing is exercised: the motive is
  --   a code FAMILY, so the ex-falso result type `El c` is exactly the
  --   `El (w cM'')` the IH slot wants — no conversion.
  ------------------------------------------------------------------------

  ihZ : RTm (⌊ Δ ⌋ ∙ ∙)
  ihZ = lam (lam (absurd (w (wᶠ (wᶠ cM))) (ordtr (nsuc (w (wᶠ (wᶠ m)))) (w (w (w m))) nzero (var vz) (var (vs (vs vz))))))

  aZBr : RTm ⌊ Δ ⌋
  aZBr = lam (lam (app (app (w (w stp)) (var (vs vz))) ihZ))

  -- the spine's cancellation: w (wᶠ (wᶠ cM)) peeled by the two ⊢apps
  cancelZ : subTm (single ihZ) (subTm (extS (single (var (vs vz)))) (w (wᶠ (wᶠ cM))))
          ≡ w cM
  cancelZ =
    trans (cong (subTm (single ihZ))
                (trans (sub-w {σ = single (var (vs vz))} (wᶠ (wᶠ cM)))
                       (cong w (wᶠ²-single cM))))
          (wk-single {v = ihZ} (w cM))

  ⊢ihZ : (((Δ ▹ A) ▹ Hom Nat m (w nzero))) ⊢ ihZ
       ∷ aIHTat (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m))
                (subTm (single (var (vs vz))) (wᶠ (wᶠ m)))
  ⊢ihZ =
    ⊢lam (ren-ty (ren-ty dA there) there)
      (⊢lam (ty-Hom ty-Nat (⊢nsuc dmY) dmX)
        (⊢strong-base' dC dmY' dmX' dlt (⊢var (there (there here)))))
    where
      dmY = ⊢wkᶠ (⊢wkᶠ dm)
      dmX = subst (λ z → (((Δ ▹ A) ▹ Hom Nat m (w nzero)) ▹ renTy vs (renTy vs A)) ⊢ z ∷ Nat)
                  (sym (cong w (wᶠ²-single m))) (⊢wk (⊢wk dm))
      dmY' = ⊢wk dmY
      dmX' = ⊢wk (⊢wk (⊢wk dm))
      dC = ⊢wk (⊢wkᶠ (⊢wkᶠ dcM))
      dlt = ⊢-cast (cong (λ z → Hom Nat (nsuc (w (wᶠ (wᶠ m)))) (w (w z)))
                         (wᶠ²-single m))
                   (⊢var here)

  ⊢aZBr : Δ ⊢ aZBr ∷ subTy (single nzero) aAuxMot
  ⊢aZBr =
    ⊢-cast (sym (mot-at nzero))
      (⊢lam dA
        (⊢lam (ty-Hom ty-Nat dm ⊢nzero)
          (⊢-cast (cong El cancelZ)
            (⊢app (⊢app (⊢-cast stp-w² (⊢wk (⊢wk dstp))) (⊢var (there here)))
                  (⊢-cast (sym (aIHT-fit (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m))))
                          ⊢ihZ)))))


  ------------------------------------------------------------------------
  -- n = suc n': the IH at n' is a CONTEXT VARIABLE, applied at `y`, and
  -- `⊢strong-step` is the descent — μ y < μ x and μ x ≤ suc n' give
  -- μ y ≤ n'.
  ------------------------------------------------------------------------

  stp-w⁴ : renTy vs (renTy vs (renTy vs (renTy vs (aStepT A cM m))))
         ≡ aStepT (renTy vs (renTy vs (renTy vs (renTy vs A))))
                  (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
  stp-w⁴ = aStepT-w^ 4 A cM m

  ih₀-w⁵ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs aAuxMot))))
         ≡ aAuxB (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs A))))))
                 (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM)))))) (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m))))))
                 (w (w (w (w (w (var vz))))))
  ih₀-w⁵ = aAuxB-w^ 5 (renTy vs A) (wᶠ cM) (wᶠ m) (var vz)

  descS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)
  descS = ordtr (nsuc (w (wᶠ (wᶠ (wᶠ (wᶠ m)))))) (w (w (w (wᶠ (wᶠ m))))) (nsuc (var (vs (vs (vs (vs (vs vz))))))) (var vz) (var (vs (vs vz)))

  ihS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙)
  ihS = lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) descS))

  aSBr : RTm (⌊ Δ ⌋ ∙ ∙)
  aSBr = lam (lam (app (app (w (w (w (w stp)))) (var (vs vz))) ihS))

  -- the IH₀ spine's cancellation: wᶠ⁶ cM peeled by its two ⊢apps
  cancelIH : subTm (single descS)
               (subTm (extS (single (var (vs vz))))
                 (w (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM))))))))
           ≡ w (wᶠ (wᶠ (wᶠ (wᶠ cM))))
  cancelIH =
    trans (cong (subTm (single descS))
                (trans (sub-w {σ = single (var (vs vz))} (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM)))))))
                       (cong w (wᶠ²-single (wᶠ (wᶠ (wᶠ (wᶠ cM))))))))
          (wk-single {v = descS} (w (wᶠ (wᶠ (wᶠ (wᶠ cM))))))

  ⊢ihS : ((((Δ ▹ Nat) ▹ aAuxMot) ▹ renTy vs (renTy vs A))
            ▹ Hom Nat (wᶠ (wᶠ m)) (nsuc (var (vs (vs vz)))))
           ⊢ ihS
         ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs A))))
                  (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
                  (subTm (single (var (vs vz))) (wᶠ (wᶠ (wᶠ (wᶠ m)))))
  ⊢ihS =
    ⊢lam (ren-ty (ren-ty (ren-ty (ren-ty dA there) there) there) there)
      (⊢lam (ty-Hom ty-Nat (⊢nsuc dm₄) dmXS)
        (⊢-cast (cong El cancelIH)
          (⊢app (⊢app (⊢-cast ih₀-w⁵ (⊢var (there (there (there (there here))))))
                      (⊢var (there here)))
                (⊢-cast (sym (cong (λ z → Hom Nat z (var (vs (vs (vs (vs (vs vz)))))))
                                   (wᶠ²-single (wᶠ (wᶠ (wᶠ (wᶠ m)))))))
                        dDesc))))
    where
      dm₄ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm)))
      dm₂ = ⊢wkᶠ (⊢wkᶠ dm)
      dmXS = subst (λ z → ((((Δ ▹ Nat) ▹ aAuxMot) ▹ renTy vs (renTy vs A))
                            ▹ Hom Nat (wᶠ (wᶠ m)) (nsuc (var (vs (vs vz)))))
                            ▹ renTy vs (renTy vs (renTy vs (renTy vs A))) ⊢ z ∷ Nat)
                   (sym (cong w (wᶠ²-single (wᶠ (wᶠ m)))))
                   (⊢wk (⊢wk dm₂))
      dDesc = ⊢strong-step (⊢wk dm₄) (⊢wk (⊢wk (⊢wk dm₂)))
                           (⊢var (there (there (there (there (there here))))))
                           (⊢-cast (cong (λ z → Hom Nat (nsuc (w (wᶠ (wᶠ (wᶠ (wᶠ m)))))) (w (w z)))
                                         (wᶠ²-single (wᶠ (wᶠ m))))
                                   (⊢var here))
                           (⊢var (there (there here)))

  -- the outer spine's cancellation: wᶠ⁴ cM peeled by the step's two ⊢apps
  cancelS : subTm (single ihS)
              (subTm (extS (single (var (vs vz)))) (w (wᶠ (wᶠ (wᶠ (wᶠ cM))))))
          ≡ w (wᶠ (wᶠ cM))
  cancelS =
    trans (cong (subTm (single ihS))
                (trans (sub-w {σ = single (var (vs vz))} (wᶠ (wᶠ (wᶠ (wᶠ cM)))))
                       (cong w (wᶠ²-single (wᶠ (wᶠ cM))))))
          (wk-single {v = ihS} (w (wᶠ (wᶠ cM))))

  ⊢aSBr : ((Δ ▹ Nat) ▹ aAuxMot) ⊢ aSBr ∷ subTy nrs aAuxMot
  ⊢aSBr =
    ⊢-cast (sym mot-s)
      (⊢lam (ren-ty (ren-ty dA there) there)
        (⊢lam (ty-Hom ty-Nat (⊢wkᶠ (⊢wkᶠ dm)) (⊢nsuc (⊢var (there (there here)))))
          (⊢-cast (cong El cancelS)
            (⊢app (⊢app (⊢-cast stp-w⁴ (⊢wk (⊢wk (⊢wk (⊢wk dstp)))))
                        (⊢var (there here)))
                  (⊢-cast (sym (aIHT-fit (renTy vs (renTy vs (renTy vs (renTy vs A))))
                                         (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))))
                          ⊢ihS)))))

  ------------------------------------------------------------------------
  -- ★★ THE BOUNDED AUXILIARY, at an arbitrary bound.
  ------------------------------------------------------------------------

  aAuxTm : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  aAuxTm n = natrec aZBr aSBr n

  ⊢aAux : {n : RTm ⌊ Δ ⌋} → Δ ⊢ n ∷ Nat →
          Δ ⊢ aAuxTm n ∷ subTy (single n) aAuxMot
  ⊢aAux dn = ⊢natrec ⊢aAuxMot ⊢aZBr ⊢aSBr dn

------------------------------------------------------------------------
-- ★★★ THE COMBINATOR ITSELF, Π-TYPED.
--
-- `AmT` is instantiated at `Δ ▹ A` — the module applies to ITSELF at a
-- deeper context, which is what parameterising over `Δ` buys.
--
-- ★★ AND THE BOUND IS LITERALLY `m`.  With the measure pre-applied, "the
--   auxiliary at μ x" is `aAuxTm m` — no application, no β-redex, and the
--   bound's typing premise is `dm` itself, unweakened.  Under AmrecC this
--   was `aAuxTm (app (w μ) (var vz))` with a `⊢app` to build it.
------------------------------------------------------------------------

module AmTΠ (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
            (dA   : Δ ⊢ty A)
            (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
            (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
            (dstp : Δ ⊢ stp ∷ aStepT A cM m)
            where

  open AmT (Δ ▹ A) (renTy vs A) (wᶠ cM) (wᶠ m) (w stp)
           (ren-ty dA there) (⊢wkᶠ dcM) (⊢wkᶠ dm)
           (⊢-cast (aStepT-ren A cM m) (⊢wk dstp))

  amrecTm : RTm ⌊ Δ ⌋
  amrecTm = lam (app (app (aAuxTm m) (var vz)) (reflTm m))

  -- the spine's two substitutions, w (wᶠ cM) → cM
  cancelΠ : subTm (single (reflTm m))
              (subTm (extS (single (var vz))) (w (wᶠ cM)))
          ≡ cM
  cancelΠ =
    trans (cong (subTm (single (reflTm m)))
                (trans (sub-w {σ = single (var vz)} (wᶠ cM))
                       (cong w (wᶠ¹-single cM))))
          (wk-single {v = reflTm m} cM)

  -- ★★ THE Π FORM.  Note the codomain: `El cM`, not
  --    `El (app (w cP) (var vz))` — the motive is already applied.
  ⊢amrecΠ : Δ ⊢ amrecTm ∷ Π A (El cM)
  ⊢amrecΠ =
    ⊢lam dA
      (⊢-cast (cong El cancelΠ)
        (⊢app (⊢app (⊢-cast (mot-at m) (⊢aAux dm)) (⊢var here))
              (⊢-cast (sym (cong₂ (λ a b → Hom Nat a b)
                                  (wᶠ¹-single m) (wk-single {v = var vz} m)))
                      (⊢le-refl dm))))

  -- ★ …and the POINTWISE form, DERIVED — and under D4 it needs NO CAST at
  --   all, because `P x` is `subTy (single x) (El cM)` definitionally.
  ⊢amrecPt : {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
             Δ ⊢ app amrecTm x ∷ subTy (single x) (El cM)
  ⊢amrecPt dx = ⊢app ⊢amrecΠ dx

  ------------------------------------------------------------------------
  -- ★★ D7 — THE COMPUTATION RULE.  A typing derivation is not enough: a
  --    caller who wants to know their function COMPUTES must otherwise
  --    re-derive how `amrecTm` unfolds, by hand, every time (that cost was
  --    measured on SpikeDivC — eight steps for `div 0`, and it NESTS on
  --    the recursive case).  These are the lemmas that make it their
  --    step function's business and not the combinator's.
  --
  -- ⚠ The unfolding is CONDITIONAL on the measure reaching a numeral,
  --   which is the honest statement: for an abstract `x` the recursion
  --   cannot step, and that is the recursor doing its job.
  ------------------------------------------------------------------------

  -- the shape, unconditionally: β exposes the auxiliary at `μ x`.
  amrec-β : (x : RTm ⌊ Δ ⌋) →
            app amrecTm x
          ⟶* app (app (natrec (subTm (single x) aZBr)
                              (subTm (extS (extS (single x))) aSBr)
                              (subTm (single x) m))
                      x)
                 (reflTm (subTm (single x) m))
  amrec-β x = step (β _ x) done

  -- ★ μ x ⟶* 0 : the recursion bottoms out in the VACUOUS branch.
  amrec-unfold-z : (x : RTm ⌊ Δ ⌋) → subTm (single x) m ⟶* nzero →
                   app amrecTm x
                 ⟶* app (app (subTm (single x) aZBr) x)
                        (reflTm (subTm (single x) m))
  amrec-unfold-z x r =
    step (β _ x)
      (⟶*-appˡ (⟶*-appˡ
        (⟶*-trans (⟶*-natrecⁿ r) (step (natrec-zero _ _) done))))

  -- ★ μ x ⟶* suc k : one layer of the auxiliary peels, exposing the STEP.
  amrec-unfold-s : (x k : RTm ⌊ Δ ⌋) → subTm (single x) m ⟶* nsuc k →
                   app amrecTm x
                 ⟶* app (app (subTm (single (natrec (subTm (single x) aZBr)
                                                    (subTm (extS (extS (single x))) aSBr)
                                                    k))
                                     (subTm (extS (single k))
                                            (subTm (extS (extS (single x))) aSBr)))
                             x)
                        (reflTm (subTm (single x) m))
  amrec-unfold-s x k r =
    step (β _ x)
      (⟶*-appˡ (⟶*-appˡ
        (⟶*-trans (⟶*-natrecⁿ r) (step (natrec-suc _ _ k) done))))

------------------------------------------------------------------------
-- ★★ AT A CLOSED CARRIER, THE UNFOLDING'S PREMISE IS FREE.
--
-- `amrec-unfold-z`/`-s` are conditional on the measure reaching a numeral.
-- That premise is real information at an OPEN context — there the measure
-- normalises to a NEUTRAL containing the free variable, and no library can
-- supply it.  At `◇` it is a THEOREM (`natEval`), so the library discharges
-- it and the caller just cases on the answer.
--
-- ⚠ The boundary is CANONICITY, not normalisation: `wnorm` works at any
--   context, `canNat` is closed-only.  Two lemmas, two domains — the
--   conditional form is the correct one whenever anything is open, not a
--   weaker fallback.
------------------------------------------------------------------------

measure-evals : (A : RTy ε) (m : RTm (ε ∙)) → (◇ ▹ A) ⊢ m ∷ Nat →
                (x : RTm ε) → ◇ ⊢ x ∷ A → NatVal (subTm (single x) m)
measure-evals A m dm x dx = natEval (⊢[] dm dx)
