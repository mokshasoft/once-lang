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
        ; _⟶*_; done; step; β; ξ-appˡ; natrec-zero; natrec-suc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ren-ty; ren-lemma; Ren⊢; Ren⊢-ext )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base'; ⊢strong-step )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; ⊢wkᶠ; cong₃; cong₄; sub-w; sub-w²; sub-w³; sub-w⁴; ren-w; wk-singleTy; wᶠ-single
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

  -- ★ public: the unfolding lemmas' TYPES mention /, so the
  --   auxiliary's branches are already part of the interface.
  open AmT (Δ ▹ A) (renTy vs A) (wᶠ cM) (wᶠ m) (w stp)
           (ren-ty dA there) (⊢wkᶠ dcM) (⊢wkᶠ dm)
           (⊢-cast (aStepT-ren A cM m) (⊢wk dstp)) public

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
  -- ★★★ D7's IDEAL SHAPE — REACH THE CALLER'S STEP.
  --
  -- ⚠ WHY THE LEMMAS ABOVE ARE NOT ENOUGH.  They land on the AUXILIARY's
  --   branch, `app (app (subTm (single x) aZBr) x) …`, but a caller's own
  --   theorem is about `app (app stp x) ih` — so the two DO NOT COMPOSE,
  --   and every caller re-peels `aZBr`'s two binders by hand.  That is the
  --   defect D7 was opened for and it survived the first attempt.
  --
  -- ★ THE INTERFACE IS CPS, and that is what makes it fit.  A caller
  --   proves their step's equation UNIVERSALLY IN THE IH — which is the
  --   shape it already has, because the IH is never inspected:
  --
  --       (ih : RTm ⌊ Δ ⌋) → app (app stp x) ih ⟶* answer
  --
  --   and hands it here to get `app amrecTm x ⟶* answer`.  Passing the IH
  --   in continuation position means the combinator never has to NAME the
  --   instantiated IH in its own statement, which is what made the direct
  --   formulation unusable.
  --
  -- ★ Two βs peel the branch's binders; the weakenings on `stp` and on `x`
  --   then cancel by `wk-single`.  ⚠ Propositionally, NOT definitionally —
  --   even at `Δ = ◇` an OPAQUE `stp` has no `w stp ≡ stp`, so D7's note
  --   that this "should be cheap at ◇" was optimistic about the wrong
  --   thing: it is cheap, but by lemma, not by computation.
  ------------------------------------------------------------------------

  -- the IH the ZERO branch hands the step, fully instantiated
  ihZ-at : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  ihZ-at x =
    subTm (single (reflTm (subTm (single x) m)))
      (subTm (extS (single x)) (subTm (extS (extS (single x))) ihZ))

  -- three weakenings on `stp`, three substitutions, one `wk-single` each
  stp-cancel : (x r : RTm ⌊ Δ ⌋) →
    subTm (single r)
      (subTm (extS (single x))
        (subTm (extS (extS (single x))) (w (w (w stp)))))
    ≡ stp
  stp-cancel x r =
    trans (cong (λ z → subTm (single r) (subTm (extS (single x)) z))
                (trans (sub-w² {σ = single x} (w stp))
                       (cong (λ z → w (w z)) (wk-single {v = x} stp))))
      (trans (cong (subTm (single r))
                   (trans (sub-w {σ = single x} (w stp))
                          (cong w (wk-single {v = x} stp))))
             (wk-single {v = r} stp))

  -- the carrier argument: the two inner substitutions COMPUTE, leaving one
  x-cancel : (x r : RTm ⌊ Δ ⌋) →
    subTm (single r)
      (subTm (extS (single x)) (subTm (extS (extS (single x))) (var (vs vz))))
    ≡ x
  x-cancel x r = wk-single {v = r} x

  -- ★★ μ x ⟶* 0 : the whole reduction, in the caller's own terms.
  amrec-step-z : {P : RTm ⌊ Δ ⌋} (x : RTm ⌊ Δ ⌋) →
                 subTm (single x) m ⟶* nzero →
                 ((ih : RTm ⌊ Δ ⌋) → app (app stp x) ih ⟶* P) →
                 app amrecTm x ⟶* P
  amrec-step-z {P = P} x r h =
    ⟶*-trans
      (⟶*-trans (amrec-unfold-z x r)
        (step (ξ-appˡ (β _ x))
          (step (β _ (reflTm (subTm (single x) m))) done)))
      (subst (λ z → z ⟶* P)
             (sym (cong₂ (λ s y → app (app s y) (ihZ-at x))
                         (stp-cancel x (reflTm (subTm (single x) m)))
                         (x-cancel x (reflTm (subTm (single x) m)))))
             (h (ihZ-at x)))

  -- ★★ μ x ⟶* suc k : the same, one layer down.  ⚠ `aSBr` carries FIVE
  --    weakenings on the step against `aZBr`'s three, so the cancellation
  --    is a five-rung chain (`sub-w⁴`…`wk-single`) rather than three.
  auxIH : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  auxIH x k = natrec (subTm (single x) aZBr)
                     (subTm (extS (extS (single x))) aSBr) k

  ihS-at : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  ihS-at x k =
    subTm (single (reflTm (subTm (single x) m)))
      (subTm (extS (single x))
        (subTm (extS (extS (single (auxIH x k))))
          (subTm (extS (extS (extS (single k))))
            (subTm (extS (extS (extS (extS (single x))))) ihS))))

  stp-cancel-s : (x k r : RTm ⌊ Δ ⌋) →
    subTm (single r)
      (subTm (extS (single x))
        (subTm (extS (extS (single (auxIH x k))))
          (subTm (extS (extS (extS (single k))))
            (subTm (extS (extS (extS (extS (single x)))))
                   (w (w (w (w (w stp)))))))))
    ≡ stp
  stp-cancel-s x k r =
    trans (cong (λ z → subTm (single r)
                         (subTm (extS (single x))
                           (subTm (extS (extS (single (auxIH x k))))
                             (subTm (extS (extS (extS (single k)))) z))))
                (trans (sub-w⁴ {σ = single x} (w stp))
                       (cong (λ z → w (w (w (w z)))) (wk-single {v = x} stp))))
    (trans (cong (λ z → subTm (single r)
                          (subTm (extS (single x))
                            (subTm (extS (extS (single (auxIH x k)))) z)))
                 (trans (sub-w³ {σ = single k} (w stp))
                        (cong (λ z → w (w (w z))) (wk-single {v = k} stp))))
    (trans (cong (λ z → subTm (single r) (subTm (extS (single x)) z))
                 (trans (sub-w² {σ = single (auxIH x k)} (w stp))
                        (cong (λ z → w (w z)) (wk-single {v = auxIH x k} stp))))
    (trans (cong (subTm (single r))
                 (trans (sub-w {σ = single x} (w stp))
                        (cong w (wk-single {v = x} stp))))
           (wk-single {v = r} stp))))

  x-cancel-s : (x k r : RTm ⌊ Δ ⌋) →
    subTm (single r)
      (subTm (extS (single x))
        (subTm (extS (extS (single (auxIH x k))))
          (subTm (extS (extS (extS (single k))))
            (subTm (extS (extS (extS (extS (single x))))) (var (vs vz))))))
    ≡ x
  x-cancel-s x k r = wk-single {v = r} x

  amrec-step-s : {P : RTm ⌊ Δ ⌋} (x k : RTm ⌊ Δ ⌋) →
                 subTm (single x) m ⟶* nsuc k →
                 ((ih : RTm ⌊ Δ ⌋) → app (app stp x) ih ⟶* P) →
                 app amrecTm x ⟶* P
  amrec-step-s {P = P} x k r h =
    ⟶*-trans
      (⟶*-trans (amrec-unfold-s x k r)
        (step (ξ-appˡ (β _ x))
          (step (β _ (reflTm (subTm (single x) m))) done)))
      (subst (λ z → z ⟶* P)
             (sym (cong₂ (λ s y → app (app s y) (ihS-at x k))
                         (stp-cancel-s x k (reflTm (subTm (single x) m)))
                         (x-cancel-s x k (reflTm (subTm (single x) m)))))
             (h (ihS-at x k)))

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

------------------------------------------------------------------------
-- ★★ AND THE TWO HALVES, COMPOSED.  At a closed carrier a caller touches
--    neither `NatVal` nor the conditional lemmas: it hands over `x` and
--    its derivation and gets the reduction.
--
-- ⚠ Still one step short of the ideal D7 shape — this reaches the
--   AUXILIARY's branch, not the user's step; two more βs would take it to
--   `app (app stp x) ⟨ih⟩`.  Flagged rather than claimed.
------------------------------------------------------------------------

module AmTΠ◇ (A : RTy ε) (cM m : RTm (ε ∙)) (stp : RTm ε)
             (dA   : ◇ ⊢ty A)
             (dcM  : (◇ ▹ A) ⊢ cM ∷ U)
             (dm   : (◇ ▹ A) ⊢ m ∷ Nat)
             (dstp : ◇ ⊢ stp ∷ aStepT A cM m)
             where

  open AmTΠ ◇ A cM m stp dA dcM dm dstp public

  data Unfold (x : RTm ε) : Set where
    unf-z : app amrecTm x
          ⟶* app (app (subTm (single x) aZBr) x) (reflTm (subTm (single x) m))
          → Unfold x
    unf-s : (k : RTm ε) →
            app amrecTm x
          ⟶* app (app (subTm (single (natrec (subTm (single x) aZBr)
                                             (subTm (extS (extS (single x))) aSBr)
                                             k))
                              (subTm (extS (single k))
                                     (subTm (extS (extS (single x))) aSBr)))
                      x)
                 (reflTm (subTm (single x) m))
          → Unfold x

  -- ★ the premise is gone: canonicity supplies it.
  amrec-unfold : (x : RTm ε) → ◇ ⊢ x ∷ A → Unfold x
  amrec-unfold x dx with measure-evals A m dm x dx
  ... | nv-zero r  = unf-z (amrec-unfold-z x r)
  ... | nv-suc k r = unf-s k (amrec-unfold-s x k r)
