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
        ; RTy; El; Hom; Nat; U; Id
        ; RTm; var; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTy-renTy; subTy-id; subTm-renTm; subTm-id; subTm-cong
        ; renTm-renTm; renTy-renTy; renTm-cong; renTy-cong; idₛ
        ; renTy-subTy; renTm-subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; _⟶*_; done; step; β; ξ-appˡ; natrec-zero; natrec-suc
        ; ⊢lam; ⊢app; _⊢ty_; ⊢conv; csymᵀ; ctrnᵀ
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ren-ty; ren-lemma; Ren⊢; Ren⊢-ext
        ; sub-ty; sub-lemma; Sub⊢; Sub⊢-ext; ⊢single )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base'; ⊢strong-step )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; ⊢wkᶠ; cong₃; cong₄; sub-w; sub-w²; sub-w³; sub-w⁴; ren-w; wk-singleTy; wᶠ-single
        ; wᶠ¹-single; wᶠ²-single; nrs-wTy; wᶠ-nrs; ren-wTy; ren-wᶠ; sub-wTy; wᶠ-sub
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
-- ★★★ THE EXTENSIONALITY PREMISE — the CALLER's half of irrelevance.
--
-- ⚠ WHY THE LIBRARY NEEDS ONE AT ALL.  `app amrecTm x` reduces exactly to
--   `app (app (auxIH x μx) x) (reflTm μx)` and no further: the auxiliary's
--   `natrec` is stuck on `μx`.  An INTERNAL unfolding therefore has to
--   transport along an `Id`, `⊢jsub`'s family must typecheck at an
--   ARBITRARY bound `v`, and `auxIH x v` only reaches an `El _` when it is
--   applied to a certificate of type `Hom Nat (μ a) v` — which for a
--   generic `v` has no inhabitant to weaken in.  So the certificate has to
--   be bound INSIDE the family, and the transport's source obligation is
--   then "any two certificates give the same answer".  That is
--   IRRELEVANCE, and it is provable by induction on the bound — but only
--   if the step's answer depends on its IH POINTWISE.
--
-- ★ This is the standard side condition: Agda's own
--   `Induction.WellFounded.FixPoint` demands precisely it.  It is the
--   caller's to discharge, and a step that uses its IH once (gcd, via
--   `RecCall`) discharges it by ONE instantiation of the hypothesis.
--
-- ⚠⚠ AND IT IS STATED META-LEVEL, NOT AS AN `RTy`.  The internal Π-form
--   would carry the pointwise hypothesis as an object-language type — four
--   nested binders over `Id`s — and every caller would have to BUILD an
--   inhabitant with `⊢lam`.  Meta-level, the hypothesis is an Agda
--   function the induction applies directly, and the caller supplies it by
--   instantiating its own reduction lemma.  Context-polymorphic (`ρ`)
--   because the induction consumes it under the branch's own binders,
--   never at `Δ` itself.
------------------------------------------------------------------------

-- a NAMED existential: "inhabited, and here is the witness".  ⚠ Named for
-- the same reason `RecCall` is — a caller must project WITHOUT
-- `with`-abstracting over the term, which at these sizes OOM-kills the
-- module (measured: exit 143).
data Prv (Γ : Ctx) (T : RTy ⌊ Γ ⌋) : Set where
  prv : (e : RTm ⌊ Γ ⌋) → Γ ⊢ e ∷ T → Prv Γ T

prvTm : {Γ : Ctx} {T : RTy ⌊ Γ ⌋} → Prv Γ T → RTm ⌊ Γ ⌋
prvTm (prv e _) = e

prvOk : {Γ : Ctx} {T : RTy ⌊ Γ ⌋} (p : Prv Γ T) → Γ ⊢ prvTm p ∷ T
prvOk (prv _ d) = d

-- ★ THE BRIDGE reductions cross to reach an `Id`: an identity between the
--   REDUCTS is an identity between the sources.  Every unfold lemma in this
--   module is `⟶*`-valued, so this is how any of them enters an internal
--   statement.
idOfRed : {Γ : Ctx} {T : RTy ⌊ Γ ⌋} {t₁ t₂ u₁ u₂ : RTm ⌊ Γ ⌋} →
          t₁ ⟶* u₁ → t₂ ⟶* u₂ → Prv Γ (Id T u₁ u₂) → Prv Γ (Id T t₁ t₂)
idOfRed r₁ r₂ (prv e d) =
  prv e (⊢conv d (csymᵀ (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ r₁)) (red→≅ᵀ (⟶ᵀ*-Idʳ r₂)))))

-- `(x : A) (ih₁ ih₂ : IH x) → (∀ y q. ih₁ y q ≡ ih₂ y q) → stp x ih₁ ≡ stp x ih₂`
StepExt : (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋) → Set
StepExt Δ A cM m stp =
  {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
  (a ih₁ ih₂ : RTm ⌊ Θ ⌋) →
  Θ ⊢ a ∷ renTy ρ A →
  -- ⚠ NO typing premise on `ih₁`/`ih₂`, deliberately.  A provider reduces
  --   `app (app stp a) ihᵢ` with `ihᵢ` an opaque term (that is what every
  --   step-reduction lemma here already does — `gcd-le-term` takes its
  --   `ih` as a bare `RTm`) and finishes with `idOfRed`, so it never
  --   inspects one; and the consumer has its own (`⊢ihZ-atP`/`⊢ihS-atP`).
  --   An unused premise would only make this harder to discharge.
  ((y q : RTm ⌊ Θ ⌋) →
     Θ ⊢ y ∷ renTy ρ A →
     Θ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) (renTm (extR ρ) m)))
                     (subTm (single a) (renTm (extR ρ) m)) →
     Prv Θ (Id (El (subTm (single y) (renTm (extR ρ) cM)))
               (app (app ih₁ y) q) (app (app ih₂ y) q))) →
  Prv Θ (Id (El (subTm (single a) (renTm (extR ρ) cM)))
            (app (app (renTm ρ stp) a) ih₁)
            (app (app (renTm ρ stp) a) ih₂))

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

  ------------------------------------------------------------------------
  -- ★★★ THE UNFOLD AT AN **ARBITRARY BOUND** — the piece that makes the
  --    recursion RE-ENTERABLE, and hence the shared infrastructure the
  --    end-to-end run needs.
  --
  -- ⚠ WHY `amrec-step-s` IS NOT ENOUGH, stated precisely.  `amrecTm` is
  --   `aAuxTm m` — the auxiliary at the bound `μ x`, and ONLY that bound.
  --   But look at what the step actually receives:
  --
  --     ihS = lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) descS))
  --                             └── the natrec's OWN IH variable
  --
  --   i.e. the induction hypothesis IS the auxiliary at the DECREMENTED
  --   bound `k`.  So a recursive call never lands back on `amrecTm`; it
  --   lands on `auxIH x k`.  A lemma phrased in terms of `amrecTm` can
  --   therefore describe the FIRST unfolding and no other — which is
  --   exactly why the base case composed and no recursing run did.
  --
  -- ★ The fix is to take the bound as a PARAMETER.  `auxIH x n` is the
  --   auxiliary at bound `n`, and the two lemmas below unfold it without
  --   ever mentioning `μ x`.  `amrec-step-z/-s` then become the special
  --   case `n := μ x`, and are re-derived as such below rather than
  --   re-proved — which is the check that the generalisation is faithful.
  ------------------------------------------------------------------------

  -- ⚠⚠ THE INDEX AND THE ARGUMENT ARE DIFFERENT TERMS, and conflating them
  --   is what stops a cycle from chaining.  `auxIH x k` is the auxiliary
  --   SPECIALISED to the carrier `x` (measured: `auxIH x k ≡ auxIH y k` is
  --   NOT refl — the measure family `m` really does mention the slot), and
  --   after one turn it is applied to a DIFFERENT `y`.  So every lemma
  --   below takes the argument `a` separately from the index `x`; with
  --   them identified, turn 2's source could never match turn 1's target.

  -- the IH term the successor branch hands to the step, with the
  -- certificate and the ARGUMENT as parameters
  ihS-atP : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  ihS-atP x a k p =
    subTm (single p)
      (subTm (extS (single a))
        (subTm (extS (extS (single (auxIH x k))))
          (subTm (extS (extS (extS (single k))))
            (subTm (extS (extS (extS (extS (single x))))) ihS))))

  stp-cancel-sAt : (x a k r : RTm ⌊ Δ ⌋) →
    subTm (single r)
      (subTm (extS (single a))
        (subTm (extS (extS (single (auxIH x k))))
          (subTm (extS (extS (extS (single k))))
            (subTm (extS (extS (extS (extS (single x)))))
                   (w (w (w (w (w stp)))))))))
    ≡ stp
  stp-cancel-sAt x a k r =
    trans (cong (λ z → subTm (single r)
                         (subTm (extS (single a))
                           (subTm (extS (extS (single (auxIH x k))))
                             (subTm (extS (extS (extS (single k)))) z))))
                (trans (sub-w⁴ {σ = single x} (w stp))
                       (cong (λ z → w (w (w (w z)))) (wk-single {v = x} stp))))
    (trans (cong (λ z → subTm (single r)
                          (subTm (extS (single a))
                            (subTm (extS (extS (single (auxIH x k)))) z)))
                 (trans (sub-w³ {σ = single k} (w stp))
                        (cong (λ z → w (w (w z))) (wk-single {v = k} stp))))
    (trans (cong (λ z → subTm (single r) (subTm (extS (single a)) z))
                 (trans (sub-w² {σ = single (auxIH x k)} (w stp))
                        (cong (λ z → w (w z)) (wk-single {v = auxIH x k} stp))))
    (trans (cong (subTm (single r))
                 (trans (sub-w {σ = single a} (w stp))
                        (cong w (wk-single {v = a} stp))))
           (wk-single {v = r} stp))))

  a-cancel-sAt : (x a k r : RTm ⌊ Δ ⌋) →
    subTm (single r)
      (subTm (extS (single a))
        (subTm (extS (extS (single (auxIH x k))))
          (subTm (extS (extS (extS (single k))))
            (subTm (extS (extS (extS (extS (single x))))) (var (vs vz))))))
    ≡ a
  a-cancel-sAt x a k r = wk-single {v = r} a

  -- ★ bound ⟶* 0 : the auxiliary takes its VACUOUS branch.
  aux-unfold-z : (x a n p : RTm ⌊ Δ ⌋) → n ⟶* nzero →
                 app (app (auxIH x n) a) p
               ⟶* app (app (subTm (single x) aZBr) a) p
  aux-unfold-z x a n p r =
    ⟶*-appˡ (⟶*-appˡ (⟶*-trans (⟶*-natrecⁿ r) (step (natrec-zero _ _) done)))

  -- ★ bound ⟶* suc k : one layer peels, exposing the STEP at bound `k`.
  aux-unfold-s : (x a n k p : RTm ⌊ Δ ⌋) → n ⟶* nsuc k →
                 app (app (auxIH x n) a) p
               ⟶* app (app (subTm (single (auxIH x k))
                              (subTm (extS (single k))
                                (subTm (extS (extS (single x))) aSBr)))
                           a) p
  aux-unfold-s x a n k p r =
    ⟶*-appˡ (⟶*-appˡ (⟶*-trans (⟶*-natrecⁿ r) (step (natrec-suc _ _ k) done)))

  -- ★★★ …and reaching the CALLER'S step, at an arbitrary bound, WITH THE
  --    TARGET ALLOWED TO MENTION `ih`.
  --
  -- ⚠⚠ THIS `P : RTm → RTm` IS THE WHOLE POINT.  `amrec-step-s` takes a
  --   FLAT `P : RTm`, quantified OUTSIDE `ih`, so `P` structurally cannot
  --   mention the recursive call — which is why the base case composed
  --   through it and no recursing run ever did.  Indexing `P` by `ih`
  --   costs nothing in the proof and is exactly what was missing.
  aux-step-sF : {P : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋} (x a n k p : RTm ⌊ Δ ⌋) →
                n ⟶* nsuc k →
                ((ih : RTm ⌊ Δ ⌋) → app (app stp a) ih ⟶* P ih) →
                app (app (auxIH x n) a) p ⟶* P (ihS-atP x a k p)
  aux-step-sF {P = P} x a n k p r h =
    ⟶*-trans
      (⟶*-trans (aux-unfold-s x a n k p r)
        (step (ξ-appˡ (β _ a)) (step (β _ p) done)))
      (subst (λ z → z ⟶* P (ihS-atP x a k p))
             (sym (cong₂ (λ sf yv → app (app sf yv) (ihS-atP x a k p))
                         (stp-cancel-sAt x a k p)
                         (a-cancel-sAt x a k p)))
             (h (ihS-atP x a k p)))

  -- the flat form is the CONSTANT family — kept because callers whose
  -- result does not mention `ih` (every base case) read better with it.
  aux-step-s : {P : RTm ⌊ Δ ⌋} (x a n k p : RTm ⌊ Δ ⌋) →
               n ⟶* nsuc k →
               ((ih : RTm ⌊ Δ ⌋) → app (app stp a) ih ⟶* P) →
               app (app (auxIH x n) a) p ⟶* P
  aux-step-s {P = P} x a n k p r h = aux-step-sF {P = λ _ → P} x a n k p r h

  -- ★★★ THE LOOP-CLOSER: the `ih` handed over IS the auxiliary at `k`.
  --
  -- ⚠ The certificate is NAMED, not existential.  An existential forces
  --   callers to destructure, and `with`-abstracting over a term this size
  --   OOM-kills the module (measured: exit 143 under the cgroup cap).
  appAt2 : {t f₁ f₂ y₁ y₂ u : RTm ⌊ Δ ⌋} → f₁ ≡ f₂ → y₁ ≡ y₂ →
           t ⟶* app (app f₁ y₁) u → t ⟶* app (app f₂ y₂) u
  appAt2 refl refl h = h

  descS-at : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ →
             RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  descS-at x a k p y q =
    subTm (single q)
      (subTm (extS (single y))
        (subTm (extS (extS (single p)))
          (subTm (extS (extS (extS (single a))))
            (subTm (extS (extS (extS (extS (single (auxIH x k))))))
              (subTm (extS (extS (extS (extS (extS (single k))))))
                (subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                       descS))))))

  aux-cancel : (x a k p y q : RTm ⌊ Δ ⌋) →
    subTm (single q)
      (subTm (extS (single y))
        (subTm (extS (extS (single p)))
          (subTm (extS (extS (extS (single a))))
            (w (w (w (w (auxIH x k))))))))
    ≡ auxIH x k
  aux-cancel x a k p y q =
    trans (cong (λ z → subTm (single q)
                         (subTm (extS (single y))
                           (subTm (extS (extS (single p))) z)))
                (trans (sub-w³ {σ = single a} (w (auxIH x k)))
                       (cong (λ z → w (w (w z))) (wk-single {v = a} (auxIH x k)))))
    (trans (cong (λ z → subTm (single q) (subTm (extS (single y)) z))
                 (trans (sub-w² {σ = single p} (w (auxIH x k)))
                        (cong (λ z → w (w z)) (wk-single {v = p} (auxIH x k)))))
    (trans (cong (subTm (single q))
                 (trans (sub-w {σ = single y} (w (auxIH x k)))
                        (cong w (wk-single {v = y} (auxIH x k)))))
           (wk-single {v = q} (auxIH x k))))

  ih-app : (x a k p y q : RTm ⌊ Δ ⌋) →
           app (app (ihS-atP x a k p) y) q
         ⟶* app (app (auxIH x k) y) (descS-at x a k p y q)
  ih-app x a k p y q =
    appAt2 (aux-cancel x a k p y q) (wk-single {v = q} y)
           (step (ξ-appˡ (β _ y)) (step (β _ q) done))

  ------------------------------------------------------------------------
  -- ★★★★ THE COMPLETE CYCLE — one full turn, and it CHAINS.
  --
  --   app (app (auxIH x n) a) p   ⟶*   app (app (auxIH x k) y) c
  --
  --   The target has the SAME SHAPE as the source with `a := y`, `n := k`,
  --   `p := c` — so the next turn is another `aux-cycle`, and a recursing
  --   run is just iterating it.  That is what no combination of the
  --   previous lemmas could express.
  ------------------------------------------------------------------------
  aux-cycle : (x a n k p y : RTm ⌊ Δ ⌋) {q : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋} →
              n ⟶* nsuc k →
              ((ih : RTm ⌊ Δ ⌋) → app (app stp a) ih ⟶* app (app ih y) (q ih)) →
              app (app (auxIH x n) a) p
            ⟶* app (app (auxIH x k) y) (descS-at x a k p y (q (ihS-atP x a k p)))
  aux-cycle x a n k p y {q = q} r h =
    ⟶*-trans (aux-step-sF {P = λ ih → app (app ih y) (q ih)} x a n k p r h)
             (ih-app x a k p y (q (ihS-atP x a k p)))

  -- ★★★★★ TWO TURNS, COMPOSED.  This is the non-vacuity check for the
  --   whole block: a cycle lemma that cannot be chained would be another
  --   `amrec-step-s` — usable once, useless for a run.  Turn 2 is applied
  --   at `a := y` and `n := k₁`, i.e. literally turn 1's target, with NO
  --   transport in between.  A run of any length is this, iterated.
  aux-cycle² : (x a n k₁ k₂ p y z : RTm ⌊ Δ ⌋)
               {q₁ q₂ : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋} →
               n ⟶* nsuc k₁ → k₁ ⟶* nsuc k₂ →
               ((ih : RTm ⌊ Δ ⌋) → app (app stp a) ih ⟶* app (app ih y) (q₁ ih)) →
               ((ih : RTm ⌊ Δ ⌋) → app (app stp y) ih ⟶* app (app ih z) (q₂ ih)) →
               app (app (auxIH x n) a) p
             ⟶* app (app (auxIH x k₂) z)
                    (descS-at x y k₂ (descS-at x a k₁ p y (q₁ (ihS-atP x a k₁ p)))
                              z (q₂ (ihS-atP x y k₂
                                       (descS-at x a k₁ p y (q₁ (ihS-atP x a k₁ p))))))
  aux-cycle² x a n k₁ k₂ p y z {q₁ = q₁} {q₂ = q₂} r₁ r₂ h₁ h₂ =
    ⟶*-trans (aux-cycle x a n k₁ p y {q = q₁} r₁ h₁)
             (aux-cycle x y k₁ k₂ (descS-at x a k₁ p y (q₁ (ihS-atP x a k₁ p)))
                        z {q = q₂} r₂ h₂)

  ------------------------------------------------------------------------
  -- ★★★ THE TYPING INTERFACE FOR THE AUXILIARY AT AN ARBITRARY BOUND.
  --
  -- ⚠ EVERYTHING IN THE CYCLE BLOCK ABOVE IS `⟶*`-VALUED, and a reduction
  --   can say nothing INTERNAL — no `Id`, no `Π`.  The first thing any
  --   internal statement about the recursion needs is a TYPE for
  --   `auxIH x n`, and the library did not have one: `⊢aAux` types the
  --   auxiliary at the `Δ ▹ A` level, i.e. BEFORE the carrier is
  --   substituted, and nothing carried it across.  These three close that.
  --
  -- ★ There is no new content: it is `⊢aAux` at the WEAKENED bound, then
  --   `⊢[]` at `x`.  The bound rides through `single x` untouched
  --   (`wk-single`) and the other three arguments peel with `mot-at`'s own
  --   lemmas, one level down.
  ------------------------------------------------------------------------

  -- ★ THE CARRIER IS SUBSTITUTED ONCE, INTO THE BRANCHES, and the bound is
  --   then free: `auxIH x n` is `natrec (auxZ x) (auxS x) n` by definition,
  --   so ONE motive and TWO branch derivations serve every bound.
  auxZ : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  auxZ x = subTm (single x) aZBr

  auxS : RTm ⌊ Δ ⌋ → RTm ((⌊ Δ ⌋ ∙) ∙)
  auxS x = subTm (extS (extS (single x))) aSBr

  -- the natrec motive at the AmTΠ level — `aAuxMot` with the carrier gone
  mot₀ : RTy (⌊ Δ ⌋ ∙)
  mot₀ = aAuxB (renTy vs A) (wᶠ cM) (wᶠ m) (var vz)

  mot₀-at : (n : RTm ⌊ Δ ⌋) → subTy (single n) mot₀ ≡ aAuxB A cM m n
  mot₀-at n =
    trans (aAuxB-sub {σ = single n} (renTy vs A) (wᶠ cM) (wᶠ m) (var vz))
          (cong₄ aAuxB (wk-singleTy A) (wᶠ-single cM) (wᶠ-single m) refl)

  mot₀-s : subTy nrs mot₀
         ≡ aAuxB (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m))
                 (nsuc (var (vs vz)))
  mot₀-s =
    trans (aAuxB-sub {σ = nrs} (renTy vs A) (wᶠ cM) (wᶠ m) (var vz))
          (cong₄ aAuxB (nrs-wTy A) (wᶠ-nrs cM) (wᶠ-nrs m) refl)

  ⊢mot₀ : (Δ ▹ Nat) ⊢ty mot₀
  ⊢mot₀ =
    ty-Π (ren-ty dA there)
      (ty-Π (ty-Hom ty-Nat (ren-lemma dm (Ren⊢-ext there)) (⊢var (there here)))
            (ty-El (⊢wk (ren-lemma dcM (Ren⊢-ext there)))))

  -- ⚠ `subTy (extS (single x)) aAuxMot` is the motive AmT hands down; it is
  --   `mot₀` only after the three peels, and Agda cannot invert `subTm` to
  --   see it.  This is the lemma the successor branch's CONTEXT needs.
  mot-x : (x : RTm ⌊ Δ ⌋) → subTy (extS (single x)) aAuxMot ≡ mot₀
  mot-x x =
    trans (aAuxB-sub {σ = extS (single x)}
                     (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m)) (var vz))
          (cong₄ aAuxB
                 (trans (sub-wTy {σ = single x} (renTy vs A))
                        (cong (renTy vs) (wk-singleTy A)))
                 (trans (wᶠ-sub {σ = single x} (wᶠ cM)) (cong wᶠ (wᶠ-single cM)))
                 (trans (wᶠ-sub {σ = single x} (wᶠ m)) (cong wᶠ (wᶠ-single m)))
                 refl)

  ⊢auxZ : {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ auxZ x ∷ subTy (single nzero) mot₀
  ⊢auxZ {x = x} dx =
    ⊢-cast (trans (cong (subTy (single x)) (mot-at nzero))
                  (trans (aAuxB-sub {σ = single x} (renTy vs A) (wᶠ cM) (wᶠ m) nzero)
                         (trans (cong₄ aAuxB (wk-singleTy A) (wᶠ-single cM)
                                             (wᶠ-single m) refl)
                                (sym (mot₀-at nzero)))))
           (⊢[] ⊢aZBr dx)

  ⊢auxS : {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
          ((Δ ▹ Nat) ▹ mot₀) ⊢ auxS x ∷ subTy nrs mot₀
  ⊢auxS {x = x} dx =
    subst (λ T → ((Δ ▹ Nat) ▹ T) ⊢ auxS x ∷ subTy nrs mot₀) (mot-x x)
      (⊢-cast (trans (cong (subTy (extS (extS (single x)))) mot-s)
                     (trans (aAuxB-sub {σ = extS (extS (single x))}
                                       (renTy vs (renTy vs (renTy vs A)))
                                       (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m)))
                                       (nsuc (var (vs vz))))
                            (trans (cong₄ aAuxB peelA peelC peelM refl)
                                   (sym mot₀-s))))
              (sub-lemma ⊢aSBr (Sub⊢-ext (Sub⊢-ext (⊢single dx)))))
    where
      peelA : subTy (extS (extS (single x))) (renTy vs (renTy vs (renTy vs A)))
            ≡ renTy vs (renTy vs A)
      peelA =
        trans (sub-wTy {σ = extS (single x)} (renTy vs (renTy vs A)))
              (cong (renTy vs)
                    (trans (sub-wTy {σ = single x} (renTy vs A))
                           (cong (renTy vs) (wk-singleTy A))))
      peelC : subTm (extS (extS (extS (single x)))) (wᶠ (wᶠ (wᶠ cM)))
            ≡ wᶠ (wᶠ cM)
      peelC =
        trans (wᶠ-sub {σ = extS (single x)} (wᶠ (wᶠ cM)))
              (cong wᶠ (trans (wᶠ-sub {σ = single x} (wᶠ cM))
                              (cong wᶠ (wᶠ-single cM))))
      peelM : subTm (extS (extS (extS (single x)))) (wᶠ (wᶠ (wᶠ m)))
            ≡ wᶠ (wᶠ m)
      peelM =
        trans (wᶠ-sub {σ = extS (single x)} (wᶠ (wᶠ m)))
              (cong wᶠ (trans (wᶠ-sub {σ = single x} (wᶠ m))
                              (cong wᶠ (wᶠ-single m))))

  ⊢auxIH : {x n : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ n ∷ Nat →
           Δ ⊢ auxIH x n ∷ aAuxB A cM m n
  ⊢auxIH {n = n} dx dn =
    ⊢-cast (mot₀-at n) (⊢natrec ⊢mot₀ (⊢auxZ dx) (⊢auxS dx) dn)

  ------------------------------------------------------------------------
  -- ★★★ …AND UNDER AN ARBITRARY AMBIENT RENAMING, which is the form an
  --    INTERNAL induction on the bound actually consumes.
  --
  -- ⚠ WHY THE `Δ`-LEVEL FORM IS NOT ENOUGH.  An induction on the bound is
  --   a `natrec` whose MOTIVE mentions the auxiliary at `var vz` and whose
  --   SUCCESSOR branch mentions it at `nsuc (var (vs vz))` — neither is a
  --   `Δ`-level term, so `⊢auxIH` cannot type either.  ⚠ And re-opening
  --   `AmTΠ` at the deeper context does NOT give the same raw term: its
  --   branches are rebuilt from the WEAKENED parameters, and that they
  --   agree with the weakening of these branches is a naturality lemma the
  --   library does not have.
  --
  -- ★ The dodge is that `renTm ρ` distributes over `natrec` DEFINITIONALLY,
  --   so the renamed branches are on the nose the branches of the renamed
  --   auxiliary — and the scrutinee is then free to be anything, including
  --   a variable.  Three renamings of the three pieces above; no naturality
  --   of the combinator is needed at all.
  ------------------------------------------------------------------------

  motAt : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') → RTy (Γ' ∙)
  motAt ρ = aAuxB (renTy vs (renTy ρ A)) (wᶠ (renTm (extR ρ) cM))
                  (wᶠ (renTm (extR ρ) m)) (var vz)

  motAt-ren : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') → renTy (extR ρ) mot₀ ≡ motAt ρ
  motAt-ren ρ =
    trans (aAuxB-ren {ρ = extR ρ} (renTy vs A) (wᶠ cM) (wᶠ m) (var vz))
          (cong₄ aAuxB (ren-wTy A) (ren-wᶠ cM) (ren-wᶠ m) refl)

  motAt-at : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (n : RTm Γ') →
             subTy (single n) (motAt ρ)
           ≡ aAuxB (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m) n
  motAt-at ρ n =
    trans (aAuxB-sub {σ = single n} (renTy vs (renTy ρ A))
                     (wᶠ (renTm (extR ρ) cM)) (wᶠ (renTm (extR ρ) m)) (var vz))
          (cong₄ aAuxB (wk-singleTy (renTy ρ A))
                       (wᶠ-single (renTm (extR ρ) cM))
                       (wᶠ-single (renTm (extR ρ) m)) refl)

  motAt-s : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') →
            subTy nrs (motAt ρ)
          ≡ aAuxB (renTy vs (renTy vs (renTy ρ A)))
                  (wᶠ (wᶠ (renTm (extR ρ) cM))) (wᶠ (wᶠ (renTm (extR ρ) m)))
                  (nsuc (var (vs vz)))
  motAt-s ρ =
    trans (aAuxB-sub {σ = nrs} (renTy vs (renTy ρ A))
                     (wᶠ (renTm (extR ρ) cM)) (wᶠ (renTm (extR ρ) m)) (var vz))
          (cong₄ aAuxB (nrs-wTy (renTy ρ A))
                       (wᶠ-nrs (renTm (extR ρ) cM))
                       (wᶠ-nrs (renTm (extR ρ) m)) refl)

  -- ⚠ `renTm ρ (auxIH x n) ≡ auxAt ρ x (renTm ρ n)` holds by `refl` — that
  --   is the whole point of taking the bound separately.
  auxAt : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (n : RTm Γ') → RTm Γ'
  auxAt ρ x n = natrec (renTm ρ (auxZ x)) (renTm (extR (extR ρ)) (auxS x)) n

  ⊢auxAt : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {x : RTm ⌊ Δ ⌋} {n : RTm ⌊ Θ ⌋} →
           Ren⊢ Δ Θ ρ → Δ ⊢ x ∷ A → Θ ⊢ n ∷ Nat →
           Θ ⊢ auxAt ρ x n
             ∷ aAuxB (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m) n
  ⊢auxAt {Θ = Θ} {ρ = ρ} {x = x} {n = n} h dx dn =
    ⊢-cast (motAt-at ρ n) (⊢natrec dMot dZ dS dn)
    where
      dMot : (Θ ▹ Nat) ⊢ty motAt ρ
      dMot = subst (λ T → (Θ ▹ Nat) ⊢ty T) (motAt-ren ρ)
                   (ren-ty ⊢mot₀ (Ren⊢-ext h))

      dZ : Θ ⊢ renTm ρ (auxZ x) ∷ subTy (single nzero) (motAt ρ)
      dZ = ⊢-cast (trans (cong (renTy ρ) (mot₀-at nzero))
                         (trans (aAuxB-ren {ρ = ρ} A cM m nzero)
                                (sym (motAt-at ρ nzero))))
                  (ren-lemma (⊢auxZ dx) h)

      peelA : renTy (extR (extR ρ)) (renTy vs (renTy vs A))
            ≡ renTy vs (renTy vs (renTy ρ A))
      peelA = trans (ren-wTy {ρ = extR ρ} (renTy vs A))
                    (cong (renTy vs) (ren-wTy {ρ = ρ} A))

      peelC : renTm (extR (extR (extR ρ))) (wᶠ (wᶠ cM))
            ≡ wᶠ (wᶠ (renTm (extR ρ) cM))
      peelC = trans (ren-wᶠ {ρ = extR ρ} (wᶠ cM))
                    (cong wᶠ (ren-wᶠ {ρ = ρ} cM))

      peelM : renTm (extR (extR (extR ρ))) (wᶠ (wᶠ m))
            ≡ wᶠ (wᶠ (renTm (extR ρ) m))
      peelM = trans (ren-wᶠ {ρ = extR ρ} (wᶠ m))
                    (cong wᶠ (ren-wᶠ {ρ = ρ} m))

      dS : ((Θ ▹ Nat) ▹ motAt ρ) ⊢ renTm (extR (extR ρ)) (auxS x)
             ∷ subTy nrs (motAt ρ)
      dS = subst (λ T → ((Θ ▹ Nat) ▹ T) ⊢ renTm (extR (extR ρ)) (auxS x)
                          ∷ subTy nrs (motAt ρ))
                 (motAt-ren ρ)
                 (⊢-cast (trans (cong (renTy (extR (extR ρ))) mot₀-s)
                                (trans (aAuxB-ren {ρ = extR (extR ρ)}
                                                  (renTy vs (renTy vs A))
                                                  (wᶠ (wᶠ cM)) (wᶠ (wᶠ m))
                                                  (nsuc (var (vs vz))))
                                       (trans (cong₄ aAuxB peelA peelC peelM refl)
                                              (sym (motAt-s ρ)))))
                         (ren-lemma (⊢auxS dx) (Ren⊢-ext (Ren⊢-ext h))))

  -- ★ …and the auxiliary APPLIED: the argument's measure slot is
  --   `subTm (single a) m`, which is why the certificate's type mentions
  --   `a` and not `x` — the same separation the cycle lemmas make.
  ⊢aux-app : {x a n p : RTm ⌊ Δ ⌋} →
             Δ ⊢ x ∷ A → Δ ⊢ n ∷ Nat → Δ ⊢ a ∷ A →
             Δ ⊢ p ∷ Hom Nat (subTm (single a) m) n →
             Δ ⊢ app (app (auxIH x n) a) p ∷ El (subTm (single a) cM)
  ⊢aux-app {a = a} {n = n} {p = p} dx dn da dp =
    ⊢-cast (cong El (wk-single {v = p} (subTm (single a) cM)))
      (⊢app (⊢-cast (cong₂ (λ b c → Π (Hom Nat (subTm (single a) m) b) (El c))
                           (wk-single {v = a} n) (sub-w {σ = single a} cM))
                    (⊢app (⊢auxIH dx dn) da))
            dp)

  -- ★★ THE NON-VACUITY WITNESS, and it is the one instance the combinator
  --   itself uses: bound `μ x`, certificate `reflTm (μ x)`, argument `x`.
  --   That term is exactly `amrec-β`'s target, so the pair above types the
  --   β-reduct of `app amrecTm x` — the premise is dischargeable at the
  --   arguments the library actually reduces to.
  ⊢aux-at-μ : {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
              Δ ⊢ app (app (auxIH x (subTm (single x) m)) x)
                      (reflTm (subTm (single x) m))
                ∷ El (subTm (single x) cM)
  ⊢aux-at-μ dx = ⊢aux-app dx (⊢[] dm dx) dx (⊢le-refl (⊢[] dm dx))

  amrec-step-s : {P : RTm ⌊ Δ ⌋} (x k : RTm ⌊ Δ ⌋) →
                 subTm (single x) m ⟶* nsuc k →
                 ((ih : RTm ⌊ Δ ⌋) → app (app stp x) ih ⟶* P) →
                 app amrecTm x ⟶* P
  -- ★ now a SPECIAL CASE of `aux-step-s` at `n := μ x`, not a second
  --   proof: `amrecTm` β-reduces to the auxiliary at that bound, and the
  --   general lemma takes it from there.
  amrec-step-s {P = P} x k r h =
    ⟶*-trans (amrec-β x)
             (aux-step-s x x (subTm (single x) m) k
                         (reflTm (subTm (single x) m)) r h)

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
