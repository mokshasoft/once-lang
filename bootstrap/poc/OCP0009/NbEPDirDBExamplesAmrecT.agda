------------------------------------------------------------------------
-- ⚠ PARTIAL: both branches and `⊢aAux` are GREEN.  Still to come: the Π
--   form, D7's unfolding lemma, and the SpikeDivC rewrite that measures
--   the use-site saving.
--
-- ⚠ P1 IN PRACTICE: use `⊢wkᶠ` for a FAMILY, `⊢wk` for a term — they
--   produce terms that look interchangeable and are not.  But note both of
--   the successor branch's real bugs were the weakening COUNT, not the
--   kind; the helper makes the choice visible, not the arithmetic right.
--
-- ★ THE DESIGN RISK IS RETIRED.  `⊢absurd` is CODE-indexed, so the whole
--   D4 shape depended on the vacuous branch's ex-falso result type landing
--   exactly on the IH slot.  It does: `ihZ`'s type is literally the slot's
--   `El (w (wᶠ (wᶠ cM)))`, with NO conversion.  Keeping the motive a code
--   FAMILY rather than an `RTy` family is what buys that.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- OCP-0009 — ★★ MEASURE RECURSION, D4: CARRIER AS A TYPE, MOTIVE AND
-- MEASURE AS FAMILIES.  The β-tax fix.
--
-- `NbEPDirDBExamplesAmrecC` takes the motive and measure as object-language
-- FUNCTIONS — `cP : Π (El cA) U`, `μ : Π (El cA) Nat` — so every use of
-- either is a β-REDEX that never reduces on its own.  Measured in
-- SpikeDivC's fifty-line step: 4 × elCP, 4 × elNat, 3 × asA, 1 × homμ.
--
-- ★ HERE THEY ARE PRE-APPLIED:
--
--     A  : RTy ⌊ Δ ⌋        the carrier, a TYPE — no code, no `El`
--     cM : RTm (⌊ Δ ⌋ ∙)    the motive, a CODE FAMILY over the carrier var
--     m  : RTm (⌊ Δ ⌋ ∙)    the measure, a TERM over the carrier var
--
--   and then, at the binder where the carrier variable IS `x`:
--
--     μ x  is literally  `m`          — no application, no redex
--     P x  is literally  `El cM`      — no application, no redex
--
--   `μ y` for the IH's fresh `y` is `wᶠ m`, a RENAMING.  There is not one
--   `app` in any of the three types below.
--
-- ⚠ WHY THE MOTIVE STAYS A CODE, and is not an `RTy` family.  The vacuous
--   branch builds its IH by EX FALSO, and `⊢absurd` is CODE-INDEXED:
--       ⊢absurd : Γ ⊢ c ∷ U → Γ ⊢ e ∷ base → Γ ⊢ absurd c e ∷ El c
--   so ex falso can only produce `El c`.  That is deliberate — the kernel
--   notes a `⊢ty C` premise "could never rebuild" the inversion, since
--   `⊢conv` moves the result type.  So the motive is a code FAMILY
--   (pre-applied) rather than a code-valued FUNCTION (applicable): all of
--   the β saving, none of the kernel change.
--
-- ⇒ THE WHOLE OF D4 IS A LIBRARY CHANGE.  Nothing is added to `RTy`,
--   `RTm` or the judgments; `subTy`/`subTm`/`single`/`extR` already exist.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesAmrecT where

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
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ren-ty; ren-lemma; Ren⊢; Ren⊢-ext )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLexC using ( w; cong₄; sub-w; ren-w )

------------------------------------------------------------------------
-- ★ `wᶠ` — weaken a FAMILY under a new binder, keeping the family's own
--   variable in place.  This is the one new piece of plumbing D4 needs,
--   and `ren-w` already covers its naturality.
------------------------------------------------------------------------

wᶠ : {Γ : Cx} → RTm (Γ ∙) → RTm ((Γ ∙) ∙)
wᶠ = renTm (extR vs)

-- ★ `⊢wkᶠ` is to `wᶠ` what `⊢wk` is to `w`: it inserts a slot BELOW the
--   family's own variable, so the family keeps pointing at the carrier.
--   ⚠ Reach for this, not `⊢wk`, whenever the subject is a FAMILY — the
--   two produce terms that look interchangeable and are not (P1).
⊢wkᶠ : {Γ : Ctx} {A B : RTy ⌊ Γ ⌋} {t : RTm (⌊ Γ ⌋ ∙)} {T : RTy (⌊ Γ ⌋ ∙)} →
       (Γ ▹ A) ⊢ t ∷ T → ((Γ ▹ B) ▹ renTy vs A) ⊢ wᶠ t ∷ renTy (extR vs) T
⊢wkᶠ d = ren-lemma d (Ren⊢-ext there)

------------------------------------------------------------------------
-- THE THREE TYPES — and there is not one `app` in them.
------------------------------------------------------------------------

-- ★ the IH at an EXPLICIT `μ x`.  `aIHT` is its instance where the
--   carrier variable is `x`, so `μ x` is `m` itself — which is the whole
--   point of pre-applying the measure.
aIHTat' : {Γ : Cx} (A : RTy Γ) (m mx : RTm (Γ ∙)) (cm : RTm ((Γ ∙) ∙)) → RTy Γ
aIHTat' A m mx cm = Π A (Π (Hom Nat (nsuc m) mx) (El cm))

aIHTat : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (μx : RTm Γ) → RTy Γ
aIHTat A cM m μx = aIHTat' A m (w μx) (w cM)

-- `(y : A) → μ y < μ x → P y`, at the binder where `x` is the carrier var
aIHT : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) → RTy (Γ ∙)
aIHT A cM m = aIHTat (renTy vs A) (wᶠ cM) (wᶠ m) m

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
wk-singleTy : {Γ : Cx} {v : RTm Γ} (T : RTy Γ) → subTy (single v) (renTy vs T) ≡ T
wk-singleTy T = trans (subTy-renTy T) (subTy-id T)

-- ★ THE FAMILY VERSION.  `extS (single v) ₛ∘ᵣ extR vs` is the IDENTITY:
--   the family's own variable is held in place by both, and everything
--   below it is weakened then immediately substituted back.
wᶠ-single : {Γ : Cx} {v : RTm Γ} (t : RTm (Γ ∙)) →
            subTm (extS (single v)) (wᶠ t) ≡ t
wᶠ-single t =
  trans (subTm-renTm t) (trans (subTm-cong bridge t) (subTm-id t))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl

-- `nrs` on a weakened type / family: one more weakening, as for `nrs-w`
nrs-wTy : {Γ : Cx} (T : RTy Γ) → subTy nrs (renTy vs T) ≡ renTy vs (renTy vs T)
nrs-wTy T =
  trans (subTy-renTy T)
        (sym (trans (renTy-renTy T) (ren-subTy T)))
  where
    ren-subTy : (T : RTy _) → renTy _ T ≡ subTy (λ x → var _) T
    ren-subTy T = trans (cong (renTy _) (sym (subTy-id T))) (renTy-subTy T)

-- ⚠ this one needs a pointwise BRIDGE: `extS nrs ₛ∘ᵣ extR vs` and
--   `extR vs ∘ᵣ extR vs` agree, but only after casing on the variable —
--   eta alone does not see it, unlike `sub-w`/`ren-w`.
wᶠ-nrs : {Γ : Cx} (t : RTm (Γ ∙)) → subTm (extS nrs) (wᶠ t) ≡ wᶠ (wᶠ t)
wᶠ-nrs t =
  trans (subTm-renTm t)
        (trans (subTm-cong bridge t)
               (sym (trans (renTm-renTm t) (ren-sub' t))))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl
    ren-sub' : (u : RTm _) → renTm _ u ≡ subTm (λ x → var _) u
    ren-sub' u = trans (cong (renTm _) (sym (subTm-id u))) (renTm-subTm u)

-- ⚠ bridge: the family under TWO `extR vs` then `single (var (vs vz))`
--   collapses to a single weakening.  This is the spine's cancellation.
wᶠ²-single : {Γ : Cx} (t : RTm (Γ ∙)) →
             subTm (single (var (vs vz))) (wᶠ (wᶠ t)) ≡ w t
wᶠ²-single t =
  trans (subTm-renTm (wᶠ t))
        (trans (subTm-renTm t)
               (trans (subTm-cong bridge t) (sym (ren-sub'' t))))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl
    ren-sub'' : (u : RTm _) → renTm vs u ≡ subTm (λ x → var (vs x)) u
    ren-sub'' u = trans (cong (renTm vs) (sym (subTm-id u))) (renTm-subTm u)

-- the renaming twins the step's reassociation needs
ren-wTy : {Γ Δ : Cx} {ρ : Ren Γ Δ} (T : RTy Γ) →
          renTy (extR ρ) (renTy vs T) ≡ renTy vs (renTy ρ T)
ren-wTy T = trans (renTy-renTy T) (sym (renTy-renTy T))

-- ⚠ bridge again: `extR (extR ρ) ∘ᵣ extR vs` and `extR vs ∘ᵣ extR ρ`
--   agree only after casing, exactly as in `wᶠ-nrs`.
ren-wᶠ : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
         renTm (extR (extR ρ)) (wᶠ t) ≡ wᶠ (renTm (extR ρ) t)
ren-wᶠ t =
  trans (renTm-renTm t) (trans (renTm-cong bridge t) (sym (renTm-renTm t)))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl

aIHT-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m : RTm (Γ ∙)) →
           renTy (extR ρ) (aIHT A cM m)
         ≡ aIHT (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
aIHT-ren {ρ = ρ} A cM m =
  cong₄ (λ a p q c → Π a (Π (Hom Nat (nsuc p) q) (El c)))
        (ren-wTy A) (ren-wᶠ m) (ren-w {ρ = extR ρ} m)
        (trans (ren-w {ρ = extR (extR ρ)} (wᶠ cM)) (cong w (ren-wᶠ cM)))

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
aIHT-fit : {Γ : Cx} {X : RTm Γ} (A : RTy Γ) (cM m : RTm (Γ ∙)) →
           subTy (single X) (aIHT A cM m)
         ≡ aIHTat A cM m (subTm (single X) m)
aIHT-fit {X = X} A cM m =
  cong₄ aIHTat' (wk-singleTy A) (wᶠ-single m) (sub-w m)
        (trans (sub-w {σ = extS (single X)} (wᶠ cM)) (cong w (wᶠ-single cM)))

-- ★ the `⊢wk` ladder (D5: these are iterates of ONE lemma and should be
--   indexed, not listed — recorded, not fixed).
aAuxB-w² : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) →
           renTy vs (renTy vs (aAuxB A cM m n))
         ≡ aAuxB (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m)) (w (w n))
aAuxB-w² A cM m n =
  trans (cong (renTy vs) (aAuxB-ren A cM m n))
        (aAuxB-ren (renTy vs A) (wᶠ cM) (wᶠ m) (w n))

aAuxB-w⁵ : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) →
           renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (aAuxB A cM m n)))))
         ≡ aAuxB (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs A)))))
                 (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM))))) (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m)))))
                 (w (w (w (w (w n)))))
aAuxB-w⁵ A cM m n =
  trans (cong (renTy vs) (cong (renTy vs) (cong (renTy vs) (aAuxB-w² A cM m n))))
  (trans (cong (renTy vs) (cong (renTy vs) (aAuxB-ren (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m)) (w (w n)))))
  (trans (cong (renTy vs) (aAuxB-ren (renTy vs (renTy vs (renTy vs A))) (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m))) (w (w (w n)))))
         (aAuxB-ren (renTy vs (renTy vs (renTy vs (renTy vs A))))
                    (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m)))) (w (w (w (w n)))))))

aStepT-w⁴ : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) →
            renTy vs (renTy vs (renTy vs (renTy vs (aStepT A cM m))))
          ≡ aStepT (renTy vs (renTy vs (renTy vs (renTy vs A))))
                   (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
aStepT-w⁴ A cM m =
  trans (cong (renTy vs) (cong (renTy vs) (cong (renTy vs) (aStepT-ren A cM m))))
  (trans (cong (renTy vs) (cong (renTy vs) (aStepT-ren (renTy vs A) (wᶠ cM) (wᶠ m))))
  (trans (cong (renTy vs) (aStepT-ren (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m))))
         (aStepT-ren (renTy vs (renTy vs (renTy vs A)))
                     (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m))))))

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
  stp-w² = trans (cong (renTy vs) (aStepT-ren A cM m))
                 (aStepT-ren (renTy vs A) (wᶠ cM) (wᶠ m))

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
  stp-w⁴ = aStepT-w⁴ A cM m

  ih₀-w⁵ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs aAuxMot))))
         ≡ aAuxB (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs A))))))
                 (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM)))))) (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m))))))
                 (w (w (w (w (w (var vz))))))
  ih₀-w⁵ = aAuxB-w⁵ (renTy vs A) (wᶠ cM) (wᶠ m) (var vz)

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
