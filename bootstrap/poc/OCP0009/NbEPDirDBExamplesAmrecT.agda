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

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
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

------------------------------------------------------------------------
-- THE THREE TYPES — and there is not one `app` in them.
------------------------------------------------------------------------

-- `(y : A) → μ y < μ x → P y`, at the binder where `x` is the carrier var
aIHT : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) → RTy (Γ ∙)
aIHT A cM m =
  Π (renTy vs A)
    (Π (Hom Nat (nsuc (wᶠ m)) (w m))
       (El (w (wᶠ cM))))

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
