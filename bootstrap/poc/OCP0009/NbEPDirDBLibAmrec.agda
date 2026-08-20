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
-- Ships FOUR things, and a caller needs all four:
--   * `⊢amrecΠ`  the combinator as a closed Π-typed TERM;
--   * `⊢amrecPt` the pointwise form, DERIVED — one `⊢app`, no cast;
--   * `amrec-β` / `amrec-unfold-z` / `amrec-unfold-s`, the COMPUTATION
--     rule, so a caller never re-derives how `amrecTm` unfolds (D7);
--   * `irr-ind` and `amrec-unfold-Id`, the INTERNAL forms of both — an
--     object-language `Id`, not a `⟶*`.
--
-- ★★ THE INTERNAL LAYER, and why it exists.  Everything `⟶*`-valued says
--   nothing INSIDE the language: no `Id`, no `Π`, so no defining equation
--   at a variable.  `app amrecTm x` reduces exactly to
--   `app (app (auxIH x μx) x) (reflTm μx)` and no further — the auxiliary's
--   `natrec` is stuck on the neutral `μ x`.  Moving off that bound is
--   CERTIFICATE- AND BOUND-IRRELEVANCE:
--
--     irr-ind : (n₂ : Nat) (a : A) (c₁ : μ a ≤ n) (c₂ : μ a ≤ n₂) →
--                 aux x n a c₁ ≡ aux y n₂ a c₂
--
--   proved by induction on the bound from `StepExt`, and then
--
--     amrec-unfold-Id : μ x ≤ suc k  →  amrecTm x ≡ stp x ⟨ih⟩
--
--   ⚠ CONDITIONAL on `StepExt`, which is the CALLER's to discharge and
--   which nothing in this tree supplies yet.  `amrec-unfold-Id-red` is the
--   non-vacuity witness for the OTHER premise.
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
        ; renTm-renTm; renTy-renTy; renTm-cong; renTy-cong; subTy-cong; idₛ
        ; renTy-subTy; renTm-subTm; ordtr-cong₅; Id-cong₃ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _∋_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; _⟶*_; done; step; β; ξ-appˡ; natrec-zero; natrec-suc
        ; ⊢lam; ⊢app; _⊢ty_; ⊢conv; csymᵀ; ctrnᵀ; ⊢⌜Id⌝; El-⌜Id⌝
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Id )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-Homʳ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ∋-cast; ren-ty; ren-lemma; Ren⊢; Ren⊢-ext
        ; sub-ty; sub-lemma; Sub⊢; Sub⊢-ext; ⊢single )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibOrd using ( ⊢strong-base'; ⊢strong-step )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; ⊢wkᶠ; cong₃; cong₄; sub-w; sub-w²; sub-w³; sub-w⁴; ren-w; wk-singleTy; wᶠ-single
        ; wᶠ¹-single; wᶠ²-single; nrs-wTy; wᶠ-nrs; ren-wTy; ren-wᶠ; sub-wTy; wᶠ-sub
        ; ren-sub; ren-w²; ren-w³; nrs-w; cong₅; cong₆; _∙^_; w^; wTy^; wᶠ^ )
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

-- ★ a `Prv` transports along a typed renaming, and it is two lines: `Prv`
--   is just a term plus its derivation, so `ren-lemma` does all the work.
--   ⚠ Nothing renamed a `Prv` before 2026-08-20; every client that needed
--   a renamed fact restated it instead.
-- ⚠ HOISTED from inside `AmTΠ` (2026-08-20).  It never depended on the
--   module's parameters, and a top-level client could not see it — the
--   third time today a module-LOCAL definition of a parameter-independent
--   fact had to be lifted (`mId`, `idR`, now this).
prv-cast : {Γ : Ctx} {T T' : RTy ⌊ Γ ⌋} → T ≡ T' → Prv Γ T → Prv Γ T'
prv-cast refl pp = pp

prv-ren : {Γ Θ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Θ ⌋} → Ren⊢ Γ Θ ρ →
          {T : RTy ⌊ Γ ⌋} → Prv Γ T → Prv Θ (renTy ρ T)
prv-ren ρ⊢ (prv e d) = prv (renTm _ e) (ren-lemma d ρ⊢)

-- ★ THE BRIDGE reductions cross to reach an `Id`: an identity between the
--   REDUCTS is an identity between the sources.  Every unfold lemma in this
--   module is `⟶*`-valued, so this is how any of them enters an internal
--   statement.
idOfRed : {Γ : Ctx} {T : RTy ⌊ Γ ⌋} {t₁ t₂ u₁ u₂ : RTm ⌊ Γ ⌋} →
          t₁ ⟶* u₁ → t₂ ⟶* u₂ → Prv Γ (Id T u₁ u₂) → Prv Γ (Id T t₁ t₂)
idOfRed r₁ r₂ (prv e d) =
  prv e (⊢conv d (csymᵀ (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ r₁)) (red→≅ᵀ (⟶ᵀ*-Idʳ r₂)))))

-- ★ …and the SAME BRIDGE the other way: an identity between two terms is
--   an identity between their reducts.  ⚠ Both directions are needed and
--   they are not interchangeable — a proof arrives at whichever end its
--   producer left it, and only one of the two ends is the caller's.
idToRed : {Γ : Ctx} {T : RTy ⌊ Γ ⌋} {t₁ t₂ u₁ u₂ : RTm ⌊ Γ ⌋} →
          t₁ ⟶* u₁ → t₂ ⟶* u₂ → Prv Γ (Id T t₁ t₂) → Prv Γ (Id T u₁ u₂)
idToRed r₁ r₂ (prv e d) =
  prv e (⊢conv d (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ r₁)) (red→≅ᵀ (⟶ᵀ*-Idʳ r₂))))

-- ★ `Ren⊢` under one more AMBIENT binder.  `Ren⊢-ext` grows the renaming
--   with a matching slot on BOTH sides; this grows only the TARGET, which
--   is what an ambient TOWER `vs^n` needs — and a tower is exactly what an
--   internal induction's motive sits under.  ⚠ Reach for this, not
--   `Ren⊢-ext`, whenever the new binder is NOT in the source context.
wR : {Γ Θ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Θ ⌋} {B : RTy ⌊ Θ ⌋} →
     Ren⊢ Γ Θ ρ → Ren⊢ Γ (Θ ▹ B) (λ v → vs (ρ v))
wR h v = ∋-cast (renTy-renTy _) (there (h v))

------------------------------------------------------------------------
-- ★★★ THE POINTWISE CALCULUS — every peel the induction needs, from ONE
--    observation: a substitution that meets a renaming is another
--    RENAMING, and which one is decided VARIABLE-BY-VARIABLE.
--
-- ⚠ WHY THIS, RATHER THAN MORE `wᶠ`-TOWER LEMMAS.  The induction pushes
--   `single _` and `nrs` past an AMBIENT tower `vs^n` that grows with the
--   depth, and a tower lemma has to be re-proved at every rung (that is
--   what `wᶠ¹/²/³-single` are, and they ran out at three).  Stated
--   pointwise, the SAME four lemmas serve every rung and every branch:
--   the caller supplies a two-case bridge and gets the collapse.
------------------------------------------------------------------------

ren-subTy' : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (T : RTy Γ) →
             renTy ρ T ≡ subTy (λ x → var (ρ x)) T
ren-subTy' {ρ = ρ} T = trans (cong (renTy ρ) (sym (subTy-id T))) (renTy-subTy T)

subren : {Γ Γ' Γ'' : Cx} {σ : Sub Γ' Γ''} {ρ : Ren Γ Γ'} {ρ' : Ren Γ Γ''} →
         (∀ v → σ (ρ v) ≡ var (ρ' v)) →
         (t : RTm Γ) → subTm σ (renTm ρ t) ≡ renTm ρ' t
subren h t = trans (subTm-renTm t) (trans (subTm-cong h t) (sym (ren-sub t)))

subrenTy : {Γ Γ' Γ'' : Cx} {σ : Sub Γ' Γ''} {ρ : Ren Γ Γ'} {ρ' : Ren Γ Γ''} →
           (∀ v → σ (ρ v) ≡ var (ρ' v)) →
           (T : RTy Γ) → subTy σ (renTy ρ T) ≡ renTy ρ' T
subrenTy h T = trans (subTy-renTy T) (trans (subTy-cong h T) (sym (ren-subTy' T)))

renren : {Γ Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''} {ρ : Ren Γ Γ'} {ρ' : Ren Γ Γ''} →
         (∀ v → ϑ (ρ v) ≡ ρ' v) →
         (t : RTm Γ) → renTm ϑ (renTm ρ t) ≡ renTm ρ' t
renren h t = trans (renTm-renTm t) (renTm-cong h t)

renrenTy : {Γ Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''} {ρ : Ren Γ Γ'} {ρ' : Ren Γ Γ''} →
           (∀ v → ϑ (ρ v) ≡ ρ' v) →
           (T : RTy Γ) → renTy ϑ (renTy ρ T) ≡ renTy ρ' T
renrenTy h T = trans (renTy-renTy T) (renTy-cong h T)

-- ★ …and the bridges themselves lift under a binder, so a condition proved
--   once at the ambient level serves at every depth the branches reach.
extcond : {Γ Γ' Γ'' : Cx} {σ : Sub Γ' Γ''} {ρ : Ren Γ Γ'} {ρ' : Ren Γ Γ''} →
          (∀ v → σ (ρ v) ≡ var (ρ' v)) →
          (∀ v → extS σ (extR ρ v) ≡ var (extR ρ' v))
extcond h vz     = refl
extcond h (vs v) = cong (renTm vs) (h v)

extcondR : {Γ Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''} {ρ : Ren Γ Γ'} {ρ' : Ren Γ Γ''} →
           (∀ v → ϑ (ρ v) ≡ ρ' v) →
           (∀ v → extR ϑ (extR ρ v) ≡ extR ρ' v)
extcondR h vz     = refl
extcondR h (vs v) = cong vs (h v)

-- ★★ THE THIRD COMPOSITE: a RENAMING that meets a SUBSTITUTION.
--
-- `subren` and `renren` cover sub∘ren and ren∘ren.  ren∘sub is the one a
-- CALLER of `StepExt` needs, because the pointwise premise is
-- renaming-indexed and every term it speaks about (`ihS-atR`, `auxAt`) is
-- built as a tower of substitutions.  Same one-line shape as its two
-- siblings: fuse both sides to a single substitution and bridge them.
--
-- ⚠ The bridge relates `renTm ϑ (σ v)` to `σ' (ϑ' v)` — FOUR maps, not
--   three, because ren∘sub has to re-emit both a substitution and a
--   renaming.  That is why it needs its own `extcond`.
rensub : {Γ Γ' Γ'' Γ₃ : Cx} {σ : Sub Γ Γ'} {ϑ : Ren Γ' Γ''}
         {σ' : Sub Γ₃ Γ''} {ϑ' : Ren Γ Γ₃} →
         (∀ v → renTm ϑ (σ v) ≡ σ' (ϑ' v)) →
         (t : RTm Γ) → renTm ϑ (subTm σ t) ≡ subTm σ' (renTm ϑ' t)
rensub h t = trans (renTm-subTm t) (trans (subTm-cong h t) (sym (subTm-renTm t)))

extcondRS : {Γ Γ' Γ'' Γ₃ : Cx} {σ : Sub Γ Γ'} {ϑ : Ren Γ' Γ''}
            {σ' : Sub Γ₃ Γ''} {ϑ' : Ren Γ Γ₃} →
            (∀ v → renTm ϑ (σ v) ≡ σ' (ϑ' v)) →
            (∀ v → renTm (extR ϑ) (extS σ v) ≡ extS σ' (extR ϑ' v))
extcondRS h vz = refl
extcondRS {σ = σ} {ϑ = ϑ} h (vs v) =
  trans (renren {ϑ = extR ϑ} {ρ = vs} {ρ' = λ u → vs (ϑ u)} (λ _ → refl) (σ v))
        (trans (sym (renren {ϑ = vs} {ρ = ϑ} {ρ' = λ u → vs (ϑ u)}
                            (λ _ → refl) (σ v)))
               (cong (renTm vs) (h v)))

-- ★ the bridge for the commonest substitution of all.  ⚠ It needs the case
--   split even though both cases are `refl`: `single` matches on the
--   variable, so neither side computes until it is given one.
singleBr : {Γ Γ' : Cx} {ϑ : Ren Γ Γ'} (t : RTm Γ) →
           ∀ v → renTm ϑ (single t v) ≡ single (renTm ϑ t) (extR ϑ v)
singleBr t vz     = refl
singleBr t (vs v) = refl

-- ★ …and the composite the two of them make, which is the SHAPE OF A
--   MEASURE: `μ` at a renamed carrier.  Generic in the body, so `m` and
--   `cM` share it.
sub1-ren : {Γ Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''} (θ : Ren Γ Γ') (θ' : Ren Γ Γ'') →
           (∀ v → ϑ (θ v) ≡ θ' v) → (a : RTm Γ') (t : RTm (Γ ∙)) →
           renTm ϑ (subTm (single a) (renTm (extR θ) t))
         ≡ subTm (single (renTm ϑ a)) (renTm (extR θ') t)
sub1-ren {ϑ = ϑ} θ θ' br a t =
  trans (rensub {ϑ' = extR ϑ} (singleBr a) (renTm (extR θ) t))
        (cong (subTm (single (renTm ϑ a))) (renren (extcondR br) t))

-- ★ TYPED renamings compose — pointwise, into a THIRD renaming `ρ'`.
--
-- ⚠ NOT `Ren⊢ Γ Θ' (λ v → ϑ (ρ v))`.  Bridging to a named `ρ'` is what
--   keeps every type downstream written in one renaming instead of a
--   composition, and it is the discipline `auxAt-renʳ`/`irrT-ren` already
--   follow.  Composition-shaped types are what made the tower lemmas
--   proliferate.
Ren⊢-comp : {Γ Θ Θ' : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Θ ⌋} {ϑ : Ren ⌊ Θ ⌋ ⌊ Θ' ⌋}
            {ρ' : Ren ⌊ Γ ⌋ ⌊ Θ' ⌋} →
            Ren⊢ Γ Θ ρ → Ren⊢ Θ Θ' ϑ → (∀ v → ϑ (ρ v) ≡ ρ' v) →
            Ren⊢ Γ Θ' ρ'
Ren⊢-comp {Θ' = Θ'} {ρ' = ρ'} hρ hϑ br {x = x} {A = A} v =
  subst (λ u → Θ' ∋ u ∷ renTy ρ' A) (br x)
        (∋-cast (renrenTy br A) (hϑ (hρ v)))

-- ★ …and the degenerate case: a renaming that is POINTWISE the identity is
--   the identity.  `extR` of the identity is not definitionally the
--   identity function, so even this needs the bridge.
renTm-idR : {Γ : Cx} {ρ : Ren Γ Γ} → (∀ v → ρ v ≡ v) → (t : RTm Γ) →
            renTm ρ t ≡ t
renTm-idR h t = trans (renTm-cong h t) (trans (ren-sub t) (subTm-id t))

renTy-idR : {Γ : Cx} {ρ : Ren Γ Γ} → (∀ v → ρ v ≡ v) → (T : RTy Γ) →
            renTy ρ T ≡ T
renTy-idR h T = trans (renTy-cong h T) (trans (ren-subTy' T) (subTy-id T))

cong₇ : {A B C D E F G H : Set} (f : A → B → C → D → E → F → G → H)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {g g' : F} {i i' : G} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → g ≡ g' → i ≡ i' →
        f a b c d e g i ≡ f a' b' c' d' e' g' i'
cong₇ f refl refl refl refl refl refl refl = refl

cong₈ : {A B C D E F G H I : Set} (f : A → B → C → D → E → F → G → H → I)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {g g' : F}
        {i i' : G} {j j' : H} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → g ≡ g' → i ≡ i' → j ≡ j' →
        f a b c d e g i j ≡ f a' b' c' d' e' g' i' j'
cong₈ f refl refl refl refl refl refl refl refl = refl

-- ⚠ TWO NATURALITY LEMMAS FOR `aIHTat`, kept HERE while the irrelevance
--   work is in flight — they belong in `NbEPDirDBLibRec` beside `aIHT-ren`
--   and `aIHT-fit`, and should be lifted once it settles (the route
--   `sub-wTy` took, and `LibRec` has 13 dependents to recheck).
-- ★ `Π`/`Hom`/`El` all distribute DEFINITIONALLY, so each is one `cong₂`
--   over the two `w`s and nothing else.
aIHTat-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (A : RTy Γ) (cM m : RTm (Γ ∙)) (μ : RTm Γ) →
             subTy σ (aIHTat A cM m μ)
           ≡ aIHTat (subTy σ A) (subTm (extS σ) cM) (subTm (extS σ) m) (subTm σ μ)
aIHTat-sub {σ = σ} A cM m μ =
  cong₂ (λ u c → Π (subTy σ A) (Π (Hom Nat (nsuc (subTm (extS σ) m)) u) (El c)))
        (sub-w μ) (sub-w {σ = extS σ} cM)

aIHTat-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (A : RTy Γ) (cM m : RTm (Γ ∙)) (μ : RTm Γ) →
             renTy ρ (aIHTat A cM m μ)
           ≡ aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m) (renTm ρ μ)
aIHTat-ren {ρ = ρ} A cM m μ =
  cong₂ (λ u c → Π (renTy ρ A) (Π (Hom Nat (nsuc (renTm (extR ρ) m)) u) (El c)))
        (ren-w μ) (ren-w {ρ = extR ρ} cM)

------------------------------------------------------------------------
-- ★★★ THE POINTWISE HYPOTHESIS — "the two IHs agree at every argument".
--
-- ⚠⚠ RENAMING-INDEXED, and that is NOT decoration (2026-08-16).  It was a
--   plain `(y q : RTm ⌊ Θ ⌋) → …` until gcd's `StepExt` was attempted, and
--   that form is UNUSABLE by any provider whose step case-splits.  A split
--   is a `natrec`, `⊢natrec` types its successor branch in `(Γ ▹ Nat) ▹ M`,
--   and the recursive leaf's argument mentions the variables the split just
--   bound — so the instance needed is at a `y : RTm ⌊ Θ' ⌋` for a Θ' with
--   binders Θ does not have, and there is no `RTm ⌊ Θ' ⌋ → RTm ⌊ Θ ⌋`.
--   It is a type error, not a difficulty.  Four escapes were checked and
--   all are closed — see `HANDOFF-2026-08-16.md`; the one worth repeating
--   is that internalising the premise as a `Π` first is CIRCULAR, because
--   building that `Π` needs the premise at `Θ ▹ A ▹ Hom …`.
--
-- ★ The bridge `∀ v → ϑ (ρ v) ≡ ρ' v` rather than a composition `ϑ ∘ ρ`:
--   every type below is then written in ONE renaming, which is what
--   `auxAt-renʳ`/`irrT-ren` already do and what keeps the peels pointwise.
--
-- ★ The bound is `renTm ϑ (μ a)`, not `μ (renTm ϑ a)`.  The two are equal
--   (`sub1-ren`) and the first is what `ren-lemma` hands the SUPPLIER for
--   free, so the naturality is paid once, inside, instead of at every use.
------------------------------------------------------------------------

StepPW : (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙))
         (Θ : Ctx) (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (a ih₁ ih₂ : RTm ⌊ Θ ⌋) → Set
StepPW Δ A cM m Θ ρ a ih₁ ih₂ =
  {Θ' : Ctx} {ϑ : Ren ⌊ Θ ⌋ ⌊ Θ' ⌋} {ρ' : Ren ⌊ Δ ⌋ ⌊ Θ' ⌋} →
  Ren⊢ Θ Θ' ϑ → (∀ v → ϑ (ρ v) ≡ ρ' v) →
  (y q : RTm ⌊ Θ' ⌋) →
  Θ' ⊢ y ∷ renTy ρ' A →
  Θ' ⊢ q ∷ Hom Nat (nsuc (subTm (single y) (renTm (extR ρ') m)))
                   (renTm ϑ (subTm (single a) (renTm (extR ρ) m))) →
  Prv Θ' (Id (El (subTm (single y) (renTm (extR ρ') cM)))
             (app (app (renTm ϑ ih₁) y) q)
             (app (app (renTm ϑ ih₂) y) q))

-- ⚠⚠⚠ `StepExt-ren` — DRAFTED AND PARKED (2026-08-20).  NOT PROVED.
--
--     StepExt-ren : Ren⊢ Δ Θ ρ → StepExt Δ A cM m stp →
--                   StepExt Θ (renTy ρ A) (renTm (extR ρ) cM)
--                             (renTm (extR ρ) m) (renTm ρ stp)
--
-- ★ DERIVABLE, not a new assumption: `StepExt` is ALREADY quantified over
--   renamings, so this instantiates the original at the COMPOSITE `ϑ ∘ ρ`
--   and re-associates.  `Ren⊢-comp` composes the typed renamings.
--
-- ⚠ WHAT IS HARD IS `StepPW`, not the idea.  It is DOUBLY
--   renaming-indexed with its own coherence condition, so transporting it
--   means calling the given `pw` at `ρ' := ϑ³ ∘ ϑ` — where the condition
--   is `refl`, hence always available — and then re-expressing the RESULT
--   at `ρ³` via `br`.  Three rounds went on those casts; the last failure
--   was a malformed motive on `dq` (`Δ != Θ`), not a wrong plan.
--
-- ⇒ WHY IT MATTERS: it is the last piece before `AmTΠ` can be INSTANTIATED
--   at `Θ'`, which is what supplies irrelevance at `Θ'`-level arguments and
--   hence the renaming-indexed bridge `IndPW` needs.  The `-ren` family is
--   COMPLETE and green; only this transport is open.

-- `(x : A) (ih₁ ih₂ : IH x) → (∀ y q. ih₁ y q ≡ ih₂ y q) → stp x ih₁ ≡ stp x ih₂`
StepExt : (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋) → Set
StepExt Δ A cM m stp =
  {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
  (a ih₁ ih₂ : RTm ⌊ Θ ⌋) →
  Θ ⊢ a ∷ renTy ρ A →
  -- ⚠⚠ THESE TWO WERE DROPPED AND ARE BACK — measured 2026-08-15.  The
  --   argument for dropping them was that a provider reduces
  --   `app (app stp a) ihᵢ` with `ihᵢ` opaque and never inspects one.  True
  --   of the REDUCTION, false of the provider as a whole: to instantiate
  --   the pointwise hypothesis it must supply `q`'s typing, i.e. type the
  --   recursive call's CERTIFICATE, and (probe, same day) that certificate
  --   is literally the step branch's own certificate under the reduction's
  --   substitutions — so it is typed by `sub-lemma` on the branch's
  --   derivation, and `sub-lemma` needs a `Sub⊢` for a substitution that
  --   includes `single ihᵢ`.  Hence `ihᵢ` must be typed.
  Θ ⊢ ih₁ ∷ aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                   (subTm (single a) (renTm (extR ρ) m)) →
  Θ ⊢ ih₂ ∷ aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                   (subTm (single a) (renTm (extR ρ) m)) →
  StepPW Δ A cM m Θ ρ a ih₁ ih₂ →
  Prv Θ (Id (El (subTm (single a) (renTm (extR ρ) cM)))
            (app (app (renTm ρ stp) a) ih₁)
            (app (app (renTm ρ stp) a) ih₂))

------------------------------------------------------------------------
-- THE COMBINATOR, over an arbitrary ambient context.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ THE TERM-LEVEL CONSTRUCTIONS, PARAMETERISED — and their `-ren` laws.
--
-- ⚠ THE ASYMMETRY THIS FIXES.  The TYPE-level constructions are already
--   top-level and parameterised, with commutation laws: `aAuxB`/`aAuxB-ren`,
--   `aStepT`/`aStepT-ren`, `aIHT`/`aIHT-ren`.  The TERM-level ones —
--   `ihZ`, `ihS`, `aZBr`, `aSBr`, `aAuxTm`, `amrecTm` — are defined INSIDE
--   `AmT`/`AmTΠ` against the module's parameters, so nothing can say how
--   they behave under a renaming.
--
-- ★ WHY THAT MATTERS.  `amrec-ind`'s `IndPW` premise quantifies over an
--   ARBITRARY `y : RTm ⌊ Θ' ⌋`, but the irrelevance layer (`irrT`,
--   `irrElim`, `irr-ind`) takes `x y : RTm ⌊ Δ ⌋` — the CONTEXT is
--   renaming-indexed, the ARGUMENTS are not.  The way to reach `Θ'`-level
--   arguments is to INSTANTIATE the module at `Θ'` (which `AmTΠ` already
--   does internally, opening `AmT` at `Δ ▹ A`), and then these `-ren` laws
--   are what connect that instantiation back to `renTm ρ` of this one.
--
-- ⇒ this is the same technique the module already uses, applied one level
--   down.  It is NOT a generalisation of the irrelevance layer — that
--   would widen the largest piece of this file; this reuses it as-is.
------------------------------------------------------------------------

ihZ' : {Γ : Cx} (cM m : RTm (Γ ∙)) → RTm ((Γ ∙) ∙)
ihZ' cM m =
  lam (lam (absurd (w (wᶠ (wᶠ cM)))
                   (ordtr (nsuc (w (wᶠ (wᶠ m)))) (w (w (w m))) nzero
                          (var vz) (var (vs (vs vz))))))

-- the `w ∘ wᶠ ∘ wᶠ` spine, pushed through a renaming
wwᶠ²-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
           renTm (extR (extR (extR (extR ρ)))) (w (wᶠ (wᶠ t)))
         ≡ w (wᶠ (wᶠ (renTm (extR ρ) t)))
wwᶠ²-ren {ρ = ρ} t =
  trans (ren-w {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ t)))
        (cong w (trans (ren-wᶠ {ρ = extR ρ} (wᶠ t))
                       (cong wᶠ (ren-wᶠ {ρ = ρ} t))))

ihZ-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cM m : RTm (Γ ∙)) →
          renTm (extR (extR ρ)) (ihZ' cM m)
        ≡ ihZ' (renTm (extR ρ) cM) (renTm (extR ρ) m)
ihZ-ren {ρ = ρ} cM m =
  cong₃ (λ c u v → lam (lam (absurd c (ordtr (nsuc u) v nzero
                                             (var vz) (var (vs (vs vz)))))))
        (wwᶠ²-ren {ρ = ρ} cM) (wwᶠ²-ren {ρ = ρ} m) (ren-w³ {ρ = extR ρ} m)

-- ★ two more spine peels, same construction as `wwᶠ²-ren`
wwᶠ⁴-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
           renTm (extR (extR (extR (extR (extR (extR ρ))))))
                 (w (wᶠ (wᶠ (wᶠ (wᶠ t)))))
         ≡ w (wᶠ (wᶠ (wᶠ (wᶠ (renTm (extR ρ) t)))))
wwᶠ⁴-ren {ρ = ρ} t =
  trans (ren-w {ρ = extR (extR (extR (extR (extR ρ))))} (wᶠ (wᶠ (wᶠ (wᶠ t)))))
        (cong w (trans (ren-wᶠ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ (wᶠ t))))
                 (cong wᶠ (trans (ren-wᶠ {ρ = extR (extR ρ)} (wᶠ (wᶠ t)))
                           (cong wᶠ (trans (ren-wᶠ {ρ = extR ρ} (wᶠ t))
                                     (cong wᶠ (ren-wᶠ {ρ = ρ} t))))))))

w³wᶠ²-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
            renTm (extR (extR (extR (extR (extR (extR ρ))))))
                  (w (w (w (wᶠ (wᶠ t)))))
          ≡ w (w (w (wᶠ (wᶠ (renTm (extR ρ) t)))))
w³wᶠ²-ren {ρ = ρ} t =
  trans (ren-w³ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ t)))
        (cong (λ z → w (w (w z)))
              (trans (ren-wᶠ {ρ = extR ρ} (wᶠ t)) (cong wᶠ (ren-wᶠ {ρ = ρ} t))))

ren-w⁴ : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
         renTm (extR (extR (extR (extR ρ)))) (w (w (w (w t))))
       ≡ w (w (w (w (renTm ρ t))))
ren-w⁴ {ρ = ρ} t = trans (ren-w {ρ = extR (extR (extR ρ))} (w (w (w t))))
                         (cong w (ren-w³ t))

-- ★★ the SUCCESSOR side: `descS` depends only on the measure.
descS' : {Γ : Cx} (m : RTm (Γ ∙)) → RTm ((((((Γ ∙) ∙) ∙) ∙) ∙) ∙)
descS' m =
  ordtr (nsuc (w (wᶠ (wᶠ (wᶠ (wᶠ m)))))) (w (w (w (wᶠ (wᶠ m)))))
        (nsuc (var (vs (vs (vs (vs (vs vz))))))) (var vz) (var (vs (vs vz)))

descS-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (m : RTm (Γ ∙)) →
            renTm (extR (extR (extR (extR (extR (extR ρ)))))) (descS' m)
          ≡ descS' (renTm (extR ρ) m)
descS-ren {ρ = ρ} m =
  cong₂ (λ u v → ordtr (nsuc u) v (nsuc (var (vs (vs (vs (vs (vs vz)))))))
                       (var vz) (var (vs (vs vz))))
        (wwᶠ⁴-ren {ρ = ρ} m) (w³wᶠ²-ren {ρ = ρ} m)

ihS' : {Γ : Cx} (m : RTm (Γ ∙)) → RTm ((((Γ ∙) ∙) ∙) ∙)
ihS' m = lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) (descS' m)))

ihS-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (m : RTm (Γ ∙)) →
          renTm (extR (extR (extR (extR ρ)))) (ihS' m)
        ≡ ihS' (renTm (extR ρ) m)
ihS-ren {ρ = ρ} m =
  cong (λ d → lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) d)))
       (descS-ren {ρ = ρ} m)

-- ★★★ …and the two AUXILIARY BRANCHES.
aZBr' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙)) → RTm Γ
aZBr' stp cM m = lam (lam (app (app (w (w stp)) (var (vs vz))) (ihZ' cM m)))

aZBr-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (stp : RTm Γ) (cM m : RTm (Γ ∙)) →
           renTm ρ (aZBr' stp cM m)
         ≡ aZBr' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
aZBr-ren {ρ = ρ} stp cM m =
  cong₂ (λ s i → lam (lam (app (app s (var (vs vz))) i)))
        (ren-w² {ρ = ρ} stp) (ihZ-ren {ρ = ρ} cM m)

aSBr' : {Γ : Cx} (stp : RTm Γ) (m : RTm (Γ ∙)) → RTm ((Γ ∙) ∙)
aSBr' stp m =
  lam (lam (app (app (w (w (w (w stp)))) (var (vs vz))) (ihS' m)))

aSBr-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (stp : RTm Γ) (m : RTm (Γ ∙)) →
           renTm (extR (extR ρ)) (aSBr' stp m)
         ≡ aSBr' (renTm ρ stp) (renTm (extR ρ) m)
aSBr-ren {ρ = ρ} stp m =
  cong₂ (λ s i → lam (lam (app (app s (var (vs vz))) i)))
        (ren-w⁴ {ρ = ρ} stp) (ihS-ren {ρ = ρ} m)

-- ★★★★ THE AUXILIARY AND THE RECURSOR — the top of the chain.
--
-- ⚠ `amrecTm` is built from the auxiliary AT THE EXTENDED CONTEXT: `AmTΠ`
--   opens `AmT` at `Δ ▹ A` with `(w stp) (wᶠ cM) (wᶠ m)`, so the
--   parameterised form carries those weakenings explicitly.
aAuxTm' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) → RTm Γ
aAuxTm' stp cM m n = natrec (aZBr' stp cM m) (aSBr' stp m) n

aAuxTm-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ}
             (stp : RTm Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) →
             renTm ρ (aAuxTm' stp cM m n)
           ≡ aAuxTm' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                     (renTm ρ n)
aAuxTm-ren {ρ = ρ} stp cM m n =
  cong₂ (λ z sb → natrec z sb (renTm ρ n))
        (aZBr-ren {ρ = ρ} stp cM m) (aSBr-ren {ρ = ρ} stp m)

amrecTm' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙)) → RTm Γ
amrecTm' stp cM m =
  lam (app (app (aAuxTm' (w stp) (wᶠ cM) (wᶠ m) m) (var vz)) (reflTm m))

-- ⭐ `reflTm` needs no law: `reflTm t = natrec unit (var vz) t`, and both
--   `unit` and `var vz` are renaming-invariant, so it commutes
--   DEFINITIONALLY.
amrecTm-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (stp : RTm Γ) (cM m : RTm (Γ ∙)) →
              renTm ρ (amrecTm' stp cM m)
            ≡ amrecTm' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
amrecTm-ren {ρ = ρ} stp cM m =
  cong (λ a → lam (app (app a (var vz)) (reflTm (renTm (extR ρ) m))))
       (trans (aAuxTm-ren {ρ = extR ρ} (w stp) (wᶠ cM) (wᶠ m) m)
              (cong₃ (λ s c μ → aAuxTm' s c μ (renTm (extR ρ) m))
                     (ren-w {ρ = ρ} stp)
                     (ren-wᶠ {ρ = ρ} cM)
                     (ren-wᶠ {ρ = ρ} m)))

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
  ihZ = ihZ' cM m

  aZBr : RTm ⌊ Δ ⌋
  aZBr = aZBr' stp cM m

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
  descS = descS' m

  ihS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙)
  ihS = ihS' m

  aSBr : RTm (⌊ Δ ⌋ ∙ ∙)
  aSBr = aSBr' stp m

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
  aAuxTm n = aAuxTm' stp cM m n

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
  amrecTm = amrecTm' stp cM m

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

  -- ★★ THE SIX PEELS, hoisted: each is used by the branch's TYPE, by its
  --    renaming, and again by the branch IH's typing below.  Three carry a
  --    substitution `single x` past two family weakenings, three a renaming.
  peelA-x : (x : RTm ⌊ Δ ⌋) →
            subTy (extS (extS (single x))) (renTy vs (renTy vs (renTy vs A)))
          ≡ renTy vs (renTy vs A)
  peelA-x x =
    trans (sub-wTy {σ = extS (single x)} (renTy vs (renTy vs A)))
          (cong (renTy vs)
                (trans (sub-wTy {σ = single x} (renTy vs A))
                       (cong (renTy vs) (wk-singleTy A))))

  peelC-x : (x : RTm ⌊ Δ ⌋) →
            subTm (extS (extS (extS (single x)))) (wᶠ (wᶠ (wᶠ cM))) ≡ wᶠ (wᶠ cM)
  peelC-x x =
    trans (wᶠ-sub {σ = extS (single x)} (wᶠ (wᶠ cM)))
          (cong wᶠ (trans (wᶠ-sub {σ = single x} (wᶠ cM))
                          (cong wᶠ (wᶠ-single cM))))

  peelM-x : (x : RTm ⌊ Δ ⌋) →
            subTm (extS (extS (extS (single x)))) (wᶠ (wᶠ (wᶠ m))) ≡ wᶠ (wᶠ m)
  peelM-x x =
    trans (wᶠ-sub {σ = extS (single x)} (wᶠ (wᶠ m)))
          (cong wᶠ (trans (wᶠ-sub {σ = single x} (wᶠ m))
                          (cong wᶠ (wᶠ-single m))))

  peelA-ρ : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') →
            renTy (extR (extR ρ)) (renTy vs (renTy vs A))
          ≡ renTy vs (renTy vs (renTy ρ A))
  peelA-ρ ρ = trans (ren-wTy {ρ = extR ρ} (renTy vs A))
                    (cong (renTy vs) (ren-wTy {ρ = ρ} A))

  peelC-ρ : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') →
            renTm (extR (extR (extR ρ))) (wᶠ (wᶠ cM))
          ≡ wᶠ (wᶠ (renTm (extR ρ) cM))
  peelC-ρ ρ = trans (ren-wᶠ {ρ = extR ρ} (wᶠ cM)) (cong wᶠ (ren-wᶠ {ρ = ρ} cM))

  peelM-ρ : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') →
            renTm (extR (extR (extR ρ))) (wᶠ (wᶠ m))
          ≡ wᶠ (wᶠ (renTm (extR ρ) m))
  peelM-ρ ρ = trans (ren-wᶠ {ρ = extR ρ} (wᶠ m)) (cong wᶠ (ren-wᶠ {ρ = ρ} m))

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
                            (trans (cong₄ aAuxB (peelA-x x) (peelC-x x) (peelM-x x) refl)
                                   (sym mot₀-s))))
              (sub-lemma ⊢aSBr (Sub⊢-ext (Sub⊢-ext (⊢single dx)))))

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
                                       (trans (cong₄ aAuxB (peelA-ρ ρ) (peelC-ρ ρ) (peelM-ρ ρ) refl)
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

  -- ★ …AND THE SAME AT A RENAMING, which is the form an INTERNAL statement
  --   about the auxiliary needs: the two endpoints of `irrB`'s `Id` live
  --   under four binders, so nothing at the `Δ` level can type them.  A
  --   direct transcription of `⊢aux-app` with `renTy ρ A` /
  --   `renTm (extR ρ) cM` / `renTm (extR ρ) m` for the bare parameters and
  --   `⊢auxAt` for `⊢auxIH` — no new content.
  ⊢aux-appAt : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
               {x : RTm ⌊ Δ ⌋} {a n p : RTm ⌊ Θ ⌋} →
               Δ ⊢ x ∷ A → Θ ⊢ n ∷ Nat → Θ ⊢ a ∷ renTy ρ A →
               Θ ⊢ p ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) n →
               Θ ⊢ app (app (auxAt ρ x n) a) p
                 ∷ El (subTm (single a) (renTm (extR ρ) cM))
  ⊢aux-appAt {ρ = ρ} h {a = a} {n = n} {p = p} dx dn da dp =
    ⊢-cast (cong El (wk-single {v = p} (subTm (single a) (renTm (extR ρ) cM))))
      (⊢app (⊢-cast (cong₂ (λ b c →
                              Π (Hom Nat (subTm (single a) (renTm (extR ρ) m)) b)
                                (El c))
                           (wk-single {v = a} n)
                           (sub-w {σ = single a} (renTm (extR ρ) cM)))
                    (⊢app (⊢auxAt h dx dn) da))
            dp)

  ------------------------------------------------------------------------
  -- ★★★ THE ZERO BRANCH'S IH, TYPED — after the carrier, the argument and
  --    the certificate have all been substituted in.
  --
  -- ⚠ WHY THIS IS NEEDED, and it was NOT obvious.  The pointwise half of
  --   irrelevance at bound `0` is EX FALSO, so it looked free.  It is not:
  --   `⊢absurd` wants a CODE, the code is `⌜Id⌝ c (ih₁ y q) (ih₂ y q)`, and
  --   `⊢⌜Id⌝` types that only when BOTH ENDPOINTS are typed — so the
  --   ex-falso proof needs the branch IH's OWN type.  `⊢ihZ` has it only
  --   BEFORE the three substitutions, and `subTm` does not inverse.
  --
  -- ★ Four steps, and the type is in `aIHTat` normal form at every one:
  --   substitute the carrier `x`, rename the ambient, substitute the
  --   argument `a`, substitute the certificate `p`.  ⚠ The bound needs
  --   NAMING first: `⊢ihZ` states it as `subTm (single (var (vs vz)))
  --   (wᶠ³ m)`, which `wᶠ²-single` reads as `w (wᶠ m)` — the measure at the
  --   branch's own argument slot.  Left as it stands, no peel matches.
  ------------------------------------------------------------------------

  ihZ-atR : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (a p : RTm Γ') → RTm Γ'
  ihZ-atR ρ x a p =
    subTm (single p)
      (subTm (extS (single a))
        (renTm (extR (extR ρ)) (subTm (extS (extS (single x))) ihZ)))

  ⊢ihZ-atR : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
             {x : RTm ⌊ Δ ⌋} {a p : RTm ⌊ Θ ⌋} →
             Δ ⊢ x ∷ A → Θ ⊢ a ∷ renTy ρ A →
             Θ ⊢ p ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) nzero →
             Θ ⊢ ihZ-atR ρ x a p
               ∷ aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                        (subTm (single a) (renTm (extR ρ) m))
  ⊢ihZ-atR {Θ = Θ} {ρ = ρ} h {x = x} {a = a} {p = p} dx da dp =
    ⊢-cast (trans (aIHTat-sub {σ = single p} (renTy vs (renTy ρ A))
                              (wᶠ (renTm (extR ρ) cM)) (wᶠ (renTm (extR ρ) m))
                              (w (subTm (single a) (renTm (extR ρ) m))))
                  (cong₄ aIHTat (wk-singleTy (renTy ρ A))
                                (wᶠ-single (renTm (extR ρ) cM))
                                (wᶠ-single (renTm (extR ρ) m))
                                (wk-single {v = p}
                                           (subTm (single a) (renTm (extR ρ) m)))))
           (⊢[] d3 dp)
    where
      -- the bound, NAMED (see the header's ⚠)
      d0 : (((Δ ▹ A) ▹ renTy vs A) ▹ Hom Nat (wᶠ m) nzero) ⊢ ihZ
             ∷ aIHTat (renTy vs (renTy vs (renTy vs A)))
                      (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m))) (w (wᶠ m))
      d0 = ⊢-cast (cong (aIHTat (renTy vs (renTy vs (renTy vs A)))
                                (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m))))
                        (wᶠ²-single (wᶠ m)))
                  ⊢ihZ

      d1 : ((Δ ▹ A) ▹ Hom Nat m nzero)
             ⊢ subTm (extS (extS (single x))) ihZ
             ∷ aIHTat (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m)) (w m)
      d1 = subst (λ T → ((Δ ▹ A) ▹ T) ⊢ subTm (extS (extS (single x))) ihZ
                          ∷ aIHTat (renTy vs (renTy vs A)) (wᶠ (wᶠ cM))
                                   (wᶠ (wᶠ m)) (w m))
                 (cong (λ z → Hom Nat z nzero) (wᶠ-single m))
             (subst (λ T → ((Δ ▹ T)
                             ▹ subTy (extS (single x)) (Hom Nat (wᶠ m) nzero))
                             ⊢ subTm (extS (extS (single x))) ihZ
                             ∷ aIHTat (renTy vs (renTy vs A)) (wᶠ (wᶠ cM))
                                      (wᶠ (wᶠ m)) (w m))
                    (wk-singleTy A)
                    (⊢-cast (trans (aIHTat-sub {σ = extS (extS (single x))}
                                               (renTy vs (renTy vs (renTy vs A)))
                                               (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m)))
                                               (w (wᶠ m)))
                                   (cong₄ aIHTat (peelA-x x) (peelC-x x) (peelM-x x)
                                          (trans (sub-w {σ = extS (single x)} (wᶠ m))
                                                 (cong w (wᶠ-single m)))))
                            (sub-lemma d0 (Sub⊢-ext (Sub⊢-ext (⊢single dx))))))

      d2 : ((Θ ▹ renTy ρ A) ▹ Hom Nat (renTm (extR ρ) m) nzero)
             ⊢ renTm (extR (extR ρ)) (subTm (extS (extS (single x))) ihZ)
             ∷ aIHTat (renTy vs (renTy vs (renTy ρ A)))
                      (wᶠ (wᶠ (renTm (extR ρ) cM))) (wᶠ (wᶠ (renTm (extR ρ) m)))
                      (w (renTm (extR ρ) m))
      d2 = ⊢-cast (trans (aIHTat-ren {ρ = extR (extR ρ)}
                                     (renTy vs (renTy vs A)) (wᶠ (wᶠ cM))
                                     (wᶠ (wᶠ m)) (w m))
                         (cong₄ aIHTat (peelA-ρ ρ) (peelC-ρ ρ) (peelM-ρ ρ)
                                (ren-w {ρ = extR ρ} m)))
                  (ren-lemma d1 (Ren⊢-ext (Ren⊢-ext h)))

      d3 : (Θ ▹ Hom Nat (subTm (single a) (renTm (extR ρ) m)) nzero)
             ⊢ subTm (extS (single a))
                     (renTm (extR (extR ρ)) (subTm (extS (extS (single x))) ihZ))
             ∷ aIHTat (renTy vs (renTy ρ A)) (wᶠ (renTm (extR ρ) cM))
                      (wᶠ (renTm (extR ρ) m))
                      (w (subTm (single a) (renTm (extR ρ) m)))
      d3 = ⊢-cast (trans (aIHTat-sub {σ = extS (single a)}
                                     (renTy vs (renTy vs (renTy ρ A)))
                                     (wᶠ (wᶠ (renTm (extR ρ) cM)))
                                     (wᶠ (wᶠ (renTm (extR ρ) m)))
                                     (w (renTm (extR ρ) m)))
                         (cong₄ aIHTat
                                (trans (sub-wTy {σ = single a}
                                                (renTy vs (renTy ρ A)))
                                       (cong (renTy vs) (wk-singleTy (renTy ρ A))))
                                (trans (wᶠ-sub {σ = single a}
                                               (wᶠ (renTm (extR ρ) cM)))
                                       (cong wᶠ (wᶠ-single (renTm (extR ρ) cM))))
                                (trans (wᶠ-sub {σ = single a}
                                               (wᶠ (renTm (extR ρ) m)))
                                       (cong wᶠ (wᶠ-single (renTm (extR ρ) m))))
                                (sub-w {σ = single a} (renTm (extR ρ) m))))
                  (sub-lemma d2 (Sub⊢-ext (⊢single da)))

  ------------------------------------------------------------------------
  -- ★★★★ IRRELEVANCE AT BOUND `0` — THE FIRST ONE, and the induction's
  --     zero branch.
  --
  --   Two certificates, one answer: `aux 0 a c₁ ≡ aux 0 a c₂`.  The
  --   auxiliary DOES look at its certificate (the zero branch feeds it to
  --   `ordtr`), so this is not syntactic — it is `StepExt` plus the fact
  --   that the IH the branch hands over is EX FALSO, which is what makes
  --   the pointwise premise free: `μ y < μ a ≤ 0` is `base`, and
  --   `Id (El C) t u` is `El (⌜Id⌝ C t u)`, so `absurd` reaches it.
  --
  -- ⚠ `⊢⌜Id⌝` is why `⊢ihZ-atR` had to exist: the code needs BOTH endpoints
  --   typed, and the endpoints are the two IHs applied.
  ------------------------------------------------------------------------

  -- the zero branch's three weakenings on `stp`, across the renaming
  stp-cancel-zR : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (a p : RTm Γ') →
    subTm (single p)
      (subTm (extS (single a))
        (renTm (extR (extR ρ))
          (subTm (extS (extS (single x))) (w (w (w stp))))))
    ≡ renTm ρ stp
  stp-cancel-zR ρ x a p =
    trans (cong (λ z → subTm (single p)
                         (subTm (extS (single a)) (renTm (extR (extR ρ)) z)))
                (trans (sub-w² {σ = single x} (w stp))
                       (cong (λ z → w (w z)) (wk-single {v = x} stp))))
    (trans (cong (λ z → subTm (single p) (subTm (extS (single a)) z))
                 (trans (ren-w {ρ = extR ρ} (w stp))
                        (cong w (ren-w {ρ = ρ} stp))))
    (trans (cong (subTm (single p))
                 (trans (sub-w {σ = single a} (w (renTm ρ stp)))
                        (cong w (wk-single {v = a} (renTm ρ stp)))))
           (wk-single {v = p} (renTm ρ stp))))

  -- ★ the CPS zero-unfold, at a renaming — `aux-step-sF`'s twin
  auxAt-step-z : {Γ' : Cx} {P : RTm Γ' → RTm Γ'}
                 (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (a n p : RTm Γ') →
                 n ⟶* nzero →
                 ((ih : RTm Γ') → app (app (renTm ρ stp) a) ih ⟶* P ih) →
                 app (app (auxAt ρ x n) a) p ⟶* P (ihZ-atR ρ x a p)
  auxAt-step-z {P = P} ρ x a n p r hh =
    ⟶*-trans
      (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-trans (⟶*-natrecⁿ r)
                                            (step (natrec-zero _ _) done))))
                (step (ξ-appˡ (β _ a)) (step (β _ p) done)))
      (subst (λ z → z ⟶* P (ihZ-atR ρ x a p))
             (sym (cong₂ (λ sf yv → app (app sf yv) (ihZ-atR ρ x a p))
                         (stp-cancel-zR ρ x a p) (wk-single {v = p} a)))
             (hh (ihZ-atR ρ x a p)))

  -- ★ …and the SUCCESSOR twin.  `aSBr` carries FIVE weakenings on the step
  --   against `aZBr`'s three, so the cancellation is a five-rung chain, and
  --   the renaming rides through each rung by `ren-w`.
  ihS-atR : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (a k p : RTm Γ') →
            RTm Γ'
  ihS-atR ρ x a k p =
    subTm (single p)
      (subTm (extS (single a))
        (subTm (extS (extS (single (auxAt ρ x k))))
          (subTm (extS (extS (extS (single k))))
            (renTm (extR (extR (extR (extR ρ))))
              (subTm (extS (extS (extS (extS (single x))))) ihS)))))

  stp-cancel-sR : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (a k r : RTm Γ') →
    subTm (single r)
      (subTm (extS (single a))
        (subTm (extS (extS (single (auxAt ρ x k))))
          (subTm (extS (extS (extS (single k))))
            (renTm (extR (extR (extR (extR ρ))))
              (subTm (extS (extS (extS (extS (single x)))))
                     (w (w (w (w (w stp))))))))))
    ≡ renTm ρ stp
  stp-cancel-sR ρ x a k r =
    trans (cong (λ z → subTm (single r)
                         (subTm (extS (single a))
                           (subTm (extS (extS (single (auxAt ρ x k))))
                             (subTm (extS (extS (extS (single k))))
                               (renTm (extR (extR (extR (extR ρ)))) z)))))
                (trans (sub-w⁴ {σ = single x} (w stp))
                       (cong (λ z → w (w (w (w z)))) (wk-single {v = x} stp))))
    (trans (cong (λ z → subTm (single r)
                          (subTm (extS (single a))
                            (subTm (extS (extS (single (auxAt ρ x k))))
                              (subTm (extS (extS (extS (single k)))) z))))
                 (trans (ren-w {ρ = extR (extR (extR ρ))} (w (w (w stp))))
                        (cong w (trans (ren-w {ρ = extR (extR ρ)} (w (w stp)))
                                       (cong w (trans (ren-w {ρ = extR ρ} (w stp))
                                                      (cong w (ren-w {ρ = ρ} stp))))))))
    (trans (cong (λ z → subTm (single r)
                          (subTm (extS (single a))
                            (subTm (extS (extS (single (auxAt ρ x k)))) z)))
                 (trans (sub-w³ {σ = single k} (w (renTm ρ stp)))
                        (cong (λ z → w (w (w z))) (wk-single {v = k} (renTm ρ stp)))))
    (trans (cong (λ z → subTm (single r) (subTm (extS (single a)) z))
                 (trans (sub-w² {σ = single (auxAt ρ x k)} (w (renTm ρ stp)))
                        (cong (λ z → w (w z))
                              (wk-single {v = auxAt ρ x k} (renTm ρ stp)))))
    (trans (cong (subTm (single r))
                 (trans (sub-w {σ = single a} (w (renTm ρ stp)))
                        (cong w (wk-single {v = a} (renTm ρ stp)))))
           (wk-single {v = r} (renTm ρ stp))))))

  auxAt-step-sF : {Γ' : Cx} {P : RTm Γ' → RTm Γ'}
                  (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (a n k p : RTm Γ') →
                  n ⟶* nsuc k →
                  ((ih : RTm Γ') → app (app (renTm ρ stp) a) ih ⟶* P ih) →
                  app (app (auxAt ρ x n) a) p ⟶* P (ihS-atR ρ x a k p)
  auxAt-step-sF {P = P} ρ x a n k p r hh =
    ⟶*-trans
      (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-trans (⟶*-natrecⁿ r)
                                            (step (natrec-suc _ _ k) done))))
                (step (ξ-appˡ (β _ a)) (step (β _ p) done)))
      (subst (λ z → z ⟶* P (ihS-atR ρ x a k p))
             (sym (cong₂ (λ sf yv → app (app sf yv) (ihS-atR ρ x a k p))
                         (stp-cancel-sR ρ x a k p) (wk-single {v = p} a)))
             (hh (ihS-atR ρ x a k p)))

  ------------------------------------------------------------------------
  -- ★★★ THE SUCCESSOR BRANCH'S IH, TYPED.  `⊢ihZ-atR` one level up: SIX
  --    steps rather than four, because `ihS` sits under five binders
  --    (`x`, `k`, `ih₀`, `a`, `p`) and the renaming goes in after `x`.
  --
  -- ★ Step 4 is why `⊢auxAt` had to exist: the `ih₀` slot is substituted by
  --   `auxAt ρ x k`, the auxiliary at the DECREMENTED bound, and `Sub⊢`
  --   wants it typed at `aAuxB (renTy ρ A) … k` — which is exactly
  --   `⊢auxAt`'s conclusion.
  ------------------------------------------------------------------------

  ⊢ihS-atR : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
             {x : RTm ⌊ Δ ⌋} {a k p : RTm ⌊ Θ ⌋} →
             Δ ⊢ x ∷ A → Θ ⊢ k ∷ Nat → Θ ⊢ a ∷ renTy ρ A →
             Θ ⊢ p ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) (nsuc k) →
             Θ ⊢ ihS-atR ρ x a k p
               ∷ aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                        (subTm (single a) (renTm (extR ρ) m))
  ⊢ihS-atR {Θ = Θ} {ρ = ρ} h {x = x} {a = a} {k = k} {p = p} dx dk da dp =
    ⊢-cast (trans (aIHTat-sub {σ = single p} (renTy vs Aρ) (wᶠ cMρ) (wᶠ mρ) (w μa))
                  (cong₄ aIHTat (wk-singleTy Aρ) (wᶠ-single cMρ) (wᶠ-single mρ)
                                (wk-single {v = p} μa)))
           (⊢[] d5 dp)
    where
      Aρ  = renTy ρ A
      cMρ = renTm (extR ρ) cM
      mρ  = renTm (extR ρ) m
      μa  = subTm (single a) mρ
      AX  = auxAt ρ x k

      d0 : (((((Δ ▹ A) ▹ Nat) ▹ aAuxMot) ▹ renTy vs (renTy vs (renTy vs A)))
             ▹ Hom Nat (wᶠ (wᶠ (wᶠ m))) (nsuc (var (vs (vs vz)))))
             ⊢ ihS
             ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs A)))))
                      (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM))))) (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m)))))
                      (w (wᶠ (wᶠ (wᶠ m))))
      d0 = ⊢-cast (cong (aIHTat (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs A)))))
                                (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM)))))
                                (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m))))))
                        (wᶠ²-single (wᶠ (wᶠ (wᶠ m)))))
                  ⊢ihS

      d1 : ((((Δ ▹ Nat) ▹ mot₀) ▹ renTy vs (renTy vs A))
             ▹ Hom Nat (wᶠ (wᶠ m)) (nsuc (var (vs (vs vz)))))
             ⊢ subTm (extS (extS (extS (extS (single x))))) ihS
             ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs A))))
                      (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
                      (w (wᶠ (wᶠ m)))
      d1 =
        subst (λ T → ((((Δ ▹ Nat) ▹ mot₀) ▹ renTy vs (renTy vs A)) ▹ T)
                       ⊢ subTm (extS (extS (extS (extS (single x))))) ihS
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs A))))
                                (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
                                (w (wᶠ (wᶠ m))))
              (cong (λ z → Hom Nat z (nsuc (var (vs (vs vz))))) (peelM-x x))
        (subst (λ T → ((((Δ ▹ Nat) ▹ mot₀) ▹ T)
                        ▹ subTy (extS (extS (extS (single x))))
                                (Hom Nat (wᶠ (wᶠ (wᶠ m))) (nsuc (var (vs (vs vz))))))
                       ⊢ subTm (extS (extS (extS (extS (single x))))) ihS
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs A))))
                                (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
                                (w (wᶠ (wᶠ m))))
               (peelA-x x)
        (subst (λ T → ((((Δ ▹ Nat) ▹ T)
                         ▹ subTy (extS (extS (single x)))
                                 (renTy vs (renTy vs (renTy vs A))))
                        ▹ subTy (extS (extS (extS (single x))))
                                (Hom Nat (wᶠ (wᶠ (wᶠ m))) (nsuc (var (vs (vs vz))))))
                       ⊢ subTm (extS (extS (extS (extS (single x))))) ihS
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs A))))
                                (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
                                (w (wᶠ (wᶠ m))))
               (mot-x x)
               (⊢-cast ty1 (sub-lemma d0 (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext
                                            (Sub⊢-ext (⊢single dx)))))))))
        where
          ty1 : subTy (extS (extS (extS (extS (single x)))))
                      (aIHTat (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs A)))))
                              (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM))))) (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m)))))
                              (w (wᶠ (wᶠ (wᶠ m)))))
              ≡ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs A))))
                       (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m)))) (w (wᶠ (wᶠ m)))
          ty1 =
            trans (aIHTat-sub {σ = extS (extS (extS (extS (single x))))}
                              (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs A)))))
                              (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ cM))))) (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m)))))
                              (w (wᶠ (wᶠ (wᶠ m)))))
                  (cong₄ aIHTat
                    (trans (sub-wTy {σ = extS (extS (extS (single x)))}
                                    (renTy vs (renTy vs (renTy vs (renTy vs A)))))
                           (cong (renTy vs)
                                 (trans (sub-wTy {σ = extS (extS (single x))}
                                                 (renTy vs (renTy vs (renTy vs A))))
                                        (cong (renTy vs) (peelA-x x)))))
                    (trans (wᶠ-sub {σ = extS (extS (extS (single x)))}
                                   (wᶠ (wᶠ (wᶠ (wᶠ cM)))))
                           (cong wᶠ (trans (wᶠ-sub {σ = extS (extS (single x))}
                                                   (wᶠ (wᶠ (wᶠ cM))))
                                           (cong wᶠ (peelC-x x)))))
                    (trans (wᶠ-sub {σ = extS (extS (extS (single x)))}
                                   (wᶠ (wᶠ (wᶠ (wᶠ m)))))
                           (cong wᶠ (trans (wᶠ-sub {σ = extS (extS (single x))}
                                                   (wᶠ (wᶠ (wᶠ m))))
                                           (cong wᶠ (peelM-x x)))))
                    (trans (sub-w {σ = extS (extS (extS (single x)))} (wᶠ (wᶠ (wᶠ m))))
                           (cong w (peelM-x x))))

      d2 : ((((Θ ▹ Nat) ▹ motAt ρ) ▹ renTy vs (renTy vs Aρ))
             ▹ Hom Nat (wᶠ (wᶠ mρ)) (nsuc (var (vs (vs vz)))))
             ⊢ renTm (extR (extR (extR (extR ρ))))
                     (subTm (extS (extS (extS (extS (single x))))) ihS)
             ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs Aρ))))
                      (wᶠ (wᶠ (wᶠ (wᶠ cMρ)))) (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
                      (w (wᶠ (wᶠ mρ)))
      d2 =
        subst (λ T → ((((Θ ▹ Nat) ▹ motAt ρ) ▹ renTy vs (renTy vs Aρ)) ▹ T)
                       ⊢ renTm (extR (extR (extR (extR ρ))))
                               (subTm (extS (extS (extS (extS (single x))))) ihS)
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs Aρ))))
                                (wᶠ (wᶠ (wᶠ (wᶠ cMρ)))) (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
                                (w (wᶠ (wᶠ mρ))))
              (cong (λ z → Hom Nat z (nsuc (var (vs (vs vz))))) (peelM-ρ ρ))
        (subst (λ T → ((((Θ ▹ Nat) ▹ motAt ρ) ▹ T)
                        ▹ renTy (extR (extR (extR ρ)))
                                (Hom Nat (wᶠ (wᶠ m)) (nsuc (var (vs (vs vz))))))
                       ⊢ renTm (extR (extR (extR (extR ρ))))
                               (subTm (extS (extS (extS (extS (single x))))) ihS)
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs Aρ))))
                                (wᶠ (wᶠ (wᶠ (wᶠ cMρ)))) (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
                                (w (wᶠ (wᶠ mρ))))
               (peelA-ρ ρ)
        (subst (λ T → ((((Θ ▹ Nat) ▹ T)
                         ▹ renTy (extR (extR ρ)) (renTy vs (renTy vs A)))
                        ▹ renTy (extR (extR (extR ρ)))
                                (Hom Nat (wᶠ (wᶠ m)) (nsuc (var (vs (vs vz))))))
                       ⊢ renTm (extR (extR (extR (extR ρ))))
                               (subTm (extS (extS (extS (extS (single x))))) ihS)
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs Aρ))))
                                (wᶠ (wᶠ (wᶠ (wᶠ cMρ)))) (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
                                (w (wᶠ (wᶠ mρ))))
               (motAt-ren ρ)
               (⊢-cast ty2 (ren-lemma d1 (Ren⊢-ext (Ren⊢-ext (Ren⊢-ext
                                            (Ren⊢-ext h))))))))
        where
          ty2 : renTy (extR (extR (extR (extR ρ))))
                      (aIHTat (renTy vs (renTy vs (renTy vs (renTy vs A))))
                              (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
                              (w (wᶠ (wᶠ m))))
              ≡ aIHTat (renTy vs (renTy vs (renTy vs (renTy vs Aρ))))
                       (wᶠ (wᶠ (wᶠ (wᶠ cMρ)))) (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
                       (w (wᶠ (wᶠ mρ)))
          ty2 =
            trans (aIHTat-ren {ρ = extR (extR (extR (extR ρ)))}
                              (renTy vs (renTy vs (renTy vs (renTy vs A))))
                              (wᶠ (wᶠ (wᶠ (wᶠ cM)))) (wᶠ (wᶠ (wᶠ (wᶠ m))))
                              (w (wᶠ (wᶠ m))))
                  (cong₄ aIHTat
                    (trans (ren-wTy {ρ = extR (extR (extR ρ))}
                                    (renTy vs (renTy vs (renTy vs A))))
                           (cong (renTy vs)
                                 (trans (ren-wTy {ρ = extR (extR ρ)}
                                                 (renTy vs (renTy vs A)))
                                        (cong (renTy vs) (peelA-ρ ρ)))))
                    (trans (ren-wᶠ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ (wᶠ cM))))
                           (cong wᶠ (trans (ren-wᶠ {ρ = extR (extR ρ)} (wᶠ (wᶠ cM)))
                                           (cong wᶠ (peelC-ρ ρ)))))
                    (trans (ren-wᶠ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ (wᶠ m))))
                           (cong wᶠ (trans (ren-wᶠ {ρ = extR (extR ρ)} (wᶠ (wᶠ m)))
                                           (cong wᶠ (peelM-ρ ρ)))))
                    (trans (ren-w {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ m)))
                           (cong w (peelM-ρ ρ))))

      d3 : (((Θ ▹ aAuxB Aρ cMρ mρ k) ▹ renTy vs Aρ)
             ▹ Hom Nat (wᶠ mρ) (nsuc (w (w k))))
             ⊢ subTm (extS (extS (extS (single k))))
                     (renTm (extR (extR (extR (extR ρ))))
                            (subTm (extS (extS (extS (extS (single x))))) ihS))
             ∷ aIHTat (renTy vs (renTy vs (renTy vs Aρ)))
                      (wᶠ (wᶠ (wᶠ cMρ))) (wᶠ (wᶠ (wᶠ mρ))) (w (wᶠ mρ))
      d3 =
        subst (λ T → (((Θ ▹ aAuxB Aρ cMρ mρ k) ▹ renTy vs Aρ) ▹ T)
                       ⊢ subTm (extS (extS (extS (single k))))
                               (renTm (extR (extR (extR (extR ρ))))
                                      (subTm (extS (extS (extS (extS (single x))))) ihS))
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs Aρ)))
                                (wᶠ (wᶠ (wᶠ cMρ))) (wᶠ (wᶠ (wᶠ mρ))) (w (wᶠ mρ)))
              (cong (λ z → Hom Nat z (nsuc (w (w k))))
                    (trans (wᶠ-sub {σ = single k} (wᶠ mρ))
                           (cong wᶠ (wᶠ-single mρ))))
        (subst (λ T → (((Θ ▹ aAuxB Aρ cMρ mρ k) ▹ T)
                        ▹ subTy (extS (extS (single k)))
                                (Hom Nat (wᶠ (wᶠ mρ)) (nsuc (var (vs (vs vz))))))
                       ⊢ subTm (extS (extS (extS (single k))))
                               (renTm (extR (extR (extR (extR ρ))))
                                      (subTm (extS (extS (extS (extS (single x))))) ihS))
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs Aρ)))
                                (wᶠ (wᶠ (wᶠ cMρ))) (wᶠ (wᶠ (wᶠ mρ))) (w (wᶠ mρ)))
               (trans (sub-wTy {σ = single k} (renTy vs Aρ))
                      (cong (renTy vs) (wk-singleTy Aρ)))
        (subst (λ T → (((Θ ▹ T) ▹ subTy (extS (single k)) (renTy vs (renTy vs Aρ)))
                        ▹ subTy (extS (extS (single k)))
                                (Hom Nat (wᶠ (wᶠ mρ)) (nsuc (var (vs (vs vz))))))
                       ⊢ subTm (extS (extS (extS (single k))))
                               (renTm (extR (extR (extR (extR ρ))))
                                      (subTm (extS (extS (extS (extS (single x))))) ihS))
                       ∷ aIHTat (renTy vs (renTy vs (renTy vs Aρ)))
                                (wᶠ (wᶠ (wᶠ cMρ))) (wᶠ (wᶠ (wᶠ mρ))) (w (wᶠ mρ)))
               (motAt-at ρ k)
               (⊢-cast ty3 (sub-lemma d2 (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext
                                            (⊢single dk))))))))
        where
          ty3 : subTy (extS (extS (extS (single k))))
                      (aIHTat (renTy vs (renTy vs (renTy vs (renTy vs Aρ))))
                              (wᶠ (wᶠ (wᶠ (wᶠ cMρ)))) (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
                              (w (wᶠ (wᶠ mρ))))
              ≡ aIHTat (renTy vs (renTy vs (renTy vs Aρ)))
                       (wᶠ (wᶠ (wᶠ cMρ))) (wᶠ (wᶠ (wᶠ mρ))) (w (wᶠ mρ))
          ty3 =
            trans (aIHTat-sub {σ = extS (extS (extS (single k)))}
                              (renTy vs (renTy vs (renTy vs (renTy vs Aρ))))
                              (wᶠ (wᶠ (wᶠ (wᶠ cMρ)))) (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
                              (w (wᶠ (wᶠ mρ))))
                  (cong₄ aIHTat
                    (trans (sub-wTy {σ = extS (extS (single k))}
                                    (renTy vs (renTy vs (renTy vs Aρ))))
                           (cong (renTy vs)
                                 (trans (sub-wTy {σ = extS (single k)}
                                                 (renTy vs (renTy vs Aρ)))
                                        (cong (renTy vs)
                                              (trans (sub-wTy {σ = single k}
                                                              (renTy vs Aρ))
                                                     (cong (renTy vs)
                                                           (wk-singleTy Aρ)))))))
                    (trans (wᶠ-sub {σ = extS (extS (single k))} (wᶠ (wᶠ (wᶠ cMρ))))
                           (cong wᶠ (trans (wᶠ-sub {σ = extS (single k)} (wᶠ (wᶠ cMρ)))
                                           (cong wᶠ (trans (wᶠ-sub {σ = single k}
                                                                   (wᶠ cMρ))
                                                           (cong wᶠ (wᶠ-single cMρ)))))))
                    (trans (wᶠ-sub {σ = extS (extS (single k))} (wᶠ (wᶠ (wᶠ mρ))))
                           (cong wᶠ (trans (wᶠ-sub {σ = extS (single k)} (wᶠ (wᶠ mρ)))
                                           (cong wᶠ (trans (wᶠ-sub {σ = single k}
                                                                   (wᶠ mρ))
                                                           (cong wᶠ (wᶠ-single mρ)))))))
                    (trans (sub-w {σ = extS (extS (single k))} (wᶠ (wᶠ mρ)))
                           (cong w (trans (wᶠ-sub {σ = single k} (wᶠ mρ))
                                          (cong wᶠ (wᶠ-single mρ))))))

      d4 : ((Θ ▹ Aρ) ▹ Hom Nat mρ (nsuc (w k)))
             ⊢ subTm (extS (extS (single AX)))
                     (subTm (extS (extS (extS (single k))))
                            (renTm (extR (extR (extR (extR ρ))))
                                   (subTm (extS (extS (extS (extS (single x))))) ihS)))
             ∷ aIHTat (renTy vs (renTy vs Aρ)) (wᶠ (wᶠ cMρ)) (wᶠ (wᶠ mρ)) (w mρ)
      d4 =
        subst (λ T → ((Θ ▹ Aρ) ▹ T)
                       ⊢ subTm (extS (extS (single AX)))
                               (subTm (extS (extS (extS (single k))))
                                      (renTm (extR (extR (extR (extR ρ))))
                                             (subTm (extS (extS (extS (extS (single x))))) ihS)))
                       ∷ aIHTat (renTy vs (renTy vs Aρ)) (wᶠ (wᶠ cMρ))
                                (wᶠ (wᶠ mρ)) (w mρ))
              (cong₂ (λ u v → Hom Nat u (nsuc v)) (wᶠ-single mρ)
                     (trans (sub-w {σ = single AX} (w k))
                            (cong w (wk-single {v = AX} k))))
        (subst (λ T → ((Θ ▹ T)
                        ▹ subTy (extS (single AX)) (Hom Nat (wᶠ mρ) (nsuc (w (w k)))))
                       ⊢ subTm (extS (extS (single AX)))
                               (subTm (extS (extS (extS (single k))))
                                      (renTm (extR (extR (extR (extR ρ))))
                                             (subTm (extS (extS (extS (extS (single x))))) ihS)))
                       ∷ aIHTat (renTy vs (renTy vs Aρ)) (wᶠ (wᶠ cMρ))
                                (wᶠ (wᶠ mρ)) (w mρ))
               (wk-singleTy Aρ)
               (⊢-cast ty4 (sub-lemma d3 (Sub⊢-ext (Sub⊢-ext
                                            (⊢single (⊢auxAt h dx dk)))))))
        where
          ty4 : subTy (extS (extS (single AX)))
                      (aIHTat (renTy vs (renTy vs (renTy vs Aρ)))
                              (wᶠ (wᶠ (wᶠ cMρ))) (wᶠ (wᶠ (wᶠ mρ))) (w (wᶠ mρ)))
              ≡ aIHTat (renTy vs (renTy vs Aρ)) (wᶠ (wᶠ cMρ)) (wᶠ (wᶠ mρ)) (w mρ)
          ty4 =
            trans (aIHTat-sub {σ = extS (extS (single AX))}
                              (renTy vs (renTy vs (renTy vs Aρ)))
                              (wᶠ (wᶠ (wᶠ cMρ))) (wᶠ (wᶠ (wᶠ mρ))) (w (wᶠ mρ)))
                  (cong₄ aIHTat
                    (trans (sub-wTy {σ = extS (single AX)} (renTy vs (renTy vs Aρ)))
                           (cong (renTy vs)
                                 (trans (sub-wTy {σ = single AX} (renTy vs Aρ))
                                        (cong (renTy vs) (wk-singleTy Aρ)))))
                    (trans (wᶠ-sub {σ = extS (single AX)} (wᶠ (wᶠ cMρ)))
                           (cong wᶠ (trans (wᶠ-sub {σ = single AX} (wᶠ cMρ))
                                           (cong wᶠ (wᶠ-single cMρ)))))
                    (trans (wᶠ-sub {σ = extS (single AX)} (wᶠ (wᶠ mρ)))
                           (cong wᶠ (trans (wᶠ-sub {σ = single AX} (wᶠ mρ))
                                           (cong wᶠ (wᶠ-single mρ)))))
                    (trans (sub-w {σ = extS (single AX)} (wᶠ mρ))
                           (cong w (wᶠ-single mρ))))

      d5 : (Θ ▹ Hom Nat μa (nsuc k))
             ⊢ subTm (extS (single a))
                     (subTm (extS (extS (single AX)))
                            (subTm (extS (extS (extS (single k))))
                                   (renTm (extR (extR (extR (extR ρ))))
                                          (subTm (extS (extS (extS (extS (single x))))) ihS))))
             ∷ aIHTat (renTy vs Aρ) (wᶠ cMρ) (wᶠ mρ) (w μa)
      d5 =
        subst (λ T → (Θ ▹ T)
                       ⊢ subTm (extS (single a))
                               (subTm (extS (extS (single AX)))
                                      (subTm (extS (extS (extS (single k))))
                                             (renTm (extR (extR (extR (extR ρ))))
                                                    (subTm (extS (extS (extS (extS (single x))))) ihS))))
                       ∷ aIHTat (renTy vs Aρ) (wᶠ cMρ) (wᶠ mρ) (w μa))
              (cong (λ z → Hom Nat μa (nsuc z)) (wk-single {v = a} k))
              (⊢-cast ty5 (sub-lemma d4 (Sub⊢-ext (⊢single da))))
        where
          ty5 : subTy (extS (single a))
                      (aIHTat (renTy vs (renTy vs Aρ)) (wᶠ (wᶠ cMρ))
                              (wᶠ (wᶠ mρ)) (w mρ))
              ≡ aIHTat (renTy vs Aρ) (wᶠ cMρ) (wᶠ mρ) (w μa)
          ty5 =
            trans (aIHTat-sub {σ = extS (single a)} (renTy vs (renTy vs Aρ))
                              (wᶠ (wᶠ cMρ)) (wᶠ (wᶠ mρ)) (w mρ))
                  (cong₄ aIHTat
                    (trans (sub-wTy {σ = single a} (renTy vs Aρ))
                           (cong (renTy vs) (wk-singleTy Aρ)))
                    (trans (wᶠ-sub {σ = single a} (wᶠ cMρ))
                           (cong wᶠ (wᶠ-single cMρ)))
                    (trans (wᶠ-sub {σ = single a} (wᶠ mρ))
                           (cong wᶠ (wᶠ-single mρ)))
                    (sub-w {σ = single a} mρ))

  ------------------------------------------------------------------------
  -- ★★★ THE SUCCESSOR BRANCH'S IH, APPLIED — `ih-app` at a renaming, and
  --    WITH ITS CERTIFICATE NAMED.
  --
  -- ⚠ WHY THE CERTIFICATE HAS TO BE PEELED, and it was the one place the
  --   route could have stalled.  The (suc,suc) leaf of the induction closes
  --   by instantiating the INDUCTION HYPOTHESIS at the recursive call — and
  --   `⊢app` wants that call's certificate TYPED.  The certificate the
  --   reduction actually hands over is `descS` under SEVEN substitution
  --   layers, and `subTm` does not invert, so no amount of subject
  --   reduction produces a typing for it.  `descS-peel` says what it IS —
  --   `ordtr (nsuc μy) μa (nsuc k) q p` — and then `⊢strong-step` types it
  --   from the two hypotheses the pointwise premise already supplies.
  ------------------------------------------------------------------------

  appAt2R : {Γ' : Cx} {t f₁ f₂ y₁ y₂ u : RTm Γ'} → f₁ ≡ f₂ → y₁ ≡ y₂ →
            t ⟶* app (app f₁ y₁) u → t ⟶* app (app f₂ y₂) u
  appAt2R refl refl hh = hh

  descS-atR : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋)
              (a k p y q : RTm Γ') → RTm Γ'
  descS-atR ρ x a k p y q =
    subTm (single q)
      (subTm (extS (single y))
        (subTm (extS (extS (single p)))
          (subTm (extS (extS (extS (single a))))
            (subTm (extS (extS (extS (extS (single (auxAt ρ x k))))))
              (subTm (extS (extS (extS (extS (extS (single k))))))
                (renTm (extR (extR (extR (extR (extR (extR ρ))))))
                  (subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                         descS)))))))

  -- the IH₀ slot survives the four outer substitutions — `aux-cancel` with
  -- `auxAt ρ x k` in place of `auxIH x k`; the renaming sits BELOW it and
  -- acts as the identity on the slot's variable, so the proof is the same
  aux-cancelR : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋)
                (a k p y q : RTm Γ') →
    subTm (single q)
      (subTm (extS (single y))
        (subTm (extS (extS (single p)))
          (subTm (extS (extS (extS (single a))))
            (w (w (w (w (auxAt ρ x k))))))))
    ≡ auxAt ρ x k
  aux-cancelR ρ x a k p y q =
    trans (cong (λ z → subTm (single q)
                         (subTm (extS (single y))
                           (subTm (extS (extS (single p))) z)))
                (trans (sub-w³ {σ = single a} (w (auxAt ρ x k)))
                       (cong (λ z → w (w (w z)))
                             (wk-single {v = a} (auxAt ρ x k)))))
    (trans (cong (λ z → subTm (single q) (subTm (extS (single y)) z))
                 (trans (sub-w² {σ = single p} (w (auxAt ρ x k)))
                        (cong (λ z → w (w z))
                              (wk-single {v = p} (auxAt ρ x k)))))
    (trans (cong (subTm (single q))
                 (trans (sub-w {σ = single y} (w (auxAt ρ x k)))
                        (cong w (wk-single {v = y} (auxAt ρ x k)))))
           (wk-single {v = q} (auxAt ρ x k))))

  ih-appR : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋) (a k p y q : RTm Γ') →
            app (app (ihS-atR ρ x a k p) y) q
          ⟶* app (app (auxAt ρ x k) y) (descS-atR ρ x a k p y q)
  ih-appR ρ x a k p y q =
    appAt2R (aux-cancelR ρ x a k p y q) (wk-single {v = q} y)
            (step (ξ-appˡ (β _ y)) (step (β _ q) done))

  -- ★★ …AND WHAT THAT CERTIFICATE IS.  Five arguments, five peels: two are
  --    `refl` (the two variables `q` and `p` reach their slots by
  --    computation), one is the five-rung `w`-ladder for the bound, and the
  --    two measures are the `w`/`wᶠ` staircase — `sub-w`+`wᶠ-sub` down,
  --    `ren-wᶠ` across the renaming, `wᶠ-single` at each landing.
  descS-peel : {Γ' : Cx} (ρ : Ren ⌊ Δ ⌋ Γ') (x : RTm ⌊ Δ ⌋)
               (a k p y q : RTm Γ') →
               descS-atR ρ x a k p y q
             ≡ ordtr (nsuc (subTm (single y) (renTm (extR ρ) m)))
                     (subTm (single a) (renTm (extR ρ) m))
                     (nsuc k) q p
  descS-peel {Γ' = Γ'} ρ x a k p y q =
    ordtr-cong₅ (cong nsuc pμy) pμa (cong nsuc pk) refl pp
    where
      AX = auxAt ρ x k
      mρ = renTm (extR ρ) m

      S1 : RTm (Γ' ∙) → RTm Γ'
      S1 t = subTm (single q) t
      S2 : RTm ((Γ' ∙) ∙) → RTm Γ'
      S2 t = S1 (subTm (extS (single y)) t)
      S3 : RTm (((Γ' ∙) ∙) ∙) → RTm Γ'
      S3 t = S2 (subTm (extS (extS (single p))) t)
      S4 : RTm ((((Γ' ∙) ∙) ∙) ∙) → RTm Γ'
      S4 t = S3 (subTm (extS (extS (extS (single a)))) t)
      S5 : RTm (((((Γ' ∙) ∙) ∙) ∙) ∙) → RTm Γ'
      S5 t = S4 (subTm (extS (extS (extS (extS (single AX))))) t)
      S6 : RTm ((((((Γ' ∙) ∙) ∙) ∙) ∙) ∙) → RTm Γ'
      S6 t = S5 (subTm (extS (extS (extS (extS (extS (single k)))))) t)
      S7 : RTm ((((((⌊ Δ ⌋ ∙) ∙) ∙) ∙) ∙) ∙) → RTm Γ'
      S7 t = S6 (renTm (extR (extR (extR (extR (extR (extR ρ)))))) t)

      ------------------------------------------------------------------
      -- argument 1: the measure at the ARGUMENT slot, `w (wᶠ⁵ m)`
      ------------------------------------------------------------------
      a1e7 : subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                   (w (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m))))))
           ≡ w (wᶠ (wᶠ (wᶠ (wᶠ m))))
      a1e7 =
        trans (sub-w {σ = extS (extS (extS (extS (extS (single x)))))}
                     (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m))))))
              (cong w (trans (wᶠ-sub {σ = extS (extS (extS (single x)))}
                                     (wᶠ (wᶠ (wᶠ (wᶠ m)))))
                      (cong wᶠ (trans (wᶠ-sub {σ = extS (extS (single x))}
                                              (wᶠ (wᶠ (wᶠ m))))
                               (cong wᶠ (trans (wᶠ-sub {σ = extS (single x)}
                                                       (wᶠ (wᶠ m)))
                                        (cong wᶠ (trans (wᶠ-sub {σ = single x} (wᶠ m))
                                                 (cong wᶠ (wᶠ-single m))))))))))

      a1e6 : renTm (extR (extR (extR (extR (extR (extR ρ))))))
                   (w (wᶠ (wᶠ (wᶠ (wᶠ m)))))
           ≡ w (wᶠ (wᶠ (wᶠ (wᶠ mρ))))
      a1e6 =
        trans (ren-w {ρ = extR (extR (extR (extR (extR ρ))))} (wᶠ (wᶠ (wᶠ (wᶠ m)))))
              (cong w (trans (ren-wᶠ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ (wᶠ m))))
                      (cong wᶠ (trans (ren-wᶠ {ρ = extR (extR ρ)} (wᶠ (wᶠ m)))
                               (cong wᶠ (trans (ren-wᶠ {ρ = extR ρ} (wᶠ m))
                                        (cong wᶠ (ren-wᶠ {ρ = ρ} m))))))))

      a1e5 : subTm (extS (extS (extS (extS (extS (single k))))))
                   (w (wᶠ (wᶠ (wᶠ (wᶠ mρ)))))
           ≡ w (wᶠ (wᶠ (wᶠ mρ)))
      a1e5 =
        trans (sub-w {σ = extS (extS (extS (extS (single k))))}
                     (wᶠ (wᶠ (wᶠ (wᶠ mρ)))))
              (cong w (trans (wᶠ-sub {σ = extS (extS (single k))} (wᶠ (wᶠ (wᶠ mρ))))
                      (cong wᶠ (trans (wᶠ-sub {σ = extS (single k)} (wᶠ (wᶠ mρ)))
                               (cong wᶠ (trans (wᶠ-sub {σ = single k} (wᶠ mρ))
                                        (cong wᶠ (wᶠ-single mρ))))))))

      a1e4 : subTm (extS (extS (extS (extS (single AX)))))
                   (w (wᶠ (wᶠ (wᶠ mρ))))
           ≡ w (wᶠ (wᶠ mρ))
      a1e4 =
        trans (sub-w {σ = extS (extS (extS (single AX)))} (wᶠ (wᶠ (wᶠ mρ))))
              (cong w (trans (wᶠ-sub {σ = extS (single AX)} (wᶠ (wᶠ mρ)))
                      (cong wᶠ (trans (wᶠ-sub {σ = single AX} (wᶠ mρ))
                               (cong wᶠ (wᶠ-single mρ))))))

      a1e3 : subTm (extS (extS (extS (single a)))) (w (wᶠ (wᶠ mρ)))
           ≡ w (wᶠ mρ)
      a1e3 =
        trans (sub-w {σ = extS (extS (single a))} (wᶠ (wᶠ mρ)))
              (cong w (trans (wᶠ-sub {σ = single a} (wᶠ mρ))
                             (cong wᶠ (wᶠ-single mρ))))

      a1e2 : subTm (extS (extS (single p))) (w (wᶠ mρ)) ≡ w mρ
      a1e2 = trans (sub-w {σ = extS (single p)} (wᶠ mρ))
                   (cong w (wᶠ-single mρ))

      a1e1 : subTm (extS (single y)) (w mρ) ≡ w (subTm (single y) mρ)
      a1e1 = sub-w {σ = single y} mρ

      pμy : S7 (subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                      (w (wᶠ (wᶠ (wᶠ (wᶠ (wᶠ m)))))))
          ≡ subTm (single y) mρ
      pμy =
        trans (cong S7 a1e7)
        (trans (cong S6 a1e6)
        (trans (cong S5 a1e5)
        (trans (cong S4 a1e4)
        (trans (cong S3 a1e3)
        (trans (cong S2 a1e2)
        (trans (cong S1 a1e1)
               (wk-single {v = q} (subTm (single y) mρ))))))))

      ------------------------------------------------------------------
      -- argument 2: the measure at the CARRIER slot, `w³ (wᶠ³ m)`
      ------------------------------------------------------------------
      a2e7 : subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                   (w (w (w (wᶠ (wᶠ (wᶠ m))))))
           ≡ w (w (w (wᶠ (wᶠ m))))
      a2e7 =
        trans (sub-w³ {σ = extS (extS (extS (single x)))} (wᶠ (wᶠ (wᶠ m))))
              (cong (λ z → w (w (w z)))
                    (trans (wᶠ-sub {σ = extS (single x)} (wᶠ (wᶠ m)))
                           (cong wᶠ (trans (wᶠ-sub {σ = single x} (wᶠ m))
                                           (cong wᶠ (wᶠ-single m))))))

      a2e6 : renTm (extR (extR (extR (extR (extR (extR ρ))))))
                   (w (w (w (wᶠ (wᶠ m)))))
           ≡ w (w (w (wᶠ (wᶠ mρ))))
      a2e6 =
        trans (ren-w³ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ m)))
              (cong (λ z → w (w (w z)))
                    (trans (ren-wᶠ {ρ = extR ρ} (wᶠ m))
                           (cong wᶠ (ren-wᶠ {ρ = ρ} m))))

      a2e5 : subTm (extS (extS (extS (extS (extS (single k))))))
                   (w (w (w (wᶠ (wᶠ mρ)))))
           ≡ w (w (w (wᶠ mρ)))
      a2e5 =
        trans (sub-w³ {σ = extS (extS (single k))} (wᶠ (wᶠ mρ)))
              (cong (λ z → w (w (w z)))
                    (trans (wᶠ-sub {σ = single k} (wᶠ mρ))
                           (cong wᶠ (wᶠ-single mρ))))

      a2e4 : subTm (extS (extS (extS (extS (single AX))))) (w (w (w (wᶠ mρ))))
           ≡ w (w (w mρ))
      a2e4 =
        trans (sub-w³ {σ = extS (single AX)} (wᶠ mρ))
              (cong (λ z → w (w (w z))) (wᶠ-single mρ))

      a2e3 : subTm (extS (extS (extS (single a)))) (w (w (w mρ)))
           ≡ w (w (w (subTm (single a) mρ)))
      a2e3 = sub-w³ {σ = single a} mρ

      a2e2 : subTm (extS (extS (single p))) (w (w (w (subTm (single a) mρ))))
           ≡ w (w (subTm (single a) mρ))
      a2e2 = trans (sub-w² {σ = single p} (w (subTm (single a) mρ)))
                   (cong (λ z → w (w z)) (wk-single {v = p} (subTm (single a) mρ)))

      a2e1 : subTm (extS (single y)) (w (w (subTm (single a) mρ)))
           ≡ w (subTm (single a) mρ)
      a2e1 = trans (sub-w {σ = single y} (w (subTm (single a) mρ)))
                   (cong w (wk-single {v = y} (subTm (single a) mρ)))

      pμa : S7 (subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                      (w (w (w (wᶠ (wᶠ (wᶠ m)))))))
          ≡ subTm (single a) mρ
      pμa =
        trans (cong S7 a2e7)
        (trans (cong S6 a2e6)
        (trans (cong S5 a2e5)
        (trans (cong S4 a2e4)
        (trans (cong S3 a2e3)
        (trans (cong S2 a2e2)
        (trans (cong S1 a2e1)
               (wk-single {v = q} (subTm (single a) mρ))))))))

      ------------------------------------------------------------------
      -- argument 3: the BOUND — five rungs of `w`, and the first three
      -- layers reach it by computation
      ------------------------------------------------------------------
      a3e4 : subTm (extS (extS (extS (extS (single AX)))))
                   (w (w (w (w (w k)))))
           ≡ w (w (w (w k)))
      a3e4 = trans (sub-w⁴ {σ = single AX} (w k))
                   (cong (λ z → w (w (w (w z)))) (wk-single {v = AX} k))

      a3e3 : subTm (extS (extS (extS (single a)))) (w (w (w (w k))))
           ≡ w (w (w k))
      a3e3 = trans (sub-w³ {σ = single a} (w k))
                   (cong (λ z → w (w (w z))) (wk-single {v = a} k))

      a3e2 : subTm (extS (extS (single p))) (w (w (w k))) ≡ w (w k)
      a3e2 = trans (sub-w² {σ = single p} (w k))
                   (cong (λ z → w (w z)) (wk-single {v = p} k))

      a3e1 : subTm (extS (single y)) (w (w k)) ≡ w k
      a3e1 = trans (sub-w {σ = single y} (w k)) (cong w (wk-single {v = y} k))

      pk : S5 (w (w (w (w (w k))))) ≡ k
      pk =
        trans (cong S4 a3e4)
        (trans (cong S3 a3e3)
        (trans (cong S2 a3e2)
        (trans (cong S1 a3e1)
               (wk-single {v = q} k))))

      ------------------------------------------------------------------
      -- argument 5: the OTHER certificate — two rungs, the rest computes
      ------------------------------------------------------------------
      pp : S2 (w (w p)) ≡ p
      pp =
        trans (cong S1 (trans (sub-w {σ = single y} (w p))
                              (cong w (wk-single {v = y} p))))
              (wk-single {v = q} p)

  -- ★ THE IH's OWN TYPE, abbreviated — it is the one type every pointwise
  --   argument below is stated at.
  ihTy : {Θ : Ctx} (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (a : RTm ⌊ Θ ⌋) → RTy ⌊ Θ ⌋
  ihTy ρ a = aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                    (subTm (single a) (renTm (extR ρ) m))

  -- applying an IH to its two arguments: two `⊢app`s, three peels
  appIH : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {a ih : RTm ⌊ Θ ⌋} →
          Θ ⊢ ih ∷ ihTy ρ a →
          (y q : RTm ⌊ Θ ⌋) → Θ ⊢ y ∷ renTy ρ A →
          Θ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) (renTm (extR ρ) m)))
                          (subTm (single a) (renTm (extR ρ) m)) →
          Θ ⊢ app (app ih y) q ∷ El (subTm (single y) (renTm (extR ρ) cM))
  appIH {ρ = ρ} {a = a} dih y q dy dq =
    ⊢-cast (cong El (wk-single {v = q} (subTm (single y) (renTm (extR ρ) cM))))
      (⊢app (⊢-cast (cong₂ (λ u c →
                              Π (Hom Nat (nsuc (subTm (single y)
                                                      (renTm (extR ρ) m))) u)
                                (El c))
                           (wk-single {v = y}
                                      (subTm (single a) (renTm (extR ρ) m)))
                           (sub-w {σ = single y} (renTm (extR ρ) cM)))
                    (⊢app dih dy))
            dq)

  -- ★★ THE IRRELEVANCE COMBINATOR, factored out of `aux-irr-z`.  TWO
  --    reductions to `app (app stp a) ihᵢ` and the pointwise hypothesis give
  --    the `Id` between the SOURCES — and the sources are free, so the same
  --    lemma serves all four leaves of the induction below.
  aux-irr : StepExt Δ A cM m stp →
            {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
            {t₁ t₂ a ih₁ ih₂ : RTm ⌊ Θ ⌋} →
            Θ ⊢ a ∷ renTy ρ A →
            Θ ⊢ ih₁ ∷ ihTy ρ a → Θ ⊢ ih₂ ∷ ihTy ρ a →
            t₁ ⟶* app (app (renTm ρ stp) a) ih₁ →
            t₂ ⟶* app (app (renTm ρ stp) a) ih₂ →
            StepPW Δ A cM m Θ ρ a ih₁ ih₂ →
            Prv Θ (Id (El (subTm (single a) (renTm (extR ρ) cM))) t₁ t₂)
  aux-irr ext h da d₁ d₂ r₁ r₂ pw = idOfRed r₁ r₂ (ext h _ _ _ da d₁ d₂ pw)

  -- ★★ …AND THE POINTWISE PREMISE IS EX FALSO whenever EITHER bound is `0`:
  --    `μ y < μ a ≤ 0` is `base`, and `Id (El C) t u` is `El (⌜Id⌝ C t u)`,
  --    so `absurd` reaches it.  ⚠ It does not matter WHICH of the two
  --    certificates is the `≤ 0` one — the code is `⌜Id⌝ C (ih₁ y q)
  --    (ih₂ y q)` either way, which is why three of the four leaves share
  --    this one lemma.
  -- ★ the IH TYPE's naturality — four slots, four peels, and the fourth is
  --   `sub1-ren`.  Needed because every supplier of `StepPW` has to move
  --   its two IH derivations to the deeper context.
  ihTy-ren : {Θ Θ' : Ctx} {ϑ : Ren ⌊ Θ ⌋ ⌊ Θ' ⌋}
             (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (ρ' : Ren ⌊ Δ ⌋ ⌊ Θ' ⌋) →
             (∀ v → ϑ (ρ v) ≡ ρ' v) → (a : RTm ⌊ Θ ⌋) →
             renTy ϑ (ihTy ρ a) ≡ ihTy ρ' (renTm ϑ a)
  ihTy-ren {ϑ = ϑ} ρ ρ' br a =
    trans (aIHTat-ren {ρ = ϑ} (renTy ρ A) (renTm (extR ρ) cM)
                      (renTm (extR ρ) m) (subTm (single a) (renTm (extR ρ) m)))
          (cong₄ aIHTat (renrenTy br A)
                        (renren (extcondR br) cM)
                        (renren (extcondR br) m)
                        (sub1-ren ρ ρ' br a m))

  pwZ : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
        {a c ih₁ ih₂ : RTm ⌊ Θ ⌋} →
        Θ ⊢ a ∷ renTy ρ A →
        Θ ⊢ c ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) nzero →
        Θ ⊢ ih₁ ∷ ihTy ρ a → Θ ⊢ ih₂ ∷ ihTy ρ a →
        StepPW Δ A cM m Θ ρ a ih₁ ih₂
  pwZ {ρ = ρ} h {a = a} da dc d₁ d₂ {ϑ = ϑ} {ρ' = ρ'} hϑ br y q dy dq =
    prv _ (⊢conv (⊢strong-base' (⊢⌜Id⌝ (⊢[] dcM' dy)
                                       (appIH d₁' y q dy dq')
                                       (appIH d₂' y q dy dq'))
                                (⊢[] dm' dy) dμ' dq' dc')
                 (red→≅ᵀ (stepᵀ (El-⌜Id⌝ _ _ _) doneᵀ)))
    where
      -- ⚠ the composite typed renaming — `Ren⊢-comp`, not `Ren⊢-ext` twice:
      --   `ρ'` is a THIRD renaming bridged to `ϑ ∘ ρ`, never that composite.
      h'   = Ren⊢-comp h hϑ br
      dcM' = ren-lemma dcM (Ren⊢-ext h')
      dm'  = ren-lemma dm (Ren⊢-ext h')
      -- ★ the ONE naturality this proof pays: the bound arrives as
      --   `renTm ϑ (μ a)` and every typing rule below wants `μ (renTm ϑ a)`.
      μeq  = sub1-ren ρ ρ' br a m
      da'  = ⊢-cast (renrenTy br A) (ren-lemma da hϑ)
      dμ'  = ⊢[] dm' da'
      dq'  = ⊢-cast (cong (λ u → Hom Nat (nsuc (subTm (single y)
                                                      (renTm (extR ρ') m))) u)
                          μeq)
                    dq
      dc'  = ⊢-cast (cong (λ u → Hom Nat u nzero) μeq) (ren-lemma dc hϑ)
      d₁'  = ⊢-cast (ihTy-ren ρ ρ' br a) (ren-lemma d₁ hϑ)
      d₂'  = ⊢-cast (ihTy-ren ρ ρ' br a) (ren-lemma d₂ hϑ)

  -- ★ …and the ORIGINAL zero-irrelevance is now DERIVED — the faithfulness
  --   check on the factoring.
  aux-irr-z : StepExt Δ A cM m stp →
              {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
              (x : RTm ⌊ Δ ⌋) (a c₁ c₂ : RTm ⌊ Θ ⌋) →
              Δ ⊢ x ∷ A → Θ ⊢ a ∷ renTy ρ A →
              Θ ⊢ c₁ ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) nzero →
              Θ ⊢ c₂ ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) nzero →
              Prv Θ (Id (El (subTm (single a) (renTm (extR ρ) cM)))
                        (app (app (auxAt ρ x nzero) a) c₁)
                        (app (app (auxAt ρ x nzero) a) c₂))
  aux-irr-z ext {ρ = ρ} h x a c₁ c₂ dx da dc₁ dc₂ =
    aux-irr ext h da (⊢ihZ-atR h dx da dc₁) (⊢ihZ-atR h dx da dc₂)
            (auxAt-step-z ρ x a nzero c₁ done (λ _ → done))
            (auxAt-step-z ρ x a nzero c₂ done (λ _ → done))
            (pwZ h da dc₁ (⊢ihZ-atR h dx da dc₁) (⊢ihZ-atR h dx da dc₂))

  ------------------------------------------------------------------------
  -- ★★★★ PIECE 7 — IRRELEVANCE AS AN OBJECT-LANGUAGE TYPE.
  --
  -- ⚠ WHY `aux-irr-z` IS NOT ALREADY THE THEOREM.  It is META-level: an
  --   Agda function from two certificates to a `Prv`.  An INDUCTION on the
  --   bound is a `natrec`, and a `natrec` needs a MOTIVE — an `RTy`.  `irrT`
  --   is that motive, and `aux-irr-z` becomes a branch only once the
  --   statement exists to be a branch OF.
  --
  -- ★ TWO INDICES, TWO BOUNDS, and only one of them is internal.  Through
  --   the induction the INDICES never change (the successor branch recurses
  --   at `auxIH X k` with `X` untouched — the `gcd-2-1` run measured it), so
  --   `x` and `y` stay META-level parameters.  `irrT` quantifies the three
  --   binders `a , c₁ , c₂` and takes BOTH bounds as parameters; `irrB`
  --   binds the second one internally, which is what the outer induction's
  --   motive has to do.
  --
  -- ★★ AND IT IS INDEXED BY THE AMBIENT RENAMING `θ`, not by a `vs`-tower.
  --    Every branch of the induction lands at a different depth; with the
  --    tower spelled out, each depth needs its own peel (that is what
  --    `wᶠ¹/²/³-single` are, and they ran out at three).  With `θ` abstract
  --    there is ONE peel — `peelθ` — and the branches differ only in which
  --    `θ` they pass.
  ------------------------------------------------------------------------

  -- the ambient renaming, pushed under `irrT`'s three binders
  θ₃ : {Γ' : Cx} → Ren ⌊ Δ ⌋ Γ' → Ren ⌊ Δ ⌋ (((Γ' ∙) ∙) ∙)
  θ₃ θ v = vs (vs (vs (θ v)))

  cond₃ : {Γ' Γ'' : Cx} {σ : Sub Γ' Γ''} {θ : Ren ⌊ Δ ⌋ Γ'} {θ' : Ren ⌊ Δ ⌋ Γ''} →
          (∀ v → σ (θ v) ≡ var (θ' v)) →
          (∀ v → extS (extS (extS σ)) (θ₃ θ v) ≡ var (θ₃ θ' v))
  cond₃ h v = cong (renTm vs) (cong (renTm vs) (cong (renTm vs) (h v)))

  cond₃R : {Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''} {θ : Ren ⌊ Δ ⌋ Γ'} {θ' : Ren ⌊ Δ ⌋ Γ''} →
           (∀ v → ϑ (θ v) ≡ θ' v) →
           (∀ v → extR (extR (extR ϑ)) (θ₃ θ v) ≡ θ₃ θ' v)
  cond₃R h v = cong vs (cong vs (cong vs (h v)))

  -- ⚠⚠ THE ONE REAL PEEL, and it is the whole cost of the piece.
  --   `⊢aux-appAt` demands the measure as `subTm (single a) (renTm (extR θ) m)`
  --   — a SUBSTITUTED RENAMING — while the certificate slots reach the body
  --   as a TOWER of `renTy vs`.  It is unavoidable: reordering the binders
  --   does not change the tower's depth, and canonicalising on either form
  --   just moves the collapse to the other side.  ★ Pointwise, it is two
  --   `refl`s and a `renTm-renTm` fuse — and generic in `θ` and in the
  --   family, so `cM` and `m` share it at every depth.
  ww-ren : {Γ' : Cx} (θ : Ren ⌊ Δ ⌋ Γ') (t : RTm (⌊ Δ ⌋ ∙)) →
           w (w (renTm (extR θ) t)) ≡ renTm (λ v → vs (vs (extR θ v))) t
  ww-ren θ t = trans (cong w (renTm-renTm t)) (renTm-renTm t)

  peelθ : {Γ' : Cx} (θ : Ren ⌊ Δ ⌋ Γ') (t : RTm (⌊ Δ ⌋ ∙)) →
          subTm (single (var (vs (vs vz)))) (renTm (extR (θ₃ θ)) t)
        ≡ w (w (renTm (extR θ) t))
  peelθ θ t = trans (subren {ρ' = λ v → vs (vs (extR θ v))} bridge t)
                    (sym (ww-ren θ t))
    where
      bridge : ∀ v → single (var (vs (vs vz))) (extR (θ₃ θ) v)
                   ≡ var (vs (vs (extR θ v)))
      bridge vz     = refl
      bridge (vs v) = refl

  -- the TYPE-level twin: the carrier slot's three `renTy vs`, fused
  renθ₃ : {Γ' : Cx} (θ : Ren ⌊ Δ ⌋ Γ') (T : RTy ⌊ Δ ⌋) →
          renTy vs (renTy vs (renTy vs (renTy θ T))) ≡ renTy (θ₃ θ) T
  renθ₃ θ T =
    trans (cong (λ S → renTy vs (renTy vs S)) (renTy-renTy T))
          (trans (cong (renTy vs) (renTy-renTy T)) (renTy-renTy T))

  -- ★ the auxiliary's own naturality.  `auxAt` is a `natrec` of two RENAMED
  --   branches, so a substitution meets each of them as `subren` — the
  --   auxiliary never has to be re-derived at a new depth.
  auxAt-sub : {Γ' Γ'' : Cx} {σ : Sub Γ' Γ''}
              (θ : Ren ⌊ Δ ⌋ Γ') (θ' : Ren ⌊ Δ ⌋ Γ'') →
              (∀ v → σ (θ v) ≡ var (θ' v)) →
              (x : RTm ⌊ Δ ⌋) (n : RTm Γ') →
              subTm σ (auxAt θ x n) ≡ auxAt θ' x (subTm σ n)
  auxAt-sub {σ = σ} θ θ' h x n =
    cong₂ (λ z s → natrec z s (subTm σ n))
          (subren h (auxZ x))
          (subren (extcond (extcond h)) (auxS x))

  auxAt-renʳ : {Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''}
               (θ : Ren ⌊ Δ ⌋ Γ') (θ' : Ren ⌊ Δ ⌋ Γ'') →
               (∀ v → ϑ (θ v) ≡ θ' v) →
               (x : RTm ⌊ Δ ⌋) (n : RTm Γ') →
               renTm ϑ (auxAt θ x n) ≡ auxAt θ' x (renTm ϑ n)
  auxAt-renʳ {ϑ = ϑ} θ θ' h x n =
    cong₂ (λ z s → natrec z s (renTm ϑ n))
          (renren h (auxZ x))
          (renren (extcondR (extcondR h)) (auxS x))

  ------------------------------------------------------------------------
  -- ★★★ THE IH ARGUMENT'S NATURALITY — what makes `StepExt`'s pointwise
  --     premise supplyable at a DEEPER context than `Θ`.
  --
  -- ⚠ WHY IT IS NEEDED AT ALL (2026-08-16).  A provider of `StepExt` whose
  --   step CASE-SPLITS — and gcd's does, three times — consumes the
  --   pointwise premise inside `natrec` branches, i.e. in a context with
  --   binders `Θ` does not have.  So the premise is renaming-indexed, and
  --   the library, which supplies it at `ih₁ = ihS-atR ρ x a k p`, has to
  --   say what a renaming does to that.
  --
  -- ★ FIVE LAYERS, FIVE PEELS, and nothing else: four substitutions by
  --   `rensub` and the innermost renaming by `renren`.  Each bridge is the
  --   one below it under an `extcond`, so the whole thing is decided
  --   variable-by-variable exactly once — the pointwise calculus, not a
  --   tower lemma.  ⭐ The only layer that is not a bare `singleBr` is the
  --   auxiliary's, and it composes with `auxAt-renʳ` in one `cong`.
  --
  -- ⚠ `descS-atR` deliberately gets NO twin.  Its seven layers would be a
  --   real cost, and it is not needed: once the term has been rewritten to
  --   `ihS-atR θ' …`, `ih-appR` is instantiated FRESH at the deeper context
  --   and emits `descS-atR θ' …` directly, and `descS-peel` is already
  --   generic in the renaming.
  ------------------------------------------------------------------------

  ihS-atR-renʳ : {Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''}
                 (θ : Ren ⌊ Δ ⌋ Γ') (θ' : Ren ⌊ Δ ⌋ Γ'') →
                 (∀ v → ϑ (θ v) ≡ θ' v) →
                 (x : RTm ⌊ Δ ⌋) (a k p : RTm Γ') →
                 renTm ϑ (ihS-atR θ x a k p)
               ≡ ihS-atR θ' x (renTm ϑ a) (renTm ϑ k) (renTm ϑ p)
  ihS-atR-renʳ {ϑ = ϑ} θ θ' h x a k p =
    trans (rensub {ϑ' = extR ϑ} br₁ T₄)
      (cong (subTm (single (renTm ϑ p)))
        (trans (rensub {ϑ' = extR (extR ϑ)} br₂ T₃)
          (cong (subTm (extS (single (renTm ϑ a))))
            (trans (rensub {ϑ' = extR (extR (extR ϑ))} br₃ T₂)
              (cong (subTm (extS (extS (single (auxAt θ' x (renTm ϑ k))))))
                (trans (rensub {ϑ' = extR (extR (extR (extR ϑ)))} br₄ T₁)
                  (cong (subTm (extS (extS (extS (single (renTm ϑ k))))))
                    (renren br₅ T₀))))))))
    where
      T₀ = subTm (extS (extS (extS (extS (single x))))) ihS
      T₁ = renTm (extR (extR (extR (extR θ)))) T₀
      T₂ = subTm (extS (extS (extS (single k)))) T₁
      T₃ = subTm (extS (extS (single (auxAt θ x k)))) T₂
      T₄ = subTm (extS (single a)) T₃

      -- ★ the auxiliary's layer: `singleBr` moves the renaming inside, then
      --   `auxAt-renʳ` re-indexes the auxiliary itself.
      brAux : ∀ v → renTm ϑ (single (auxAt θ x k) v)
                  ≡ single (auxAt θ' x (renTm ϑ k)) (extR ϑ v)
      brAux v = trans (singleBr (auxAt θ x k) v)
                      (cong (λ t → single t (extR ϑ v)) (auxAt-renʳ θ θ' h x k))

      -- ⚠ EACH BRIDGE IS NAMED WITH ITS TYPE, and that is not style.  Left
      --   inline, `rensub`'s re-emitted `σ'` and `ϑ'` are metas that only
      --   the bridge's own type pins, and a tower of `extcondRS`s blocks
      --   every one of them on the next — measured, five unsolved
      --   constraints.  ⭐ Same signature of failure as `subTm` not
      --   inverting: an UNSOLVED META, never a wrong solution.
      br₁ : ∀ v → renTm ϑ (single p v) ≡ single (renTm ϑ p) (extR ϑ v)
      br₁ = singleBr p

      br₂ : ∀ v → renTm (extR ϑ) (extS (single a) v)
                ≡ extS (single (renTm ϑ a)) (extR (extR ϑ) v)
      br₂ = extcondRS (singleBr a)

      br₃ : ∀ v → renTm (extR (extR ϑ)) (extS (extS (single (auxAt θ x k))) v)
                ≡ extS (extS (single (auxAt θ' x (renTm ϑ k))))
                       (extR (extR (extR ϑ)) v)
      br₃ = extcondRS (extcondRS brAux)

      br₄ : ∀ v → renTm (extR (extR (extR ϑ))) (extS (extS (extS (single k))) v)
                ≡ extS (extS (extS (single (renTm ϑ k))))
                       (extR (extR (extR (extR ϑ))) v)
      br₄ = extcondRS (extcondRS (extcondRS (singleBr k)))

      br₅ : ∀ v → extR (extR (extR (extR ϑ))) (extR (extR (extR (extR θ))) v)
                ≡ extR (extR (extR (extR θ'))) v
      br₅ = extcondR (extcondR (extcondR (extcondR h)))

  ------------------------------------------------------------------------
  -- ★★ THE MOTIVE.  `(a : A) (c₁ : μ a ≤ n₁) (c₂ : μ a ≤ n₂) →
  --    aux x n₁ a c₁ ≡ aux y n₂ a c₂`.
  --
  -- ★ `irrT'` takes every slot ALREADY at the depth it is used, so `subTy`
  --   and `renTy` distribute into it by `refl` — the `aAuxB'` trick.  All
  --   the naturality lives in the eight peels of `irrT-sub`/`-ren`.
  ------------------------------------------------------------------------

  irrT' : {Γ' : Cx} (Aθ : RTy Γ') (m₁ b₁ : RTm (Γ' ∙)) (m₂ b₂ : RTm ((Γ' ∙) ∙))
          (c₃ zx zy : RTm (((Γ' ∙) ∙) ∙)) → RTy Γ'
  irrT' Aθ m₁ b₁ m₂ b₂ c₃ zx zy =
    Π Aθ
      (Π (Hom Nat m₁ b₁)
        (Π (Hom Nat m₂ b₂)
          (Id (El c₃)
              (app (app zx (var (vs (vs vz)))) (var (vs vz)))
              (app (app zy (var (vs (vs vz)))) (var vz)))))

  irrT : {Γ' : Cx} (θ : Ren ⌊ Δ ⌋ Γ') (x y : RTm ⌊ Δ ⌋) (n₁ n₂ : RTm Γ') → RTy Γ'
  irrT θ x y n₁ n₂ =
    irrT' (renTy θ A) (renTm (extR θ) m) (w n₁)
          (w (renTm (extR θ) m)) (w (w n₂))
          (w (w (renTm (extR θ) cM)))
          (auxAt (θ₃ θ) x (w (w (w n₁))))
          (auxAt (θ₃ θ) y (w (w (w n₂))))

  irrT-sub : {Γ' Γ'' : Cx} {σ : Sub Γ' Γ''}
             (θ : Ren ⌊ Δ ⌋ Γ') (θ' : Ren ⌊ Δ ⌋ Γ'') →
             (∀ v → σ (θ v) ≡ var (θ' v)) →
             (x y : RTm ⌊ Δ ⌋) (n₁ n₂ : RTm Γ') →
             subTy σ (irrT θ x y n₁ n₂)
           ≡ irrT θ' x y (subTm σ n₁) (subTm σ n₂)
  irrT-sub {σ = σ} θ θ' h x y n₁ n₂ =
    cong₈ irrT'
      (subrenTy h A)
      (subren (extcond h) m)
      (sub-w n₁)
      (trans (sub-w {σ = extS σ} (renTm (extR θ) m))
             (cong w (subren (extcond h) m)))
      (sub-w² n₂)
      (trans (sub-w² {σ = extS σ} (renTm (extR θ) cM))
             (cong (λ z → w (w z)) (subren (extcond h) cM)))
      (trans (auxAt-sub (θ₃ θ) (θ₃ θ') (cond₃ {σ = σ} {θ = θ} {θ' = θ'} h) x (w (w (w n₁))))
             (cong (auxAt (θ₃ θ') x) (sub-w³ n₁)))
      (trans (auxAt-sub (θ₃ θ) (θ₃ θ') (cond₃ {σ = σ} {θ = θ} {θ' = θ'} h) y (w (w (w n₂))))
             (cong (auxAt (θ₃ θ') y) (sub-w³ n₂)))

  irrT-ren : {Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''}
             (θ : Ren ⌊ Δ ⌋ Γ') (θ' : Ren ⌊ Δ ⌋ Γ'') →
             (∀ v → ϑ (θ v) ≡ θ' v) →
             (x y : RTm ⌊ Δ ⌋) (n₁ n₂ : RTm Γ') →
             renTy ϑ (irrT θ x y n₁ n₂)
           ≡ irrT θ' x y (renTm ϑ n₁) (renTm ϑ n₂)
  irrT-ren {ϑ = ϑ} θ θ' h x y n₁ n₂ =
    cong₈ irrT'
      (renrenTy h A)
      (renren (extcondR h) m)
      (ren-w n₁)
      (trans (ren-w {ρ = extR ϑ} (renTm (extR θ) m))
             (cong w (renren (extcondR h) m)))
      (ren-w² n₂)
      (trans (ren-w² {ρ = extR ϑ} (renTm (extR θ) cM))
             (cong (λ z → w (w z)) (renren (extcondR h) cM)))
      (trans (auxAt-renʳ (θ₃ θ) (θ₃ θ') (cond₃R {ϑ = ϑ} {θ = θ} {θ' = θ'} h) x (w (w (w n₁))))
             (cong (auxAt (θ₃ θ') x) (ren-w³ n₁)))
      (trans (auxAt-renʳ (θ₃ θ) (θ₃ θ') (cond₃R {ϑ = ϑ} {θ = θ} {θ' = θ'} h) y (w (w (w n₂))))
             (cong (auxAt (θ₃ θ') y) (ren-w³ n₂)))

  ------------------------------------------------------------------------
  -- the three binders, as a context, and the three variables they bind —
  -- named once so every leaf of the induction reuses them
  ------------------------------------------------------------------------

  irrΘ : {Θ : Ctx} (θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (n₁ n₂ : RTm ⌊ Θ ⌋) → Ctx
  irrΘ {Θ = Θ} θ n₁ n₂ =
    ((Θ ▹ renTy θ A) ▹ Hom Nat (renTm (extR θ) m) (w n₁))
       ▹ Hom Nat (w (renTm (extR θ) m)) (w (w n₂))

  ⊢irr-θ₃ : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ θ →
            {n₁ n₂ : RTm ⌊ Θ ⌋} → Ren⊢ Δ (irrΘ θ n₁ n₂) (θ₃ θ)
  ⊢irr-θ₃ h = wR (wR (wR h))

  ⊢irr-a : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {n₁ n₂ : RTm ⌊ Θ ⌋} →
           irrΘ θ n₁ n₂ ⊢ var (vs (vs vz)) ∷ renTy (θ₃ θ) A
  ⊢irr-a {θ = θ} = ⊢-cast (renθ₃ θ A) (⊢var (there (there here)))

  ⊢irr-c₁ : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {n₁ n₂ : RTm ⌊ Θ ⌋} →
            irrΘ θ n₁ n₂ ⊢ var (vs vz)
              ∷ Hom Nat (subTm (single (var (vs (vs vz))))
                               (renTm (extR (θ₃ θ)) m))
                        (w (w (w n₁)))
  ⊢irr-c₁ {θ = θ} {n₁ = n₁} =
    ⊢-cast (cong (λ z → Hom Nat z (w (w (w n₁)))) (sym (peelθ θ m)))
           (⊢var (there here))

  ⊢irr-c₂ : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {n₁ n₂ : RTm ⌊ Θ ⌋} →
            irrΘ θ n₁ n₂ ⊢ var vz
              ∷ Hom Nat (subTm (single (var (vs (vs vz))))
                               (renTm (extR (θ₃ θ)) m))
                        (w (w (w n₂)))
  ⊢irr-c₂ {θ = θ} {n₂ = n₂} =
    ⊢-cast (cong (λ z → Hom Nat z (w (w (w n₂)))) (sym (peelθ θ m)))
           (⊢var here)

  ⊢irrT : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ θ →
          {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A →
          {n₁ n₂ : RTm ⌊ Θ ⌋} → Θ ⊢ n₁ ∷ Nat → Θ ⊢ n₂ ∷ Nat →
          Θ ⊢ty irrT θ x y n₁ n₂
  ⊢irrT {θ = θ} h dx dy dn₁ dn₂ =
    ty-Π (ren-ty dA h)
      (ty-Π (ty-Hom ty-Nat dmθ (⊢wk dn₁))
        (ty-Π (ty-Hom ty-Nat (⊢wk dmθ) (⊢wk (⊢wk dn₂)))
          (ty-Id (ty-El (⊢wk (⊢wk dcMθ)))
                 (⊢-cast (cong El (peelθ θ cM))
                         (⊢aux-appAt (⊢irr-θ₃ h) dx (⊢wk (⊢wk (⊢wk dn₁)))
                                     ⊢irr-a ⊢irr-c₁))
                 (⊢-cast (cong El (peelθ θ cM))
                         (⊢aux-appAt (⊢irr-θ₃ h) dy (⊢wk (⊢wk (⊢wk dn₂)))
                                     ⊢irr-a ⊢irr-c₂)))))
    where
      dmθ = ren-lemma dm (Ren⊢-ext h)
      dcMθ = ren-lemma dcM (Ren⊢-ext h)

  -- ★ …and the OUTER motive: the second bound bound internally.
  irrB : (x y : RTm ⌊ Δ ⌋) → RTy (⌊ Δ ⌋ ∙)
  irrB x y = Π Nat (irrT (λ v → vs (vs v)) x y (var (vs vz)) (var vz))

  ⊢irrB : {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A → (Δ ▹ Nat) ⊢ty irrB x y
  ⊢irrB dx dy =
    ty-Π ty-Nat
      (⊢irrT (wR there) dx dy (⊢var (there here)) (⊢var here))

  ------------------------------------------------------------------------
  -- ★★★★ PIECE 8 — THE INDUCTION ON THE BOUND.
  --
  -- ONE `natrec` on the first bound, and INSIDE each of its branches one
  -- more on the second.  ⚠ The inner one is a CASE SPLIT, not a recursion:
  -- the second bound never descends, it is only looked at.  That is why the
  -- two-bound statement costs ~1.5× the one-bound one and not twice.
  --
  -- The four leaves:
  --   (0,0) (0,S) (S,0)  the pointwise premise is EX FALSO — one of the two
  --                      certificates bounds `μ a` by `0`, so `μ y < μ a ≤ 0`
  --                      is `base`.  All three are `pwZ`.
  --   (S,S)              the pointwise premise IS the induction hypothesis,
  --                      instantiated at the recursive call.
  ------------------------------------------------------------------------

  -- ⚠ `prv-cast` is now TOP LEVEL — it never used the module's parameters.

  vsθ : {Γ' : Cx} → Ren ⌊ Δ ⌋ Γ' → Ren ⌊ Δ ⌋ (Γ' ∙)
  vsθ θ v = vs (θ v)

  -- ★ INTRODUCTION: three `⊢lam`s, and the body is the `Id` that `aux-irr`
  --   produces — with `peelθ` folded in, since that is the one place the
  --   motive's `El` and the combinator's `El` are written differently.
  irrIntro : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ θ →
             {x y : RTm ⌊ Δ ⌋} {n₁ n₂ : RTm ⌊ Θ ⌋} →
             Θ ⊢ n₁ ∷ Nat → Θ ⊢ n₂ ∷ Nat →
             Prv (irrΘ θ n₁ n₂)
                 (Id (El (subTm (single (var (vs (vs vz))))
                                (renTm (extR (θ₃ θ)) cM)))
                     (app (app (auxAt (θ₃ θ) x (w (w (w n₁))))
                               (var (vs (vs vz)))) (var (vs vz)))
                     (app (app (auxAt (θ₃ θ) y (w (w (w n₂))))
                               (var (vs (vs vz)))) (var vz))) →
             Prv Θ (irrT θ x y n₁ n₂)
  irrIntro {θ = θ} h {x = x} {y = y} {n₁ = n₁} {n₂ = n₂} dn₁ dn₂ (prv e d) =
    prv (lam (lam (lam e)))
        (⊢lam (ren-ty dA h)
          (⊢lam (ty-Hom ty-Nat dmθ (⊢wk dn₁))
            (⊢lam (ty-Hom ty-Nat (⊢wk dmθ) (⊢wk (⊢wk dn₂)))
                  (⊢-cast (cong (λ C →
                                   Id (El C)
                                      (app (app (auxAt (θ₃ θ) x (w (w (w n₁))))
                                                (var (vs (vs vz)))) (var (vs vz)))
                                      (app (app (auxAt (θ₃ θ) y (w (w (w n₂))))
                                                (var (vs (vs vz)))) (var vz)))
                                (peelθ θ cM))
                          d))))
    where dmθ = ren-lemma dm (Ren⊢-ext h)

  -- ★★ ELIMINATION — what `irrT` MEANS, in the combinator's own vocabulary.
  --    Three `⊢app`s; every peel is `wk-single`, `sub-w` or `auxAt-sub`.
  --    ⚠ This is also the form PIECE 9 consumes: an internal `Id` between
  --    two auxiliary applications, at bounds and certificates of the
  --    caller's choosing.
  irrElim : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {x y : RTm ⌊ Δ ⌋}
            {n₁ n₂ t : RTm ⌊ Θ ⌋} →
            Θ ⊢ t ∷ irrT θ x y n₁ n₂ →
            (a c₁ c₂ : RTm ⌊ Θ ⌋) →
            Θ ⊢ a ∷ renTy θ A →
            Θ ⊢ c₁ ∷ Hom Nat (subTm (single a) (renTm (extR θ) m)) n₁ →
            Θ ⊢ c₂ ∷ Hom Nat (subTm (single a) (renTm (extR θ) m)) n₂ →
            Prv Θ (Id (El (subTm (single a) (renTm (extR θ) cM)))
                      (app (app (auxAt θ x n₁) a) c₁)
                      (app (app (auxAt θ y n₂) a) c₂))
  irrElim {Θ = Θ} {θ = θ} {x = x} {y = y} {n₁ = n₁} {n₂ = n₂} {t = t} dt a c₁ c₂ da dc₁ dc₂ =
    prv (app (app (app t a) c₁) c₂)
        (⊢-cast eq3 (⊢app (⊢-cast eq2 (⊢app (⊢-cast eq1 (⊢app dt da)) dc₁)) dc₂))
    where
      mθ  = renTm (extR θ) m
      cMθ = renTm (extR θ) cM
      μa  = subTm (single a) mθ
      μcM = subTm (single a) cMθ
      θ₁ = vsθ θ
      θ₂ = vsθ (vsθ θ)

      -- layer 1: the carrier `a`
      b₁₁ : subTm (single a) (w n₁) ≡ n₁
      b₁₁ = wk-single {v = a} n₁

      m₂₁ : subTm (extS (single a)) (w mθ) ≡ w μa
      m₂₁ = sub-w {σ = single a} mθ

      b₂₁ : subTm (extS (single a)) (w (w n₂)) ≡ w n₂
      b₂₁ = trans (sub-w {σ = single a} (w n₂)) (cong w (wk-single {v = a} n₂))

      c₃₁ : subTm (extS (extS (single a))) (w (w cMθ)) ≡ w (w μcM)
      c₃₁ = sub-w² {σ = single a} cMθ

      aux₁ : {z : RTm ⌊ Δ ⌋} {n : RTm ⌊ Θ ⌋} →
             subTm (extS (extS (single a))) (auxAt (θ₃ θ) z (w (w (w n))))
           ≡ auxAt θ₂ z (w (w n))
      aux₁ {z = z} {n = n} =
        trans (auxAt-sub (θ₃ θ) θ₂ (λ v → refl) z (w (w (w n))))
              (cong (auxAt θ₂ z)
                    (trans (sub-w² {σ = single a} (w n))
                           (cong (λ u → w (w u)) (wk-single {v = a} n))))

      eq1 : subTy (single a)
                  (Π (Hom Nat mθ (w n₁))
                     (Π (Hom Nat (w mθ) (w (w n₂)))
                        (Id (El (w (w cMθ)))
                            (app (app (auxAt (θ₃ θ) x (w (w (w n₁))))
                                      (var (vs (vs vz)))) (var (vs vz)))
                            (app (app (auxAt (θ₃ θ) y (w (w (w n₂))))
                                      (var (vs (vs vz)))) (var vz)))))
          ≡ Π (Hom Nat μa n₁)
              (Π (Hom Nat (w μa) (w n₂))
                 (Id (El (w (w μcM)))
                     (app (app (auxAt θ₂ x (w (w n₁))) (w (w a))) (var (vs vz)))
                     (app (app (auxAt θ₂ y (w (w n₂))) (w (w a))) (var vz))))
      eq1 = cong₆ (λ u₁ u₂ u₃ u₄ e₁ e₂ →
                     Π (Hom Nat μa u₁) (Π (Hom Nat u₂ u₃) (Id (El u₄) e₁ e₂)))
                  b₁₁ m₂₁ b₂₁ c₃₁
                  (cong (λ z → app (app z (w (w a))) (var (vs vz))) (aux₁ {z = x}))
                  (cong (λ z → app (app z (w (w a))) (var vz)) (aux₁ {z = y}))

      -- layer 2: the first certificate
      aux₂ : {z : RTm ⌊ Δ ⌋} {n : RTm ⌊ Θ ⌋} →
             subTm (extS (single c₁)) (auxAt θ₂ z (w (w n))) ≡ auxAt θ₁ z (w n)
      aux₂ {z = z} {n = n} =
        trans (auxAt-sub θ₂ θ₁ (λ v → refl) z (w (w n)))
              (cong (auxAt θ₁ z)
                    (trans (sub-w {σ = single c₁} (w n)) (cong w (wk-single {v = c₁} n))))

      eq2 : subTy (single c₁)
                  (Π (Hom Nat (w μa) (w n₂))
                     (Id (El (w (w μcM)))
                         (app (app (auxAt θ₂ x (w (w n₁))) (w (w a))) (var (vs vz)))
                         (app (app (auxAt θ₂ y (w (w n₂))) (w (w a))) (var vz))))
          ≡ Π (Hom Nat μa n₂)
              (Id (El (w μcM))
                  (app (app (auxAt θ₁ x (w n₁)) (w a)) (w c₁))
                  (app (app (auxAt θ₁ y (w n₂)) (w a)) (var vz)))
      eq2 = cong₅ (λ u₁ u₂ u₃ e₁ e₂ → Π (Hom Nat u₁ u₂) (Id (El u₃) e₁ e₂))
                  (wk-single {v = c₁} μa) (wk-single {v = c₁} n₂)
                  (trans (sub-w {σ = single c₁} (w μcM))
                         (cong w (wk-single {v = c₁} μcM)))
                  (cong₂ (λ z u → app (app z u) (w c₁)) (aux₂ {z = x})
                         (trans (sub-w {σ = single c₁} (w a))
                                (cong w (wk-single {v = c₁} a))))
                  (cong₂ (λ z u → app (app z u) (var vz)) (aux₂ {z = y})
                         (trans (sub-w {σ = single c₁} (w a))
                                (cong w (wk-single {v = c₁} a))))

      -- layer 3: the second certificate
      aux₃ : {z : RTm ⌊ Δ ⌋} {n : RTm ⌊ Θ ⌋} →
             subTm (single c₂) (auxAt θ₁ z (w n)) ≡ auxAt θ z n
      aux₃ {z = z} {n = n} =
        trans (auxAt-sub θ₁ θ (λ v → refl) z (w n))
              (cong (auxAt θ z) (wk-single {v = c₂} n))

      eq3 : subTy (single c₂)
                  (Id (El (w μcM))
                      (app (app (auxAt θ₁ x (w n₁)) (w a)) (w c₁))
                      (app (app (auxAt θ₁ y (w n₂)) (w a)) (var vz)))
          ≡ Id (El μcM) (app (app (auxAt θ x n₁) a) c₁)
                        (app (app (auxAt θ y n₂) a) c₂)
      eq3 = cong₃ (λ u e₁ e₂ → Id (El u) e₁ e₂)
                  (wk-single {v = c₂} μcM)
                  (cong₃ (λ z u v → app (app z u) v) (aux₃ {z = x})
                         (wk-single {v = c₂} a) (wk-single {v = c₂} c₁))
                  (cong₂ (λ z u → app (app z u) c₂) (aux₃ {z = y})
                         (wk-single {v = c₂} a))

  -- ★★ THE INNER CASE SPLIT.
  irrSplit : {Θ₀ : Ctx} {θ : Ren ⌊ Δ ⌋ (⌊ Θ₀ ⌋ ∙)} → Ren⊢ Δ (Θ₀ ▹ Nat) θ →
             {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A →
             {n₁ : RTm (⌊ Θ₀ ⌋ ∙)} → (Θ₀ ▹ Nat) ⊢ n₁ ∷ Nat →
             Prv (Θ₀ ▹ Nat) (irrT θ x y n₁ nzero) →
             Prv (((Θ₀ ▹ Nat) ▹ Nat) ▹ irrT (vsθ θ) x y (w n₁) (var vz))
                 (irrT (vsθ (vsθ θ)) x y (w (w n₁)) (nsuc (var (vs vz)))) →
             Prv (Θ₀ ▹ Nat) (irrT θ x y n₁ (var vz))
  irrSplit {θ = θ} h dx dy {n₁ = n₁} dn₁ (prv z dz) (prv s ds) =
    prv (natrec z s (var vz))
        (⊢-cast eqAt (⊢natrec (⊢irrT (wR h) dx dy (⊢wk dn₁) (⊢var here))
                              (⊢-cast (sym eqZ) dz) (⊢-cast (sym eqS) ds)
                              (⊢var here)))
    where
      eqAt : subTy (single (var vz)) (irrT (vsθ θ) _ _ (w n₁) (var vz))
           ≡ irrT θ _ _ n₁ (var vz)
      eqAt = trans (irrT-sub (vsθ θ) θ (λ v → refl) _ _ (w n₁) (var vz))
                   (cong (λ u → irrT θ _ _ u (var vz)) (wk-single {v = var vz} n₁))

      eqZ : subTy (single nzero) (irrT (vsθ θ) _ _ (w n₁) (var vz))
          ≡ irrT θ _ _ n₁ nzero
      eqZ = trans (irrT-sub (vsθ θ) θ (λ v → refl) _ _ (w n₁) (var vz))
                  (cong (λ u → irrT θ _ _ u nzero) (wk-single {v = nzero} n₁))

      eqS : subTy nrs (irrT (vsθ θ) _ _ (w n₁) (var vz))
          ≡ irrT (vsθ (vsθ θ)) _ _ (w (w n₁)) (nsuc (var (vs vz)))
      eqS = trans (irrT-sub (vsθ θ) (vsθ (vsθ θ)) (λ v → refl) _ _ (w n₁) (var vz))
                  (cong (λ u → irrT (vsθ (vsθ θ)) _ _ u (nsuc (var (vs vz))))
                        (nrs-w n₁))

  ------------------------------------------------------------------------
  -- THE FOUR LEAVES
  ------------------------------------------------------------------------

  irr-zz : StepExt Δ A cM m stp →
           {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ) →
           {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A →
           Prv Θ (irrT θ x y nzero nzero)
  irr-zz ext {θ = θ} h {x = x} {y = y} dx dy =
    irrIntro h ⊢nzero ⊢nzero
      (aux-irr ext (⊢irr-θ₃ h) ⊢irr-a d₁ d₂
               (auxAt-step-z (θ₃ θ) x (var (vs (vs vz))) nzero (var (vs vz))
                             done (λ _ → done))
               (auxAt-step-z (θ₃ θ) y (var (vs (vs vz))) nzero (var vz)
                             done (λ _ → done))
               (pwZ (⊢irr-θ₃ h) ⊢irr-a ⊢irr-c₁ d₁ d₂))
    where
      d₁ = ⊢ihZ-atR (⊢irr-θ₃ h) dx ⊢irr-a ⊢irr-c₁
      d₂ = ⊢ihZ-atR (⊢irr-θ₃ h) dy ⊢irr-a ⊢irr-c₂

  irr-zs : StepExt Δ A cM m stp →
           {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ) →
           {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A →
           {k : RTm ⌊ Θ ⌋} → Θ ⊢ k ∷ Nat →
           Prv Θ (irrT θ x y nzero (nsuc k))
  irr-zs ext {θ = θ} h {x = x} {y = y} dx dy {k = k} dk =
    irrIntro h ⊢nzero (⊢nsuc dk)
      (aux-irr ext (⊢irr-θ₃ h) ⊢irr-a d₁ d₂
               (auxAt-step-z (θ₃ θ) x (var (vs (vs vz))) nzero (var (vs vz))
                             done (λ _ → done))
               (auxAt-step-sF (θ₃ θ) y (var (vs (vs vz))) (nsuc (w (w (w k))))
                              (w (w (w k))) (var vz) done (λ _ → done))
               (pwZ (⊢irr-θ₃ h) ⊢irr-a ⊢irr-c₁ d₁ d₂))
    where
      d₁ = ⊢ihZ-atR (⊢irr-θ₃ h) dx ⊢irr-a ⊢irr-c₁
      d₂ = ⊢ihS-atR (⊢irr-θ₃ h) dy (⊢wk (⊢wk (⊢wk dk))) ⊢irr-a ⊢irr-c₂

  irr-sz : StepExt Δ A cM m stp →
           {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ) →
           {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A →
           {k : RTm ⌊ Θ ⌋} → Θ ⊢ k ∷ Nat →
           Prv Θ (irrT θ x y (nsuc k) nzero)
  irr-sz ext {θ = θ} h {x = x} {y = y} dx dy {k = k} dk =
    irrIntro h (⊢nsuc dk) ⊢nzero
      (aux-irr ext (⊢irr-θ₃ h) ⊢irr-a d₁ d₂
               (auxAt-step-sF (θ₃ θ) x (var (vs (vs vz))) (nsuc (w (w (w k))))
                              (w (w (w k))) (var (vs vz)) done (λ _ → done))
               (auxAt-step-z (θ₃ θ) y (var (vs (vs vz))) nzero (var vz)
                             done (λ _ → done))
               (pwZ (⊢irr-θ₃ h) ⊢irr-a ⊢irr-c₂ d₁ d₂))
    where
      d₁ = ⊢ihS-atR (⊢irr-θ₃ h) dx (⊢wk (⊢wk (⊢wk dk))) ⊢irr-a ⊢irr-c₁
      d₂ = ⊢ihZ-atR (⊢irr-θ₃ h) dy ⊢irr-a ⊢irr-c₂

  -- ★ the IH, weakened one binder — `irrB`'s own `Π Nat` rides through by
  --   `irrT-ren`, which is the only place the motive's naturality is used
  irrΠ-ren : {Γ' : Cx} (θ : Ren ⌊ Δ ⌋ Γ') (x y : RTm ⌊ Δ ⌋) (k : RTm Γ') →
             renTy vs (Π Nat (irrT (vsθ θ) x y (w k) (var vz)))
           ≡ Π Nat (irrT (vsθ (vsθ θ)) x y (w (w k)) (var vz))
  irrΠ-ren θ x y k =
    cong (Π Nat)
         (trans (irrT-ren (vsθ θ) (vsθ (vsθ θ)) (λ v → refl) x y (w k) (var vz))
                (cong (λ u → irrT (vsθ (vsθ θ)) x y u (var vz)) (ren-w k)))

  ihW : {Θ : Ctx} {B : RTy ⌊ Θ ⌋} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {x y : RTm ⌊ Δ ⌋}
        {k t : RTm ⌊ Θ ⌋} →
        Θ ⊢ t ∷ Π Nat (irrT (vsθ θ) x y (w k) (var vz)) →
        (Θ ▹ B) ⊢ w t ∷ Π Nat (irrT (vsθ (vsθ θ)) x y (w (w k)) (var vz))
  ihW {θ = θ} {x = x} {y = y} {k = k} d = ⊢-cast (irrΠ-ren θ x y k) (⊢wk d)

  -- ★★★★ THE (S,S) LEAF — the only one that uses the induction hypothesis,
  --      and the only one that needs the recursive call's CERTIFICATE typed.
  irr-ss : StepExt Δ A cM m stp →
           {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ) →
           {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A →
           {k₁ k₂ t : RTm ⌊ Θ ⌋} → Θ ⊢ k₁ ∷ Nat → Θ ⊢ k₂ ∷ Nat →
           Θ ⊢ t ∷ Π Nat (irrT (vsθ θ) x y (w k₁) (var vz)) →
           Prv Θ (irrT θ x y (nsuc k₁) (nsuc k₂))
  irr-ss ext {Θ = Θ} {θ = θ} h {x = x} {y = y} dx dy {k₁ = k₁} {k₂ = k₂} {t = t} dk₁ dk₂ dih =
    irrIntro h (⊢nsuc dk₁) (⊢nsuc dk₂)
      (aux-irr ext ρ⊢ ⊢irr-a d₁ d₂
               (auxAt-step-sF ρ x A3 (nsuc K₁) K₁ C₁ done (λ _ → done))
               (auxAt-step-sF ρ y A3 (nsuc K₂) K₂ C₂ done (λ _ → done))
               pw)
    where
      ρ  = θ₃ θ
      ρ⊢ = ⊢irr-θ₃ h {n₁ = nsuc k₁} {n₂ = nsuc k₂}
      A3 = var (vs (vs vz))
      C₁ = var (vs vz)
      C₂ = var vz
      K₁ = w (w (w k₁))
      K₂ = w (w (w k₂))

      dK₁ = ⊢wk (⊢wk (⊢wk dk₁))
      dK₂ = ⊢wk (⊢wk (⊢wk dk₂))
      d₁ = ⊢ihS-atR ρ⊢ dx dK₁ ⊢irr-a ⊢irr-c₁
      d₂ = ⊢ihS-atR ρ⊢ dy dK₂ ⊢irr-a ⊢irr-c₂

      dmρ  = ren-lemma dm (Ren⊢-ext ρ⊢)
      dμa  = ⊢[] dmρ (⊢irr-a {n₁ = nsuc k₁} {n₂ = nsuc k₂})

      -- the IH at the leaf's depth, then INSTANTIATED at the second bound
      dihΘ₃ : irrΘ θ (nsuc k₁) (nsuc k₂)
                ⊢ w (w (w t)) ∷ Π Nat (irrT (vsθ ρ) x y (w K₁) (var vz))
      dihΘ₃ = ihW (ihW (ihW dih))

      dihAt : irrΘ θ (nsuc k₁) (nsuc k₂)
                ⊢ app (w (w (w t))) K₂ ∷ irrT ρ x y K₁ K₂
      dihAt = ⊢-cast (trans (irrT-sub (vsθ ρ) ρ (λ v → refl) x y (w K₁) (var vz))
                            (cong (λ u → irrT ρ x y u K₂) (wk-single {v = K₂} K₁)))
                     (⊢app dihΘ₃ dK₂)

      -- ★★★★ THE ONLY LEAF WHOSE POINTWISE PREMISE HAS CONTENT — and, since
      --      2026-08-16, the only one that pays for `StepPW` being
      --      renaming-indexed.  ⚠ The extra cost is ONE rewrite: `ihS-atR-renʳ`
      --      moves the two IH arguments to `Θ'`, and after that `ih-appR`,
      --      `descS-atR` and `descS-peel` are instantiated FRESH at `ρ'` —
      --      they are already generic in the renaming, so none of them needs
      --      a naturality lemma of its own.  That is the whole saving.
      pw : StepPW Δ A cM m (irrΘ θ (nsuc k₁) (nsuc k₂)) ρ A3
                  (ihS-atR ρ x A3 K₁ C₁) (ihS-atR ρ y A3 K₂ C₂)
      pw {ϑ = ϑ} {ρ' = ρ'} hϑ br y' q dy' dq =
        prv-cast (Id-cong₃ refl (atArg (sym (ihS-atR-renʳ ρ ρ' br x A3 K₁ C₁)))
                                (atArg (sym (ihS-atR-renʳ ρ ρ' br y A3 K₂ C₂))))
          (idOfRed (ih-appR ρ' x A3' K₁' C₁' y' q)
                   (ih-appR ρ' y A3' K₂' C₂' y' q)
                   (irrElim dihAt' y' (descS-atR ρ' x A3' K₁' C₁' y' q)
                                      (descS-atR ρ' y A3' K₂' C₂' y' q)
                            dy' (dD x K₁' C₁' dK₁' dC₁') (dD y K₂' C₂' dK₂' dC₂')))
        where
          -- ⚠ the rewrite lands on the IH ARGUMENT, but `Id-cong₃` wants it
          --   on the whole application — one `cong`, easy to forget.
          atArg : {u u' : RTm ⌊ _ ⌋} → u ≡ u' →
                  app (app u y') q ≡ app (app u' y') q
          atArg e = cong (λ z → app (app z y') q) e

          h'  = Ren⊢-comp ρ⊢ hϑ br
          A3' = renTm ϑ A3
          K₁' = renTm ϑ K₁
          K₂' = renTm ϑ K₂
          C₁' = renTm ϑ C₁
          C₂' = renTm ϑ C₂

          -- the one naturality: the premise states the bound as
          -- `renTm ϑ (μ A3)`, every rule below wants `μ (renTm ϑ A3)`
          μeq  = sub1-ren ρ ρ' br A3 m
          dmρ' = ren-lemma dm (Ren⊢-ext h')
          dA3' = ⊢-cast (renrenTy br A) (ren-lemma ⊢irr-a hϑ)
          dμa' = ⊢[] dmρ' dA3'
          dq'  = ⊢-cast (cong (λ u → Hom Nat (nsuc (subTm (single y')
                                                          (renTm (extR ρ') m))) u)
                              μeq)
                        dq

          dK₁' = ren-lemma dK₁ hϑ
          dK₂' = ren-lemma dK₂ hϑ
          dC₁' = ⊢-cast (cong (λ u → Hom Nat u (nsuc K₁')) μeq)
                        (ren-lemma (⊢irr-c₁ {n₁ = nsuc k₁} {n₂ = nsuc k₂}) hϑ)
          dC₂' = ⊢-cast (cong (λ u → Hom Nat u (nsuc K₂')) μeq)
                        (ren-lemma (⊢irr-c₂ {n₁ = nsuc k₁} {n₂ = nsuc k₂}) hϑ)

          dihAt' = ⊢-cast (irrT-ren ρ ρ' br x y K₁ K₂) (ren-lemma dihAt hϑ)

          -- ★ the recursive call's certificate: `descS-peel` says WHAT it is,
          --   and `⊢strong-step` then types it from the two hypotheses the
          --   pointwise premise already hands over — `q` (μ y' < μ a) and the
          --   branch's own certificate (μ a ≤ suc K).
          dD : (z : RTm ⌊ Δ ⌋) (K C : RTm ⌊ _ ⌋) →
               _ ⊢ K ∷ Nat →
               _ ⊢ C ∷ Hom Nat (subTm (single A3') (renTm (extR ρ') m)) (nsuc K) →
               _ ⊢ descS-atR ρ' z A3' K C y' q
                 ∷ Hom Nat (subTm (single y') (renTm (extR ρ') m)) K
          dD z K C dK dC =
            subst (λ u → _ ⊢ u
                           ∷ Hom Nat (subTm (single y') (renTm (extR ρ') m)) K)
                  (sym (descS-peel ρ' z A3' K C y' q))
                  (⊢strong-step (⊢[] dmρ' dy') dμa' dK dq' dC)

  ------------------------------------------------------------------------
  -- ★★★★★ …AND THE INDUCTION ITSELF — CERTIFICATE- AND BOUND-IRRELEVANCE,
  --       INTERNALLY.
  --
  --     ⊢ (n₂ : Nat) (a : A) (c₁ : μ a ≤ n) (c₂ : μ a ≤ n₂) →
  --         aux x n a c₁ ≡ aux y n₂ a c₂
  --
  -- ⚠ CONDITIONAL on `StepExt`, which is the CALLER's to discharge — see the
  --   header.  Nothing in this module supplies one, so this is machinery
  --   with a real statement, not yet evidence that any particular function
  --   has the property.
  ------------------------------------------------------------------------

  irr-ind : StepExt Δ A cM m stp →
            {x y : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ y ∷ A →
            {n : RTm ⌊ Δ ⌋} → Δ ⊢ n ∷ Nat →
            Prv Δ (Π Nat (irrT vs x y (w n) (var vz)))
  irr-ind ext {x = x} {y = y} dx dy {n = n} dn =
    prv (natrec (lam (prvTm ZP)) (lam (prvTm SP)) n)
        (⊢-cast (peelAt n)
                (⊢natrec (⊢irrB dx dy)
                         (⊢-cast (sym (peelAt nzero)) (⊢lam ty-Nat (prvOk ZP)))
                         (⊢-cast (sym peelS) (⊢lam ty-Nat (prvOk SP)))
                         dn))
    where
      peelAt : (u : RTm ⌊ Δ ⌋) →
               subTy (single u) (irrB x y) ≡ Π Nat (irrT vs x y (w u) (var vz))
      peelAt u = cong (Π Nat)
                      (irrT-sub (λ v → vs (vs v)) vs (λ v → refl) x y
                                (var (vs vz)) (var vz))

      peelS : subTy nrs (irrB x y)
            ≡ Π Nat (irrT (λ v → vs (vs (vs v))) x y
                          (nsuc (var (vs (vs vz)))) (var vz))
      peelS = cong (Π Nat)
                   (irrT-sub (λ v → vs (vs v)) (λ v → vs (vs (vs v))) (λ v → refl)
                             x y (var (vs vz)) (var vz))

      -- n = 0: both inner cases are ex falso, from `c₁ : μ a ≤ 0`
      ZP : Prv (Δ ▹ Nat) (irrT vs x y nzero (var vz))
      ZP = irrSplit there dx dy ⊢nzero
                    (irr-zz ext there dx dy)
                    (irr-zs ext (wR (wR there)) dx dy (⊢var (there here)))

      -- n = suc k₁: the (S,0) case is ex falso from `c₂`, and (S,S) is the IH
      dIH : ((((Δ ▹ Nat) ▹ irrB x y) ▹ Nat) ▹ Nat)
              ▹ irrT (vsθ (λ v → vs (vs (vs v)))) x y
                     (w (nsuc (var (vs (vs vz))))) (var vz)
              ⊢ var (vs (vs (vs vz)))
              ∷ Π Nat (irrT (vsθ (λ v → vs (vs (vs (vs (vs v)))))) x y
                            (w (var (vs (vs (vs (vs vz)))))) (var vz))
      dIH =
        ⊢-cast (trans (cong (λ S → renTy vs (renTy vs (renTy vs S)))
                            (irrΠ-ren vs x y (var vz)))
               (trans (cong (λ S → renTy vs (renTy vs S))
                            (irrΠ-ren (vsθ vs) x y (w (var vz))))
               (trans (cong (renTy vs)
                            (irrΠ-ren (vsθ (vsθ vs)) x y (w (w (var vz)))))
                      (irrΠ-ren (vsθ (vsθ (vsθ vs))) x y (w (w (w (var vz))))))))
               (⊢var (there (there (there here))))

      SP : Prv (((Δ ▹ Nat) ▹ irrB x y) ▹ Nat)
               (irrT (λ v → vs (vs (vs v))) x y
                     (nsuc (var (vs (vs vz)))) (var vz))
      SP = irrSplit (wR (wR there)) dx dy (⊢nsuc (⊢var (there (there here))))
                    (irr-sz ext (wR (wR there)) dx dy
                            (⊢var (there (there here))))
                    (irr-ss ext (wR (wR (wR (wR there)))) dx dy
                            (⊢var (there (there (there (there here)))))
                            (⊢var (there here))
                            dIH)

  ------------------------------------------------------------------------
  -- ★★★★★ PIECE 9 — THE INTERNAL UNFOLDING, `amrec-unfold-Id`.
  --
  --     ⊢ app amrecTm x  ≡  app (app stp x) ⟨ih⟩     : El (P x)
  --
  -- ⚠⚠ AND IT DOES NOT NEED `jsub` AT ALL.  The plan this route was opened
  --   with was "TRANSPORT FIRST, THEN REDUCE": move the auxiliary's bound
  --   off the stuck `μ x` along an `Id`, so `amrec-unfold-s` can fire.  That
  --   forced the family to bind the certificate internally (`⌜Π⌝` over
  --   `⌜Hom⌝`), which made the transport's source obligation certificate
  --   irrelevance — and irrelevance is what pieces 6–8 built.
  --
  -- ★ But the theorem those pieces actually produce is BOUND irrelevance as
  --   well: `aux x n₁ a c₁ ≡ aux y n₂ a c₂` for two INDEPENDENT bounds.  So
  --   the bound can be moved DIRECTLY, and `jsub` — with its ban on the
  --   family mentioning the proof, and its demand that the family typecheck
  --   at an arbitrary `v` — never enters.  ⚠ Do not re-attempt the
  --   `⌜Π⌝`-family transport; it is not on the path any more.
  --
  -- ★★ AND THE PREMISE CAME OUT WEAKER THAN PLANNED.  The plan needed
  --   `Id Nat (μ x) (nsuc k)`; what is needed is only the INEQUALITY
  --   `μ x ≤ nsuc k`, because the auxiliary at ANY bound above the measure
  --   computes the same answer.  An identity would give the inequality; the
  --   converse is false, so this is strictly more usable.
  ------------------------------------------------------------------------

  -- the identity ambient renaming, and what it does to the three data
  idR : Ren ⌊ Δ ⌋ ⌊ Δ ⌋
  idR v = v

  ------------------------------------------------------------------------
  -- ★★★★ PIECE 11 — THE ELIMINATION, PERFORMED AT AN ABSTRACT STEP.
  --
  -- ⚠ WHY THIS BELONGS HERE AND NOT AT THE CALL SITE.  `irr-ind` returns a
  --   `Prv` of a `Π Nat …`; every caller then has to `⊢app` it and cancel
  --   the resulting `subTy` against `irrT`.  Written at the CALL SITE that
  --   application is elaborated at a CONCRETE step term — and `irrT`
  --   mentions `auxAt`, which carries the step, so the types involved are
  --   enormous.  Written HERE it is elaborated ONCE, with `stp` and `ext`
  --   still variables.
  --
  -- ★ MEASURED, in `…ExamplesAbsProbe` (marginal cost over module overhead,
  --   on the `irrSplit` rung):
  --
  --     assembly written at a CONCRETE step            9.9s
  --     assembly written ABSTRACT, then instantiated   1.7s   ~5.8×
  --
  --   ⚠ This is NOT the `opaque` family — nothing is asked to refrain from
  --   unfolding.  The same elaboration still happens in full; it happens
  --   ONCE, generically, instead of at every concrete use.  Nine remedies
  --   were tried before this one and every other measured NULL; do not
  --   "simplify" this back to the call site.
  ------------------------------------------------------------------------

  -- ⚠⚠ AND IT MUST RETURN `Prv`, NOT A RAW `⊢` JUDGEMENT.  The obvious
  --   signature
  --
  --     Δ ⊢ app (prvTm (irr-ind ext dx dy dk)) n₂ ∷ irrT idR x y k n₂
  --
  --   mentions `prvTm (irr-ind …)`, so merely STATING it forces the whole
  --   assembly's witness — `natrec (lam (prvTm ZP)) (lam (prvTm SP)) n`,
  --   whose `ZP`/`SP` force their own leaves in turn.  MEASURED: that form
  --   kills `…LibAmrec` outright (EXIT 143 twice, 9m26s and 7m34s
  --   uncontended, 0 errors) where it is ~57s green.  `Prv Γ T` is indexed
  --   ONLY by `T` — the witness is hidden in the constructor — which is
  --   exactly what the rest of this module returns.
  irr-at : (ext : StepExt Δ A cM m stp)
           {x y k n₂ : RTm ⌊ Δ ⌋}
           (dx : Δ ⊢ x ∷ A) (dy : Δ ⊢ y ∷ A)
           (dk : Δ ⊢ k ∷ Nat) (dn₂ : Δ ⊢ n₂ ∷ Nat) →
           Prv Δ (irrT idR x y k n₂)
  irr-at ext {x = x} {y = y} {k = k} {n₂ = n₂} dx dy dk dn₂ =
    prv _ (⊢-cast (trans (irrT-sub vs idR (λ v → refl) x y (w k) (var vz))
                         (cong (λ u → irrT idR x y u n₂) (wk-single {v = n₂} k)))
                  (⊢app (prvOk (irr-ind ext dx dy dk)) dn₂))

  extR-idR : ∀ v → extR idR v ≡ v
  extR-idR vz     = refl
  extR-idR (vs v) = refl

  extR²-idR : ∀ v → extR (extR idR) v ≡ v
  extR²-idR vz          = refl
  extR²-idR (vs vz)     = refl
  extR²-idR (vs (vs v)) = refl

  auxAt-id : (z n : RTm ⌊ Δ ⌋) → auxAt idR z n ≡ auxIH z n
  auxAt-id z n =
    cong₂ (λ u s → natrec u s n)
          (renTm-idR (λ v → refl) (auxZ z))
          (renTm-idR extR²-idR (auxS z))

  ------------------------------------------------------------------------
  -- ★ TYPING THE RECURSIVE CALL'S CERTIFICATE, un-renamed.
  --
  -- `descS-peel` says what the certificate IS, but only for the RENAMED
  -- form `descS-atR`.  At the identity renaming the two coincide — the
  -- extra `renTm (extR⁶ idR)` layer collapses and `auxAt idR` is `auxIH` —
  -- so one bridge gives the un-renamed twin, and `⊢strong-step` types it.
  --
  -- ⚠ Same shape as `irr-ss`'s `dD`: a certificate that exists only as a
  --   REDUCT can never be typed by subject reduction, because `subTm` does
  --   not invert.  Say what it is first.
  --
  -- ⚠⚠ THESE LIVED IN `…ExamplesGcdEqs` UNTIL 2026-08-20, stated at gcd's
  --   `msr`.  Nothing about them is gcd-specific — they speak only about
  --   `descS-at`/`descS-atR`/`auxAt`, which are this module's own.  What
  --   disguised it is that a general lemma STATED AT AN INSTANCE looks
  --   instance-specific.
  --
  -- ⚠⚠⚠ AND THE MOVE WAS NOT A RENAME.  At gcd's CLOSED `msr`,
  --   `renTm (extR idR) msr` reduces to `msr` DEFINITIONALLY, so the
  --   original proof never mentioned it.  At an abstract `m` it is only
  --   PROPOSITIONAL — the proof silently depended on the measure being
  --   closed.  `mId` below is that dependency, made explicit.
  ------------------------------------------------------------------------

  extR-id : {Γ : Cx} {ρ : Ren Γ Γ} → (∀ v → ρ v ≡ v) → (∀ v → extR ρ v ≡ v)
  extR-id h vz     = refl
  extR-id h (vs v) = cong vs (h v)

  extR⁶-id : ∀ v → extR (extR (extR (extR (extR (extR idR))))) v ≡ v
  extR⁶-id = extR-id (extR-id (extR-id (extR-id (extR-id (extR-id (λ v → refl))))))

  descS-at-idR : (x a k p y q : RTm ⌊ Δ ⌋) →
                 descS-atR idR x a k p y q ≡ descS-at x a k p y q
  descS-at-idR x a k p y q =
    cong₂ (λ u t → subTm (single q)
                     (subTm (extS (single y))
                       (subTm (extS (extS (single p)))
                         (subTm (extS (extS (extS (single a))))
                           (subTm (extS (extS (extS (extS (single u)))))
                             (subTm (extS (extS (extS (extS (extS (single k))))))
                                    t))))))
          (auxAt-id x k)
          (renTm-idR extR⁶-id
                     (subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                            descS))

  -- ★ the dependency the gcd version hid: at an abstract measure the
  --   identity renaming does NOT vanish definitionally.
  mId : renTm (extR idR) m ≡ m
  mId = renTm-idR (extR-id (λ v → refl)) m

  ⊢descS-at : {x a k p y q : RTm ⌊ Δ ⌋} →
              Δ ⊢ subTm (single y) m ∷ Nat →
              Δ ⊢ subTm (single a) m ∷ Nat → Δ ⊢ k ∷ Nat →
              Δ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) m)) (subTm (single a) m) →
              Δ ⊢ p ∷ Hom Nat (subTm (single a) m) (nsuc k) →
              Δ ⊢ descS-at x a k p y q ∷ Hom Nat (subTm (single y) m) k
  ⊢descS-at {x = x} {a} {k} {p} {y} {q} dμy dμa dk dq dp =
    subst (λ u → Δ ⊢ u ∷ Hom Nat (subTm (single y) m) k)
          (trans (sym peelId) (descS-at-idR x a k p y q))
          (⊢strong-step dμy dμa dk dq dp)
    where
      peelId : descS-atR idR x a k p y q
             ≡ ordtr (nsuc (subTm (single y) m)) (subTm (single a) m)
                     (nsuc k) q p
      peelId =
        trans (descS-peel idR x a k p y q)
              (cong₂ (λ u v → ordtr (nsuc (subTm (single y) u))
                                    (subTm (single a) v) (nsuc k) q p)
                     mId mId)

  amrec-unfold-Id :
    StepExt Δ A cM m stp →
    {x k p : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ k ∷ Nat →
    Δ ⊢ p ∷ Hom Nat (subTm (single x) m) (nsuc k) →
    Prv Δ (Id (El (subTm (single x) cM))
              (app amrecTm x)
              (app (app stp x) (ihS-atP x x k p)))
  amrec-unfold-Id ext {x = x} {k = k} {p = p} dx dk dp =
    idToRed done
            (aux-step-sF {P = λ ih → app (app stp x) ih} x x (nsuc k) k p done
                         (λ _ → done))
            (idOfRed (amrec-β x) done
                     (prv-cast idEq (irrElim dAt x (reflTm μx) p dA' dc₁ dc₂)))
    where
      μx  = subTm (single x) m
      dμx = ⊢[] dm dx

      -- ⚠ `mId` was defined HERE, locally.  It is now at module level,
      --   because `⊢descS-at` needs the same fact — the dependency on the
      --   measure not being closed was already known, just not shared.

      -- the induction, instantiated at the SECOND bound `nsuc k`
      dAt : Δ ⊢ app (prvTm (irr-ind ext dx dx dμx)) (nsuc k)
              ∷ irrT idR x x μx (nsuc k)
      dAt = ⊢-cast (trans (irrT-sub vs idR (λ v → refl) x x (w μx) (var vz))
                          (cong (λ u → irrT idR x x u (nsuc k))
                                (wk-single {v = nsuc k} μx)))
                   (⊢app (prvOk (irr-ind ext dx dx dμx)) (⊢nsuc dk))

      dA' : Δ ⊢ x ∷ renTy idR A
      dA' = ⊢-cast (sym (renTy-idR (λ v → refl) A)) dx

      dc₁ : Δ ⊢ reflTm μx ∷ Hom Nat (subTm (single x) (renTm (extR idR) m)) μx
      dc₁ = ⊢-cast (cong (λ z → Hom Nat (subTm (single x) z) μx) (sym mId))
                   (⊢le-refl dμx)

      dc₂ : Δ ⊢ p ∷ Hom Nat (subTm (single x) (renTm (extR idR) m)) (nsuc k)
      dc₂ = ⊢-cast (cong (λ z → Hom Nat (subTm (single x) z) (nsuc k)) (sym mId))
                   dp

      idEq : Id (El (subTm (single x) (renTm (extR idR) cM)))
                (app (app (auxAt idR x μx) x) (reflTm μx))
                (app (app (auxAt idR x (nsuc k)) x) p)
           ≡ Id (El (subTm (single x) cM))
                (app (app (auxIH x μx) x) (reflTm μx))
                (app (app (auxIH x (nsuc k)) x) p)
      idEq = cong₃ (λ c e₁ e₂ → Id (El c) e₁ e₂)
                   (cong (subTm (single x)) (renTm-idR extR-idR cM))
                   (cong (λ z → app (app z x) (reflTm μx)) (auxAt-id x μx))
                   (cong (λ z → app (app z x) p) (auxAt-id x (nsuc k)))

  -- ★★ NON-VACUITY, and it is the thing to check before believing any of
  --    this (Green ≠ meaningful).  `amrec-unfold-Id`'s premise is NOT a
  --    hidden identity: whenever the measure REDUCES to a successor it is
  --    discharged by `reflTm` and one conversion.  So the Id-form subsumes
  --    the `⟶*`-form `amrec-step-s`, and the premise is inhabited at exactly
  --    the arguments the library already reduces at.
  --
  -- ⚠ What is STILL undischarged is `StepExt` — the caller's half.  Nothing
  --   in this tree supplies one, so `amrec-unfold-Id` is real machinery with
  --   a real statement and is NOT yet evidence that any particular function
  --   unfolds internally.
  ⊢le-of-red : {x k : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → subTm (single x) m ⟶* nsuc k →
               Δ ⊢ reflTm (subTm (single x) m)
                 ∷ Hom Nat (subTm (single x) m) (nsuc k)
  ⊢le-of-red dx r = ⊢conv (⊢le-refl (⊢[] dm dx)) (red→≅ᵀ (⟶ᵀ*-Homʳ r))

  amrec-unfold-Id-red :
    StepExt Δ A cM m stp →
    {x k : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ k ∷ Nat →
    subTm (single x) m ⟶* nsuc k →
    Prv Δ (Id (El (subTm (single x) cM))
              (app amrecTm x)
              (app (app stp x)
                   (ihS-atP x x k (reflTm (subTm (single x) m)))))
  amrec-unfold-Id-red ext dx dk r = amrec-unfold-Id ext dx dk (⊢le-of-red dx r)

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
