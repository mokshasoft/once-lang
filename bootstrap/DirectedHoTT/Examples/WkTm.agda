------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ OBJECT-LEVEL WEAKENING FOR A SYNTAX.
--
--     wkTmTm : Tm n → Tm (suc n)
--
-- One rung up from `Examples/WkFin`: `Tm` HAS A BINDER, which `Fin` does
-- not, and this is the shape `_∋_∷_`'s `renTy vs A` actually needs.
--
-- ★★ AND IT NEEDS NO KRIPKE MOTIVE.  Weakening AT THE OUTSIDE shifts the
--   index uniformly, so `M(i,t) = Tm (suc ⟨i⟩)` still serves: under
--   `lam` the body is at `suc ⟨i⟩` and its IH is the SAME function one
--   index higher.  ⇒ what forces a motive that is a FUNCTION OF THE
--   RENAMING is `subTy (single u)` (⊢app's index), not binders as such.
--   That distinction is the useful output of this file.
--
-- ⚠ AND `TmD` IS FORD-FREE — under D074 its constructors' targets are
--   the fibre's, where `Fin`'s `fzero`/`fsuc` ford theirs.  So no
--   method here needs the `⊢jsub` transport `WkFin` needed; the
--   transport is reached only THROUGH `wkFinTm`, in the `var` case.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.WkTm where
open import normalizer.Syntax.Types using ( _≡_; cong; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-con; ⟶*-pairˡ; ⟶*-pairʳ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; conₗ; methₗ; selF; selF-β; nth-z; nth-s; MethK; PerK; []ₘ; _∷ₘ_; ⊢methₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Examples.Scoped
  using ( TmTs; TmD; ⊢TmD; TmOK; Tm; varT; lamT; appT; varOK; lamOK; appOK
        ; tvar; tlam; tapp; ⊢tvar; ⊢tlam; ⊢tapp; ⊢isuc; fz; ffz; idTm; FinD )
open import DirectedHoTT.Examples.WkFin using ( wkFinTm; ⊢wkFinTm; fromFin; wk-fz )

------------------------------------------------------------------------
-- 1. THE MOTIVE — the same index shift as `WkFin`'s.
------------------------------------------------------------------------

wkTmMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkTmMot = Tm (nsuc (var (vs vz)))

⊢wkTmMot : {Γ : Ctx} → ((Γ ▹ El ⌜Nat⌝) ▹ Tm (var vz)) ⊢ty wkTmMot
⊢wkTmMot = ty-IMu ⊢⌜Nat⌝ ⊢TmD (⊢isuc (⊢var (there here)))

------------------------------------------------------------------------
-- 2. THE THREE METHODS, against the hypotheses' and payload's normal
--    forms.  `v₂` the index, `v₁` the payload, `v₀` the hypotheses.
------------------------------------------------------------------------

v₀ v₁ v₂ : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙)
v₀ = var vz
v₁ = var (vs vz)
v₂ = var (vs (vs vz))

-- var : Fin n → Tm n   ↦   var (wkFin k) : Tm (suc n)
wkVar wkLam wkApp : {Γ : Cx} → RTm Γ
wkVar = lam (lam (lam (tvar (wkFinTm v₂ (fst v₁)))))
-- lam : Tm (suc n) → Tm n   ↦   lam ⟨ih⟩ : Tm (suc n)
wkLam = lam (lam (lam (tlam (fst v₀))))
-- app : Tm n → Tm n → Tm n   ↦   app ⟨ih₁⟩ ⟨ih₂⟩ : Tm (suc n)
wkApp = lam (lam (lam (tapp (fst v₀) (fst (snd v₀)))))

WkMs : {Γ : Cx} → Cons Γ 3
WkMs = wkVar ∷ wkLam ∷ wkApp ∷ []

module _ {Γ : Ctx} where
  private
    HV = HypCtx Γ ⌜Nat⌝ TmD wkTmMot varT
    idx : {T : Tel (⌊ Γ ⌋ ∙)} → HypCtx Γ ⌜Nat⌝ TmD wkTmMot T ⊢ v₂ ∷ El ⌜Nat⌝
    idx = ⊢var (there (there here))

  ⊢kV : HV ⊢ fst v₁ ∷ El (⌜IMu⌝ ⌜Nat⌝ FinD v₂)
  ⊢kV = ⊢fst (⊢payHyp {I = ⌜Nat⌝} {D = TmD} {M = wkTmMot} {T = varT})

  ⊢wkVar : Γ ⊢ wkVar ∷ MethK ⌜Nat⌝ TmD wkTmMot ⌜ varT ⌝ᵗ zero
  ⊢wkVar = ⊢methT {T = varT} {s = conₗ zero (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢wkTmMot varOK
             (⊢tvar (⊢isuc idx) (⊢wkFinTm idx (fromFin ⊢kV)))

  ⊢wkLam : Γ ⊢ wkLam ∷ MethK ⌜Nat⌝ TmD wkTmMot ⌜ lamT ⌝ᵗ (suc zero)
  ⊢wkLam = ⊢methT {T = lamT} {s = conₗ (suc zero) (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢wkTmMot lamOK
             (⊢tlam (⊢isuc idx) (⊢fst (⊢var here)))

  ⊢wkApp : Γ ⊢ wkApp ∷ MethK ⌜Nat⌝ TmD wkTmMot ⌜ appT ⌝ᵗ (suc (suc zero))
  ⊢wkApp = ⊢methT {T = appT} {s = conₗ (suc (suc zero)) (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢wkTmMot appOK
             (⊢tapp (⊢isuc idx) (⊢fst (⊢var here)) (⊢fst (⊢snd (⊢var here))))

  perWk : PerK Γ ⌜Nat⌝ TmD wkTmMot (selF ⌜ TmTs ⌝ₛ) zero WkMs
  perWk = (selF-β {Cs = ⌜ TmTs ⌝ₛ} nth-z , ⊢wkVar)
       ∷ₘ ((selF-β {Cs = ⌜ TmTs ⌝ₛ} (nth-s nth-z) , ⊢wkLam)
       ∷ₘ ((selF-β {Cs = ⌜ TmTs ⌝ₛ} (nth-s (nth-s nth-z)) , ⊢wkApp) ∷ₘ []ₘ))

------------------------------------------------------------------------
-- 3. ★★★ OBJECT-LEVEL WEAKENING FOR THE SYNTAX: `Tm n → Tm (suc n)`.
------------------------------------------------------------------------

wkTmTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTmTm n t = ielim TmD n (methₗ WkMs) t

⊢wkTmTm : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ wkTmTm n t ∷ Tm (nsuc n)
⊢wkTmTm {n = n} dn dt =
  ⊢-cast (cong (λ z → Tm (nsuc z)) (wk-single n))
    (⊢ielim ⊢⌜Nat⌝ ⊢TmD ⊢wkTmMot (⊢methₗ ⊢⌜Nat⌝ (allD (⊢wk ⊢⌜Nat⌝) TmOK) ⊢wkTmMot perWk) dn dt)

------------------------------------------------------------------------
-- 4. ★★ …AND IT COMPUTES, through the binder AND into `Fin`:
--    `wk (λx. x) ⟶* λx. x` one level up — the bound variable `fz` at
--    depth 1 becomes `fz` at depth 2 (`WkFin.wk-fz`).
------------------------------------------------------------------------

-- the first field of a constructor (`conₗ k (pair a …)`)
⟶*-arg₁ : {Γ : Cx} {k : ℕ} {a a' r : RTm Γ} → a ⟶* a' → conₗ k (pair a r) ⟶* conₗ k (pair a' r)
⟶*-arg₁ s = ⟶*-con (⟶*-pairʳ (⟶*-pairˡ s))

wk-var : {Γ : Cx} → wkTmTm {Γ} (nsuc nzero) (tvar fz) ⟶* tvar (ffz (nsuc nzero))
wk-var =
  ⟶*-trans (ιT {Cs = ⌜ TmTs ⌝ₛ} {ms = WkMs} {T = varT} (nth-⌜⌝ {Ts = TmTs} nthᵗ-z) nth-z)
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _)
    (step (ξ-con (ξ-pairʳ (ξ-pairˡ (ξ-ielimᵗ (βfst _ _)))))
      (⟶*-arg₁ wk-fz)))))

wk-id : {Γ : Cx} → wkTmTm {Γ} nzero idTm ⟶* tlam (tvar (ffz (nsuc nzero)))
wk-id =
  ⟶*-trans (ιT {Cs = ⌜ TmTs ⌝ₛ} {ms = WkMs} {T = lamT} (nth-⌜⌝ {Ts = TmTs} (nthᵗ-s nthᵗ-z)) (nth-s nth-z))
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _)
    (step (ξ-con (ξ-pairʳ (ξ-pairˡ (βfst _ _))))
    (step (ξ-con (ξ-pairʳ (ξ-pairˡ (ξ-ielimᵗ (βfst _ _)))))
      (⟶*-arg₁ wk-var))))))
