------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: A **KRIPKE MOTIVE**, i.e. one whose
-- Π DOMAIN MENTIONS THE INDEX.
--
-- `Examples/WkTm` showed weakening needs no such thing: weakening at the
-- outside shifts the index uniformly, so a plain `Tm (suc ⟨i⟩)` motive
-- serves.  What DOES force a function-of-the-index motive is
-- `subTy (single u)` — `⊢app`'s index, and hence the gate on `_⊢_∷_`:
--
--     subTm σ (lam t) = lam (subTm (extS σ) t)
--
-- the recursive call is at a DIFFERENT substitution, so the motive must
-- quantify over it, and its type mentions the index.
--
-- ★ THE SMALLEST HONEST TEST of that shape, needing no helper:
--
--     M(i, t) = (Fin ⟨i⟩ → Nat) → Nat
--
--   The domain mentions `⟨i⟩`, so under `lam` the IH's domain is
--   `Fin (suc ⟨i⟩) → Nat` — DIFFERENT from the method's own — and using
--   the IH means supplying a function at the shifted domain.  That is
--   precisely the manoeuvre `subTm`'s `lam` case performs.
--
-- ⚠ WHAT IT IS NOT.  This is a SHAPE test.  The function it computes
--   (sum the valuation over free occurrences, counting bound variables
--   as 0) is real but uninteresting; the point is the motive, and the
--   `lam` case supplying `λ_. 0` at the shifted domain rather than a
--   genuine extension is deliberate — an extension would need a `Fin`
--   eliminator and would test nothing further about the motive.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.KripkeIx where
open import normalizer.Syntax.Types using ( _≡_; cong; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; conₗ; methₗ; selF; selF-β; nth-z; nth-s; MethK; PerK; []ₘ; _∷ₘ_; ⊢methₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Examples.Scoped
  using ( TmTs; TmD; ⊢TmD; TmOK; Tm; varT; lamT; appT; varOK; lamOK; appOK
        ; FinD; ⊢FinD; FinI; ⊢isuc; tvar; fz )
open import DirectedHoTT.Examples.WkFin using ( fromFin )

------------------------------------------------------------------------
-- 1. ★★★ THE KRIPKE MOTIVE.  `(Fin ⟨i⟩ → Nat) → Nat`.
------------------------------------------------------------------------

kMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
kMot = Π (Π (FinI (var (vs vz))) Nat) Nat

⊢kMot : {Γ : Ctx} → ((Γ ▹ El ⌜Nat⌝) ▹ Tm (var vz)) ⊢ty kMot
⊢kMot = ty-Π (ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢var (there here))) ty-Nat) ty-Nat

------------------------------------------------------------------------
-- 2. THE THREE METHODS.  Method binders `i p h` (`v₂ v₁ v₀`), then the
--    motive's own valuation `ρ`.
------------------------------------------------------------------------

v₀ v₁ v₂ : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙)
v₀ = var vz
v₁ = var (vs vz)
v₂ = var (vs (vs vz))

-- var k : look the variable up in the valuation
kVar : {Γ : Cx} → RTm Γ
kVar = lam (lam (lam (lam (app (var vz) (fst (var (vs (vs vz))))))))

-- ★★ lam b : use the IH AT THE SHIFTED DOMAIN.  `h` expects a
--    `Fin (suc ⟨i⟩) → Nat` where `ρ` is a `Fin ⟨i⟩ → Nat`.
kLam : {Γ : Cx} → RTm Γ
kLam = lam (lam (lam (lam (app (fst (var (vs vz))) (lam nzero)))))

-- app f a : both IHs at the SAME domain, so `ρ` is passed twice
kApp : {Γ : Cx} → RTm Γ
kApp = lam (lam (lam (lam
         (plusTm (app (fst (var (vs vz))) (var vz))
                 (app (fst (snd (var (vs vz)))) (var vz))))))

KMs : {Γ : Cx} → Cons Γ 3
KMs = kVar ∷ kLam ∷ kApp ∷ []

module _ {Γ : Ctx} where
  private
    H : Tel (⌊ Γ ⌋ ∙) → Ctx
    H T = HypCtx Γ ⌜Nat⌝ TmD kMot T
    idx : {T : Tel (⌊ Γ ⌋ ∙)} → H T ⊢ v₂ ∷ El ⌜Nat⌝
    idx = ⊢var (there (there here))
    ρTy : {T : Tel (⌊ Γ ⌋ ∙)} → H T ⊢ty Π (FinI v₂) Nat
    ρTy = ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢FinD idx) ty-Nat

  ⊢kV : H varT ⊢ fst v₁ ∷ El (⌜IMu⌝ ⌜Nat⌝ FinD v₂)
  ⊢kV = ⊢fst (⊢payHyp {I = ⌜Nat⌝} {D = TmD} {M = kMot} {T = varT})

  ⊢kVar : Γ ⊢ kVar ∷ MethK ⌜Nat⌝ TmD kMot ⌜ varT ⌝ᵗ zero
  ⊢kVar = ⊢methT {T = varT} {s = conₗ zero (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢kMot varOK
            (⊢lam ρTy (⊢app (⊢var here) (fromFin (⊢wk ⊢kV))))

  ⊢kLam : Γ ⊢ kLam ∷ MethK ⌜Nat⌝ TmD kMot ⌜ lamT ⌝ᵗ (suc zero)
  ⊢kLam = ⊢methT {T = lamT} {s = conₗ (suc zero) (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢kMot lamOK
            (⊢lam ρTy (⊢app (⊢fst (⊢var (there here)))
                            (⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc (⊢wk idx))) ⊢nzero)))

  ⊢kApp : Γ ⊢ kApp ∷ MethK ⌜Nat⌝ TmD kMot ⌜ appT ⌝ᵗ (suc (suc zero))
  ⊢kApp = ⊢methT {T = appT} {s = conₗ (suc (suc zero)) (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢kMot appOK
            (⊢lam ρTy (⊢plus (⊢app (⊢fst (⊢var (there here))) (⊢var here))
                             (⊢app (⊢fst (⊢snd (⊢var (there here)))) (⊢var here))))

  perK : PerK Γ ⌜Nat⌝ TmD kMot (selF ⌜ TmTs ⌝ₛ) zero KMs
  perK = (selF-β {Cs = ⌜ TmTs ⌝ₛ} nth-z , ⊢kVar)
      ∷ₘ ((selF-β {Cs = ⌜ TmTs ⌝ₛ} (nth-s nth-z) , ⊢kLam)
      ∷ₘ ((selF-β {Cs = ⌜ TmTs ⌝ₛ} (nth-s (nth-s nth-z)) , ⊢kApp) ∷ₘ []ₘ))

------------------------------------------------------------------------
-- 3. ★★★ THE ELIMINATION ITSELF, AT A KRIPKE MOTIVE.
------------------------------------------------------------------------

-- ★★★ `Tm n → (Fin n → Nat) → Nat`, by `ielim` at a KRIPKE motive.
kEval : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kEval n t = ielim TmD n (methₗ KMs) t

⊢kEval : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n →
         Γ ⊢ kEval n t ∷ Π (Π (FinI n) Nat) Nat
⊢kEval {n = n} dn dt =
  ⊢-cast (cong (λ z → Π (Π (FinI z) Nat) Nat) (wk-single n))
    (⊢ielim ⊢⌜Nat⌝ ⊢TmD ⊢kMot (⊢methₗ ⊢⌜Nat⌝ (allD (⊢wk ⊢⌜Nat⌝) TmOK) ⊢kMot perK) dn dt)

------------------------------------------------------------------------
-- 4. ★★ …AND IT COMPUTES.  A KRIPKE motive is a `Π`, so the method's
--    result is a FUNCTION — `ι` still has to fire and deliver it.
------------------------------------------------------------------------

kVarPay : {Γ : Cx} → RTm Γ
kVarPay = pair fz unit

kEval-var : {Γ : Cx} → kEval {Γ} (nsuc nzero) (tvar fz) ⟶* lam (app (var vz) (fst kVarPay))
kEval-var =
  ⟶*-trans (ιT {Cs = ⌜ TmTs ⌝ₛ} {ms = KMs} {T = varT} (nth-⌜⌝ {Ts = TmTs} nthᵗ-z) nth-z)
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _) done)))
