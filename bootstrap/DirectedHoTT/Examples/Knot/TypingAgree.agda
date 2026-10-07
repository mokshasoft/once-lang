-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★ THE TYPING JUDGEMENTS ARE FAITHFUL (PLAN-FAITHFUL
-- F5, `⊢ty`/`⊢`): every Spec derivation maps to a Knot inhabitant AT THE
-- QUOTED JUDGEMENT.
--
--     enTy : Γ ⊢ty A   → Θ ⊢ _ ∷ IMu JT (D⊢ t𝒮) (tyIx (dep Γ) ⌜Γ⌝ ⌜A⌝)
--     enTm : Γ ⊢ t ∷ A → Θ ⊢ _ ∷ IMu JT (D⊢ t𝒮) (tmIx (dep Γ) ⌜Γ⌝ ⌜t⌝ ⌜A⌝)
--
-- Most rules are EXACT: the constructor's index is the quoted judgement.
-- Where a Knot row states a type through an OPERATION (`sub0`, `wk`,
-- `nrsK`, `DF`, `mc`, `MethTyK`, `iinstK`, …) the Spec states the operated
-- type, and F3's agreement `op ⌜…⌝ ⟶* ⌜op …⌝` bridges them by `⊢conv` on
-- the index — premises backwards, the conclusion forwards.
--
-- `⊢ref` converts its conclusion by `εwk-agree-ty` (the body's type, weakened
-- to the depth); its row is hand-written (`Knot/RefJudge`, PLAN-BIDI §2-ter).
--
-- Two rules need more than a conversion:
--   * `⊢tr` — the Knot row takes the motive's code and base point
--     STRENGTHENED (`e1`/`e2` at `Γ`), the Spec keeps them under the binder
--     with `occTm vz … ≡ false`.  The strengthened codes are `c[t]`/`a[t]`,
--     and `strength` puts them back under `vs`.
--   * `⊢conv` — the Knot's conversion rows are per subject head, so it
--     dispatches through the generated `ConvHead.convAt`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.TypingAgree (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; NoNatC; nonatc-sub; occTm; subTm-occ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; stepᵀ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-IMu; ⟶*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-natrecᶻ; ⟶*-appˡ; ⟶*-appʳ; ⟶*-fst; ⟶*-snd )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( wk-cancel-tm )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( quoteCtx; ⊢quoteCtx; cext )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; tyIx; tmIx; ⌜Tm⌝; ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( toTm )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf core using ( D⊢ )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf core using ( El-⌜≅ᵀ⌝; module ≅ᵀF )
open import DirectedHoTT.Examples.Knot.QuoteSig 𝒮 wf using ( q𝒮; t𝒮; ⊢t𝒮; ⊢belowT; typesQ-at )
open import DirectedHoTT.Examples.Knot.Unquote 𝒮 wf using ( quoteℕ-num )
open import DirectedHoTT.Lib.NatNum 𝒮 (Defs.size 𝒮) using ( num )
open import DirectedHoTT.Examples.Knot.Preds 𝒮 wf using ( El-⌜NNC⌝; El-⌜Flat⌝ )
open import DirectedHoTT.Examples.Knot.JudgeConGen 𝒮 wf core
open import DirectedHoTT.Examples.Knot.OpAgree 𝒮 wf
open import DirectedHoTT.Examples.Knot.PredsAgree 𝒮 wf using ( ⊢nncC; ⊢flatC )
open import DirectedHoTT.Examples.Knot.LookupAgree 𝒮 wf using ( enLk )
open import DirectedHoTT.Examples.Knot.JudgeConv 𝒮 wf core using ( El-⌜∋⌝ )
open import DirectedHoTT.Examples.Knot.ConvAgree 𝒮 wf core using ( enConvT )
open import DirectedHoTT.Examples.Knot.ConvHead 𝒮 wf core using ( convAt )
open import DirectedHoTT.Examples.Knot.RefCon 𝒮 wf core using ( con⊢ref )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( v₀ )

------------------------------------------------------------------------
-- 1. Index conversions, by position in `tmIx j g t A`/`tyIx j g A`
------------------------------------------------------------------------

private
  module _ {Ξ : Ctx} where
    -- tmIx j g t A = pair (pair (tag 1) j) (pair t (pair g A))
    tmA : {j g t A A' : RTm ⌊ Ξ ⌋} → A ⟶* A' → IMu JT (D⊢ t𝒮) (tmIx j g t A) ≅ᵀ IMu JT (D⊢ t𝒮) (tmIx j g t A')
    tmA R = red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ R))))

    tmT : {j g t t' A : RTm ⌊ Ξ ⌋} → t ⟶* t' → IMu JT (D⊢ t𝒮) (tmIx j g t A) ≅ᵀ IMu JT (D⊢ t𝒮) (tmIx j g t' A)
    tmT R = red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairˡ R)))

    -- tyIx j g A = pair (pair (tag 0) j) (pair A (pair g unit))
    tyG : {j g g' A : RTm ⌊ Ξ ⌋} → g ⟶* g' → IMu JT (D⊢ t𝒮) (tyIx j g A) ≅ᵀ IMu JT (D⊢ t𝒮) (tyIx j g' A)
    tyG R = red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ R))))

    -- the Id-premise of the `tr` rows: `a` is (a reduct of) `b`
    idTm : {d a b : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ a ∷ K 1 d → b ⟶* a →
           Ξ ⊢ idrefl (⌜Tm⌝ d) a ∷ El (⌜Id⌝ (⌜Tm⌝ d) a b)
    idTm dd da R = ⊢conv (⊢idrefl (⊢⌜Tm⌝ dd) (toTm da)) (csymᵀ (red→≅ᵀ (stepᵀ (El-⌜Id⌝ _ _ _) (⟶ᵀ*-Idʳ R))))

  -- a code free of the bound variable is the weakening of its instance
  strength : {Ξ : Cx} (t : RTm Ξ) (c : RTm (Ξ ∙)) → occTm vz c ≡ false → renTm vs (subTm (single t) c) ≡ c
  strength t c o = trans (renTm-subTm c) (trans (subTm-occ c agree) (subTm-id c))
    where
    agree : ∀ x → occTm x c ≡ true → _
    agree vz oc with trans (sym oc) o
    ... | ()
    agree (vs i) oc = refl

  -- `⊢tr`'s source and target types, at strengthened codes
  homEq : {Γ Θ : Cx} (x c₀ a₀ : RTm Γ) →
          quoteTy (El (subTm (single x) (⌜Hom⌝ (renTm vs c₀) (renTm vs a₀) v₀))) {Θ} ≡ kEl (kcHom (quoteTm c₀) (quoteTm a₀) (quoteTm x))
  homEq x c₀ a₀ = cong₂ (λ C D → kEl (kcHom (quoteTm C) (quoteTm D) (quoteTm x))) (wk-cancel-tm x c₀) (wk-cancel-tm x a₀)

------------------------------------------------------------------------
-- 2. The maps
------------------------------------------------------------------------

KTy : (Γ : Ctx) → RTy ⌊ Γ ⌋ → (Θ : Ctx) → Set
KTy Γ A Θ = Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ IMu JT (D⊢ t𝒮) (tyIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy A)))

KTm : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → (Θ : Ctx) → Set
KTm Γ t A Θ = Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ IMu JT (D⊢ t𝒮) (tmIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTm t) (quoteTy A)))

enTy : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} → Γ ⊢ty A → {Θ : Ctx} → KTy Γ A Θ
enTm : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → {Θ : Ctx} → KTm Γ t A Θ

-- `⊢tr` at strengthened codes: `c`/`a` ARE weakenings
private
  enTr : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {c a : RTm (⌊ Γ ⌋ ∙)} {p e t u : RTm ⌊ Γ ⌋} (c₀ a₀ : RTm ⌊ Γ ⌋) →
         renTm vs c₀ ≡ c → renTm vs a₀ ≡ a → NoNatC c₀ → {Θ : Ctx} →
         KTm (Γ ▹ A) c U Θ → KTm (Γ ▹ A) a (El c) Θ → KTm (Γ ▹ A) v₀ (El c) Θ →
         KTm Γ t A Θ → KTm Γ u A Θ → KTm Γ p (Hom A t u) Θ →
         KTm Γ e (El (subTm (single t) (⌜Hom⌝ c a v₀))) Θ →
         KTm Γ (tr (⌜Hom⌝ c a v₀) p e) (El (subTm (single u) (⌜Hom⌝ c a v₀))) Θ
  enTr {Γ} {A} {p = p} {e} {t} {u} c₀ a₀ refl refl nc {Θ} (_ , rc) (_ , ra) (_ , rv) (_ , rt) (_ , ru) (_ , rp) (ke , re) =
    subst (λ X → Σ (RTm ⌊ Θ ⌋) (λ k → Θ ⊢ k ∷ IMu JT (D⊢ t𝒮) (tmIx dj g (quoteTm (tr (⌜Hom⌝ c a v₀) p e)) X))) (sym (homEq u c₀ a₀))
      (_ , con⊢tr₂ ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm (⌜Hom⌝ c a v₀)) (⊢quoteTm p) (⊢quoteTm e)
                   (⊢quoteTy A) (⊢quoteTm c₀) (⊢quoteTm a₀)
                   (⊢conv (⊢nncC nc) (csymᵀ El-⌜NNC⌝))
                   (idTm (⊢dep' (⌊ Γ ⌋ ∙)) (⊢quoteTm (⌜Hom⌝ c a v₀))
                         (⟶*-trans (node-1 (wk-agree-tm c₀)) (node-2 (wk-agree-tm a₀))))
                   (⊢quoteTm t) (⊢quoteTm u)
                   (⊢conv rc (csymᵀ (tmT (wk-agree-tm c₀))))
                   (⊢conv (⊢conv ra (csymᵀ (tmT (wk-agree-tm a₀)))) (csymᵀ (tmA (node-1 (wk-agree-tm c₀)))))
                   (⊢conv rv (csymᵀ (tmA (node-1 (wk-agree-tm c₀)))))
                   rt ru rp
                   (subst (λ X → Θ ⊢ ke ∷ IMu JT (D⊢ t𝒮) (tmIx dj g (quoteTm e) X)) (homEq t c₀ a₀) re))
    where
    c a : RTm (⌊ Γ ⌋ ∙)
    c = renTm vs c₀
    a = renTm vs a₀
    dj g : RTm ⌊ Θ ⌋
    dj = dep ⌊ Γ ⌋
    g = quoteCtx Γ

enTy {Γ} ty-base = _ , con⊢tybase ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTy {Γ} ty-U = _ , con⊢tyU ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTy {Γ} (ty-Π {A = A} {B} dA dB) =
  _ , con⊢tyPi ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A) (⊢quoteTy B) (Σ.snd (enTy dA)) (Σ.snd (enTy dB))
enTy {Γ} (ty-Σ {A = A} {B} dA dB) =
  _ , con⊢tySg ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A) (⊢quoteTy B) (Σ.snd (enTy dA)) (Σ.snd (enTy dB))
enTy {Γ} (ty-El {c = c} dc) = _ , con⊢tyEl ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (Σ.snd (enTm dc))
enTy {Γ} (ty-Id {A = A} {t} {u} dA dt du) =
  _ , con⊢tyId ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A) (⊢quoteTm t) (⊢quoteTm u)
               (Σ.snd (enTy dA)) (Σ.snd (enTm dt)) (Σ.snd (enTm du))
enTy {Γ} ty-Unit = _ , con⊢tyUnit ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTy {Γ} ty-Nat = _ , con⊢tyNat ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTy {Γ} (ty-IMu {I = I} {D} {i} dI dD di) =
  _ , con⊢tyIMu ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm I) (⊢quoteTm D) (⊢quoteTm i)
                (Σ.snd (enTm dI)) (⊢conv (Σ.snd (enTm dD)) (csymᵀ (tmA (DF-agree I)))) (Σ.snd (enTm di))
enTy {Γ} (ty-Desc {I = I} dI) = _ , con⊢tyDesc ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm I) (Σ.snd (enTm dI))
enTy {Γ} (ty-DIh {I = I} {D} {M} {C} {p} dI dD dM dC dp) =
  _ , con⊢tyDIh ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm D) (⊢quoteTy M) (⊢quoteTm C) (⊢quoteTm p) (⊢quoteTm I)
                (Σ.snd (enTm dI)) (⊢conv (Σ.snd (enTm dD)) (csymᵀ (tmA (DF-agree I))))
                (⊢conv (Σ.snd (enTy dM)) (csymᵀ (tyG (mc-agree Γ I D))))
                (Σ.snd (enTm dC)) (Σ.snd (enTm dp))
enTy {Γ} (ty-Fin {n = n} dn) = _ , con⊢tyFin ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm n) (Σ.snd (enTm dn))
enTy {Γ} (ty-Hom {A = A} {t} {u} dA dt du) =
  _ , con⊢tyHom ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A) (⊢quoteTm t) (⊢quoteTm u)
                (Σ.snd (enTy dA)) (Σ.snd (enTm dt)) (Σ.snd (enTm du))

enTm {Γ} (⊢var {x = x} {A} d) =
  _ , con⊢var ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A) (⊢quoteVar x) (⊢conv (Σ.snd (enLk d)) (csymᵀ (credᵀ El-⌜∋⌝)))
enTm {Γ} (⊢lam {A = A} {B} {t} dA dt) =
  _ , con⊢lam ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm t) (⊢quoteTy A) (⊢quoteTy B) (Σ.snd (enTy dA)) (Σ.snd (enTm dt))
enTm {Γ} (⊢app {A = A} {B} {t} {u} dt du) =
  _ , ⊢conv (con⊢app ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm t) (⊢quoteTm u) (⊢quoteTy A) (⊢quoteTy B)
                     (Σ.snd (enTm dt)) (Σ.snd (enTm du)))
            (tmA (sub0-agree-ty B u))
enTm {Γ} (⊢pair {A = A} {B} {a} {b} dB da db) =
  _ , con⊢pair ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm a) (⊢quoteTm b) (⊢quoteTy A) (⊢quoteTy B)
               (Σ.snd (enTy dB)) (Σ.snd (enTm da)) (⊢conv (Σ.snd (enTm db)) (csymᵀ (tmA (sub0-agree-ty B a))))
enTm {Γ} (⊢absurd {c = c} {e} dc de) =
  _ , con⊢absurd ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (⊢quoteTm e) (Σ.snd (enTm dc)) (Σ.snd (enTm de))
enTm {Γ} (⊢ordtr {a = a} {t} {u} {p} {q} da dt du dp dq) =
  _ , con⊢ordtr ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm a) (⊢quoteTm t) (⊢quoteTm u) (⊢quoteTm p) (⊢quoteTm q)
                (Σ.snd (enTm da)) (Σ.snd (enTm dt)) (Σ.snd (enTm du)) (Σ.snd (enTm dp)) (Σ.snd (enTm dq))
enTm {Γ} (⊢fst {A = A} {B} {p} dp) =
  _ , con⊢fst ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A) (⊢quoteTm p) (⊢quoteTy B) (Σ.snd (enTm dp))
enTm {Γ} (⊢snd {A = A} {B} {p} dp) =
  _ , ⊢conv (con⊢snd ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm p) (⊢quoteTy A) (⊢quoteTy B) (Σ.snd (enTm dp)))
            (tmA (sub0-agree-ty B (fst p)))
enTm {Γ} ⊢⌜base⌝ = _ , con⊢cbase ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTm {Γ} (⊢⌜Π⌝ {c = c} {d} dc dd) =
  _ , con⊢cPi ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (⊢quoteTm d) (Σ.snd (enTm dc)) (Σ.snd (enTm dd))
enTm {Γ} (⊢⌜Σ⌝ {c = c} {d} dc dd) =
  _ , con⊢cSg ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (⊢quoteTm d) (Σ.snd (enTm dc)) (Σ.snd (enTm dd))
enTm {Γ} (⊢⌜Hom⌝ {c = c} {a} {b} dc da db) =
  _ , con⊢cHom ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (⊢quoteTm a) (⊢quoteTm b)
               (Σ.snd (enTm dc)) (Σ.snd (enTm da)) (Σ.snd (enTm db))
enTm {Γ} (⊢hrefl {c = c} {t} dc dt) =
  _ , con⊢hrefl ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (⊢quoteTm t) (Σ.snd (enTm dc)) (Σ.snd (enTm dt))
enTm {Γ} (⊢trU {p = p} {e} {t} {u} dt du dp de) =
  _ , con⊢tr₁ ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm (var {⌊ Γ ⌋ ∙} vz)) (⊢quoteTm p) (⊢quoteTm e) (⊢quoteTm t) (⊢quoteTm u)
              (idTm (⊢dep' (⌊ Γ ⌋ ∙)) (⊢quoteTm (var {⌊ Γ ⌋ ∙} vz)) done)
              (Σ.snd (enTm dt)) (Σ.snd (enTm du)) (Σ.snd (enTm dp)) (Σ.snd (enTm de))
enTm {Γ} (⊢tr {c = c} {a} {t = t} dc da dv nc oc oa dt du dp de) =
  enTr (subTm (single t) c) (subTm (single t) a) (strength t c oc) (strength t a oa) (nonatc-sub (single t) nc)
       (enTm dc) (enTm da) (enTm dv) (enTm dt) (enTm du) (enTm dp) (enTm de)
enTm {Γ} (⊢ap {cA = cA} {cB} {b} {p} {t} {u} dA fl dB db dt du dp) =
  _ , ⊢conv (con⊢ap ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm cB) (⊢quoteTm b) (⊢quoteTm p) (⊢quoteTm cA)
                    (⊢conv (⊢flatC cA fl) (csymᵀ El-⌜Flat⌝)) (⊢quoteTm t) (⊢quoteTm u)
                    (Σ.snd (enTm dA)) (Σ.snd (enTm dB))
                    (⊢conv (Σ.snd (enTm db)) (csymᵀ (tmA (node-1 (wk-agree-tm cB)))))
                    (Σ.snd (enTm dt)) (Σ.snd (enTm du)) (Σ.snd (enTm dp)))
            (tmA (⟶*-trans (node-2 (sub0-agree-tm b t)) (node-3 (sub0-agree-tm b u))))
enTm {Γ} (⊢⌜Id⌝ {c = c} {a} {b} dc da db) =
  _ , con⊢cId ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (⊢quoteTm a) (⊢quoteTm b)
              (Σ.snd (enTm dc)) (Σ.snd (enTm da)) (Σ.snd (enTm db))
enTm {Γ} ⊢⌜Nat⌝ = _ , con⊢cNat ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTm {Γ} (⊢⌜IMu⌝ {I = I} {D} {i} dI dD di) =
  _ , con⊢cIMu ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm I) (⊢quoteTm D) (⊢quoteTm i)
               (Σ.snd (enTm dI)) (⊢conv (Σ.snd (enTm dD)) (csymᵀ (tmA (DF-agree I)))) (Σ.snd (enTm di))
enTm {Γ} (⊢⌜Fin⌝ {n = n} dn) = _ , con⊢cFin ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm n) (Σ.snd (enTm dn))
enTm {Γ} ⊢⌜Unit⌝ = _ , con⊢cUnit ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTm {Γ} (⊢idrefl {c = c} {t} dc dt) =
  _ , con⊢idrefl ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm c) (⊢quoteTm t) (Σ.snd (enTm dc)) (Σ.snd (enTm dt))
enTm {Γ} (⊢jsub {A = A} {d} {t} {u} {p} {e} dd dt du dp de) =
  _ , ⊢conv (con⊢jsub ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm d) (⊢quoteTm p) (⊢quoteTm e) (⊢quoteTy A) (⊢quoteTm t) (⊢quoteTm u)
                      (Σ.snd (enTm dd)) (Σ.snd (enTm dt)) (Σ.snd (enTm du)) (Σ.snd (enTm dp))
                      (⊢conv (Σ.snd (enTm de)) (csymᵀ (tmA (node-1 (sub0-agree-tm d t))))))
            (tmA (node-1 (sub0-agree-tm d u)))
enTm {Γ} ⊢unit = _ , con⊢unit ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTm {Γ} ⊢nzero = _ , con⊢nzero ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ)
enTm {Γ} (⊢nsuc {n = n} dn) = _ , con⊢nsuc ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm n) (Σ.snd (enTm dn))
enTm {Γ} (⊢natrec {M = M} {z} {s} {n} dM dz ds dn) =
  _ , ⊢conv (con⊢natrec ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm z) (⊢quoteTm s) (⊢quoteTm n) (⊢quoteTy M)
                        (Σ.snd (enTy dM)) (⊢conv (Σ.snd (enTm dz)) (csymᵀ (tmA (sub0-agree-ty M nzero))))
                        (⊢conv (Σ.snd (enTm ds)) (csymᵀ (tmA (nrs-agree M)))) (Σ.snd (enTm dn)))
            (tmA (sub0-agree-ty M n))
enTm {Γ} (⊢dι {I = I} dI) = _ , con⊢dI ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm I) (Σ.snd (enTm dI))
enTm {Γ} (⊢dσ {I = I} {S} {f} dI dS df) =
  _ , con⊢dS ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm S) (⊢quoteTm f) (⊢quoteTm I)
             (Σ.snd (enTm dI)) (Σ.snd (enTm dS)) (⊢conv (Σ.snd (enTm df)) (csymᵀ (tmA (node-2 (node-1 (wk-agree-tm I))))))
enTm {Γ} (⊢dρ {I = I} {j} {C} dI dj dC) =
  _ , con⊢dR ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm j) (⊢quoteTm C) (⊢quoteTm I)
             (Σ.snd (enTm dI)) (Σ.snd (enTm dj)) (Σ.snd (enTm dC))
enTm {Γ} (⊢dpay {I = I} {D} {C} dI dD dC) =
  _ , con⊢dpay ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm I) (⊢quoteTm D) (⊢quoteTm C)
               (Σ.snd (enTm dI)) (⊢conv (Σ.snd (enTm dD)) (csymᵀ (tmA (DF-agree I)))) (Σ.snd (enTm dC))
enTm {Γ} (⊢con {I = I} {D} {i} {p} dI dD di dp) =
  _ , con⊢con ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm p) (⊢quoteTm I) (⊢quoteTm D) (⊢quoteTm i)
              (Σ.snd (enTm dI)) (⊢conv (Σ.snd (enTm dD)) (csymᵀ (tmA (DF-agree I)))) (Σ.snd (enTm di)) (Σ.snd (enTm dp))
enTm {Γ} (⊢dih {I = I} {D} {M} {e} {C} {p} dI dD dM de dC dp) =
  _ , con⊢dih ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm D) (⊢quoteTm e) (⊢quoteTm C) (⊢quoteTm p) (⊢quoteTm I) (⊢quoteTy M)
              (Σ.snd (enTm dI)) (⊢conv (Σ.snd (enTm dD)) (csymᵀ (tmA (DF-agree I))))
              (⊢conv (Σ.snd (enTy dM)) (csymᵀ (tyG (mc-agree Γ I D))))
              (⊢conv (Σ.snd (enTm de)) (csymᵀ (tmA (MethTy-agree I D M))))
              (Σ.snd (enTm dC)) (Σ.snd (enTm dp))
enTm {Γ} (⊢ielim {I = I} {D} {M} {e} {i} {t} dI dD dM de di dt) =
  _ , ⊢conv (con⊢ielim ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm D) (⊢quoteTm i) (⊢quoteTm e) (⊢quoteTm t) (⊢quoteTm I) (⊢quoteTy M)
                       (Σ.snd (enTm dI)) (⊢conv (Σ.snd (enTm dD)) (csymᵀ (tmA (DF-agree I))))
                       (⊢conv (Σ.snd (enTy dM)) (csymᵀ (tyG (mc-agree Γ I D))))
                       (⊢conv (Σ.snd (enTm de)) (csymᵀ (tmA (MethTy-agree I D M))))
                       (Σ.snd (enTm di)) (Σ.snd (enTm dt)))
            (tmA (iinst-agree i t M))
enTm {Γ} (⊢fzero {n = n} dn) = _ , con⊢fzero ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm n) (Σ.snd (enTm dn))
enTm {Γ} (⊢fsuc {n = n} {t} dt) = _ , con⊢fsuc ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm t) (⊢quoteTm n) (Σ.snd (enTm dt))
enTm {Γ} (⊢fcase {n = n} {P} {t} {a} {b} dP dt da db) =
  _ , ⊢conv (con⊢fcase ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm t) (⊢quoteTm a) (⊢quoteTm b) (⊢quoteTm n) (⊢quoteTy P)
                       (Σ.snd (enTy dP)) (Σ.snd (enTm dt))
                       (⊢conv (Σ.snd (enTm da)) (csymᵀ (tmA (sub0-agree-ty P fzero))))
                       (⊢conv (Σ.snd (enTm db)) (csymᵀ (tmA (fsucS-agree P)))))
            (tmA (sub0-agree-ty P t))
enTm {Γ} (⊢fcase0 {P = P} {t} dP dt) =
  _ , ⊢conv (con⊢fcase0 ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm t) (⊢quoteTy P) (Σ.snd (enTy dP)) (Σ.snd (enTm dt)))
            (tmA (sub0-agree-ty P t))
enTm {Γ} (⊢psplit {A = A} {B} {P} {q} {b} dA dB dP dq db) =
  _ , ⊢conv (con⊢psplit ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTm b) (⊢quoteTm q) (⊢quoteTy A) (⊢quoteTy B) (⊢quoteTy P)
                        (Σ.snd (enTy dA)) (Σ.snd (enTy dB)) (Σ.snd (enTy dP)) (Σ.snd (enTm dq))
                        (⊢conv (Σ.snd (enTm db)) (csymᵀ (tmA (pairS-agree P)))))
            (tmA (sub0-agree-ty P q))
-- ★ PLAN-REF K4: the side condition computed (`⊢belowT`), the declared
--   type looked up in the quoted signature (`typesQ-at`)
enTm {Γ} (⊢ref {d = n} lt) =
  _ , ⊢conv (con⊢ref ⊢t𝒮 (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteℕ n) (⊢belowT lt))
            (tmA (⟶*-trans (⟶*-natrecᶻ (⟶*-trans (⟶*-appˡ (⟶*-fst (⟶*-snd (step (βfst q𝒮 (num (Defs.size 𝒮))) done))))
                                         (⟶*-trans (⟶*-appʳ (subst (λ z → quoteℕ n ⟶* z) (quoteℕ-num n) done))
                                                   (typesQ-at 𝒮 n))))
                           (εwk-agree-ty ⌊ Γ ⌋ (Defs.type 𝒮 n))))
enTm {Γ} (⊢conv {t = t} {A} {B} d c) =
  convAt Γ t (⊢quoteTy A) (⊢quoteTy B) (Σ.snd (enTm d))
         (⊢conv (Σ.snd (enConvT c)) (csymᵀ (ctrnᵀ El-⌜≅ᵀ⌝ (red→≅ᵀ (≅ᵀF.KF-⟶ᵀ* (step (βfst q𝒮 (num (Defs.size 𝒮))) done))))))
