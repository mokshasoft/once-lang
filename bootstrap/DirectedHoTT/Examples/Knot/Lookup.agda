-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ `Γ ∋ x ∷ A`, the first judgement, FIBRED BY ITS
-- SUBJECT (D077).
--
-- The index is `(d , Γ , x , A)`.  The fibre over it is computed by CASE:
-- on the context (`Ctx 0 = ε` has no variable, so its fibre is EMPTY),
-- then on the variable, the other components riding along (a convoy):
--
--     (suc m , Γ' ▹ A' , fzero  , A) ↦ [ Id A (wk A') ]                  here
--     (suc m , Γ' ▹ A' , fsuc y , A) ↦ [ Σ B. (Γ' ∋ y ∷ B) × Id A (wk B) ]  there
--
-- The context and the variable are patterns, so they cost nothing.  Only
-- the TYPE, a computed output (`renTy vs`), Fords.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.Lookup (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; _,_; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using ( wk-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import DirectedHoTT.Lib.NatNum 𝒮 𝓃 using ( ⊢num )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; conₗ; tag; selF; Dσ; ⊢selF; AllD; []ᵈ; _∷ᵈ_; subC; lt-z; nth-z; nth-s; v₀; v₁; v₂; v₃; v₄; v₅; v₆; v₇; _,ₚ_ )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.TelAt 𝒮 𝓃 ok using ( HypAt; ⊢payAt )
open import DirectedHoTT.Lib.MethAt 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatFib 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( wk; ⊢wkS )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 1. THE INDEX, and a fibre as a list of rows.
------------------------------------------------------------------------

⌜Ctx⌝ ⌜Var⌝ : RTm Γ → RTm Γ
⌜Ctx⌝ d = ⌜IMu⌝ ⌜Nat⌝ CtxD d
⌜Var⌝ d = ⌜Fin⌝ d

-- (d , Γ , x , A)
I∋ : RTm Γ
I∋ = ⌜Σ⌝ ⌜Nat⌝ (⌜Σ⌝ (⌜Ctx⌝ v₀) (⌜Σ⌝ (⌜Var⌝ v₁) (⌜Ty⌝ v₂)))

⊢I∋ : {Γ : Ctx} → Γ ⊢ I∋ ∷ U
⊢I∋ = ⊢⌜Σ⌝ ⊢⌜Nat⌝ (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢CtxD (⊢var here))
        (⊢⌜Σ⌝ (⊢⌜Fin⌝ (fromI (⊢var (there here)))) (⊢⌜Ty⌝ (⊢var (there (there here))))))

-- its closedness, cast once (`knot-description-normalisation-trap`)
I∋-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (I∋ {Δ}) ≡ I∋
I∋-sub σ =
  cong (⌜Σ⌝ ⌜Nat⌝) (cong₂ ⌜Σ⌝ (cong (λ D → ⌜IMu⌝ ⌜Nat⌝ D v₀) (CtxD-sub (extS σ)))
                             (cong (⌜Σ⌝ (⌜Var⌝ v₁)) (⌜Ty⌝-sub (extS (extS (extS σ))) v₂)))

Desc∋-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTy σ (Desc (I∋ {Δ})) ≡ Desc I∋
Desc∋-sub σ = cong Desc (I∋-sub σ)

I∋-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) → renTm ρ (I∋ {Δ}) ≡ I∋
I∋-ren ρ = trans (sym (subTm-var ρ I∋)) (I∋-sub ⟨ ρ ⟩ᵣ)

ix∋ : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ix∋ d g x a = pair d (g ,ₚ x ,ₚ a)

-- the Knot's types and contexts, as codes and back
toTy : {Γ : Ctx} {d a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ K 0 d → Γ ⊢ a ∷ El (⌜Ty⌝ d)
toTy da = ⊢conv da (csymᵀ (credᵀ El-⌜Ty⌝))

toVar : {Γ : Ctx} {d x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ Fin d → Γ ⊢ x ∷ El (⌜Var⌝ d)
toVar dx = ⊢conv dx (csymᵀ (credᵀ El-⌜Fin⌝))

toCtx : {Γ : Ctx} {d g : RTm ⌊ Γ ⌋} → Γ ⊢ g ∷ KCtx d → Γ ⊢ g ∷ El (⌜Ctx⌝ d)
toCtx dg = ⊢conv dg (csymᵀ (credᵀ El-⌜IMu⌝))

-- ★ an index, typed.  Every substitution into a code is CAST
--   (`knot-description-normalisation-trap`).
module IxEq {Ξ : Ctx} (d g x : RTm ⌊ Ξ ⌋) where
  wk2 : RTm ⌊ Ξ ⌋ → RTm ((⌊ Ξ ⌋ ∙) ∙)
  wk2 t = renTm vs (renTm vs t)
  B1 : RTm (⌊ Ξ ⌋ ∙)
  B1 = ⌜Σ⌝ (⌜Ctx⌝ v₀) (⌜Σ⌝ (⌜Var⌝ v₁) (⌜Ty⌝ v₂))
  B2 : RTm (⌊ Ξ ⌋ ∙)
  B2 = ⌜Σ⌝ (⌜Var⌝ (renTm vs d)) (⌜Ty⌝ (wk2 d))
  B3 : RTm (⌊ Ξ ⌋ ∙)
  B3 = ⌜Ty⌝ (renTm vs d)
  eqB1 : subTy (single d) (El B1) ≡ El (⌜Σ⌝ (⌜Ctx⌝ d) B2)
  eqB1 = cong El (cong₂ ⌜Σ⌝ (cong (λ D → ⌜IMu⌝ ⌜Nat⌝ D d) (CtxD-sub (single d)))
                            (cong (⌜Σ⌝ (⌜Var⌝ (renTm vs d))) (⌜Ty⌝-sub (extS (extS (single d))) v₂)))
  eqB2 : subTy (single g) (El B2) ≡ El (⌜Σ⌝ (⌜Var⌝ d) (⌜Ty⌝ (renTm vs d)))
  eqB2 = cong El (cong₂ ⌜Σ⌝ (cong ⌜Fin⌝ (wk-cancel-tm g d))
                            (trans (⌜Ty⌝-sub (extS (single g)) (wk2 d))
                                   (cong ⌜Ty⌝ {x = subTm (extS (single g)) (wk2 d)} {y = renTm vs d}
                                         (trans (wk-sub (single g) (renTm vs d)) (cong (renTm vs) (wk-cancel-tm g d))))))
  eqB3 : subTy (single x) (El B3) ≡ El (⌜Ty⌝ d)
  eqB3 = cong El (trans (⌜Ty⌝-sub (single x) (renTm vs d))
                        (cong ⌜Ty⌝ {x = subTm (single x) (renTm vs d)} {y = d} (wk-cancel-tm x d)))
  tyB1 : (Ξ ▹ El ⌜Nat⌝) ⊢ty El B1
  tyB1 = ty-El (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢CtxD (⊢var here))
                (⊢⌜Σ⌝ (⊢⌜Fin⌝ (fromI (⊢var (there here)))) (⊢⌜Ty⌝ (⊢var (there (there here))))))

module _ {Ξ : Ctx} {d g x a : RTm ⌊ Ξ ⌋} where
  open IxEq d g x
  ⊢ix∋ : Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx d → Ξ ⊢ x ∷ Fin d → Ξ ⊢ a ∷ K 0 d → Ξ ⊢ ix∋ d g x a ∷ El I∋
  ⊢ix∋ dd dg dx da = ⊢conv p1 (csymᵀ (credᵀ (El-⌜Σ⌝ ⌜Nat⌝ B1)))
    where
      tyB2 : (Ξ ▹ El (⌜Ctx⌝ d)) ⊢ty El B2
      tyB2 = ty-El (⊢⌜Σ⌝ (⊢⌜Fin⌝ (fromI (⊢wk dd))) (⊢⌜Ty⌝ (⊢wk (⊢wk dd))))
      tyB3 : (Ξ ▹ El (⌜Var⌝ d)) ⊢ty El B3
      tyB3 = ty-El (⊢⌜Ty⌝ (⊢wk dd))
      p3 : Ξ ⊢ pair x a ∷ Σ' (El (⌜Var⌝ d)) (El B3)
      p3 = ⊢pair tyB3 (toVar dx) (⊢-cast {Ξ} {a} {El (⌜Ty⌝ d)} {subTy (single x) (El B3)} (sym eqB3) (toTy da))
      p2 : Ξ ⊢ pair g (x ,ₚ a) ∷ Σ' (El (⌜Ctx⌝ d)) (El B2)
      p2 = ⊢pair tyB2 (toCtx dg)
             (⊢-cast {Ξ} {pair x a} {El (⌜Σ⌝ (⌜Var⌝ d) B3)} {subTy (single g) (El B2)} (sym eqB2)
                     (⊢conv p3 (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜Var⌝ d) B3)))))
      p1 : Ξ ⊢ ix∋ d g x a ∷ Σ' (El ⌜Nat⌝) (El B1)
      p1 = ⊢pair tyB1 dd
             (⊢-cast {Ξ} {pair g (x ,ₚ a)} {El (⌜Σ⌝ (⌜Ctx⌝ d) B2)} {subTy (single d) (El B1)} (sym eqB1)
                     (⊢conv p2 (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ d) B2)))))

-- a fibre: a tag, then the selected row
rows : {c : ℕ} → Cons Γ c → RTm Γ
rows Cs = Dσ Cs

⊢rows : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {c : ℕ} {Cs : Cons ⌊ Γ ⌋ c} → Γ ⊢ I ∷ U → AllD Γ I Cs → Γ ⊢ rows Cs ∷ Desc I
⊢rows {c = c} dI ds = ⊢dσ dI (⊢⌜Fin⌝ (⊢num c)) (⊢selF dI ds)

------------------------------------------------------------------------
-- 2. THE TWO ROWS.
------------------------------------------------------------------------

-- here, at depth `suc m`:  Id A (wk A')
hereT : RTm Γ → RTm Γ → RTm Γ → Tel Γ
hereT m a' a = tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m a')) tι

-- there, at depth `suc m`:  Σ B. (Γ' ∋ y ∷ B) × Id A (wk B)
thereT : RTm Γ → RTm Γ → RTm Γ → RTm Γ → Tel Γ
thereT m g y a =
  tσ (⌜Ty⌝ m)
    (tρ (ix∋ (renTm vs m) (renTm vs g) (renTm vs y) v₀)
      (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc (renTm vs m))) (renTm vs a) (wk 0 (renTm vs m) v₀)) tι))

module _ {Θ : Ctx} {m a' a : RTm ⌊ Θ ⌋} where
  hereOK : Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ a' ∷ K 0 m → Θ ⊢ a ∷ K 0 (nsuc m) → TelOK Θ I∋ (hereT m a' a)
  hereOK dm da' da = ok-σ dId ok-ι
    where
      dId : Θ ⊢ ⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m a') ∷ U
      dId = ⊢⌜Id⌝ {Θ} {⌜Ty⌝ (nsuc m)} {a} {wk 0 m a'} (⊢⌜Ty⌝ (⊢isuc dm)) (toTy da)
                  (toTy (⊢wkS {Θ} {0} {m} {a'} lt-z dm da'))

-- the newest variable, a type code, read as a Knot type
hereTy : {Θ : Ctx} {m : RTm ⌊ Θ ⌋} → (Θ ▹ El (⌜Ty⌝ m)) ⊢ v₀ ∷ K 0 (renTm vs m)
hereTy {Θ} {m} = ⊢conv (⊢-cast {Θ ▹ El (⌜Ty⌝ m)} {v₀} {renTy vs (El (⌜Ty⌝ m))} {El (⌜Ty⌝ (renTm vs m))}
                              (cong El (⌜Ty⌝-ren vs m)) (⊢var here))
                       (credᵀ El-⌜Ty⌝)

module _ {Θ : Ctx} {m g y a : RTm ⌊ Θ ⌋} where
  thereOK : Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ g ∷ KCtx m → Θ ⊢ y ∷ Fin m → Θ ⊢ a ∷ K 0 (nsuc m) →
            TelOK Θ I∋ (thereT m g y a)
  thereOK dm dg dy da = ok-σ (⊢⌜Ty⌝ dm) (subst (λ X → TelOK Θ₁ X (tρ (ix∋ m₁ (renTm vs g) (renTm vs y) v₀) (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m₁)) (renTm vs a) (wk 0 m₁ v₀)) tι))) (sym (I∋-ren vs)) (ok-ρ dj okI))
    where
      Θ₁ : Ctx
      Θ₁ = Θ ▹ El (⌜Ty⌝ m)
      m₁ : RTm ⌊ Θ₁ ⌋
      m₁ = renTm vs m
      dm₁ : Θ₁ ⊢ m₁ ∷ El ⌜Nat⌝
      dm₁ = ⊢wk {Θ} {El (⌜Ty⌝ m)} {m} {El ⌜Nat⌝} dm
      dB : Θ₁ ⊢ v₀ ∷ K 0 m₁
      dB = hereTy
      dj : Θ₁ ⊢ ix∋ m₁ (renTm vs g) (renTm vs y) v₀ ∷ El I∋
      dj = ⊢ix∋ {Θ₁} {m₁} {renTm vs g} {renTm vs y} {v₀} dm₁ (⊢wkCtx {Θ} {El (⌜Ty⌝ m)} {m} {g} dg)
             (⊢wk {Θ} {El (⌜Ty⌝ m)} {y} {Fin m} dy) dB
      dwB : Θ₁ ⊢ wk 0 m₁ v₀ ∷ K 0 (nsuc m₁)
      dwB = ⊢wkS {Θ₁} {0} {m₁} {v₀} lt-z dm₁ dB
      da₁ : Θ₁ ⊢ renTm vs a ∷ K 0 (nsuc m₁)
      da₁ = ⊢wkSK {Γ = Θ} {B = El (⌜Ty⌝ m)} {sg = KSig} {s = 0} {d = nsuc m} {t = a} da
      dId : Θ₁ ⊢ ⌜Id⌝ (⌜Ty⌝ (nsuc m₁)) (renTm vs a) (wk 0 m₁ v₀) ∷ U
      dId = ⊢⌜Id⌝ {Θ₁} {⌜Ty⌝ (nsuc m₁)} {renTm vs a} {wk 0 m₁ v₀} (⊢⌜Ty⌝ (⊢isuc dm₁)) (toTy da₁) (toTy dwB)
      okI : TelOK Θ₁ I∋ (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m₁)) (renTm vs a) (wk 0 m₁ v₀)) tι)
      okI = ok-σ dId ok-ι

------------------------------------------------------------------------
-- 3. ★ THE FIBRE: case on the context, then on the variable.  The
--   context's case carries the variable and the type along (a convoy:
--   its index is not the outer depth); the variable's case is the
--   kernel's `fcase` at the FIXED depth `suc m`, so it needs none.
------------------------------------------------------------------------

tyK : {Θ : Ctx} {d : RTm ⌊ Θ ⌋} → Θ ⊢ d ∷ El ⌜Nat⌝ → Θ ⊢ty K 0 d
tyK dd = ty-SK KOK lt-z dd

tyCtx : {Θ : Ctx} {d : RTm ⌊ Θ ⌋} → Θ ⊢ d ∷ El ⌜Nat⌝ → Θ ⊢ty KCtx d
tyCtx dd = ty-IMu ⊢⌜Nat⌝ ⊢CtxD dd

------------------------------------------------------------------------
-- 3a. The context's case.  Motive: G(j, g) = Fin j → Ty j → Desc
------------------------------------------------------------------------

GM : RTy ((Γ ∙) ∙)
GM = Π (Fin v₁) (Π (K 0 v₂) (Desc I∋))

GB : RTm Γ → RTy Γ
GB j = Π (Fin j) (Π (K 0 (renTm vs j)) (Desc I∋))

GM-sub : {Δ Θ : Cx} (τ : Sub ((Δ ∙) ∙) Θ) → subTy τ (GM {Δ}) ≡ GB (τ (vs vz))
GM-sub τ = cong₂ Π refl (cong₂ Π (SK-sub (extS τ) KSig 0 v₂) (Desc∋-sub (extS (extS τ))))

⊢GM : {Θ : Ctx} → motCtx Θ ⌜Nat⌝ CtxD ⊢ty GM
⊢GM = ty-Π (ty-Fin (fromI (⊢var (there here)))) (ty-Π (tyK (⊢var (there (there here)))) (ty-Desc ⊢I∋))

-- at 0 (binders payload, hypotheses, x, A): the empty context has no variable, so NO row
gz : RTm Γ
gz = lam (lam (lam (lam (rows []))))

-- at suc m (binders m | payload (Γ', A'), hypotheses, x, A): the payload's
--   two components bound by λ (so the rows come out clean), then the case
--   on the variable — `here` at `fzero`, `there` at `fsuc y`
FB : RTm (((((((Γ ∙) ∙) ∙) ∙) ∙) ∙) ∙)          -- binders … x, A, A', Γ'
FB = fcase v₃ (rows (⌜ hereT v₆ v₁ v₂ ⌝ᵗ ∷ []))
              (rows (⌜ thereT v₇ v₁ v₀ v₃ ⌝ᵗ ∷ []))

gsB : RTm (((((Γ ∙) ∙) ∙) ∙) ∙)
gsB = app (app (lam (lam FB)) (fst (snd v₃))) (fst v₃)

gs : RTm (Γ ∙)
gs = lam (lam (lam (lam gsB)))

gM : RTm Γ
gM = methN (methAt (gz ∷ [])) (methAt (gs ∷ []))

-- ★ THE FIBRE FUNCTION
D∋ : RTm Γ
D∋ = lam (app (app (ielim CtxD (fst v₀) gM (fst (snd v₀))) (fst (snd (snd v₀))))
              (snd (snd (snd v₀))))

K∋ : RTm Γ → RTy Γ
K∋ i = IMu I∋ D∋ i

module _ {Θ : Ctx} where
  private
    HZ : Ctx
    HZ = HypAt Θ ⌜Nat⌝ (DN ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ) GM (single nzero) emptyT
    HS : Ctx
    HS = HypAt (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs CtxD) (wk1M GM) τS extT

    GM-at0 : subTy (atS nzero (conₗ 0 v₁)) (GM {⌊ Θ ⌋}) ≡ GB nzero
    GM-at0 = GM-sub (atS nzero (conₗ 0 v₁))

    GM-atS : subTy (atS (nsuc v₀) (conₗ 0 v₁)) (wk1M (GM {⌊ Θ ⌋})) ≡ GB (nsuc v₂)
    GM-atS = trans {x = subTy (atS (nsuc v₀) (conₗ 0 v₁)) (wk1M (GM {⌊ Θ ⌋}))}
                   {y = subTy (atS (nsuc v₀) (conₗ 0 v₁) ₛ∘ᵣ extR (extR vs)) GM}
                   {z = GB (nsuc v₂)}
                   (subTy-renTy {σ = atS (nsuc v₀) (conₗ 0 v₁)} {ρ = extR (extR vs)} GM)
                   (GM-sub (atS (nsuc v₀) (conₗ 0 v₁) ₛ∘ᵣ extR (extR vs)))

    dnz : {Ξ : Ctx} → Ξ ⊢ nzero ∷ El ⌜Nat⌝
    dnz = ⊢conv ⊢nzero (csymᵀ elNat)

    bz' : HZ ⊢ lam (lam (rows [])) ∷ subTy (atS nzero (conₗ 0 v₁)) GM
    bz' = ⊢-cast {HZ} {lam (lam (rows []))} {GB nzero} {subTy (atS nzero (conₗ 0 v₁)) GM} (sym GM-at0)
            (⊢lam (ty-Fin (fromI dnz)) (⊢lam (tyK dnz) (⊢rows {I = I∋} {Cs = []} ⊢I∋ []ᵈ)))

    -- the successor case's body: the variable's case at `suc m`
    C2 : Ctx
    C2 = (HS ▹ Fin (nsuc v₂)) ▹ K 0 (nsuc v₃)
    m4 : RTm ⌊ C2 ⌋
    m4 = v₄
    dm4 : C2 ⊢ m4 ∷ El ⌜Nat⌝
    dm4 = ⊢var (there (there (there (there here))))
    dPay : HS ⊢ v₁ ∷ PayN (vs ᵣ∘ₛ (vs ᵣ∘ₛ τS)) extT (renTm vs (renTm vs ⌜Nat⌝)) (renTm vs (renTm vs (renTm vs CtxD)))
    dPay = ⊢payAt {Γ = Θ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {D = renTm vs CtxD} {M = wk1M GM} {σ = τS} {T = extT}
    eD : renTm vs (renTm vs (renTm vs CtxD)) ≡ CtxD {⌊ HS ⌋}
    eD = trans (cong (renTm vs) {x = renTm vs (renTm vs CtxD)} {y = CtxD}
                     (trans (cong (renTm vs) {x = renTm vs CtxD} {y = CtxD} (CtxD-ren vs)) (CtxD-ren vs)))
               (CtxD-ren vs)
    dG0 : HS ⊢ fst v₁ ∷ KCtx v₂
    dG0 = extFst {HS} {⌊ Θ ⌋} {vs ᵣ∘ₛ (vs ᵣ∘ₛ τS)} {renTm vs (renTm vs (renTm vs CtxD))} {v₁} eD dPay
    dA0 : HS ⊢ fst (snd v₁) ∷ K 0 v₂
    dA0 = extSnd {HS} {⌊ Θ ⌋} {vs ᵣ∘ₛ (vs ᵣ∘ₛ τS)} {renTm vs (renTm vs (renTm vs CtxD))} {v₁} eD dPay
    -- the convoy, in C2: Γ' and A' (the payload), x, A
    dG' : C2 ⊢ fst v₃ ∷ KCtx m4
    dG' = ⊢wkCtx {HS ▹ Fin (nsuc v₂)} {K 0 (nsuc v₃)} (⊢wkCtx {HS} {Fin (nsuc v₂)} dG0)
    dA' : C2 ⊢ fst (snd v₃) ∷ K 0 m4
    dA' = ⊢wkSK {Γ = HS ▹ Fin (nsuc v₂)} {B = K 0 (nsuc v₃)} {sg = KSig} {s = 0}
                (⊢wkSK {Γ = HS} {B = Fin (nsuc v₂)} {sg = KSig} {s = 0} dA0)
    dx : C2 ⊢ v₁ ∷ Fin (nsuc m4)
    dx = ⊢wk {HS ▹ Fin (nsuc v₂)} {K 0 (nsuc v₃)} {v₀} {Fin (nsuc v₃)} (⊢var here)
    dA : C2 ⊢ v₀ ∷ K 0 (nsuc m4)
    dA = hereSK {Γ = HS ▹ Fin (nsuc v₂)} {sg = KSig} {s = 0} {d = nsuc v₃}
    -- the λ-bound A' and Γ', over C2
    C4 : Ctx
    C4 = (C2 ▹ K 0 m4) ▹ KCtx (renTm vs m4)
    m6 : RTm ⌊ C4 ⌋
    m6 = v₆
    dm6 : C4 ⊢ m6 ∷ El ⌜Nat⌝
    dm6 = ⊢wk (⊢wk dm4)
    da6 : C4 ⊢ v₁ ∷ K 0 m6
    da6 = ⊢wkSK {Γ = C2 ▹ K 0 m4} {B = KCtx (renTm vs m4)} {sg = KSig} {s = 0}
                (hereSK {Γ = C2} {sg = KSig} {s = 0} {d = m4})
    dg6 : C4 ⊢ v₀ ∷ KCtx m6
    dg6 = hereCtx {C2 ▹ K 0 m4} {renTm vs m4}
    dA6 : C4 ⊢ v₂ ∷ K 0 (nsuc m6)
    dA6 = ⊢wkSK {Γ = C2 ▹ K 0 m4} {B = KCtx (renTm vs m4)} {sg = KSig} {s = 0}
                (⊢wkSK {Γ = C2} {B = K 0 m4} {sg = KSig} {s = 0} dA)
    dx6 : C4 ⊢ v₃ ∷ Fin (nsuc m6)
    dx6 = ⊢wk (⊢wk dx)
    -- here, at `fzero`
    hRow : C4 ⊢ rows (⌜ hereT m6 v₁ v₂ ⌝ᵗ ∷ []) ∷ Desc I∋
    hRow = ⊢rows {C4} {I∋} {1} {⌜ hereT m6 v₁ v₂ ⌝ᵗ ∷ []} ⊢I∋
             (⊢tel {C4} {I∋} {hereT m6 v₁ v₂} ⊢I∋ (hereOK {C4} {m6} dm6 da6 dA6) ∷ᵈ []ᵈ)
    -- there, at `fsuc y`, one binder further
    C5 : Ctx
    C5 = C4 ▹ Fin m6
    tRow : C5 ⊢ rows (⌜ thereT v₇ v₁ v₀ v₃ ⌝ᵗ ∷ []) ∷ Desc I∋
    tRow = ⊢rows {C5} {I∋} {1} {⌜ thereT v₇ v₁ v₀ v₃ ⌝ᵗ ∷ []} ⊢I∋
             (⊢tel {C5} {I∋} {thereT v₇ v₁ v₀ v₃} ⊢I∋
                   (thereOK {C5} {v₇} {v₁} {v₀} {v₃} (⊢wk dm6) (⊢wkCtx {C4} {Fin m6} dg6) (⊢var here)
                            (⊢wkSK {Γ = C4} {B = Fin m6} {sg = KSig} {s = 0} dA6)) ∷ᵈ []ᵈ)
    dFB : C4 ⊢ FB ∷ Desc I∋
    dFB = ⊢-cast (Desc∋-sub (single v₃))
            (⊢fcase (ty-Desc ⊢I∋) dx6 (⊢-cast (sym (Desc∋-sub (single fzero))) hRow)
                    (⊢-cast (sym (Desc∋-sub fsucS)) tRow))
    -- the two λs, applied to the payload's components
    L2 : RTy (⌊ C2 ⌋ ∙)
    L2 = Π (KCtx (renTm vs m4)) (Desc I∋)
    dL : C2 ⊢ lam (lam FB) ∷ Π (K 0 m4) L2
    dL = ⊢lam (tyK dm4) (⊢lam (tyCtx (⊢wk dm4)) dFB)
    e1 : subTy (single (fst (snd v₃))) L2 ≡ Π (KCtx m4) (Desc I∋)
    e1 = cong₂ Π (trans (KCtx-sub (single (fst (snd v₃))) (renTm vs m4))
                        (cong KCtx {x = subTm (single (fst (snd v₃))) (renTm vs m4)} {y = m4} (wk-cancel-tm (fst (snd v₃)) m4)))
                 (Desc∋-sub (extS (single (fst (snd v₃)))))
    body : C2 ⊢ gsB ∷ Desc I∋
    body = ⊢-cast (Desc∋-sub (single (fst v₃)))
             (⊢app (⊢-cast e1 (⊢app dL dA')) dG')

    bs' : HS ⊢ lam (lam gsB) ∷ subTy (atS (nsuc v₀) (conₗ 0 v₁)) (wk1M GM)
    bs' = ⊢-cast {HS} {_} {GB (nsuc v₂)} {subTy (atS (nsuc v₀) (conₗ 0 v₁)) (wk1M GM)}
            (sym GM-atS)
            (⊢lam (ty-Fin (⊢nsuc (fromI (⊢var (there (there here))))))
              (⊢lam (tyK (⊢isuc (⊢var (there (there (there here)))))) body))

  ⊢gM : Θ ⊢ gM ∷ MethTy ⌜Nat⌝ CtxD GM
  ⊢gM = ⊢methN {Γ = Θ} {D = CtxD} {M = GM} {E0 = methAt (gz ∷ [])} {ES = methAt (gs ∷ [])} ⊢CtxD ⊢GM
          (⊢caseZ {Γ = Θ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} {M = GM} {ms = gz ∷ []} dZ dS ⊢GM perZ)
          (⊢caseS {Γ = Θ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} {M = GM} {ms = gs ∷ []} dZ dS ⊢GM perS)
    where
      dZ : AllD (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ ⌜ CtxZ ⌝ₛ
      dZ = allD {Γ = Θ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxZ} (⊢wk ⊢⌜Nat⌝) CtxZOK
      dS : AllD (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ ⌜ CtxS ⌝ₛ
      dS = allD {Γ = Θ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxS} (⊢wk ⊢⌜Nat⌝) CtxSOK
      perZ : PerKAt Θ ⌜Nat⌝ CtxD GM nzero (selF (subC (single nzero) ⌜ CtxZ ⌝ₛ)) zero (gz ∷ [])
      perZ = entZ {Γ = Θ} {Ts = CtxZ} {CS = ⌜ CtxS ⌝ₛ} {T = emptyT} {M = GM} CtxZOK dS ⊢GM nthᵗ-z bz' ∷ₐ []ₐ
      perS : PerKAt (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs CtxD) (wk1M GM) (nsuc v₀)
                    (selF (subC τS ⌜ CtxS ⌝ₛ)) zero (gs ∷ [])
      perS = entN {Γ = Θ} {C0 = ⌜ CtxZ ⌝ₛ} {Ts = CtxS} {T = extT} {M = GM} dZ CtxSOK ⊢GM nthᵗ-z bs' ∷ₐ []ₐ

-- the context case's result, applied to its convoy
module _ {Ξ : Ctx} {j f x a : RTm ⌊ Ξ ⌋} where
  ⊢GBapp : Ξ ⊢ f ∷ GB j → Ξ ⊢ x ∷ Fin j → Ξ ⊢ a ∷ K 0 j → Ξ ⊢ app (app f x) a ∷ Desc I∋
  ⊢GBapp df dx da = ⊢-cast {Ξ} {app (app f x) a} {subTy (single a) (Desc I∋)} {Desc I∋} (Desc∋-sub (single a)) f2
    where
      e : subTy (single x) (Π (K 0 (renTm vs j)) (Desc I∋)) ≡ Π (K 0 j) (Desc I∋)
      e = cong₂ Π (trans (SK-sub (single x) KSig 0 (renTm vs j)) (cong (K 0) {x = subTm (single x) (renTm vs j)} {y = j} (wk-cancel-tm x j)))
                  (Desc∋-sub (extS (single x)))
      f1 : Ξ ⊢ app f x ∷ Π (K 0 j) (Desc I∋)
      f1 = ⊢-cast {Ξ} {app f x} {subTy (single x) (Π (K 0 (renTm vs j)) (Desc I∋))} {Π (K 0 j) (Desc I∋)} e
                  (⊢app {Ξ} {Fin j} {Π (K 0 (renTm vs j)) (Desc I∋)} {f} {x} df dx)
      f2 : Ξ ⊢ app (app f x) a ∷ subTy (single a) (Desc I∋)
      f2 = ⊢app {Ξ} {K 0 j} {Desc I∋} {app f x} {a} f1 da

-- ★ an index's four components, typed (the inverse of `⊢ix∋`)
module Un∋ {Ξ : Ctx} {v : RTm ⌊ Ξ ⌋} (dv : Ξ ⊢ v ∷ El I∋) where
  d0 g0 x0 a0 : RTm ⌊ Ξ ⌋
  d0 = fst v
  g0 = fst (snd v)
  x0 = fst (snd (snd v))
  a0 = snd (snd (snd v))
  open IxEq d0 g0 x0
  private
    dv' : Ξ ⊢ v ∷ Σ' (El ⌜Nat⌝) (El B1)
    dv' = ⊢conv dv (credᵀ (El-⌜Σ⌝ ⌜Nat⌝ B1))
    s1 : Ξ ⊢ snd v ∷ Σ' (El (⌜Ctx⌝ d0)) (El B2)
    s1 = ⊢conv (⊢-cast {Ξ} {snd v} {subTy (single d0) (El B1)} {El (⌜Σ⌝ (⌜Ctx⌝ d0) B2)} eqB1 (⊢snd dv'))
               (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ d0) B2))
    s2 : Ξ ⊢ snd (snd v) ∷ Σ' (El (⌜Var⌝ d0)) (El B3)
    s2 = ⊢conv (⊢-cast {Ξ} {snd (snd v)} {subTy (single g0) (El B2)} {El (⌜Σ⌝ (⌜Var⌝ d0) B3)} eqB2 (⊢snd s1))
               (credᵀ (El-⌜Σ⌝ (⌜Var⌝ d0) B3))
  dd0 : Ξ ⊢ d0 ∷ El ⌜Nat⌝
  dd0 = ⊢fst dv'
  dg0 : Ξ ⊢ g0 ∷ KCtx d0
  dg0 = ⊢conv (⊢fst s1) (credᵀ El-⌜IMu⌝)
  dx0 : Ξ ⊢ x0 ∷ Fin d0
  dx0 = ⊢conv (⊢fst s2) (credᵀ El-⌜Fin⌝)
  da0 : Ξ ⊢ a0 ∷ K 0 d0
  da0 = ⊢conv (⊢-cast {Ξ} {a0} {subTy (single x0) (El B3)} {El (⌜Ty⌝ d0)} eqB3 (⊢snd s2)) (credᵀ El-⌜Ty⌝)

------------------------------------------------------------------------
-- 4. ★ THE FAMILY IS WELL FORMED.
------------------------------------------------------------------------

module _ {Θ : Ctx} where
  private
    Ξ : Ctx
    Ξ = Θ ▹ El I∋
    dv : Ξ ⊢ v₀ ∷ El I∋
    dv = ⊢-cast {Ξ} {v₀} {renTy vs (El I∋)} {El I∋} (cong El (I∋-ren vs)) (⊢var here)
    open Un∋ dv
    dI : Ξ ⊢ ielim CtxD d0 gM g0 ∷ iinst d0 g0 GM
    dI = ⊢ielim {Ξ} {⌜Nat⌝} {CtxD} {GM} {gM} {d0} {g0} ⊢⌜Nat⌝ ⊢CtxD ⊢GM ⊢gM dd0 dg0
    eG : iinst d0 g0 GM ≡ GB d0
    eG = trans {x = iinst d0 g0 GM} {y = subTy (single g0 ∘ₛ extS (single d0)) GM} {z = GB d0}
               (subTy-subTy {τ = single g0} {σ = extS (single d0)} GM)
               (trans (GM-sub (single g0 ∘ₛ extS (single d0)))
                      (cong GB {x = subTm (single g0) (renTm vs d0)} {y = d0} (wk-cancel-tm g0 d0)))
    bodyD : Ξ ⊢ app (app (ielim CtxD d0 gM g0) x0) a0 ∷ Desc I∋
    bodyD = ⊢GBapp {Ξ} {d0} (⊢-cast {Ξ} {ielim CtxD d0 gM g0} {iinst d0 g0 GM} {GB d0} eG dI) dx0 da0

  ⊢D∋ : Θ ⊢ D∋ ∷ DescF I∋
  ⊢D∋ = ⊢lam (ty-El ⊢I∋) (⊢-cast {Ξ} {_} {Desc I∋} {Desc (renTm vs I∋)} (cong Desc (sym (I∋-ren vs))) bodyD)

  ty-K∋ : {i : RTm ⌊ Θ ⌋} → Θ ⊢ i ∷ El I∋ → Θ ⊢ty K∋ i
  ty-K∋ di = ty-IMu ⊢I∋ ⊢D∋ di
