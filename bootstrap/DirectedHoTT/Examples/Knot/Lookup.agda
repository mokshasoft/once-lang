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
module DirectedHoTT.Examples.Knot.Lookup where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; _,_; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; selF; ⊢selF; AllD; []ᵈ; _∷ᵈ_; subC; lt-z; nth-z; nth-s )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelAt using ( HypAt; ⊢payAt )
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Ren using ( wk; ⊢wkS )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 1. THE INDEX, and a fibre as a list of rows.
------------------------------------------------------------------------

⌜Ctx⌝ ⌜Var⌝ : RTm Γ → RTm Γ
⌜Ctx⌝ d = ⌜IMu⌝ ⌜Nat⌝ CtxD d
⌜Var⌝ d = ⌜IMu⌝ ⌜Nat⌝ FinD d

-- (d , Γ , x , A)
I∋ : RTm Γ
I∋ = ⌜Σ⌝ ⌜Nat⌝ (⌜Σ⌝ (⌜Ctx⌝ (var vz)) (⌜Σ⌝ (⌜Var⌝ (var (vs vz))) (⌜Ty⌝ (var (vs (vs vz))))))

⊢I∋ : {Γ : Ctx} → Γ ⊢ I∋ ∷ U
⊢I∋ = ⊢⌜Σ⌝ ⊢⌜Nat⌝ (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢CtxD (⊢var here))
        (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢var (there here))) (⊢⌜Ty⌝ (⊢var (there (there here))))))

-- its closedness, cast once (`knot-description-normalisation-trap`)
I∋-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (I∋ {Δ}) ≡ I∋
I∋-sub σ =
  cong (⌜Σ⌝ ⌜Nat⌝) (cong₂ ⌜Σ⌝ (cong (λ D → ⌜IMu⌝ ⌜Nat⌝ D (var vz)) (CtxD-sub (extS σ)))
                             (cong (⌜Σ⌝ (⌜Var⌝ (var (vs vz)))) (⌜Ty⌝-sub (extS (extS (extS σ))) (var (vs (vs vz))))))

Desc∋-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTy σ (Desc (I∋ {Δ})) ≡ Desc I∋
Desc∋-sub σ = cong Desc (I∋-sub σ)

I∋-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) → renTm ρ (I∋ {Δ}) ≡ I∋
I∋-ren ρ = trans (sym (subTm-var ρ I∋)) (I∋-sub ⟨ ρ ⟩ᵣ)

ix∋ : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ix∋ d g x a = pair d (pair g (pair x a))

-- the Knot's types and contexts, as codes and back
toTy : {Γ : Ctx} {d a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ K 0 d → Γ ⊢ a ∷ El (⌜Ty⌝ d)
toTy da = ⊢conv da (csymᵀ (credᵀ El-⌜Ty⌝))

toVar : {Γ : Ctx} {d x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ FinI d → Γ ⊢ x ∷ El (⌜Var⌝ d)
toVar dx = ⊢conv dx (csymᵀ (credᵀ El-⌜IMu⌝))

toCtx : {Γ : Ctx} {d g : RTm ⌊ Γ ⌋} → Γ ⊢ g ∷ KCtx d → Γ ⊢ g ∷ El (⌜Ctx⌝ d)
toCtx dg = ⊢conv dg (csymᵀ (credᵀ El-⌜IMu⌝))

-- ★ an index, typed.  Every substitution into a code is CAST
--   (`knot-description-normalisation-trap`).
module IxEq {Ξ : Ctx} (d g x : RTm ⌊ Ξ ⌋) where
  wk2 : RTm ⌊ Ξ ⌋ → RTm ((⌊ Ξ ⌋ ∙) ∙)
  wk2 t = renTm vs (renTm vs t)
  B1 : RTm (⌊ Ξ ⌋ ∙)
  B1 = ⌜Σ⌝ (⌜Ctx⌝ (var vz)) (⌜Σ⌝ (⌜Var⌝ (var (vs vz))) (⌜Ty⌝ (var (vs (vs vz)))))
  B2 : RTm (⌊ Ξ ⌋ ∙)
  B2 = ⌜Σ⌝ (⌜Var⌝ (renTm vs d)) (⌜Ty⌝ (wk2 d))
  B3 : RTm (⌊ Ξ ⌋ ∙)
  B3 = ⌜Ty⌝ (renTm vs d)
  eqB1 : subTy (single d) (El B1) ≡ El (⌜Σ⌝ (⌜Ctx⌝ d) B2)
  eqB1 = cong El (cong₂ ⌜Σ⌝ (cong (λ D → ⌜IMu⌝ ⌜Nat⌝ D d) (CtxD-sub (single d)))
                            (cong (⌜Σ⌝ (⌜Var⌝ (renTm vs d))) (⌜Ty⌝-sub (extS (extS (single d))) (var (vs (vs vz))))))
  eqB2 : subTy (single g) (El B2) ≡ El (⌜Σ⌝ (⌜Var⌝ d) (⌜Ty⌝ (renTm vs d)))
  eqB2 = cong El (cong₂ ⌜Σ⌝ (cong (⌜IMu⌝ ⌜Nat⌝ FinD) (wk-cancel-tm g d))
                            (trans (⌜Ty⌝-sub (extS (single g)) (wk2 d))
                                   (cong ⌜Ty⌝ {x = subTm (extS (single g)) (wk2 d)} {y = renTm vs d}
                                         (trans (wk-sub (single g) (renTm vs d)) (cong (renTm vs) (wk-cancel-tm g d))))))
  eqB3 : subTy (single x) (El B3) ≡ El (⌜Ty⌝ d)
  eqB3 = cong El (trans (⌜Ty⌝-sub (single x) (renTm vs d))
                        (cong ⌜Ty⌝ {x = subTm (single x) (renTm vs d)} {y = d} (wk-cancel-tm x d)))
  tyB1 : (Ξ ▹ El ⌜Nat⌝) ⊢ty El B1
  tyB1 = ty-El (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢CtxD (⊢var here))
                (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢var (there here))) (⊢⌜Ty⌝ (⊢var (there (there here))))))

module _ {Ξ : Ctx} {d g x a : RTm ⌊ Ξ ⌋} where
  open IxEq d g x
  ⊢ix∋ : Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx d → Ξ ⊢ x ∷ FinI d → Ξ ⊢ a ∷ K 0 d → Ξ ⊢ ix∋ d g x a ∷ El I∋
  ⊢ix∋ dd dg dx da = ⊢conv p1 (csymᵀ (credᵀ (El-⌜Σ⌝ ⌜Nat⌝ B1)))
    where
      tyB2 : (Ξ ▹ El (⌜Ctx⌝ d)) ⊢ty El B2
      tyB2 = ty-El (⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢wk dd)) (⊢⌜Ty⌝ (⊢wk (⊢wk dd))))
      tyB3 : (Ξ ▹ El (⌜Var⌝ d)) ⊢ty El B3
      tyB3 = ty-El (⊢⌜Ty⌝ (⊢wk dd))
      p3 : Ξ ⊢ pair x a ∷ Σ' (El (⌜Var⌝ d)) (El B3)
      p3 = ⊢pair tyB3 (toVar dx) (⊢-cast {Ξ} {a} {El (⌜Ty⌝ d)} {subTy (single x) (El B3)} (sym eqB3) (toTy da))
      p2 : Ξ ⊢ pair g (pair x a) ∷ Σ' (El (⌜Ctx⌝ d)) (El B2)
      p2 = ⊢pair tyB2 (toCtx dg)
             (⊢-cast {Ξ} {pair x a} {El (⌜Σ⌝ (⌜Var⌝ d) B3)} {subTy (single g) (El B2)} (sym eqB2)
                     (⊢conv p3 (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜Var⌝ d) B3)))))
      p1 : Ξ ⊢ ix∋ d g x a ∷ Σ' (El ⌜Nat⌝) (El B1)
      p1 = ⊢pair tyB1 dd
             (⊢-cast {Ξ} {pair g (pair x a)} {El (⌜Σ⌝ (⌜Ctx⌝ d) B2)} {subTy (single d) (El B1)} (sym eqB1)
                     (⊢conv p2 (csymᵀ (credᵀ (El-⌜Σ⌝ (⌜Ctx⌝ d) B2)))))

-- the predecessor
pd : RTm Γ → RTm Γ
pd i = natrec nzero (var (vs vz)) i

⊢pd : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El ⌜Nat⌝ → Γ ⊢ pd i ∷ El ⌜Nat⌝
⊢pd di = ⊢natrec (ty-El ⊢⌜Nat⌝) (⊢conv ⊢nzero (csymᵀ elNat))
                 (⊢conv (⊢var (there here)) (csymᵀ elNat)) (⊢conv di elNat)

-- a fibre: a tag, then the selected row
rows : {c : ℕ} → Cons Γ c → RTm Γ
rows {c = c} Cs = dσ (⌜Fin⌝ c) (selF Cs)

⊢rows : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {c : ℕ} {Cs : Cons ⌊ Γ ⌋ c} → Γ ⊢ I ∷ U → AllD Γ I Cs → Γ ⊢ rows Cs ∷ Desc I
⊢rows dI ds = ⊢dσ dI ⊢⌜Fin⌝ (⊢selF dI ds)

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
    (tρ (ix∋ (renTm vs m) (renTm vs g) (renTm vs y) (var vz))
      (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc (renTm vs m))) (renTm vs a) (wk 0 (renTm vs m) (var vz))) tι))

module _ {Θ : Ctx} {m a' a : RTm ⌊ Θ ⌋} where
  hereOK : Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ a' ∷ K 0 m → Θ ⊢ a ∷ K 0 (nsuc m) → TelOK Θ I∋ (hereT m a' a)
  hereOK dm da' da = ok-σ dId ok-ι
    where
      dId : Θ ⊢ ⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m a') ∷ U
      dId = ⊢⌜Id⌝ {Θ} {⌜Ty⌝ (nsuc m)} {a} {wk 0 m a'} (⊢⌜Ty⌝ (⊢isuc dm)) (toTy da)
                  (toTy (⊢wkS {Θ} {0} {m} {a'} lt-z dm da'))

-- the newest variable, a type code, read as a Knot type
hereTy : {Θ : Ctx} {m : RTm ⌊ Θ ⌋} → (Θ ▹ El (⌜Ty⌝ m)) ⊢ var vz ∷ K 0 (renTm vs m)
hereTy {Θ} {m} = ⊢conv (⊢-cast {Θ ▹ El (⌜Ty⌝ m)} {var vz} {renTy vs (El (⌜Ty⌝ m))} {El (⌜Ty⌝ (renTm vs m))}
                              (cong El (⌜Ty⌝-ren vs m)) (⊢var here))
                       (credᵀ El-⌜Ty⌝)

module _ {Θ : Ctx} {m g y a : RTm ⌊ Θ ⌋} where
  thereOK : Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ g ∷ KCtx m → Θ ⊢ y ∷ FinI m → Θ ⊢ a ∷ K 0 (nsuc m) →
            TelOK Θ I∋ (thereT m g y a)
  thereOK dm dg dy da = ok-σ (⊢⌜Ty⌝ dm) (subst (λ X → TelOK Θ₁ X (tρ (ix∋ m₁ (renTm vs g) (renTm vs y) (var vz)) (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m₁)) (renTm vs a) (wk 0 m₁ (var vz))) tι))) (sym (I∋-ren vs)) (ok-ρ dj okI))
    where
      Θ₁ : Ctx
      Θ₁ = Θ ▹ El (⌜Ty⌝ m)
      m₁ : RTm ⌊ Θ₁ ⌋
      m₁ = renTm vs m
      dm₁ : Θ₁ ⊢ m₁ ∷ El ⌜Nat⌝
      dm₁ = ⊢wk {Θ} {El (⌜Ty⌝ m)} {m} {El ⌜Nat⌝} dm
      dB : Θ₁ ⊢ var vz ∷ K 0 m₁
      dB = hereTy
      dj : Θ₁ ⊢ ix∋ m₁ (renTm vs g) (renTm vs y) (var vz) ∷ El I∋
      dj = ⊢ix∋ {Θ₁} {m₁} {renTm vs g} {renTm vs y} {var vz} dm₁ (⊢wkCtx {Θ} {El (⌜Ty⌝ m)} {m} {g} dg)
             (⊢wk {Θ} {El (⌜Ty⌝ m)} {y} {FinI m} dy) dB
      dwB : Θ₁ ⊢ wk 0 m₁ (var vz) ∷ K 0 (nsuc m₁)
      dwB = ⊢wkS {Θ₁} {0} {m₁} {var vz} lt-z dm₁ dB
      da₁ : Θ₁ ⊢ renTm vs a ∷ K 0 (nsuc m₁)
      da₁ = ⊢wkSK {Γ = Θ} {B = El (⌜Ty⌝ m)} {sg = KSig} {s = 0} {d = nsuc m} {t = a} da
      dId : Θ₁ ⊢ ⌜Id⌝ (⌜Ty⌝ (nsuc m₁)) (renTm vs a) (wk 0 m₁ (var vz)) ∷ U
      dId = ⊢⌜Id⌝ {Θ₁} {⌜Ty⌝ (nsuc m₁)} {renTm vs a} {wk 0 m₁ (var vz)} (⊢⌜Ty⌝ (⊢isuc dm₁)) (toTy da₁) (toTy dwB)
      okI : TelOK Θ₁ I∋ (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m₁)) (renTm vs a) (wk 0 m₁ (var vz))) tι)
      okI = ok-σ dId ok-ι

------------------------------------------------------------------------
-- 3. ★ THE FIBRE: case on the context, then on the variable.  Each case
--   carries the other components along (a convoy: the case's index is
--   not the outer depth, so they must be re-typed at it).
------------------------------------------------------------------------

tyK : {Θ : Ctx} {d : RTm ⌊ Θ ⌋} → Θ ⊢ d ∷ El ⌜Nat⌝ → Θ ⊢ty K 0 d
tyK dd = ty-SK KOK lt-z dd

tyCtx : {Θ : Ctx} {d : RTm ⌊ Θ ⌋} → Θ ⊢ d ∷ El ⌜Nat⌝ → Θ ⊢ty KCtx d
tyCtx dd = ty-IMu ⊢⌜Nat⌝ ⊢CtxD dd

-- the predecessor of a successor, in a Knot type and a context type
pdK : {Θ : Ctx} {m t : RTm ⌊ Θ ⌋} → Θ ⊢ t ∷ K 0 (pd (nsuc m)) → Θ ⊢ t ∷ K 0 m
pdK {Θ} {m} {t} dt =
  ⊢-cast {Θ} {t} {K 0 (subTm (single (pd m)) (renTm vs m))} {K 0 m}
         (cong (K 0) {x = subTm (single (pd m)) (renTm vs m)} {y = m} (wk-cancel-tm (pd m) m))
         (⊢conv {Θ} {t} {K 0 (pd (nsuc m))} {K 0 (subTm (single (pd m)) (renTm vs m))} dt
                (credᵀ (ξ-SK (natrec-suc nzero (var (vs vz)) m))))

pdCtx : {Θ : Ctx} {m t : RTm ⌊ Θ ⌋} → Θ ⊢ t ∷ KCtx (pd (nsuc m)) → Θ ⊢ t ∷ KCtx m
pdCtx {Θ} {m} {t} dt =
  ⊢-cast {Θ} {t} {KCtx (subTm (single (pd m)) (renTm vs m))} {KCtx m}
         (cong KCtx {x = subTm (single (pd m)) (renTm vs m)} {y = m} (wk-cancel-tm (pd m) m))
         (⊢conv {Θ} {t} {KCtx (pd (nsuc m))} {KCtx (subTm (single (pd m)) (renTm vs m))} dt
                (credᵀ (ξ-IMuⁱ (natrec-suc nzero (var (vs vz)) m))))

------------------------------------------------------------------------
-- 3a. The variable's case.  Motive: X(j, y) = Ty (pred j) → Ctx (pred j) → Ty j → Desc
------------------------------------------------------------------------

XM : RTy ((Γ ∙) ∙)
XM = Π (K 0 (pd (var (vs vz)))) (Π (KCtx (pd (var (vs (vs vz))))) (Π (K 0 (var (vs (vs (vs vz))))) (Desc I∋)))

-- its instances: the motive under any substitution of its two binders
XB : RTm Γ → RTy Γ
XB j = Π (K 0 (pd j)) (Π (KCtx (pd (renTm vs j))) (Π (K 0 (renTm vs (renTm vs j))) (Desc I∋)))

XM-sub : {Δ Θ : Cx} (τ : Sub ((Δ ∙) ∙) Θ) → subTy τ (XM {Δ}) ≡ XB (τ (vs vz))
XM-sub τ = cong₂ Π (SK-sub τ KSig 0 (pd (var (vs vz))))
             (cong₂ Π (KCtx-sub (extS τ) (pd (var (vs (vs vz)))))
               (cong₂ Π (SK-sub (extS (extS τ)) KSig 0 (var (vs (vs (vs vz))))) (Desc∋-sub (extS (extS (extS τ))))))

⊢XM : {Θ : Ctx} → motCtx Θ ⌜Nat⌝ FinD ⊢ty XM
⊢XM = ty-Π (tyK (⊢pd (⊢var (there here))))
        (ty-Π (tyCtx (⊢pd (⊢var (there (there here)))))
          (ty-Π (tyK (⊢var (there (there (there here))))) (ty-Desc ⊢I∋)))

-- the method bodies at `suc m` (binders m | payload, hypotheses, A', Γ', A)
xz xs : RTm (Γ ∙)
xz = lam (lam (lam (lam (lam (rows (⌜ hereT (var (vs (vs (vs (vs (vs vz)))))) (var (vs (vs vz))) (var vz) ⌝ᵗ ∷ []))))))
xs = lam (lam (lam (lam (lam (rows (⌜ thereT (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz))
                                              (fst (var (vs (vs (vs (vs vz)))))) (var vz) ⌝ᵗ ∷ []))))))

xM : RTm Γ
xM = methN (methAt []) (methAt (xz ∷ xs ∷ []))

module _ {Θ : Ctx} where
  private
    -- the successor case's method context, and its body type
    H : Tel (⌊ Θ ⌋ ∙) → Ctx
    H T = HypAt (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs FinD) (wk1M XM) τS T
    BX : RTy (((⌊ Θ ⌋ ∙) ∙) ∙)
    BX = XB (nsuc (var (vs (vs vz))))
    XM-at : (k : ℕ) → subTy (atS (nsuc (var vz)) (conₗ k (var (vs vz)))) (wk1M (XM {⌊ Θ ⌋})) ≡ BX
    XM-at k = trans {x = subTy (atS (nsuc (var vz)) (conₗ k (var (vs vz)))) (wk1M (XM {⌊ Θ ⌋}))}
                    {y = subTy (atS (nsuc (var vz)) (conₗ k (var (vs vz))) ₛ∘ᵣ extR (extR vs)) XM} {z = BX}
                    (subTy-renTy {σ = atS (nsuc (var vz)) (conₗ k (var (vs vz)))} {ρ = extR (extR vs)} XM)
                    (XM-sub (atS (nsuc (var vz)) (conₗ k (var (vs vz))) ₛ∘ᵣ extR (extR vs)))

    -- the three convoy binders over a method context `Hk`
    module Body (Hk : Ctx) (m3 : RTm ⌊ Hk ⌋) (dm : Hk ⊢ m3 ∷ El ⌜Nat⌝) where
      H1 = Hk ▹ K 0 (pd (nsuc m3))
      H2 = H1 ▹ KCtx (pd (nsuc (renTm vs m3)))
      H3 = H2 ▹ K 0 (nsuc (renTm vs (renTm vs m3)))
      m5 : RTm ⌊ H3 ⌋
      m5 = renTm vs (renTm vs (renTm vs m3))
      dm5 : H3 ⊢ m5 ∷ El ⌜Nat⌝
      dm5 = ⊢wk (⊢wk (⊢wk dm))
      dA : H3 ⊢ var vz ∷ K 0 (nsuc m5)
      dA = hereSK {Γ = H2} {sg = KSig} {s = 0} {d = nsuc (renTm vs (renTm vs m3))}
      dA' : H3 ⊢ var (vs (vs vz)) ∷ K 0 m5
      dA' = pdK {H3} {m5} (⊢wkSK {Γ = H2} {B = K 0 (nsuc (renTm vs (renTm vs m3)))} {sg = KSig} {s = 0}
                              (⊢wkSK {Γ = H1} {B = KCtx (pd (nsuc (renTm vs m3)))} {sg = KSig} {s = 0}
                                 (hereSK {Γ = Hk} {sg = KSig} {s = 0} {d = pd (nsuc m3)})))
      dG' : H3 ⊢ var (vs vz) ∷ KCtx m5
      dG' = pdCtx {H3} {m5} (⊢wkCtx {H2} {K 0 (nsuc (renTm vs (renTm vs m3)))} (hereCtx {H1} {pd (nsuc (renTm vs m3))}))
      hRow : H3 ⊢ rows (⌜ hereT m5 (var (vs (vs vz))) (var vz) ⌝ᵗ ∷ []) ∷ Desc I∋
      hT : TelOK H3 I∋ (hereT m5 (var (vs (vs vz))) (var vz))
      hT = hereOK {H3} {m5} {var (vs (vs vz))} {var vz} dm5 dA' dA
      hD : H3 ⊢ ⌜ hereT m5 (var (vs (vs vz))) (var vz) ⌝ᵗ ∷ Desc I∋
      hD = ⊢tel {H3} {I∋} {hereT m5 (var (vs (vs vz))) (var vz)} ⊢I∋ hT
      hRow = ⊢rows {H3} {I∋} {1} {⌜ hereT m5 (var (vs (vs vz))) (var vz) ⌝ᵗ ∷ []} ⊢I∋ (hD ∷ᵈ []ᵈ)
      tRow : {y : RTm ⌊ H3 ⌋} → H3 ⊢ y ∷ FinI m5 → H3 ⊢ rows (⌜ thereT m5 (var (vs vz)) y (var vz) ⌝ᵗ ∷ []) ∷ Desc I∋
      tRow {y} dy = ⊢rows {H3} {I∋} {1} {⌜ thereT m5 (var (vs vz)) y (var vz) ⌝ᵗ ∷ []} ⊢I∋ (tD ∷ᵈ []ᵈ)
        where
          tT : TelOK H3 I∋ (thereT m5 (var (vs vz)) y (var vz))
          tT = thereOK {H3} {m5} {var (vs vz)} {y} {var vz} dm5 dG' dy dA
          tD : H3 ⊢ ⌜ thereT m5 (var (vs vz)) y (var vz) ⌝ᵗ ∷ Desc I∋
          tD = ⊢tel {H3} {I∋} {thereT m5 (var (vs vz)) y (var vz)} ⊢I∋ tT
      lams : {b : RTm ⌊ H3 ⌋} → H3 ⊢ b ∷ Desc I∋ → Hk ⊢ lam (lam (lam b)) ∷ XB (nsuc m3)
      lams db = ⊢lam (tyK (⊢pd (⊢isuc dm)))
                  (⊢lam (tyCtx (⊢pd (⊢isuc (⊢wk dm))))
                    (⊢lam (tyK (⊢isuc (⊢wk (⊢wk dm)))) db))

    bz : H fzeroT ⊢ lam (lam (lam (rows (⌜ hereT (var (vs (vs (vs (vs (vs vz)))))) (var (vs (vs vz))) (var vz) ⌝ᵗ ∷ []))))
                 ∷ subTy (atS (nsuc (var vz)) (conₗ 0 (var (vs vz)))) (wk1M XM)
    bz = ⊢-cast (sym (XM-at 0)) (lams hRow)
      where open Body (H fzeroT) (var (vs (vs vz))) (⊢var (there (there here)))

    bs : H fsucT ⊢ lam (lam (lam (rows (⌜ thereT (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz))
                                                  (fst (var (vs (vs (vs (vs vz)))))) (var vz) ⌝ᵗ ∷ []))))
                 ∷ subTy (atS (nsuc (var vz)) (conₗ 1 (var (vs vz)))) (wk1M XM)
    bs = ⊢-cast (sym (XM-at 1))
           (lams (tRow dy))
      where
        open Body (H fsucT) (var (vs (vs vz))) (⊢var (there (there here)))
        dy : H3 ⊢ fst (var (vs (vs (vs (vs vz))))) ∷ FinI m5
        dy = ⊢conv (⊢wk (⊢wk (⊢wk (⊢fst (⊢payAt {I = ⌜Nat⌝} {D = renTm vs FinD} {M = wk1M XM} {σ = τS} {T = fsucT})))))
                   crflᵀ

  ⊢xM : Θ ⊢ xM ∷ MethTy ⌜Nat⌝ FinD XM
  ⊢xM = ⊢methN {Γ = Θ} {D = FinD} {M = XM} {E0 = methAt []} {ES = methAt (xz ∷ xs ∷ [])} ⊢FinD ⊢XM
          (⊢caseZ {Γ = Θ} {C0 = []} {CS = ⌜ FinTs ⌝ₛ} {M = XM} {ms = []} []ᵈ dS ⊢XM []ₐ)
          (⊢caseS {Γ = Θ} {C0 = []} {CS = ⌜ FinTs ⌝ₛ} {M = XM} {ms = xz ∷ xs ∷ []} []ᵈ dS ⊢XM perX)
    where
      dS : AllD (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ ⌜ FinTs ⌝ₛ
      dS = allD {Γ = Θ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = FinTs} (⊢wk ⊢⌜Nat⌝) (FinOK {Θ})
      perX : PerKAt (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs FinD) (wk1M XM) (nsuc (var vz))
                    (selF (subC τS ⌜ FinTs ⌝ₛ)) zero (xz ∷ xs ∷ [])
      perX = entN {Γ = Θ} {C0 = []} {Ts = FinTs} {T = fzeroT} {M = XM} []ᵈ FinOK ⊢XM nthᵗ-z bz
          ∷ₐ entN {Γ = Θ} {C0 = []} {Ts = FinTs} {T = fsucT} {M = XM} []ᵈ FinOK ⊢XM (nthᵗ-s nthᵗ-z) bs
          ∷ₐ []ₐ

-- ★ the variable case's result, applied to its convoy — cast once, generically
module _ {Ξ : Ctx} {j f a' g' a : RTm ⌊ Ξ ⌋} where
  private
    B1 : RTy (⌊ Ξ ⌋ ∙)
    B1 = Π (KCtx (pd (renTm vs j))) (Π (K 0 (renTm vs (renTm vs j))) (Desc I∋))
    B2 : RTy (⌊ Ξ ⌋ ∙)
    B2 = Π (K 0 (renTm vs j)) (Desc I∋)
    e1 : subTy (single a') B1 ≡ Π (KCtx (pd j)) B2
    e1 = cong₂ Π (trans (KCtx-sub (single a') (pd (renTm vs j)))
                        (cong (λ z → KCtx (pd z)) {x = subTm (single a') (renTm vs j)} {y = j} (wk-cancel-tm a' j)))
                 (cong₂ Π (trans (SK-sub (extS (single a')) KSig 0 (renTm vs (renTm vs j)))
                                 (cong (K 0) {x = subTm (extS (single a')) (renTm vs (renTm vs j))} {y = renTm vs j}
                                       (trans (wk-sub (single a') (renTm vs j)) (cong (renTm vs) (wk-cancel-tm a' j)))))
                          (Desc∋-sub (extS (extS (single a')))))
    e2 : subTy (single g') B2 ≡ Π (K 0 j) (Desc I∋)
    e2 = cong₂ Π (trans (SK-sub (single g') KSig 0 (renTm vs j)) (cong (K 0) {x = subTm (single g') (renTm vs j)} {y = j} (wk-cancel-tm g' j)))
                 (Desc∋-sub (extS (single g')))
  ⊢XBapp : Ξ ⊢ f ∷ XB j → Ξ ⊢ a' ∷ K 0 (pd j) → Ξ ⊢ g' ∷ KCtx (pd j) → Ξ ⊢ a ∷ K 0 j →
           Ξ ⊢ app (app (app f a') g') a ∷ Desc I∋
  ⊢XBapp df da' dg' da = ⊢-cast {Ξ} {app (app (app f a') g') a} {subTy (single a) (Desc I∋)} {Desc I∋} (Desc∋-sub (single a)) f3
    where
      f1 : Ξ ⊢ app f a' ∷ Π (KCtx (pd j)) B2
      f1 = ⊢-cast {Ξ} {app f a'} {subTy (single a') B1} {Π (KCtx (pd j)) B2} e1
                  (⊢app {Ξ} {K 0 (pd j)} {B1} {f} {a'} df da')
      f2 : Ξ ⊢ app (app f a') g' ∷ Π (K 0 j) (Desc I∋)
      f2 = ⊢-cast {Ξ} {app (app f a') g'} {subTy (single g') B2} {Π (K 0 j) (Desc I∋)} e2
                  (⊢app {Ξ} {KCtx (pd j)} {B2} {app f a'} {g'} f1 dg')
      f3 : Ξ ⊢ app (app (app f a') g') a ∷ subTy (single a) (Desc I∋)
      f3 = ⊢app {Ξ} {K 0 j} {Desc I∋} {app (app f a') g'} {a} f2 da

-- the inverse of `pdK`/`pdCtx`
unpdK : {Θ : Ctx} {m t : RTm ⌊ Θ ⌋} → Θ ⊢ t ∷ K 0 m → Θ ⊢ t ∷ K 0 (pd (nsuc m))
unpdK {Θ} {m} {t} dt =
  ⊢conv {Θ} {t} {K 0 (subTm (single (pd m)) (renTm vs m))} {K 0 (pd (nsuc m))}
        (⊢-cast {Θ} {t} {K 0 m} {K 0 (subTm (single (pd m)) (renTm vs m))}
                (cong (K 0) {x = m} {y = subTm (single (pd m)) (renTm vs m)} (sym (wk-cancel-tm (pd m) m))) dt)
        (csymᵀ (credᵀ (ξ-SK (natrec-suc nzero (var (vs vz)) m))))

unpdCtx : {Θ : Ctx} {m t : RTm ⌊ Θ ⌋} → Θ ⊢ t ∷ KCtx m → Θ ⊢ t ∷ KCtx (pd (nsuc m))
unpdCtx {Θ} {m} {t} dt =
  ⊢conv {Θ} {t} {KCtx (subTm (single (pd m)) (renTm vs m))} {KCtx (pd (nsuc m))}
        (⊢-cast {Θ} {t} {KCtx m} {KCtx (subTm (single (pd m)) (renTm vs m))}
                (cong KCtx {x = m} {y = subTm (single (pd m)) (renTm vs m)} (sym (wk-cancel-tm (pd m) m))) dt)
        (csymᵀ (credᵀ (ξ-IMuⁱ (natrec-suc nzero (var (vs vz)) m))))

------------------------------------------------------------------------
-- 3b. The context's case.  Motive: G(j, g) = Fin j → Ty j → Desc
------------------------------------------------------------------------

GM : RTy ((Γ ∙) ∙)
GM = Π (FinI (var (vs vz))) (Π (K 0 (var (vs (vs vz)))) (Desc I∋))

GB : RTm Γ → RTy Γ
GB j = Π (FinI j) (Π (K 0 (renTm vs j)) (Desc I∋))

GM-sub : {Δ Θ : Cx} (τ : Sub ((Δ ∙) ∙) Θ) → subTy τ (GM {Δ}) ≡ GB (τ (vs vz))
GM-sub τ = cong₂ Π refl (cong₂ Π (SK-sub (extS τ) KSig 0 (var (vs (vs vz)))) (Desc∋-sub (extS (extS τ))))

⊢GM : {Θ : Ctx} → motCtx Θ ⌜Nat⌝ CtxD ⊢ty GM
⊢GM = ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢var (there here))) (ty-Π (tyK (⊢var (there (there here)))) (ty-Desc ⊢I∋))

-- at 0 (binders payload, hypotheses, x, A): the empty context has no variable, so NO row
gz : RTm Γ
gz = lam (lam (lam (lam (rows []))))

-- at suc m (binders m | payload (Γ', A'), hypotheses, x, A): case on the variable
gs : RTm (Γ ∙)
gs = lam (lam (lam (lam (app (app (app (ielim FinD (nsuc (var (vs (vs (vs (vs vz)))))) xM (var (vs vz)))
                                        (fst (snd (var (vs (vs (vs vz)))))))
                                   (fst (var (vs (vs (vs vz))))))
                              (var vz)))))

gM : RTm Γ
gM = methN (methAt (gz ∷ [])) (methAt (gs ∷ []))

-- ★ THE FIBRE FUNCTION
D∋ : RTm Γ
D∋ = lam (app (app (ielim CtxD (fst (var vz)) gM (fst (snd (var vz)))) (fst (snd (snd (var vz)))))
              (snd (snd (snd (var vz)))))

K∋ : RTm Γ → RTy Γ
K∋ i = IMu I∋ D∋ i

module _ {Θ : Ctx} where
  private
    HZ : Ctx
    HZ = HypAt Θ ⌜Nat⌝ (DN ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ) GM (single nzero) emptyT
    HS : Ctx
    HS = HypAt (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs CtxD) (wk1M GM) τS extT

    GM-at0 : subTy (atS nzero (conₗ 0 (var (vs vz)))) (GM {⌊ Θ ⌋}) ≡ GB nzero
    GM-at0 = GM-sub (atS nzero (conₗ 0 (var (vs vz))))

    GM-atS : subTy (atS (nsuc (var vz)) (conₗ 0 (var (vs vz)))) (wk1M (GM {⌊ Θ ⌋})) ≡ GB (nsuc (var (vs (vs vz))))
    GM-atS = trans {x = subTy (atS (nsuc (var vz)) (conₗ 0 (var (vs vz)))) (wk1M (GM {⌊ Θ ⌋}))}
                   {y = subTy (atS (nsuc (var vz)) (conₗ 0 (var (vs vz))) ₛ∘ᵣ extR (extR vs)) GM}
                   {z = GB (nsuc (var (vs (vs vz))))}
                   (subTy-renTy {σ = atS (nsuc (var vz)) (conₗ 0 (var (vs vz)))} {ρ = extR (extR vs)} GM)
                   (GM-sub (atS (nsuc (var vz)) (conₗ 0 (var (vs vz))) ₛ∘ᵣ extR (extR vs)))

    dnz : {Ξ : Ctx} → Ξ ⊢ nzero ∷ El ⌜Nat⌝
    dnz = ⊢conv ⊢nzero (csymᵀ elNat)

    bz' : HZ ⊢ lam (lam (rows [])) ∷ subTy (atS nzero (conₗ 0 (var (vs vz)))) GM
    bz' = ⊢-cast {HZ} {lam (lam (rows []))} {GB nzero} {subTy (atS nzero (conₗ 0 (var (vs vz)))) GM} (sym GM-at0)
            (⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD dnz) (⊢lam (tyK dnz) (⊢rows {I = I∋} {Cs = []} ⊢I∋ []ᵈ)))

    -- the successor case's body: the variable's case at `suc m`, with its convoy
    C2 : Ctx
    C2 = (HS ▹ FinI (nsuc (var (vs (vs vz))))) ▹ K 0 (nsuc (var (vs (vs (vs vz)))))
    m4 : RTm ⌊ C2 ⌋
    m4 = var (vs (vs (vs (vs vz))))
    dm4 : C2 ⊢ m4 ∷ El ⌜Nat⌝
    dm4 = ⊢var (there (there (there (there here))))
    dPay : HS ⊢ var (vs vz) ∷ PayN (vs ᵣ∘ₛ (vs ᵣ∘ₛ τS)) extT (renTm vs (renTm vs ⌜Nat⌝)) (renTm vs (renTm vs (renTm vs CtxD)))
    dPay = ⊢payAt {Γ = Θ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {D = renTm vs CtxD} {M = wk1M GM} {σ = τS} {T = extT}
    eD : renTm vs (renTm vs (renTm vs CtxD)) ≡ CtxD {⌊ HS ⌋}
    eD = trans (cong (renTm vs) {x = renTm vs (renTm vs CtxD)} {y = CtxD}
                     (trans (cong (renTm vs) {x = renTm vs CtxD} {y = CtxD} (CtxD-ren vs)) (CtxD-ren vs)))
               (CtxD-ren vs)
    dG0 : HS ⊢ fst (var (vs vz)) ∷ KCtx (var (vs (vs vz)))
    dG0 = extFst {HS} {⌊ Θ ⌋} {vs ᵣ∘ₛ (vs ᵣ∘ₛ τS)} {renTm vs (renTm vs (renTm vs CtxD))} {var (vs vz)} eD dPay
    dA0 : HS ⊢ fst (snd (var (vs vz))) ∷ K 0 (var (vs (vs vz)))
    dA0 = extSnd {HS} {⌊ Θ ⌋} {vs ᵣ∘ₛ (vs ᵣ∘ₛ τS)} {renTm vs (renTm vs (renTm vs CtxD))} {var (vs vz)} eD dPay
    dG' : C2 ⊢ fst (var (vs (vs (vs vz)))) ∷ KCtx (pd (nsuc m4))
    dG' = unpdCtx {C2} {m4} (⊢wkCtx {HS ▹ FinI (nsuc (var (vs (vs vz))))} {K 0 (nsuc (var (vs (vs (vs vz)))))}
                               (⊢wkCtx {HS} {FinI (nsuc (var (vs (vs vz))))} dG0))
    dA' : C2 ⊢ fst (snd (var (vs (vs (vs vz))))) ∷ K 0 (pd (nsuc m4))
    dA' = unpdK {C2} {m4} (⊢wkSK {Γ = HS ▹ FinI (nsuc (var (vs (vs vz))))} {B = K 0 (nsuc (var (vs (vs (vs vz)))))} {sg = KSig} {s = 0}
                            (⊢wkSK {Γ = HS} {B = FinI (nsuc (var (vs (vs vz))))} {sg = KSig} {s = 0} dA0))
    dx : C2 ⊢ var (vs vz) ∷ FinI (nsuc m4)
    dx = ⊢wk {HS ▹ FinI (nsuc (var (vs (vs vz))))} {K 0 (nsuc (var (vs (vs (vs vz)))))} {var vz} {FinI (nsuc (var (vs (vs (vs vz)))))} (⊢var here)
    dA : C2 ⊢ var vz ∷ K 0 (nsuc m4)
    dA = hereSK {Γ = HS ▹ FinI (nsuc (var (vs (vs vz))))} {sg = KSig} {s = 0} {d = nsuc (var (vs (vs (vs vz))))}
    d1 : C2 ⊢ ielim FinD (nsuc m4) xM (var (vs vz)) ∷ iinst (nsuc m4) (var (vs vz)) XM
    d1 = ⊢ielim {C2} {⌜Nat⌝} {FinD} {XM} {xM} {nsuc m4} {var (vs vz)} ⊢⌜Nat⌝ ⊢FinD ⊢XM ⊢xM (⊢isuc dm4) dx
    eX : iinst (nsuc m4) (var (vs vz)) XM ≡ XB (nsuc m4)
    eX = trans {x = iinst (nsuc m4) (var (vs vz)) XM} {y = subTy (single (var (vs vz)) ∘ₛ extS (single (nsuc m4))) XM}
               {z = XB (nsuc m4)}
               (subTy-subTy {τ = single (var (vs vz))} {σ = extS (single (nsuc m4))} XM)
               (XM-sub (single (var (vs vz)) ∘ₛ extS (single (nsuc m4))))
    d2 : C2 ⊢ ielim FinD (nsuc m4) xM (var (vs vz)) ∷ XB (nsuc m4)
    d2 = ⊢-cast {C2} {ielim FinD (nsuc m4) xM (var (vs vz))} {iinst (nsuc m4) (var (vs vz)) XM} {XB (nsuc m4)} eX d1
    body : C2 ⊢ app (app (app (ielim FinD (nsuc m4) xM (var (vs vz))) (fst (snd (var (vs (vs (vs vz)))))))
                         (fst (var (vs (vs (vs vz)))))) (var vz) ∷ Desc I∋
    body = ⊢XBapp {C2} {nsuc m4} d2 dA' dG' dA

    bs' : HS ⊢ lam (lam (app (app (app (ielim FinD (nsuc m4) xM (var (vs vz))) (fst (snd (var (vs (vs (vs vz)))))))
                                   (fst (var (vs (vs (vs vz)))))) (var vz)))
             ∷ subTy (atS (nsuc (var vz)) (conₗ 0 (var (vs vz)))) (wk1M GM)
    bs' = ⊢-cast {HS} {_} {GB (nsuc (var (vs (vs vz))))} {subTy (atS (nsuc (var vz)) (conₗ 0 (var (vs vz)))) (wk1M GM)}
            (sym GM-atS)
            (⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc (⊢var (there (there here)))))
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
      perS : PerKAt (Θ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs CtxD) (wk1M GM) (nsuc (var vz))
                    (selF (subC τS ⌜ CtxS ⌝ₛ)) zero (gs ∷ [])
      perS = entN {Γ = Θ} {C0 = ⌜ CtxZ ⌝ₛ} {Ts = CtxS} {T = extT} {M = GM} dZ CtxSOK ⊢GM nthᵗ-z bs' ∷ₐ []ₐ

-- the context case's result, applied to its convoy
module _ {Ξ : Ctx} {j f x a : RTm ⌊ Ξ ⌋} where
  ⊢GBapp : Ξ ⊢ f ∷ GB j → Ξ ⊢ x ∷ FinI j → Ξ ⊢ a ∷ K 0 j → Ξ ⊢ app (app f x) a ∷ Desc I∋
  ⊢GBapp df dx da = ⊢-cast {Ξ} {app (app f x) a} {subTy (single a) (Desc I∋)} {Desc I∋} (Desc∋-sub (single a)) f2
    where
      e : subTy (single x) (Π (K 0 (renTm vs j)) (Desc I∋)) ≡ Π (K 0 j) (Desc I∋)
      e = cong₂ Π (trans (SK-sub (single x) KSig 0 (renTm vs j)) (cong (K 0) {x = subTm (single x) (renTm vs j)} {y = j} (wk-cancel-tm x j)))
                  (Desc∋-sub (extS (single x)))
      f1 : Ξ ⊢ app f x ∷ Π (K 0 j) (Desc I∋)
      f1 = ⊢-cast {Ξ} {app f x} {subTy (single x) (Π (K 0 (renTm vs j)) (Desc I∋))} {Π (K 0 j) (Desc I∋)} e
                  (⊢app {Ξ} {FinI j} {Π (K 0 (renTm vs j)) (Desc I∋)} {f} {x} df dx)
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
  dx0 : Ξ ⊢ x0 ∷ FinI d0
  dx0 = ⊢conv (⊢fst s2) (credᵀ El-⌜IMu⌝)
  da0 : Ξ ⊢ a0 ∷ K 0 d0
  da0 = ⊢conv (⊢-cast {Ξ} {a0} {subTy (single x0) (El B3)} {El (⌜Ty⌝ d0)} eqB3 (⊢snd s2)) (credᵀ El-⌜Ty⌝)

------------------------------------------------------------------------
-- 4. ★ THE FAMILY IS WELL FORMED.
------------------------------------------------------------------------

module _ {Θ : Ctx} where
  private
    Ξ : Ctx
    Ξ = Θ ▹ El I∋
    dv : Ξ ⊢ var vz ∷ El I∋
    dv = ⊢-cast {Ξ} {var vz} {renTy vs (El I∋)} {El I∋} (cong El (I∋-ren vs)) (⊢var here)
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
