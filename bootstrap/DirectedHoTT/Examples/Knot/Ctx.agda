-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — CONTEXTS, a family FIBRED OVER THE DEPTH
-- (`Lib/NatFib`, D076):
--
--     Ctx 0       = ε
--     Ctx (suc m) = Ctx m ▹ Ty m
--
-- A context is not a sort of the syntax — `_▹_` carries a type, the
-- syntax never carries a context — so it is its own family (a STRATUM),
-- indexed by the depth it binds.  Its extension field is a TYPE of the
-- Knot (`Knot/Sig`) at the predecessor depth.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.Ctx (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( conₗ; tag; nth-z; lt-z; _∷ᵈ_; []ᵈ; []; _∷_; subC; AllD; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatFib 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃 using ( toI; ⊢isuc )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf

-- the code of the Knot's types at a depth — OPAQUE: it carries the
-- description, and two syntactic forms of one context would compare it by
-- normalisation (`context-form-mismatch-opaque`).  Its interface: typing,
-- closedness, and the one reduction `El (⌜Ty⌝ d) ⟶ K 0 d`.
opaque
  ⌜Ty⌝ : {Γ : Cx} → RTm Γ → RTm Γ
  ⌜Ty⌝ d = ⌜IMu⌝ (SI 2) KD ((tag 0) ,ₚ d)

  ⊢⌜Ty⌝ : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ ⌜Ty⌝ d ∷ U
  ⊢⌜Ty⌝ dd = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix lt-z dd)

  ⌜Ty⌝-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (d : RTm Δ) → subTm σ (⌜Ty⌝ d) ≡ ⌜Ty⌝ (subTm σ d)
  ⌜Ty⌝-sub σ d = cong (λ D → ⌜IMu⌝ (SI 2) D ((tag 0) ,ₚ (subTm σ d))) (SD-sub σ KSig)

  El-⌜Ty⌝ : {Γ : Cx} {d : RTm Γ} → El (⌜Ty⌝ d) ⟶ᵀ K 0 d
  El-⌜Ty⌝ = El-⌜SK⌝

------------------------------------------------------------------------
-- 1. THE FAMILY.
------------------------------------------------------------------------

emptyT : {Γ : Cx} → Tel (Γ ∙)
emptyT = tι                                   -- ε : Ctx 0

extT : {Γ : Cx} → Tel (Γ ∙)
extT = tρ v₀ (tσ (⌜Ty⌝ v₀) tι)    -- Γ ▹ A : Ctx (suc m),  Γ : Ctx m,  A : Ty m

CtxZ CtxS : {Γ : Cx} → Tels (Γ ∙) 1
CtxZ = emptyT ∷ᵗ []ᵗ
CtxS = extT ∷ᵗ []ᵗ

CtxD : {Γ : Cx} → RTm Γ
CtxD = DN ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ

KCtx : {Γ : Cx} → RTm Γ → RTy Γ
KCtx d = IMu ⌜Nat⌝ CtxD d

module _ {Γ : Ctx} where
  CtxZOK : AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CtxZ
  CtxZOK = ok-ι ∷ᵒ []ᵒ

  extOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ extT
  extOK = ok-ρ (⊢var here) (ok-σ (⊢⌜Ty⌝ (⊢var here)) ok-ι)

  CtxSOK : AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CtxS
  CtxSOK = extOK ∷ᵒ []ᵒ

⊢CtxD : {Γ : Ctx} → Γ ⊢ CtxD ∷ DescF ⌜Nat⌝
⊢CtxD {Γ} = ⊢DN {Γ = Γ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} (allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxZ} (⊢wk ⊢⌜Nat⌝) CtxZOK)
                                               (allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxS} (⊢wk ⊢⌜Nat⌝) CtxSOK)

------------------------------------------------------------------------
-- 1½. ★ THE FAMILY IS CLOSED — proven structurally, ONCE.  A context's
--   type mentions the Knot's description; left to the checker, every
--   weakening of it normalises all 51 constructors.
------------------------------------------------------------------------

CtxS-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subC (extS σ) (⌜ CtxS {Δ} ⌝ₛ) ≡ ⌜ CtxS {Θ} ⌝ₛ
CtxS-sub σ = cong (λ X → dρ v₀ (dσ X (lam dι)) ∷ []) (⌜Ty⌝-sub (extS σ) v₀)

-- ⚠ PIN the endpoints: `DN` is not injective, and an unpinned `cong₂ DN`
--   normalises the Knot's description on the known side (27 s → 0 s)
CtxD-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (CtxD {Δ}) ≡ CtxD
CtxD-sub {Δ} {Θ} σ =
  trans {x = subTm σ (DN {Δ = Δ} ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ)}
        {y = DN (subC (extS σ) ⌜ CtxZ {Δ} ⌝ₛ) (subC (extS σ) ⌜ CtxS {Δ} ⌝ₛ)}
        {z = DN {Δ = Θ} ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ}
    (DN-sub σ ⌜ CtxZ ⌝ₛ ⌜ CtxS ⌝ₛ)
    (cong₂ DN {x = subC (extS σ) ⌜ CtxZ {Δ} ⌝ₛ} {x' = ⌜ CtxZ {Θ} ⌝ₛ}
              {y = subC (extS σ) ⌜ CtxS {Δ} ⌝ₛ} {y' = ⌜ CtxS {Θ} ⌝ₛ} refl (CtxS-sub σ))

KCtx-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) (d : RTm Δ) → renTy ρ (KCtx d) ≡ KCtx (renTm ρ d)
KCtx-ren ρ d = trans (sym (subTy-var ρ (KCtx d))) (cong₂ (IMu ⌜Nat⌝) (CtxD-sub ⟨ ρ ⟩ᵣ) (subTm-var ρ d))

⌜Ty⌝-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) (d : RTm Δ) → renTm ρ (⌜Ty⌝ d) ≡ ⌜Ty⌝ (renTm ρ d)
⌜Ty⌝-ren ρ d = trans (sym (subTm-var ρ (⌜Ty⌝ d))) (trans (⌜Ty⌝-sub ⟨ ρ ⟩ᵣ d)
                 (cong ⌜Ty⌝ {x = subTm ⟨ ρ ⟩ᵣ d} {y = renTm ρ d} (subTm-var ρ d)))

KCtx-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (d : RTm Δ) → subTy σ (KCtx d) ≡ KCtx (subTm σ d)
KCtx-sub σ d = cong (λ D → IMu ⌜Nat⌝ D (subTm σ d)) (CtxD-sub σ)

CtxD-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) → renTm ρ (CtxD {Δ}) ≡ CtxD
CtxD-ren ρ = trans (sym (subTm-var ρ CtxD)) (CtxD-sub ⟨ ρ ⟩ᵣ)

-- the typed weakenings the rows use
⊢wkCtx : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {d g : RTm ⌊ Γ ⌋} → Γ ⊢ g ∷ KCtx d → (Γ ▹ B) ⊢ renTm vs g ∷ KCtx (renTm vs d)
⊢wkCtx {Γ} {B} {d} {g} dg = ⊢-cast {Γ ▹ B} {renTm vs g} {renTy vs (KCtx d)} {KCtx (renTm vs d)} (KCtx-ren vs d) (⊢wk {Γ} {B} {g} {KCtx d} dg)

hereCtx : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → (Γ ▹ KCtx d) ⊢ v₀ ∷ KCtx (renTm vs d)
hereCtx {Γ} {d} = ⊢-cast {Γ ▹ KCtx d} {v₀} {renTy vs (KCtx d)} {KCtx (renTm vs d)} (KCtx-ren vs d) (⊢var here)

------------------------------------------------------------------------
-- 2. THE CONSTRUCTORS.
------------------------------------------------------------------------

cε : {Γ : Cx} → RTm Γ
cε = conₗ zero unit

cext : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
cext g a = conₗ zero (g ,ₚ a ,ₚ unit)

module _ {Γ : Ctx} where
  private
    dZ : AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ ⌜ CtxZ ⌝ₛ
    dZ = allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxZ} (⊢wk ⊢⌜Nat⌝) CtxZOK
    dS : AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ ⌜ CtxS ⌝ₛ
    dS = allD {Γ = Γ ▹ El ⌜Nat⌝} {I = ⌜Nat⌝} {Ts = CtxS} (⊢wk ⊢⌜Nat⌝) CtxSOK

  ⊢cε : Γ ⊢ cε ∷ KCtx nzero
  ⊢cε = ⊢conN-z {Γ = Γ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} {C = ⌜ emptyT ⌝ᵗ} {p = unit} dZ dS nth-z
          (⊢payι {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {unit} ⊢unit)

  -- the extension's telescope at `m`, with the type code's substitution CAST
  --   (left to the checker it normalises the Knot's description)
  extAt : (m : RTm ⌊ Γ ⌋) → subTm (single m) ⌜ extT {⌊ Γ ⌋} ⌝ᵗ ≡ ⌜ tρ m (tσ (⌜Ty⌝ m) tι) ⌝ᵗ
  extAt m = cong (λ X → dρ m (dσ X (lam dι))) (⌜Ty⌝-sub (single m) v₀)

  ⊢cext : {m g a : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ El ⌜Nat⌝ →
          Γ ⊢ g ∷ KCtx m → Γ ⊢ a ∷ K 0 m → Γ ⊢ cext g a ∷ KCtx (nsuc m)
  ⊢cext {m} {g} {a} dm dg da =
    ⊢conN-s {Γ = Γ} {C0 = ⌜ CtxZ ⌝ₛ} {CS = ⌜ CtxS ⌝ₛ} {C = ⌜ extT ⌝ᵗ} {m = m} {p = pair g (a ,ₚ unit)} dZ dS nth-z dm
      (⊢-cast {Γ} {pair g (a ,ₚ unit)} {El (dpay ⌜Nat⌝ CtxD ⌜ tρ m (tσ (⌜Ty⌝ m) tι) ⌝ᵗ)}
              {El (dpay ⌜Nat⌝ CtxD (subTm (single m) ⌜ extT ⌝ᵗ))}
              (cong (λ C → El (dpay ⌜Nat⌝ CtxD C)) (sym (extAt m))) dp)
    where
      dp : Γ ⊢ pair g (a ,ₚ unit) ∷ El (dpay ⌜Nat⌝ CtxD ⌜ tρ m (tσ (⌜Ty⌝ m) tι) ⌝ᵗ)
      dp = ⊢payρ {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {m} {g} {pair a unit} {tσ (⌜Ty⌝ m) tι}
             (ok-ρ dm (ok-σ (⊢⌜Ty⌝ dm) ok-ι)) dg
             (⊢payσ {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {⌜Ty⌝ m} {a} {unit} {tι}
                (ok-σ (⊢⌜Ty⌝ dm) ok-ι) (⊢conv da (csymᵀ (credᵀ El-⌜Ty⌝)))
                (⊢payι {Γ} {⌜Nat⌝} {CtxD} ⊢⌜Nat⌝ ⊢CtxD {unit} ⊢unit))

------------------------------------------------------------------------
-- 2½. A METHOD'S VIEW of an extension's payload (under any pending
--   substitution, as `Lib/TelAt.⊢payAt` presents it): its two fields.
------------------------------------------------------------------------

module _ {Θ : Ctx} {Δ : Cx} {σ : Sub (Δ ∙) ⌊ Θ ⌋} {D p : RTm ⌊ Θ ⌋} (eD : D ≡ CtxD) where
  private
    fp = fst p
    T2 : RTy ⌊ Θ ⌋
    T2 = subTy (single fp) (El (subTm (vs ᵣ∘ₛ σ) (⌜Ty⌝ v₀)))
    eT : T2 ≡ El (⌜Ty⌝ (σ vz))
    eT = cong El (trans {x = subTm (single fp) (subTm (vs ᵣ∘ₛ σ) (⌜Ty⌝ v₀))}
                        {y = subTm (single fp) (⌜Ty⌝ (renTm vs (σ vz)))} {z = ⌜Ty⌝ (σ vz)}
                        (cong (subTm (single fp)) (⌜Ty⌝-sub (vs ᵣ∘ₛ σ) v₀))
                        (trans (⌜Ty⌝-sub (single fp) (renTm vs (σ vz)))
                               (cong ⌜Ty⌝ {x = subTm (single fp) (renTm vs (σ vz))} {y = σ vz} (wk-cancel-tm fp (σ vz)))))

  extFst : Θ ⊢ p ∷ PayN σ extT ⌜Nat⌝ D → Θ ⊢ fst p ∷ KCtx (σ vz)
  extFst dp = ⊢-cast {Θ} {fst p} {IMu ⌜Nat⌝ D (σ vz)} {KCtx (σ vz)} (cong (λ X → IMu ⌜Nat⌝ X (σ vz)) eD) (⊢fst dp)

  extSnd : Θ ⊢ p ∷ PayN σ extT ⌜Nat⌝ D → Θ ⊢ fst (snd p) ∷ K 0 (σ vz)
  extSnd dp = ⊢conv (⊢-cast {Θ} {fst (snd p)} {T2} {El (⌜Ty⌝ (σ vz))} eT (⊢fst (⊢snd dp))) (credᵀ El-⌜Ty⌝)

------------------------------------------------------------------------
-- 3. ★ THE QUOTATION of a kernel context, typed at its depth.
------------------------------------------------------------------------

quoteCtx : Ctx → {Θ : Cx} → RTm Θ
quoteCtx ◇       = cε
quoteCtx (Γ ▹ A) = cext (quoteCtx Γ) (quoteTy A)

⊢quoteCtx : (Γ : Ctx) {Θ : Ctx} → Θ ⊢ quoteCtx Γ ∷ KCtx (dep ⌊ Γ ⌋)
⊢quoteCtx ◇       = ⊢cε
⊢quoteCtx (Γ ▹ A) = ⊢cext (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A)
