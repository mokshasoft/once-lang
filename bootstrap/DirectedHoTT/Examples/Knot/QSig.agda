-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ the QUOTED SIGNATURE (PLAN-REF K2): the parameter
-- of the Knot's families.
--
--   ⌜QSig⌝ = Σ Nat (Σ (Π Nat ⌜Ty⌝₀) (Π Nat ⌜Tm⌝₀))
--   ⌜TSig⌝ = Σ ⌜QSig⌝ Nat           (typing: the signature and the bound)
--
-- a size, the declared types and the bodies — each a closed Knot type /
-- term (depth 0), selected by name.  Functions, not a list: a lookup is
-- an application, and no list type is needed.  The kernel's signature
-- (`Spec/Syntax.Defs`) mirrors it: `size`, `type`, `body`.
--
-- This module is the CODE and its typed projections only — light, so the
-- families (`RedIx`, `JudgeIx`) can take it as their parameter.  The
-- quotation of a concrete signature and its lookup reductions are
-- `Knot/QuoteSig` (they need `Unquote`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.QSig (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast; ⊢wk )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃 using ( toI )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( tag; lt-z; lt-s; _,ₚ_ )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. THE CODE.
------------------------------------------------------------------------

-- closed Knot types / terms (depth 0); OPAQUE: they carry the description
--   (`context-form-mismatch-opaque`)
opaque
  ⌜Ty⌝₀ ⌜Tm⌝₀ : RTm Δ
  ⌜Ty⌝₀ = ⌜IMu⌝ (SI 2) KD ((tag 0) ,ₚ nzero)
  ⌜Tm⌝₀ = ⌜IMu⌝ (SI 2) KD ((tag 1) ,ₚ nzero)

  ⌜Ty⌝₀-sub : (σ : Sub Δ Θ) → subTm σ (⌜Ty⌝₀ {Δ}) ≡ ⌜Ty⌝₀
  ⌜Ty⌝₀-sub σ = cong (λ D → ⌜IMu⌝ (SI 2) D ((tag 0) ,ₚ nzero)) (SD-sub σ KSig)

  ⌜Tm⌝₀-sub : (σ : Sub Δ Θ) → subTm σ (⌜Tm⌝₀ {Δ}) ≡ ⌜Tm⌝₀
  ⌜Tm⌝₀-sub σ = cong (λ D → ⌜IMu⌝ (SI 2) D ((tag 1) ,ₚ nzero)) (SD-sub σ KSig)

  ⊢⌜Ty⌝₀ : {Γ : Ctx} → Γ ⊢ ⌜Ty⌝₀ ∷ U
  ⊢⌜Ty⌝₀ = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix lt-z (toI ⊢nzero))

  ⊢⌜Tm⌝₀ : {Γ : Ctx} → Γ ⊢ ⌜Tm⌝₀ ∷ U
  ⊢⌜Tm⌝₀ = ⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix (lt-s lt-z) (toI ⊢nzero))

  El-⌜Ty⌝₀ : El (⌜Ty⌝₀ {Δ}) ⟶ᵀ K 0 nzero
  El-⌜Ty⌝₀ = El-⌜SK⌝

  El-⌜Tm⌝₀ : El (⌜Tm⌝₀ {Δ}) ⟶ᵀ K 1 nzero
  El-⌜Tm⌝₀ = El-⌜SK⌝

-- the two tables, and the signature
⌜Tys⌝ ⌜Bds⌝ ⌜Tabs⌝ ⌜QSig⌝ : RTm Δ
⌜Tys⌝  = ⌜Π⌝ ⌜Nat⌝ ⌜Ty⌝₀
⌜Bds⌝  = ⌜Π⌝ ⌜Nat⌝ ⌜Tm⌝₀
⌜Tabs⌝ = ⌜Σ⌝ ⌜Tys⌝ ⌜Bds⌝
⌜QSig⌝ = ⌜Σ⌝ ⌜Nat⌝ ⌜Tabs⌝

⌜Tys⌝-sub : (σ : Sub Δ Θ) → subTm σ (⌜Tys⌝ {Δ}) ≡ ⌜Tys⌝
⌜Tys⌝-sub σ = cong (⌜Π⌝ ⌜Nat⌝) (⌜Ty⌝₀-sub (extS σ))

⌜Bds⌝-sub : (σ : Sub Δ Θ) → subTm σ (⌜Bds⌝ {Δ}) ≡ ⌜Bds⌝
⌜Bds⌝-sub σ = cong (⌜Π⌝ ⌜Nat⌝) (⌜Tm⌝₀-sub (extS σ))

⌜Tabs⌝-sub : (σ : Sub Δ Θ) → subTm σ (⌜Tabs⌝ {Δ}) ≡ ⌜Tabs⌝
⌜Tabs⌝-sub σ = cong₂ ⌜Σ⌝ (⌜Tys⌝-sub σ) (⌜Bds⌝-sub (extS σ))

⌜QSig⌝-sub : (σ : Sub Δ Θ) → subTm σ (⌜QSig⌝ {Δ}) ≡ ⌜QSig⌝
⌜QSig⌝-sub σ = cong (⌜Σ⌝ ⌜Nat⌝) (⌜Tabs⌝-sub (extS σ))

⊢⌜Tys⌝ : {Γ : Ctx} → Γ ⊢ ⌜Tys⌝ ∷ U
⊢⌜Tys⌝ = ⊢⌜Π⌝ ⊢⌜Nat⌝ ⊢⌜Ty⌝₀

⊢⌜Bds⌝ : {Γ : Ctx} → Γ ⊢ ⌜Bds⌝ ∷ U
⊢⌜Bds⌝ = ⊢⌜Π⌝ ⊢⌜Nat⌝ ⊢⌜Tm⌝₀

⊢⌜Tabs⌝ : {Γ : Ctx} → Γ ⊢ ⌜Tabs⌝ ∷ U
⊢⌜Tabs⌝ = ⊢⌜Σ⌝ ⊢⌜Tys⌝ ⊢⌜Bds⌝

⊢⌜QSig⌝ : {Γ : Ctx} → Γ ⊢ ⌜QSig⌝ ∷ U
⊢⌜QSig⌝ = ⊢⌜Σ⌝ ⊢⌜Nat⌝ ⊢⌜Tabs⌝

------------------------------------------------------------------------
-- 2. THE PROJECTIONS: `size`, `types`, `bodies` (cf. `Defs`).
------------------------------------------------------------------------

sizeQ : RTm Δ → RTm Δ
sizeQ q = fst q

typesQ bodiesQ : RTm Δ → RTm Δ → RTm Δ
typesQ q d  = app (fst (snd q)) d
bodiesQ q d = app (snd (snd q)) d

module _ {Ξ : Ctx} {q : RTm ⌊ Ξ ⌋} (dq : Ξ ⊢ q ∷ El ⌜QSig⌝) where
  private
    dΣ : Ξ ⊢ q ∷ Σ' (El ⌜Nat⌝) (El ⌜Tabs⌝)
    dΣ = ⊢conv dq (credᵀ (El-⌜Σ⌝ ⌜Nat⌝ ⌜Tabs⌝))

    dtabs : Ξ ⊢ snd q ∷ Σ' (El ⌜Tys⌝) (El ⌜Bds⌝)
    dtabs = ⊢conv (⊢-cast {Ξ} {snd q} {subTy (single (fst q)) (El ⌜Tabs⌝)} {El ⌜Tabs⌝}
                          (cong El (⌜Tabs⌝-sub (single (fst q)))) (⊢snd dΣ))
                  (credᵀ (El-⌜Σ⌝ ⌜Tys⌝ ⌜Bds⌝))

  ⊢sizeQ : Ξ ⊢ sizeQ q ∷ El ⌜Nat⌝
  ⊢sizeQ = ⊢fst dΣ

  ⊢typesQ : {d : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ typesQ q d ∷ K 0 nzero
  ⊢typesQ {d} dd =
    ⊢conv (⊢-cast {Ξ} {typesQ q d} {subTy (single d) (El ⌜Ty⌝₀)} {El ⌜Ty⌝₀} (cong El (⌜Ty⌝₀-sub (single d)))
                  (⊢app (⊢conv (⊢fst dtabs) (credᵀ (El-⌜Π⌝ ⌜Nat⌝ ⌜Ty⌝₀))) dd))
          (credᵀ El-⌜Ty⌝₀)

  ⊢bodiesQ : {d : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ bodiesQ q d ∷ K 1 nzero
  ⊢bodiesQ {d} dd =
    ⊢conv (⊢-cast {Ξ} {bodiesQ q d} {subTy (single d) (El ⌜Tm⌝₀)} {El ⌜Tm⌝₀} (cong El (⌜Tm⌝₀-sub (single d)))
                  (⊢app (⊢conv (⊢-cast {Ξ} {snd (snd q)} {subTy (single (fst (snd q))) (El ⌜Bds⌝)} {El ⌜Bds⌝}
                                       (cong El (⌜Bds⌝-sub (single (fst (snd q))))) (⊢snd dtabs))
                               (credᵀ (El-⌜Π⌝ ⌜Nat⌝ ⌜Tm⌝₀))) dd))
          (credᵀ El-⌜Tm⌝₀)

-- a parameter weakens past a binder
⌜QSig⌝-ren : (ρ : Ren Δ Θ) → renTm ρ (⌜QSig⌝ {Δ}) ≡ ⌜QSig⌝
⌜QSig⌝-ren ρ = trans (sym (subTm-var ρ ⌜QSig⌝)) (⌜QSig⌝-sub ⟨ ρ ⟩ᵣ)

wkQ : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜QSig⌝ → (Γ ▹ B) ⊢ renTm vs t ∷ El ⌜QSig⌝
wkQ {Γ} {B} {t} dt = ⊢-cast {Γ ▹ B} {renTm vs t} {El (renTm vs ⌜QSig⌝)} {El ⌜QSig⌝} (cong El (⌜QSig⌝-ren vs))
                            (⊢wk {Γ} {B} {t} {El ⌜QSig⌝} dt)

------------------------------------------------------------------------
-- 3. ★ THE TYPING PARAMETER: the signature and the bound (`Spec/Typing`
--    is over `(𝒮)(n)`: reduction at `𝒮`, references below `n`).
------------------------------------------------------------------------

⌜TSig⌝ : RTm Δ
⌜TSig⌝ = ⌜Σ⌝ ⌜QSig⌝ ⌜Nat⌝

⌜TSig⌝-sub : (σ : Sub Δ Θ) → subTm σ (⌜TSig⌝ {Δ}) ≡ ⌜TSig⌝
⌜TSig⌝-sub σ = cong (λ X → ⌜Σ⌝ X ⌜Nat⌝) (⌜QSig⌝-sub σ)

⊢⌜TSig⌝ : {Γ : Ctx} → Γ ⊢ ⌜TSig⌝ ∷ U
⊢⌜TSig⌝ = ⊢⌜Σ⌝ ⊢⌜QSig⌝ ⊢⌜Nat⌝

sigT boundT : RTm Δ → RTm Δ
sigT t   = fst t
boundT t = snd t

module _ {Ξ : Ctx} {t : RTm ⌊ Ξ ⌋} (dt : Ξ ⊢ t ∷ El ⌜TSig⌝) where
  private
    dΣ : Ξ ⊢ t ∷ Σ' (El ⌜QSig⌝) (El ⌜Nat⌝)
    dΣ = ⊢conv dt (credᵀ (El-⌜Σ⌝ ⌜QSig⌝ ⌜Nat⌝))

  ⊢sigT : Ξ ⊢ sigT t ∷ El ⌜QSig⌝
  ⊢sigT = ⊢fst dΣ

  ⊢boundT : Ξ ⊢ boundT t ∷ El ⌜Nat⌝
  ⊢boundT = ⊢snd dΣ

⌜TSig⌝-ren : (ρ : Ren Δ Θ) → renTm ρ (⌜TSig⌝ {Δ}) ≡ ⌜TSig⌝
⌜TSig⌝-ren ρ = trans (sym (subTm-var ρ ⌜TSig⌝)) (⌜TSig⌝-sub ⟨ ρ ⟩ᵣ)

wkT : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜TSig⌝ → (Γ ▹ B) ⊢ renTm vs t ∷ El ⌜TSig⌝
wkT {Γ} {B} {t} dt = ⊢-cast {Γ ▹ B} {renTm vs t} {El (renTm vs ⌜TSig⌝)} {El ⌜TSig⌝} (cong El (⌜TSig⌝-ren vs))
                            (⊢wk {Γ} {B} {t} {El ⌜TSig⌝} dt)
