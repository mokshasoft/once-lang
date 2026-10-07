-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ CONTEXT LOOKUP IS FAITHFUL (PLAN-FAITHFUL F5, `∋`):
-- every Spec `Γ ∋ x ∷ A` maps to a Knot inhabitant at the quoted judgement.
-- The Knot's rows state the looked-up type as `wk 0 m ⌜A⌝`, the Spec as
-- `renTy vs A`; the Id-premise is `idrefl`, converted by `wk-agree-ty`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.LookupAgree (𝒮 : Defs) (wf : WfK 𝒮) where



open import normalizer.Syntax.Types using ( Σ; _,_ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; stepᵀ; ⟶ᵀ*-Idʳ )
open import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( wk )
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( toTy; K∋; ix∋ )
open import DirectedHoTT.Examples.Knot.LookupCon 𝒮 wf using ( ⊢here∋; ⊢there∋ )
open import DirectedHoTT.Examples.Knot.OpAgree 𝒮 wf using ( wk-agree-ty )

-- the Id-premise `a ≡ wk a'`, where the Spec's `a` IS `renTy vs A`
private
  idWk : {Γ : Cx} (A : RTy Γ) {Θ : Ctx} →
         Θ ⊢ idrefl (⌜Ty⌝ (dep (Γ ∙))) (quoteTy (renTy vs A)) ∷ El (⌜Id⌝ (⌜Ty⌝ (dep (Γ ∙))) (quoteTy (renTy vs A)) (wk 0 (dep Γ) (quoteTy A)))
  idWk {Γ} A = ⊢conv (⊢idrefl (⊢⌜Ty⌝ (⊢dep' (Γ ∙))) (toTy (⊢quoteTy (renTy vs A))))
                     (csymᵀ (red→≅ᵀ (stepᵀ (El-⌜Id⌝ _ _ _) (⟶ᵀ*-Idʳ (wk-agree-ty A)))))

enLk : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ∋ x ∷ A → {Θ : Ctx} →
       Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K∋ (ix∋ (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteVar x) (quoteTy A)))
enLk (here {Γ} {A}) =
  _ , ⊢here∋ (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy A) (⊢quoteTy (renTy vs A)) (idWk A)
enLk (there {Γ} {A} {B} {x} d) =
  _ , ⊢there∋ (⊢dep' ⌊ Γ ⌋) (⊢quoteCtx Γ) (⊢quoteTy B) (⊢quoteVar x) (⊢quoteTy (renTy vs A)) (⊢quoteTy A)
              (Σ.snd (enLk d)) (idWk A)
