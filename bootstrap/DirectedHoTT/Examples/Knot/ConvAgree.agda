-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ THE CONVERSIONS ARE FAITHFUL (PLAN-FAITHFUL F5,
-- `≅`/`≅ᵀ`): every Spec conversion maps to a Knot inhabitant AT THE QUOTED
-- JUDGEMENT.  `Knot/ConvCon`'s constructors are generic in the subject's
-- head, so each case takes the quoted subject's HEAD VIEW (`Knot/QView`),
-- builds at `conₗ k p`, and transports back along the view's `refl`-born
-- equation.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.ConvAgree (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf
open import DirectedHoTT.Examples.Knot.QView 𝒮 wf
open import DirectedHoTT.Examples.Knot.Red 𝒮 wf using ( El-⌜⟶⌝; K⟶ )
open import DirectedHoTT.Examples.Knot.RedT 𝒮 wf using ( El-⌜⟶ᵀ⌝; K⟶ᵀ )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf using ( K≅; K≅ᵀ )
open import DirectedHoTT.Examples.Knot.ConvCon 𝒮 wf
open import DirectedHoTT.Examples.Knot.RedAgree 𝒮 wf using ( enRed )
open import DirectedHoTT.Examples.Knot.RedTAgree 𝒮 wf using ( enRedT )

------------------------------------------------------------------------
-- 1. t ≅ u
------------------------------------------------------------------------

enConv : {Γ : Cx} {t u : RTm Γ} → t ≅ u → {Θ : Ctx} → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ (dep Γ) (quoteTm t) (quoteTm u))
enConv {Γ} {t} {u} (cred r) {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ (dep Γ) T (quoteTm u))) (sym eq)
    (_ , cred≅ nh (⊢dep' Γ) dp (⊢quoteTm u)
               (⊢conv (subst (λ T → Θ ⊢ Σ.fst (enRed r) ∷ K⟶ (dep Γ) T (quoteTm u)) eq (Σ.snd (enRed r))) (csymᵀ El-⌜⟶⌝)))
  where open HeadV (qviewTm t {Θ})
enConv {Γ} {t} {.t} crfl {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ (dep Γ) T T)) (sym eq) (_ , crfl≅ nh (⊢dep' Γ) dp)
  where open HeadV (qviewTm t {Θ})
enConv {Γ} {t} {u} (csym d) {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ (dep Γ) T (quoteTm u))) (sym eq)
    (_ , csym≅ nh (⊢dep' Γ) dp (⊢quoteTm u)
               (subst (λ T → Θ ⊢ Σ.fst (enConv d) ∷ K≅ (dep Γ) (quoteTm u) T) eq (Σ.snd (enConv d))))
  where open HeadV (qviewTm t {Θ})
enConv {Γ} {t} {u} (ctrn {u = v} d₁ d₂) {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ (dep Γ) T (quoteTm u))) (sym eq)
    (_ , ctrn≅ nh (⊢dep' Γ) dp (⊢quoteTm u) (⊢quoteTm v)
               (subst (λ T → Θ ⊢ Σ.fst (enConv d₁) ∷ K≅ (dep Γ) T (quoteTm v)) eq (Σ.snd (enConv d₁)))
               (Σ.snd (enConv d₂)))
  where open HeadV (qviewTm t {Θ})

------------------------------------------------------------------------
-- 2. A ≅ᵀ B
------------------------------------------------------------------------

enConvT : {Γ : Cx} {A B : RTy Γ} → A ≅ᵀ B → {Θ : Ctx} → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ᵀ (dep Γ) (quoteTy A) (quoteTy B))
enConvT {Γ} {A} {B} (credᵀ r) {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ᵀ (dep Γ) T (quoteTy B))) (sym eq)
    (_ , cred≅ᵀ nh (⊢dep' Γ) dp (⊢quoteTy B)
                (⊢conv (subst (λ T → Θ ⊢ Σ.fst (enRedT r) ∷ K⟶ᵀ (dep Γ) T (quoteTy B)) eq (Σ.snd (enRedT r))) (csymᵀ El-⌜⟶ᵀ⌝)))
  where open HeadV (qviewTy A {Θ})
enConvT {Γ} {A} {.A} crflᵀ {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ᵀ (dep Γ) T T)) (sym eq) (_ , crfl≅ᵀ nh (⊢dep' Γ) dp)
  where open HeadV (qviewTy A {Θ})
enConvT {Γ} {A} {B} (csymᵀ d) {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ᵀ (dep Γ) T (quoteTy B))) (sym eq)
    (_ , csym≅ᵀ nh (⊢dep' Γ) dp (⊢quoteTy B)
                (subst (λ T → Θ ⊢ Σ.fst (enConvT d) ∷ K≅ᵀ (dep Γ) (quoteTy B) T) eq (Σ.snd (enConvT d))))
  where open HeadV (qviewTy A {Θ})
enConvT {Γ} {A} {B} (ctrnᵀ {B = V} d₁ d₂) {Θ} =
  subst (λ T → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K≅ᵀ (dep Γ) T (quoteTy B))) (sym eq)
    (_ , ctrn≅ᵀ nh (⊢dep' Γ) dp (⊢quoteTy B) (⊢quoteTy V)
                (subst (λ T → Θ ⊢ Σ.fst (enConvT d₁) ∷ K≅ᵀ (dep Γ) T (quoteTy V)) eq (Σ.snd (enConvT d₁)))
                (Σ.snd (enConvT d₂)))
  where open HeadV (qviewTy A {Θ})
