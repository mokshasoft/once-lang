-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ CONVERSION OF WELL-TYPED TERMS IS DECIDABLE.
--                      No parameters left.
--
-- `dec-conv-typed` (Metatheory/Fundamental) decided `_≅_` for well-typed
-- terms given ONE input — decidable syntactic equality of raw terms.
-- `Algorithm/DecEq` supplies it, so this module is the closed theorem.
--
-- ⚠ SCOPE: TERM conversion `_≅_`.  TYPE conversion `_≅ᵀ_`, which `⊢conv`
--   uses and a type checker must decide, is NOT covered — types have only
--   weak-head forms (`fund-ty`).  That is the next piece of the checker.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Algorithm.DecideConversionTyped (𝒮 : KSig) (wf : WfK 𝒮) where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax

-- ★ PLAN-REF: at a well-formed signature (all its names)
private
  n = KSig.size 𝒮
  ok = Entries.sigOK 𝒮 n wf
  refs = Entries.refsOK 𝒮 n (λ p → p) wf

open import DirectedHoTT.Spec.Typing 𝒮 n
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _≅_; ⊢ctx_; c-◇; c-▹
        ; ⊢var; ⊢lam; ⊢app; here; there; ty-base; ⊢appex )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Tm_ )
open import DirectedHoTT.Metatheory.Fundamental 𝒮 n ok refs using ( dec-conv-typed )

private
  variable
    Γ : Ctx

decide-≅ : {t u : RTm ⌊ Γ ⌋} {A B : RTy ⌊ Γ ⌋} →
           ⊢ctx Γ → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B → Dec (t ≅ u)
decide-≅ = dec-conv-typed _≟Tm_

------------------------------------------------------------------------
-- NON-VACUITY — it RUNS, and answers both ways.
------------------------------------------------------------------------

private
  isYes : {P : Set} → Dec P → Bool
  isYes (yes _) = true
  isYes (no  _) = false

  Γ₁ : Ctx
  Γ₁ = ◇ ▹ base

  Γ₂ : Ctx
  Γ₂ = (◇ ▹ base) ▹ base

  wΓ₁ : ⊢ctx Γ₁
  wΓ₁ = c-▹ c-◇ ty-base

  wΓ₂ : ⊢ctx Γ₂
  wΓ₂ = c-▹ wΓ₁ ty-base

  -- (λx.x) y ≅ y — a β-redex against its reduct: YES.
  redex-yes : isYes (decide-≅ wΓ₁ ⊢appex (⊢var here)) ≡ true
  redex-yes = refl

  -- x ≅ y for two distinct variables: NO.
  vars-no : isYes (decide-≅ wΓ₂ (⊢var here) (⊢var (there here))) ≡ false
  vars-no = refl
