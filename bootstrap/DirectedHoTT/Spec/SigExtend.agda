-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ SIGNATURE EXTENSION (PLAN-REF, D082).
--
-- The signature is the definition context; `𝒮 ⊑ᴰ 𝒮'` is context
-- extension: every name of `𝒮` is a name of `𝒮'`, declared with the same
-- type and defined by the same body.  Reduction and typing are monotone
-- along it (`Metatheory/SigExt`: δ fires only below the size, so a step
-- under `𝒮` is a step under `𝒮'`).
--
-- A development that USES names takes "a signature containing them" as
-- its hypothesis — e.g. the Knot citing the core's entries (`Knot/PwCore`)
-- is over any `𝒮` with `kernel core ⊑ᴰ 𝒮`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.SigExtend where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax using ( Defs; _<ˢ_ )

infix 4 _⊑ᴰ_
record _⊑ᴰ_ (𝒮 𝒮' : Defs) : Set where
  field
    inc   : ∀ {d} → d <ˢ Defs.size 𝒮 → d <ˢ Defs.size 𝒮'
    type≡ : ∀ {d} → d <ˢ Defs.size 𝒮 → Defs.type 𝒮 d ≡ Defs.type 𝒮' d
    body≡ : ∀ {d} → d <ˢ Defs.size 𝒮 → Defs.body 𝒮 d ≡ Defs.body 𝒮' d

⊑ᴰ-refl : {𝒮 : Defs} → 𝒮 ⊑ᴰ 𝒮
⊑ᴰ-refl = record { inc = λ p → p ; type≡ = λ _ → refl ; body≡ = λ _ → refl }
