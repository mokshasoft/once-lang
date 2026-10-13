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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax using ( Defs; Def; kType; kBody; _▸ᴷ_; _<ˢ_; <-there; lookupK-▸ )

infix 4 _⊑ᴰ_
record _⊑ᴰ_ (𝒮 𝒮' : Defs) : Set where
  field
    inc   : ∀ {d} → d <ˢ Defs.size 𝒮 → d <ˢ Defs.size 𝒮'
    type≡ : ∀ {d} → d <ˢ Defs.size 𝒮 → Defs.type 𝒮 d ≡ Defs.type 𝒮' d
    body≡ : ∀ {d} → d <ˢ Defs.size 𝒮 → Defs.body 𝒮 d ≡ Defs.body 𝒮' d

⊑ᴰ-refl : {𝒮 : Defs} → 𝒮 ⊑ᴰ 𝒮
⊑ᴰ-refl = record { inc = λ p → p ; type≡ = λ _ → refl ; body≡ = λ _ → refl }

-- one entry extends a signature: the names below are untouched
⊑ᴰ-▸ : {𝒮 : Defs} {e : Def} → 𝒮 ⊑ᴰ (𝒮 ▸ᴷ e)
⊑ᴰ-▸ = record { inc   = <-there
              ; type≡ = λ p → cong kType (sym (lookupK-▸ p))
              ; body≡ = λ p → cong kBody (sym (lookupK-▸ p)) }

-- extension composes
⊑ᴰ-trans : {𝒮₁ 𝒮₂ 𝒮₃ : Defs} → 𝒮₁ ⊑ᴰ 𝒮₂ → 𝒮₂ ⊑ᴰ 𝒮₃ → 𝒮₁ ⊑ᴰ 𝒮₃
⊑ᴰ-trans a b = record { inc   = λ p → _⊑ᴰ_.inc b (_⊑ᴰ_.inc a p)
                      ; type≡ = λ p → trans (_⊑ᴰ_.type≡ a p) (_⊑ᴰ_.type≡ b (_⊑ᴰ_.inc a p))
                      ; body≡ = λ p → trans (_⊑ᴰ_.body≡ a p) (_⊑ᴰ_.body≡ b (_⊑ᴰ_.inc a p)) }
