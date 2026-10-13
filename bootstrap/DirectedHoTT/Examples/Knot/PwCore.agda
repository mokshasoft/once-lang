-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ Pw's CODE IS THE CORE'S (PLAN-BIDI §3g, P4).
--
-- The interface of the generated `Knot/Pw`'s code — `⌜Pw⌝`, its typing,
-- its closedness, its decoding — with the index and the description
-- REFERENCES to the core entries `Examples/PwCore.#PwJ` and `#PwD`:
--
--     ⌜Pw⌝ d t u = ⌜IMu⌝ (ref #PwJ) (ref #PwD) (ixPw d t u)
--
-- ★ PLAN-REF (D082): a reference is a projection from the AMBIENT
--   signature, so this module is over any signature that CONTAINS the
--   core (`core : Kc ⊑ᴰ 𝒮`, `Spec/SigExtend`) — the Knot citing the core
--   is typed in a context extending it.
--
--   · `⌜Pw⌝-sub` is `refl` (references are closed);
--   · `⊢⌜Pw⌝` is `⊢⌜IMu⌝` on `⊢ref` — no premise: the name is below the
--     bound and its declared type is the core's (`core`), the index cast
--     by a certified conversion;
--   · `El-⌜Pw⌝` decodes to the Knot's own `KPw`: the core's index and
--     description are CONVERTIBLE with the Knot's — decided ONCE, at the
--     core itself, by NbE (`nbe-sound` at its value table, normal forms
--     decided equal), and carried to the ambient signature by
--     monotonicity (`Metatheory/SigExt.ext≅`).
--
-- The Knot's pieces are Agda-opaque, hence the `unfolding`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Metatheory.Entries as Entries
import DirectedHoTT.Examples.PwCore as P
import DirectedHoTT.Examples.PredsCore as Core₀
open import DirectedHoTT.Spec.Base hiding ( _,,_; _×_ )
module DirectedHoTT.Examples.Knot.PwCore (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮)
open import DirectedHoTT.Examples.Knot.CoreRef 𝒮 wf core using ( _≅ᶜ_; byNbE; lift≅; below; ⊢core )
open import DirectedHoTT.Algorithm.ConvLazy 𝒮 using ( cong≅ᵗ )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf using ( K )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf using ( CP; ixPw; ⊢ixPw; module Pwₘ )
open import DirectedHoTT.Examples.Knot.Pw 𝒮 wf core using ( module PwF; KPw )
import DirectedHoTT.Examples.Knot.Ren 𝒮 wf as KR
import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf as JI
import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) as LS

private
  variable
    Δ : Cx

  -- the core's index and description, as references
  Jc Dc : RTm Δ
  Jc = ref P.#PwJ
  Dc = ref P.#PwD

  ltJ : P.#PwJ <ˢ Defs.size Core₀.Kc
  ltJ = below P.#PwJ tt
  ltD : P.#PwD <ˢ Defs.size Core₀.Kc
  ltD = below P.#PwD tt

opaque
  unfolding PwF.FIBMₒ CP KR.wk JI.⌜Tm⌝ LS.SK LS.SD

  -- ★ the core's index and description ARE the Knot's (closed terms, at the core)
  cJ₀ : Jc {ε} ≅ᶜ Pwₘ.J {ε}
  cJ₀ = byNbE _ _ tt

  cD₀ : Dc {ε} ≅ᶜ PwF.DF {ε} unit
  cD₀ = byNbE _ _ tt

private
  ≡→≅ : {Γ : Cx} {t u : RTm Γ} → t ≡ u → t ≅ u
  ≡→≅ refl = crfl

  -- …in every context, at every signature containing the core
  cJ : Jc {Δ} ≅ Pwₘ.J {Δ}
  cJ = ctrn (lift≅ cJ₀) (≡→≅ (Pwₘ.J-sub εsub))

  cD : Dc {Δ} ≅ PwF.DF {Δ} unit
  cD = ctrn (lift≅ cD₀) (≡→≅ (PwF.DF-sub εsub unit))

opaque
  ⌜Pw⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜Pw⌝ d t u = ⌜IMu⌝ Jc Dc (ixPw d t u)

  ⌜Pw⌝-sub : {Θ : Cx} (σ : Sub Δ Θ) (d t u : RTm Δ) → subTm σ (⌜Pw⌝ d t u) ≡ ⌜Pw⌝ (subTm σ d) (subTm σ t) (subTm σ u)
  ⌜Pw⌝-sub σ d t u = refl

  ⊢⌜Pw⌝ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 (nsuc d) → Ξ ⊢ ⌜Pw⌝ d t u ∷ U
  ⊢⌜Pw⌝ dd dt du =
    ⊢⌜IMu⌝ (⊢core ltJ) (⊢core ltD) (⊢conv (⊢ixPw dd dt du) (cong≅ᵗ El ξ-El (csym cJ)))

  El-⌜Pw⌝ : {d t u : RTm Δ} → El (⌜Pw⌝ d t u) ≅ᵀ KPw d t u
  El-⌜Pw⌝ {d = d} {t} {u} =
    ctrnᵀ (credᵀ El-⌜IMu⌝)
          (ctrnᵀ (cong≅ᵗ (λ x → IMu x Dc (ixPw d t u)) ξ-IMuᴵ cJ)
                 (cong≅ᵗ (λ x → IMu Pwₘ.J x (ixPw d t u)) ξ-IMuᴰ cD))
