-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ A KNOT CODE THAT IS A CORE REFERENCE (PLAN-BIDI
-- §3g, P6): what every Knot code citing the core shares, over a signature
-- containing the core (`core : Core₀.Kc ⊑ᴰ 𝒮`, `Spec/SigExtend`; `Core₀`
-- is the TOP core segment, which contains every segment below it).
--
-- · `⊢core`: a reference to a core entry, typed at the core's declared
--   type; `below` decides the name's bound from its literal;
-- · `byNbE`: two terms convertible AT THE CORE, decided by their NbE
--   normal forms (`nbe-sound` at the core's value table);
-- · `lift≅`: a closed conversion at the core, in every context and at the
--   ambient signature (`≅-sub`, then monotonicity `Metatheory/SigExt.ext≅`).
--
-- Extracted from `Knot/PwCore` (P5: its frame was a per-family template);
-- `Knot/Preds` (generated) uses it for the codes it takes from the core.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PredsCore as Core₀
open import DirectedHoTT.Spec.Base hiding ( _,,_; _×_ )
module DirectedHoTT.Examples.Knot.CoreRef (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong; ⊤; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮)
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢-cast )
import DirectedHoTT.Spec.Reduction Core₀.Kc as Rc
import DirectedHoTT.Metatheory.SigExt Core₀.Kc 𝒮 (_⊑ᴰ_.inc core) (_⊑ᴰ_.body≡ core) as X
open import DirectedHoTT.Algorithm.NbETable using ( mkTbl; mkTbl-ok )
open import DirectedHoTT.Algorithm.NbE (mkTbl Core₀.Kc) using ( nbe )
open import DirectedHoTT.Algorithm.NbESound Core₀.Kc (mkTbl Core₀.Kc) (mkTbl-ok Core₀.Kc) using ( nbe-sound; ≅-sub )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Tm_ )

open _⊑ᴰ_ core

IsYes : {X : Set} → Dec X → Set
IsYes (yes _) = ⊤
IsYes (no _)  = ⊥

fromYes : {X : Set} (p : Dec X) → IsYes p → X
fromYes (yes p) _ = p

-- conversion AT THE CORE
_≅ᶜ_ : {Γ : Cx} → RTm Γ → RTm Γ → Set
_≅ᶜ_ = Rc._≅_
infix 4 _≅ᶜ_

private
  ≡→≅ᶜ : {Γ : Cx} {t u : RTm Γ} → t ≡ u → t ≅ᶜ u
  ≡→≅ᶜ refl = Rc.crfl

-- ★ t ≅ u AT THE CORE, by their NbE normal forms, decided equal
byNbE : {Γ : Cx} (t u : RTm Γ) → IsYes (nbe 100000 t ≟Tm nbe 100000 u) → t ≅ᶜ u
byNbE t u y = Rc.ctrn (nbe-sound 100000 t) (Rc.ctrn (≡→≅ᶜ (fromYes _ y)) (Rc.csym (nbe-sound 100000 u)))

-- ★ a closed conversion at the core holds in every context, at 𝒮
lift≅ : {Δ : Cx} {t u : RTm ε} → t ≅ᶜ u → subTm (εsub {Δ}) t ≅ subTm εsub u
lift≅ {t = t} {u} c = X.ext≅ (≅-sub εsub {t} {u} c)

-- a core name's bound, decided from its literal
below : (d : ℕ) → IsYes (d <ˢ? Defs.size Core₀.Kc) → d <ˢ Defs.size Core₀.Kc
below d y = fromYes (d <ˢ? Defs.size Core₀.Kc) y

-- ★ a reference to a core entry, typed at its declared type.  Proved over
--   an ABSTRACT smaller signature: at `Core₀.Kc` itself, unifying the cast
--   unfolds `Defs.type Core₀.Kc d` — the whole core, elaborated (>5.6 GB).
private
  ⊢refAt : (K : Defs) → K ⊑ᴰ 𝒮 → {Ξ : Ctx} {d : ℕ} → d <ˢ Defs.size K → Ξ ⊢ ref d ∷ εwkTy (Defs.type K d)
  ⊢refAt K c {Ξ} {d} lt = ⊢-cast {Ξ} {ref d} {εwkTy (Defs.type 𝒮 d)} {εwkTy (Defs.type K d)}
                                 (cong εwkTy (sym (_⊑ᴰ_.type≡ c lt))) (⊢ref (_⊑ᴰ_.inc c lt))

⊢core : {Ξ : Ctx} {d : ℕ} → d <ˢ Defs.size Core₀.Kc → Ξ ⊢ ref d ∷ εwkTy (Defs.type Core₀.Kc d)
⊢core = ⊢refAt Core₀.Kc core
