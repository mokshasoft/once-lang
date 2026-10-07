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
--   · `⌜Pw⌝-sub` is `refl` (references are closed);
--   · `⊢⌜Pw⌝` is `⊢⌜IMu⌝` on the kernel's `⊢ref` of the two entries,
--     typed by the signature's well-formedness (`wf→ok`: the checker's
--     output), the index cast by a certified conversion;
--   · `El-⌜Pw⌝` decodes to the Knot's own `KPw`: the core's index and
--     description are CONVERTIBLE with the Knot's (`nbe-sound` on both
--     sides, normal forms decided equal).
--
-- Each conversion is proved ONCE on closed terms and weakened.  The
-- Knot's pieces are Agda-opaque, hence the `unfolding`.
--
-- ⚠ Agda costs, measured 2026-10-06: Agda compares two DIFFERENTLY WRITTEN
--   forms of one erased body or type by descending through the erasure,
--   into every body it references (the rows' cascade: >300 s, OOM).  So
--   an entry's typing `wf→ok …` has its type INFERRED (`_`), a reference's
--   body is written exactly as that typing carries it, and implicits
--   hiding a substituted term are pinned (`≅-sub σ {t} {u}`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.PwCore (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Signature using ( Sig; <-here; <-there )
open import DirectedHoTT.Metatheory.Signature using ( wf→ok )
open import DirectedHoTT.Algorithm.NbE using ( nbe )
open import DirectedHoTT.Algorithm.NbESound 𝒮 using ( nbe-sound; ≅-sub )
open import DirectedHoTT.Algorithm.ConvLazy 𝒮 using ( cong≅ᵗ )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟Tm_ )
import DirectedHoTT.Examples.PwCore as P
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf using ( K )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf using ( CP; ixPw; ⊢ixPw; module Pwₘ )
open import DirectedHoTT.Examples.Knot.Pw 𝒮 wf using ( module PwF; KPw )
import DirectedHoTT.Examples.Knot.Ren 𝒮 wf as KR
import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf as JI
import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok as LS

private
  variable
    Δ : Cx

  -- ★ the entries' bodies, typed in the empty context (types INFERRED)
  okJ : _
  okJ = wf→ok P.S P.wf {P.#PwJ} (<-there (<-there (<-there <-here)))

  okD : _
  okD = wf→ok P.S P.wf {P.#PwD} (<-there <-here)

  -- the core's index and description, as references — the bodies written
  --   EXACTLY as the typings carry them: `⊢ref` pins its body both ways,
  --   and two forms of one body are compared by descending through the
  --   erasure, into every body it references (the rows: >300 s)
  Jc : RTm Δ
  Jc = ref P.#PwJ (Sig.body P.S P.#PwJ)
  Dc : RTm Δ
  Dc = ref P.#PwD (Sig.body P.S P.#PwD)

  IsYes : {X : Set} → Dec X → Set
  IsYes (yes _) = ⊤
  IsYes (no _)  = ⊥
  fromYes : {X : Set} (p : Dec X) → IsYes p → X
  fromYes (yes p) _ = p

  ≡→≅ : {Γ : Cx} {t u : RTm Γ} → t ≡ u → t ≅ u
  ≡→≅ refl = crfl

  -- t ≅ u by their NbE normal forms, decided equal
  byNbE : {Γ : Cx} (t u : RTm Γ) → IsYes (nbe 100000 t ≟Tm nbe 100000 u) → t ≅ u
  byNbE t u y = ctrn (nbe-sound 100000 t) (ctrn (≡→≅ (fromYes _ y)) (csym (nbe-sound 100000 u)))

opaque
  unfolding PwF.FIBMₒ CP KR.wk JI.⌜Tm⌝ LS.SK

  -- ★ the core's index and description ARE the Knot's (closed terms)
  cJ₀ : Jc {ε} ≅ Pwₘ.J {ε}
  cJ₀ = byNbE _ _ tt

  cD₀ : Dc {ε} ≅ PwF.DF {ε}
  cD₀ = byNbE _ _ tt

private
  cJ : Jc {Δ} ≅ Pwₘ.J {Δ}
  cJ = ctrn (≅-sub εsub {Jc} {Pwₘ.J} cJ₀) (≡→≅ (Pwₘ.J-sub εsub))

  cD : Dc {Δ} ≅ PwF.DF {Δ}
  cD = ctrn (≅-sub εsub {Dc} {PwF.DF} cD₀) (≡→≅ (PwF.DF-sub εsub))

opaque
  ⌜Pw⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜Pw⌝ d t u = ⌜IMu⌝ Jc Dc (ixPw d t u)

  ⌜Pw⌝-sub : {Θ : Cx} (σ : Sub Δ Θ) (d t u : RTm Δ) → subTm σ (⌜Pw⌝ d t u) ≡ ⌜Pw⌝ (subTm σ d) (subTm σ t) (subTm σ u)
  ⌜Pw⌝-sub σ d t u = refl

  ⊢⌜Pw⌝ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 (nsuc d) → Ξ ⊢ ⌜Pw⌝ d t u ∷ U
  ⊢⌜Pw⌝ dd dt du =
    ⊢⌜IMu⌝ (⊢ref okJ) (⊢ref okD) (⊢conv (⊢ixPw dd dt du) (cong≅ᵗ El ξ-El (csym cJ)))

  El-⌜Pw⌝ : {d t u : RTm Δ} → El (⌜Pw⌝ d t u) ≅ᵀ KPw d t u
  El-⌜Pw⌝ {d = d} {t} {u} =
    ctrnᵀ (credᵀ El-⌜IMu⌝)
          (ctrnᵀ (cong≅ᵗ (λ x → IMu x Dc (ixPw d t u)) ξ-IMuᴵ cJ)
                 (cong≅ᵗ (λ x → IMu Pwₘ.J x (ixPw d t u)) ξ-IMuᴰ cD))
