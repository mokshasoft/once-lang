-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ THE SIZE of a term of the kernel's syntax,
-- object-level: the library fold (`Lib/TelFoldS`, `sizeAlg`) at the
-- Knot's signature.  No Knot-specific method is written: a sorted
-- syntax folds like a flat one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.Sz (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( conₗ; tag; Lt; _,ₚ_ )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok using ( Tel; Tels; NthT; dihN )
open import DirectedHoTT.Lib.TelAt 𝒮 𝓃 ok using ( NthST )
open import DirectedHoTT.Lib.TelFold 𝒮 𝓃 ok using ( sizeAlg; foldK )
open import DirectedHoTT.Lib.TelFoldS 𝒮 𝓃 ok using ( sortFolds; ⊢foldₛ; fold-ιₛ )
open import DirectedHoTT.Lib.MethAt 𝒮 𝓃 ok using ( methAt )
open import DirectedHoTT.Lib.Sorted 𝒮 𝓃 ok using ( Dₛₜ )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf

private
  variable
    Γ : Cx

-- the method: the size algebra, sort by sort
szM : RTm Γ
szM {Γ} = methAt (sortFolds sizeAlg (stels {Δ = Γ} KSig))

⊢szM : {Γ : Ctx} → Γ ⊢ szM ∷ MethTy (SI 2) KD Nat
⊢szM = ⊢foldₛ sizeAlg ⊢⌜Nat⌝ (sigOK KOK)

-- ★ `sz s d t`: the size of `t : K s d`
sz : ℕ → RTm Γ → RTm Γ → RTm Γ
sz s d t = ielim KD ((tag s) ,ₚ d) szM t

⊢sz : {Γ : Ctx} {s : ℕ} {d t : RTm ⌊ Γ ⌋} → Lt s 2 → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ K s d → Γ ⊢ sz s d t ∷ Nat
⊢sz lt dd dt = ⊢ielim ⊢SI ⊢KD ty-Nat ⊢szM (⊢ix lt dd) (⊢SK→IMu {sg = KSig} dt)

-- ★ …and it computes, one node at a time: `1 + Σ (sizes of the recursive fields)`
sz-con : {s c k : ℕ} {Ts : Tels (Γ ∙) c} {T : Tel (Γ ∙)} {d p : RTm Γ} →
         NthST (stels KSig) s Ts → NthT Ts k T →
         sz s d (conₗ k p) ⟶* nsuc (foldK sizeAlg T (dihN (single ((tag s) ,ₚ d)) T KD szM p))
sz-con ns nt = fold-ιₛ sizeAlg ns nt
