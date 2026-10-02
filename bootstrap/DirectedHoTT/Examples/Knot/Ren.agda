-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ RENAMING AND WEAKENING of the kernel's syntax,
-- object-level: `Lib/SynRen` at the Knot's signature.  Nothing here is
-- about the Knot's rows — it is the generic traversal, instantiated.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Ren where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; sym; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Lt; lt-z; lt-s; tag )
open import normalizer.Syntax.Types using ( cong₂ )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynTravM using ( VarsAt )
open import DirectedHoTT.Lib.SynRen
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms

-- the kernel's variables are terms: sort 1, the `var` row (Tm row 0)
KVars : VarsAt KSig 1
KVars = varsAt KSig 1 refl

open Ren KOK {v = 1} {kv = 0} (atᵍ 1) (atʰ 0) KVars public hiding ( wk; ⊢wkS )
open Ren KOK {v = 1} {kv = 0} (atᵍ 1) (atʰ 0) KVars using () renaming ( wk to wkᵗ; ⊢wkS to ⊢wkSᵗ )

------------------------------------------------------------------------
-- ★★ `wk` is OPAQUE (as `Knot/Sub.sub0`): its body carries the traversal
--   method under an implicit context, and two syntactic forms of one
--   context would compare it by normalisation.  Its interface: typing
--   (`⊢wkS`), closedness (`wk-sub`/`wk-ren`), `wk-def`.
------------------------------------------------------------------------

opaque
  wk : {Γ : Cx} → ℕ → RTm Γ → RTm Γ → RTm Γ
  wk = wkᵗ

  wk-def : {Γ : Cx} (s : ℕ) (d t : RTm Γ) → wk s d t ≡ wkᵗ s d t
  wk-def s d t = refl

  ⊢wkS : {Γ : Ctx} {s : ℕ} {d t : RTm ⌊ Γ ⌋} → Lt s 2 →
         Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ K s d → Γ ⊢ wk s d t ∷ K s (nsuc d)
  ⊢wkS = ⊢wkSᵗ

-- ★ weakening a quoted term: `renTm vs`, object-level, typed
⊢wk-quote : {Γ : Cx} (t : RTm Γ) {Θ : Ctx} → Θ ⊢ wk 1 (dep Γ) (quoteTm t) ∷ K 1 (nsuc (dep Γ))
⊢wk-quote {Γ} t = ⊢wkS (lt-s lt-z) (⊢dep' Γ) (⊢quoteTm t)

------------------------------------------------------------------------
-- ★ CLOSEDNESS: weakening commutes with substitution.  The traversal's
--   methods contain no description, so their closedness is one `refl`
--   (measured 0.7 s); the description's goes through `SD-sub`.
------------------------------------------------------------------------

TRAVM-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (TRAVM {Δ}) ≡ TRAVM
TRAVM-sub σ = refl

WKρ-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (WKρ {Δ}) ≡ WKρ
WKρ-sub σ = refl

opaque
 unfolding wk
 wk-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (s : ℕ) (d t : RTm Δ) → subTm σ (wk s d t) ≡ wk s (subTm σ d) (subTm σ t)
 wk-sub σ s d t =
  cong₄ (λ D T M W → app (app (ielim D (pair T (subTm σ d)) M (subTm σ t)) (nsuc (subTm σ d))) W)
        (SD-sub σ KSig) (tag-sub σ s) (TRAVM-sub σ) (WKρ-sub σ)

wk-ren : {Δ Θ : Cx} (ρ : Ren Δ Θ) (s : ℕ) (d t : RTm Δ) → renTm ρ (wk s d t) ≡ wk s (renTm ρ d) (renTm ρ t)
wk-ren ρ s d t = trans (sym (subTm-var ρ (wk s d t)))
                       (trans (wk-sub ⟨ ρ ⟩ᵣ s d t)
                              (cong₂ (wk s) {x = subTm ⟨ ρ ⟩ᵣ d} {x' = renTm ρ d} {y = subTm ⟨ ρ ⟩ᵣ t} {y' = renTm ρ t}
                                     (subTm-var ρ d) (subTm-var ρ t)))
  where open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
