-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ SUBSTITUTION of the kernel's syntax, object-level:
-- `Lib/SynSub` at the Knot's signature.  `sub0 t u` is `subTm (single u) t`
-- — what `β` needs — typed at every depth.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Sub where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Lt; lt-z; lt-s; _,ₚ_ )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynSub
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appʳ )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ren using ( KVars )

open Sub KOK {v = 1} {kv = 0} (atᵍ 1) (atʰ 0) KVars public hiding ( sub0; ⊢sub0 )
open Sub KOK {v = 1} {kv = 0} (atᵍ 1) (atʰ 0) KVars using () renaming ( sub0 to sub0ᵗ; ⊢sub0 to ⊢sub0ᵗ )

------------------------------------------------------------------------
-- ★★ `sub0` is OPAQUE: an abstraction boundary, not an optimisation
--   hack.  Its body carries the substitution method (`TRAVM`, ~the size
--   of the description) under an implicit CONTEXT.  A row's telescope
--   elaborates it at `(⌊ Ξ ⌋ ∙) ∙` and a typing lemma at `⌊ (Ξ ▹ A) ▹ B ⌋`;
--   the two are not syntactically equal, so a TRANSPARENT `sub0` is
--   compared by normalising `TRAVM` — measured ~35 s per meeting (the
--   ⊢app row: 80 s → 5 s).  Opaque, a mismatch compares four arguments.
--   Everything a consumer needs is a lemma: typing, closedness, and
--   `sub0-def` for the rare computation.
------------------------------------------------------------------------

opaque
  sub0 : {Γ : Cx} → ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  sub0 = sub0ᵗ

  sub0-def : {Γ : Cx} (s : ℕ) (d t u : RTm Γ) → sub0 s d t u ≡ sub0ᵗ s d t u
  sub0-def s d t u = refl

  ⊢sub0 : {Γ : Ctx} {s : ℕ} {d t u : RTm ⌊ Γ ⌋} → Lt s 2 →
          Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ K s (nsuc d) → Γ ⊢ u ∷ K 1 d → Γ ⊢ sub0 s d t u ∷ K s d
  ⊢sub0 = ⊢sub0ᵗ

-- ★ the body of a `lam` at depth `suc |Γ|`, instantiated at an argument
⊢β-quote : {Γ : Cx} (t : RTm (Γ ∙)) (u : RTm Γ) {Θ : Ctx} →
           Θ ⊢ sub0 1 (dep Γ) (quoteTm t) (quoteTm u) ∷ K 1 (dep Γ)
⊢β-quote {Γ} t u = ⊢sub0 (lt-s lt-z) (⊢dep' Γ) (⊢quoteTm t) (⊢quoteTm u)

------------------------------------------------------------------------
-- ★ CLOSEDNESS: substitution commutes with substitution.
--   ⚠ `TRAVMs-sub` is one `refl` that costs ~30 s (the substitution kit's
--   weakening carries the description); a structural proof needs the
--   kits' closedness laws in `Lib/SynTravM` — an optimisation, not a gap.
------------------------------------------------------------------------

TRAVMs-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (TRAVM {Δ}) ≡ TRAVM
TRAVMs-sub σ = refl

SINGLE-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (SINGLE {Δ}) ≡ SINGLE
SINGLE-sub σ = refl

opaque
 unfolding sub0
 sub0-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (s : ℕ) (d t u : RTm Δ) → subTm σ (sub0 s d t u) ≡ sub0 s (subTm σ d) (subTm σ t) (subTm σ u)
 sub0-sub σ s d t u =
  cong₄ (λ D T M S → app (app (ielim D (T ,ₚ (nsuc (subTm σ d))) M (subTm σ t)) (subTm σ d)) (app (app S (subTm σ d)) (subTm σ u)))
        (SD-sub σ KSig) (tag-sub σ s) (TRAVMs-sub σ) (SINGLE-sub σ)

-- a reduction in the argument (the substitution's image)
opaque
 unfolding sub0
 ⟶*-sub0ᵘ : {Γ : Cx} {s : ℕ} {d t u u' : RTm Γ} → u ⟶* u' → sub0 s d t u ⟶* sub0 s d t u'
 ⟶*-sub0ᵘ r = ⟶*-appʳ (⟶*-appʳ r)
