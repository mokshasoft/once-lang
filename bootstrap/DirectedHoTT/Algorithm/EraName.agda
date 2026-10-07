-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · ALGORITHM — ERASURE BY NAMES: compare two annotated types
-- with every reference's body left OUT.
--
-- Erasure unfolds a reference to its body, `⌈ ref d ⌉ = ref d (δ d)`, and
-- bodies nest.  A syntactic comparison of two erased types therefore
-- walks the transitive closure of every body they mention (profiled
-- 2026-10-06 on `Examples/PwCore`: ~40% of the checker's work was
-- `≟Ty` encoding the Knot signature's bodies, inside the fast path of
-- `CheckA.decTo`).
--
-- `E₀` erases with a DUMMY body (`unit`); `fill` puts the real body
-- back, by the name.  `fill-era` (one clause per constructor) says that
-- is the real erasure, so equal dummy erasures are equal real ones
-- (`by-names`).  A comparison is then linear in the TYPE, not in the
-- signature.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
module DirectedHoTT.Algorithm.EraName (δ : ℕ → RTm ε) where
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans; sym )
open import DirectedHoTT.Spec.Annotated

open Era δ
module E₀ = Era (λ _ → unit)

-- ★ the real body back, by the name
mutual
  fillᵀ : {Γ : Cx} → RTy Γ → RTy Γ
  fill : {Γ : Cx} → RTm Γ → RTm Γ
  fillᵀ base = base
  fillᵀ U = U
  fillᵀ (Π x0 x1) = Π (fillᵀ x0) (fillᵀ x1)
  fillᵀ (Σ' x0 x1) = Σ' (fillᵀ x0) (fillᵀ x1)
  fillᵀ (El x0) = El (fill x0)
  fillᵀ (Hom x0 x1 x2) = Hom (fillᵀ x0) (fill x1) (fill x2)
  fillᵀ Unit = Unit
  fillᵀ Nat = Nat
  fillᵀ (Id x0 x1 x2) = Id (fillᵀ x0) (fill x1) (fill x2)
  fillᵀ (IMu x0 x1 x2) = IMu (fill x0) (fill x1) (fill x2)
  fillᵀ (Desc x0) = Desc (fill x0)
  fillᵀ (DIh x0 x1 x2 x3) = DIh (fill x0) (fillᵀ x1) (fill x2) (fill x3)
  fillᵀ (Fin x0) = Fin (fill x0)
  fill (var x0) = var x0
  fill (lam x0) = lam (fill x0)
  fill (app x0 x1) = app (fill x0) (fill x1)
  fill (pair x0 x1) = pair (fill x0) (fill x1)
  fill (absurd x0 x1) = absurd (fill x0) (fill x1)
  fill (ordtr x0 x1 x2 x3 x4) = ordtr (fill x0) (fill x1) (fill x2) (fill x3) (fill x4)
  fill (fst x0) = fst (fill x0)
  fill (snd x0) = snd (fill x0)
  fill ⌜base⌝ = ⌜base⌝
  fill (⌜Π⌝ x0 x1) = ⌜Π⌝ (fill x0) (fill x1)
  fill (⌜Σ⌝ x0 x1) = ⌜Σ⌝ (fill x0) (fill x1)
  fill (⌜Hom⌝ x0 x1 x2) = ⌜Hom⌝ (fill x0) (fill x1) (fill x2)
  fill (hrefl x0 x1) = hrefl (fill x0) (fill x1)
  fill (tr x0 x1 x2) = tr (fill x0) (fill x1) (fill x2)
  fill (ap x0 x1 x2) = ap (fill x0) (fill x1) (fill x2)
  fill (⌜Id⌝ x0 x1 x2) = ⌜Id⌝ (fill x0) (fill x1) (fill x2)
  fill (idrefl x0 x1) = idrefl (fill x0) (fill x1)
  fill (jsub x0 x1 x2) = jsub (fill x0) (fill x1) (fill x2)
  fill unit = unit
  fill nzero = nzero
  fill (nsuc x0) = nsuc (fill x0)
  fill (natrec x0 x1 x2) = natrec (fill x0) (fill x1) (fill x2)
  fill (con x0) = con (fill x0)
  fill (ielim x0 x1 x2 x3) = ielim (fill x0) (fill x1) (fill x2) (fill x3)
  fill dι = dι
  fill (dσ x0 x1) = dσ (fill x0) (fill x1)
  fill (dρ x0 x1) = dρ (fill x0) (fill x1)
  fill (dpay x0 x1 x2) = dpay (fill x0) (fill x1) (fill x2)
  fill (dih x0 x1 x2 x3) = dih (fill x0) (fill x1) (fill x2) (fill x3)
  fill fzero = fzero
  fill (fsuc x0) = fsuc (fill x0)
  fill (fcase x0 x1 x2) = fcase (fill x0) (fill x1) (fill x2)
  fill (fcase0 x0) = fcase0 (fill x0)
  fill (psplit x0 x1) = psplit (fill x0) (fill x1)
  fill ⌜Nat⌝ = ⌜Nat⌝
  fill (⌜IMu⌝ x0 x1 x2) = ⌜IMu⌝ (fill x0) (fill x1) (fill x2)
  fill (⌜Fin⌝ x0) = ⌜Fin⌝ (fill x0)
  fill ⌜Unit⌝ = ⌜Unit⌝
  fill (ref d b) = ref d (δ d)

private
  cong₅ : {A B C D E F : Set} (f : A → B → C → D → E → F) {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f a b c d e ≡ f a' b' c' d' e'
  cong₅ f refl refl refl refl refl = refl

-- ★ the dummy erasure, refilled, IS the erasure
mutual
  fill-eraᵀ : {Γ : Cx} (A : ATy Γ) → fillᵀ (E₀.⌈ A ⌉ᵀ) ≡ ⌈ A ⌉ᵀ
  fill-era : {Γ : Cx} (t : ATm Γ) → fill (E₀.⌈ t ⌉) ≡ ⌈ t ⌉
  fill-eraᵀ base = refl
  fill-eraᵀ U = refl
  fill-eraᵀ (Π x0 x1) = cong₂ (λ y0 y1 → Π y0 y1) (fill-eraᵀ x0) (fill-eraᵀ x1)
  fill-eraᵀ (Σ' x0 x1) = cong₂ (λ y0 y1 → Σ' y0 y1) (fill-eraᵀ x0) (fill-eraᵀ x1)
  fill-eraᵀ (El x0) = cong (λ y0 → El y0) (fill-era x0)
  fill-eraᵀ (Hom x0 x1 x2) = cong₃ (λ y0 y1 y2 → Hom y0 y1 y2) (fill-eraᵀ x0) (fill-era x1) (fill-era x2)
  fill-eraᵀ Unit = refl
  fill-eraᵀ Nat = refl
  fill-eraᵀ (Id x0 x1 x2) = cong₃ (λ y0 y1 y2 → Id y0 y1 y2) (fill-eraᵀ x0) (fill-era x1) (fill-era x2)
  fill-eraᵀ (IMu x0 x1 x2) = cong₃ (λ y0 y1 y2 → IMu y0 y1 y2) (fill-era x0) (fill-era x1) (fill-era x2)
  fill-eraᵀ (Desc x0) = cong (λ y0 → Desc y0) (fill-era x0)
  fill-eraᵀ (DIh x0 x1 x2 x3 x4) = cong₄ (λ y0 y1 y2 y3 → DIh y0 y1 y2 y3) (fill-era x1) (fill-eraᵀ x2) (fill-era x3) (fill-era x4)
  fill-eraᵀ (Fin x0) = cong (λ y0 → Fin y0) (fill-era x0)
  fill-era (var x) = refl
  fill-era (lam x0 x1) = cong (λ y0 → lam y0) (fill-era x1)
  fill-era (app x0 x1) = cong₂ (λ y0 y1 → app y0 y1) (fill-era x0) (fill-era x1)
  fill-era (pair x0 x1 x2 x3) = cong₂ (λ y0 y1 → pair y0 y1) (fill-era x2) (fill-era x3)
  fill-era (absurd x0 x1) = cong₂ (λ y0 y1 → absurd y0 y1) (fill-era x0) (fill-era x1)
  fill-era (ordtr x0 x1 x2 x3 x4) = cong₅ (λ y0 y1 y2 y3 y4 → ordtr y0 y1 y2 y3 y4) (fill-era x0) (fill-era x1) (fill-era x2) (fill-era x3) (fill-era x4)
  fill-era (fst x0) = cong (λ y0 → fst y0) (fill-era x0)
  fill-era (snd x0) = cong (λ y0 → snd y0) (fill-era x0)
  fill-era ⌜base⌝ = refl
  fill-era (⌜Π⌝ x0 x1) = cong₂ (λ y0 y1 → ⌜Π⌝ y0 y1) (fill-era x0) (fill-era x1)
  fill-era (⌜Σ⌝ x0 x1) = cong₂ (λ y0 y1 → ⌜Σ⌝ y0 y1) (fill-era x0) (fill-era x1)
  fill-era (⌜Hom⌝ x0 x1 x2) = cong₃ (λ y0 y1 y2 → ⌜Hom⌝ y0 y1 y2) (fill-era x0) (fill-era x1) (fill-era x2)
  fill-era (hrefl x0 x1) = cong₂ (λ y0 y1 → hrefl y0 y1) (fill-era x0) (fill-era x1)
  fill-era (tr x0 x1 x2 x3 x4 x5) = cong₃ (λ y0 y1 y2 → tr y0 y1 y2) (fill-era x3) (fill-era x4) (fill-era x5)
  fill-era (ap x0 x1 x2 x3 x4 x5) = cong₃ (λ y0 y1 y2 → ap y0 y1 y2) (fill-era x3) (fill-era x4) (fill-era x5)
  fill-era (⌜Id⌝ x0 x1 x2) = cong₃ (λ y0 y1 y2 → ⌜Id⌝ y0 y1 y2) (fill-era x0) (fill-era x1) (fill-era x2)
  fill-era (idrefl x0 x1) = cong₂ (λ y0 y1 → idrefl y0 y1) (fill-era x0) (fill-era x1)
  fill-era (jsub x0 x1 x2 x3 x4 x5) = cong₃ (λ y0 y1 y2 → jsub y0 y1 y2) (fill-era x3) (fill-era x4) (fill-era x5)
  fill-era unit = refl
  fill-era nzero = refl
  fill-era (nsuc x0) = cong (λ y0 → nsuc y0) (fill-era x0)
  fill-era (natrec x0 x1 x2 x3) = cong₃ (λ y0 y1 y2 → natrec y0 y1 y2) (fill-era x1) (fill-era x2) (fill-era x3)
  fill-era ⌜Nat⌝ = refl
  fill-era ⌜Unit⌝ = refl
  fill-era (⌜IMu⌝ x0 x1 x2) = cong₃ (λ y0 y1 y2 → ⌜IMu⌝ y0 y1 y2) (fill-era x0) (fill-era x1) (fill-era x2)
  fill-era (⌜Fin⌝ x0) = cong (λ y0 → ⌜Fin⌝ y0) (fill-era x0)
  fill-era (con x0 x1 x2 x3) = cong (λ y0 → con y0) (fill-era x3)
  fill-era (ielim x0 x1 x2 x3 x4 x5) = cong₄ (λ y0 y1 y2 y3 → ielim y0 y1 y2 y3) (fill-era x1) (fill-era x3) (fill-era x4) (fill-era x5)
  fill-era (dι x0) = refl
  fill-era (dσ x0 x1 x2) = cong₂ (λ y0 y1 → dσ y0 y1) (fill-era x1) (fill-era x2)
  fill-era (dρ x0 x1 x2) = cong₂ (λ y0 y1 → dρ y0 y1) (fill-era x1) (fill-era x2)
  fill-era (dpay x0 x1 x2) = cong₃ (λ y0 y1 y2 → dpay y0 y1 y2) (fill-era x0) (fill-era x1) (fill-era x2)
  fill-era (dih x0 x1 x2 x3 x4 x5) = cong₄ (λ y0 y1 y2 y3 → dih y0 y1 y2 y3) (fill-era x1) (fill-era x3) (fill-era x4) (fill-era x5)
  fill-era (fzero x0) = refl
  fill-era (fsuc x0 x1) = cong (λ y0 → fsuc y0) (fill-era x1)
  fill-era (fcase x0 x1 x2 x3 x4) = cong₃ (λ y0 y1 y2 → fcase y0 y1 y2) (fill-era x2) (fill-era x3) (fill-era x4)
  fill-era (fcase0 x0 x1) = cong (λ y0 → fcase0 y0) (fill-era x1)
  fill-era (psplit x0 x1 x2 x3 x4) = cong₂ (λ y0 y1 → psplit y0 y1) (fill-era x3) (fill-era x4)
  fill-era (ref x0) = refl

-- ★ equal by names ⇒ equal erasures
by-names : {Γ : Cx} (A B : ATy Γ) → E₀.⌈ A ⌉ᵀ ≡ E₀.⌈ B ⌉ᵀ → ⌈ A ⌉ᵀ ≡ ⌈ B ⌉ᵀ
by-names A B e = trans (sym (fill-eraᵀ A)) (trans (cong fillᵀ e) (fill-eraᵀ B))
