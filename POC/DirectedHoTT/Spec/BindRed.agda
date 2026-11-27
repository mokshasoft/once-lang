-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — RELATIONS over the generic syntax, generic in the
-- signature (SPIKE-GENERIC-SYNTAX S8, promoted from `POC/tmp/RedGen.agda`).
--
-- `Spec/Reduction` instantiates `Red` at the kernel's contractions.
------------------------------------------------------------------------
--
-- Two pieces, each proved once for every signature:
--   1. RENAMING REFLECTS FORMERS: `ren ρ t ≡ node c ys` gives `t ≡ node c xs`
--      with `ys` the renamed `xs`. The hand-written metatheory got this from
--      Agda inverting the old constructor-headed `renTm` (a hidden invariant);
--      here it is a lemma.
--   2. REDUCTION as ONE congruence rule (for every former and position) plus a
--      table of CONTRACTIONS `_▷_` (the content: β, ι, guarded rules). Then:
--        * renaming preserves reduction (given: it preserves contractions);
--        * renaming REFLECTS reduction (given: it reflects contractions);
--        * SN is closed under anti-renaming.
--      Each is stated with an EQUATION `v ≡ ren ρ t`, never an index that Agda
--      would have to invert; the congruence case is one generic case.

{-# OPTIONS --safe #-}
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong; Σ; _,_; _×_; _⊎_; inj₁; inj₂; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Scope
open import DirectedHoTT.Spec.Bind
module DirectedHoTT.Spec.BindRed (Σᴮ : BSig) where
open Trav Σᴮ

private
  Tmᴮ = Tm Σᴮ
  ⟦_⟧ᴮ = ⟦_⟧ Σᴮ

------------------------------------------------------------------------
-- 1. Renaming reflects formers (and variables)
------------------------------------------------------------------------

ren-node : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) (t : Tmᴮ s Γ) {c : Con Σᴮ s} {ys : ⟦ fields Σᴮ c ⟧ᴮ Δ}
         → ren ρ t ≡ node c ys
         → Σ (⟦ fields Σᴮ c ⟧ᴮ Γ) (λ xs → (t ≡ node c xs) × (travF renK (fields Σᴮ c) ρ xs ≡ ys))
ren-node ρ (var x)     ()
ren-node ρ (node c xs) refl = xs , (refl , refl)

ren-var : ∀ {Γ Δ} (ρ : Var Γ → Var Δ) (t : Tmᴮ (vsort Σᴮ) Γ) {y : Var Δ}
        → ren ρ t ≡ var y → Σ (Var Γ) (λ x → (t ≡ var x) × (ρ x ≡ y))
ren-var ρ (var x)     refl = x , (refl , refl)
ren-var ρ (node c xs) ()

------------------------------------------------------------------------
-- 2. Reduction: one congruence rule, plus the contractions
------------------------------------------------------------------------

module Red (_▷_ : ∀ {s Γ} → Tmᴮ s Γ → Tmᴮ s Γ → Set) where

  infix 4 _⟶_
  data _⟶_ : ∀ {s Γ} → Tmᴮ s Γ → Tmᴮ s Γ → Set
  -- exactly one field steps, the others are equal
  Step : ∀ fs {Γ} → ⟦ fs ⟧ᴮ Γ → ⟦ fs ⟧ᴮ Γ → Set

  data _⟶_ where
    ⟶head : ∀ {s Γ} {a b : Tmᴮ s Γ} → a ▷ b → a ⟶ b
    ⟶cong : ∀ {s Γ} {c : Con Σᴮ s} {xs ys : ⟦ fields Σᴮ c ⟧ᴮ Γ} → Step (fields Σᴮ c) xs ys → node c xs ⟶ node c ys

  Step []                                _         _         = ⊥
  Step (fld s zero ∷ fs)                 (x ,ᶠ xs) (y ,ᶠ ys) = ((x ⟶ y) × (xs ≡ ys)) ⊎ ((x ≡ y) × Step fs xs ys)
  Step (fld s (suc zero) ∷ fs)           (x ,ᶠ xs) (y ,ᶠ ys) = ((x ⟶ y) × (xs ≡ ys)) ⊎ ((x ≡ y) × Step fs xs ys)
  Step (fld s (suc (suc zero)) ∷ fs)     (x ,ᶠ xs) (y ,ᶠ ys) = ((x ⟶ y) × (xs ≡ ys)) ⊎ ((x ≡ y) × Step fs xs ys)
  Step (fld s (suc (suc (suc k))) ∷ fs)  (x ,ᶠ xs) (y ,ᶠ ys) = ((x ⟶ y) × (xs ≡ ys)) ⊎ ((x ≡ y) × Step fs xs ys)
  Step (fnat ∷ fs)                       (n ,ᶠ xs) (m ,ᶠ ys) = (n ≡ m) × Step fs xs ys

  ----------------------------------------------------------------------
  -- renaming PRESERVES reduction (the rules supply: it preserves ▷)
  ----------------------------------------------------------------------

  module Forward (▷-ren : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {a b : Tmᴮ s Γ} → a ▷ b → ren ρ a ▷ ren ρ b) where
    ⟶-ren  : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {a b : Tmᴮ s Γ} → a ⟶ b → ren ρ a ⟶ ren ρ b
    Step-ren : ∀ fs {Γ Δ} (ρ : Var Γ → Var Δ) {xs ys : ⟦ fs ⟧ᴮ Γ}
             → Step fs xs ys → Step fs (travF renK fs ρ xs) (travF renK fs ρ ys)
    ⟶-ren ρ (⟶head r) = ⟶head (▷-ren ρ r)
    ⟶-ren ρ (⟶cong {c = c} st) = ⟶cong (Step-ren (fields Σᴮ c) ρ st)
    Step-ren [] ρ ()
    Step-ren (fld s zero ∷ fs) ρ (inj₁ (r , refl)) = inj₁ (⟶-ren ρ r , refl)
    Step-ren (fld s zero ∷ fs) ρ (inj₂ (refl , st)) = inj₂ (refl , Step-ren fs ρ st)
    Step-ren (fld s (suc zero) ∷ fs) ρ (inj₁ (r , refl)) = inj₁ (⟶-ren (ext renK ρ) r , refl)
    Step-ren (fld s (suc zero) ∷ fs) ρ (inj₂ (refl , st)) = inj₂ (refl , Step-ren fs ρ st)
    Step-ren (fld s (suc (suc zero)) ∷ fs) ρ (inj₁ (r , refl)) = inj₁ (⟶-ren (ext renK (ext renK ρ)) r , refl)
    Step-ren (fld s (suc (suc zero)) ∷ fs) ρ (inj₂ (refl , st)) = inj₂ (refl , Step-ren fs ρ st)
    Step-ren (fld s (suc (suc (suc k))) ∷ fs) ρ (inj₁ (r , refl)) = inj₁ (⟶-ren (extN renK (suc (suc (suc k))) ρ) r , refl)
    Step-ren (fld s (suc (suc (suc k))) ∷ fs) ρ (inj₂ (refl , st)) = inj₂ (refl , Step-ren fs ρ st)
    Step-ren (fnat ∷ fs) ρ (refl , st) = refl , Step-ren fs ρ st

    -- SN, and its closure under ANTI-renaming: one proof, by the forward direction
    data SN {s Γ} (t : Tmᴮ s Γ) : Set where
      sn : (∀ {u} → t ⟶ u → SN u) → SN t

    SN-anti : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {v : Tmᴮ s Δ} → SN v → (t : Tmᴮ s Γ) → v ≡ ren ρ t → SN t
    SN-anti ρ (sn h) t refl = sn (λ {u} r → SN-anti ρ (h (⟶-ren ρ r)) u refl)

  ----------------------------------------------------------------------
  -- renaming REFLECTS reduction (the rules supply: it reflects ▷)
  ----------------------------------------------------------------------

  module Backward (▷-anti : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {a b : Tmᴮ s Δ} → a ▷ b → (t : Tmᴮ s Γ) → a ≡ ren ρ t
                            → Σ (Tmᴮ s Γ) (λ u → (t ▷ u) × (b ≡ ren ρ u))) where
    ⟶-anti : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {a b : Tmᴮ s Δ} → a ⟶ b → (t : Tmᴮ s Γ) → a ≡ ren ρ t
           → Σ (Tmᴮ s Γ) (λ u → (t ⟶ u) × (b ≡ ren ρ u))
    Step-anti : ∀ fs {Γ Δ} (ρ : Var Γ → Var Δ) {xs ys : ⟦ fs ⟧ᴮ Δ} → Step fs xs ys → (zs : ⟦ fs ⟧ᴮ Γ)
              → xs ≡ travF renK fs ρ zs
              → Σ (⟦ fs ⟧ᴮ Γ) (λ ws → Step fs zs ws × (ys ≡ travF renK fs ρ ws))
    ⟶-anti ρ (⟶head r) t e with ▷-anti ρ r t e
    ... | u , (r′ , e′) = u , (⟶head r′ , e′)
    ⟶-anti ρ (⟶cong {c = c} st) t e with ren-node ρ t (sym e)
    ... | zs , (refl , e₂) with Step-anti (fields Σᴮ c) ρ st zs (sym e₂)
    ...   | ws , (st′ , refl) = node c ws , (⟶cong st′ , refl)
    Step-anti [] ρ () zs e
    Step-anti (fld s zero ∷ fs) ρ (inj₁ (r , refl)) (z ,ᶠ zs) refl with ⟶-anti ρ r z refl
    ... | w , (r′ , refl) = (w ,ᶠ zs) , (inj₁ (r′ , refl) , refl)
    Step-anti (fld s zero ∷ fs) ρ (inj₂ (refl , st)) (z ,ᶠ zs) refl with Step-anti fs ρ st zs refl
    ... | ws , (st′ , refl) = (z ,ᶠ ws) , (inj₂ (refl , st′) , refl)
    Step-anti (fld s (suc zero) ∷ fs) ρ (inj₁ (r , refl)) (z ,ᶠ zs) refl with ⟶-anti (ext renK ρ) r z refl
    ... | w , (r′ , refl) = (w ,ᶠ zs) , (inj₁ (r′ , refl) , refl)
    Step-anti (fld s (suc zero) ∷ fs) ρ (inj₂ (refl , st)) (z ,ᶠ zs) refl with Step-anti fs ρ st zs refl
    ... | ws , (st′ , refl) = (z ,ᶠ ws) , (inj₂ (refl , st′) , refl)
    Step-anti (fld s (suc (suc zero)) ∷ fs) ρ (inj₁ (r , refl)) (z ,ᶠ zs) refl with ⟶-anti (ext renK (ext renK ρ)) r z refl
    ... | w , (r′ , refl) = (w ,ᶠ zs) , (inj₁ (r′ , refl) , refl)
    Step-anti (fld s (suc (suc zero)) ∷ fs) ρ (inj₂ (refl , st)) (z ,ᶠ zs) refl with Step-anti fs ρ st zs refl
    ... | ws , (st′ , refl) = (z ,ᶠ ws) , (inj₂ (refl , st′) , refl)
    Step-anti (fld s (suc (suc (suc k))) ∷ fs) ρ (inj₁ (r , refl)) (z ,ᶠ zs) refl with ⟶-anti (extN renK (suc (suc (suc k))) ρ) r z refl
    ... | w , (r′ , refl) = (w ,ᶠ zs) , (inj₁ (r′ , refl) , refl)
    Step-anti (fld s (suc (suc (suc k))) ∷ fs) ρ (inj₂ (refl , st)) (z ,ᶠ zs) refl with Step-anti fs ρ st zs refl
    ... | ws , (st′ , refl) = (z ,ᶠ ws) , (inj₂ (refl , st′) , refl)
    Step-anti (fnat ∷ fs) ρ (refl , st) (n ,ᶠ zs) refl with Step-anti fs ρ st zs refl
    ... | ws , (st′ , refl) = (n ,ᶠ ws) , ((refl , st′) , refl)
