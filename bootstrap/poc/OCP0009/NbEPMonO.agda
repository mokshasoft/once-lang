------------------------------------------------------------------------
-- OCP-0009 · CONSOLIDATION — THE AXIOMS ARE REDUNDANT
--
-- The completeness theorem (`complete`, `NbEPMonE`) turns every
-- coherence AXIOM of the free SMC into a THEOREM: state the axiom at
-- fully generic types, check the wiring by finite case split, done.
-- This module re-derives, in one line each, results that cost the
-- completeness climb weeks of machine-checked work — and the axioms
-- themselves:
--
--   * the PENTAGON, the TRIANGLE, the HEXAGON — the Mac Lane axiom set,
--     recovered from wiring equality at generic A B D E;
--   * YANG–BAXTER for the conjugated head transposition — the braid
--     relation that `NbEPMonY` proved through F2/G/PENTL/PENT2 and one
--     interchange, here a four-way leaf split;
--   * `swapHead` involution and naturality-free commutation instances.
--
-- Moral (for the eventual kernel): once conversion is DECIDED, the
-- equational presentation is a convenience, not a trust surface — any
-- sound axiom whose wiring checks is admissible. The kernel need only
-- trust `wire`, `≈m-sound`, and `complete`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonO where

open import normalizer.Syntax.Types
  using ( _≡_; refl )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; Leaf; goL; goR; wire )
open import poc.OCP0009.NbEPMonP
  using ( swapHead )
open import poc.OCP0009.NbEPMonE
  using ( complete )

------------------------------------------------------------------------
-- The Mac Lane axioms, as theorems of the decision procedure.
------------------------------------------------------------------------

pentagon′ : ∀ {A B D E} →
            ((idm {A} ⊗m αr {B} {D} {E}) ∘m (αr ∘m (αr ⊗m idm {E})))
            ≈m (αr ∘m αr)
pentagon′ = complete _ _ λ
  { (goL a)               → refl
  ; (goR (goL b))         → refl
  ; (goR (goR (goL d)))   → refl
  ; (goR (goR (goR e)))   → refl
  }

triangle′ : ∀ {A B} →
            ((idm {A} ⊗m ƛr {B}) ∘m αr) ≈m (ρr ⊗m idm)
triangle′ = complete _ _ λ
  { (goL a) → refl
  ; (goR b) → refl
  }

hexagon′ : ∀ {A B D} →
           ((idm {B} ⊗m σm {A} {D}) ∘m (αr ∘m (σm {A} {B} ⊗m idm {D})))
           ≈m (αr ∘m (σm ∘m αr))
hexagon′ = complete _ _ λ
  { (goL b)         → refl
  ; (goR (goL d))   → refl
  ; (goR (goR a))   → refl
  }

σ-invol′ : ∀ {A B} → (σm {B} {A} ∘m σm {A} {B}) ≈m idm
σ-invol′ = complete _ _ λ
  { (goL a) → refl
  ; (goR b) → refl
  }

------------------------------------------------------------------------
-- YANG–BAXTER — the braid relation, one line. (`NbEPMonY` spent the
-- hexagon, two pentagon corollaries and an interchange on this.)
------------------------------------------------------------------------

YB′ : ∀ {x y z w} →
      ((idm {z} ⊗m swapHead {y} {x} {w}) ∘m
       (swapHead {y} {z} {x ⊗ w} ∘m (idm {y} ⊗m swapHead {x} {z} {w})))
      ≈m
      (swapHead {x} {z} {y ⊗ w} ∘m
       ((idm {x} ⊗m swapHead {y} {z} {w}) ∘m swapHead {y} {x} {z ⊗ w}))
YB′ = complete _ _ λ
  { (goL a)               → refl
  ; (goR (goL b))         → refl
  ; (goR (goR (goL d)))   → refl
  ; (goR (goR (goR s)))   → refl
  }

-- The head transposition is an involution — no proof term to invent.
ŝ-invol′ : ∀ {x y S} →
           (swapHead {y} {x} {S} ∘m swapHead {x} {y} {S}) ≈m idm
ŝ-invol′ = complete _ _ λ
  { (goL a)       → refl
  ; (goR (goL b)) → refl
  ; (goR (goR s)) → refl
  }
