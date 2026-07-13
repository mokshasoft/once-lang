------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3C.1 — the `swapHead` TOOLKIT
--
-- The realization-compatibility layer (stage 3C) reduces, case by case,
-- to a small toolkit of facts about the conjugated head transposition
-- `swapHead = αr ∘ (σ ⊗ id) ∘ αl`. This module proves them:
--
--   * `inv-nat` — the generic INVERSE-NATURALITY combinator: from a
--     naturality square for `u` and two-sided inverses, the square for
--     `u`'s inverse. (Used to derive `αl`-naturality from `αr`'s, and
--     reusable for every iso in the theory.)
--   * `α-natˡ`  — naturality of the reassociator's inverse, derived.
--   * `swapHead-nat` — `swapHead` is natural in all three positions:
--     `swapHead ∘ (f ⊗ (g ⊗ h)) ≈ (g ⊗ (f ⊗ h)) ∘ swapHead`. This is the
--     COMMUTATION half of the symmetric-group presentation (far-apart
--     transpositions commute — here: a transposition commutes past
--     anything happening elsewhere).
--   * `swapHead-invol` — `swapHead ∘ swapHead ≈ id` (the transposition is
--     an involution).
--
-- What remains of 3C after this (recorded in plan §10): the BRAID half —
-- Yang–Baxter for `swapHead`, derived from the hexagon — and then the
-- per-operation compatibility proofs (`ins-swap-real`, `push-real`,
-- `⊙P-real`, `nt-perm-nat`) that consume this toolkit.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonR where

open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-nat; ƛ-nat; ρ-nat; σ-nat
        ; α-iso₁; α-iso₂; ƛ-iso₁; ƛ-iso₂; ρ-iso₁; ρ-iso₂
        ; σ-invol; pentagon; triangle; hexagon )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; cancel )
open import poc.OCP0009.NbEPMonP
  using ( swapHead )

------------------------------------------------------------------------
-- Generic inverse-naturality: from `u ∘ Y ≈ X ∘ u'` and the iso pairs,
-- conclude `Y ∘ v' ≈ v ∘ X`.
------------------------------------------------------------------------

inv-nat : ∀ {L L' R R' : MTy}
          {u : STm L' R'} {v : STm R' L'} {u' : STm L R} {v' : STm R L}
          {Y : STm L L'} {X : STm R R'} →
          (v ∘m u) ≈m idm → (u' ∘m v') ≈m idm →
          (u ∘m Y) ≈m (X ∘m u') →
          (Y ∘m v') ≈m (v ∘m X)
inv-nat p q nat =
  ≈trans (≈sym id-l)
  (≈trans (∘-congˡ (≈sym p))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ nat))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ q))
          (∘-congʳ id-r)))))))

-- Naturality of the inverse reassociator, derived.
α-natˡ : ∀ {A B D A' B' D'} {f : STm A A'} {g : STm B B'} {h : STm D D'} →
         (((f ⊗m g) ⊗m h) ∘m αl) ≈m (αl ∘m (f ⊗m (g ⊗m h)))
α-natˡ = inv-nat α-iso₂ α-iso₁ α-nat

------------------------------------------------------------------------
-- swapHead is natural in all three positions (the COMMUTATION relation).
------------------------------------------------------------------------

swapHead-nat : ∀ {x y W x' y' W'} {f : STm x x'} {g : STm y y'} {h : STm W W'} →
               (swapHead ∘m (f ⊗m (g ⊗m h))) ≈m ((g ⊗m (f ⊗m h)) ∘m swapHead)
swapHead-nat {f = f} {g} {h} =
  -- swapHead ∘ (f⊗(g⊗h))  =  (αr ∘ ((σ⊗id) ∘ αl)) ∘ (f⊗(g⊗h))
  ≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  -- αr ∘ ((σ⊗id) ∘ (αl ∘ (f⊗(g⊗h))))
  (≈trans (∘-congʳ (∘-congʳ (≈sym α-natˡ)))
  -- αr ∘ ((σ⊗id) ∘ (((f⊗g)⊗h) ∘ αl))
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  -- αr ∘ (((σ⊗id) ∘ ((f⊗g)⊗h)) ∘ αl)
  (≈trans (∘-congʳ (∘-congˡ step-σ))
  -- αr ∘ ((((g⊗f)⊗h) ∘ (σ⊗id)) ∘ αl)
  (≈trans (∘-congʳ ∘-assoc)
  -- αr ∘ (((g⊗f)⊗h) ∘ ((σ⊗id) ∘ αl))
  (≈trans (≈sym ∘-assoc)
  -- (αr ∘ ((g⊗f)⊗h)) ∘ ((σ⊗id) ∘ αl)
  (≈trans (∘-congˡ α-nat)
  -- ((g⊗(f⊗h)) ∘ αr) ∘ ((σ⊗id) ∘ αl)
  ∘-assoc)))))))
  -- (g⊗(f⊗h)) ∘ (αr ∘ ((σ⊗id) ∘ αl))  =  (g⊗(f⊗h)) ∘ swapHead
  where
  step-σ : ∀ {x y W x' y' W'} {f : STm x x'} {g : STm y y'} {h : STm W W'} →
           ((σm ⊗m idm) ∘m ((f ⊗m g) ⊗m h)) ≈m (((g ⊗m f) ⊗m h) ∘m (σm ⊗m idm))
  step-σ =
    ≈trans (≈sym ⊗-∘)
    (≈trans (⊗-cong σ-nat (≈trans id-l (≈sym id-r)))
            ⊗-∘)

------------------------------------------------------------------------
-- swapHead is an involution.
------------------------------------------------------------------------

swapHead-invol : ∀ {x y W} →
                 (swapHead {y} {x} {W} ∘m swapHead {x} {y} {W}) ≈m idm
swapHead-invol =
  ≈trans (∘-congˡ (≈sym ∘-assoc))
  -- ((αr ∘ (σ⊗id)) ∘ αl) ∘ (αr ∘ ((σ⊗id) ∘ αl))
  (≈trans (cancel α-iso₂)
  -- (αr ∘ (σ⊗id)) ∘ ((σ⊗id) ∘ αl)
  (≈trans (cancel σ⊗-cancel)
  -- αr ∘ αl
          α-iso₁))
  where
  σ⊗-cancel : ∀ {x y W} →
              ((σm {y} {x} ⊗m idm {W}) ∘m (σm {x} {y} ⊗m idm)) ≈m idm
  σ⊗-cancel = ≈trans (≈sym ⊗-∘) (≈trans (⊗-cong σ-invol id-l) ⊗-id)
