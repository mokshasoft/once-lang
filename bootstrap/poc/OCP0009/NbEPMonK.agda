------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3D (part 2) — THE UNIT-σ CLUSTER
--
-- The classical unit coherence lemmas for symmetry, machine-checked:
--
--   * `K3′ : ƛ_B ∘ σ_{B,I} ≈ ρ_B` and `K3 : ρ_B ∘ σ_{I,B} ≈ ƛ_B` —
--     Joyal–Street's "the two unitors agree through the braiding".
--     Proof: instantiate the HEXAGON at (B, I, C), postcompose with `ƛ`,
--     reduce both paths with `K2` (twice), `ƛ`-naturality, `σ`-naturality
--     and the triangle — both land on `σ_{B,C} ∘ (— ⊗ 1_C)` forms; cancel
--     `σ ∘ −` (by involution) and then `− ⊗ 1_I` (by `ρ`-conjugation,
--     the mirror of 3D part 1's `cancel-1I`).
--   * `K4 : ƛ ∘ swapHead_{x,I} ≈ 1_x ⊗ ƛ` — carrying a resource past the
--     empty block is the deep unitor. `K2` + `K3′` + the triangle.
--
-- These are exactly what the base cases of `nt-σ` (the bswap square)
-- consume.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonK where

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
  using ( ∘-congˡ; ∘-congʳ )
open import poc.OCP0009.NbEPMonP
  using ( swapHead )
open import poc.OCP0009.NbEPMonY
  using ( fuse⊗ˡ; fuse⊗ʳ )
open import poc.OCP0009.NbEPMonG
  using ( K2 )

------------------------------------------------------------------------
-- Cancellation combinators.
------------------------------------------------------------------------

-- σ ∘ − is cancellable (σ is an involution).
cancel-σˡ : ∀ {A B D} {f g : STm D (A ⊗ B)} →
            (σm {A} {B} ∘m f) ≈m (σm ∘m g) → f ≈m g
cancel-σˡ p =
  ≈trans (≈sym id-l)
  (≈trans (∘-congˡ (≈sym σ-invol))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ p)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ σ-invol) id-l)))))

-- − ⊗ 1_I is cancellable (ρ-conjugation).
conj-ρ : ∀ {A B} (f : STm A B) → f ≈m ((ρr ∘m (f ⊗m idm {I})) ∘m ρl)
conj-ρ f =
  ≈trans (≈sym id-r)
  (≈trans (∘-congʳ (≈sym ρ-iso₁))
  (≈trans (≈sym ∘-assoc)
          (∘-congˡ (≈sym ρ-nat))))

cancel-I1 : ∀ {A B} {f g : STm A B} →
            (f ⊗m idm {I}) ≈m (g ⊗m idm) → f ≈m g
cancel-I1 {f = f} {g} p =
  ≈trans (conj-ρ f)
  (≈trans (∘-congˡ (∘-congʳ p))
          (≈sym (conj-ρ g)))

-- The triangle, solved for `1_A ⊗ ƛ_B` (general form).
tri-solveg : ∀ {A B} → (idm {A} ⊗m ƛr {B}) ≈m ((ρr ⊗m idm) ∘m αl)
tri-solveg =
  ≈trans (≈sym id-r)
  (≈trans (∘-congʳ (≈sym α-iso₁))
  (≈trans (≈sym ∘-assoc)
          (∘-congˡ triangle)))

------------------------------------------------------------------------
-- The hexagon at (B, I, C), squeezed: (ƛ∘σ)⊗1 ≈ ρ⊗1, then cancel.
------------------------------------------------------------------------

λσ⊗ : ∀ {B C} → ((ƛr {B} ∘m σm {B} {I}) ⊗m idm {C}) ≈m (ρr {B} ⊗m idm {C})
λσ⊗ {B} {C} =
  cancel-σˡ (≈trans (≈sym chainX) (≈trans (∘-congʳ hexagon) chainY))
  where
  chainX : (ƛr {C ⊗ B} ∘m
            ((idm {I} ⊗m σm {B} {C}) ∘m (αr ∘m (σm {B} {I} ⊗m idm {C}))))
           ≈m (σm {B} {C} ∘m ((ƛr {B} ∘m σm {B} {I}) ⊗m idm {C}))
  chainX =
    ≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ ƛ-nat)
    (≈trans ∘-assoc
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ (≈sym K2)))
            (∘-congʳ fuse⊗ʳ)))))
  chainY : (ƛr {C ⊗ B} ∘m (αr ∘m (σm {B} {I ⊗ C} ∘m αr)))
           ≈m (σm {B} {C} ∘m (ρr {B} ⊗m idm {C}))
  chainY =
    ≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ (≈sym K2))
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ (≈sym σ-nat))
    (≈trans ∘-assoc
            (∘-congʳ triangle)))))

K3′ : ∀ {B} → (ƛr {B} ∘m σm {B} {I}) ≈m ρr {B}
K3′ = cancel-I1 λσ⊗

K3 : ∀ {B} → (ρr {B} ∘m σm {I} {B}) ≈m ƛr {B}
K3 =
  ≈trans (∘-congˡ (≈sym K3′))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ σ-invol) id-r))

------------------------------------------------------------------------
-- K4 — carrying past the empty block is the deep unitor.
------------------------------------------------------------------------

K4 : ∀ {x S} → (ƛr {x ⊗ S} ∘m swapHead {x} {I} {S}) ≈m (idm {x} ⊗m ƛr {S})
K4 =
  ≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (≈sym K2))
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ fuse⊗ʳ)
  (≈trans (∘-congˡ (⊗-cong K3′ ≈refl))
          (≈sym tri-solveg)))))
