------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3D (part 4) — THE MIRROR HEXAGON
--
--   * `inv-cong` — the generic INVERSE-OF-EQUATION combinator: from
--     `x ≈ y` and one-sided inverses, `x⁻¹ ≈ y⁻¹`.
--   * `H2` — the hexagon for the INVERSE braiding, derived (not
--     postulated): both sides of the hexagon axiom are isos; `inv-cong`
--     transports the axiom to their inverses.
--   * `σ-block` — the σ-TENSOR-MOVER decomposition, solved from `H2`:
--       σ_{B⊗D,A} ≈ αr ∘ (σ_{B,A}⊗1) ∘ αl ∘ (1_B⊗σ_{D,A}) ∘ αr
--     — a tensor block moves as a whole iff its parts move in sequence.
--     This is what the `⊗`-case of `nt-σ` consumes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonH where

open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-iso₁; α-iso₂; σ-invol; hexagon )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; cancel )
open import poc.OCP0009.NbEPMonY
  using ( ⊗σ-invol )

------------------------------------------------------------------------
-- Generic: equal isos have equal inverses.
------------------------------------------------------------------------

inv-cong : ∀ {P Q} {x y : STm P Q} {xi yi : STm Q P} →
           (x ∘m xi) ≈m idm → (yi ∘m y) ≈m idm → x ≈m y → xi ≈m yi
inv-cong p q e =
  ≈trans (≈sym id-l)
  (≈trans (∘-congˡ (≈sym q))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ (∘-congˡ (≈sym e)))
  (≈trans (∘-congʳ p) id-r))))

------------------------------------------------------------------------
-- The two hexagon sides are isos.
------------------------------------------------------------------------

private
  σ⊗-cancel : ∀ {A B D} →
              ((σm {A} {B} ⊗m idm {D}) ∘m (σm {B} {A} ⊗m idm)) ≈m idm
  σ⊗-cancel = ≈trans (≈sym ⊗-∘) (≈trans (⊗-cong σ-invol id-l) ⊗-id)

  -- L ∘ L⁻¹ ≈ id for the hexagon's left side.
  pL : ∀ {A B D} →
       (((idm {B} ⊗m σm {A} {D}) ∘m (αr ∘m (σm {A} {B} ⊗m idm {D}))) ∘m
        ((σm {B} {A} ⊗m idm {D}) ∘m (αl ∘m (idm {B} ⊗m σm {D} {A})))) ≈m idm
  pL =
    ≈trans (∘-congˡ (≈sym ∘-assoc))
    (≈trans (cancel σ⊗-cancel)
    (≈trans (cancel α-iso₁)
            ⊗σ-invol))

  -- R⁻¹ ∘ R ≈ id for the hexagon's right side.
  qR : ∀ {A B D} →
       ((αl {A} {B} {D} ∘m (σm {B ⊗ D} {A} ∘m αl)) ∘m
        (αr ∘m (σm {A} {B ⊗ D} ∘m αr))) ≈m idm
  qR =
    ≈trans (∘-congˡ (≈sym ∘-assoc))
    (≈trans (cancel α-iso₂)
    (≈trans (cancel σ-invol)
            α-iso₂))

------------------------------------------------------------------------
-- H2 — the mirror hexagon.
------------------------------------------------------------------------

H2 : ∀ {A B D} →
     ((σm {B} {A} ⊗m idm {D}) ∘m (αl ∘m (idm {B} ⊗m σm {D} {A}))) ≈m
     (αl ∘m (σm {B ⊗ D} {A} ∘m αl))
H2 = inv-cong pL qR hexagon

------------------------------------------------------------------------
-- σ-block — the tensor-mover decomposition, solved from H2.
------------------------------------------------------------------------

σ-block : ∀ {A B D} →
          σm {B ⊗ D} {A} ≈m
          (αr ∘m (((σm {B} {A} ⊗m idm {D}) ∘m (αl ∘m (idm {B} ⊗m σm {D} {A}))) ∘m αr))
σ-block =
  ≈sym
  (≈trans (∘-congʳ (∘-congˡ H2))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ α-iso₁)
  (≈trans id-l
  (≈trans ∘-assoc
  (≈trans (∘-congʳ α-iso₂) id-r)))))))
