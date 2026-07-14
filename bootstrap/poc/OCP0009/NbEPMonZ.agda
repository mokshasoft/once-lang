------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3D (final) — nt-σ: THE BSWAP SQUARE
--
-- The last generator square: flattening intertwines the symmetry with the
-- block transposition —
--
--   nt-σ : nt (B⊗A) R ∘ (σ_{A,B} ⊗ 1_R) ≈ permM (bswap A B r) ∘ nt (A⊗B) R
--
-- Induction on `A`, each case consuming exactly the machinery built for
-- it:
--   * `A = I`  — triangle + `K3` (ρ∘σ ≈ ƛ, the unit-σ cluster) + `K2`;
--     both sides meet at `nt B R ∘ (ƛ_B ⊗ 1_R)`.
--   * `A = ι`  — `insAcc-real` at `here` + `ŝ-αr` + `pid-real`.
--   * `A = A₁⊗A₂` — the boss: `σ-block` (the tensor-mover decomposition
--     from the mirror hexagon) splits the symmetry into two block moves;
--     `nt-α`/`nt-αl` absorb the α-dressing; the `σ_{A₁,B}` move meets
--     IH₁ after α-naturality + interchange; the deep `σ_{A₂,B}` move
--     meets IH₂ + `nt-perm-nat` (padding); `⊙P-real` reassembles — and
--     the composite lands on `permM (bswap (A₁⊗A₂) B r) ∘ nt` on the
--     nose, because `bswap`'s definition IS this decomposition.
--
-- Also: `nt-αl` (the inverse reassociator square, 5-step conjugation).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonZ where

open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-nat; ƛ-nat; σ-nat
        ; α-iso₁; α-iso₂; triangle )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; norm; nt )
open import poc.OCP0009.NbEPMonP
  using ( Lf; lf₁; lf₂; IsL; lnil; lcons; isL-norm
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; insM; permM; swapHead )
open import poc.OCP0009.NbEPMonA
  using ( ins-swap; push; _⊙P_; padP; insAcc; bswap )
open import poc.OCP0009.NbEPMonY
  using ( fuse⊗ˡ; fuse⊗ʳ; interchange )
open import poc.OCP0009.NbEPMonQ
  using ( ⊙P-real; nt-perm-nat )
open import poc.OCP0009.NbEPMonG
  using ( pid-real; nt-α; K2 )
open import poc.OCP0009.NbEPMonK
  using ( K3 )
open import poc.OCP0009.NbEPMonS
  using ( ŝ-αr; insAcc-real )
open import poc.OCP0009.NbEPMonH
  using ( σ-block )

------------------------------------------------------------------------
-- The inverse reassociator square (conjugation from nt-α).
------------------------------------------------------------------------

nt-αl : ∀ {A B D R} →
        (nt ((A ⊗ B) ⊗ D) R ∘m (αl {A} {B} {D} ⊗m idm {R})) ≈m
        nt (A ⊗ (B ⊗ D)) R
nt-αl =
  ≈trans (∘-congˡ (≈sym nt-α))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ fuse⊗ʳ)
  (≈trans (∘-congʳ (≈trans (⊗-cong α-iso₁ ≈refl) ⊗-id))
          id-r)))

------------------------------------------------------------------------
-- nt-σ — the bswap square.
------------------------------------------------------------------------

nt-σ : ∀ A B {R} (r : IsL R) →
       (nt (B ⊗ A) R ∘m (σm {A} {B} ⊗m idm {R})) ≈m
       (permM (bswap A B r) ∘m nt (A ⊗ B) R)

nt-σ I B r =
  ≈trans (∘-congˡ (∘-congʳ triangle))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ fuse⊗ʳ)
  (≈trans (∘-congʳ (⊗-cong K3 ≈refl))
  (≈trans (∘-congʳ K2)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (≈sym ƛ-nat))
          (≈trans ∘-assoc
                  (≈sym (≈trans (∘-congˡ (pid-real (isL-norm B r))) id-l)))))))))

nt-σ ι₁ B r =
  ≈trans lhs-red (≈sym (rhs-red r))
  where
  lhs-red : ∀ {R} →
    (nt (B ⊗ ι₁) R ∘m (σm ⊗m idm {R})) ≈m
    (nt B (ι₁ ⊗ R) ∘m (αr ∘m (σm ⊗m idm)))
  lhs-red =
    ≈trans (∘-congˡ (∘-congʳ (≈trans (∘-congˡ ⊗-id) id-l)))
            ∘-assoc
  rhs-red : ∀ {R} (r : IsL R) →
    (permM (bswap ι₁ B r) ∘m nt (ι₁ ⊗ B) R) ≈m
    (nt B (ι₁ ⊗ R) ∘m (αr ∘m (σm ⊗m idm)))
  rhs-red r =
    ≈trans (∘-congˡ (≈trans (∘-congʳ (≈trans (⊗-cong ≈refl (pid-real (isL-norm B r))) ⊗-id)) id-r))
    (≈trans (∘-congʳ id-l)
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ (insAcc-real B here))
    (≈trans (∘-congˡ (≈trans (∘-congˡ (≈trans (∘-congʳ ⊗-id) id-r)) ≈refl))
    (≈trans ∘-assoc
            (∘-congʳ ŝ-αr))))))

nt-σ ι₂ B r =
  ≈trans lhs-red (≈sym (rhs-red r))
  where
  lhs-red : ∀ {R} →
    (nt (B ⊗ ι₂) R ∘m (σm ⊗m idm {R})) ≈m
    (nt B (ι₂ ⊗ R) ∘m (αr ∘m (σm ⊗m idm)))
  lhs-red =
    ≈trans (∘-congˡ (∘-congʳ (≈trans (∘-congˡ ⊗-id) id-l)))
            ∘-assoc
  rhs-red : ∀ {R} (r : IsL R) →
    (permM (bswap ι₂ B r) ∘m nt (ι₂ ⊗ B) R) ≈m
    (nt B (ι₂ ⊗ R) ∘m (αr ∘m (σm ⊗m idm)))
  rhs-red r =
    ≈trans (∘-congˡ (≈trans (∘-congʳ (≈trans (⊗-cong ≈refl (pid-real (isL-norm B r))) ⊗-id)) id-r))
    (≈trans (∘-congʳ id-l)
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ (insAcc-real B here))
    (≈trans (∘-congˡ (≈trans (∘-congˡ (≈trans (∘-congʳ ⊗-id) id-r)) ≈refl))
    (≈trans ∘-assoc
            (∘-congʳ ŝ-αr))))))

nt-σ (A₁ ⊗ A₂) B {R} r =
  ≈trans lhs-to-M (≈sym rhs-to-M)
  where
  q₂ = bswap A₂ B r
  q₁ = bswap A₁ B (isL-norm A₂ r)

  rhs-to-M :
    (permM (bswap (A₁ ⊗ A₂) B r) ∘m nt ((A₁ ⊗ A₂) ⊗ B) R) ≈m
    (permM q₁ ∘m (permM (padP A₁ q₂) ∘m nt ((A₁ ⊗ A₂) ⊗ B) R))
  rhs-to-M = ≈trans (∘-congˡ (⊙P-real (padP A₁ q₂) q₁)) ∘-assoc

  -- 4b: the σ_{A₁,B} move meets IH₁.
  nt₃F :
    (nt ((B ⊗ A₁) ⊗ A₂) R ∘m ((σm {A₁} {B} ⊗m idm {A₂}) ⊗m idm {R})) ≈m
    (permM q₁ ∘m nt ((A₁ ⊗ B) ⊗ A₂) R)
  nt₃F =
    ≈trans ∘-assoc
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (∘-congʳ (∘-congʳ α-nat))
    (≈trans (∘-congʳ (∘-congʳ (∘-congˡ (⊗-cong ≈refl ⊗-id))))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ (≈sym interchange)))
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ (nt-σ A₁ B (isL-norm A₂ r)))
            ∘-assoc))))))))

  -- 6b: the deep σ_{A₂,B} move meets IH₂ + padding.
  deepσ :
    (nt (A₁ ⊗ (B ⊗ A₂)) R ∘m ((idm {A₁} ⊗m σm {A₂} {B}) ⊗m idm {R})) ≈m
    (permM (padP A₁ q₂) ∘m nt (A₁ ⊗ (A₂ ⊗ B)) R)
  deepσ =
    ≈trans ∘-assoc
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (∘-congʳ (∘-congʳ α-nat))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ fuse⊗ˡ))
    (≈trans (∘-congʳ (∘-congˡ (⊗-cong ≈refl (nt-σ A₂ B r))))
    (≈trans (∘-congʳ (∘-congˡ (≈sym fuse⊗ˡ)))
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ (nt-perm-nat A₁ q₂))
            ∘-assoc)))))))))

  split-chain :
    ((αr ∘m (((σm {A₁} {B} ⊗m idm {A₂}) ∘m (αl ∘m (idm {A₁} ⊗m σm {A₂} {B}))) ∘m αr)) ⊗m idm {R}) ≈m
    ((αr ⊗m idm) ∘m ((((σm ⊗m idm) ⊗m idm) ∘m ((αl ⊗m idm) ∘m ((idm ⊗m σm) ⊗m idm))) ∘m (αr ⊗m idm)))
  split-chain =
    ≈trans (≈sym fuse⊗ʳ)
    (∘-congʳ (≈trans (≈sym fuse⊗ʳ)
             (∘-congˡ (≈trans (≈sym fuse⊗ʳ)
                      (∘-congʳ (≈sym fuse⊗ʳ))))))

  lhs-to-M :
    (nt (B ⊗ (A₁ ⊗ A₂)) R ∘m (σm {A₁ ⊗ A₂} {B} ⊗m idm {R})) ≈m
    (permM q₁ ∘m (permM (padP A₁ q₂) ∘m nt ((A₁ ⊗ A₂) ⊗ B) R))
  lhs-to-M =
    ≈trans (∘-congʳ (⊗-cong σ-block ≈refl))
    (≈trans (∘-congʳ split-chain)
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ nt-α)
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ nt₃F)
    (≈trans ∘-assoc
    (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ nt-αl))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ deepσ))
    (≈trans (∘-congʳ ∘-assoc)
            (∘-congʳ (∘-congʳ nt-α)))))))))))))))
