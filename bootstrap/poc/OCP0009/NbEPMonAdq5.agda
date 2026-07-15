------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A2b.2b — KELLY, PART II + THE σ-BLOCK
--
-- The remaining classical lemmas the swap realizations consume:
--
--   * `lem-ƛ⊗`  : 1_I ⊗ ƛ_B ≈ ƛ_{I⊗B}       (one line, by ƛ-cancel)
--   * `ƛρ-IC`   : ƛ_I ≈ ρ_I                  (Kelly's unit identity)
--   * `σƛl`     : σ_{I,B} ∘ ƛl ≈ ρl          (K3, inverted)
--   * `tri-ρC`  : ρ_{A⊗B} ≈ (1_A ⊗ ρ_B) ∘ α  (the RIGHT-UNIT triangle
--     — derived in 14 steps via the σ-block, K2, K3′ and the solved
--     middle triangle; the classical pentagon-only proof is longer)
--   * `tri-ρlC` : its l-form, by inverse congruence
--   * `pLC`/`qRC`/`H2C`/`σ-blockC` — the mirror hexagon and the
--     σ-TENSOR-MOVER decomposition (`NbEPMonH`'s recipes, ported)
--   * `σblk-αl` : ŝ ∘ (1 ⊗ σ) ≈ σ_{block} ∘ αl — the corollary
--     `bswapW-real`'s cons case lands on.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq5 where

open import poc.OCP0009.NbEPMonL
  using ( CTy; I; _⊗_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cα-nat; cƛ-nat; cρ-nat; cσ-nat
        ; cα-iso₁; cα-iso₂; cƛ-iso₁; cƛ-iso₂; cρ-iso₁; cρ-iso₂
        ; cσ-invol; cpentagon; ctriangle; chexagon )
open import poc.OCP0009.NbEPMonW
  using ( swapHeadC )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; cancelC; fuse⊗ˡC; fuse⊗ʳC )
open import poc.OCP0009.NbEPMonAdq2
  using ( ⊗σ-involC )
open import poc.OCP0009.NbEPMonAdq3
  using ( inv-congC )
open import poc.OCP0009.NbEPMonAdq4
  using ( K2C; K3′C; K3C; cancel-I1C; tri-solvegC )

------------------------------------------------------------------------
-- Kelly, part II.
------------------------------------------------------------------------

-- Left-cancellation by ƛr (an iso).
cancel-ƛˡC : ∀ {D A} {f g : CTm D (I ⊗ A)} →
             (ƛrc ∘c f) ≈c (ƛrc ∘c g) → f ≈c g
cancel-ƛˡC p =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym cƛ-iso₂))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ p)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ cƛ-iso₂) cid-l)))))

lem-ƛ⊗ : ∀ {B} → (idc {I} ⊗c ƛrc {B}) ≈c ƛrc {I ⊗ B}
lem-ƛ⊗ = cancel-ƛˡC cƛ-nat

ƛρ-IC : ƛrc {I} ≈c ρrc {I}
ƛρ-IC =
  cancel-I1C (≈ctrans K2C
             (≈ctrans (∘c-congˡ (≈csym lem-ƛ⊗)) ctriangle))

ƛρl-IC : ƛlc {I} ≈c ρlc {I}
ƛρl-IC = inv-congC cƛ-iso₁ cρ-iso₂ ƛρ-IC

-- σ against the left unitor's inverse is the right unitor's inverse.
σƛl : ∀ {B} → (σc {I} {B} ∘c ƛlc {B}) ≈c ρlc {B}
σƛl =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym cρ-iso₂))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ inner) cid-r)))
  where
  inner : ∀ {B} → (ρrc {B} ∘c (σc {I} {B} ∘c ƛlc)) ≈c idc
  inner =
    ≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ K3C) cƛ-iso₁)

------------------------------------------------------------------------
-- The σ-block (NbEPMonH's recipes, ported).
------------------------------------------------------------------------

private
  pLC : ∀ {A B D} →
        (((idc {B} ⊗c σc {A} {D}) ∘c (αrc ∘c (σc {A} {B} ⊗c idc {D}))) ∘c
         ((σc {B} {A} ⊗c idc {D}) ∘c (αlc ∘c (idc {B} ⊗c σc {D} {A})))) ≈c idc
  pLC =
    ≈ctrans (∘c-congˡ (≈csym c∘-assoc))
    (≈ctrans (cancelC σ⊗-cancel)
    (≈ctrans (cancelC cα-iso₁)
             ⊗σ-involC))
    where
    σ⊗-cancel : ∀ {A B D} →
                ((σc {A} {B} ⊗c idc {D}) ∘c (σc {B} {A} ⊗c idc)) ≈c idc
    σ⊗-cancel =
      ≈ctrans (≈csym c⊗-∘) (≈ctrans (⊗c-cong cσ-invol cid-l) c⊗-id)

  qRC : ∀ {A B D} →
        ((αlc {A} {B} {D} ∘c (σc {B ⊗ D} {A} ∘c αlc)) ∘c
         (αrc ∘c (σc {A} {B ⊗ D} ∘c αrc))) ≈c idc
  qRC =
    ≈ctrans (∘c-congˡ (≈csym c∘-assoc))
    (≈ctrans (cancelC cα-iso₂)
    (≈ctrans (cancelC cσ-invol)
             cα-iso₂))

H2C : ∀ {A B D} →
      ((σc {B} {A} ⊗c idc {D}) ∘c (αlc ∘c (idc {B} ⊗c σc {D} {A}))) ≈c
      (αlc ∘c (σc {B ⊗ D} {A} ∘c αlc))
H2C = inv-congC pLC qRC chexagon

σ-blockC : ∀ {A B D} →
           σc {B ⊗ D} {A} ≈c
           (αrc ∘c (((σc {B} {A} ⊗c idc {D}) ∘c
                     (αlc ∘c (idc {B} ⊗c σc {D} {A}))) ∘c αrc))
σ-blockC =
  ≈csym
  (≈ctrans (∘c-congʳ (∘c-congˡ H2C))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ cα-iso₁)
  (≈ctrans cid-l
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ cα-iso₂) cid-r)))))))

-- ŝ ∘ (1 ⊗ σ) ≈ σ_block ∘ αl — what bswapW-real's cons case lands on.
σblk-αl : ∀ {A W D} →
          (swapHeadC {A} {D} {W} ∘c (idc {A} ⊗c σc {W} {D})) ≈c
          (σc {A ⊗ W} {D} ∘c αlc {A} {W} {D})
σblk-αl =
  ≈csym
  (≈ctrans (∘c-congˡ σ-blockC)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ cα-iso₁))
  (≈ctrans (∘c-congʳ cid-r)
           (≈csym (≈ctrans c∘-assoc (∘c-congʳ c∘-assoc))))))))

------------------------------------------------------------------------
-- The right-unit triangle (via the σ-block — 14 steps).
------------------------------------------------------------------------

tri-ρC : ∀ {A B} →
         ρrc {A ⊗ B} ≈c ((idc {A} ⊗c ρrc {B}) ∘c αrc {A} {B} {I})
tri-ρC {A} {B} =
  ≈ctrans (≈csym K3′C)
  (≈ctrans (∘c-congʳ σ-blockC)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym K2C))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym c∘-assoc))
  (≈ctrans (∘c-congˡ (∘c-congˡ fuse⊗ʳC))
  (≈ctrans (∘c-congˡ (∘c-congˡ (⊗c-cong K3′C ≈crefl)))
  (≈ctrans (∘c-congˡ (≈csym c∘-assoc))
  (≈ctrans (∘c-congˡ (∘c-congˡ (≈csym tri-solvegC)))
  (≈ctrans (∘c-congˡ fuse⊗ˡC)
           (∘c-congˡ (⊗c-cong ≈crefl K3′C))))))))))))

-- The l-form, by inverse congruence.
tri-ρlC : ∀ {A B} →
          (αlc {A} {B} {I} ∘c (idc {A} ⊗c ρlc {B})) ≈c ρlc {A ⊗ B}
tri-ρlC =
  ≈csym (inv-congC cρ-iso₁ q tri-ρC)
  where
  q : ∀ {A B} →
      ((αlc {A} {B} {I} ∘c (idc ⊗c ρlc {B})) ∘c
       ((idc ⊗c ρrc) ∘c αrc)) ≈c idc
  q =
    ≈ctrans (cancelC (≈ctrans fuse⊗ˡC
                     (≈ctrans (⊗c-cong ≈crefl cρ-iso₂) c⊗-id)))
            cα-iso₂
