------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3D (part 3) — CARRYING, REALIZED
--
--   * `K5′` — swapHead MULTIPLICATIVITY: carrying `x` past a tensor block
--     `B₁ ⊗ B₂` is carrying it past `B₁`, then past `B₂`, with α-plumbing:
--       αr ∘ ŝ_{x,B₁⊗B₂|S} ≈ (1_{B₁} ⊗ ŝ_{x,B₂|S}) ∘ (ŝ_{x,B₁|B₂⊗S} ∘ (1_x ⊗ αr))
--     Proof: THE Yang–Baxter recipe, shorter — F2 turns both head swaps
--     into block-σ moves, σ-naturality peels the common block-σ tail, G
--     rotates, and the residue is EXACTLY one pentagon + one α-naturality.
--   * `ŝ-αr` — the head transposition against the reassociator (a
--     two-step α-collapse; the `ι`-case of `nt-σ` consumes it).
--   * `insAcc-real` — END-INSERTION, REALIZED: inserting into the
--     accumulator inside a flattened block is flattening after carrying
--     the resource past the block:
--       insM (insAcc B i) ∘ (1_x ⊗ nt B S) ≈ (nt B S′ ∘ (1_B ⊗ insM i)) ∘ ŝ_{x,B|S}
--     Induction on `B`: leaves are unit shuffles, `I` is `K4` (the deep
--     unitor), `⊗` is both IHs + `swapHead-nat` + `K5′`.
--
-- These are the last lemmas `nt-σ` (the bswap square) needs.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonS where

open import normalizer.Syntax.Types
  using ( _≡_; refl )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-nat; ƛ-nat; σ-nat
        ; α-iso₁; α-iso₂; σ-invol; pentagon )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; norm; nt )
open import poc.OCP0009.NbEPMonP
  using ( Ins; here; there; insM; swapHead )
open import poc.OCP0009.NbEPMonA
  using ( insAcc )
open import poc.OCP0009.NbEPMonR
  using ( swapHead-nat )
open import poc.OCP0009.NbEPMonY
  using ( fuse⊗ˡ; fuse⊗ʳ; F2; G )
open import poc.OCP0009.NbEPMonK
  using ( K4 )

------------------------------------------------------------------------
-- K5′ — swapHead multiplicativity (the Yang–Baxter recipe, shorter).
------------------------------------------------------------------------

K5′ : ∀ {x B₁ B₂ S} →
      (αr {B₁} {B₂} {x ⊗ S} ∘m swapHead {x} {B₁ ⊗ B₂} {S}) ≈m
      ((idm {B₁} ⊗m swapHead {x} {B₂} {S}) ∘m
       (swapHead {x} {B₁} {B₂ ⊗ S} ∘m (idm {x} ⊗m αr)))
K5′ = ≈trans Lred (≈sym Rred)
  where
  Lred : ∀ {x B₁ B₂ S} →
         (αr {B₁} {B₂} {x ⊗ S} ∘m swapHead {x} {B₁ ⊗ B₂} {S}) ≈m
         ((αr ∘m ((idm {B₁ ⊗ B₂} ⊗m σm {S} {x}) ∘m αr)) ∘m σm {x} {(B₁ ⊗ B₂) ⊗ S})
  Lred =
    ≈trans (∘-congʳ F2)
    (≈trans (∘-congʳ (≈sym ∘-assoc))
            (≈sym ∘-assoc))
  Rred : ∀ {x B₁ B₂ S} →
         ((idm {B₁} ⊗m swapHead {x} {B₂} {S}) ∘m
          (swapHead {x} {B₁} {B₂ ⊗ S} ∘m (idm {x} ⊗m αr))) ≈m
         ((αr ∘m ((idm {B₁ ⊗ B₂} ⊗m σm {S} {x}) ∘m αr)) ∘m σm {x} {(B₁ ⊗ B₂) ⊗ S})
  Rred =
    ≈trans (∘-congʳ (∘-congˡ F2))
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
    (≈trans (∘-congʳ (∘-congʳ (∘-congʳ σ-nat)))
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ fuse⊗ˡ)
    (≈trans (∘-congˡ (⊗-cong ≈refl G))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (≈sym ∘-assoc)
            (∘-congˡ inner)))))))))
    where
    -- (1_{B₁} ⊗ ((1_{B₂}⊗σ) ∘ αr)) ∘ (αr ∘ (αr⊗1))
    --   ≈ αr ∘ ((1_{B₁⊗B₂}⊗σ) ∘ αr)   — pentagon + α-naturality.
    inner : ∀ {x B₁ B₂ S} →
            ((idm {B₁} ⊗m ((idm {B₂} ⊗m σm {S} {x}) ∘m αr)) ∘m
             (αr ∘m (αr {B₁} {B₂} {S} ⊗m idm {x}))) ≈m
            (αr ∘m ((idm {B₁ ⊗ B₂} ⊗m σm {S} {x}) ∘m αr))
    inner =
      ≈trans (∘-congˡ (≈sym fuse⊗ˡ))
      (≈trans ∘-assoc
      (≈trans (∘-congʳ pentagon)
      (≈trans (≈sym ∘-assoc)
      (≈trans (∘-congˡ (≈trans (≈sym α-nat)
                        (∘-congʳ (⊗-cong ⊗-id ≈refl))))
              ∘-assoc))))

------------------------------------------------------------------------
-- The head transposition against the reassociator (two-step collapse).
------------------------------------------------------------------------

ŝ-αr : ∀ {a B R} →
       (swapHead {a} {B} {R} ∘m αr {a} {B} {R}) ≈m (αr ∘m (σm {a} {B} ⊗m idm {R}))
ŝ-αr =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ α-iso₂))
          (∘-congʳ id-r)))

------------------------------------------------------------------------
-- insAcc-real — end-insertion, realized.
------------------------------------------------------------------------

insAcc-real : ∀ B {x S S'} (i : Ins x S S') →
              (insM (insAcc B i) ∘m (idm {x} ⊗m nt B S)) ≈m
              ((nt B S' ∘m (idm {B} ⊗m insM i)) ∘m swapHead {x} {B} {S})
insAcc-real ι₁ i =
  ≈trans (∘-congʳ ⊗-id) (≈trans id-r (≈sym (∘-congˡ id-l)))
insAcc-real ι₂ i =
  ≈trans (∘-congʳ ⊗-id) (≈trans id-r (≈sym (∘-congˡ id-l)))
insAcc-real I i =
  ≈sym (≈trans (∘-congˡ ƛ-nat) (≈trans ∘-assoc (∘-congʳ K4)))
insAcc-real (B₁ ⊗ B₂) {x} {S} {S'} i =
  ≈trans (∘-congʳ (≈sym fuse⊗ˡ))
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (insAcc-real B₁ (insAcc B₂ i)))
  (≈trans (∘-congʳ (≈sym fuse⊗ˡ))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ swapHead-nat))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ ∘-assoc)
  (≈trans (∘-congˡ (∘-congʳ fuse⊗ˡ))
  (≈trans (∘-congˡ (∘-congʳ (⊗-cong ≈refl (insAcc-real B₂ i))))
  (≈trans (∘-congˡ (∘-congʳ (≈sym fuse⊗ˡ)))
  (≈trans (∘-congˡ (∘-congʳ (∘-congˡ (≈sym fuse⊗ˡ))))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ (≈sym K5′)))
  (≈trans (∘-congʳ ∘-assoc)
          (≈sym rhs-shape))))))))))))))))))
  where
  rhs-shape :
    ((nt (B₁ ⊗ B₂) S' ∘m (idm {B₁ ⊗ B₂} ⊗m insM i)) ∘m swapHead {x} {B₁ ⊗ B₂} {S})
    ≈m
    (nt B₁ (norm B₂ S') ∘m
     ((idm {B₁} ⊗m nt B₂ S') ∘m
      ((idm {B₁} ⊗m (idm {B₂} ⊗m insM i)) ∘m
       (αr ∘m swapHead {x} {B₁ ⊗ B₂} {S}))))
  rhs-shape =
    ≈trans (∘-congˡ ∘-assoc)
    (≈trans (∘-congˡ (∘-congʳ ∘-assoc))
    (≈trans (∘-congˡ (∘-congʳ (∘-congʳ (≈trans
              (∘-congʳ (⊗-cong (≈sym ⊗-id) ≈refl)) α-nat))))
    (≈trans ∘-assoc
    (≈trans (∘-congʳ ∘-assoc)
            (∘-congʳ (∘-congʳ ∘-assoc))))))
