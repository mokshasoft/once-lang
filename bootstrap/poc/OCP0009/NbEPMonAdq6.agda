------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A2b.2c — THE SWAP REALIZATIONS: A2 CLOSED
--
-- The last realization lemmas, completing the A2 layer:
--
--   * `ŝ-Iƛ`     : ŝ_{x,I} ∘ (1 ⊗ ƛl) ≈ ƛl   (K4C, inverted)
--   * `K5′ₗC`    : the αl-form of swapHead multiplicativity —
--     αl ∘ (1⊗ŝ) ∘ ŝ ≈ ŝ_{block} ∘ (1⊗αl)
--   * `mult-insEnd` : carrying past a whole block IS the head
--     transposition at the block — mult ∘ insC (insEnd Θ) ≈
--     ŝ_{x,⟪Θ⟫} ∘ (1 ⊗ mult)
--   * `mult-insˡ`   : insertion under a prefix
--   * `pidR-real`   : the ε-wart realizes as ρl (needs ƛ_I = ρ_I and
--     the right-unit triangle — Kelly earns its keep)
--   * `bswapW-real` : THE BLOCK SWAP REALIZES σ —
--       mult Δ Γ ∘ permC (bswapW Γ Δ) ≈ σ ∘ mult Γ Δ
--     (the nt-σ analogue; cons case = mult-insEnd + IH + σblk-αl,
--     NINE steps against nt-σ's multi-module campaign — the entire
--     dividend of list-normalized worlds in one comparison)
--
-- With this, EVERY operation of the world category that the model
-- uses (⊙P, padˡ, padʳ, insʳ, insˡ, insEnd, pid, pidR, bswapW) is
-- realized against the closed theory. A2 IS CLOSED; A3 (the Sp-tree
-- gluing relation and its splice lemmas) builds directly on these.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq6 where

open import poc.OCP0009.NbEPMonL
  using ( CTy; I; _⊗_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cƛ-nat
        ; cα-iso₁; cα-iso₂; cƛ-iso₁; cƛ-iso₂ )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; insˡ; insEnd; pidR; bswapW )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; swapHeadC; insC; permC; mult )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; cancelC; fuse⊗ˡC; fuse⊗ʳC )
open import poc.OCP0009.NbEPMonAdq2
  using ( inv-natC; α-natˡC; swapHeadC-nat; ⊗α-cancelˡ′C )
open import poc.OCP0009.NbEPMonAdq4
  using ( K4C; K5′C )
open import poc.OCP0009.NbEPMonAdq5
  using ( ƛρl-IC; σƛl; tri-ρlC; σblk-αl )

------------------------------------------------------------------------
-- The unit head-swap, inverted.
------------------------------------------------------------------------

ŝ-Iƛ : ∀ {x R} →
       (swapHeadC {x} {I} {R} ∘c (idc {x} ⊗c ƛlc {R})) ≈c ƛlc {x ⊗ R}
ŝ-Iƛ =
  ≈ctrans (∘c-congˡ ŝ-red)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ fuse⊗ˡC)
  (≈ctrans (∘c-congʳ (⊗c-cong ≈crefl cƛ-iso₁))
  (≈ctrans (∘c-congʳ c⊗-id) cid-r))))
  where
  ŝ-red : ∀ {x R} →
          swapHeadC {x} {I} {R} ≈c (ƛlc ∘c (idc {x} ⊗c ƛrc))
  ŝ-red =
    ≈ctrans (≈csym cid-l)
    (≈ctrans (∘c-congˡ (≈csym cƛ-iso₂))
    (≈ctrans c∘-assoc (∘c-congʳ K4C)))

------------------------------------------------------------------------
-- swapHead multiplicativity, αl-form.
------------------------------------------------------------------------

private
  K5′-post : ∀ {x B₁ B₂ S} →
             ((idc {B₁} ⊗c swapHeadC {x} {B₂} {S}) ∘c
              swapHeadC {x} {B₁} {B₂ ⊗ S}) ≈c
             ((αrc ∘c swapHeadC {x} {B₁ ⊗ B₂} {S}) ∘c
              (idc {x} ⊗c αlc {B₁} {B₂} {S}))
  K5′-post =
    ≈ctrans (≈csym cid-r)
    (≈ctrans (∘c-congʳ (≈csym ⊗α-cancelˡ′C))
    (≈ctrans (≈csym c∘-assoc)
             (∘c-congˡ (≈ctrans c∘-assoc (≈csym K5′C)))))

K5′ₗC : ∀ {x B₁ B₂ S} →
        (αlc {B₁} {B₂} {x ⊗ S} ∘c
         ((idc {B₁} ⊗c swapHeadC {x} {B₂} {S}) ∘c
          swapHeadC {x} {B₁} {B₂ ⊗ S})) ≈c
        (swapHeadC {x} {B₁ ⊗ B₂} {S} ∘c (idc {x} ⊗c αlc {B₁} {B₂} {S}))
K5′ₗC =
  ≈ctrans (∘c-congʳ K5′-post)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym c∘-assoc))
  (≈ctrans (∘c-congˡ (∘c-congˡ cα-iso₂))
           (∘c-congˡ cid-l))))

------------------------------------------------------------------------
-- Carrying past a block; insertion under a prefix.
------------------------------------------------------------------------

mult-insEnd : ∀ Θ {x xs} →
              (mult Θ (x ∷ xs) ∘c insC (insEnd Θ {x} {xs})) ≈c
              (swapHeadC {x} {⟪ Θ ⟫} {⟪ xs ⟫} ∘c (idc {x} ⊗c mult Θ xs))
mult-insEnd ε = ≈ctrans cid-r (≈csym ŝ-Iƛ)
mult-insEnd (A ∷ Θ) {x} {xs} =
  ≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ˡC))
  (≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong ≈crefl (mult-insEnd Θ))))
  (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym fuse⊗ˡC)))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym swapHeadC-nat)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ K5′ₗC)
  (≈ctrans c∘-assoc
           (∘c-congʳ fuse⊗ˡC)))))))))))

mult-insˡ : ∀ Θ {x xs ys} (i : Ins x xs ys) →
            (mult Θ ys ∘c insC (insˡ Θ i)) ≈c
            ((idc {⟪ Θ ⟫} ⊗c insC i) ∘c
             (swapHeadC {x} {⟪ Θ ⟫} {⟪ xs ⟫} ∘c (idc {x} ⊗c mult Θ xs)))
mult-insˡ ε i =
  ≈csym (≈ctrans (∘c-congʳ ŝ-Iƛ)
        (inv-natC cƛ-iso₂ cƛ-iso₁ cƛ-nat))
mult-insˡ (A ∷ Θ) {x} i =
  ≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ˡC))
  (≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong ≈crefl (mult-insˡ Θ i))))
  (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym fuse⊗ˡC)))
  (≈ctrans (∘c-congʳ (∘c-congˡ (∘c-congʳ (≈csym fuse⊗ˡC))))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym swapHeadC-nat))))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym α-natˡC))
  (≈ctrans (∘c-congˡ (∘c-congˡ (⊗c-cong c⊗-id ≈crefl)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ K5′ₗC))
  (≈ctrans (∘c-congʳ c∘-assoc)
           (∘c-congʳ (∘c-congʳ fuse⊗ˡC))))))))))))))))))

------------------------------------------------------------------------
-- The ε-wart realizes as ρl; the block swap realizes σ.
------------------------------------------------------------------------

pidR-real : ∀ Δ → (mult Δ ε ∘c permC (pidR Δ)) ≈c ρlc {⟪ Δ ⟫}
pidR-real ε       = ≈ctrans cid-r ƛρl-IC
pidR-real (A ∷ Δ) =
  ≈ctrans (∘c-congʳ cid-l)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ fuse⊗ˡC)
  (≈ctrans (∘c-congʳ (⊗c-cong ≈crefl (pidR-real Δ)))
           tri-ρlC)))

bswapW-real : ∀ Γ Δ →
              (mult Δ Γ ∘c permC (bswapW Γ Δ)) ≈c
              (σc {⟪ Γ ⟫} {⟪ Δ ⟫} ∘c mult Γ Δ)
bswapW-real ε       Δ = ≈ctrans (pidR-real Δ) (≈csym σƛl)
bswapW-real (A ∷ Γ) Δ =
  ≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (mult-insEnd Δ))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ fuse⊗ˡC)
  (≈ctrans (∘c-congʳ (⊗c-cong ≈crefl (bswapW-real Γ Δ)))
  (≈ctrans (∘c-congʳ (≈csym fuse⊗ˡC))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ σblk-αl)
           c∘-assoc)))))))
