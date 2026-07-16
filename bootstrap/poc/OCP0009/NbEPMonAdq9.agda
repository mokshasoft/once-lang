------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A3b.2 — THE NODE ALGEBRA
--
-- The shared structural lemmas the withSp/go splice proofs consume.
-- Every Sp node written by the (transport-free) model carries a
-- permutation of the shape `(ρ ⊙P padʳ Γ₂ q) ⊙P passoc`; this module
-- reduces its mult-composite to realized parts, and collapses the
-- head-plumbing that the spl/usI cases then meet:
--
--   * `PENTAR`        — the pentagon, solved for `αr ⊗ 1`
--   * `mult-head²`    — the two-head collapse: what the spl-case's
--     α/multInv-dressing reduces to (lands exactly on PENTAR)
--   * `mult-headI`    — the unit-head collapse: the usI-case's
--     dressing (lands exactly on K2C)
--   * `n-α`           — sliding a neutral out of a reassociation
--   * `node-perm-real`— THE NODE PERMUTATION, REALIZED:
--       mult ∘ permC ((ρ ⊙P padʳ q) ⊙P passoc) ≈
--       (1 ⊗ multInv) ∘ αr ∘ ((mult ∘ permC q) ⊗ 1) ∘ (mult ∘ permC ρ)
--     — ⊙P-realC twice, passoc-real, padʳ-real, and reassociation.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq9 where

open import poc.OCP0009.NbEPMonL
  using ( CTy; I; _⊗_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cα-nat; cƛ-nat
        ; cα-iso₁; cα-iso₂; cpentagon )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pnil; pcons; pid
        ; _⊙P_; padˡ; padʳ; passoc; passocInv )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; fuse⊗ˡC; fuse⊗ʳC; mult-inv-r )
open import poc.OCP0009.NbEPMonAdq2
  using ( ⊗α-cancelˡC; ⊙P-realC; interchangeC )
open import poc.OCP0009.NbEPMonAdq3
  using ( mult-insʳ )
open import poc.OCP0009.NbEPMonAdq4
  using ( K2C )
open import poc.OCP0009.NbEPMonAdq8
  using ( passoc-real; passocInv-real )
open import poc.OCP0009.NbEPMonAdq3
  using ( padʳ-real; padˡ-real )

------------------------------------------------------------------------
-- The pentagon, solved for αr ⊗ 1.
------------------------------------------------------------------------

PENTAR : ∀ {A B D E} →
         (αrc {A} {B} {D} ⊗c idc {E}) ≈c
         (αlc {A} {B ⊗ D} {E} ∘c
          ((idc {A} ⊗c αlc {B} {D} {E}) ∘c
           (αrc {A} {B} {D ⊗ E} ∘c αrc {A ⊗ B} {D} {E})))
PENTAR =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym cα-iso₂))
  (≈ctrans c∘-assoc
           (∘c-congʳ inner)))
  where
  inner : ∀ {A B D E} →
          (αrc {A} {B ⊗ D} {E} ∘c (αrc {A} {B} {D} ⊗c idc {E})) ≈c
          ((idc {A} ⊗c αlc {B} {D} {E}) ∘c
           (αrc {A} {B} {D ⊗ E} ∘c αrc {A ⊗ B} {D} {E}))
  inner =
    ≈ctrans (≈csym cid-l)
    (≈ctrans (∘c-congˡ (≈csym ⊗α-cancelˡC))
    (≈ctrans c∘-assoc
             (∘c-congʳ cpentagon)))

------------------------------------------------------------------------
-- The head collapses.
------------------------------------------------------------------------

-- Two heads: the spl-case dressing reduces to αr ⊗ 1.
mult-head² : ∀ X Y Θ₂ Γ₂ →
  (mult (X ∷ (Y ∷ Θ₂)) Γ₂ ∘c
   (αrc {X} {Y} {⟪ Θ₂ ++ Γ₂ ⟫} ∘c
    ((idc {X ⊗ Y} ⊗c multInv Θ₂ Γ₂) ∘c αrc {X ⊗ Y} {⟪ Θ₂ ⟫} {⟪ Γ₂ ⟫})))
  ≈c (αrc {X} {Y} {⟪ Θ₂ ⟫} ⊗c idc {⟪ Γ₂ ⟫})
mult-head² X Y Θ₂ Γ₂ =
  ≈ctrans (∘c-congˡ (∘c-congʳ (≈csym fuse⊗ˡC)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ
            (≈ctrans (≈csym cα-nat)
                     (∘c-congʳ (⊗c-cong c⊗-id ≈crefl))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            (≈ctrans fuse⊗ˡC
            (≈ctrans (⊗c-cong ≈crefl (mult-inv-r Θ₂ Γ₂)) c⊗-id))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ cid-l)))
           (≈csym PENTAR)))))))))

-- Unit head: the usI-case dressing reduces to ƛr ⊗ 1 — K2C exactly.
mult-headI : ∀ Θ₂ Γ₂ →
  (mult Θ₂ Γ₂ ∘c
   (ƛrc {⟪ Θ₂ ++ Γ₂ ⟫} ∘c
    ((idc {I} ⊗c multInv Θ₂ Γ₂) ∘c αrc {I} {⟪ Θ₂ ⟫} {⟪ Γ₂ ⟫})))
  ≈c (ƛrc {⟪ Θ₂ ⟫} ⊗c idc {⟪ Γ₂ ⟫})
mult-headI Θ₂ Γ₂ =
  ≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ cƛ-nat))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (mult-inv-r Θ₂ Γ₂))
  (≈ctrans cid-l (≈csym K2C))))))

------------------------------------------------------------------------
-- Sliding a neutral out of a reassociation.
------------------------------------------------------------------------

-- Abstract target `Z` (the `X ⊗ Y` case is the spl-node use; `Z` general
-- covers the usI-node's non-⊗ neutral as well).
n-α : ∀ {S Z T E} {n : CTm S Z} →
      ((n ⊗c idc {T ⊗ E}) ∘c αrc {S} {T} {E}) ≈c
      (αrc {Z} {T} {E} ∘c ((n ⊗c idc {T}) ⊗c idc {E}))
n-α = ≈csym (≈ctrans cα-nat (∘c-congˡ (⊗c-cong ≈crefl c⊗-id)))

------------------------------------------------------------------------
-- The node permutation, realized.
------------------------------------------------------------------------

node-perm-real :
  ∀ {Γ Γ₁} Θ₁ Θ₂ Γ₂ (q : Perm Γ₁ (Θ₁ ++ Θ₂)) (ρ : Perm Γ (Γ₁ ++ Γ₂)) →
  (mult Θ₁ (Θ₂ ++ Γ₂) ∘c
   permC ((ρ ⊙P padʳ Γ₂ q) ⊙P passoc Θ₁ Θ₂ Γ₂)) ≈c
  ((idc {⟪ Θ₁ ⟫} ⊗c multInv Θ₂ Γ₂) ∘c
   (αrc ∘c
    (((mult Θ₁ Θ₂ ∘c permC q) ⊗c idc {⟪ Γ₂ ⟫}) ∘c
     (mult Γ₁ Γ₂ ∘c permC ρ))))
node-perm-real Θ₁ Θ₂ Γ₂ q ρ =
  ≈ctrans (∘c-congʳ (⊙P-realC (ρ ⊙P padʳ Γ₂ q) (passoc Θ₁ Θ₂ Γ₂)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (⊙P-realC ρ (padʳ Γ₂ q))))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (passoc-real Θ₁ Θ₂ Γ₂))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ (padʳ-real Γ₂ q)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
           (∘c-congʳ (∘c-congʳ (∘c-congˡ fuse⊗ʳC)))))))))))))

------------------------------------------------------------------------
-- The node permutation, realized — LEFT (αl) mirror of node-perm-real,
-- for the withSpʳ / αlc side (passocInv-real + padˡ-real + ⊙P-realC).
------------------------------------------------------------------------

node-perm-realˡ :
  ∀ {Γ Γ₂} Δ₁ Θ₁ Θ₂ (q : Perm Γ₂ (Θ₁ ++ Θ₂)) (ρ : Perm Γ (Δ₁ ++ Γ₂)) →
  (mult (Δ₁ ++ Θ₁) Θ₂ ∘c permC ((ρ ⊙P padˡ Δ₁ q) ⊙P passocInv Δ₁ Θ₁ Θ₂)) ≈c
  ((multInv Δ₁ Θ₁ ⊗c idc {⟪ Θ₂ ⟫}) ∘c
   (αlc ∘c ((idc {⟪ Δ₁ ⟫} ⊗c (mult Θ₁ Θ₂ ∘c permC q)) ∘c
            (mult Δ₁ Γ₂ ∘c permC ρ))))
node-perm-realˡ Δ₁ Θ₁ Θ₂ q ρ =
  ≈ctrans (∘c-congʳ (⊙P-realC (ρ ⊙P padˡ Δ₁ q) (passocInv Δ₁ Θ₁ Θ₂)))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (passocInv-real Δ₁ Θ₁ Θ₂))
  (≈ctrans (∘c-congʳ (⊙P-realC ρ (padˡ Δ₁ q)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ
             (≈ctrans (≈csym c∘-assoc)
             (≈ctrans (∘c-congˡ (padˡ-real Δ₁ q)) c∘-assoc)))))
           (∘c-congʳ (∘c-congʳ
             (≈ctrans (≈csym c∘-assoc)
                      (∘c-congˡ (≈ctrans (≈csym c⊗-∘)
                                         (⊗c-cong cid-l ≈crefl)))))))))))))

------------------------------------------------------------------------
-- The head collapse, factored out — the chain the appSp `dagger` and the
-- withSpˡ `nodeL` both run AFTER the node-permutation is realized.
-- Generic in the inner mult (`P`) and the outer mult (`M`).
------------------------------------------------------------------------

collapse² : ∀ {Wᴾ Wᴹ} X Y Θ₂ Γ₂ {Θ₁} (n : CTm ⟪ Θ₁ ⟫ (X ⊗ Y))
            (P : CTm Wᴾ (⟪ Θ₁ ⟫ ⊗ ⟪ Θ₂ ⟫)) (M : CTm Wᴹ (Wᴾ ⊗ ⟪ Γ₂ ⟫)) →
  (mult (X ∷ (Y ∷ Θ₂)) Γ₂ ∘c
   (αrc ∘c ((n ⊗c idc) ∘c
     ((idc ⊗c multInv Θ₂ Γ₂) ∘c
      (αrc ∘c ((P ⊗c idc) ∘c M)))))) ≈c
  (((αrc ∘c ((n ⊗c idc) ∘c P)) ⊗c idc) ∘c M)
collapse² X Y Θ₂ Γ₂ n P M =
  ≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-α))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (mult-head² X Y Θ₂ Γ₂))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ʳC))
  (≈ctrans (≈csym c∘-assoc)
           (∘c-congˡ fuse⊗ʳC)))))))))))))

collapseI : ∀ {Wᴾ Wᴹ} Θ₂ Γ₂ {Θ₁} (n : CTm ⟪ Θ₁ ⟫ I)
            (P : CTm Wᴾ (⟪ Θ₁ ⟫ ⊗ ⟪ Θ₂ ⟫)) (M : CTm Wᴹ (Wᴾ ⊗ ⟪ Γ₂ ⟫)) →
  (mult Θ₂ Γ₂ ∘c
   (ƛrc ∘c ((n ⊗c idc) ∘c
     ((idc ⊗c multInv Θ₂ Γ₂) ∘c
      (αrc ∘c ((P ⊗c idc) ∘c M)))))) ≈c
  (((ƛrc ∘c ((n ⊗c idc) ∘c P)) ⊗c idc) ∘c M)
collapseI Θ₂ Γ₂ n P M =
  ≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
             (≈csym (≈ctrans cα-nat
                      (∘c-congˡ (⊗c-cong ≈crefl c⊗-id))))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (mult-headI Θ₂ Γ₂))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ʳC))
  (≈ctrans (≈csym c∘-assoc)
           (∘c-congˡ fuse⊗ʳC)))))))))))))
