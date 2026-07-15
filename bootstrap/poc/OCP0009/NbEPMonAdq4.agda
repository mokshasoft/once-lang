------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A2b.2a — THE KELLY CLUSTER, PORTED
--
-- `mult-insEnd` (carrying a resource past a whole block — the next
-- stage's key lemma) consumes the classical unit-coherence cluster and
-- swapHead multiplicativity. This module ports them to the closed
-- theory — verbatim recipes from `NbEPMonG` (K2), `NbEPMonK`
-- (K3′/K3/K4), and `NbEPMonS` (K5′, ŝ-αr):
--
--   * `K2C`  : ƛ_A ⊗ 1_B ≈ ƛ_{A⊗B} ∘ α       (Kelly/Mac Lane VII.2)
--   * `K3′C` : ƛ ∘ σ ≈ ρ   and   `K3C` : ρ ∘ σ ≈ ƛ   (Joyal–Street)
--   * `K4C`  : ƛ ∘ ŝ_{x,I} ≈ 1_x ⊗ ƛ          (the deep unitor)
--   * `K5′C` : swapHead MULTIPLICATIVITY — carrying past a tensor
--     block is carrying past its parts, α-conjugated
--   * `ŝ-αrC`: the head transposition against the reassociator
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq4 where

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
  using ( α-natˡC; ⊗α-cancelʳC )

------------------------------------------------------------------------
-- Conjugation by ƛ, and K2 (NbEPMonG's recipe).
------------------------------------------------------------------------

conj-ƛC : ∀ {A B} (f : CTm A B) →
          f ≈c ((ƛrc ∘c (idc {I} ⊗c f)) ∘c ƛlc)
conj-ƛC f =
  ≈ctrans (≈csym cid-r)
  (≈ctrans (∘c-congʳ (≈csym cƛ-iso₁))
  (≈ctrans (≈csym c∘-assoc)
           (∘c-congˡ (≈csym cƛ-nat))))

cancel-1IC : ∀ {A B} {f g : CTm A B} →
             (idc {I} ⊗c f) ≈c (idc ⊗c g) → f ≈c g
cancel-1IC {f = f} {g} p =
  ≈ctrans (conj-ƛC f)
  (≈ctrans (∘c-congˡ (∘c-congʳ p))
           (≈csym (conj-ƛC g)))

K2C : ∀ {A B} → (ƛrc {A} ⊗c idc {B}) ≈c (ƛrc {A ⊗ B} ∘c αrc {I} {A} {B})
K2C {A} {B} = cancel-1IC (≈ctrans lhs-red (≈csym rhs-red))
  where
  tri-solve : ∀ {X} → (idc {I} ⊗c ƛrc {X}) ≈c ((ρrc ⊗c idc) ∘c αlc)
  tri-solve =
    ≈ctrans (≈csym cid-r)
    (≈ctrans (∘c-congʳ (≈csym cα-iso₁))
    (≈ctrans (≈csym c∘-assoc)
             (∘c-congˡ ctriangle)))

  lhs-red : (idc {I} ⊗c (ƛrc {A} ⊗c idc {B})) ≈c
            (αrc ∘c ((((ρrc {I} ⊗c idc {A}) ⊗c idc {B}) ∘c (αlc ⊗c idc))
                     ∘c αlc))
  lhs-red =
    ≈ctrans (≈csym cid-r)
    (≈ctrans (∘c-congʳ (≈csym cα-iso₁))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (≈csym cα-nat))
    (≈ctrans c∘-assoc
             (∘c-congʳ (∘c-congˡ (≈ctrans (⊗c-cong tri-solve ≈crefl)
                                          (≈csym fuse⊗ʳC))))))))

  cancel-r : ((αrc {I} {I ⊗ A} {B} ∘c (αrc {I} {I} {A} ⊗c idc {B})) ∘c
              ((αlc ⊗c idc) ∘c αlc)) ≈c idc
  cancel-r =
    ≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congˡ ⊗α-cancelʳC))
    (≈ctrans (∘c-congʳ cid-l)
             cα-iso₁)))

  pent-solve : (idc {I} ⊗c αrc {I} {A} {B}) ≈c
               ((αrc ∘c αrc) ∘c ((αlc {I} {I} {A} ⊗c idc {B}) ∘c αlc))
  pent-solve =
    ≈ctrans (≈csym cid-r)
    (≈ctrans (∘c-congʳ (≈csym cancel-r))
    (≈ctrans (≈csym c∘-assoc)
             (∘c-congˡ cpentagon)))

  ρ-α-nat : ((ρrc {I} ⊗c idc {A ⊗ B}) ∘c αrc {I ⊗ I} {A} {B}) ≈c
            (αrc {I} {A} {B} ∘c ((ρrc ⊗c idc) ⊗c idc))
  ρ-α-nat = ≈csym (≈ctrans cα-nat (∘c-congˡ (⊗c-cong ≈crefl c⊗-id)))

  rhs-red : (idc {I} ⊗c (ƛrc {A ⊗ B} ∘c αrc {I} {A} {B})) ≈c
            (αrc ∘c ((((ρrc {I} ⊗c idc {A}) ⊗c idc {B}) ∘c (αlc ⊗c idc))
                     ∘c αlc))
  rhs-red =
    ≈ctrans (≈csym fuse⊗ˡC)
    (≈ctrans (∘c-congˡ tri-solve)
    (≈ctrans (∘c-congʳ pent-solve)
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym c∘-assoc)))
    (≈ctrans (∘c-congʳ (∘c-congˡ (∘c-congˡ cα-iso₂)))
    (≈ctrans (∘c-congʳ (∘c-congˡ cid-l))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ ρ-α-nat)
    (≈ctrans c∘-assoc
             (∘c-congʳ (≈csym c∘-assoc))))))))))))

------------------------------------------------------------------------
-- The unit-σ cluster (NbEPMonK's recipes).
------------------------------------------------------------------------

cancel-σˡC : ∀ {A B D} {f g : CTm D (A ⊗ B)} →
             (σc {A} {B} ∘c f) ≈c (σc ∘c g) → f ≈c g
cancel-σˡC p =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym cσ-invol))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ p)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ cσ-invol) cid-l)))))

conj-ρC : ∀ {A B} (f : CTm A B) →
          f ≈c ((ρrc ∘c (f ⊗c idc {I})) ∘c ρlc)
conj-ρC f =
  ≈ctrans (≈csym cid-r)
  (≈ctrans (∘c-congʳ (≈csym cρ-iso₁))
  (≈ctrans (≈csym c∘-assoc)
           (∘c-congˡ (≈csym cρ-nat))))

cancel-I1C : ∀ {A B} {f g : CTm A B} →
             (f ⊗c idc {I}) ≈c (g ⊗c idc) → f ≈c g
cancel-I1C {f = f} {g} p =
  ≈ctrans (conj-ρC f)
  (≈ctrans (∘c-congˡ (∘c-congʳ p))
           (≈csym (conj-ρC g)))

tri-solvegC : ∀ {A B} → (idc {A} ⊗c ƛrc {B}) ≈c ((ρrc ⊗c idc) ∘c αlc)
tri-solvegC =
  ≈ctrans (≈csym cid-r)
  (≈ctrans (∘c-congʳ (≈csym cα-iso₁))
  (≈ctrans (≈csym c∘-assoc)
           (∘c-congˡ ctriangle)))

λσ⊗C : ∀ {B C} →
       ((ƛrc {B} ∘c σc {B} {I}) ⊗c idc {C}) ≈c (ρrc {B} ⊗c idc {C})
λσ⊗C {B} {C} =
  cancel-σˡC (≈ctrans (≈csym chainX) (≈ctrans (∘c-congʳ chexagon) chainY))
  where
  chainX : (ƛrc {C ⊗ B} ∘c
            ((idc {I} ⊗c σc {B} {C}) ∘c (αrc ∘c (σc {B} {I} ⊗c idc {C}))))
           ≈c (σc {B} {C} ∘c ((ƛrc {B} ∘c σc {B} {I}) ⊗c idc {C}))
  chainX =
    ≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ cƛ-nat)
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym K2C)))
             (∘c-congʳ fuse⊗ʳC)))))
  chainY : (ƛrc {C ⊗ B} ∘c (αrc ∘c (σc {B} {I ⊗ C} ∘c αrc)))
           ≈c (σc {B} {C} ∘c (ρrc {B} ⊗c idc {C}))
  chainY =
    ≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (≈csym K2C))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (≈csym cσ-nat))
    (≈ctrans c∘-assoc
             (∘c-congʳ ctriangle)))))

K3′C : ∀ {B} → (ƛrc {B} ∘c σc {B} {I}) ≈c ρrc {B}
K3′C = cancel-I1C λσ⊗C

K3C : ∀ {B} → (ρrc {B} ∘c σc {I} {B}) ≈c ƛrc {B}
K3C =
  ≈ctrans (∘c-congˡ (≈csym K3′C))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ cσ-invol) cid-r))

K4C : ∀ {x S} →
      (ƛrc {x ⊗ S} ∘c swapHeadC {x} {I} {S}) ≈c (idc {x} ⊗c ƛrc {S})
K4C =
  ≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym K2C))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ fuse⊗ʳC)
  (≈ctrans (∘c-congˡ (⊗c-cong K3′C ≈crefl))
           (≈csym tri-solvegC)))))

------------------------------------------------------------------------
-- swapHead multiplicativity and the α-collapse (NbEPMonS's recipes).
------------------------------------------------------------------------

K5′C : ∀ {x B₁ B₂ S} →
       (αrc {B₁} {B₂} {x ⊗ S} ∘c swapHeadC {x} {B₁ ⊗ B₂} {S}) ≈c
       ((idc {B₁} ⊗c swapHeadC {x} {B₂} {S}) ∘c
        (swapHeadC {x} {B₁} {B₂ ⊗ S} ∘c (idc {x} ⊗c αrc)))
K5′C = ≈ctrans Lred (≈csym Rred)
  where
  open import poc.OCP0009.NbEPMonAdq2 using ( F2C; GC )

  Lred : ∀ {x B₁ B₂ S} →
         (αrc {B₁} {B₂} {x ⊗ S} ∘c swapHeadC {x} {B₁ ⊗ B₂} {S}) ≈c
         ((αrc ∘c ((idc {B₁ ⊗ B₂} ⊗c σc {S} {x}) ∘c αrc)) ∘c
          σc {x} {(B₁ ⊗ B₂) ⊗ S})
  Lred =
    ≈ctrans (∘c-congʳ F2C)
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
             (≈csym c∘-assoc))
  Rred : ∀ {x B₁ B₂ S} →
         ((idc {B₁} ⊗c swapHeadC {x} {B₂} {S}) ∘c
          (swapHeadC {x} {B₁} {B₂ ⊗ S} ∘c (idc {x} ⊗c αrc))) ≈c
         ((αrc ∘c ((idc {B₁ ⊗ B₂} ⊗c σc {S} {x}) ∘c αrc)) ∘c
          σc {x} {(B₁ ⊗ B₂) ⊗ S})
  Rred =
    ≈ctrans (∘c-congʳ (∘c-congˡ F2C))
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ cσ-nat)))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ fuse⊗ˡC)
    (≈ctrans (∘c-congˡ (⊗c-cong ≈crefl GC))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (≈csym c∘-assoc)
             (∘c-congˡ inner)))))))))
    where
    inner : ∀ {x B₁ B₂ S} →
            ((idc {B₁} ⊗c ((idc {B₂} ⊗c σc {S} {x}) ∘c αrc)) ∘c
             (αrc ∘c (αrc {B₁} {B₂} {S} ⊗c idc {x}))) ≈c
            (αrc ∘c ((idc {B₁ ⊗ B₂} ⊗c σc {S} {x}) ∘c αrc))
    inner =
      ≈ctrans (∘c-congˡ (≈csym fuse⊗ˡC))
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ cpentagon)
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ (≈ctrans (≈csym cα-nat)
                          (∘c-congʳ (⊗c-cong c⊗-id ≈crefl))))
               c∘-assoc))))

ŝ-αrC : ∀ {a B R} →
        (swapHeadC {a} {B} {R} ∘c αrc {a} {B} {R}) ≈c
        (αrc ∘c (σc {a} {B} ⊗c idc {R}))
ŝ-αrC =
  ≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ cα-iso₂))
           (∘c-congʳ cid-r)))
