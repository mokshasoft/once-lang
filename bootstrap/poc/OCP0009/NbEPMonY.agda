------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3C.2 (part 1) — HEXAGON, SPENT:
--            the block and rotation forms of `swapHead`
--
-- The Yang–Baxter relation for `swapHead` (the braid half of the
-- symmetric-group presentation; the commutation half is `swapHead-nat`,
-- stage 3C.1) decomposes so that the HEXAGON axiom is consumed exactly
-- here, in two reusable forms:
--
--   * `F2` (BLOCK form):     ŝ_{a,b|W} ≈ (1_b ⊗ σ_{W,a}) ∘ α ∘ σ_{a,b⊗W}
--     — the head transposition is a whole-block swap of `a` past `b⊗W`,
--     reassociated, with the tail fixed up. One hexagon.
--   * `G`  (ROTATION form):  ŝ_{y,x|w} ∘ σ_{x⊗w,y} ≈ (1_x ⊗ σ_{w,y}) ∘ α
--     — rotating `y` in from the back is a pure α-move plus a deep σ.
--     F2 + σ-involution.
--
-- With F2/G, both sides of Yang–Baxter reduce (σ-naturality peels a
-- common block-σ tail) to an equation built ONLY from α, slot-clean σ's,
-- and identities — a residue that pentagon + interchange discharge with
-- no further hexagon (part 2).
--
-- Also here: the ⊗-plumbing this and every later stage uses (`fuse⊗ˡ`,
-- `fuse⊗ʳ`, `interchange`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonY where

open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-nat; σ-nat
        ; α-iso₁; α-iso₂; σ-invol; pentagon; hexagon )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; cancel )
open import poc.OCP0009.NbEPMonP
  using ( swapHead )

------------------------------------------------------------------------
-- ⊗-plumbing.
------------------------------------------------------------------------

fuse⊗ˡ : ∀ {A B D E} {f : STm B D} {g : STm A B} →
         ((idm {E} ⊗m f) ∘m (idm ⊗m g)) ≈m (idm ⊗m (f ∘m g))
fuse⊗ˡ = ≈trans (≈sym ⊗-∘) (⊗-cong id-l ≈refl)

fuse⊗ʳ : ∀ {A B D E} {f : STm B D} {g : STm A B} →
         ((f ⊗m idm {E}) ∘m (g ⊗m idm)) ≈m ((f ∘m g) ⊗m idm)
fuse⊗ʳ = ≈trans (≈sym ⊗-∘) (⊗-cong ≈refl id-l)

interchange : ∀ {A A' B B'} {f : STm A A'} {g : STm B B'} →
              ((f ⊗m idm) ∘m (idm ⊗m g)) ≈m ((idm ⊗m g) ∘m (f ⊗m idm))
interchange =
  ≈trans (≈sym ⊗-∘)
  (≈trans (⊗-cong (≈trans id-r (≈sym id-l)) (≈trans id-l (≈sym id-r)))
          ⊗-∘)

-- (1 ⊗ σ) is an involution.
⊗σ-invol : ∀ {E A B} →
           ((idm {E} ⊗m σm {B} {A}) ∘m (idm ⊗m σm {A} {B})) ≈m idm
⊗σ-invol = ≈trans fuse⊗ˡ (≈trans (⊗-cong ≈refl σ-invol) ⊗-id)

------------------------------------------------------------------------
-- F2 — the BLOCK form of the head transposition (hexagon, spent).
------------------------------------------------------------------------

F2 : ∀ {a b W} →
     swapHead {a} {b} {W} ≈m
     ((idm {b} ⊗m σm {W} {a}) ∘m (αr ∘m σm {a} {b ⊗ W}))
F2 =
  ≈trans (≈sym id-l)
  (≈trans (∘-congˡ (≈sym ⊗σ-invol))
  (≈trans ∘-assoc
          (∘-congʳ inner)))
  where
  -- (1 ⊗ σ_{a,W}) ∘ swapHead  ≈  αr ∘ σ_{a,b⊗W}
  inner : ∀ {a b W} →
          ((idm {b} ⊗m σm {a} {W}) ∘m swapHead {a} {b} {W}) ≈m
          (αr ∘m σm {a} {b ⊗ W})
  inner =
    ≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ hexagon)
    (≈trans ∘-assoc
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (∘-congʳ (∘-congʳ α-iso₁))
            (∘-congʳ id-r))))))

------------------------------------------------------------------------
-- G — the ROTATION form: pulling the back element to the middle.
------------------------------------------------------------------------

G : ∀ {x y w} →
    (swapHead {y} {x} {w} ∘m σm {x ⊗ w} {y}) ≈m
    ((idm {x} ⊗m σm {w} {y}) ∘m αr)
G =
  ≈trans (∘-congˡ F2)
  (≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ σ-invol))
          (∘-congʳ id-r))))
