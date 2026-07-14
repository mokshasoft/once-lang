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
open import poc.OCP0009.NbEPMonR
  using ( α-natˡ; swapHead-nat; swapHead-invol )

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

------------------------------------------------------------------------
-- Pentagon, spent: the two rearranged forms the M-reductions consume.
------------------------------------------------------------------------

⊗α-cancelˡ : ∀ {E A B D} →
             ((idm {E} ⊗m αl {A} {B} {D}) ∘m (idm ⊗m αr)) ≈m idm
⊗α-cancelˡ = ≈trans fuse⊗ˡ (≈trans (⊗-cong ≈refl α-iso₂) ⊗-id)

⊗α-cancelʳ : ∀ {A B D E} →
             ((αr {A} {B} {D} ⊗m idm {E}) ∘m (αl ⊗m idm)) ≈m idm
⊗α-cancelʳ = ≈trans fuse⊗ʳ (≈trans (⊗-cong α-iso₁ ≈refl) ⊗-id)

-- PENTL: the pentagon, solved for `αr ∘ (αr ⊗ 1)`.
PENTL : ∀ {A B D E} →
        (αr {A} {B ⊗ D} {E} ∘m (αr {A} {B} {D} ⊗m idm {E})) ≈m
        ((idm {A} ⊗m αl {B} {D} {E}) ∘m (αr ∘m αr))
PENTL =
  ≈trans (≈sym id-l)
  (≈trans (∘-congˡ (≈sym ⊗α-cancelˡ))
  (≈trans ∘-assoc
          (∘-congʳ pentagon)))

-- P′: the pentagon, solved for `(1 ⊗ αr) ∘ αr`.
P′ : ∀ {A B D E} →
     ((idm {A} ⊗m αr {B} {D} {E}) ∘m αr {A} {B ⊗ D} {E}) ≈m
     ((αr {A} {B} {D ⊗ E} ∘m αr {A ⊗ B} {D} {E}) ∘m (αl {A} {B} {D} ⊗m idm {E}))
P′ =
  ≈trans (∘-congʳ (≈sym id-r))
  (≈trans (∘-congʳ (∘-congʳ (≈sym ⊗α-cancelʳ)))
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (≈sym ∘-assoc)
          (∘-congˡ pentagon))))

-- PENT2: the α-route identity the RHS→M reduction lands on.
PENT2 : ∀ {A B D E} →
        (αl {A} {B} {D ⊗ E} ∘m ((idm {A} ⊗m αr {B} {D} {E}) ∘m αr {A} {B ⊗ D} {E})) ≈m
        (αr {A ⊗ B} {D} {E} ∘m (αl {A} {B} {D} ⊗m idm {E}))
PENT2 =
  ≈trans (∘-congʳ P′)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (≈sym ∘-assoc))
  (≈trans (∘-congˡ (∘-congˡ α-iso₂))
          (∘-congˡ id-l))))

⊗α-cancelˡ′ : ∀ {E A B D} →
              ((idm {E} ⊗m αr {A} {B} {D}) ∘m (idm ⊗m αl)) ≈m idm
⊗α-cancelˡ′ = ≈trans fuse⊗ˡ (≈trans (⊗-cong ≈refl α-iso₁) ⊗-id)

------------------------------------------------------------------------
-- The M-reductions: both Yang–Baxter residues normalize to the canonical
-- mid-form M = αr ∘ (1⊗σ) ∘ (σ⊗1) ∘ αr ∘ (αl⊗1) — deep σ last, block σ
-- first, pure-α bookkeeping around. Pentagon + interchange only.
------------------------------------------------------------------------

LtoM : ∀ {x z w y} →
  ((idm {z} ⊗m ((idm {x} ⊗m σm {w} {y}) ∘m αr)) ∘m
   (αr ∘m (swapHead {x} {z} {w} ⊗m idm {y})))
  ≈m
  (αr ∘m ((idm {z ⊗ x} ⊗m σm {w} {y}) ∘m
          ((σm {x} {z} ⊗m idm {w ⊗ y}) ∘m (αr ∘m (αl ⊗m idm {y})))))
LtoM =
  ≈trans (∘-congˡ (≈sym fuse⊗ˡ))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ (∘-congʳ (∘-congʳ split₁)))
  (≈trans (∘-congʳ (∘-congʳ (≈sym ∘-assoc)))
  (≈trans (∘-congʳ (∘-congʳ (∘-congˡ PENTL)))
  (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ ⊗α-cancelˡ′))
  (≈trans (∘-congʳ id-l)
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ (≈sym ∘-assoc)))
  (≈trans (∘-congʳ (∘-congʳ (∘-congˡ α-nat)))
  (≈trans (∘-congʳ (∘-congʳ (∘-congˡ (∘-congˡ (⊗-cong ≈refl ⊗-id)))))
  (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (≈sym α-nat))
  (≈trans (∘-congˡ (∘-congʳ (⊗-cong ⊗-id ≈refl)))
          ∘-assoc))))))))))))))))
  where
  split₁ : ∀ {x z w y} →
           (swapHead {x} {z} {w} ⊗m idm {y}) ≈m
           ((αr ⊗m idm) ∘m (((σm ⊗m idm) ⊗m idm) ∘m (αl ⊗m idm)))
  split₁ = ≈trans (≈sym fuse⊗ʳ) (∘-congʳ (≈sym fuse⊗ʳ))

RtoM : ∀ {x z w y} →
  (swapHead {x} {z} {y ⊗ w} ∘m
   ((idm {x} ⊗m ((idm {z} ⊗m σm {w} {y}) ∘m αr)) ∘m αr))
  ≈m
  (αr ∘m ((idm {z ⊗ x} ⊗m σm {w} {y}) ∘m
          ((σm {x} {z} ⊗m idm {w ⊗ y}) ∘m (αr ∘m (αl ⊗m idm {y})))))
RtoM =
  ≈trans (∘-congʳ (∘-congˡ (≈sym fuse⊗ˡ)))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ (≈sym ∘-assoc)))
  (≈trans (∘-congʳ (∘-congʳ (∘-congˡ (≈sym α-natˡ))))
  (≈trans (∘-congʳ (∘-congʳ (∘-congˡ (∘-congˡ (⊗-cong ⊗-id ≈refl)))))
  (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
  (≈trans (∘-congʳ (∘-congʳ (∘-congʳ PENT2)))
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ interchange))
          (∘-congʳ ∘-assoc)))))))))))

-- GOAL2 — the hexagon-free residue, closed.
GOAL2 : ∀ {x z w y} →
  ((idm {z} ⊗m ((idm {x} ⊗m σm {w} {y}) ∘m αr)) ∘m
   (αr ∘m (swapHead {x} {z} {w} ⊗m idm {y})))
  ≈m
  (swapHead {x} {z} {y ⊗ w} ∘m
   ((idm {x} ⊗m ((idm {z} ⊗m σm {w} {y}) ∘m αr)) ∘m αr))
GOAL2 = ≈trans LtoM (≈sym RtoM)

------------------------------------------------------------------------
-- YANG–BAXTER for `swapHead` — the braid relation, proven.
------------------------------------------------------------------------

YB : ∀ {x y z w} →
  ((idm {z} ⊗m swapHead {y} {x} {w}) ∘m
   (swapHead {y} {z} {x ⊗ w} ∘m (idm {y} ⊗m swapHead {x} {z} {w})))
  ≈m
  (swapHead {x} {z} {y ⊗ w} ∘m
   ((idm {x} ⊗m swapHead {y} {z} {w}) ∘m swapHead {y} {x} {z ⊗ w}))
YB =
  ≈trans Achain (≈trans (∘-congˡ GOAL2) (≈sym Bchain))
  where
  Achain : ∀ {x y z w} →
    ((idm {z} ⊗m swapHead {y} {x} {w}) ∘m
     (swapHead {y} {z} {x ⊗ w} ∘m (idm {y} ⊗m swapHead {x} {z} {w})))
    ≈m
    (((idm {z} ⊗m ((idm {x} ⊗m σm {w} {y}) ∘m αr)) ∘m
      (αr ∘m (swapHead {x} {z} {w} ⊗m idm {y}))) ∘m σm {y} {x ⊗ (z ⊗ w)})
  Achain =
    ≈trans (∘-congʳ (∘-congˡ F2))
    (≈trans (∘-congʳ ∘-assoc)
    (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
    (≈trans (∘-congʳ (∘-congʳ (∘-congʳ σ-nat)))
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ fuse⊗ˡ)
    (≈trans (∘-congˡ (⊗-cong ≈refl G))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
            (≈sym ∘-assoc))))))))
  Bchain : ∀ {x y z w} →
    (swapHead {x} {z} {y ⊗ w} ∘m
     ((idm {x} ⊗m swapHead {y} {z} {w}) ∘m swapHead {y} {x} {z ⊗ w}))
    ≈m
    ((swapHead {x} {z} {y ⊗ w} ∘m
      ((idm {x} ⊗m ((idm {z} ⊗m σm {w} {y}) ∘m αr)) ∘m αr)) ∘m σm {y} {x ⊗ (z ⊗ w)})
  Bchain =
    ≈trans (∘-congʳ (∘-congʳ F2))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ fuse⊗ˡ))
    (≈trans (∘-congʳ (∘-congˡ (⊗-cong ≈refl G)))
    (≈trans (∘-congʳ (≈sym ∘-assoc))
            (≈sym ∘-assoc)))))
