------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A2 — THE REALIZATION HOMOMORPHISM
--
-- The fundamental lemma (A4) needs the world category's realization to
-- be a HOMOMORPHISM into the closed theory:
--
--   ⊙P-realC : permC (p ⊙P q) ≈c (permC q ∘c permC p)
--
-- This is the stage-3C tower re-run over CTy worlds — every proof a
-- VERBATIM PORT of the corresponding `≈m` recipe (`NbEPMonR/Y/I/Q`),
-- the recipes never depended on what the list elements were:
--
--   * `inv-natC`/`α-natˡC`, `swapHeadC-nat`, `swapHeadC-invol` — the
--     commutation half of the symmetric-group presentation (3C.1);
--   * `F2C`/`GC` (hexagon, spent), pentagon corollaries, the
--     M-reductions, and **`YBC` — Yang–Baxter** (3C.2);
--   * `ins-swap-realC` — the insertion diamond realized (3C.3a);
--   * `pid-realC`, `push-realC`, `⊙P-realC` — identity, factorization
--     and composition realized (3C.3b).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq2 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; _⊗_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; σc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cα-nat; cσ-nat
        ; cα-iso₁; cα-iso₂; cσ-invol; cpentagon; chexagon )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; Ins; here; there; Perm; pnil; pcons; pid
        ; ins-swap; push; _⊙P_ )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; swapHeadC; insC; permC )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; cancelC; fuse⊗ˡC; fuse⊗ʳC )

------------------------------------------------------------------------
-- 3C.1 ports: inverse naturality, swapHead commutation and involution.
------------------------------------------------------------------------

inv-natC : ∀ {L L' R R' : CTy}
           {u : CTm L' R'} {v : CTm R' L'} {u' : CTm L R} {v' : CTm R L}
           {Y : CTm L L'} {X : CTm R R'} →
           (v ∘c u) ≈c idc → (u' ∘c v') ≈c idc →
           (u ∘c Y) ≈c (X ∘c u') →
           (Y ∘c v') ≈c (v ∘c X)
inv-natC p q nat =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym p))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ nat))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ q))
           (∘c-congʳ cid-r)))))))

α-natˡC : ∀ {A B D A' B' D'}
            {f : CTm A A'} {g : CTm B B'} {h : CTm D D'} →
          (((f ⊗c g) ⊗c h) ∘c αlc) ≈c (αlc ∘c (f ⊗c (g ⊗c h)))
α-natˡC = inv-natC cα-iso₂ cα-iso₁ cα-nat

swapHeadC-nat : ∀ {x y W x' y' W'}
                  {f : CTm x x'} {g : CTm y y'} {h : CTm W W'} →
                (swapHeadC ∘c (f ⊗c (g ⊗c h))) ≈c
                ((g ⊗c (f ⊗c h)) ∘c swapHeadC)
swapHeadC-nat {f = f} {g} {h} =
  ≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym α-natˡC)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ step-σ))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ cα-nat)
           c∘-assoc)))))))
  where
  step-σ : ∀ {x y W x' y' W'}
             {f : CTm x x'} {g : CTm y y'} {h : CTm W W'} →
           ((σc ⊗c idc) ∘c ((f ⊗c g) ⊗c h)) ≈c
           (((g ⊗c f) ⊗c h) ∘c (σc ⊗c idc))
  step-σ =
    ≈ctrans (≈csym c⊗-∘)
    (≈ctrans (⊗c-cong cσ-nat (≈ctrans cid-l (≈csym cid-r)))
             c⊗-∘)

swapHeadC-invol : ∀ {x y W} →
                  (swapHeadC {y} {x} {W} ∘c swapHeadC {x} {y} {W}) ≈c idc
swapHeadC-invol =
  ≈ctrans (∘c-congˡ (≈csym c∘-assoc))
  (≈ctrans (cancelC cα-iso₂)
  (≈ctrans (cancelC σ⊗-cancel)
           cα-iso₁))
  where
  σ⊗-cancel : ∀ {x y W} →
              ((σc {y} {x} ⊗c idc {W}) ∘c (σc {x} {y} ⊗c idc)) ≈c idc
  σ⊗-cancel = ≈ctrans (≈csym c⊗-∘) (≈ctrans (⊗c-cong cσ-invol cid-l) c⊗-id)

------------------------------------------------------------------------
-- 3C.2 ports: hexagon spent (F2/G), pentagon corollaries, M-reductions,
-- YANG–BAXTER.
------------------------------------------------------------------------

interchangeC : ∀ {A A' B B'} {f : CTm A A'} {g : CTm B B'} →
               ((f ⊗c idc) ∘c (idc ⊗c g)) ≈c ((idc ⊗c g) ∘c (f ⊗c idc))
interchangeC =
  ≈ctrans (≈csym c⊗-∘)
  (≈ctrans (⊗c-cong (≈ctrans cid-r (≈csym cid-l))
                    (≈ctrans cid-l (≈csym cid-r)))
           c⊗-∘)

⊗σ-involC : ∀ {E A B} →
            ((idc {E} ⊗c σc {B} {A}) ∘c (idc ⊗c σc {A} {B})) ≈c idc
⊗σ-involC = ≈ctrans fuse⊗ˡC (≈ctrans (⊗c-cong ≈crefl cσ-invol) c⊗-id)

F2C : ∀ {a b W} →
      swapHeadC {a} {b} {W} ≈c
      ((idc {b} ⊗c σc {W} {a}) ∘c (αrc ∘c σc {a} {b ⊗ W}))
F2C =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym ⊗σ-involC))
  (≈ctrans c∘-assoc
           (∘c-congʳ inner)))
  where
  inner : ∀ {a b W} →
          ((idc {b} ⊗c σc {a} {W}) ∘c swapHeadC {a} {b} {W}) ≈c
          (αrc ∘c σc {a} {b ⊗ W})
  inner =
    ≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ chexagon)
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ cα-iso₁))
             (∘c-congʳ cid-r))))))

GC : ∀ {x y w} →
     (swapHeadC {y} {x} {w} ∘c σc {x ⊗ w} {y}) ≈c
     ((idc {x} ⊗c σc {w} {y}) ∘c αrc)
GC =
  ≈ctrans (∘c-congˡ F2C)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ cσ-invol))
           (∘c-congʳ cid-r))))

⊗α-cancelˡC : ∀ {E A B D} →
              ((idc {E} ⊗c αlc {A} {B} {D}) ∘c (idc ⊗c αrc)) ≈c idc
⊗α-cancelˡC = ≈ctrans fuse⊗ˡC (≈ctrans (⊗c-cong ≈crefl cα-iso₂) c⊗-id)

⊗α-cancelʳC : ∀ {A B D E} →
              ((αrc {A} {B} {D} ⊗c idc {E}) ∘c (αlc ⊗c idc)) ≈c idc
⊗α-cancelʳC = ≈ctrans fuse⊗ʳC (≈ctrans (⊗c-cong cα-iso₁ ≈crefl) c⊗-id)

⊗α-cancelˡ′C : ∀ {E A B D} →
               ((idc {E} ⊗c αrc {A} {B} {D}) ∘c (idc ⊗c αlc)) ≈c idc
⊗α-cancelˡ′C = ≈ctrans fuse⊗ˡC (≈ctrans (⊗c-cong ≈crefl cα-iso₁) c⊗-id)

PENTLC : ∀ {A B D E} →
         (αrc {A} {B ⊗ D} {E} ∘c (αrc {A} {B} {D} ⊗c idc {E})) ≈c
         ((idc {A} ⊗c αlc {B} {D} {E}) ∘c (αrc ∘c αrc))
PENTLC =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym ⊗α-cancelˡC))
  (≈ctrans c∘-assoc
           (∘c-congʳ cpentagon)))

P′C : ∀ {A B D E} →
      ((idc {A} ⊗c αrc {B} {D} {E}) ∘c αrc {A} {B ⊗ D} {E}) ≈c
      ((αrc {A} {B} {D ⊗ E} ∘c αrc {A ⊗ B} {D} {E}) ∘c
       (αlc {A} {B} {D} ⊗c idc {E}))
P′C =
  ≈ctrans (∘c-congʳ (≈csym cid-r))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym ⊗α-cancelʳC)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (≈csym c∘-assoc)
           (∘c-congˡ cpentagon))))

PENT2C : ∀ {A B D E} →
         (αlc {A} {B} {D ⊗ E} ∘c
          ((idc {A} ⊗c αrc {B} {D} {E}) ∘c αrc {A} {B ⊗ D} {E})) ≈c
         (αrc {A ⊗ B} {D} {E} ∘c (αlc {A} {B} {D} ⊗c idc {E}))
PENT2C =
  ≈ctrans (∘c-congʳ P′C)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym c∘-assoc))
  (≈ctrans (∘c-congˡ (∘c-congˡ cα-iso₂))
           (∘c-congˡ cid-l))))

LtoMC : ∀ {x z w y} →
  ((idc {z} ⊗c ((idc {x} ⊗c σc {w} {y}) ∘c αrc)) ∘c
   (αrc ∘c (swapHeadC {x} {z} {w} ⊗c idc {y})))
  ≈c
  (αrc ∘c ((idc {z ⊗ x} ⊗c σc {w} {y}) ∘c
           ((σc {x} {z} ⊗c idc {w ⊗ y}) ∘c (αrc ∘c (αlc ⊗c idc {y})))))
LtoMC =
  ≈ctrans (∘c-congˡ (≈csym fuse⊗ˡC))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ split₁)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ PENTLC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ ⊗α-cancelˡ′C))
  (≈ctrans (∘c-congʳ cid-l)
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ cα-nat)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (∘c-congˡ (⊗c-cong ≈crefl c⊗-id)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym cα-nat))
  (≈ctrans (∘c-congˡ (∘c-congʳ (⊗c-cong c⊗-id ≈crefl)))
           c∘-assoc))))))))))))))))
  where
  split₁ : ∀ {x z w y} →
           (swapHeadC {x} {z} {w} ⊗c idc {y}) ≈c
           ((αrc ⊗c idc) ∘c (((σc ⊗c idc) ⊗c idc) ∘c (αlc ⊗c idc)))
  split₁ = ≈ctrans (≈csym fuse⊗ʳC) (∘c-congʳ (≈csym fuse⊗ʳC))

RtoMC : ∀ {x z w y} →
  (swapHeadC {x} {z} {y ⊗ w} ∘c
   ((idc {x} ⊗c ((idc {z} ⊗c σc {w} {y}) ∘c αrc)) ∘c αrc))
  ≈c
  (αrc ∘c ((idc {z ⊗ x} ⊗c σc {w} {y}) ∘c
           ((σc {x} {z} ⊗c idc {w ⊗ y}) ∘c (αrc ∘c (αlc ⊗c idc {y})))))
RtoMC =
  ≈ctrans (∘c-congʳ (∘c-congˡ (≈csym fuse⊗ˡC)))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (≈csym α-natˡC))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (∘c-congˡ (⊗c-cong c⊗-id ≈crefl)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ PENT2C)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ interchangeC))
           (∘c-congʳ c∘-assoc)))))))))))

GOAL2C : ∀ {x z w y} →
  ((idc {z} ⊗c ((idc {x} ⊗c σc {w} {y}) ∘c αrc)) ∘c
   (αrc ∘c (swapHeadC {x} {z} {w} ⊗c idc {y})))
  ≈c
  (swapHeadC {x} {z} {y ⊗ w} ∘c
   ((idc {x} ⊗c ((idc {z} ⊗c σc {w} {y}) ∘c αrc)) ∘c αrc))
GOAL2C = ≈ctrans LtoMC (≈csym RtoMC)

YBC : ∀ {x y z w} →
  ((idc {z} ⊗c swapHeadC {y} {x} {w}) ∘c
   (swapHeadC {y} {z} {x ⊗ w} ∘c (idc {y} ⊗c swapHeadC {x} {z} {w})))
  ≈c
  (swapHeadC {x} {z} {y ⊗ w} ∘c
   ((idc {x} ⊗c swapHeadC {y} {z} {w}) ∘c swapHeadC {y} {x} {z ⊗ w}))
YBC =
  ≈ctrans Achain (≈ctrans (∘c-congˡ GOAL2C) (≈csym Bchain))
  where
  Achain : ∀ {x y z w} →
    ((idc {z} ⊗c swapHeadC {y} {x} {w}) ∘c
     (swapHeadC {y} {z} {x ⊗ w} ∘c (idc {y} ⊗c swapHeadC {x} {z} {w})))
    ≈c
    (((idc {z} ⊗c ((idc {x} ⊗c σc {w} {y}) ∘c αrc)) ∘c
      (αrc ∘c (swapHeadC {x} {z} {w} ⊗c idc {y}))) ∘c
     σc {y} {x ⊗ (z ⊗ w)})
  Achain =
    ≈ctrans (∘c-congʳ (∘c-congˡ F2C))
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ cσ-nat)))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ fuse⊗ˡC)
    (≈ctrans (∘c-congˡ (⊗c-cong ≈crefl GC))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
             (≈csym c∘-assoc))))))))
  Bchain : ∀ {x y z w} →
    (swapHeadC {x} {z} {y ⊗ w} ∘c
     ((idc {x} ⊗c swapHeadC {y} {z} {w}) ∘c swapHeadC {y} {x} {z ⊗ w}))
    ≈c
    ((swapHeadC {x} {z} {y ⊗ w} ∘c
      ((idc {x} ⊗c ((idc {z} ⊗c σc {w} {y}) ∘c αrc)) ∘c αrc)) ∘c
     σc {y} {x ⊗ (z ⊗ w)})
  Bchain =
    ≈ctrans (∘c-congʳ (∘c-congʳ F2C))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ˡC))
    (≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong ≈crefl GC)))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
             (≈csym c∘-assoc)))))

------------------------------------------------------------------------
-- 3C.3 ports: the diamond realized, then factorization and composition.
------------------------------------------------------------------------

ins-swap-realC :
  ∀ {x y w₂ w₁ w w₃} (i : Ins x w₂ w₁) (j : Ins y w₁ w)
    {jy : Ins y w₂ w₃} {jx : Ins x w₃ w} →
  ins-swap i j ≡ (w₃ , (jy , jx)) →
  (insC j ∘c (idc ⊗c insC i)) ≈c
  ((insC jx ∘c (idc ⊗c insC jy)) ∘c swapHeadC)

ins-swap-realC here here refl =
  ≈ctrans (≈ctrans cid-l c⊗-id) (≈csym rhs)
  where
  rhs : ∀ {x y w₂} →
        ((((idc {y} ⊗c idc {x ⊗ ⟪ w₂ ⟫}) ∘c swapHeadC) ∘c (idc ⊗c idc))
         ∘c swapHeadC)
        ≈c idc
  rhs = ≈ctrans (∘c-congˡ (∘c-congˡ (∘c-congˡ c⊗-id)))
        (≈ctrans (∘c-congˡ (∘c-congˡ cid-l))
        (≈ctrans (∘c-congˡ (∘c-congʳ c⊗-id))
        (≈ctrans (∘c-congˡ cid-r)
                 swapHeadC-invol)))

ins-swap-realC here (there j₀) refl =
  ≈ctrans (∘c-congʳ c⊗-id) (≈ctrans cid-r (∘c-congˡ (≈csym cid-l)))

ins-swap-realC (there i₀) here refl =
  ≈ctrans cid-l (≈csym rhs3)
  where
  rhs3 : ∀ {x y z w₂' w₁'} {k : Ins x w₂' w₁'} →
         ((((idc {y} ⊗c insC (there {y = z} k)) ∘c swapHeadC) ∘c
           (idc {x} ⊗c idc)) ∘c swapHeadC)
         ≈c (idc {y} ⊗c insC (there k))
  rhs3 = ≈ctrans (∘c-congˡ (∘c-congʳ c⊗-id))
         (≈ctrans (∘c-congˡ cid-r)
         (≈ctrans c∘-assoc
         (≈ctrans (∘c-congʳ swapHeadC-invol) cid-r)))

ins-swap-realC (there i₀) (there j₀) refl =
  ≈ctrans lhs≈LT (≈ctrans (∘c-congʳ (∘c-congʳ YBC)) (≈csym rhs≈RT))
  where
  lhs≈LT = ≈ctrans (∘c-congʳ (≈csym fuse⊗ˡC))
           (≈ctrans c∘-assoc
           (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
           (≈ctrans (∘c-congʳ (∘c-congˡ swapHeadC-nat))
           (≈ctrans (∘c-congʳ c∘-assoc)
           (≈ctrans (≈csym c∘-assoc)
           (≈ctrans (∘c-congˡ fuse⊗ˡC)
           (≈ctrans (∘c-congˡ (⊗c-cong ≈crefl (ins-swap-realC i₀ j₀ refl)))
           (≈ctrans (∘c-congˡ (≈csym fuse⊗ˡC))
           (≈ctrans (∘c-congˡ (∘c-congˡ (≈csym fuse⊗ˡC)))
           (≈ctrans c∘-assoc
                    c∘-assoc))))))))))
  rhs≈RT = ≈ctrans (∘c-congˡ (∘c-congʳ (≈csym fuse⊗ˡC)))
           (≈ctrans (∘c-congˡ c∘-assoc)
           (≈ctrans (∘c-congˡ (∘c-congʳ (≈csym c∘-assoc)))
           (≈ctrans (∘c-congˡ (∘c-congʳ (∘c-congˡ swapHeadC-nat)))
           (≈ctrans (∘c-congˡ (∘c-congʳ c∘-assoc))
           (≈ctrans c∘-assoc
           (≈ctrans (∘c-congʳ c∘-assoc)
                    (∘c-congʳ (∘c-congʳ c∘-assoc))))))))

pid-realC : ∀ Γ → permC (pid Γ) ≈c idc
pid-realC ε       = ≈crefl
pid-realC (A ∷ Γ) =
  ≈ctrans cid-l (≈ctrans (⊗c-cong ≈crefl (pid-realC Γ)) c⊗-id)

push-realC :
  ∀ {x ys zs ws ws'} (i : Ins x ys zs) (q : Perm zs ws)
    {q' : Perm ys ws'} {j' : Ins x ws' ws} →
  push i q ≡ (ws' , (q' , j')) →
  (permC q ∘c insC i) ≈c (insC j' ∘c (idc ⊗c permC q'))

push-realC here (pcons q₀ j) refl = cid-r

push-realC (there i₀) (pcons q₀ j) refl =
  ≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ˡC))
  (≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong ≈crefl (push-realC i₀ q₀ refl))))
  (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym fuse⊗ˡC)))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (ins-swap-realC _ j refl))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ swapHeadC-nat))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ swapHeadC-invol))
  (≈ctrans (∘c-congʳ cid-r)
  (≈ctrans c∘-assoc
           (∘c-congʳ fuse⊗ˡC)))))))))))))))

⊙P-realC : ∀ {xs ys zs} (p : Perm xs ys) (q : Perm ys zs) →
           permC (p ⊙P q) ≈c (permC q ∘c permC p)
⊙P-realC pnil         q = ≈csym cid-r
⊙P-realC (pcons p₀ i) q =
  ≈ctrans (∘c-congʳ (⊗c-cong ≈crefl (⊙P-realC p₀ _)))
  (≈ctrans (∘c-congʳ (≈csym fuse⊗ˡC))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym (push-realC i q refl)))
           c∘-assoc)))
