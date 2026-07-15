------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A2b (part 1) — THE PAD REALIZATIONS
--
-- A3's splice lemmas need the padding operations of the world category
-- realized against the Day mediators, in MULT-FORM (post-compose with
-- `mult`, no inverses):
--
--   mult-insʳ : mult ∘ insC (insʳ Θ i) ≈c (insC i ⊗ 1) ∘ αl ∘ (1 ⊗ mult)
--   padʳ-real : mult ∘ permC (padʳ Θ p) ≈c (permC p ⊗ 1) ∘ mult
--   padˡ-real : mult ∘ permC (padˡ Θ q) ≈c (1 ⊗ permC q) ∘ mult
--
-- New machinery, derived on paper first (per the ladder discipline):
--   * `inv-congC` — equal isos have equal inverses (H's port);
--   * `pentagonₗC` — the MIRROR pentagon (for `αl`), by `inv-congC`
--     on `cpentagon` with the two side-inverses cancelled;
--   * `α-shuffle` — the 5-α identity, proven by composing with `αl`
--     and cancelling (both sides collapse onto the mirror pentagon);
--   * `ŝ-tail` — the head transposition against a TENSORED tail:
--     ŝ at `W⊗T` is ŝ at `W` padded by `T`, conjugated by α — the
--     K5′-flavoured multiplicativity, here with a two-line σ-move
--     because list worlds have no accumulator noise.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq3 where

open import normalizer.Syntax.Types
  using ( _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; _⊗_; I
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; σc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cƛ-nat
        ; cα-iso₁; cα-iso₂; cƛ-iso₁; cƛ-iso₂; cpentagon )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; insʳ; padˡ; padʳ )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; swapHeadC; insC; permC; mult )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; cancelC; fuse⊗ˡC; fuse⊗ʳC
        ; mult-inv-l )
open import poc.OCP0009.NbEPMonAdq2
  using ( inv-natC; α-natˡC; swapHeadC-nat
        ; ⊗α-cancelʳC; ⊗α-cancelˡ′C; pid-realC )

------------------------------------------------------------------------
-- Equal isos have equal inverses (H's `inv-cong`, ported).
------------------------------------------------------------------------

inv-congC : ∀ {P Q} {x y : CTm P Q} {xi yi : CTm Q P} →
            (x ∘c xi) ≈c idc → (yi ∘c y) ≈c idc → x ≈c y → xi ≈c yi
inv-congC p q e =
  ≈ctrans (≈csym cid-l)
  (≈ctrans (∘c-congˡ (≈csym q))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym e)))
  (≈ctrans (∘c-congʳ p) cid-r))))

------------------------------------------------------------------------
-- The mirror pentagon.
------------------------------------------------------------------------

pentagonₗC : ∀ {A B D E} →
             ((αlc {A} {B} {D} ⊗c idc {E}) ∘c
              (αlc {A} {B ⊗ D} {E} ∘c (idc {A} ⊗c αlc {B} {D} {E})))
             ≈c (αlc {A ⊗ B} {D} {E} ∘c αlc {A} {B} {D ⊗ E})
pentagonₗC = inv-congC side-inv mirror-inv cpentagon
  where
  side-inv : ∀ {A B D E} →
             (((idc {A} ⊗c αrc {B} {D} {E}) ∘c (αrc ∘c (αrc ⊗c idc {E}))) ∘c
              ((αlc ⊗c idc) ∘c (αlc ∘c (idc ⊗c αlc)))) ≈c idc
  side-inv =
    ≈ctrans (∘c-congˡ (≈csym c∘-assoc))
    (≈ctrans (cancelC ⊗α-cancelʳC)
    (≈ctrans (cancelC cα-iso₁)
             ⊗α-cancelˡ′C))
  mirror-inv : ∀ {A B D E} →
               ((αlc {A ⊗ B} {D} {E} ∘c αlc {A} {B} {D ⊗ E}) ∘c
                (αrc ∘c αrc)) ≈c idc
  mirror-inv = ≈ctrans (cancelC cα-iso₂) cα-iso₂

------------------------------------------------------------------------
-- The 5-α identity (proved by right-composition with αl, cancelled).
------------------------------------------------------------------------

α-shuffle : ∀ {y x W T} →
            ((αlc {y} {x ⊗ W} {T} ∘c (idc {y} ⊗c αlc {x} {W} {T})) ∘c
             αrc {y} {x} {W ⊗ T})
            ≈c ((αrc {y} {x} {W} ⊗c idc {T}) ∘c αlc {y ⊗ x} {W} {T})
α-shuffle {y} {x} {W} {T} =
  ≈ctrans (≈csym cid-r)
  (≈ctrans (∘c-congʳ (≈csym cα-iso₂))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ both∘αl)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ cα-iso₂) cid-r)))))
  where
  -- (LHS ∘ αl) ≈ (RHS ∘ αl), both collapsing to αl∘(1⊗αl).
  both∘αl :
    (((αlc {y} {x ⊗ W} {T} ∘c (idc {y} ⊗c αlc {x} {W} {T})) ∘c
      αrc {y} {x} {W ⊗ T}) ∘c αlc {y} {x} {W ⊗ T})
    ≈c (((αrc {y} {x} {W} ⊗c idc {T}) ∘c αlc {y ⊗ x} {W} {T}) ∘c
        αlc {y} {x} {W ⊗ T})
  both∘αl =
    ≈ctrans (cancelC' cα-iso₁)
    (≈csym
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (≈csym pentagonₗC))
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ fuse⊗ʳC)
      (≈ctrans (∘c-congˡ (⊗c-cong cα-iso₁ ≈crefl))
      (≈ctrans (∘c-congˡ c⊗-id) cid-l)))))))
    where
    -- ((f ∘ g) ∘ h) with g∘h ≈ id collapses to f.
    cancelC' : ∀ {A B D} {f : CTm B D} {g : CTm A B} {h : CTm B A} →
               (g ∘c h) ≈c idc → ((f ∘c g) ∘c h) ≈c f
    cancelC' p = ≈ctrans c∘-assoc (≈ctrans (∘c-congʳ p) cid-r)

------------------------------------------------------------------------
-- ŝ against a tensored tail.
------------------------------------------------------------------------

ŝ-tail : ∀ {x y W T} →
         (αlc {y} {x ⊗ W} {T} ∘c
          ((idc {y} ⊗c αlc {x} {W} {T}) ∘c swapHeadC {x} {y} {W ⊗ T}))
         ≈c
         ((swapHeadC {x} {y} {W} ⊗c idc {T}) ∘c
          (αlc {x} {y ⊗ W} {T} ∘c (idc {x} ⊗c αlc {y} {W} {T})))
ŝ-tail {x} {y} {W} {T} =
  ≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym c∘-assoc))
  (≈ctrans (∘c-congˡ α-shuffle)
  (≈ctrans c∘-assoc
           (≈csym rhs-red)))))
  where
  -- RHS reduces to (αr⊗1) ∘ (αl ∘ ((σ⊗1)∘αl)) with the pentagon spent.
  rhs-red :
    ((swapHeadC {x} {y} {W} ⊗c idc {T}) ∘c
     (αlc {x} {y ⊗ W} {T} ∘c (idc {x} ⊗c αlc {y} {W} {T})))
    ≈c
    ((αrc {y} {x} {W} ⊗c idc {T}) ∘c
     (αlc {y ⊗ x} {W} {T} ∘c
      ((σc {x} {y} ⊗c idc {W ⊗ T}) ∘c αlc {x} {y} {W ⊗ T})))
  rhs-red =
    ≈ctrans (∘c-congˡ (≈csym fuse⊗ʳC))
    (≈ctrans (∘c-congˡ (∘c-congʳ (≈csym fuse⊗ʳC)))
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ pentagonₗC))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congˡ (≈ctrans α-natˡC
                        (∘c-congʳ (⊗c-cong ≈crefl c⊗-id)))))
             (∘c-congʳ c∘-assoc)))))))

------------------------------------------------------------------------
-- The insertion-past-a-suffix realization.
------------------------------------------------------------------------

mult-insʳ : ∀ Θ {x xs ys} (i : Ins x xs ys) →
            (mult ys Θ ∘c insC (insʳ Θ i)) ≈c
            ((insC i ⊗c idc {⟪ Θ ⟫}) ∘c
             (αlc ∘c (idc {x} ⊗c mult xs Θ)))
mult-insʳ Θ here =
  ≈ctrans cid-r (≈csym (≈ctrans (∘c-congˡ c⊗-id) cid-l))
mult-insʳ Θ {x} (there {y} {xs₀} {ys₀} i₀) =
  ≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ˡC))
  (≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong ≈crefl (mult-insʳ Θ i₀))))
  (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym fuse⊗ˡC)))
  (≈ctrans (∘c-congʳ (∘c-congˡ (∘c-congʳ (≈csym fuse⊗ˡC))))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym swapHeadC-nat))))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym α-natˡC))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ ŝ-tail))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈csym rhs-shape)))))))))))))))))
  where
  rhs-shape :
    ((insC (there {y = y} i₀) ⊗c idc {⟪ Θ ⟫}) ∘c
     (αlc ∘c (idc {x} ⊗c mult (y ∷ xs₀) Θ)))
    ≈c
    (((idc {y} ⊗c insC i₀) ⊗c idc) ∘c
     ((swapHeadC ⊗c idc) ∘c
      (αlc ∘c ((idc ⊗c αlc) ∘c (idc ⊗c (idc ⊗c mult xs₀ Θ))))))
  rhs-shape =
    ≈ctrans (∘c-congˡ (≈csym fuse⊗ʳC))
    (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym fuse⊗ˡC)))
             c∘-assoc)

------------------------------------------------------------------------
-- The pad realizations, mult-form.
------------------------------------------------------------------------

padʳ-real : ∀ Θ {xs ys} (p : Perm xs ys) →
            (mult ys Θ ∘c permC (padʳ Θ p)) ≈c
            ((permC p ⊗c idc {⟪ Θ ⟫}) ∘c mult xs Θ)
padʳ-real Θ pnil =
  ≈ctrans (∘c-congʳ (pid-realC Θ))
  (≈ctrans cid-r (≈csym (≈ctrans (∘c-congˡ c⊗-id) cid-l)))
padʳ-real Θ (pcons {x} p i) =
  ≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (mult-insʳ Θ i))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ fuse⊗ˡC))
  (≈ctrans (∘c-congʳ (∘c-congʳ (⊗c-cong ≈crefl (padʳ-real Θ p))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym fuse⊗ˡC)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym α-natˡC)))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (≈csym c∘-assoc)
           (∘c-congˡ fuse⊗ʳC)))))))))))

padˡ-real : ∀ Θ {xs ys} (q : Perm xs ys) →
            (mult Θ ys ∘c permC (padˡ Θ q)) ≈c
            ((idc {⟪ Θ ⟫} ⊗c permC q) ∘c mult Θ xs)
padˡ-real ε q =
  ≈csym (inv-natC cƛ-iso₂ cƛ-iso₁ cƛ-nat)
padˡ-real (A ∷ Θ) q =
  ≈ctrans (∘c-congʳ cid-l)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈ctrans fuse⊗ˡC
            (≈ctrans (⊗c-cong ≈crefl (padˡ-real Θ q))
                     (≈csym fuse⊗ˡC))))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈ctrans (≈csym α-natˡC)
                     (∘c-congˡ (⊗c-cong c⊗-id ≈crefl))))
           c∘-assoc))))
