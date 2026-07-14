------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3C.3 (part 1) — the DIAMOND, REALIZED
--
-- `ins-swap` (stage 3A) commutes two insertions at the DATA level; this
-- module proves the realizations agree — the morphism that inserts `x`
-- then `y` equals the morphism that inserts `y` then `x`, conjugated by
-- the head transposition:
--
--   ins-swap-real : ins-swap i j ≡ (w₃ , (jy , jx)) →
--     insM j ∘ (1 ⊗ insM i) ≈m (insM jx ∘ (1 ⊗ insM jy)) ∘ swapHead
--
-- (Stated in "graph" form — the equation hypothesis binds the diamond's
-- components — so the proof's case analysis mirrors `ins-swap`'s `with`
-- and everything reduces.)
--
-- Where the symmetric-group presentation gets consumed, case by case:
--   * here/here and there/here — `swapHead-invol` (the transposition is
--     its own inverse);
--   * here/there — a unit shuffle;
--   * there/there — `swapHead-nat` (commutation) on BOTH sides + the
--     induction hypothesis + **Yang–Baxter** (3C.2) connecting the two
--     three-transposition tails. This is the case the whole 3C.2 climb
--     existed for.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonI where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ )
open import poc.OCP0009.NbEPMonP
  using ( Ins; here; there; insM; swapHead )
open import poc.OCP0009.NbEPMonA
  using ( ins-swap )
open import poc.OCP0009.NbEPMonR
  using ( swapHead-nat; swapHead-invol )
open import poc.OCP0009.NbEPMonY
  using ( fuse⊗ˡ; YB )

------------------------------------------------------------------------
-- The realization of the insertion diamond.
------------------------------------------------------------------------

ins-swap-real :
  ∀ {x y w₂ w₁ w w₃} (i : Ins x w₂ w₁) (j : Ins y w₁ w)
    {jy : Ins y w₂ w₃} {jx : Ins x w₃ w} →
  ins-swap i j ≡ (w₃ , (jy , jx)) →
  (insM j ∘m (idm ⊗m insM i)) ≈m
  ((insM jx ∘m (idm ⊗m insM jy)) ∘m swapHead)

ins-swap-real here here refl =
  ≈trans (≈trans id-l ⊗-id) (≈sym rhs)
  where
  rhs : ∀ {x y w₂} →
        ((((idm {y} ⊗m idm {x ⊗ w₂}) ∘m swapHead) ∘m (idm ⊗m idm)) ∘m swapHead)
        ≈m idm
  rhs = ≈trans (∘-congˡ (∘-congˡ (∘-congˡ ⊗-id)))
        (≈trans (∘-congˡ (∘-congˡ id-l))
        (≈trans (∘-congˡ (∘-congʳ ⊗-id))
        (≈trans (∘-congˡ id-r)
                swapHead-invol)))

ins-swap-real here (there j₀) refl =
  ≈trans (∘-congʳ ⊗-id) (≈trans id-r (∘-congˡ (≈sym id-l)))

ins-swap-real (there i₀) here refl =
  ≈trans id-l (≈sym rhs3)
  where
  rhs3 : ∀ {x y z w₂' w₁'} {k : Ins x w₂' w₁'} →
         ((((idm {y} ⊗m insM (there {y = z} k)) ∘m swapHead) ∘m (idm {x} ⊗m idm)) ∘m swapHead)
         ≈m (idm {y} ⊗m insM (there k))
  rhs3 = ≈trans (∘-congˡ (∘-congʳ ⊗-id))
         (≈trans (∘-congˡ id-r)
         (≈trans ∘-assoc
         (≈trans (∘-congʳ swapHead-invol) id-r)))

ins-swap-real (there i₀) (there j₀) refl =
  ≈trans lhs≈LT (≈trans (∘-congʳ (∘-congʳ YB)) (≈sym rhs≈RT))
  where
  lhs≈LT = ≈trans (∘-congʳ (≈sym fuse⊗ˡ))
           (≈trans ∘-assoc
           (≈trans (∘-congʳ (≈sym ∘-assoc))
           (≈trans (∘-congʳ (∘-congˡ swapHead-nat))
           (≈trans (∘-congʳ ∘-assoc)
           (≈trans (≈sym ∘-assoc)
           (≈trans (∘-congˡ fuse⊗ˡ)
           (≈trans (∘-congˡ (⊗-cong ≈refl (ins-swap-real i₀ j₀ refl)))
           (≈trans (∘-congˡ (≈sym fuse⊗ˡ))
           (≈trans (∘-congˡ (∘-congˡ (≈sym fuse⊗ˡ)))
           (≈trans ∘-assoc
                   ∘-assoc))))))))))
  rhs≈RT = ≈trans (∘-congˡ (∘-congʳ (≈sym fuse⊗ˡ)))
           (≈trans (∘-congˡ ∘-assoc)
           (≈trans (∘-congˡ (∘-congʳ (≈sym ∘-assoc)))
           (≈trans (∘-congˡ (∘-congʳ (∘-congˡ swapHead-nat)))
           (≈trans (∘-congˡ (∘-congʳ ∘-assoc))
           (≈trans ∘-assoc
           (≈trans (∘-congʳ ∘-assoc)
                   (∘-congʳ (∘-congʳ ∘-assoc))))))))
