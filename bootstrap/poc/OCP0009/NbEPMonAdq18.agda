------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A4.5 — THE CAPSTONE
--
-- The completeness/adequacy theorem for the free SMCC, assembled from
-- the fundamental lemma and the boundary lemmas:
--
--   adequacy : f ≈c NF f
--   decide   : NF f ≡ NF g → f ≈c g
--
-- Chain: NF f = reify (evalV f (reflectTy A)) ∘ splitTm A.  The
-- fundamental lemma relates `evalV f (reflectTy A)` to `f ∘ joinTm A`
-- (via R-reflectTy), R-reify reads that back off the reification, and
-- `join-split` (joinTm ∘ splitTm ≈ id) cancels the boundary — leaving
-- `f`.  `decide` is then the decision procedure for ≈c: normal forms
-- are syntactically equal iff the terms are convertible.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq18 where

open import normalizer.Syntax.Types
  using ( _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; CTm; idc; _∘c_
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans
        ; cid-r; c∘-assoc )
open import poc.OCP0009.NbEPMonW
  using ( joinTm )
open import poc.OCP0009.NbEPMonF
  using ( reify; evalV; reflectTy; NF )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; join-split )
open import poc.OCP0009.NbEPMonAdq14
  using ( R-reify; R-reflectTy )
open import poc.OCP0009.NbEPMonAdq15
  using ( fund )

------------------------------------------------------------------------
-- Adequacy: every combinator is convertible to its normal form.
------------------------------------------------------------------------

adequacy : ∀ {A B} (f : CTm A B) → f ≈c NF f
adequacy {A} f =
  ≈csym
    (≈ctrans (∘c-congˡ (R-reify _ (fund f (R-reflectTy A))))
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ (join-split A)) cid-r)))

------------------------------------------------------------------------
-- The decision procedure for ≈c (soundness direction of `NF`).
------------------------------------------------------------------------

private
  ≡→≈c : ∀ {A B} {f g : CTm A B} → f ≡ g → f ≈c g
  ≡→≈c refl = ≈crefl

decide : ∀ {A B} (f g : CTm A B) → NF f ≡ NF g → f ≈c g
decide f g p =
  ≈ctrans (adequacy f) (≈ctrans (≡→≈c p) (≈csym (adequacy g)))
