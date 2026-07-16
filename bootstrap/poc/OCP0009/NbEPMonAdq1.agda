------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A1 — THE ISO BACKBONE
--
-- The adequacy climb (plan §10, L3.4b, staged A1–A4) begins where the
-- completeness proof will END: the final step of `f ≈c NF f` peels
-- `reify (evalV f (reflectTy A)) ∘ splitTm A` back to `f` through
--
--   join-split : joinTm A ∘c splitTm A ≈c idc
--
-- This module proves that backbone and the kit it stands on — all
-- ports of proven recipes (`NbEPMonN`'s `cancel`/`nt-tn` shapes,
-- `NbEPMonY`'s fuses), re-run over the closed theory `_≈c_`:
--
--   * `∘c-congˡ/ʳ`, `cancelC`  — the chain kit
--   * `fuse⊗ˡC`/`fuse⊗ʳC`      — tensor fusions
--   * `mult-inv-l/r`           — ⟪Γ++Δ⟫ ≅ ⟪Γ⟫⊗⟪Δ⟫, mutually inverse
--   * `join-split`/`split-join`— A ≅ ⟪ctxOf A⟫: the generic
--     decomposition is an ISO up to `_≈c_`
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq1 where

open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; Λc; evc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong; Λc-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cα-iso₁; cα-iso₂; cƛ-iso₁; cƛ-iso₂; cρ-iso₁; cρ-iso₂ )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv; ctxOf; splitTm; joinTm )
open import normalizer.Syntax.Types
  using ( _≡_; refl )

------------------------------------------------------------------------
-- Permutation congruence: equal perms give ≈c-equal reifications.
------------------------------------------------------------------------

permC-≡ : ∀ {xs ys} {p q : Perm xs ys} → p ≡ q → permC p ≈c permC q
permC-≡ refl = ≈crefl

------------------------------------------------------------------------
-- The chain kit (ports of NbEPMonN).
------------------------------------------------------------------------

∘c-congˡ : ∀ {A B D} {f f' : CTm B D} {g : CTm A B} →
           f ≈c f' → (f ∘c g) ≈c (f' ∘c g)
∘c-congˡ p = ∘c-cong p ≈crefl

∘c-congʳ : ∀ {A B D} {f : CTm B D} {g g' : CTm A B} →
           g ≈c g' → (f ∘c g) ≈c (f ∘c g')
∘c-congʳ p = ∘c-cong ≈crefl p

cancelC : ∀ {A B D E} {f : CTm B E} {g : CTm D B} {h : CTm B D}
            {k : CTm A B} →
          (g ∘c h) ≈c idc → ((f ∘c g) ∘c (h ∘c k)) ≈c (f ∘c k)
cancelC p =
  ≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ p))
           (∘c-congʳ cid-l)))

fuse⊗ˡC : ∀ {A B D E} {f : CTm B D} {g : CTm A B} →
          ((idc {E} ⊗c f) ∘c (idc ⊗c g)) ≈c (idc ⊗c (f ∘c g))
fuse⊗ˡC = ≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-l ≈crefl)

fuse⊗ʳC : ∀ {A B D E} {f : CTm B D} {g : CTm A B} →
          ((f ⊗c idc {E}) ∘c (g ⊗c idc)) ≈c ((f ∘c g) ⊗c idc)
fuse⊗ʳC = ≈ctrans (≈csym c⊗-∘) (⊗c-cong ≈crefl cid-l)

------------------------------------------------------------------------
-- The Day mediators are mutually inverse (the nt-tn recipe).
------------------------------------------------------------------------

mult-inv-l : ∀ Γ Δ → (multInv Γ Δ ∘c mult Γ Δ) ≈c idc
mult-inv-l ε       Δ = cƛ-iso₁
mult-inv-l (A ∷ Γ) Δ =
  ≈ctrans (cancelC cα-iso₁)
  (≈ctrans fuse⊗ˡC
  (≈ctrans (⊗c-cong ≈crefl (mult-inv-l Γ Δ)) c⊗-id))

mult-inv-r : ∀ Γ Δ → (mult Γ Δ ∘c multInv Γ Δ) ≈c idc
mult-inv-r ε       Δ = cƛ-iso₂
mult-inv-r (A ∷ Γ) Δ =
  ≈ctrans (cancelC (≈ctrans fuse⊗ˡC
                   (≈ctrans (⊗c-cong ≈crefl (mult-inv-r Γ Δ)) c⊗-id)))
          cα-iso₂

------------------------------------------------------------------------
-- Generic decomposition is an iso: A ≅ ⟪ctxOf A⟫ up to ≈c.
------------------------------------------------------------------------

join-split : ∀ A → (joinTm A ∘c splitTm A) ≈c idc
join-split ι₁      = cρ-iso₁
join-split ι₂      = cρ-iso₁
join-split I       = cid-l
join-split (A ⊗ B) =
  ≈ctrans (cancelC (mult-inv-r (ctxOf A) (ctxOf B)))
  (≈ctrans (≈csym c⊗-∘)
  (≈ctrans (⊗c-cong (join-split A) (join-split B)) c⊗-id))
join-split (A ⊸ B) = cρ-iso₁

split-join : ∀ A → (splitTm A ∘c joinTm A) ≈c idc
split-join ι₁      = cρ-iso₂
split-join ι₂      = cρ-iso₂
split-join I       = cid-l
split-join (A ⊗ B) =
  ≈ctrans (cancelC (≈ctrans (≈csym c⊗-∘)
                   (≈ctrans (⊗c-cong (split-join A) (split-join B))
                            c⊗-id)))
          (mult-inv-l (ctxOf A) (ctxOf B))
split-join (A ⊸ B) = cρ-iso₂
