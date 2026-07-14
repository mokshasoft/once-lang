------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3C.3 (complete) — THE ALGEBRA, REALIZED
--
-- The three remaining compatibility theorems between the `Perm`-algebra
-- (stage 3A) and the morphism theory:
--
--   * `push-real` — the factorization is a NATURALITY SQUARE:
--       permM q ∘ insM i  ≈  insM j′ ∘ (1 ⊗ permM q′)
--     for `push i q ≡ (ws′, (q′, j′))`. Consumes `ins-swap-real` (hence
--     Yang–Baxter), `swapHead-nat`, `swapHead-invol`.
--   * `⊙P-real` — composition of permutations realizes composition of
--     morphisms: permM (p ⊙P q) ≈ permM q ∘ permM p. Via `push-real`.
--   * `nt-perm-nat` — the PADDING SQUARE: flattening commutes with an
--     accumulator permutation,
--       nt B S′ ∘ (1_B ⊗ permM q)  ≈  permM (padP B q) ∘ nt B S.
--     Induction on `B`: leaves are unit shuffles, `I` is exactly `ƛ-nat`,
--     `⊗` is α-naturality + both IHs. This is the lemma that lets the
--     `_⊗m_` case of the key lemma (stage 3E) avoid list-append transport
--     entirely.
--
-- With these, stage 3C is COMPLETE: every operation of the permutation
-- algebra is provably realized. What remains for completeness: the
-- generator squares (3D) and the key-lemma assembly (3E).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonQ where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; ƛr
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; α-nat; ƛ-nat )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; norm; nt )
open import poc.OCP0009.NbEPMonP
  using ( Ins; here; there; Perm; pnil; pcons
        ; insM; permM; swapHead )
open import poc.OCP0009.NbEPMonA
  using ( ins-swap; push; _⊙P_; padP )
open import poc.OCP0009.NbEPMonR
  using ( swapHead-nat; swapHead-invol )
open import poc.OCP0009.NbEPMonY
  using ( fuse⊗ˡ )
open import poc.OCP0009.NbEPMonI
  using ( ins-swap-real )

------------------------------------------------------------------------
-- Factorization, realized: a naturality square for insertions.
------------------------------------------------------------------------

push-real :
  ∀ {x ys zs ws ws'} (i : Ins x ys zs) (q : Perm zs ws)
    {q' : Perm ys ws'} {j' : Ins x ws' ws} →
  push i q ≡ (ws' , (q' , j')) →
  (permM q ∘m insM i) ≈m (insM j' ∘m (idm ⊗m permM q'))

push-real here (pcons q₀ j) refl = id-r

push-real (there i₀) (pcons q₀ j) refl =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ fuse⊗ˡ))
  (≈trans (∘-congʳ (∘-congˡ (⊗-cong ≈refl (push-real i₀ q₀ refl))))
  (≈trans (∘-congʳ (∘-congˡ (≈sym fuse⊗ˡ)))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (ins-swap-real _ j refl))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ swapHead-nat))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ swapHead-invol))
  (≈trans (∘-congʳ id-r)
  (≈trans ∘-assoc
          (∘-congʳ fuse⊗ˡ)))))))))))))))

------------------------------------------------------------------------
-- Composition, realized.
------------------------------------------------------------------------

⊙P-real : ∀ {xs ys zs} (p : Perm xs ys) (q : Perm ys zs) →
          permM (p ⊙P q) ≈m (permM q ∘m permM p)
⊙P-real pnil        q = ≈sym id-r
⊙P-real (pcons p₀ i) q =
  ≈trans (∘-congʳ (⊗-cong ≈refl (⊙P-real p₀ _)))
  (≈trans (∘-congʳ (≈sym fuse⊗ˡ))
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (≈sym (push-real i q refl)))
          ∘-assoc)))

------------------------------------------------------------------------
-- Padding, realized: flattening commutes with accumulator permutations.
------------------------------------------------------------------------

nt-perm-nat : ∀ B {S S'} (q : Perm S S') →
              (nt B S' ∘m (idm {B} ⊗m permM q)) ≈m
              (permM (padP B q) ∘m nt B S)
nt-perm-nat ι₁ q = ≈trans id-l (≈sym (≈trans (∘-congˡ id-l) id-r))
nt-perm-nat ι₂ q = ≈trans id-l (≈sym (≈trans (∘-congˡ id-l) id-r))
nt-perm-nat I  q = ƛ-nat
nt-perm-nat (A ⊗ B) {S} {S'} q =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ (∘-congʳ (⊗-cong (≈sym ⊗-id) ≈refl))))
  (≈trans (∘-congʳ (∘-congʳ α-nat))
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ fuse⊗ˡ))
  (≈trans (∘-congʳ (∘-congˡ (⊗-cong ≈refl (nt-perm-nat B q))))
  (≈trans (∘-congʳ (∘-congˡ (≈sym fuse⊗ˡ)))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (nt-perm-nat A (padP B q)))
          ∘-assoc))))))))))
