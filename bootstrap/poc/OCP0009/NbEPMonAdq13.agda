------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A4.2 — KRIPKE MONOTONICITY
--
--   R-vmap : R A v t → R A (vmap A ρ v) (t ∘c permC ρ)
--
-- The split-monad's "pending permutation lives only in the top node"
-- design (L3.1b) pays out once more: `vmap` is shallow, so R-vmap is
-- shallow too — the spl/usI cases REUSE their continuation's relation
-- proof and only re-associate the node dressing (⊙P-realC), the
-- ret/leaf cases adjust one ≈c. Only the ⊸ case does real work:
-- recursive R-vmap over the world-extended argument, transported by
-- `padʳ-real`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq13 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; ƛrc; evc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ⊗c-cong
        ; cid-r; c∘-assoc; c⊗-∘ )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pnil; pcons; _⊙P_; padʳ )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; AtCore; Val; vmap )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ )
open import poc.OCP0009.NbEPMonAdq2
  using ( ⊙P-realC )
open import poc.OCP0009.NbEPMonAdq3
  using ( padʳ-real )
open import poc.OCP0009.NbEPMonAdq12
  using ( R; R-resp )

------------------------------------------------------------------------
-- The node-dressing re-association (head-agnostic).
------------------------------------------------------------------------

private
  headAdj :
    ∀ {V P Γ₁ Γ₂ Γ' Γ}
      (H : CTm (P ⊗ ⟪ Γ₂ ⟫) V) (n : CTm ⟪ Γ₁ ⟫ P)
      (ρ₀ : Perm Γ (Γ₁ ++ Γ₂)) (ρ : Perm Γ' Γ) →
    ((H ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ₀))) ∘c permC ρ) ≈c
    (H ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC (ρ ⊙P ρ₀))))
  headAdj H n ρ₀ ρ =
    ≈ctrans c∘-assoc (∘c-congʳ (≈ctrans c∘-assoc
      (∘c-congʳ (≈ctrans c∘-assoc (∘c-congʳ (≈csym (⊙P-realC ρ ρ₀)))))))

  -- The spl/usI outer-eq adjustment: from `t ≈c t'∘DRESS(ρ₀)` conclude
  -- `t∘permC ρ ≈c t'∘DRESS(ρ⊙Pρ₀)`.
  splAdj :
    ∀ {A V P Γ₁ Γ₂ Γ' Γ}
      {t' : CTm ⟪ V ⟫ A} (H : CTm (P ⊗ ⟪ Γ₂ ⟫) ⟪ V ⟫)
      (n : CTm ⟪ Γ₁ ⟫ P) (ρ₀ : Perm Γ (Γ₁ ++ Γ₂)) (ρ : Perm Γ' Γ)
      {t : CTm ⟪ Γ ⟫ A} →
    t ≈c (t' ∘c (H ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ₀)))) →
    (t ∘c permC ρ) ≈c
    (t' ∘c (H ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC (ρ ⊙P ρ₀)))))
  splAdj H n ρ₀ ρ e =
    ≈ctrans (∘c-congˡ e) (≈ctrans c∘-assoc (∘c-congʳ (headAdj H n ρ₀ ρ)))

------------------------------------------------------------------------
-- Monotonicity.
------------------------------------------------------------------------

R-vmap : ∀ A {Γ' Γ} (ρ : Perm Γ' Γ) {v : Val A Γ} {t : CTm ⟪ Γ ⟫ A} →
         R A v t → R A (vmap A ρ v) (t ∘c permC ρ)

-- atoms
R-vmap ι₁ ρ {ret (Γ₀ , (ρ₀ , m))} r =
  ≈ctrans (∘c-congʳ (⊙P-realC ρ ρ₀))
          (≈ctrans (≈csym c∘-assoc) (∘c-congˡ r))
R-vmap ι₁ ρ {spl ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj αrc n ρ₀ ρ e)
R-vmap ι₁ ρ {usI ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj ƛrc n ρ₀ ρ e)

R-vmap ι₂ ρ {ret (Γ₀ , (ρ₀ , m))} r =
  ≈ctrans (∘c-congʳ (⊙P-realC ρ ρ₀))
          (≈ctrans (≈csym c∘-assoc) (∘c-congˡ r))
R-vmap ι₂ ρ {spl ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj αrc n ρ₀ ρ e)
R-vmap ι₂ ρ {usI ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj ƛrc n ρ₀ ρ e)

-- unit
R-vmap I pnil {ret refl} r = ≈ctrans r (≈csym cid-r)
R-vmap I (pcons p ()) {ret refl} r
R-vmap I ρ {spl ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj αrc n ρ₀ ρ e)
R-vmap I ρ {usI ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj ƛrc n ρ₀ ρ e)

-- tensor
R-vmap (A ⊗ B) ρ {ret (Δ₁ , (Δ₂ , (ρ₀ , (va , vb))))} (ta , (tb , (ra , (rb , e)))) =
  ta , (tb , (ra , (rb ,
    ≈ctrans (∘c-congˡ e)
    (≈ctrans c∘-assoc
    (∘c-congʳ (≈ctrans c∘-assoc
      (∘c-congʳ (≈csym (⊙P-realC ρ ρ₀)))))))))
R-vmap (A ⊗ B) ρ {spl ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj αrc n ρ₀ ρ e)
R-vmap (A ⊗ B) ρ {usI ρ₀ n k} (t' , (rk , e)) =
  t' , (rk , splAdj ƛrc n ρ₀ ρ e)

-- function (the only recursive case)
R-vmap (A ⊸ B) ρ {f} {t} rf {Δ} w s rws =
  R-resp B (R-vmap B (padʳ Δ ρ) (rf w s rws)) termEq
  where
  termEq :
    ((evc ∘c ((t ⊗c s) ∘c mult _ Δ)) ∘c permC (padʳ Δ ρ)) ≈c
    (evc ∘c (((t ∘c permC ρ) ⊗c s) ∘c mult _ Δ))
  termEq =
    ≈ctrans c∘-assoc
    (∘c-congʳ (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (padʳ-real Δ ρ))
      (≈ctrans (≈csym c∘-assoc)
               (∘c-congˡ (≈ctrans (≈csym c⊗-∘)
                        (⊗c-cong ≈crefl cid-r)))))))
