------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A4.4b — THE withSp SPLICE, AT R-LEVEL
--
-- The generic tree relation `Tree LP` (a split tree with leaf predicate
-- LP and the standard reifySp node dressing) — R⊗, RI, RVal are all
-- instances — plus the R-level withSp-splice lemmas that the
-- fundamental lemma's α/ƛ/ρ cases consume:
--
--   withSpˡ-Tree : Tree LP sp t → Tree LQ (withSpˡ ρ sp f) (C ∘ …)
--   withSpʳ-Tree : the mirror
--
-- The node computation is the same appSp `dagger` — here `nodeL`/`nodeR`
-- via node-perm-real (DIRECTLY, since withSpˡ's node perm is already
-- `(ρ ⊙P padʳ Γ₂ ρ₁) ⊙P passoc`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq17 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; ƛrc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘; cα-nat )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pid; _⊙P_; padˡ; padʳ; passoc; passocInv )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; withSpˡ; withSpʳ )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; fuse⊗ʳC )
open import poc.OCP0009.NbEPMonAdq2
  using ( interchangeC; pid-realC )
open import poc.OCP0009.NbEPMonAdq9
  using ( node-perm-real; mult-head²; mult-headI; n-α )

------------------------------------------------------------------------
-- The generic tree relation.
------------------------------------------------------------------------

Tree : ∀ {P : Ctx → Set} {S} (LP : ∀ {Δ} → P Δ → CTm ⟪ Δ ⟫ S → Set)
       {Γ} → Sp P Γ → CTm ⟪ Γ ⟫ S → Set
Tree LP (ret p) t = LP p t
Tree LP (spl {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
  Σ _ (λ t' → Σ (Tree LP k t')
    (λ _ → t ≈c (t' ∘c (αrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))
Tree LP (usI {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
  Σ _ (λ t' → Σ (Tree LP k t')
    (λ _ → t ≈c (t' ∘c (ƛrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))

------------------------------------------------------------------------
-- The node collapse (shared by both nodes) — the appSp `collapse`,
-- parameterized by the head (αr for spl, ƛr for usI) and its mult-head.
------------------------------------------------------------------------

private
  -- (H ∘ ((n⊗1) ∘ MR)) ⊗ 1 ∘ (mult Γ₁ Γ₂ ∘ permC ρ)  with the node-perm
  -- expansion already applied, collapses to the head form. Two copies
  -- (αr / ƛr) because the neutral slides differently.
  nodeL : ∀ {Γ Γ₁} X Y Θ₁ Θ₂ Γ₂ (ρ₁ : Perm Γ₁ (Θ₁ ++ Θ₂))
            (ρ : Perm Γ (Γ₁ ++ Γ₂)) (n : CTm ⟪ Θ₁ ⟫ (X ⊗ Y)) →
          (((αrc ∘c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ₁))) ⊗c idc {⟪ Γ₂ ⟫})
           ∘c (mult Γ₁ Γ₂ ∘c permC ρ)) ≈c
          (mult (X ∷ (Y ∷ Θ₂)) Γ₂ ∘c
           (αrc ∘c ((n ⊗c idc) ∘c
             (mult Θ₁ (Θ₂ ++ Γ₂) ∘c
              permC ((ρ ⊙P padʳ Γ₂ ρ₁) ⊙P passoc Θ₁ Θ₂ Γ₂)))))
  nodeL X Y Θ₁ Θ₂ Γ₂ ρ₁ ρ n =
    ≈csym (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (node-perm-real Θ₁ Θ₂ Γ₂ ρ₁ ρ))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
      (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-α))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
      (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ (mult-head² X Y Θ₂ Γ₂))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ʳC))
      (≈ctrans (≈csym c∘-assoc)
               (∘c-congˡ fuse⊗ʳC)))))))))))))))

  nodeLI : ∀ {Γ Γ₁} Θ₁ Θ₂ Γ₂ (ρ₁ : Perm Γ₁ (Θ₁ ++ Θ₂))
             (ρ : Perm Γ (Γ₁ ++ Γ₂)) (n : CTm ⟪ Θ₁ ⟫ I) →
           (((ƛrc ∘c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ₁))) ⊗c idc {⟪ Γ₂ ⟫})
            ∘c (mult Γ₁ Γ₂ ∘c permC ρ)) ≈c
           (mult Θ₂ Γ₂ ∘c
            (ƛrc ∘c ((n ⊗c idc) ∘c
              (mult Θ₁ (Θ₂ ++ Γ₂) ∘c
               permC ((ρ ⊙P padʳ Γ₂ ρ₁) ⊙P passoc Θ₁ Θ₂ Γ₂)))))
  nodeLI Θ₁ Θ₂ Γ₂ ρ₁ ρ n =
    ≈csym (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (node-perm-real Θ₁ Θ₂ Γ₂ ρ₁ ρ))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
      (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
                 (≈csym (≈ctrans cα-nat
                          (∘c-congˡ (⊗c-cong ≈crefl c⊗-id))))))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
      (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ (mult-headI Θ₂ Γ₂))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ʳC))
      (≈ctrans (≈csym c∘-assoc)
               (∘c-congˡ fuse⊗ʳC)))))))))))))))


------------------------------------------------------------------------
-- withSpˡ-Tree — the R-level withSpˡ-splice.
------------------------------------------------------------------------

withSpˡ-Tree : ∀ {P Q : Ctx → Set} {S T : CTy} {Γ₂}
  (LP : ∀ {Δ} → P Δ → CTm ⟪ Δ ⟫ S → Set)
  (LQ : ∀ {Δ} → Q Δ → CTm ⟪ Δ ⟫ T → Set)
  (C : CTm (S ⊗ ⟪ Γ₂ ⟫) T)
  (f : ∀ {Δ₁ Δ} → Perm Δ (Δ₁ ++ Γ₂) → P Δ₁ → Sp Q Δ)
  (Hf : ∀ {Δ₁ Δ} (ρ' : Perm Δ (Δ₁ ++ Γ₂)) (p : P Δ₁) {sp' : CTm ⟪ Δ₁ ⟫ S} →
        LP p sp' →
        Tree LQ (f ρ' p) (C ∘c ((sp' ⊗c idc) ∘c (mult Δ₁ Γ₂ ∘c permC ρ')))) →
  ∀ {Γ Γ₁} (ρ : Perm Γ (Γ₁ ++ Γ₂)) (sp : Sp P Γ₁) {t} →
  Tree LP sp t →
  Tree LQ (withSpˡ ρ sp f)
    (C ∘c ((t ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ)))
withSpˡ-Tree LP LQ C f Hf ρ (ret p) rp = Hf ρ p rp
withSpˡ-Tree {Γ₂ = Γ₂} LP LQ C f Hf ρ
             (spl {X = X} {Y = Y} {Γ₁ = Θ₁} {Γ₂ = Θ₂} ρ₁ n k) {t} (t' , (rk , e)) =
  _ , (withSpˡ-Tree LP LQ C f Hf (pid _) k rk ,
    ≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong e ≈crefl)))
    (≈ctrans (∘c-congʳ (∘c-congˡ
               (≈ctrans (⊗c-cong ≈crefl (≈csym cid-l)) c⊗-∘)))
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ (nodeL X Y Θ₁ Θ₂ Γ₂ ρ₁ ρ n)))
             (≈csym (≈ctrans c∘-assoc (∘c-congʳ (≈ctrans c∘-assoc
               (∘c-congʳ (≈ctrans c∘-assoc
                 (∘c-congʳ (≈ctrans (∘c-congˡ (pid-realC _)) cid-l))))))))))))
withSpˡ-Tree {Γ₂ = Γ₂} LP LQ C f Hf ρ
             (usI {Γ₁ = Θ₁} {Θ₂} ρ₁ n k) {t} (t' , (rk , e)) =
  _ , (withSpˡ-Tree LP LQ C f Hf (pid _) k rk ,
    ≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong e ≈crefl)))
    (≈ctrans (∘c-congʳ (∘c-congˡ
               (≈ctrans (⊗c-cong ≈crefl (≈csym cid-l)) c⊗-∘)))
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ (nodeLI Θ₁ Θ₂ Γ₂ ρ₁ ρ n)))
             (≈csym (≈ctrans c∘-assoc (∘c-congʳ (≈ctrans c∘-assoc
               (∘c-congʳ (≈ctrans c∘-assoc
                 (∘c-congʳ (≈ctrans (∘c-congˡ (pid-realC _)) cid-l))))))))))))
