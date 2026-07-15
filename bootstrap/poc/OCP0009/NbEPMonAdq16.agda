------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A4.4a — THE JOIN PRESERVES R
--
-- The shared helper the fundamental lemma's absorb/withSp cases need:
-- `absorb` (the split-monad join) preserves the gluing relation.
--
--   RVal  B sp t  — a tree of Val-B leaves relates to t (R-related
--                   leaves, node dressing mirroring reifySp)
--   R-join        : RVal B sp t → R B (absorb B sp) t
--   appSp-RVal    : the ⊸-case engine — applying a related argument
--                   under the pending splits (the R-level appSp-splice)
--
-- The transport-free split monad keeps the non-⊸ node cases clean
-- recursion (absorb = bindSp id threads through spl/usI on the nose);
-- the ⊸ case pushes the argument through via `appSp`, whose node
-- permutation realizes exactly as in appSp-splice.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq16 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; sym; cong )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; ƛrc; evc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘; cα-nat )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pid; _⊙P_; padʳ; passoc )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; Val; absorb; appSp )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; fuse⊗ʳC )
open import poc.OCP0009.NbEPMonAdq2
  using ( interchangeC; pid-realC )
open import poc.OCP0009.NbEPMonAdq8
  using ( ⊙P-pidˡ )
open import poc.OCP0009.NbEPMonAdq9
  using ( node-perm-real; mult-head²; mult-headI; n-α )
open import poc.OCP0009.NbEPMonAdq12
  using ( R )

private
  permC-≡ : ∀ {xs ys} {p q : Perm xs ys} → p ≡ q → permC p ≈c permC q
  permC-≡ refl = ≈crefl

------------------------------------------------------------------------
-- The tree relation over Val-B leaves.
------------------------------------------------------------------------

RVal : ∀ B {Γ} → Sp (Val B) Γ → CTm ⟪ Γ ⟫ B → Set
RVal B (ret x) t = R B x t
RVal B (spl {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
  Σ _ (λ t' → Σ (RVal B k t')
    (λ _ → t ≈c (t' ∘c (αrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))
RVal B (usI {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
  Σ _ (λ t' → Σ (RVal B k t')
    (λ _ → t ≈c (t' ∘c (ƛrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))

------------------------------------------------------------------------
-- (†) — the appSp node computation (the appSp-splice node eqn, bare).
------------------------------------------------------------------------

private
  dagger : ∀ Γ X Y Θ₁ Θ₂ (ρ : Perm Γ (Θ₁ ++ Θ₂))
             (n : CTm ⟪ Θ₁ ⟫ (X ⊗ Y)) Δ →
           (((αrc ∘c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ)))
             ⊗c idc {⟪ Δ ⟫}) ∘c mult Γ Δ) ≈c
           (mult (X ∷ (Y ∷ Θ₂)) Δ ∘c
            (αrc ∘c ((n ⊗c idc) ∘c
              (mult Θ₁ (Θ₂ ++ Δ) ∘c permC (padʳ Δ ρ ⊙P passoc Θ₁ Θ₂ Δ)))))
  dagger Γ X Y Θ₁ Θ₂ ρ n Δ =
    ≈csym (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ npr))) collapse)
    where
    npr : (mult Θ₁ (Θ₂ ++ Δ) ∘c permC (padʳ Δ ρ ⊙P passoc Θ₁ Θ₂ Δ)) ≈c
          ((idc ⊗c multInv Θ₂ Δ) ∘c
           (αrc ∘c (((mult Θ₁ Θ₂ ∘c permC ρ) ⊗c idc) ∘c mult Γ Δ)))
    npr =
      ≈ctrans (∘c-congʳ (permC-≡
                (cong (_⊙P passoc Θ₁ Θ₂ Δ) (sym (⊙P-pidˡ (padʳ Δ ρ))))))
      (≈ctrans (node-perm-real Θ₁ Θ₂ Δ ρ (pid _))
               (∘c-congʳ (∘c-congʳ (∘c-congʳ
                 (≈ctrans (∘c-congʳ (pid-realC _)) cid-r)))))
    collapse :
      (mult (X ∷ (Y ∷ Θ₂)) Δ ∘c
       (αrc ∘c ((n ⊗c idc) ∘c
         ((idc ⊗c multInv Θ₂ Δ) ∘c
          (αrc ∘c (((mult Θ₁ Θ₂ ∘c permC ρ) ⊗c idc) ∘c mult Γ Δ)))))) ≈c
      (((αrc ∘c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ))) ⊗c idc) ∘c
       mult Γ Δ)
    collapse =
      ≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
      (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-α))))
      (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
      (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ (mult-head² X Y Θ₂ Δ))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ʳC))
      (≈ctrans (≈csym c∘-assoc)
               (∘c-congˡ fuse⊗ʳC)))))))))))))

  daggerI : ∀ Γ Θ₁ Θ₂ (ρ : Perm Γ (Θ₁ ++ Θ₂))
              (n : CTm ⟪ Θ₁ ⟫ I) Δ →
            (((ƛrc ∘c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ)))
              ⊗c idc {⟪ Δ ⟫}) ∘c mult Γ Δ) ≈c
            (mult Θ₂ Δ ∘c
             (ƛrc ∘c ((n ⊗c idc) ∘c
               (mult Θ₁ (Θ₂ ++ Δ) ∘c permC (padʳ Δ ρ ⊙P passoc Θ₁ Θ₂ Δ)))))
  daggerI Γ Θ₁ Θ₂ ρ n Δ =
    ≈csym (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ npr))) collapseI)
    where
    npr : (mult Θ₁ (Θ₂ ++ Δ) ∘c permC (padʳ Δ ρ ⊙P passoc Θ₁ Θ₂ Δ)) ≈c
          ((idc ⊗c multInv Θ₂ Δ) ∘c
           (αrc ∘c (((mult Θ₁ Θ₂ ∘c permC ρ) ⊗c idc) ∘c mult Γ Δ)))
    npr =
      ≈ctrans (∘c-congʳ (permC-≡
                (cong (_⊙P passoc Θ₁ Θ₂ Δ) (sym (⊙P-pidˡ (padʳ Δ ρ))))))
      (≈ctrans (node-perm-real Θ₁ Θ₂ Δ ρ (pid _))
               (∘c-congʳ (∘c-congʳ (∘c-congʳ
                 (≈ctrans (∘c-congʳ (pid-realC _)) cid-r)))))
    collapseI :
      (mult Θ₂ Δ ∘c
       (ƛrc ∘c ((n ⊗c idc) ∘c
         ((idc ⊗c multInv Θ₂ Δ) ∘c
          (αrc ∘c (((mult Θ₁ Θ₂ ∘c permC ρ) ⊗c idc) ∘c mult Γ Δ)))))) ≈c
      (((ƛrc ∘c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ))) ⊗c idc) ∘c
       mult Γ Δ)
    collapseI =
      ≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
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
      (≈ctrans (∘c-congˡ (mult-headI Θ₂ Δ))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ʳC))
      (≈ctrans (≈csym c∘-assoc)
               (∘c-congˡ fuse⊗ʳC)))))))))))))

------------------------------------------------------------------------
-- The join preserves R.
------------------------------------------------------------------------

mutual
  R-join : ∀ B {Γ} (sp : Sp (Val B) Γ) {t} → RVal B sp t → R B (absorb B sp) t
  -- atoms / unit / tensor: absorb = bindSp id threads through nodes.
  R-join ι₁ (ret x) rx = rx
  R-join ι₁ (spl ρ n k) (t' , (rk , e)) = t' , (R-join ι₁ k rk , e)
  R-join ι₁ (usI ρ n k) (t' , (rk , e)) = t' , (R-join ι₁ k rk , e)
  R-join ι₂ (ret x) rx = rx
  R-join ι₂ (spl ρ n k) (t' , (rk , e)) = t' , (R-join ι₂ k rk , e)
  R-join ι₂ (usI ρ n k) (t' , (rk , e)) = t' , (R-join ι₂ k rk , e)
  R-join I (ret x) rx = rx
  R-join I (spl ρ n k) (t' , (rk , e)) = t' , (R-join I k rk , e)
  R-join I (usI ρ n k) (t' , (rk , e)) = t' , (R-join I k rk , e)
  R-join (A ⊗ B) (ret x) rx = rx
  R-join (A ⊗ B) (spl ρ n k) (t' , (rk , e)) = t' , (R-join (A ⊗ B) k rk , e)
  R-join (A ⊗ B) (usI ρ n k) (t' , (rk , e)) = t' , (R-join (A ⊗ B) k rk , e)
  -- function: push the argument through appSp.
  R-join (A ⊸ B) sp rsp {Δ} w s rws =
    R-join B (appSp Δ w sp) (appSp-RVal sp rsp w s rws)

  appSp-RVal : ∀ {A B Γ} (sp : Sp (Val (A ⊸ B)) Γ) {t} →
               RVal (A ⊸ B) sp t →
               ∀ {Δ} (w : Val A Δ) (s : CTm ⟪ Δ ⟫ A) → R A w s →
               RVal B (appSp Δ w sp) (evc ∘c ((t ⊗c s) ∘c mult Γ Δ))
  appSp-RVal (ret f) rf w s rws = rf w s rws
  appSp-RVal (spl {Γ = Γ} {X} {Y} {Γ₁ = Θ₁} {Γ₂ = Θ₂} ρ n k)
             {t} (t' , (rk , e)) {Δ} w s rws =
    _ , (appSp-RVal k rk w s rws ,
      ≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong e ≈crefl)))
      (≈ctrans (∘c-congʳ (∘c-congˡ
                 (≈ctrans (⊗c-cong ≈crefl (≈csym cid-r)) c⊗-∘)))
      (≈ctrans (∘c-congʳ c∘-assoc)
      (≈ctrans (∘c-congʳ (∘c-congʳ (dagger Γ X Y Θ₁ Θ₂ ρ n Δ)))
               (≈csym (≈ctrans c∘-assoc (∘c-congʳ c∘-assoc)))))))
  appSp-RVal (usI {Γ = Γ} {Γ₁ = Θ₁} {Γ₂ = Θ₂} ρ n k)
             {t} (t' , (rk , e)) {Δ} w s rws =
    _ , (appSp-RVal k rk w s rws ,
      ≈ctrans (∘c-congʳ (∘c-congˡ (⊗c-cong e ≈crefl)))
      (≈ctrans (∘c-congʳ (∘c-congˡ
                 (≈ctrans (⊗c-cong ≈crefl (≈csym cid-r)) c⊗-∘)))
      (≈ctrans (∘c-congʳ c∘-assoc)
      (≈ctrans (∘c-congʳ (∘c-congʳ (daggerI Γ Θ₁ Θ₂ ρ n Δ)))
               (≈csym (≈ctrans c∘-assoc (∘c-congʳ c∘-assoc)))))))
