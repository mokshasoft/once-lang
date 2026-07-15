------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A4.1 — THE GLUING RELATION
--
-- The Kripke logical relation `R A v t` ("the value v represents the
-- term t") that the fundamental lemma is stated over. Positive types
-- relate a SPLIT TREE to a term by mirroring `reifySp`'s node dressing
-- (so `R`-⟹-reify is almost definitional), with the ⊗ leaves carrying
-- COMPONENT relations. The ⊸ case is Kripke: related arguments to
-- related results, over world extension.
--
--   R ι  v t   — the atom split-tree splices to t (base: emit ≈c t)
--   R I  v t   — the unit split-tree splices to t
--   R A⊗B v t  — the pair split-tree splices to t, EACH pair leaf's
--                components R-related (this is what lets the fund.
--                lemma apply a ⊗-extracted function at ⊸-type)
--   R A⊸B f t  — ∀ related (w,s), (f w) represents the application
--                evc ∘ ((t ⊗ s) ∘ mult)
--
-- Plus `R-resp` (R respects `≈c` on the term side) — the transport
-- the ⊸ and vmap lemmas need.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq12 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; ƛrc; evc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ⊗c-cong )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; AtCore; Val )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ )

------------------------------------------------------------------------
-- The relation.
------------------------------------------------------------------------

mutual
  R : ∀ A {Γ} → Val A Γ → CTm ⟪ Γ ⟫ A → Set
  R ι₁      v t = RAt v t
  R ι₂      v t = RAt v t
  R I       v t = RI v t
  R (A ⊗ B) v t = R⊗ A B v t
  R (A ⊸ B) {Γ} f t =
    ∀ {Δ} (w : Val A Δ) (s : CTm ⟪ Δ ⟫ A) →
    R A w s → R B (f Δ w) (evc ∘c ((t ⊗c s) ∘c mult Γ Δ))

  RAt : ∀ {A Γ} → Sp (AtCore A) Γ → CTm ⟪ Γ ⟫ A → Set
  RAt (ret (Γ₀ , (ρ₀ , m))) t = (m ∘c permC ρ₀) ≈c t
  RAt (spl {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
    Σ _ (λ t' → Σ (RAt k t')
      (λ _ → t ≈c (t' ∘c (αrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))
  RAt (usI {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
    Σ _ (λ t' → Σ (RAt k t')
      (λ _ → t ≈c (t' ∘c (ƛrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))

  RI : ∀ {Γ} → Sp (λ Δ → Δ ≡ ε) Γ → CTm ⟪ Γ ⟫ I → Set
  RI (ret refl) t = idc ≈c t
  RI (spl {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
    Σ _ (λ t' → Σ (RI k t')
      (λ _ → t ≈c (t' ∘c (αrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))
  RI (usI {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
    Σ _ (λ t' → Σ (RI k t')
      (λ _ → t ≈c (t' ∘c (ƛrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))

  R⊗ : ∀ A B {Γ} → Val (A ⊗ B) Γ → CTm ⟪ Γ ⟫ (A ⊗ B) → Set
  R⊗ A B (ret (Δ₁ , (Δ₂ , (ρ , (va , vb))))) t =
    Σ _ (λ ta → Σ _ (λ tb →
      Σ (R A va ta) (λ _ → Σ (R B vb tb)
        (λ _ → t ≈c ((ta ⊗c tb) ∘c (mult Δ₁ Δ₂ ∘c permC ρ))))))
  R⊗ A B (spl {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
    Σ _ (λ t' → Σ (R⊗ A B k t')
      (λ _ → t ≈c (t' ∘c (αrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))
  R⊗ A B (usI {Γ₁ = Γ₁} {Γ₂} ρ n k) t =
    Σ _ (λ t' → Σ (R⊗ A B k t')
      (λ _ → t ≈c (t' ∘c (ƛrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ))))))

------------------------------------------------------------------------
-- R respects ≈c on the term side.
------------------------------------------------------------------------

mutual
  R-resp : ∀ A {Γ} {v : Val A Γ} {t t'} → R A v t → t ≈c t' → R A v t'
  R-resp ι₁      = RAt-resp
  R-resp ι₂      = RAt-resp
  R-resp I       = RI-resp
  R-resp (A ⊗ B) = R⊗-resp
  R-resp (A ⊸ B) {v = f} rf e =
    λ w s rws → R-resp B (rf w s rws)
                        (∘c-congʳ (∘c-congˡ (⊗c-cong e ≈crefl)))

  RAt-resp : ∀ {A Γ} {v : Sp (AtCore A) Γ} {t t'} →
             RAt v t → t ≈c t' → RAt v t'
  RAt-resp {v = ret (_ , (_ , _))} r e = ≈ctrans r e
  RAt-resp {v = spl _ _ _} (w , (rk , e0)) e = w , (rk , ≈ctrans (≈csym e) e0)
  RAt-resp {v = usI _ _ _} (w , (rk , e0)) e = w , (rk , ≈ctrans (≈csym e) e0)

  RI-resp : ∀ {Γ} {v : Sp (λ Δ → Δ ≡ ε) Γ} {t t'} →
            RI v t → t ≈c t' → RI v t'
  RI-resp {v = ret refl} r e = ≈ctrans r e
  RI-resp {v = spl _ _ _} (w , (rk , e0)) e = w , (rk , ≈ctrans (≈csym e) e0)
  RI-resp {v = usI _ _ _} (w , (rk , e0)) e = w , (rk , ≈ctrans (≈csym e) e0)

  R⊗-resp : ∀ {A B Γ} {v : Val (A ⊗ B) Γ} {t t'} →
            R⊗ A B v t → t ≈c t' → R⊗ A B v t'
  R⊗-resp {v = ret (_ , (_ , (_ , (_ , _))))} (ta , (tb , (ra , (rb , e0)))) e =
    ta , (tb , (ra , (rb , ≈ctrans (≈csym e) e0)))
  R⊗-resp {v = spl _ _ _} (w , (rk , e0)) e = w , (rk , ≈ctrans (≈csym e) e0)
  R⊗-resp {v = usI _ _ _} (w , (rk , e0)) e = w , (rk , ≈ctrans (≈csym e) e0)
