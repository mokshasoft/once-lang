------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A3a — SPLICE LEMMAS FOR THE SPLIT MONAD
--
-- The gluing relation (A4) compares Sp-trees through their SPLICES
-- (`reifySp`). This module gives the splice laws for the split-monad
-- combinators, over the canonical model's `Sp` (`NbEPMonF`):
--
--   * `bind-reify`/`map-reify` — the fold laws, at the LITERAL `≡`
--     level (bind and map do not touch nodes, so the splices agree
--     definitionally, node by node).
--   * `vmapSp-splice` — the world action splices as post-composition
--     with the realized permutation:
--       reifySp g (vmapSp pv ρ sp) ≈c reifySp g sp ∘c permC ρ
--     given payload compatibility. KEY: no induction — pending
--     permutations live ONLY in the top node (the L3.1b design), so
--     `⊙P-realC` + reassociation closes every case in five steps.
--   * `pvAt-compat`/`pvI-compat` — the payload-compatibility instances
--     for the atom and unit carriers.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq7 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; cong )
open import poc.OCP0009.NbEPMonL
  using ( CTy; I; _⊗_
        ; CTm; idc; _∘c_; _⊗c_; αrc; ƛrc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans
        ; cid-l; cid-r; c∘-assoc )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pnil; pcons; _⊙P_ )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; mapSp; bindSp; vmapSp; reifySp )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ )
open import poc.OCP0009.NbEPMonAdq2
  using ( ⊙P-realC )

------------------------------------------------------------------------
-- Fold laws (literal ≡ — bind/map never touch the nodes).
------------------------------------------------------------------------

bind-reify :
  ∀ {P Q : Ctx → Set} {T Γ}
    (g : ∀ {Δ} → Q Δ → CTm ⟪ Δ ⟫ T)
    (k : ∀ {Δ} → P Δ → Sp Q Δ) (sp : Sp P Γ) →
  reifySp g (bindSp sp k) ≡ reifySp (λ p → reifySp g (k p)) sp
bind-reify g k (ret p)      = refl
bind-reify g k (spl ρ n k') = cong (_∘c _) (bind-reify g k k')
bind-reify g k (usI ρ n k') = cong (_∘c _) (bind-reify g k k')

map-reify :
  ∀ {P Q : Ctx → Set} {T Γ}
    (g : ∀ {Δ} → Q Δ → CTm ⟪ Δ ⟫ T)
    (h : ∀ {Δ} → P Δ → Q Δ) (sp : Sp P Γ) →
  reifySp g (mapSp h sp) ≡ reifySp (λ p → g (h p)) sp
map-reify g h (ret p)      = refl
map-reify g h (spl ρ n k') = cong (_∘c _) (map-reify g h k')
map-reify g h (usI ρ n k') = cong (_∘c _) (map-reify g h k')

------------------------------------------------------------------------
-- The world action splices as post-composition.
------------------------------------------------------------------------

vmapSp-splice :
  ∀ {P : Ctx → Set} {T}
    (g : ∀ {Δ} → P Δ → CTm ⟪ Δ ⟫ T)
    (pv : ∀ {Δ' Δ} → Perm Δ' Δ → P Δ → P Δ') →
  (∀ {Δ' Δ} (ρ : Perm Δ' Δ) (p : P Δ) →
     g (pv ρ p) ≈c (g p ∘c permC ρ)) →
  ∀ {Γ' Γ} (ρ : Perm Γ' Γ) (sp : Sp P Γ) →
  reifySp g (vmapSp pv ρ sp) ≈c (reifySp g sp ∘c permC ρ)
vmapSp-splice g pv H ρ (ret p) = H ρ p
vmapSp-splice g pv H ρ (spl ρ₀ n k) =
  ≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (⊙P-realC ρ ρ₀)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
           (≈csym c∘-assoc))))
vmapSp-splice g pv H ρ (usI ρ₀ n k) =
  ≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (⊙P-realC ρ ρ₀)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
           (≈csym c∘-assoc))))

------------------------------------------------------------------------
-- Payload compatibility for the atom and unit carriers.
------------------------------------------------------------------------

-- The atom carrier: a core world, a pending permutation, a neutral.
AtP : CTy → Ctx → Set
AtP A Δ = Σ Ctx (λ Γ₀ → Σ (Perm Δ Γ₀) (λ _ → CTm ⟪ Γ₀ ⟫ A))

gAt : ∀ {A Δ} → AtP A Δ → CTm ⟪ Δ ⟫ A
gAt (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀

pvAt : ∀ {A Δ' Δ} → Perm Δ' Δ → AtP A Δ → AtP A Δ'
pvAt ρ (Γ₀ , (ρ₀ , n)) = Γ₀ , ((ρ ⊙P ρ₀) , n)

pvAt-compat : ∀ {A Δ' Δ} (ρ : Perm Δ' Δ) (p : AtP A Δ) →
              gAt {A} (pvAt ρ p) ≈c (gAt p ∘c permC ρ)
pvAt-compat ρ (Γ₀ , (ρ₀ , n)) =
  ≈ctrans (∘c-congʳ (⊙P-realC ρ ρ₀)) (≈csym c∘-assoc)

-- The unit carrier.
gI : ∀ {Δ} → Δ ≡ ε → CTm ⟪ Δ ⟫ I
gI refl = idc

pvI-compat : ∀ {Δ' Δ} (ρ : Perm Δ' Δ) (p : Δ ≡ ε) →
             ∀ (q : Δ' ≡ ε) → gI q ≈c (gI p ∘c permC ρ)
pvI-compat pnil refl refl = ≈csym cid-l
