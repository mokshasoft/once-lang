------------------------------------------------------------------------
-- SPIKE — CAN A PARAMETER'S INTERPRETATION COME FROM THE INDEX'S
--         TYPING DERIVATION, VIA `fund`?
--
-- `icw-clo` carries `◇ ⊢ c ∷ U` and `elW` runs `fund` on it at the
-- EMPTY environment.  The question is whether the same move works at a
-- GENERAL semantic environment for a code that is a PROJECTION of the
-- index — which is what a parameter is.
--
--     Γ ⊢ i ∷ Σ' U X   ⇒   ⊩₀ (El (fst (subTm σ i)))   for Γ ⊩ˢ σ
--
-- ★ If this compiles, then `icw-par` can carry the index's typing
--   derivation exactly as `icw-clo` carries the code's, the layering
--   stays clean (a SYNTACTIC witness carried, the SEMANTIC interp
--   derived), and §10.1's *"`Θ ⊢ κ ∷ U` does not give one"* is seen to
--   be about the environment being a BARE `Sub` — not about the code.
------------------------------------------------------------------------

module tmp.ParWSpike where

open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; RTy; Sub; subTm; subTy; fst; El; U; Σ' )
open import DirectedHoTT.Spec.Typing using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢fst )
open import DirectedHoTT.Spec.Syntax using ( Var )
open import DirectedHoTT.Spec.Typing using ( crflᵀ )
open import DirectedHoTT.Metatheory.Injectivity using ( _⟶ᵀ*_; doneᵀ )
open import DirectedHoTT.Metatheory.LogicalRelation
  using ( ⊩₀_; ⊩₁_; ⊩₁U; sem-El; irrel₁ )
open import DirectedHoTT.Metatheory.Fundamental.Semantic using ( Rel; _⊩ˢ_ )
open import DirectedHoTT.Metatheory.Fundamental using ( fund )
open import normalizer.Syntax.Types using ( Σ; _,_ )

------------------------------------------------------------------------
-- ★★★ THE TEST.  Modelled on `elW` (`Fundamental:303`), but at a
--   GENERAL `ρ : Γ ⊩ˢ σ` rather than `⊩ˢ-ε`, and on `⊢fst di` rather
--   than a closed code.
------------------------------------------------------------------------

parW : {Γ : Ctx} {Ξ : Cx} {i : RTm ⌊ Γ ⌋} {X : RTy (⌊ Γ ⌋ Cx.∙)}
       {σ : Sub ⌊ Γ ⌋ Ξ} →
       Γ ⊢ i ∷ Σ' U X → (x₀ : Var Ξ) → Γ ⊩ˢ σ →
       ⊩₀ (El (fst (subTm σ i)))
parW {i = i} {σ = σ} di x₀ ρ =
  sem-El doneᵀ
    (projl (irrel₁ crflᵀ (dfst (fund (⊢fst di) x₀ ρ)) (⊩₁U doneᵀ))
           (fst (subTm σ i)) (dsnd (fund (⊢fst di) x₀ ρ)))
  where
    projl : {P Q : Set} → Σ P (λ _ → Q) → P
    projl (p , _) = p
    dfst  = λ {A : RTy _} {t : RTm _} (r : Rel A t) → Σ.fst r
    dsnd  = λ {A : RTy _} {t : RTm _} (r : Rel A t) → Σ.snd r
