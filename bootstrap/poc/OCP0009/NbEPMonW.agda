------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L3.1a — REALIZING THE WORLDS
--
-- The linear-NbE model (plan §10) computes over list worlds (`Ctx`,
-- stage L3.0); its OUTPUT must be syntax (`CTm`). This module is the
-- two-way bridge:
--
--   * `⟪_⟫`               — a world as a right-nested tensor type
--   * `swapHeadC`/`insC`/`permC` — world maps realized as structural
--     morphisms (the stage-2 realization, ported to `CTy` elements —
--     the recipes are verbatim `NbEPMonP`)
--   * `mult`/`multInv`    — the Day-tensor mediators
--       ⟪Γ ++ Δ⟫ ⇄ ⟪Γ⟫ ⊗ ⟪Δ⟫   (list-append vs. tensor, by fold)
--   * `ctxOf`/`splitTm`/`joinTm` — GENERIC DECOMPOSITION of a type
--     into its resource world: ⊗ flattens, I vanishes, ⊸ stays atomic.
--     This is what makes reflection type-directed (derivation
--     discovery #1): the model never has to reflect a ⊗- or I-typed
--     VARIABLE, because sources are pre-split into atoms-and-arrows.
--
-- Everything here is structural syntax; no model, no theorems beyond
-- well-typedness. L3.1b builds `Val`/`eval`/`reflect`/`reify` on top.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonW where

open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Ins; here; there; Perm; pnil; pcons )

------------------------------------------------------------------------
-- Worlds as types.
------------------------------------------------------------------------

⟪_⟫ : Ctx → CTy
⟪ ε ⟫     = I
⟪ A ∷ Γ ⟫ = A ⊗ ⟪ Γ ⟫

------------------------------------------------------------------------
-- World maps as structural morphisms (the stage-2 realization, ported).
------------------------------------------------------------------------

swapHeadC : ∀ {x y R} → CTm (x ⊗ (y ⊗ R)) (y ⊗ (x ⊗ R))
swapHeadC = αrc ∘c ((σc ⊗c idc) ∘c αlc)

insC : ∀ {x xs ys} → Ins x xs ys → CTm (x ⊗ ⟪ xs ⟫) ⟪ ys ⟫
insC here      = idc
insC (there i) = (idc ⊗c insC i) ∘c swapHeadC

permC : ∀ {xs ys} → Perm xs ys → CTm ⟪ xs ⟫ ⟪ ys ⟫
permC pnil        = idc
permC (pcons p i) = insC i ∘c (idc ⊗c permC p)

------------------------------------------------------------------------
-- The Day-tensor mediators: append vs. tensor.
------------------------------------------------------------------------

mult : ∀ Γ Δ → CTm ⟪ Γ ++ Δ ⟫ (⟪ Γ ⟫ ⊗ ⟪ Δ ⟫)
mult ε       Δ = ƛlc
mult (A ∷ Γ) Δ = αlc ∘c (idc ⊗c mult Γ Δ)

multInv : ∀ Γ Δ → CTm (⟪ Γ ⟫ ⊗ ⟪ Δ ⟫) ⟪ Γ ++ Δ ⟫
multInv ε       Δ = ƛrc
multInv (A ∷ Γ) Δ = (idc ⊗c multInv Γ Δ) ∘c αrc

------------------------------------------------------------------------
-- Generic decomposition: a type as its resource world. ⊗ flattens,
-- I vanishes, ⊸ is an atomic resource.
------------------------------------------------------------------------

ctxOf : CTy → Ctx
ctxOf ι₁      = ι₁ ∷ ε
ctxOf ι₂      = ι₂ ∷ ε
ctxOf I       = ε
ctxOf (A ⊗ B) = ctxOf A ++ ctxOf B
ctxOf (A ⊸ B) = (A ⊸ B) ∷ ε

splitTm : ∀ A → CTm A ⟪ ctxOf A ⟫
splitTm ι₁      = ρlc
splitTm ι₂      = ρlc
splitTm I       = idc
splitTm (A ⊗ B) = multInv (ctxOf A) (ctxOf B) ∘c (splitTm A ⊗c splitTm B)
splitTm (A ⊸ B) = ρlc

joinTm : ∀ A → CTm ⟪ ctxOf A ⟫ A
joinTm ι₁      = ρrc
joinTm ι₂      = ρrc
joinTm I       = idc
joinTm (A ⊗ B) = (joinTm A ⊗c joinTm B) ∘c mult (ctxOf A) (ctxOf B)
joinTm (A ⊸ B) = ρrc
