------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 13d — a FULLY-VARIANT universe
--
-- `NbEPDirUnivS`'s small universe was DISCRETE — `disc` trivialised the
-- directed structure. A fully-variant universe has codes that decode to
-- GENUINELY directed types: whose functor action is non-trivial. The key
-- base code is the REPRESENTABLE `Yo⁺ 𝒞 a` (the directed identity `Hom(a,-)`),
-- whose action is POST-COMPOSITION `h ↦ h ⨾ g` — real variance, not `id`.
--
--   * `Code 𝒞`     — small codes over a base category: `⊤`/`⊥`, the
--                    representable `` `Yo a ``, and `×`/`+`;
--   * `El`         — decodes to a `Ty⁺ ⌊𝒞⌋`, `` `Yo a ↦ Yo⁺ 𝒞 a `` (variant);
--   * `𝒰`          — the universe (`fam _ = Code 𝒞`, still discrete CODES, but
--                    what they NAME is variant), a genuine `Ty⁺`;
--   * `Yo-variant` — the witness that a decoded representable ACTS by
--                    post-composition (its action is not the identity).
--
-- So the universe is small (codes : `Set`) yet its inhabitants are directed
-- types with real variance — the honest "variant" object the discrete one
-- was not. (Dependent `Σ`/`Π` codes over this remain the deeper extension.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirUnivV where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirCwF  using ( Ctx; Cat; ⌊_⌋; Ty⁺ )
open import poc.OCP0009.NbEPDirTy   using ( _×⁺_; _+⁺_ )
open import poc.OCP0009.NbEPDirUniv using ( ⊤⁺; ⊥⁺ )
open import poc.OCP0009.NbEPDirCwFJ using ( Yo⁺ )

------------------------------------------------------------------------
-- Variant codes over a base category, and their decoding.
------------------------------------------------------------------------

data Code (𝒞 : Cat) : Set where
  `⊤ `⊥   : Code 𝒞
  `Yo     : Cat.Ob 𝒞 → Code 𝒞
  _`×_ _`+_ : Code 𝒞 → Code 𝒞 → Code 𝒞

El : ∀ {𝒞} → Code 𝒞 → Ty⁺ ⌊ 𝒞 ⌋
El {𝒞} `⊤       = ⊤⁺
El {𝒞} `⊥       = ⊥⁺
El {𝒞} (`Yo a)  = Yo⁺ 𝒞 a
El     (c `× d) = El c ×⁺ El d
El     (c `+ d) = El c +⁺ El d

------------------------------------------------------------------------
-- The universe (discrete codes, variant decodings), and the variance witness.
------------------------------------------------------------------------

𝒰 : ∀ {𝒞} → Ty⁺ ⌊ 𝒞 ⌋
𝒰 {𝒞} = record { fam = λ _ → Code 𝒞 ; act = λ _ c → c
               ; actid = λ _ → refl ; act⨾ = λ _ _ _ → refl }

-- A decoded representable acts by POST-COMPOSITION — genuine variance, unlike
-- the discrete universe's identity action.
module _ (𝒞 : Cat) where
  open Cat 𝒞

  Yo-variant : ∀ (a : Ob) {x y : Ob} (g : x ⇒ y) (h : a ⇒ x) →
               Ty⁺.act (El {𝒞} (`Yo a)) g h ≡ (h ⨾ g)
  Yo-variant a g h = refl
