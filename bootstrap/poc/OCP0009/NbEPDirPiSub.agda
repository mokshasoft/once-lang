------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 12d — the op-lift, and `Π⁺` stability (a finding)
--
-- The Cat→Cat substitution machinery for `Π⁺`, and an honest finding about
-- its stability.
--
--   * `_↑⁻_`    — the OP-lift `σ ↑⁻ A : (Δ ▷⁻ A[σ]⁻) ⇒ (Γ ▷⁻ A)` reindexing the
--                 op-Grothendieck (the `Π⁺` analogue of `NbEPDirStab._↑_`);
--   * `Π⁺-restr` — the RESTRICTION MAP `(Π⁺ 𝒞 A B)[σ] ⇛ Π⁺ 𝒟 (A[σ]⁻)(B[σ↑⁻])`
--                 (via a substitution `σ` that is a functor `⌊𝒟⌋ → ⌊𝒞⌋`): a
--                 `𝒞`-future-cone at `σ x` RESTRICTS to a `𝒟`-cone at `x` by
--                 `h' ↦ σ.homₛ h'`.
--
-- THE FINDING: `Π⁺` is NOT STRICTLY stable — `(Π⁺ 𝒞 A B)[σ]` and
-- `Π⁺ 𝒟 (A[σ])(B[σ↑⁻])` are NOT `≡₁`. The future-cone fibre indexes over the
-- BASE CATEGORY's morphisms (`h : x ⇒ y` in `𝒞` vs `𝒟`); under a Cat→Cat
-- substitution the index SET changes, so the two cone-types differ (the
-- `𝒞`-cone carries more data than the `𝒟`-cone unless `σ` is full). This is
-- the well-known reason Kan-extension `Π` is only PSEUDO-stable — strict CwF
-- models need Hofmann strictification (or the pointwise `Π`, which is not a
-- functor here). What DOES hold is the canonical restriction map `Π⁺-restr`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirPiSub where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; Σ; _,_ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Cat; ⌊_⌋; Ty⁺; Ty⁻; Sub; _[_]⁻; _[_]⁺ )
open import poc.OCP0009.NbEPDirSig using ( Σ≡; uip )
open import poc.OCP0009.NbEPDirPiG using ( _▷⁻_; Πfib )

------------------------------------------------------------------------
-- The op-lift.
------------------------------------------------------------------------

_↑⁻_ : ∀ {Δ Γ} (σ : Sub Δ Γ) (A : Ty⁻ Γ) → Sub (Δ ▷⁻ (A [ σ ]⁻)) (Γ ▷⁻ A)
σ ↑⁻ A = record
  { obₛ   = λ p → (Sub.obₛ σ (fst p) , snd p)
  ; homₛ  = λ m → (Sub.homₛ σ (fst m) , snd m)
  ; homid = Σ≡ (Sub.homid σ) (uip _ _)
  ; hom⨾  = λ f g → Σ≡ (Sub.hom⨾ σ (fst f) (fst g)) (uip _ _) }

------------------------------------------------------------------------
-- The restriction of cones: a `𝒞`-future-cone at `σ x` RESTRICTS to a
-- `𝒟`-cone at `x`, by whiskering with `σ`. The `coh` (wedge) is rebuilt from
-- the source cone's `coh` + `σ`'s functoriality (`hom⨾`). This is the fibre
-- component of the canonical stability map — the direction that DOES exist.
------------------------------------------------------------------------

module _ {Δ Γ : Ctx} (σ : Sub Δ Γ) (A : Ty⁻ Γ) (B : Ty⁺ (Γ ▷⁻ A)) where
  private module σ = Sub σ

  restrict : ∀ {x} → Πfib A B (σ.obₛ x) → Πfib (A [ σ ]⁻) (B [ σ ↑⁻ A ]⁺) x
  restrict G = record
    { ap  = λ y' h' a' → Πfib.ap G (σ.obₛ y') (σ.homₛ h') a'
    ; coh = λ y' z' h' k' a' →
        trans (Πfib.coh G (σ.obₛ y') (σ.obₛ z') (σ.homₛ h') (σ.homₛ k') a')
              (cong (λ m → Πfib.ap G (σ.obₛ z') m a') (sym (σ.hom⨾ h' k'))) }
