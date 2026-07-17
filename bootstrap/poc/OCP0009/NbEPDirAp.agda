------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 14 — `ap` and `transport` for the directed Id
--
-- The standard `transport`/`ap` vocabulary, DERIVED for the directed identity
-- type. In the directed CwF a path `a ⇒ b` is a morphism (a `Hom`), and:
--
--   * `transp`  — directed TRANSPORT along a path IS the type's covariant
--                 action `P.act`; it computes: `transp idₒ = id` (`transp-id`)
--                 and `transp (f ⨾ g) = transp g ∘ transp f` (`transp-∘`);
--   * `apd`     — dependent `ap` of a TERM is its naturality: a section carried
--                 along a path lands on the section at the other end;
--   * `apₛ`     — `ap` of a FUNCTION (a substitution) IS its functor action on
--                 morphisms, with `apₛ-id`/`apₛ-∘` (it preserves `idₒ`/`⨾`);
--   * `transp≡Jᶜ` — transport is exactly the Yoneda eliminator `Jᶜ` of
--                 `NbEPDirCwFJ`, evaluated (`refl`) — closing the loop: directed
--                 `J` and directed transport are the same map.
--
-- All `refl`/one-liners: `transport`/`ap` are not new operations but NAMES for
-- the functorial structure the directed CwF already carries. No `sym` — every
-- one is covariant (`DirJ.no-sym`, at the CwF level).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirAp where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirCwF  using ( Ctx; Cat; ⌊_⌋; Ty⁺; Tm; Sub )
open import poc.OCP0009.NbEPDirCwFJ using ( Yo⁺; _⇛_; Jᶜ )

------------------------------------------------------------------------
-- Transport, and the dependent `ap` of a term — over a single context.
------------------------------------------------------------------------

module _ {Γ : Ctx} where
  open Ctx Γ

  -- Directed transport of a covariant motive along a path.
  transp : (P : Ty⁺ Γ) {a b : Ob} → a ⇒ b → Ty⁺.fam P a → Ty⁺.fam P b
  transp P f = Ty⁺.act P f

  transp-id : (P : Ty⁺ Γ) {a : Ob} (d : Ty⁺.fam P a) → transp P idₒ d ≡ d
  transp-id P d = Ty⁺.actid P d

  transp-∘ : (P : Ty⁺ Γ) {a b c : Ob} (f : a ⇒ b) (g : b ⇒ c) (d : Ty⁺.fam P a) →
             transp P (f ⨾ g) d ≡ transp P g (transp P f d)
  transp-∘ P f g d = Ty⁺.act⨾ P f g d

  -- Dependent `ap` of a term = its naturality.
  apd : {P : Ty⁺ Γ} (t : Tm Γ P) {a b : Ob} (f : a ⇒ b) →
        transp P f (Tm.tm t a) ≡ Tm.tm t b
  apd t f = Tm.nat t f

------------------------------------------------------------------------
-- `ap` of a function (substitution) on paths = its action on morphisms.
------------------------------------------------------------------------

apₛ : ∀ {Δ Γ} (σ : Sub Δ Γ) {a b} →
      Ctx._⇒_ Δ a b → Ctx._⇒_ Γ (Sub.obₛ σ a) (Sub.obₛ σ b)
apₛ σ f = Sub.homₛ σ f

apₛ-id : ∀ {Δ Γ} (σ : Sub Δ Γ) {a} →
         apₛ σ (Ctx.idₒ Δ {a}) ≡ Ctx.idₒ Γ
apₛ-id σ = Sub.homid σ

apₛ-∘ : ∀ {Δ Γ} (σ : Sub Δ Γ) {a b c}
        (f : Ctx._⇒_ Δ a b) (g : Ctx._⇒_ Δ b c) →
        apₛ σ (Ctx._⨾_ Δ f g) ≡ Ctx._⨾_ Γ (apₛ σ f) (apₛ σ g)
apₛ-∘ σ f g = Sub.hom⨾ σ f g

------------------------------------------------------------------------
-- Transport IS the directed `J` (Yoneda) eliminator, evaluated.
------------------------------------------------------------------------

transp≡Jᶜ : (C : Cat) (a : Cat.Ob C) (P : Ty⁺ ⌊ C ⌋) (d : Ty⁺.fam P a)
            {b : Cat.Ob C} (f : Cat._⇒_ C a b) →
            transp P f d ≡ _⇛_.comp (Jᶜ C a P d) f
transp≡Jᶜ C a P d f = refl
