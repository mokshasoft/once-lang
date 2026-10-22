{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Layer — one layer of a recursive type, as each side
-- represents it (plan 0.121 §3.5).
--
-- The compiler holds a layer three ways: as a value of the type `⟦F⟧T C`
-- (graded), as the functor applied to a set (`Val.⟦F⟧F`, a base constant a
-- plain value), and as its polynomial's layer (`translateF`, a base constant
-- in the functor-meaning representation); the Spec two (`⟦F⟧F C` and `code`).
-- A base value is the same in every representation, so each conversion — the
-- compiler's `cfᵛ`/`cf⁻¹ᵛ`, `coerce-μ-in`/`coerce-μ-out`, the Spec's
-- `toL`/`fromL` — keeps layers related.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecCore.Layer (Σ : Signature) where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Word using (Carrier)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Internal.Type.WellFormed as LW
import Once.Internal.Core.PolyTy as LP
import Once.Spec.Type as ST
import Once.Internal.Value Carrier Carrier as V
import Once.Internal.Graded as LGr
import Once.Internal.GradedOps as LOps
import Once.Spec.Polynomial as SPoly
import Once.Spec.Domain Σ as SD
open import Once.Internal.FunctorMeaning using (translateF; ⟦_,_⟧-base)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ

------------------------------------------------------------------------
-- Base values, in the compiler's plain representation
------------------------------------------------------------------------

BVal : ∀ {A A′} → GR A A′ → V.⟦ A ⟧ → SD.⟦ A′ ⟧ᵛ → Set
BVal g-unit  _ _ = ⊤
BVal g-void  _ _ = ⊤
BVal g-int   x y = x ≡ y
BVal g-float x y = x ≡ y
BVal (g-* a b) (x , x′) (y , y′) = BVal a x y × BVal b x′ y′
BVal (g-+ a b) (inj₁ x) (inj₁ y) = BVal a x y
BVal (g-+ a b) (inj₂ x) (inj₂ y) = BVal b x y
BVal (g-+ a b) (inj₁ _) (inj₂ _) = ⊥
BVal (g-+ a b) (inj₂ _) (inj₁ _) = ⊥
BVal (g-⇒ _ _) _ _ = ⊤
BVal (g-μ _)   _ _ = ⊤
BVal (g-ν _)   _ _ = ⊤
BVal g-rigid   _ _ = ⊤

prj-R : ∀ {A A′} (ib : LW.IsBaseType A) (g : GR A A′) {x x′} → ValR g x x′ → BVal g (LOps.prjB ib x) x′
prj-R LW.base-Unit  g-unit  r = tt
prj-R LW.base-Void  g-void  r = tt
prj-R LW.base-Int   g-int   r = r
prj-R LW.base-Float g-float r = r
prj-R (LW.base-Prod a b) (g-* ga gb) {_ , _} {_ , _} (r , r′) = prj-R a ga r , prj-R b gb r′
prj-R (LW.base-Sum a b) (g-+ ga gb) {inj₁ _} {inj₁ _} r = prj-R a ga r
prj-R (LW.base-Sum a b) (g-+ ga gb) {inj₂ _} {inj₂ _} r = prj-R b gb r
prj-R (LW.base-Sum a b) (g-+ ga gb) {inj₁ _} {inj₂ _} ()
prj-R (LW.base-Sum a b) (g-+ ga gb) {inj₂ _} {inj₁ _} ()

inj-R : ∀ {A A′} (ib : LW.IsBaseType A) (g : GR A A′) {x x′} → BVal g x x′ → ValR g (LOps.injB ib x) x′
inj-R LW.base-Unit  g-unit  r = tt
inj-R LW.base-Void  g-void  r = tt
inj-R LW.base-Int   g-int   r = r
inj-R LW.base-Float g-float r = r
inj-R (LW.base-Prod a b) (g-* ga gb) {_ , _} {_ , _} (r , r′) = inj-R a ga r , inj-R b gb r′
inj-R (LW.base-Sum a b) (g-+ ga gb) {inj₁ _} {inj₁ _} r = inj-R a ga r
inj-R (LW.base-Sum a b) (g-+ ga gb) {inj₂ _} {inj₂ _} r = inj-R b gb r
inj-R (LW.base-Sum a b) (g-+ ga gb) {inj₁ _} {inj₂ _} ()
inj-R (LW.base-Sum a b) (g-+ ga gb) {inj₂ _} {inj₁ _} ()

toBase-R : ∀ {A A′} (g : GR A A′) {x x′} → BVal g x x′ → BR g (V.coerce-full-to-base A x) x′
toBase-R g-unit  r = tt
toBase-R g-void  r = tt
toBase-R g-int   r = r
toBase-R g-float r = r
toBase-R (g-* a b) {_ , _} {_ , _} (r , r′) = toBase-R a r , toBase-R b r′
toBase-R (g-+ a b) {inj₁ _} {inj₁ _} r = toBase-R a r
toBase-R (g-+ a b) {inj₂ _} {inj₂ _} r = toBase-R b r
toBase-R (g-+ a b) {inj₁ _} {inj₂ _} ()
toBase-R (g-+ a b) {inj₂ _} {inj₁ _} ()
toBase-R (g-⇒ _ _) r = tt
toBase-R (g-μ _)   r = tt
toBase-R (g-ν _)   r = tt
toBase-R g-rigid {()} r

fromBase-R : ∀ {A A′} (ib : LW.IsBaseType A) (g : GR A A′) {x x′} → BR g x x′ → BVal g (V.coerce-base-to-full ib x) x′
fromBase-R LW.base-Unit  g-unit  r = tt
fromBase-R LW.base-Void  g-void  {()} r
fromBase-R LW.base-Int   g-int   r = r
fromBase-R LW.base-Float g-float r = r
fromBase-R (LW.base-Prod a b) (g-* ga gb) {_ , _} {_ , _} (r , r′) = fromBase-R a ga r , fromBase-R b gb r′
fromBase-R (LW.base-Sum a b) (g-+ ga gb) {inj₁ _} {inj₁ _} r = fromBase-R a ga r
fromBase-R (LW.base-Sum a b) (g-+ ga gb) {inj₂ _} {inj₂ _} r = fromBase-R b gb r
fromBase-R (LW.base-Sum a b) (g-+ ga gb) {inj₁ _} {inj₂ _} ()
fromBase-R (LW.base-Sum a b) (g-+ ga gb) {inj₂ _} {inj₁ _} ()

------------------------------------------------------------------------
-- A layer in the compiler's plain representation
------------------------------------------------------------------------

LayerV : ∀ {F F′} → GF F F′ → ∀ {X Y : Set} → (X → Y → Set) → V.⟦ F ⟧F X → SPoly.⟦ SD.code F′ ⟧SF Y → Set
LayerV (g-K a)   R x y = BVal a x y
LayerV g-Id      R x y = R x y
LayerV (g-⊕ f g) R (inj₁ x) (inj₁ y) = LayerV f R x y
LayerV (g-⊕ f g) R (inj₂ x) (inj₂ y) = LayerV g R x y
LayerV (g-⊕ f g) R (inj₁ _) (inj₂ _) = ⊥
LayerV (g-⊕ f g) R (inj₂ _) (inj₁ _) = ⊥
LayerV (g-⊗ f g) R (x , x′) (y , y′) = LayerV f R x y × LayerV g R x′ y′

-- into the polynomial's layer, and back
in-R : ∀ {F F′} (f : GF F F′) {X Y : Set} {R : X → Y → Set} {l l′}
     → LayerV f R l l′ → LayerR f R (V.coerce-μ-in F X l) l′
in-R (g-K a)   r = toBase-R a r
in-R g-Id      r = r
in-R (g-⊕ f g) {l = inj₁ _} {inj₁ _} r = in-R f r
in-R (g-⊕ f g) {l = inj₂ _} {inj₂ _} r = in-R g r
in-R (g-⊕ f g) {l = inj₁ _} {inj₂ _} ()
in-R (g-⊕ f g) {l = inj₂ _} {inj₁ _} ()
in-R (g-⊗ f g) {l = _ , _} {_ , _} (r , r′) = in-R f r , in-R g r′

out-R : ∀ {F F′} (f : GF F F′) (wf : LW.WellFormedF F) {X Y : Set} {R : X → Y → Set} {l l′}
      → LayerR f R l l′ → LayerV f R (V.coerce-μ-out wf X l) l′
out-R (g-K a)   (LW.wf-K ib)    r = fromBase-R ib a r
out-R g-Id      LW.wf-Id        r = r
out-R (g-⊕ f g) (LW.wf-Sum wf wg) {l = inj₁ _} {inj₁ _} r = out-R f wf r
out-R (g-⊕ f g) (LW.wf-Sum wf wg) {l = inj₂ _} {inj₂ _} r = out-R g wg r
out-R (g-⊕ f g) (LW.wf-Sum wf wg) {l = inj₁ _} {inj₂ _} ()
out-R (g-⊕ f g) (LW.wf-Sum wf wg) {l = inj₂ _} {inj₁ _} ()
out-R (g-⊗ f g) (LW.wf-Prod wf wg) {l = _ , _} {_ , _} (r , r′) = out-R f wf r , out-R g wg r′

------------------------------------------------------------------------
-- A layer as a value of the functor applied, on both sides
------------------------------------------------------------------------

module _ {m} {σ : LP.GSub m} {σ′ : ST.TySub m 0} (g : InstG σ σ′) where

  GR-⟦⟧ : ∀ {F : LP.Fun m} {F′} (f : PFR F F′) {Xg X′} → GR Xg (X′ ST.⟨ σ′ ⟩)
        → GR (LT.⟦ F LP.⟪ σ ⟫F ⟧T Xg) (ST.⟦ F′ ⟧F X′ ST.⟨ σ′ ⟩)
  GR-⟦⟧ (p-K a)   gX = GR-inst a g
  GR-⟦⟧ p-Id      gX = gX
  GR-⟦⟧ (p-⊕ f h) gX = g-+ (GR-⟦⟧ f gX) (GR-⟦⟧ h gX)
  GR-⟦⟧ (p-⊗ f h) gX = g-* (GR-⟦⟧ f gX) (GR-⟦⟧ h gX)

  cf-R : ∀ {F : LP.Fun m} {F′} (f : PFR F F′) (wf : LW.WellFormedF (F LP.⟪ σ ⟫F)) {Xg X′} (gX : GR Xg (X′ ST.⟨ σ′ ⟩))
         {x x′} → ValR (GR-⟦⟧ f gX) x x′ → LayerV (GF-inst f g) (ValR gX) (LOps.cfᵛ Xg wf x) (SD.toL σ′ F′ X′ x′)
  cf-R (p-K a)   (LW.wf-K ib) gX r = prj-R ib (GR-inst a g) r
  cf-R p-Id      LW.wf-Id     gX r = r
  cf-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₁ _} {inj₁ _} r = cf-R f wf gX r
  cf-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₂ _} {inj₂ _} r = cf-R h wh gX r
  cf-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₁ _} {inj₂ _} ()
  cf-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₂ _} {inj₁ _} ()
  cf-R (p-⊗ f h) (LW.wf-Prod wf wh) gX {_ , _} {_ , _} (r , r′) = cf-R f wf gX r , cf-R h wh gX r′

  cf⁻¹-R : ∀ {F : LP.Fun m} {F′} (f : PFR F F′) (wf : LW.WellFormedF (F LP.⟪ σ ⟫F)) {Xg X′} (gX : GR Xg (X′ ST.⟨ σ′ ⟩))
           {l l′} → LayerV (GF-inst f g) (ValR gX) l l′ → ValR (GR-⟦⟧ f gX) (LOps.cf⁻¹ᵛ Xg wf l) (SD.fromL σ′ F′ X′ l′)
  cf⁻¹-R (p-K a)   (LW.wf-K ib) gX r = inj-R ib (GR-inst a g) r
  cf⁻¹-R p-Id      LW.wf-Id     gX r = r
  cf⁻¹-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₁ _} {inj₁ _} r = cf⁻¹-R f wf gX r
  cf⁻¹-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₂ _} {inj₂ _} r = cf⁻¹-R h wh gX r
  cf⁻¹-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₁ _} {inj₂ _} ()
  cf⁻¹-R (p-⊕ f h) (LW.wf-Sum wf wh) gX {inj₂ _} {inj₁ _} ()
  cf⁻¹-R (p-⊗ f h) (LW.wf-Prod wf wh) gX {_ , _} {_ , _} (r , r′) = cf⁻¹-R f wf gX r , cf⁻¹-R h wh gX r′
