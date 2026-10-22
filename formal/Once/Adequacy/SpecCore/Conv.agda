{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Conv — coercions mean related conversions (plan
-- 0.121 §3.5).
--
-- A subtyping derivation means a conversion on both sides, defined clause for
-- clause alike (`⟦_⟧<:ᵛ` and `conv`), except at a type variable: the compiler
-- converts the instance along its own reflexive derivation (`<:-refl`), the
-- Spec does nothing. That reflexive conversion relates as the identity
-- (`refl-R`), and a pure stream embedded into an acting one is the Spec's
-- `subν` (`embν-R`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Internal.Contract using (ISig)
import Once.Internal.Core.PolyTy as LP
open import Once.Spec.Signature using (Signature)

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Conv {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature) where


open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Word using (Carrier)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Grade as LG
import Once.Internal.Type.Sub as LS
import Once.Spec.Sub as LS
import Once.Spec.Type as ST
import Once.Spec.Grade as SG
import Once.Spec.Sub as SSub
import Once.Internal.Graded as LGr
import Once.Internal.GradedOps as LOps
import Once.Internal.Trace as LTr
import Once.Internal.Iterative as LI
import Once.Internal.Stream as LSt
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
import Once.Internal.Polynomial as LPoly
import Once.Spec.Polynomial as SPoly
open import Once.Internal.FunctorMeaning using (translateF)
import Once.Internal.Core.PolyTyping S as PT
import Once.Internal.Core.PolySub as PS
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open T∞R
open νpR
open νdR
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Type using (⊑π-S; ⊑φ-S)
open import Once.Adequacy.SpecCore.Schema using (ptyS)

------------------------------------------------------------------------
-- A map on the compiler's side only
------------------------------------------------------------------------

module _ {X X′ Y : Set} {R : X → X′ → Set} {S′ : Y → X′ → Set} {h : X → Y}
         (hh : ∀ {x x′} → R x x′ → S′ (h x) x′) where

  mapTˡ-R : ∀ {m m′} → TR R m m′ → TR S′ (LTr.fmapT h m) m′
  mapTˡ-R (ret r)      = ret (hh r)
  mapTˡ-R (call c a k) = call c a (λ b → mapTˡ-R (k b))
  mapTˡ-R (halt x a)   = halt x a

  map∞ˡ-R : ∀ {m m′} → T∞R R m m′ → T∞R S′ (LI.fmap∞ h m) m′
  mapBˡ-R : ∀ {b b′} → TR (SumR R (T∞R R)) b b′
          → TR (SumR S′ (T∞R S′)) (LI.bindBlock b (λ x → LI.return∞ (h x))) b′
  force∞ (map∞ˡ-R r) = mapBˡ-R (force∞ r)
  mapBˡ-R (ret (left r))  = ret (left (hh r))
  mapBˡ-R (ret (right r)) = ret (right (map∞ˡ-R r))
  mapBˡ-R (call c a k)    = call c a (λ b → mapBˡ-R (k b))
  mapBˡ-R (halt x a)      = halt x a

  fmapˡ-R : ∀ {π π′} (p : PR π π′) {m m′} → MR p R m m′ → MR p S′ (LOps.fmapM π h m) m′
  fmapˡ-R pr-pure r = hh r
  fmapˡ-R pr-act  r = mapTˡ-R r
  fmapˡ-R pr-eff  r = map∞ˡ-R r

------------------------------------------------------------------------
-- A pure stream, embedded
------------------------------------------------------------------------

module _ {F₀ F₀′} (f₀ : GF F₀ F₀′) where

  private
    H  = translateF Carrier Carrier F₀
    G′ = SD.code F₀′
    c′ : SE.νM SG.pureᶠ G′ → SE.T (SPoly.⟦ G′ ⟧SF (SE.νM SG.pureᶠ G′))
    c′ u = SE.returnT (SE.νM.outν u)

  embν-R : ∀ {v w} → νpR f₀ v w → νdR f₀ (LOps.embνᵃ v) (SE.anaA G′ c′ w)
  embL-R : ∀ {F F′} (f : GF F F′) {l l′}
         → LayerR f (νpR f₀) l l′
         → LayerR f (νdR f₀) (LOps.mapEmbνᵃ H (translateF Carrier Carrier F) l) (SE.mapA G′ (SD.code F′) c′ l′)
  forceᵈR (embν-R r) = ret (embL-R f₀ (forceᵖR r))
  embL-R (g-K a)   r = r
  embL-R g-Id      r = embν-R r
  embL-R (g-⊕ f g) {inj₁ _} {inj₁ _} r = embL-R f r
  embL-R (g-⊕ f g) {inj₂ _} {inj₂ _} r = embL-R g r
  embL-R (g-⊗ f g) {_ , _} {_ , _} (r , r′) = embL-R f r , embL-R g r′

------------------------------------------------------------------------
-- The compiler's reflexive conversion relates as the identity
------------------------------------------------------------------------

private
  subM-refl-R : ∀ {π π′} (p : PR π π′) {X X′ : Set} {R : X → X′ → Set} {m m′}
              → MR p R m m′ → MR p R (LGr.subM (LS.⊑π-refl π) m) m′
  subM-refl-R pr-pure r = r
  subM-refl-R pr-act  r = r
  subM-refl-R pr-eff  r = r

refl-R : ∀ {X X′} (g : GR X X′) {x x′} → ValR g x x′ → ValR g (LOps.⟦ LS.<:-refl X ⟧<:ᵛ x) x′
refl-R g-unit r = r
refl-R g-void {()} r
refl-R g-int r = r
refl-R g-float r = r
refl-R (g-* a b) {_ , _} {_ , _} (r , r′) = refl-R a r , refl-R b r′
refl-R (g-+ a b) {inj₁ _} {inj₁ _} r = refl-R a r
refl-R (g-+ a b) {inj₂ _} {inj₂ _} r = refl-R b r
refl-R (g-+ a b) {inj₁ _} {inj₂ _} ()
refl-R (g-+ a b) {inj₂ _} {inj₁ _} ()
refl-R (g-⇒ {q = LG.Zero} {π} a b) r = subM-refl-R (pr π) (fmapˡ-R (refl-R b) (pr π) r)
refl-R (g-⇒ {q = LG.One}  {π} a b) r = λ rx → subM-refl-R (pr π) (fmapˡ-R (refl-R b) (pr π) (r (refl-R a rx)))
refl-R (g-⇒ {q = LG.Many} {π} a b) r = λ rx → subM-refl-R (pr π) (fmapˡ-R (refl-R b) (pr π) (r (refl-R a rx)))
refl-R (g-μ f) r = r
refl-R (g-ν {φ = LG.pureᶠ} f) r = r
refl-R (g-ν {φ = LG.actᶠ}  f) r = r
refl-R g-rigid {()} r

------------------------------------------------------------------------
-- A coercion, on both sides
------------------------------------------------------------------------

open import Once.Adequacy.SpecCore.Poly using (module SubS)
open SubS S using (subS)

conv-R : ∀ {m} {A B : LP.Ty m} (p : A PS.<:ₚ B) {σ σ′} (g : InstG σ σ′) {x x′}
       → ValR (GR-inst (ptr A) g) x x′
       → ValR (GR-inst (ptr B) g) (LOps.⟦ PS.<:ₚ-⟪⟫ σ p ⟧<:ᵛ x) (SD.conv σ′ (subS p) x′)
conv-R {A = LP.var i} PS.sub-var g r = refl-R (g i) r
conv-R PS.sub-void g {()} r
conv-R PS.sub-unit g r = r
conv-R PS.sub-int g r = r
conv-R PS.sub-float g r = r
conv-R PS.sub-rigid g r = tt
conv-R (PS.sub-arr {q = LG.Zero} {π} {π′} a b x) g r =
  sub-R x (⊑π-S x) (pr π) (pr π′) (fmap-R (pr π) r (conv-R b g))
conv-R (PS.sub-arr {q = LG.One} {π} {π′} a b x) g r =
  λ rx → sub-R x (⊑π-S x) (pr π) (pr π′) (fmap-R (pr π) (r (conv-R a g rx)) (conv-R b g))
conv-R (PS.sub-arr {q = LG.Many} {π} {π′} a b x) g r =
  λ rx → sub-R x (⊑π-S x) (pr π) (pr π′) (fmap-R (pr π) (r (conv-R a g rx)) (conv-R b g))
conv-R (PS.sub-prod a b) g {_ , _} {_ , _} (r , r′) = conv-R a g r , conv-R b g r′
conv-R (PS.sub-sum a b) g {inj₁ _} {inj₁ _} r = conv-R a g r
conv-R (PS.sub-sum a b) g {inj₂ _} {inj₂ _} r = conv-R b g r
conv-R (PS.sub-sum a b) g {inj₁ _} {inj₂ _} ()
conv-R (PS.sub-sum a b) g {inj₂ _} {inj₁ _} ()
conv-R PS.sub-μ g r = r
conv-R (PS.sub-ν {f = LG.pureᶠ} {LG.pureᶠ} x) g r = r
conv-R (PS.sub-ν {f = LG.actᶠ}  {LG.actᶠ}  x) g r = r
conv-R (PS.sub-ν {F = F} {φ = LG.pureᶠ} {LG.actᶠ} x) g r = embν-R (GF-inst (pfr F) g) r
conv-R (PS.sub-ν {f = LG.actᶠ} {LG.pureᶠ} ()) g r
