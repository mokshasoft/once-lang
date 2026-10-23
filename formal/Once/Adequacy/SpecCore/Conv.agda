{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Conv — coercions mean related conversions (plan
-- 0.121 §3.5).
--
-- A subtyping derivation means a conversion on both sides (`conv`), the
-- instance's along the instantiated derivation (`<:-⟨⟩`), clause for clause
-- alike except at a type variable: the instance converts along the
-- reflexive derivation of the variable's type (`<:-refl`), the Spec does
-- nothing. That reflexive conversion relates as the identity (`refl-R`; at
-- an effectful arrow it is a map by the identity, related step for step),
-- and a pure stream embedded into an acting one is `subν` on both sides
-- (`embν-R`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Conv (Σ : Signature) {s : ℕ} (S : Defs s) where


open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Spec.Type as ST
import Once.Spec.Sub as SSub
open import Once.Metatheory.Types using (<:-refl; ⊑π-refl)
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
import Once.Spec.Polynomial as SPoly
open import Once.Spec.Core.Program Σ using (noVars)
import Once.Metatheory.TermModel.TySubst Σ S as TS
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open T∞R
open νpR
open νdR
open import Once.Adequacy.SpecCore.Monad Σ

------------------------------------------------------------------------
-- A map on the instance's side only
------------------------------------------------------------------------

module _ {X X′ Y : Set} {R : X → X′ → Set} {S′ : Y → X′ → Set} {h : X → Y}
         (hh : ∀ {x x′} → R x x′ → S′ (h x) x′) where

  mapTˡ-R : ∀ {m m′} → TR R m m′ → TR S′ (SE.mapT h m) m′
  mapTˡ-R (ret r)  = ret (hh r)
  mapTˡ-R (call k) = call (λ b → mapTˡ-R (k b))

  map∞ˡ-R : ∀ {m m′} → T∞R R m m′ → T∞R S′ (m SE.>>=∞ λ x → SE.return∞ (h x)) m′
  mapBˡ-R : ∀ {b b′} → TR (SumR R (T∞R R)) b b′
          → TR (SumR S′ (T∞R S′)) (SE.bindBlock b (λ x → SE.return∞ (h x))) b′
  force∞ (map∞ˡ-R r) = mapBˡ-R (force∞ r)
  mapBˡ-R (ret (left r))  = ret (left (hh r))
  mapBˡ-R (ret (right r)) = ret (right (map∞ˡ-R r))
  mapBˡ-R (call k)        = call (λ b → mapBˡ-R (k b))

  fmapˡ-R : ∀ {π π′} (p : PR π π′) {m m′} → MR p R m m′ → MR p S′ (SE.fmap π h m) m′
  fmapˡ-R pr-pure r = hh r
  fmapˡ-R pr-act  r = mapTˡ-R r
  fmapˡ-R pr-eff  r = map∞ˡ-R r

------------------------------------------------------------------------
-- A pure stream, embedded into an acting one
------------------------------------------------------------------------

module _ {F₀ F₀′} (f₀ : GF F₀ F₀′) where

  private
    G  = SD.code F₀
    G′ = SD.code F₀′
    c : SE.νM SG.pureᶠ G → SE.T (SPoly.⟦ G ⟧SF (SE.νM SG.pureᶠ G))
    c u = SE.returnT (SE.νM.outν u)
    c′ : SE.νM SG.pureᶠ G′ → SE.T (SPoly.⟦ G′ ⟧SF (SE.νM SG.pureᶠ G′))
    c′ u = SE.returnT (SE.νM.outν u)

  embν-R : ∀ {v w} → νpR f₀ v w → νdR f₀ (SE.anaA G c v) (SE.anaA G′ c′ w)
  embL-R : ∀ {F F′} (f : GF F F′) {l l′}
         → LayerR f (νpR f₀) l l′
         → LayerR f (νdR f₀) (SE.mapA G (SD.code F) c l) (SE.mapA G′ (SD.code F′) c′ l′)
  forceᵈR (embν-R r) = ret (embL-R f₀ (forceᵖR r))
  embL-R (g-K a)   r = r
  embL-R g-Id      r = embν-R r
  embL-R (g-⊕ f g) {inj₁ _} {inj₁ _} r = embL-R f r
  embL-R (g-⊕ f g) {inj₂ _} {inj₂ _} r = embL-R g r
  embL-R (g-⊗ f g) {_ , _} {_ , _} (r , r′) = embL-R f r , embL-R g r′

------------------------------------------------------------------------
-- The reflexive conversion, at a ground type read at no variable
------------------------------------------------------------------------

private
  subrefl-R : ∀ π {X X′ : Set} {R : X → X′ → Set} {m m′}
            → MR (pr π) R m m′ → MR (pr π) R (SE.sub (⊑π-refl π) m) m′
  subrefl-R LG.pure r = r
  subrefl-R LG.act  r = r
  subrefl-R LG.eff  r = r

refl-R : ∀ (X : ST.Type) {x x′} → ValR (g⟨⟩ noVars X) x x′ → ValR (g⟨⟩ noVars X) (SD.conv noVars (<:-refl X) x) x′
refl-R (ST.var ())
refl-R ST.Unit r = r
refl-R ST.Void {()} r
refl-R ST.Int r = r
refl-R ST.Float r = r
refl-R (A ST.* B) {_ , _} {_ , _} (r , r′) = refl-R A r , refl-R B r′
refl-R (A ST.+ B) {inj₁ _} {inj₁ _} r = refl-R A r
refl-R (A ST.+ B) {inj₂ _} {inj₂ _} r = refl-R B r
refl-R (A ST.+ B) {inj₁ _} {inj₂ _} ()
refl-R (A ST.+ B) {inj₂ _} {inj₁ _} ()
refl-R (A ST.⇒[ LG.mk-kind LG.Zero π ] B) r = subrefl-R π (fmapˡ-R (refl-R B) (pr π) r)
refl-R (A ST.⇒[ LG.mk-kind LG.One  π ] B) r = λ rx → subrefl-R π (fmapˡ-R (refl-R B) (pr π) (r (refl-R A rx)))
refl-R (A ST.⇒[ LG.mk-kind LG.Many π ] B) r = λ rx → subrefl-R π (fmapˡ-R (refl-R B) (pr π) (r (refl-R A rx)))
refl-R (ST.μ F) r = r
refl-R (ST.ν F LG.pureᶠ) r = r
refl-R (ST.ν F LG.actᶠ)  r = r

------------------------------------------------------------------------
-- The conversion
------------------------------------------------------------------------

conv-R : ∀ {m} (σ : ST.TySub m 0) {A B : ST.Ty m} (p : A SSub.<: B) {x x′}
       → ValR (g⟨⟩ noVars (A ST.⟨ σ ⟩)) x x′
       → ValR (g⟨⟩ noVars (B ST.⟨ σ ⟩)) (SD.conv noVars (TS.<:-⟨⟩ σ p) x) (SD.conv σ p x′)
conv-R σ (SSub.sub-var {i}) r = refl-R (σ i) r
conv-R σ SSub.sub-void {()} r
conv-R σ SSub.sub-unit r = r
conv-R σ SSub.sub-int r = r
conv-R σ SSub.sub-float r = r
conv-R σ (SSub.sub-arr {q = LG.Zero} {π} {π′} a b x) r =
  sub-R x x (pr π) (pr π′) (fmap-R (pr π) r (conv-R σ b))
conv-R σ (SSub.sub-arr {q = LG.One} {π} {π′} a b x) r =
  λ rx → sub-R x x (pr π) (pr π′) (fmap-R (pr π) (r (conv-R σ a rx)) (conv-R σ b))
conv-R σ (SSub.sub-arr {q = LG.Many} {π} {π′} a b x) r =
  λ rx → sub-R x x (pr π) (pr π′) (fmap-R (pr π) (r (conv-R σ a rx)) (conv-R σ b))
conv-R σ (SSub.sub-* a b) {_ , _} {_ , _} (r , r′) = conv-R σ a r , conv-R σ b r′
conv-R σ (SSub.sub-+ a b) {inj₁ _} {inj₁ _} r = conv-R σ a r
conv-R σ (SSub.sub-+ a b) {inj₂ _} {inj₂ _} r = conv-R σ b r
conv-R σ (SSub.sub-+ a b) {inj₁ _} {inj₂ _} ()
conv-R σ (SSub.sub-+ a b) {inj₂ _} {inj₁ _} ()
conv-R σ SSub.sub-μ r = r
conv-R σ (SSub.sub-ν {f = LG.pureᶠ} {LG.pureᶠ} SG.⊑-pure) r = r
conv-R σ (SSub.sub-ν {f = LG.actᶠ}  {LG.actᶠ}  SG.⊑-act) r = r
conv-R σ (SSub.sub-ν {F = F} {f = LG.pureᶠ} {LG.actᶠ} SG.⊑-pa) r = embν-R (gf⟨⟩ noVars (F ST.⟨ σ ⟩F)) r
conv-R σ (SSub.sub-ν {f = LG.actᶠ} {LG.pureᶠ} ()) r
