-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprTable — plan 0.146 B1.7 step 2c (D456, D457): the
-- program's table from its definitions' sources.
--
-- Each definition's body is its source's bridge (`FromExpr.Lq`) after the
-- context's unused slots are erased (`eraseL`, as `elaborateFull`'s
-- `eraseCtx`), in `Compile.directCallIR`'s shape; its label's grade is its
-- type's. This module builds the pieces and relates each to its IR.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)

module Once.LinCore.ExprTable (fmt : TargetNum) (ans : FFIAnswers) where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)

import Once.Spec.Grade as G
open import Once.Spec.Type using (Ty; Type; _⇒[_]_)
import Once.Spec.Type as ST
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_)
open import Once.Context using (⟦_⟧ᶜ; _↾_)
open import Once.IRTy using (⌊_⌋)
import Once.IR as M
open import Once.Surface.Elaborate using (eraseCtx)
open import Once.Denotation.DenotTrace using (CallEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)

open import Once.LinCore.Core fmt
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.FromExpr fmt using (ty; Co; apω; k-apω; cast; k-cast; gdB)
open import Once.LinCore.FromIR fmt using (grade)
open import Relation.Binary.PropositionalEquality using (cong; subst)
open import Once.LinCore.FromIR fmt using (⟪_⟫)
open import Once.LinCore.Bridge fmt ans using (W)
open import Once.LinCore.Bisim fmt ans using (_≈_; ≈-refl; ≈-trans; ≈-sym; ret≈R; ≈-≈R; ≈R-≈; >>=-congR; >>=-cong)
open import Once.LinCore.FromExprOk fmt ans using (Pure; PureI; bind-pure; ret-bind; module Rel)

------------------------------------------------------------------------
-- 1. ERASURE: the variables a usage leaves out, dropped (`eraseCtx`).
------------------------------------------------------------------------

module _ {L : Cx} {E : LTy} where

  eraseL : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → Tm L E ⟪ ⌊ ⟦ Γ ⟧ᶜ ⌋ ⟫ (Co Γ Ψ)
  eraseL SC.∅          []           = lid
  eraseL (Γ SC.▸ A) (G.Zero ∷ Ψ) = eraseL Γ Ψ ∘l (ρl ∘l (lid ⊗l drop))
  eraseL (Γ SC.▸ A) (G.One  ∷ Ψ) = eraseL Γ Ψ ⊗l lid
  eraseL (Γ SC.▸ A) (G.Many ∷ Ψ) = eraseL Γ Ψ ⊗l lid

  k-eraseL : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → Blk (eraseL Γ Ψ)
  k-eraseL SC.∅          []           = k-id
  k-eraseL (Γ SC.▸ A) (G.Zero ∷ Ψ) = k-∘ (k-eraseL Γ Ψ) (k-∘ k-ρ (k-⊗ k-id k-drop))
  k-eraseL (Γ SC.▸ A) (G.One  ∷ Ψ) = k-⊗ (k-eraseL Γ Ψ) k-id
  k-eraseL (Γ SC.▸ A) (G.Many ∷ Ψ) = k-⊗ (k-eraseL Γ Ψ) k-id

-- the erasure's value on each side
ev-er : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → ⟦ ⟪ ⌊ ⟦ Γ ⟧ᶜ ⌋ ⟫ ⟧ → ⟦ Co Γ Ψ ⟧
ev-er SC.∅          []           x       = x
ev-er (Γ SC.▸ A) (G.Zero ∷ Ψ) (x , a) = ev-er Γ Ψ x
ev-er (Γ SC.▸ A) (G.One  ∷ Ψ) (x , a) = ev-er Γ Ψ x , a
ev-er (Γ SC.▸ A) (G.Many ∷ Ψ) (x , a) = ev-er Γ Ψ x , a

rv-er : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → ⟦ ⌊ ⟦ Γ ⟧ᶜ ⌋ ⟧ᴰᴵ → ⟦ ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⟧ᴰᴵ
rv-er SC.∅          []           x = x
rv-er (Γ SC.▸ A) (G.Zero ∷ Ψ) x = rv-er Γ Ψ (proj₁ x)
rv-er (Γ SC.▸ A) (G.One  ∷ Ψ) x = rv-er Γ Ψ (proj₁ x) , proj₂ x
rv-er (Γ SC.▸ A) (G.Many ∷ Ψ) x = rv-er Γ Ψ (proj₁ x) , proj₂ x

er-W : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) {x x′} → W ⌊ ⟦ Γ ⟧ᶜ ⌋ x x′ → W ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ (ev-er Γ Ψ x) (rv-er Γ Ψ x′)
er-W SC.∅          []           w        = w
er-W (Γ SC.▸ A) (G.Zero ∷ Ψ) (w , _)  = er-W Γ Ψ w
er-W (Γ SC.▸ A) (G.One  ∷ Ψ) (w , wa) = er-W Γ Ψ w , wa
er-W (Γ SC.▸ A) (G.Many ∷ Ψ) (w , wa) = er-W Γ Ψ w , wa

module _ {L : Cx} (δ : Env L) where

  erase-pure : ∀ {E m n} (Γ : Ctx m n) (Ψ : Usage n) → Pure δ (eraseL {L} {E} Γ Ψ) (ev-er Γ Ψ)
  erase-pure SC.∅          []           e x       = ≈-refl
  erase-pure (Γ SC.▸ A) (G.Zero ∷ Ψ) e (x , a) =
    ≈-trans (bind-pure (bind-pure (≈-trans ret-bind ret-bind))) (erase-pure Γ Ψ e x)
  erase-pure (Γ SC.▸ A) (G.One  ∷ Ψ) e (x , a) = ≈-trans (bind-pure (erase-pure Γ Ψ e x)) ret-bind
  erase-pure (Γ SC.▸ A) (G.Many ∷ Ψ) e (x , a) = ≈-trans (bind-pure (erase-pure Γ Ψ e x)) ret-bind

module _ (ρ : CallEnv) (am : M.AllocMode) where

  eraseCtx-pure : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → PureI ρ (eraseCtx {Γ = Γ} am Ψ) (rv-er Γ Ψ)
  eraseCtx-pure SC.∅          []           x = ≈-refl
  eraseCtx-pure (Γ SC.▸ A) (G.Zero ∷ Ψ) x = ≈-trans ret-bind (eraseCtx-pure Γ Ψ (proj₁ x))
  eraseCtx-pure (Γ SC.▸ A) (G.One  ∷ Ψ) x =
    ≈-trans (bind-pure (≈-trans ret-bind (eraseCtx-pure Γ Ψ (proj₁ x)))) ret-bind
  eraseCtx-pure (Γ SC.▸ A) (G.Many ∷ Ψ) x =
    ≈-trans (bind-pure (≈-trans ret-bind (eraseCtx-pure Γ Ψ (proj₁ x)))) ret-bind

module Erase {L : Cx} (δ : Env L) (ρ : CallEnv) (am : M.AllocMode) where
  open Rel δ ρ

  -- ★ the erasure against `eraseCtx`
  rel-erase : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → Rel (eraseL Γ Ψ) (eraseCtx {Γ = Γ} am Ψ)
  rel-erase Γ Ψ = rel-pure {t = eraseL Γ Ψ} {t′ = eraseCtx {Γ = Γ} am Ψ}
                           (erase-pure δ {E = One} Γ Ψ) (eraseCtx-pure ρ am Γ Ψ) (er-W Γ Ψ)

------------------------------------------------------------------------
-- 2. A DEFINITION'S BODY, in `Compile.directCallIR`'s shape: an arrow's
-- closure applied to the argument, any other value on `tt`.
------------------------------------------------------------------------

dcDom dcCod : Type → Type
dcDom (A ⇒[ G.mk-kind G.Zero π ] B) = ST.Unit
dcDom (A ⇒[ G.mk-kind G.One π ] B)  = A
dcDom (A ⇒[ G.mk-kind G.Many π ] B) = A
dcDom ST.Unit = ST.Unit
dcDom ST.Void = ST.Unit
dcDom (X ST.* Y) = ST.Unit
dcDom (X ST.+ Y) = ST.Unit
dcDom (ST.μ F) = ST.Unit
dcDom (ST.ν F f) = ST.Unit
dcDom ST.Int = ST.Unit
dcDom ST.Float = ST.Unit
dcDom (ST.var ())
dcCod (A ⇒[ G.mk-kind q π ] B) = B
dcCod T@ST.Unit = T
dcCod T@ST.Void = T
dcCod T@(X ST.* Y) = T
dcCod T@(X ST.+ Y) = T
dcCod T@(ST.μ F) = T
dcCod T@(ST.ν F f) = T
dcCod T@ST.Int = T
dcCod T@ST.Float = T
dcCod (ST.var ())

-- the label's grade: the arrow's, a value's a block
dcGr : Type → Gr
dcGr (A ⇒[ G.mk-kind q π ] B) = grade π
dcGr ST.Unit = act
dcGr ST.Void = act
dcGr (X ST.* Y) = act
dcGr (X ST.+ Y) = act
dcGr (ST.μ F) = act
dcGr (ST.ν F f) = act
dcGr ST.Int = act
dcGr ST.Float = act
dcGr (ST.var ())

module _ {L : Cx} where

  dc : (T : Type) → LTm L One (ty T) → LTm L (ty (dcDom T)) (ty (dcCod T))
  dc (A ⇒[ G.mk-kind G.Zero π ] B) v = apω ∘l ((v ⊗l lid) ∘l lul⁻)
  dc (A ⇒[ G.mk-kind G.One π ] B)  v = apω ∘l ((v ⊗l lid) ∘l lul⁻)
  dc (A ⇒[ G.mk-kind G.Many π ] B) v = apω ∘l ((v ⊗l lid) ∘l lul⁻)
  dc ST.Unit v = v
  dc ST.Void v = v
  dc (X ST.* Y) v = v
  dc (X ST.+ Y) v = v
  dc (ST.μ F) v = v
  dc (ST.ν F f) v = v
  dc ST.Int v = v
  dc ST.Float v = v
  dc (ST.var ()) v

  -- a body's grade, when its blockness needs the grade to be finite
  gdT : ∀ {X Y} (π : G.Purity) (t : LTm L X Y) → (∀ {φ} → π ≡ G.fin φ → Blk t) → Gd (grade π) t
  gdT (G.fin φ) t h = h refl
  gdT G.eff     t h = tt

  -- the label's body: one-shot, over `One`, at its grade
  dcGd : ∀ (T : Type) {v : LTm L One (ty T)} → Blk v → Gd (dcGr T) (dc T v ∘l lul)
  dcGd (A ⇒[ G.mk-kind G.Zero π ] B) {v} β =
    gdT π (dc (A ⇒[ G.mk-kind G.Zero π ] B) v ∘l lul) (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ β k-id) k-lul⁻)) k-lul })
  dcGd (A ⇒[ G.mk-kind G.One π ] B) {v} β =
    gdT π (dc (A ⇒[ G.mk-kind G.One π ] B) v ∘l lul) (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ β k-id) k-lul⁻)) k-lul })
  dcGd (A ⇒[ G.mk-kind G.Many π ] B) {v} β =
    gdT π (dc (A ⇒[ G.mk-kind G.Many π ] B) v ∘l lul) (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ β k-id) k-lul⁻)) k-lul })
  dcGd T@ST.Unit      β = k-∘ β k-lul
  dcGd T@ST.Void      β = k-∘ β k-lul
  dcGd T@(_ ST.* _)   β = k-∘ β k-lul
  dcGd T@(_ ST.+ _)   β = k-∘ β k-lul
  dcGd T@(ST.μ _)     β = k-∘ β k-lul
  dcGd T@(ST.ν _ _)   β = k-∘ β k-lul
  dcGd T@ST.Int       β = k-∘ β k-lul
  dcGd T@ST.Float     β = k-∘ β k-lul
  dcGd T@(ST.var ())  β
