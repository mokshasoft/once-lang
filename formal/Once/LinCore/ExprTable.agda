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
import Data.Unit
import Data.Bool
open import Data.Product using (Σ)
open import Once.Compile using (directCallIR)

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
open import Once.LinCore.FromExprOk fmt ans using (Pure; PureI; bind-pure; ret-bind; module Rel; module Main)
open import Once.LinCore.FromExpr fmt using (Rs; Lq; Lq-blk)
open import Once.CompileSrc using (CompiledSrc; csName; csType; csSrc)
open import Once.IRTy using (_≟IRTy_)
open import Once.CanonicalName using (_≟ᶜ_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Once.CompileSrc using (Src; src; srcIR; expr; am)
open import Once.Denotation.SurfaceRefs using (Refs)
open import Once.Denotation.DenotTrace using (callEnv)
open import Once.Spec.Name using (CanonicalName)
open import Once.IRTy using (IRTy)

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

-- `directCallIR`, by the same cases, at the call types above
dcIR : (T : Type) → M.IR ⌊ ST.Unit {0} ⌋ ⌊ T ⌋ → M.IR ⌊ dcDom T ⌋ ⌊ dcCod T ⌋
dcIR (A ⇒[ G.mk-kind G.Zero π ] B) ir = M.apply M.∘ M.⟨ ir M.∘ M.terminal , M.id ⟩
dcIR (A ⇒[ G.mk-kind G.One π ] B)  ir = M.apply M.∘ M.⟨ ir M.∘ M.terminal , M.id ⟩
dcIR (A ⇒[ G.mk-kind G.Many π ] B) ir = M.apply M.∘ M.⟨ ir M.∘ M.terminal , M.id ⟩
dcIR ST.Unit ir = ir
dcIR ST.Void ir = ir
dcIR (X ST.* Y) ir = ir
dcIR (X ST.+ Y) ir = ir
dcIR (ST.μ F) ir = ir
dcIR (ST.ν F f) ir = ir
dcIR ST.Int ir = ir
dcIR ST.Float ir = ir
dcIR (ST.var ()) ir

-- ★ master's direct call is this one
dc-eq : (T : Type) (ir : M.IR ⌊ ST.Unit {0} ⌋ ⌊ T ⌋) → directCallIR T ir ≡ (dcDom T , dcCod T , dcIR T ir)
dc-eq (A ⇒[ G.mk-kind G.Zero π ] B) ir = refl
dc-eq (A ⇒[ G.mk-kind G.One π ] B)  ir = refl
dc-eq (A ⇒[ G.mk-kind G.Many π ] B) ir = refl
dc-eq ST.Unit ir = refl
dc-eq ST.Void ir = refl
dc-eq (X ST.* Y) ir = refl
dc-eq (X ST.+ Y) ir = refl
dc-eq (ST.μ F) ir = refl
dc-eq (ST.ν F f) ir = refl
dc-eq ST.Int ir = refl
dc-eq ST.Float ir = refl
dc-eq (ST.var ()) ir

module DefRel {L : Cx} (δ : Env L) (ρ : CallEnv) where
  open Rel δ ρ

  -- the closure built on `tt`, beside the argument (`⟨ ir ∘ terminal , id ⟩`)
  rel-beside : ∀ {X A : Once.IRTy.IRTy} {v : LTm L One ⟪ X ⟫} {v′ : M.IR Once.IRTy.Unit X}
             → Rel v v′ → Rel ((v ⊗l lid {A = ⟪ A ⟫}) ∘l lul⁻) M.⟨ v′ M.∘ M.terminal , M.id ⟩
  rel-beside rv = mkRel λ {a} {a′} wa →
    ≈-≈R ret-bind (≈R-≈ (>>=-congR (rel rv tt) (λ r → ≈-≈R ret-bind (ret≈R (r , wa))))
                        (≈-sym (≈-trans (>>=-cong ret-bind (λ _ → ≈-refl)) (>>=-cong ≈-refl (λ _ → ret-bind)))))

  -- ★ a definition's body against master's direct call
  rel-dc : ∀ (T : Type) {v : LTm L One (ty T)} {v′ : M.IR ⌊ ST.Unit {0} ⌋ ⌊ T ⌋} → Rel v v′ → Rel (dc T v) (dcIR T v′)
  rel-dc (A ⇒[ G.mk-kind G.Zero π ] B) rv = rel-∘ (rel-apω {π = π}) (rel-beside rv)
  rel-dc (A ⇒[ G.mk-kind G.One π ] B)  rv = rel-∘ (rel-apω {π = π}) (rel-beside rv)
  rel-dc (A ⇒[ G.mk-kind G.Many π ] B) rv = rel-∘ (rel-apω {π = π}) (rel-beside rv)
  rel-dc ST.Unit rv = rv
  rel-dc ST.Void rv = rv
  rel-dc (X ST.* Y) rv = rv
  rel-dc (X ST.+ Y) rv = rv
  rel-dc (ST.μ F) rv = rv
  rel-dc (ST.ν F f) rv = rv
  rel-dc ST.Int rv = rv
  rel-dc ST.Float rv = rv
  rel-dc (ST.var ()) rv

------------------------------------------------------------------------
-- 3. A SOURCE'S VALUE: its bridge after erasure, at the unit context.
------------------------------------------------------------------------

val : ∀ {L T} → Rs L → Src T → LTm L One (ty T)
val rs (src {Γ = Γ} {Ψ = Ψ} δ₀ m opt e) = cast (cong ⟪_⟫ (cong ⌊_⌋ δ₀)) refl (Lq rs e ∘l eraseL Γ Ψ)

module ValRel {L : Cx} (rs : Rs L) (δ : Env L) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  -- an input moved along an equal type, on both sides
  rel-dom′ : ∀ {ρ} {X Y B : IRTy} (e : X ≡ Y) {t : LTm L ⟪ X ⟫ ⟪ B ⟫} {t′ : M.IR X B}
           → Rel.Rel δ ρ t t′ → Rel.Rel δ ρ (cast (cong ⟪_⟫ e) refl t) (subst (λ o → M.IR o B) e t′)
  rel-dom′ refl r = r

  -- ★ a source's value against its IR (unoptimized: `compile`'s path)
  rel-val : ∀ {T} (s : Src T) → Src.opt s ≡ Data.Bool.false
          → Refs (λ _ _ → Data.Unit.⊤) (Main.RefOK rs δ cs (am s)) (Main.RefOK rs δ cs (am s)) (expr s)
          → Rel.Rel δ (callEnv cs ans) (val rs s) (srcIR s)
  rel-val (src {Γ = Γ} {Ψ = Ψ} δ₀ m Data.Bool.false e) refl refs =
    rel-dom′ (cong ⌊_⌋ δ₀) (Rel.rel-∘ δ (callEnv cs ans) (Main.Lq-ok rs δ cs m e refs) (Erase.rel-erase δ (callEnv cs ans) m Γ Ψ))

------------------------------------------------------------------------
-- 4. THE TABLE: the definitions, oldest first (the list's last), each body
-- over the labels before it; the resolver keyed with the grade (D457).
------------------------------------------------------------------------

k-val : ∀ {L T} (rs : Rs L) (s : Src T) → Blk (val rs s)
k-val rs (src {Γ = Γ} {Ψ = Ψ} δ₀ m opt e) = k-cast (cong ⟪_⟫ (cong ⌊_⌋ δ₀)) refl (k-∘ (Lq-blk rs e) (k-eraseL Γ Ψ))

-- a definition's label
sgOf : CompiledSrc → Sg
sgOf c = sg once (dcGr (csType c)) One (ty (dcDom (csType c))) (ty (dcCod (csType c)))

bodyOf : ∀ {L} (rs : Rs L) (c : CompiledSrc) → Body L (sgOf c)
bodyOf rs c = b1 (dc (csType c) (val rs (csSrc c)) ∘l lul) (dcGd (csType c) (k-val rs (csSrc c)))

_≟Gr_ : (g g′ : Gr) → Dec (g ≡ g′)
act ≟Gr act = yes refl
act ≟Gr eff = no λ ()
eff ≟Gr act = no λ ()
eff ≟Gr eff = yes refl

-- a resolution, one label further down
weakR : ∀ {L σ g A B} → Maybe (Σ ℕ λ l → L ∋[ l ] sg once g One A B) → Maybe (Σ ℕ λ l → (L ▸ σ) ∋[ l ] sg once g One A B)
weakR = Data.Maybe.map λ { (l , p) → l , there p }

-- one more definition: its label answers its name, its call types and its grade
extendR-at : ∀ {L} (rs : Rs L) (c : CompiledSrc) f A B g
           → Dec (csName c ≡ f) → Dec (⌊ dcDom (csType c) ⌋ ≡ A) → Dec (⌊ dcCod (csType c) ⌋ ≡ B) → Dec (dcGr (csType c) ≡ g)
           → Maybe (Σ ℕ λ l → (L ▸ sgOf c) ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫)
extendR-at {L} rs c f A B g (yes _) (yes p) (yes q) (yes r) =
  just (len L , subst₂ (λ X Y → (L ▸ sgOf c) ∋[ len L ] sg once g One ⟪ X ⟫ ⟪ Y ⟫) p q
                       (subst (λ g′ → (L ▸ sgOf c) ∋[ len L ] sg once g′ One (ty (dcDom (csType c))) (ty (dcCod (csType c)))) r here))
extendR-at rs c f A B g (yes _) (yes _) (yes _) (no _) = weakR (rs f A B g)
extendR-at rs c f A B g (yes _) (yes _) (no _)  _      = weakR (rs f A B g)
extendR-at rs c f A B g (yes _) (no _)  _       _      = weakR (rs f A B g)
extendR-at rs c f A B g (no _)  _       _       _      = weakR (rs f A B g)

extendR : ∀ {L} (rs : Rs L) (c : CompiledSrc) → Rs (L ▸ sgOf c)
extendR rs c f A B g = extendR-at rs c f A B g (csName c ≟ᶜ f) (⌊ dcDom (csType c) ⌋ ≟IRTy A) (⌊ dcCod (csType c) ⌋ ≟IRTy B) (dcGr (csType c) ≟Gr g)

record ETProg : Set where
  constructor etProg
  field
    {L}  : Cx
    defs : Defs L
    rs   : Rs L
open ETProg public

-- ★ the table, as `FromIR.trTable` builds its own: the earliest definition the list's last
exprTable : List CompiledSrc → ETProg
exprTable []       = etProg ε (λ _ _ _ _ → nothing)
exprTable (c ∷ cs) = etProg (defs (exprTable cs) ▸ bodyOf (rs (exprTable cs)) c) (extendR (rs (exprTable cs)) c)
