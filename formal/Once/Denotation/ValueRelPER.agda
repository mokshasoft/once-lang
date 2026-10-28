-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ValueRelPER — THE VALUE RELATION IS A PER (plan 0.39 A3).
--
-- `RelD` is symmetric and transitive at every type, and so are the step-for-
-- step relation on runs (`RelS`) and on streams (`StreamRel`) whenever the
-- results' relation is. Not reflexive: at an arrow, two functions are related
-- when they take related inputs to related runs, and a function need not be
-- related to itself. Transitivity at an arrow needs the middle input related
-- to itself, which symmetry and transitivity one type down give.
--
-- Used to compose the optimizer's passes: each pass relates its output to its
-- input, so ten passes relate the last output to the first input.
------------------------------------------------------------------------

module Once.Denotation.ValueRelPER where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Ty; var; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; μ; ν)
open import Once.Spec.Polynomial using (SFunctor; SId; SK; _S⊕_; _S⊗_)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.IR.Semantics.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt)
open import Once.Denotation.ValueRel using (RelD; StreamRel; module StreamRel; LayerRel)

open RelS using (forceS)
open StreamRel using (forceR)

------------------------------------------------------------------------
-- Runs
------------------------------------------------------------------------

RelS-sym  : ∀ {X Y} {R : X → Y → Set} {R′ : Y → X → Set} → (∀ {x y} → R x y → R′ y x)
          → ∀ {m m′} → RelS R m m′ → RelS R′ m′ m
RelSB-sym : ∀ {X Y} {R : X → Y → Set} {R′ : Y → X → Set} → (∀ {x y} → R x y → R′ y x)
          → ∀ {l l′} → RelSB R l l′ → RelSB R′ l′ l
forceS (RelS-sym s h) = RelSB-sym s (forceS h)
RelSB-sym s (s-ret r)  = s-ret (s r)
RelSB-sym s (s-next h) = s-next (RelS-sym s h)
RelSB-sym s (s-call f) = s-call (λ b → RelSB-sym s (f b))
RelSB-sym s s-halt     = s-halt

RelS-trans  : ∀ {X Y Z} {R₁ : X → Y → Set} {R₂ : Y → Z → Set} {R₃ : X → Z → Set}
            → (∀ {x y z} → R₁ x y → R₂ y z → R₃ x z)
            → ∀ {m n p} → RelS R₁ m n → RelS R₂ n p → RelS R₃ m p
RelSB-trans : ∀ {X Y Z} {R₁ : X → Y → Set} {R₂ : Y → Z → Set} {R₃ : X → Z → Set}
            → (∀ {x y z} → R₁ x y → R₂ y z → R₃ x z)
            → ∀ {l l′ l″} → RelSB R₁ l l′ → RelSB R₂ l′ l″ → RelSB R₃ l l″
forceS (RelS-trans t h₁ h₂) = RelSB-trans t (forceS h₁) (forceS h₂)
RelSB-trans t (s-ret r₁)  (s-ret r₂)  = s-ret (t r₁ r₂)
RelSB-trans t (s-next h₁) (s-next h₂) = s-next (RelS-trans t h₁ h₂)
RelSB-trans t (s-call f₁) (s-call f₂) = s-call (λ b → RelSB-trans t (f₁ b) (f₂ b))
RelSB-trans t s-halt      s-halt      = s-halt

------------------------------------------------------------------------
-- Streams
------------------------------------------------------------------------

-- The runs of a stream's layers are walked inside the stream's own block
-- (not by `RelS-sym`/`RelS-trans`, which would hide the corecursive call
-- behind a function argument).
StreamRel-sym : ∀ {H x y} → StreamRel H x y → StreamRel H y x
LayerS-sym    : ∀ H {m m′} → RelS (LayerRel H H) m m′ → RelS (LayerRel H H) m′ m
LayerSB-sym   : ∀ H {l l′} → RelSB (LayerRel H H) l l′ → RelSB (LayerRel H H) l′ l
LayerRel-sym  : ∀ H G {x y} → LayerRel H G x y → LayerRel H G y x
forceR (StreamRel-sym {H} s) = LayerS-sym H (forceR s)
forceS (LayerS-sym H h) = LayerSB-sym H (forceS h)
LayerSB-sym H (s-ret r)  = s-ret (LayerRel-sym H H r)
LayerSB-sym H (s-next h) = s-next (LayerS-sym H h)
LayerSB-sym H (s-call f) = s-call (λ b → LayerSB-sym H (f b))
LayerSB-sym H s-halt     = s-halt
LayerRel-sym H (SK B)     e = sym e
LayerRel-sym H SId        s = StreamRel-sym s
LayerRel-sym H (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} r = LayerRel-sym H G₁ r
LayerRel-sym H (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} r = LayerRel-sym H G₂ r
LayerRel-sym H (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
LayerRel-sym H (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
LayerRel-sym H (G₁ S⊗ G₂) (r , s) = LayerRel-sym H G₁ r , LayerRel-sym H G₂ s

StreamRel-trans : ∀ {H x y z} → StreamRel H x y → StreamRel H y z → StreamRel H x z
LayerS-trans    : ∀ H {m n p} → RelS (LayerRel H H) m n → RelS (LayerRel H H) n p → RelS (LayerRel H H) m p
LayerSB-trans   : ∀ H {l l′ l″} → RelSB (LayerRel H H) l l′ → RelSB (LayerRel H H) l′ l″ → RelSB (LayerRel H H) l l″
LayerRel-trans  : ∀ H G {x y z} → LayerRel H G x y → LayerRel H G y z → LayerRel H G x z
forceR (StreamRel-trans {H} s₁ s₂) = LayerS-trans H (forceR s₁) (forceR s₂)
forceS (LayerS-trans H h₁ h₂) = LayerSB-trans H (forceS h₁) (forceS h₂)
LayerSB-trans H (s-ret r₁)  (s-ret r₂)  = s-ret (LayerRel-trans H H r₁ r₂)
LayerSB-trans H (s-next h₁) (s-next h₂) = s-next (LayerS-trans H h₁ h₂)
LayerSB-trans H (s-call f₁) (s-call f₂) = s-call (λ b → LayerSB-trans H (f₁ b) (f₂ b))
LayerSB-trans H s-halt      s-halt      = s-halt
LayerRel-trans H (SK B)     e₁ e₂ = trans e₁ e₂
LayerRel-trans H SId        s₁ s₂ = StreamRel-trans s₁ s₂
LayerRel-trans H (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} {inj₁ _} r₁ r₂ = LayerRel-trans H G₁ r₁ r₂
LayerRel-trans H (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} {inj₂ _} r₁ r₂ = LayerRel-trans H G₂ r₁ r₂
LayerRel-trans H (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
LayerRel-trans H (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
LayerRel-trans H (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} {inj₂ _} _ ()
LayerRel-trans H (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} {inj₁ _} _ ()
LayerRel-trans H (G₁ S⊗ G₂) (r₁ , s₁) (r₂ , s₂) = LayerRel-trans H G₁ r₁ r₂ , LayerRel-trans H G₂ s₁ s₂

------------------------------------------------------------------------
-- Values, by type
------------------------------------------------------------------------

RelD-sym   : ∀ {m} (A : Ty m) {x y} → RelD A x y → RelD A y x
RelD-trans : ∀ {m} (A : Ty m) {x y z} → RelD A x y → RelD A y z → RelD A x z

-- the middle input of a composite at an arrow: related to itself
private
  RelD-self : ∀ {m} (A : Ty m) {x y} → RelD A x y → RelD A y y
  RelD-self A r = RelD-trans A (RelD-sym A r) r

RelD-sym Unit _ = tt
RelD-sym Void {()}
RelD-sym (A * B) (r , s) = RelD-sym A r , RelD-sym B s
RelD-sym (A + B) {inj₁ _} {inj₁ _} r = RelD-sym A r
RelD-sym (A + B) {inj₂ _} {inj₂ _} r = RelD-sym B r
RelD-sym (A + B) {inj₁ _} {inj₂ _} ()
RelD-sym (A + B) {inj₂ _} {inj₁ _} ()
RelD-sym (A ⇒[ mk-kind Zero π ] B) h = RelS-sym (RelD-sym B) h
RelD-sym (A ⇒[ mk-kind One  π ] B) h r = RelS-sym (RelD-sym B) (h (RelD-sym A r))
RelD-sym (A ⇒[ mk-kind Many π ] B) h r = RelS-sym (RelD-sym B) (h (RelD-sym A r))
RelD-sym (μ F)   e = sym e
RelD-sym (ν F _) s = StreamRel-sym s
RelD-sym Int     e = sym e
RelD-sym Float   e = sym e
RelD-sym (var _) {()}

RelD-trans Unit _ _ = tt
RelD-trans Void {()}
RelD-trans (A * B) (r₁ , s₁) (r₂ , s₂) = RelD-trans A r₁ r₂ , RelD-trans B s₁ s₂
RelD-trans (A + B) {inj₁ _} {inj₁ _} {inj₁ _} r₁ r₂ = RelD-trans A r₁ r₂
RelD-trans (A + B) {inj₂ _} {inj₂ _} {inj₂ _} r₁ r₂ = RelD-trans B r₁ r₂
RelD-trans (A + B) {inj₁ _} {inj₂ _} ()
RelD-trans (A + B) {inj₂ _} {inj₁ _} ()
RelD-trans (A + B) {inj₁ _} {inj₁ _} {inj₂ _} _ ()
RelD-trans (A + B) {inj₂ _} {inj₂ _} {inj₁ _} _ ()
RelD-trans (A ⇒[ mk-kind Zero π ] B) h₁ h₂ = RelS-trans (RelD-trans B) h₁ h₂
RelD-trans (A ⇒[ mk-kind One  π ] B) h₁ h₂ r = RelS-trans (RelD-trans B) (h₁ r) (h₂ (RelD-self A r))
RelD-trans (A ⇒[ mk-kind Many π ] B) h₁ h₂ r = RelS-trans (RelD-trans B) (h₁ r) (h₂ (RelD-self A r))
RelD-trans (μ F)   e₁ e₂ = trans e₁ e₂
RelD-trans (ν F _) s₁ s₂ = StreamRel-trans s₁ s₂
RelD-trans Int     e₁ e₂ = trans e₁ e₂
RelD-trans Float   e₁ e₂ = trans e₁ e₂
RelD-trans (var _) {()}
