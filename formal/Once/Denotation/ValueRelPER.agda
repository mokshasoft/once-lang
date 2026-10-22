-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ValueRelPER — the value relation is a partial equivalence
-- (plan 0.119 D5).
--
-- `RelD` is symmetric and transitive (not reflexive: a closure that sends
-- related arguments to unrelated runs is related to nothing, itself included).
-- Transitivity at an arrow uses the middle argument's self-relatedness, which
-- symmetry and transitivity at the smaller type give. Runs are compared step
-- for step, so `RelS` inherits both; streams likewise, coinductively.
------------------------------------------------------------------------

module Once.Denotation.ValueRelPER where

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float)
open import Once.Internal.Type using (μ-type; ν-type)
open import Once.Internal.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Internal.Iterative using (T∞)
open T∞ using (force)
open import Once.Internal.StreamInf using (νᴵ; module νᴵ)
open νᴵ using (forceᴵ)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt)
open RelS using (forceS)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.ValueRel using (RelD; StreamRel; LayerRel; RelS-mono)
open StreamRel using (forceR)

------------------------------------------------------------------------
-- Runs.
------------------------------------------------------------------------

RelS-sym  : ∀ {X Y} {R : X → Y → Set} {S : Y → X → Set} → (∀ {a b} → R a b → S b a)
          → ∀ {m n} → RelS R m n → RelS S n m
RelSB-sym : ∀ {X Y} {R : X → Y → Set} {S : Y → X → Set} → (∀ {a b} → R a b → S b a)
          → ∀ {l l′} → RelSB R l l′ → RelSB S l′ l
forceS (RelS-sym h r) = RelSB-sym h (forceS r)
RelSB-sym h (s-ret r)  = s-ret (h r)
RelSB-sym h (s-next r) = s-next (RelS-sym h r)
RelSB-sym h (s-call f) = s-call (λ b → RelSB-sym h (f b))
RelSB-sym h s-halt     = s-halt

RelS-trans  : ∀ {X Y Z} {R : X → Y → Set} {S : Y → Z → Set} {U : X → Z → Set}
            → (∀ {a b c} → R a b → S b c → U a c)
            → ∀ {m n p} → RelS R m n → RelS S n p → RelS U m p
RelSB-trans : ∀ {X Y Z} {R : X → Y → Set} {S : Y → Z → Set} {U : X → Z → Set}
            → (∀ {a b c} → R a b → S b c → U a c)
            → ∀ {l l′ l″} → RelSB R l l′ → RelSB S l′ l″ → RelSB U l l″
forceS (RelS-trans h r s) = RelSB-trans h (forceS r) (forceS s)
RelSB-trans h (s-ret r)  (s-ret s)  = s-ret (h r s)
RelSB-trans h (s-next r) (s-next s) = s-next (RelS-trans h r s)
RelSB-trans h (s-call f) (s-call g) = s-call (λ b → RelSB-trans h (f b) (g b))
RelSB-trans h s-halt     s-halt     = s-halt

-- Two runs related to a third are related to each other through it.
RelS-meet  : ∀ {X Y Z} {R : X → Z → Set} {S : Y → Z → Set} {m : T∞ X} {n : T∞ Y} {p : T∞ Z}
           → RelS R m p → RelS S n p → RelS (λ a b → Σ[ c ∈ Z ] R a c × S b c) m n
RelSB-meet : ∀ {X Y Z} {R : X → Z → Set} {S : Y → Z → Set} {l l′ l″}
           → RelSB R l l″ → RelSB S l′ l″ → RelSB (λ a b → Σ[ c ∈ Z ] R a c × S b c) l l′
forceS (RelS-meet r s) = RelSB-meet (forceS r) (forceS s)
RelSB-meet (s-ret r)  (s-ret s)  = s-ret (_ , r , s)
RelSB-meet (s-next r) (s-next s) = s-next (RelS-meet r s)
RelSB-meet (s-call f) (s-call g) = s-call (λ b → RelSB-meet (f b) (g b))
RelSB-meet s-halt     s-halt     = s-halt

-- The run on the right of a relation is related to itself, by whatever its
-- values are related to themselves by.
RelS-rightself  : ∀ {X Y} {R : X → Y → Set} {S : Y → Y → Set} → (∀ {a b} → R a b → S b b)
                → ∀ {m n} → RelS R m n → RelS S n n
RelSB-rightself : ∀ {X Y} {R : X → Y → Set} {S : Y → Y → Set} → (∀ {a b} → R a b → S b b)
                → ∀ {l l′} → RelSB R l l′ → RelSB S l′ l′
forceS (RelS-rightself h r) = RelSB-rightself h (forceS r)
RelSB-rightself h (s-ret r)  = s-ret (h r)
RelSB-rightself h (s-next r) = s-next (RelS-rightself h r)
RelSB-rightself h (s-call f) = s-call (λ b → RelSB-rightself h (f b))
RelSB-rightself h s-halt     = s-halt

-- A relation to a run, paired with that run's relation to itself.
RelS-pairʳ  : ∀ {X Y} {R : X → Y → Set} {S : Y → Y → Set} {m : T∞ X} {n : T∞ Y}
            → RelS R m n → RelS S n n → RelS (λ a b → R a b × S b b) m n
RelSB-pairʳ : ∀ {X Y} {R : X → Y → Set} {S : Y → Y → Set} {l l′}
            → RelSB R l l′ → RelSB S l′ l′ → RelSB (λ a b → R a b × S b b) l l′
forceS (RelS-pairʳ r s) = RelSB-pairʳ (forceS r) (forceS s)
RelSB-pairʳ (s-ret r)  (s-ret s)  = s-ret (r , s)
RelSB-pairʳ (s-next r) (s-next s) = s-next (RelS-pairʳ r s)
RelSB-pairʳ (s-call f) (s-call g) = s-call (λ b → RelSB-pairʳ (f b) (g b))
RelSB-pairʳ s-halt     s-halt     = s-halt

------------------------------------------------------------------------
-- Streams.
------------------------------------------------------------------------

module _ {H : SFunctor} where
  stream-sym : ∀ {x y : νᴵ H} → StreamRel H x y → StreamRel H y x
  run-sym    : ∀ {m n} → RelS (LayerRel H H) m n → RelS (LayerRel H H) n m
  block-sym  : ∀ {l l′} → RelSB (LayerRel H H) l l′ → RelSB (LayerRel H H) l′ l
  layer-sym  : ∀ (G : SFunctor) {l l′} → LayerRel H G l l′ → LayerRel H G l′ l
  forceR (stream-sym r) = run-sym (forceR r)
  forceS (run-sym r) = block-sym (forceS r)
  block-sym (s-ret r)  = s-ret (layer-sym H r)
  block-sym (s-next r) = s-next (run-sym r)
  block-sym (s-call f) = s-call (λ b → block-sym (f b))
  block-sym s-halt     = s-halt
  layer-sym (SK B)     e = sym e
  layer-sym SId        r = stream-sym r
  layer-sym (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} r = layer-sym G₁ r
  layer-sym (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} r = layer-sym G₂ r
  layer-sym (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
  layer-sym (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
  layer-sym (G₁ S⊗ G₂) {_ , _} {_ , _} (r , s) = layer-sym G₁ r , layer-sym G₂ s

  stream-trans : ∀ {x y z : νᴵ H} → StreamRel H x y → StreamRel H y z → StreamRel H x z
  run-trans    : ∀ {m n p} → RelS (LayerRel H H) m n → RelS (LayerRel H H) n p → RelS (LayerRel H H) m p
  block-trans  : ∀ {l l′ l″} → RelSB (LayerRel H H) l l′ → RelSB (LayerRel H H) l′ l″ → RelSB (LayerRel H H) l l″
  layer-trans  : ∀ (G : SFunctor) {l l′ l″} → LayerRel H G l l′ → LayerRel H G l′ l″ → LayerRel H G l l″
  forceR (stream-trans r s) = run-trans (forceR r) (forceR s)
  forceS (run-trans r s) = block-trans (forceS r) (forceS s)
  block-trans (s-ret r)  (s-ret s)  = s-ret (layer-trans H r s)
  block-trans (s-next r) (s-next s) = s-next (run-trans r s)
  block-trans (s-call f) (s-call g) = s-call (λ b → block-trans (f b) (g b))
  block-trans s-halt     s-halt     = s-halt
  layer-trans (SK B)     e e′ = trans e e′
  layer-trans SId        r s  = stream-trans r s
  layer-trans (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} {inj₁ _} r s = layer-trans G₁ r s
  layer-trans (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} {inj₂ _} r s = layer-trans G₂ r s
  layer-trans (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} () _
  layer-trans (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} () _
  layer-trans (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} {inj₂ _} _ ()
  layer-trans (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} {inj₁ _} _ ()
  layer-trans (G₁ S⊗ G₂) {_ , _} {_ , _} {_ , _} (r , s) (r′ , s′) = layer-trans G₁ r r′ , layer-trans G₂ s s′

------------------------------------------------------------------------
-- Values.
------------------------------------------------------------------------

mutual
  RelD-sym : ∀ (A : Type) {x y : ⟦ A ⟧ᴰ} → RelD A x y → RelD A y x
  RelD-sym Unit r = tt
  RelD-sym Void {()}
  RelD-sym (A * B) {_ , _} {_ , _} (r , s) = RelD-sym A r , RelD-sym B s
  RelD-sym (A + B) {inj₁ _} {inj₁ _} r = RelD-sym A r
  RelD-sym (A + B) {inj₂ _} {inj₂ _} r = RelD-sym B r
  RelD-sym (A + B) {inj₁ _} {inj₂ _} ()
  RelD-sym (A + B) {inj₂ _} {inj₁ _} ()
  RelD-sym (A ⇒[ mk-kind Zero π ] B) r = RelS-sym (RelD-sym B) r
  RelD-sym (A ⇒[ mk-kind One π ] B) r ra = RelS-sym (RelD-sym B) (r (RelD-sym A ra))
  RelD-sym (A ⇒[ mk-kind Many π ] B) r ra = RelS-sym (RelD-sym B) (r (RelD-sym A ra))
  RelD-sym (μ-type F) r = sym r
  RelD-sym (ν-type F π) r = stream-sym r
  RelD-sym Int r = sym r
  RelD-sym Float r = sym r

  RelD-trans : ∀ (A : Type) {x y z : ⟦ A ⟧ᴰ} → RelD A x y → RelD A y z → RelD A x z
  RelD-trans Unit r s = tt
  RelD-trans Void {()}
  RelD-trans (A * B) {_ , _} {_ , _} {_ , _} (r , s) (r′ , s′) = RelD-trans A r r′ , RelD-trans B s s′
  RelD-trans (A + B) {inj₁ _} {inj₁ _} {inj₁ _} r s = RelD-trans A r s
  RelD-trans (A + B) {inj₂ _} {inj₂ _} {inj₂ _} r s = RelD-trans B r s
  RelD-trans (A + B) {inj₁ _} {inj₂ _} () _
  RelD-trans (A + B) {inj₂ _} {inj₁ _} () _
  RelD-trans (A + B) {inj₁ _} {inj₁ _} {inj₂ _} _ ()
  RelD-trans (A + B) {inj₂ _} {inj₂ _} {inj₁ _} _ ()
  RelD-trans (A ⇒[ mk-kind Zero π ] B) r s = RelS-trans (RelD-trans B) r s
  RelD-trans (A ⇒[ mk-kind One π ] B) r s ra = RelS-trans (RelD-trans B) (r ra) (s (RelD-rightself A ra))
  RelD-trans (A ⇒[ mk-kind Many π ] B) r s ra = RelS-trans (RelD-trans B) (r ra) (s (RelD-rightself A ra))
  RelD-trans (μ-type F) r s = trans r s
  RelD-trans (ν-type F π) r s = stream-trans r s
  RelD-trans Int r s = trans r s
  RelD-trans Float r s = trans r s

  -- The right side of a related pair is related to itself.
  RelD-rightself : ∀ (A : Type) {x y : ⟦ A ⟧ᴰ} → RelD A x y → RelD A y y
  RelD-rightself A r = RelD-trans A (RelD-sym A r) r

RelD-leftself : ∀ (A : Type) {x y : ⟦ A ⟧ᴰ} → RelD A x y → RelD A x x
RelD-leftself A r = RelD-trans A r (RelD-sym A r)
