{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.PER — sameness is a partial equivalence:
-- symmetric and transitive at every type (not reflexive: a function may tell
-- apart arguments its type calls the same).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.PER (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Observation Σ using (History; End)
open import Once.Spec.Delay using (Delay; _⇓_; _≈⟨_⟩_)
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Coherence.Relation Σ using (EndRel-flip; EndRel-trans)

open νM using (outν)

------------------------------------------------------------------------
-- Observations
------------------------------------------------------------------------

module _ {X : Set} {R : X → X → Set} where
  private
    Out : Set
    Out = History × End X

    swap : (∀ {x y} → R x y → R y x) → ∀ {o o′} → Outcome≈ R o o′ → Outcome≈ R o′ o
    swap s (eq , er) = sym eq , EndRel-flip-sym er
      where EndRel-flip-sym : ∀ {e e′} → EndRel R e e′ → EndRel R e′ e
            EndRel-flip-sym (returned≈ r) = returned≈ (s r)
            EndRel-flip-sym halted≈ = halted≈
            EndRel-flip-sym cut≈    = cut≈

    chain : (∀ {x y z} → R x y → R y z → R x z) → ∀ {o₁ o₂ o₃} → Outcome≈ R o₁ o₂ → Outcome≈ R o₂ o₃ → Outcome≈ R o₁ o₃
    chain t (eq , er) (eq′ , er′) = trans eq eq′ , EndRel-trans t er er′

    ≈-sym : (∀ {x y} → R x y → R y x) → ∀ {d d′ : Delay Out} → d ≈⟨ Outcome≈ R ⟩ d′ → d′ ≈⟨ Outcome≈ R ⟩ d
    ≈-sym s (f , b) = (λ o a → go₁ (b o a)) , (λ o a → go₂ (f o a))
      where go₁ : ∀ {d₀ : Delay Out} {o} → ∃[ o′ ] (d₀ ⇓ o′ × Outcome≈ R o′ o) → ∃[ o′ ] (d₀ ⇓ o′ × Outcome≈ R o o′)
            go₁ (o′ , a , q) = o′ , a , swap s q
            go₂ : ∀ {d₀ : Delay Out} {o} → ∃[ o′ ] (d₀ ⇓ o′ × Outcome≈ R o o′) → ∃[ o′ ] (d₀ ⇓ o′ × Outcome≈ R o′ o)
            go₂ (o′ , a , q) = o′ , a , swap s q

    ≈-trans : (∀ {x y z} → R x y → R y z → R x z) → ∀ {d₁ d₂ d₃ : Delay Out}
            → d₁ ≈⟨ Outcome≈ R ⟩ d₂ → d₂ ≈⟨ Outcome≈ R ⟩ d₃ → d₁ ≈⟨ Outcome≈ R ⟩ d₃
    ≈-trans t {d₁} {d₂} {d₃} (f , b) (f′ , b′) = fwd , bwd
      where
        fwd : ∀ o → d₁ ⇓ o → ∃[ o′ ] (d₃ ⇓ o′ × Outcome≈ R o o′)
        fwd o a = step (f o a)
          where step : ∃[ o₂ ] (d₂ ⇓ o₂ × Outcome≈ R o o₂) → ∃[ o′ ] (d₃ ⇓ o′ × Outcome≈ R o o′)
                step (o₂ , a₂ , q) = next (f′ o₂ a₂)
                  where next : ∃[ o₃ ] (d₃ ⇓ o₃ × Outcome≈ R o₂ o₃) → _
                        next (o₃ , a₃ , q′) = o₃ , a₃ , chain t q q′
        bwd : ∀ o → d₃ ⇓ o → ∃[ o′ ] (d₁ ⇓ o′ × Outcome≈ R o′ o)
        bwd o a = step (b′ o a)
          where step : ∃[ o₂ ] (d₂ ⇓ o₂ × Outcome≈ R o₂ o) → ∃[ o′ ] (d₁ ⇓ o′ × Outcome≈ R o′ o)
                step (o₂ , a₂ , q) = next (b o₂ a₂)
                  where next : ∃[ o₁ ] (d₁ ⇓ o₁ × Outcome≈ R o₁ o₂) → _
                        next (o₁ , a₁ , q′) = o₁ , a₁ , chain t q′ q

  UpTo-sym : ∀ n → (∀ {x y} → R x y → R y x) → ∀ {m m′} → UpTo n R m m′ → UpTo n R m′ m
  UpTo-sym n s p ι = ≈-sym s (p ι)

  UpTo-trans : ∀ n → (∀ {x y z} → R x y → R y z → R x z) → ∀ {m₁ m₂ m₃} → UpTo n R m₁ m₂ → UpTo n R m₂ m₃ → UpTo n R m₁ m₃
  UpTo-trans n t p q ι = ≈-trans t (p ι) (q ι)

------------------------------------------------------------------------
-- Layers and streams
------------------------------------------------------------------------

LayerEq-sym : ∀ (G : SFunctor) {X} {R : X → X → Set} → (∀ {x y} → R x y → R y x)
            → ∀ {l l′} → LayerEq G R l l′ → LayerEq G R l′ l
LayerEq-sym (SK B) s p = sym p
LayerEq-sym SId    s p = s p
LayerEq-sym (G S⊕ H) s {inj₁ x} {inj₁ y} p = LayerEq-sym G s p
LayerEq-sym (G S⊕ H) s {inj₂ x} {inj₂ y} p = LayerEq-sym H s p
LayerEq-sym (G S⊕ H) s {inj₁ x} {inj₂ y} ()
LayerEq-sym (G S⊕ H) s {inj₂ x} {inj₁ y} ()
LayerEq-sym (G S⊗ H) s (p , q) = LayerEq-sym G s p , LayerEq-sym H s q

LayerEq-trans : ∀ (G : SFunctor) {X} {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z)
              → ∀ {l₁ l₂ l₃} → LayerEq G R l₁ l₂ → LayerEq G R l₂ l₃ → LayerEq G R l₁ l₃
LayerEq-trans (SK B) t p q = trans p q
LayerEq-trans SId    t p q = t p q
LayerEq-trans (G S⊕ H) t {inj₁ x} {inj₁ y} {inj₁ z} p q = LayerEq-trans G t p q
LayerEq-trans (G S⊕ H) t {inj₂ x} {inj₂ y} {inj₂ z} p q = LayerEq-trans H t p q
LayerEq-trans (G S⊕ H) t {inj₁ x} {inj₁ y} {inj₂ z} p ()
LayerEq-trans (G S⊕ H) t {inj₁ x} {inj₂ y} {_} () q
LayerEq-trans (G S⊕ H) t {inj₂ x} {inj₂ y} {inj₁ z} p ()
LayerEq-trans (G S⊕ H) t {inj₂ x} {inj₁ y} {_} () q
LayerEq-trans (G S⊗ H) t (p , q) (p′ , q′) = LayerEq-trans G t p p′ , LayerEq-trans H t q q′

νUpTo-sym : ∀ π (G : SFunctor) n {v w} → νUpTo π G n v w → νUpTo π G n w v
νUpTo-sym π G zero    p = tt
νUpTo-sym π G (suc n) {v} {w} p k =
  UpTo-sym k (LayerEq-sym G (νUpTo-sym π G n)) {toT∞ π (outν v)} {toT∞ π (outν w)} (p k)

νUpTo-trans : ∀ π (G : SFunctor) n {u v w} → νUpTo π G n u v → νUpTo π G n v w → νUpTo π G n u w
νUpTo-trans π G zero    p q = tt
νUpTo-trans π G (suc n) {u} {v} {w} p q k =
  UpTo-trans k (LayerEq-trans G (νUpTo-trans π G n)) {toT∞ π (outν u)} {toT∞ π (outν v)} {toT∞ π (outν w)} (p k) (q k)

------------------------------------------------------------------------
-- Sameness
------------------------------------------------------------------------

-- Symmetry and transitivity at each type, with `Same` at the argument types
-- (one type smaller) for the functions.
Same-sym    : ∀ (A : Type) {x y} → Same A x y → Same A y x
Same-trans  : ∀ (A : Type) {x y z} → Same A x y → Same A y z → Same A x z
SameM-sym   : ∀ π (A : Type) {m m′} → SameM π A m m′ → SameM π A m′ m
SameM-trans : ∀ π (A : Type) {m₁ m₂ m₃} → SameM π A m₁ m₂ → SameM π A m₂ m₃ → SameM π A m₁ m₃
SameM-sym   π A p n = UpTo-sym n (Same-sym A) (p n)
SameM-trans π A p q n = UpTo-trans n (Same-trans A) (p n) (q n)

Same-sym (var ())
Same-sym Unit  p = tt
Same-sym Void  {()}
Same-sym Int   p = sym p
Same-sym Float p = sym p
Same-sym (μ F) p = sym p
Same-sym (A * B) {x , x′} {y , y′} (p , q) = Same-sym A p , Same-sym B q
Same-sym (A + B) {inj₁ x} {inj₁ y} p = Same-sym A p
Same-sym (A + B) {inj₂ x} {inj₂ y} p = Same-sym B p
Same-sym (A + B) {inj₁ x} {inj₂ y} ()
Same-sym (A + B) {inj₂ x} {inj₁ y} ()
Same-sym (A ⇒[ mk-kind Zero π ] B) p = SameM-sym π B p
Same-sym (A ⇒[ mk-kind One  π ] B) p = λ a a′ s → SameM-sym π B (p a′ a (Same-sym A s))
Same-sym (A ⇒[ mk-kind Many π ] B) p = λ a a′ s → SameM-sym π B (p a′ a (Same-sym A s))
Same-sym (ν F π) p n = νUpTo-sym π (code F) n (p n)

Same-trans (var ())
Same-trans Unit  p q = tt
Same-trans Void  {()}
Same-trans Int   p q = trans p q
Same-trans Float p q = trans p q
Same-trans (μ F) p q = trans p q
Same-trans (A * B) {x , x′} {y , y′} {z , z′} (p , p′) (q , q′) = Same-trans A p q , Same-trans B p′ q′
Same-trans (A + B) {inj₁ x} {inj₁ y} {inj₁ z} p q = Same-trans A p q
Same-trans (A + B) {inj₂ x} {inj₂ y} {inj₂ z} p q = Same-trans B p q
Same-trans (A + B) {inj₁ x} {inj₁ y} {inj₂ z} p ()
Same-trans (A + B) {inj₁ x} {inj₂ y} () q
Same-trans (A + B) {inj₂ x} {inj₂ y} {inj₁ z} p ()
Same-trans (A + B) {inj₂ x} {inj₁ y} () q
Same-trans (A ⇒[ mk-kind Zero π ] B) p q = SameM-trans π B p q
Same-trans (A ⇒[ mk-kind One  π ] B) p q =
  λ a a′ s → SameM-trans π B (p a a′ s) (q a′ a′ (Same-trans A (Same-sym A s) s))
Same-trans (A ⇒[ mk-kind Many π ] B) p q =
  λ a a′ s → SameM-trans π B (p a a′ s) (q a′ a′ (Same-trans A (Same-sym A s) s))
Same-trans (ν F π) p q n = νUpTo-trans π (code F) n (p n) (q n)
