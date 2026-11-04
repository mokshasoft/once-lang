{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Values — the semantic operations a
-- derivation's meaning is built from respect the relational reading of
-- types, between two instances: a functor's layer read as its code's layer
-- and back, a conversion, an operation or value of the signature, and an
-- arithmetic primitive.
--
-- None looks at a type variable: `toL`/`fromL` are the identity on a
-- constant, a conversion at a variable is the identity, and the signature's
-- and the primitives' types are closed (their relation is equality).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Parametricity.Values (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (nothing)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (Dec)
open import Once.Spec.Grade using (pure; act; mk-kind; Zero; One; Many)
open import Once.Spec.Type
  using (Ty; Fun; TySub; _⟨_⟩; _⟨_⟩F; ⟦_⟧F; K; Id; _⊕_; _⊗_; Unit; _+_)
open import Once.Spec.Signature
  using (BTy; unit; void; int; float; ⌜_⌝; ⌜_⌝ᵈ; DeclType; constant; value; operation; _∶_; Op; op; ⟦_⟧ᵇ; NotEmpty; call)
import Once.Spec.Signature as S
open import Once.Spec.Sub
open import Once.Spec.Core.Syntax using (Prim; primDom; primCod;
  p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-lt; p-le; p-gt; p-ge; p-eq; p-ne; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toB; fromB; toL; fromL; conv)
open import Once.Spec.Equivalence Σ using (Rel; RelF; RelSub)
open import Once.Spec.Observation Σ using (Model; module Model)
open import Once.Spec.Trace using (returned≈; halted≈)
open import Once.Metatheory.Trace using (MaybeEnd; cut≈; end≈)
open import Once.Metatheory.Run Σ
open import Once.Metatheory.Coherence.Relation Σ using (Sim; Related; related)
open import Once.Metatheory.Coherence.Conv Σ using (subνUp)
open import Once.Metatheory.Parametricity.Comp Σ

import Once.Spec.Core.Meaning as Meaning

------------------------------------------------------------------------
-- One call, its answers mapped two ways
------------------------------------------------------------------------

module _ {X Y : Set} {R : X → Y → Set} {o : Op Σ} {v} {k : ⟦ S.Op.ans o ⟧ᵇ → X} {k′ : ⟦ S.Op.ans o ⟧ᵇ → Y}
         (hk : ∀ r → R (k r) (k′ r)) where
  private
    callA : ∀ {w h} {D : Dec (NotEmpty (S.Op.ans o))} {n d e}
          → RunA w h o v (λ r → roll (done (inj₁ (k r)))) D n d e
          → ∃[ e′ ] (RunA w h o v (λ r → roll (done (inj₁ (k′ r)))) D n d e′ × MaybeEnd R e e′)
    callA (ra-go rb-cut) = _ , ra-go rb-cut , cut≈
    callA (ra-go rb-ret) = _ , ra-go rb-ret , end≈ (returned≈ (hk _))
    callA ra-halt        = _ , ra-halt , end≈ halted≈
    callA ra-cut         = _ , ra-cut , cut≈

  callSim : Sim R (embed (performT (call o v k))) (embed (performT (call o v k′)))
  callSim w h n (run rb-cut) = _ , run rb-cut , cut≈
  callSim w h n (run (rb-call r)) with callA r
  ... | e′ , r′ , er = e′ , run (rb-call r′) , er

callRel : ∀ {X Y : Set} {R : X → Y → Set} {o : Op Σ} {v} {k : ⟦ S.Op.ans o ⟧ᵇ → X} {k′ : ⟦ S.Op.ans o ⟧ᵇ → Y}
        → (∀ r → R (k r) (k′ r)) → Related R (embed (performT (call o v k))) (embed (performT (call o v k′)))
callRel {R = R} hk = related (callSim hk) (callSim {R = flip R} hk)

------------------------------------------------------------------------
-- At two instances
------------------------------------------------------------------------

module _ {m : ℕ} {σ σ′ : TySub m 0} (ρ : RelSub σ σ′) where

  -- A functor's layer, read as its code's layer, and back.
  toL-rel : ∀ (F : Fun m) (X : Ty m) {l l′} → Rel (⟦ F ⟧F X) ρ l l′
          → LayerRel (RelF F ρ) (Rel X ρ) (toL σ F X l) (toL σ′ F X l′)
  toL-rel (K A)   X s = s
  toL-rel Id      X s = s
  toL-rel (F ⊕ G) X {inj₁ x} {inj₁ y} s = toL-rel F X s
  toL-rel (F ⊕ G) X {inj₂ x} {inj₂ y} s = toL-rel G X s
  toL-rel (F ⊕ G) X {inj₁ x} {inj₂ y} ()
  toL-rel (F ⊕ G) X {inj₂ x} {inj₁ y} ()
  toL-rel (F ⊗ G) X {x , x′} {y , y′} (s , t) = toL-rel F X s , toL-rel G X t

  fromL-rel : ∀ (F : Fun m) (X : Ty m) {l l′} → LayerRel (RelF F ρ) (Rel X ρ) l l′
            → Rel (⟦ F ⟧F X) ρ (fromL σ F X l) (fromL σ′ F X l′)
  fromL-rel (K A)   X p = p
  fromL-rel Id      X p = p
  fromL-rel (F ⊕ G) X {inj₁ x} {inj₁ y} p = fromL-rel F X p
  fromL-rel (F ⊕ G) X {inj₂ x} {inj₂ y} p = fromL-rel G X p
  fromL-rel (F ⊕ G) X {inj₁ x} {inj₂ y} ()
  fromL-rel (F ⊕ G) X {inj₂ x} {inj₁ y} ()
  fromL-rel (F ⊗ G) X {x , x′} {y , y′} (p , q) = fromL-rel F X p , fromL-rel G X q

  -- A conversion.
  convRel : ∀ {A B : Ty m} (p : A <: B) {x y} → Rel A ρ x y → Rel B ρ (conv σ p x) (conv σ′ p y)
  convRel sub-void {()}
  convRel sub-var   s = s
  convRel sub-unit  s = s
  convRel sub-int   s = s
  convRel sub-float s = s
  convRel (sub-arr {q = Zero} {π} {π′} a b g) s =
    obsRC (rcSubˡ g (rcSubʳ g (rcFmap (rcObs π π s) (convRel b))))
  convRel (sub-arr {q = One}  {π} {π′} a b g) s x x′ sx =
    obsRC (rcSubˡ g (rcSubʳ g (rcFmap (rcObs π π (s _ _ (convRel a sx))) (convRel b))))
  convRel (sub-arr {q = Many} {π} {π′} a b g) s x x′ sx =
    obsRC (rcSubˡ g (rcSubʳ g (rcFmap (rcObs π π (s _ _ (convRel a sx))) (convRel b))))
  convRel (sub-* a b) {x₁ , x₂} {y₁ , y₂} (s , t) = convRel a s , convRel b t
  convRel (sub-+ a b) {inj₁ x} {inj₁ y} s = convRel a s
  convRel (sub-+ a b) {inj₂ x} {inj₂ y} s = convRel b s
  convRel (sub-+ a b) {inj₁ x} {inj₂ y} ()
  convRel (sub-+ a b) {inj₂ x} {inj₁ y} ()
  convRel sub-μ s = s
  convRel (sub-ν {F = F} g) s = λ n → subνUp (RelF F ρ) g n (s n)

  -- The signature's base values: related exactly when equal.
  relB→ : ∀ b {x y} → Rel ⌜ b ⌝ ρ x y → toB σ b x ≡ toB σ′ b y
  relB→ unit  s = refl
  relB→ void  {()}
  relB→ int   s = s
  relB→ float s = s
  relB→ (a S.* b) {x₁ , x₂} {y₁ , y₂} (s , t) rewrite relB→ a s | relB→ b t = refl
  relB→ (a S.+ b) {inj₁ x} {inj₁ y} s rewrite relB→ a s = refl
  relB→ (a S.+ b) {inj₂ x} {inj₂ y} s rewrite relB→ b s = refl
  relB→ (a S.+ b) {inj₁ x} {inj₂ y} ()
  relB→ (a S.+ b) {inj₂ x} {inj₁ y} ()

  fromB-rel : ∀ b v → Rel ⌜ b ⌝ ρ (fromB σ b v) (fromB σ′ b v)
  fromB-rel unit  v = tt
  fromB-rel void  v = tt
  fromB-rel int   v = refl
  fromB-rel float v = refl
  fromB-rel (a S.* b) (x , y)  = fromB-rel a x , fromB-rel b y
  fromB-rel (a S.+ b) (inj₁ x) = fromB-rel a x
  fromB-rel (a S.+ b) (inj₂ y) = fromB-rel b y

  private
    valueRel : ∀ {c a q b} (mem : (c ∶ value a q b) ∈ Σ) (mo : Model) {u u′} → u ≡ u′
             → Rel ⌜ b ⌝ ρ (fromB σ b (Model.valueᵐ mo mem u)) (fromB σ′ b (Model.valueᵐ mo mem u′))
    valueRel {b = b} mem mo refl = fromB-rel b _

    opRel : ∀ {c a q b} (mem : (c ∶ operation a q b) ∈ Σ) {v v′} → v ≡ v′
          → RC act act (Rel ⌜ b ⌝ ρ) (performT (call (op mem) v (fromB σ b))) (performT (call (op mem) v′ (fromB σ′ b)))
    opRel {b = b} mem refl = rc (callRel (fromB-rel b))

  -- An operation or a value of the signature.
  sigopRel : ∀ {fmt s S} c t (mem : (c ∶ t) ∈ Σ) (mo : Model)
           → Rel ⌜ t ⌝ᵈ ρ (Meaning.sigopᵛ Σ fmt {s} S σ c t mem mo) (Meaning.sigopᵛ Σ fmt {s} S σ′ c t mem mo)
  sigopRel c (constant b) mem mo = fromB-rel b _
  sigopRel c (value a Zero b) mem mo = obsRC (rcPure (fromB-rel b _))
  sigopRel c (value a One  b) mem mo x x′ s = obsRC (rcPure (valueRel mem mo (relB→ a s)))
  sigopRel c (value a Many b) mem mo x x′ s = obsRC (rcPure (valueRel mem mo (relB→ a s)))
  sigopRel c (operation a Zero b) mem mo = obsRC (opRel mem refl)
  sigopRel c (operation a One  b) mem mo x x′ s = obsRC (opRel mem (relB→ a s))
  sigopRel c (operation a Many b) mem mo x x′ s = obsRC (opRel mem (relB→ a s))

  -- An arithmetic primitive: equal arguments, equal results.
  private
    boolRefl : ∀ (u : ⊤ ⊎ ⊤) → Rel {m} (Unit + Unit) ρ u u
    boolRefl (inj₁ tt) = tt
    boolRefl (inj₂ tt) = tt

  primRel : ∀ {fmt s S} (p : Prim) {x y} → Rel (primDom p) ρ x y
          → Rel (primCod p) ρ (Meaning.primᵛ Σ fmt {s} S σ p x) (Meaning.primᵛ Σ fmt {s} S σ′ p y)
  primRel p-add {a , b} {.a , .b} (refl , refl) = refl
  primRel p-sub {a , b} {.a , .b} (refl , refl) = refl
  primRel p-mul {a , b} {.a , .b} (refl , refl) = refl
  primRel p-div {a , b} {.a , .b} (refl , refl) = refl
  primRel p-mod {a , b} {.a , .b} (refl , refl) = refl
  primRel p-neg  refl = refl
  primRel {fmt} {s} {S} p-lt {a , b} {.a , .b} (refl , refl) = boolRefl (Meaning.primᵛ Σ fmt {s} S σ p-lt (a , b))
  primRel {fmt} {s} {S} p-le {a , b} {.a , .b} (refl , refl) = boolRefl (Meaning.primᵛ Σ fmt {s} S σ p-le (a , b))
  primRel {fmt} {s} {S} p-gt {a , b} {.a , .b} (refl , refl) = boolRefl (Meaning.primᵛ Σ fmt {s} S σ p-gt (a , b))
  primRel {fmt} {s} {S} p-ge {a , b} {.a , .b} (refl , refl) = boolRefl (Meaning.primᵛ Σ fmt {s} S σ p-ge (a , b))
  primRel {fmt} {s} {S} p-eq {a , b} {.a , .b} (refl , refl) = boolRefl (Meaning.primᵛ Σ fmt {s} S σ p-eq (a , b))
  primRel {fmt} {s} {S} p-ne {a , b} {.a , .b} (refl , refl) = boolRefl (Meaning.primᵛ Σ fmt {s} S σ p-ne (a , b))
  primRel p-fadd {a , b} {.a , .b} (refl , refl) = refl
  primRel p-fsub {a , b} {.a , .b} (refl , refl) = refl
  primRel p-fmul {a , b} {.a , .b} (refl , refl) = refl
  primRel p-fdiv {a , b} {.a , .b} (refl , refl) = refl
  primRel p-i2f  refl = refl
