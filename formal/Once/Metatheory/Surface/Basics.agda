{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Surface.Basics — the surface metatheory's lemmas that need
-- no assumption on names: the generators' names, type injectivity and
-- substitution read back at its variables, and the rules no expression
-- form can share (`Metatheory.Surface` adds the ones distinct names give).
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Name using (CanonicalName)

module Once.Metatheory.Surface.Basics (Σ : Signature) {s} (S : Defs s) (nm : Fin s → CanonicalName) where


open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Purity; pure; act; Finite; pureᶠ; actᶠ; fin; Many; mk-kind; ArrowKind; _⊑π_; ⊑-pure; EffGrade; eg-act; eg-eff)
open import Once.Spec.Name using (gen; NotGenerator; genNames)
open import Once.Spec.Type
  using (Ty; KCtx; TySub; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; _⟨_⟩; _⟨_⟩F; Occurs; OccursF;
         o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ˡ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ;
         Fun; K; Id; _⊕_; _⊗_; ⟦_⟧F)
open import Once.Spec.Signature using (_∶_; ⌜_⌝ᵈ)
open import Once.Spec.Core.Syntax using (_!!_; module Schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Typing Σ S nm

open import Once.Metatheory.OneName using (decl-unique)
open import Once.Metatheory.Types using (join-unique)
open import Once.Spec.Sub using (_⊔_≔_)


------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

module _ where
  notGen : ∀ {w} → w ∈ genNames → ¬ NotGenerator (gen w)
  notGen m n = All.lookup n m refl

  -- The eight generators that are names, and where they are listed.
  id∈       : "id" ∈ genNames
  fst∈      : "fst" ∈ genNames
  snd∈      : "snd" ∈ genNames
  terminal∈ : "terminal" ∈ genNames
  initial∈  : "initial" ∈ genNames
  unit∈     : "unit" ∈ genNames
  id∈       = here refl
  fst∈      = there (here refl)
  snd∈      = there (there (here refl))
  terminal∈ = there (there (there (here refl)))
  initial∈  = there (there (there (there (here refl))))
  unit∈     = there (there (there (there (there (there (there (here refl)))))))

  -- The special heads.
  sid       : "id" ∈ specialGenerators
  sfst      : "fst" ∈ specialGenerators
  ssnd      : "snd" ∈ specialGenerators
  sterminal : "terminal" ∈ specialGenerators
  sapply    : "apply" ∈ specialGenerators
  scata     : "cata" ∈ specialGenerators
  sOut      : "Out" ∈ specialGenerators
  sid       = here refl
  sfst      = there (here refl)
  ssnd      = there (there (here refl))
  sterminal = there (there (there (here refl)))
  sapply    = there (there (there (there (there (there (there (there (here refl))))))))
  scata     = there (there (there (there (there (there (there (there (there (there (here refl))))))))))
  sOut      = there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))

  -- No definition is named as a generator, or as an operation.
  fin0 : ∀ {n} → n ≡ 0 → Fin n → ⊥
  fin0 refl ()

  0<0 : ∀ {n} → n ≡ 0 → ¬ (0 < n)
  0<0 refl ()

------------------------------------------------------------------------
-- Types: injectivity, and substitution read back at the variables it uses
------------------------------------------------------------------------

module _ where
  *-inj : ∀ {m} {A A′ B B′ : Ty m} → (A * B) ≡ (A′ * B′) → (A ≡ A′) × (B ≡ B′)
  *-inj refl = refl , refl
  +-inj : ∀ {m} {A A′ B B′ : Ty m} → (A + B) ≡ (A′ + B′) → (A ≡ A′) × (B ≡ B′)
  +-inj refl = refl , refl
  ⇒-inj : ∀ {m} {A A′ B B′ : Ty m} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → (A ≡ A′) × (k ≡ k′) × (B ≡ B′)
  ⇒-inj refl = refl , refl , refl
  μ-inj : ∀ {m} {F F′ : Fun m} → μ F ≡ μ F′ → F ≡ F′
  μ-inj refl = refl
  ν-inj : ∀ {m} {F F′ : Fun m} {π π′} → ν F π ≡ ν F′ π′ → (F ≡ F′) × (π ≡ π′)
  ν-inj refl = refl , refl
  K-inj : ∀ {m} {A A′ : Ty m} → K A ≡ K A′ → A ≡ A′
  K-inj refl = refl
  ⊕-inj : ∀ {m} {F F′ G G′ : Fun m} → (F ⊕ G) ≡ (F′ ⊕ G′) → (F ≡ F′) × (G ≡ G′)
  ⊕-inj refl = refl , refl
  ⊗-inj : ∀ {m} {F F′ G G′ : Fun m} → (F ⊗ G) ≡ (F′ ⊗ G′) → (F ≡ F′) × (G ≡ G′)
  ⊗-inj refl = refl , refl
  kind-π : ∀ {q q′ π π′} → mk-kind q π ≡ mk-kind q′ π′ → π ≡ π′
  kind-π refl = refl

  ⟨⟩-cong  : ∀ {a k} (A : Ty a) {τ τ′ : TySub a k} → (∀ i → Occurs i A → τ i ≡ τ′ i) → A ⟨ τ ⟩ ≡ A ⟨ τ′ ⟩
  ⟨⟩F-cong : ∀ {a k} (F : Fun a) {τ τ′ : TySub a k} → (∀ i → OccursF i F → τ i ≡ τ′ i) → F ⟨ τ ⟩F ≡ F ⟨ τ′ ⟩F
  ⟨⟩-cong (var i)      h = h i o-var
  ⟨⟩-cong Unit         h = refl
  ⟨⟩-cong Void         h = refl
  ⟨⟩-cong (A * B)      h = cong₂ _*_ (⟨⟩-cong A λ i o → h i (o-*ˡ o)) (⟨⟩-cong B λ i o → h i (o-*ʳ o))
  ⟨⟩-cong (A + B)      h = cong₂ _+_ (⟨⟩-cong A λ i o → h i (o-+ˡ o)) (⟨⟩-cong B λ i o → h i (o-+ʳ o))
  ⟨⟩-cong (A ⇒[ k ] B) h = cong₂ (λ a b → a ⇒[ k ] b) (⟨⟩-cong A λ i o → h i (o-⇒ˡ o)) (⟨⟩-cong B λ i o → h i (o-⇒ʳ o))
  ⟨⟩-cong (μ F)        h = cong μ (⟨⟩F-cong F λ i o → h i (o-μ o))
  ⟨⟩-cong (ν F π)      h = cong (λ G → ν G π) (⟨⟩F-cong F λ i o → h i (o-ν o))
  ⟨⟩-cong Int          h = refl
  ⟨⟩-cong Float        h = refl
  ⟨⟩F-cong (K A)   h = cong K (⟨⟩-cong A λ i o → h i (o-K o))
  ⟨⟩F-cong Id      h = refl
  ⟨⟩F-cong (F ⊕ G) h = cong₂ _⊕_ (⟨⟩F-cong F λ i o → h i (o-⊕ˡ o)) (⟨⟩F-cong G λ i o → h i (o-⊕ʳ o))
  ⟨⟩F-cong (F ⊗ G) h = cong₂ _⊗_ (⟨⟩F-cong F λ i o → h i (o-⊗ˡ o)) (⟨⟩F-cong G λ i o → h i (o-⊗ʳ o))

  occ-det  : ∀ {a k} {A : Ty a} {τ τ′ : TySub a k} → A ⟨ τ ⟩ ≡ A ⟨ τ′ ⟩ → ∀ {i} → Occurs i A → τ i ≡ τ′ i
  occF-det : ∀ {a k} {F : Fun a} {τ τ′ : TySub a k} → F ⟨ τ ⟩F ≡ F ⟨ τ′ ⟩F → ∀ {i} → OccursF i F → τ i ≡ τ′ i
  occ-det e o-var      = e
  occ-det e (o-*ˡ o)   = occ-det (proj₁ (*-inj e)) o
  occ-det e (o-*ʳ o)   = occ-det (proj₂ (*-inj e)) o
  occ-det e (o-+ˡ o)   = occ-det (proj₁ (+-inj e)) o
  occ-det e (o-+ʳ o)   = occ-det (proj₂ (+-inj e)) o
  occ-det e (o-⇒ˡ o)   = occ-det (proj₁ (⇒-inj e)) o
  occ-det e (o-⇒ʳ o)   = occ-det (proj₂ (proj₂ (⇒-inj e))) o
  occ-det e (o-μ o)    = occF-det (μ-inj e) o
  occ-det e (o-ν o)    = occF-det (proj₁ (ν-inj e)) o
  occF-det e (o-K o)   = occ-det (K-inj e) o
  occF-det e (o-⊕ˡ o)  = occF-det (proj₁ (⊕-inj e)) o
  occF-det e (o-⊕ʳ o)  = occF-det (proj₂ (⊕-inj e)) o
  occF-det e (o-⊗ˡ o)  = occF-det (proj₁ (⊗-inj e)) o
  occF-det e (o-⊗ʳ o)  = occF-det (proj₂ (⊗-inj e)) o

  -- A monomorphic definition has one type, whatever the instance.
  mono : ∀ {m} {d d′} → d ≡ d′ → (τ : TySub (arity (S !! d)) m) (τ′ : TySub (arity (S !! d′)) m)
       → arity (S !! d) ≡ 0 → type (S !! d) ⟨ τ ⟩ ≡ type (S !! d′) ⟨ τ′ ⟩
  mono {d = d} refl τ τ′ a0 = ⟨⟩-cong (type (S !! d)) λ i _ → ⊥-elim (fin0 a0 i)

module Modes {m} (Δ : KCtx m) where
  Syn : ∀ {n} → Locals m n → Expr → Ty m → _ → Set
  Syn = _⊢_⇒_↝_ Δ
  Dom : ∀ {n} → Locals m n → Expr → Ty m → Purity → Ty m → _ → Set
  Dom = _⊢_⇐_⇒[_]↦_↝_ Δ

  module _ where
    ∋-unique : ∀ {n} {L : Locals m n} {x A A′ i i′} → L ∋ x ⦂ A at i → L ∋ x ⦂ A′ at i′ → A ≡ A′
    ∋-unique here         here         = refl
    ∋-unique here         (there ne _) = ⊥-elim (ne refl)
    ∋-unique (there ne _) here         = ⊥-elim (ne refl)
    ∋-unique (there _ p)  (there _ q)  = ∋-unique p q

    -- Forms that never synthesize.
    noSyn-compose : ∀ {n} {L : Locals m n} {f g T t} → ¬ Syn L (RApp (RApp (RResolved (gen "compose")) f) g) T t
    noSyn-compose (s-app h _ _)        = h sh-compose
    noSyn-compose (s-effApp h _ _ _)   = h sh-compose
    noSyn-compose (s-app-spine h _ _)  = h sh-compose

    noSyn-case : ∀ {n} {L : Locals m n} {f g T t} → ¬ Syn L (RApp (RApp (RResolved (gen "case")) f) g) T t
    noSyn-case (s-app h _ _)        = h sh-case
    noSyn-case (s-effApp h _ _ _)   = h sh-case
    noSyn-case (s-app-spine h _ _)  = h sh-case

    noSyn-pair : ∀ {n} {L : Locals m n} {f g T t} → ¬ Syn L (RApp (RApp (RResolved (gen "pair")) f) g) T t
    noSyn-pair (s-app h _ _)        = h sh-pair
    noSyn-pair (s-effApp h _ _ _)   = h sh-pair
    noSyn-pair (s-app-spine h _ _)  = h sh-pair

    noSyn-cata : ∀ {n} {L : Locals m n} {a T t} → ¬ Syn L (RApp (RResolved (gen "cata")) a) T t
    noSyn-cata (s-app h _ _)        = h (sh-gen scata)
    noSyn-cata (s-effApp h _ _ _)   = h (sh-gen scata)
    noSyn-cata (s-app-spine h _ _)  = h (sh-gen scata)

    effPure : ∀ {π} → EffGrade π → π ≡ pure → ⊥
    effPure eg-act ()
    effPure eg-eff ()

    ⊑pure : ∀ {π} → π ⊑π pure → π ≡ pure
    ⊑pure ⊑-pure = refl

    Int≢Float : _≡_ {A = Ty m} Int Float → ⊥
    Int≢Float ()

    noLam : ∀ {n} {L : Locals m n} {x b T t} → ¬ Syn L (RLam x b) T t
    noLam ()

    ia≢cmp : ∀ {op p p′} → IntArith op p → Compare op p′ → ⊥
    ia≢cmp ia-add ()
    ia≢cmp ia-sub ()
    ia≢cmp ia-mul ()
    ia≢cmp ia-div ()
    ia≢cmp ia-mod ()

    fa≢cmp : ∀ {op p p′} → FloatArith op p → Compare op p′ → ⊥
    fa≢cmp fa-add ()
    fa≢cmp fa-sub ()
    fa≢cmp fa-mul ()
    fa≢cmp fa-div ()

    -- A polymorphic definition at a domain: its codomain's variables all occur
    -- in its domain, so the domain fixes the instance there.
    poly-step : ∀ {a} {sd sd′ sc sc′ : Ty a} {A B B′} → sd ≡ sd′ → sc ≡ sc′
              → (∀ i → Occurs i sc → Occurs i sd) → (τ τ′ : TySub a m)
              → sd ⟨ τ ⟩ ≡ A → sd′ ⟨ τ′ ⟩ ≡ A → sc ⟨ τ ⟩ ≡ B → sc′ ⟨ τ′ ⟩ ≡ B′ → B ≡ B′
    poly-step {sc = sc} refl refl occ τ τ′ sdA sdA′ scB scB′ =
      trans (sym scB) (trans (⟨⟩-cong sc λ i o → occ-det (trans sdA (sym sdA′)) (occ i o)) scB′)

    poly-exact : ∀ {d d′} → d ≡ d′ → ∀ {sd sc π₁ sd′ sc′ π₂ A B B′}
               → type (S !! d) ≡ sd ⇒⟨ π₁ ⟩ sc → type (S !! d′) ≡ sd′ ⇒⟨ π₂ ⟩ sc′
               → (∀ i → Occurs i sc → Occurs i sd)
               → (τ : TySub (arity (S !! d)) m) (τ′ : TySub (arity (S !! d′)) m)
               → sd ⟨ τ ⟩ ≡ A → sd′ ⟨ τ′ ⟩ ≡ A → sc ⟨ τ ⟩ ≡ B → sc′ ⟨ τ′ ⟩ ≡ B′ → B ≡ B′
    poly-exact refl ty ty′ occ τ τ′ sdA sdA′ scB scB′ =
      let e = ⇒-inj (trans (sym ty) ty′) in poly-step (proj₁ e) (proj₂ (proj₂ e)) occ τ τ′ sdA sdA′ scB scB′

