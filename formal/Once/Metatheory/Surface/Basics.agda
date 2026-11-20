{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Surface.Basics — the surface metatheory's lemmas that need
-- no assumption on names: the generator table's kinds, type injectivity and
-- substitution read back at its variables, and the forms that never
-- synthesize (`Metatheory.Surface` adds the ones distinct names give).
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Name using (CanonicalName)

module Once.Metatheory.Surface.Basics (Σ : Signature) {s} (S : Defs s) (nm : Fin s → CanonicalName) where


open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Purity; pure; mk-kind; _⊑π_; ⊑-pure; EffGrade; eg-act; eg-eff)
open import Once.Spec.Surface.Generators
  using (kind; IsConstant; IsMap; IsCombinator; FromDomain; FromCodomain; Constant;
         is-constant; is-map; is-combinator; fd-domain; fd-both; fc-codomain; fc-both; k-unit; k-toFloat)
open import Once.Spec.Type
  using (Ty; KCtx; TySub; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; _⟨_⟩; _⟨_⟩F; Occurs; OccursF;
         o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ˡ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ;
         Fun; K; Id; _⊕_; _⊗_)
open import Once.Spec.Core.Syntax using (_!!_; module Schema)
open Schema using (arity; type)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Typing Σ S nm

open import Once.Spec.Theory using (NumTy; int; float; ⌜_⌝ⁿ)


------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

module _ where
  -- The kinds are disjoint classes.
  const-map : ∀ {k} → IsConstant k → IsMap k → ⊥
  const-map is-constant ()

  map-comb : ∀ {k n} → IsMap k → IsCombinator n k → ⊥
  map-comb is-map ()

  comb-12 : ∀ {k} → IsCombinator 1 k → IsCombinator 2 k → ⊥
  comb-12 is-combinator ()

  fd-map : ∀ {k} → FromDomain k → IsMap k
  fd-map fd-domain = is-map
  fd-map fd-both   = is-map

  fc-map : ∀ {k} → FromCodomain k → IsMap k
  fc-map fc-codomain = is-map
  fc-map fc-both     = is-map

  -- Arity facts.
  fin0 : ∀ {n} → n ≡ 0 → Fin n → ⊥
  fin0 refl ()

  0<0 : ∀ {n} → n ≡ 0 → ¬ (0 < n)
  0<0 refl ()

------------------------------------------------------------------------
-- Types: injectivity, and substitution read back at the variables it uses
------------------------------------------------------------------------

module _ where
  -- A number type is named by one type.
  ⌜⌝ⁿ-inj : ∀ {m} {a b : NumTy} → _≡_ {A = Ty m} ⌜ a ⌝ⁿ ⌜ b ⌝ⁿ → a ≡ b
  ⌜⌝ⁿ-inj {a = int}   {int}   _ = refl
  ⌜⌝ⁿ-inj {a = int}   {float} ()
  ⌜⌝ⁿ-inj {a = float} {int}   ()
  ⌜⌝ⁿ-inj {a = float} {float} _ = refl

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

    -- A constant of the table has one type.
    const-unique : ∀ {n′} {g k k′ T T′} {t t′ : Once.Spec.Core.Syntax.Tm S m n′}
                 → Constant Δ g k T t → Constant Δ g k′ T′ t′ → T ≡ T′
    const-unique k-unit    k-unit    = refl
    const-unique k-toFloat k-toFloat = refl

    -- Forms that never synthesize: a structure map, and a combinator given
    -- its arms.
    noSyn-map : ∀ {n} {L : Locals m n} {g T t} → IsMap (kind g) → ¬ Syn L (RGen g) T t
    noSyn-map im (s-const {k = k} _) = const-map k im

    noSyn-comb₁ : ∀ {n} {L : Locals m n} {g a T t} → IsCombinator 1 (kind g) → ¬ Syn L (RApp (RGen g) a) T t
    noSyn-comb₁ ic (s-app pc _ _ _)              = pc (pc-bare ic)
    noSyn-comb₁ ic (s-app-spine (ch-map im) _ _) = map-comb im ic

    noSyn-comb₂ : ∀ {n} {L : Locals m n} {g f h T t} → IsCombinator 2 (kind g) → ¬ Syn L (RApp (RApp (RGen g) f) h) T t
    noSyn-comb₂ ic (s-app pc _ _ _)                 = pc (pc-one ic)
    noSyn-comb₂ ic (s-app-spine (ch-comb₁ ic₁) _ _) = comb-12 ic₁ ic

    effPure : ∀ {π} → EffGrade π → π ≡ pure → ⊥
    effPure eg-act ()
    effPure eg-eff ()

    ⊑pure : ∀ {π} → π ⊑π pure → π ≡ pure
    ⊑pure ⊑-pure = refl

    Int≢Float : _≡_ {A = Ty m} Int Float → ⊥
    Int≢Float ()

    noLam : ∀ {n} {L : Locals m n} {x b T t} → ¬ Syn L (RLam x b) T t
    noLam ()

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

