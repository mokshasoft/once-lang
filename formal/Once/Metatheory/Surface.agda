{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Surface — the surface judgment's modes agree
-- (`Spec.Metatheory.Surface`).
--
-- Under distinct names (`Distinct`, D249) every expression form has one
-- synthesis rule, or several whose premises fix the same type; the
-- domain-given mode is exact; and where an expression both synthesizes and
-- checks against a domain, the two agree. One induction on the first
-- derivation, the three statements mutually.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Metatheory using (Distinct)

module Once.Metatheory.Surface (Σ : Signature) {s} (S : Defs s) (nm : Fin s → CanonicalName)
                               (dist : Distinct Σ nm) where

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
open import Once.Spec.Metatheory using (Surface)

open Distinct dist
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
  def-gen : ∀ d {w} → w ∈ genNames → nm d ≢ gen w
  def-gen d m e = notGen m (subst NotGenerator e (def-not-gen d))

  def-sig : ∀ d {c t} → nm d ≡ c → ¬ ((c ∶ t) ∈ Σ)
  def-sig d refl = def-not-sig d

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

------------------------------------------------------------------------
-- The modes
------------------------------------------------------------------------

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
    noSyn-gen : ∀ {n} {L : Locals m n} {w T t} → w ∈ genNames → w ≢ "unit" → ¬ Syn L (RResolved (gen w)) T t
    noSyn-gen m₁ nu s-unit-g         = nu refl
    noSyn-gen m₁ nu (s-sigop ng _)   = notGen m₁ ng
    noSyn-gen m₁ nu (s-def d e _ _)  = def-gen d m₁ e

    noSyn-poly : ∀ {n} {L : Locals m n} {c T t} (d : Fin s) → nm d ≡ c → 0 < arity (S !! d) → ¬ Syn L (RResolved c) T t
    noSyn-poly d e lt s-unit-g          = def-gen d unit∈ e
    noSyn-poly d e lt (s-sigop _ mem)   = def-sig d e mem
    noSyn-poly d e lt (s-def d′ e′ _ a0) = 0<0 (subst (λ x → arity (S !! x) ≡ 0) (sym (def-inj (trans e (sym e′)))) a0) lt

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

  synth-unique : ∀ {n} {L : Locals m n} {e A A′ t t′} → Syn L e A t → Syn L e A′ t′ → A ≡ A′
  domain-exact : ∀ {n} {L : Locals m n} {e A π B B′ t t′} → Dom L e A π B t → Dom L e A π B′ t′ → B ≡ B′
  agree        : ∀ {n} {L : Locals m n} {e A π B T t t′} → Dom L e A π B t → Syn L e T t′
               → Σ[ A′ ∈ Ty m ] Σ[ π′ ∈ Purity ] (T ≡ A′ ⇒[ mk-kind Many π′ ] B) × π′ ⊑π π

  -- the helpers that carry an equality of types into a binder
  private
    under   : ∀ {n} {L : Locals m n} {x A A′ e B B′ t t′} → A ≡ A′
            → Syn (L ▹ x ∶ A) e B t → Syn (L ▹ x ∶ A′) e B′ t′ → B ≡ B′
    domUnder : ∀ {n} {L : Locals m n} {e A A′ π B B′ t t′} → A ≡ A′
             → Dom L e A π B t → Dom L e A′ π B′ t′ → B ≡ B′
    -- two joins of equal pairs are equal
    joinUnder : ∀ {A A′ B B′ C C′ : Ty m} → A ≡ A′ → B ≡ B′ → A ⊔ B ≔ C → A′ ⊔ B′ ≔ C′ → C ≡ C′

  under refl d d′ = synth-unique d d′
  joinUnder refl refl j j′ = join-unique j j′
  domUnder refl d d′ = domain-exact d d′

  -- Synthesis.
  synth-unique (s-int i)     (s-int .i)      = refl
  synth-unique (s-float i f l) (s-float .i .f .l) = refl
  synth-unique s-unit        s-unit          = refl
  synth-unique s-unit-g      s-unit-g        = refl
  synth-unique s-unit-g      (s-sigop ng _)  = ⊥-elim (notGen unit∈ ng)
  synth-unique s-unit-g      (s-def d e _ _) = ⊥-elim (def-gen d unit∈ e)
  synth-unique (s-var p)     (s-var q)       = ∋-unique p q
  synth-unique (s-sigop _ m₁) (s-sigop _ m₂) = cong ⌜_⌝ᵈ (decl-unique one-name m₁ m₂)
  synth-unique (s-sigop ng _) s-unit-g       = ⊥-elim (notGen unit∈ ng)
  synth-unique (s-sigop _ mem) (s-def d e _ _) = ⊥-elim (def-sig d e mem)
  synth-unique (s-def d e τ a0) (s-def d′ e′ τ′ _) = mono (def-inj (trans e (sym e′))) τ τ′ a0
  synth-unique (s-def d e _ _) s-unit-g        = ⊥-elim (def-gen d unit∈ e)
  synth-unique (s-def d e _ _) (s-sigop _ mem) = ⊥-elim (def-sig d e mem)
  synth-unique (s-annot _)   (s-annot _)     = refl
  synth-unique (s-pair a b)  (s-pair a′ b′)  = cong₂ _*_ (synth-unique a a′) (synth-unique b b′)
  synth-unique (s-neg _)     (s-neg _)       = refl
  synth-unique (s-neg ())    (s-neg-float _ _ _)
  synth-unique (s-neg-float _ _ _) (s-neg ())
  synth-unique (s-neg-float _ _ _) (s-neg-float _ _ _) = refl
  synth-unique (s-let q d₁ d₂) (s-let q′ d₁′ d₂′) = under (synth-unique d₁ d₁′) d₂ d₂′
  synth-unique (s-case ql qr ds dl dr j) (s-case ql′ qr′ ds′ dl′ dr′ j′) =
    joinUnder (under (proj₁ (+-inj (synth-unique ds ds′))) dl dl′)
              (under (proj₂ (+-inj (synth-unique ds ds′))) dr dr′) j j′
  -- arithmetic: the operand types decide the rule
  synth-unique (s-arith _ _ _)          (s-arith _ _ _)          = refl
  synth-unique (s-arith _ a _)          (s-arith-float _ a′ _)   = ⊥-elim (Int≢Float (synth-unique a a′))
  synth-unique (s-arith _ _ b)          (s-arith-float-il _ _ b′) = ⊥-elim (Int≢Float (synth-unique b b′))
  synth-unique (s-arith _ a _)          (s-arith-float-ir _ a′ _) = ⊥-elim (Int≢Float (synth-unique a a′))
  synth-unique (s-arith ia _ _)         (s-compare c _ _)        = ⊥-elim (ia≢cmp ia c)
  synth-unique (s-arith-float _ a _)    (s-arith _ a′ _)         = ⊥-elim (Int≢Float (synth-unique a′ a))
  synth-unique (s-arith-float _ _ _)    (s-arith-float _ _ _)    = refl
  synth-unique (s-arith-float _ a _)    (s-arith-float-il _ a′ _) = ⊥-elim (Int≢Float (synth-unique a′ a))
  synth-unique (s-arith-float _ _ b)    (s-arith-float-ir _ _ b′) = ⊥-elim (Int≢Float (synth-unique b′ b))
  synth-unique (s-arith-float fa _ _)   (s-compare c _ _)        = ⊥-elim (fa≢cmp fa c)
  synth-unique (s-arith-float-il _ _ b) (s-arith _ _ b′)         = ⊥-elim (Int≢Float (synth-unique b′ b))
  synth-unique (s-arith-float-il _ a _) (s-arith-float _ a′ _)   = ⊥-elim (Int≢Float (synth-unique a a′))
  synth-unique (s-arith-float-il _ _ _) (s-arith-float-il _ _ _) = refl
  synth-unique (s-arith-float-il _ a _) (s-arith-float-ir _ a′ _) = ⊥-elim (Int≢Float (synth-unique a a′))
  synth-unique (s-arith-float-il fa _ _) (s-compare c _ _)       = ⊥-elim (fa≢cmp fa c)
  synth-unique (s-arith-float-ir _ a _) (s-arith _ a′ _)         = ⊥-elim (Int≢Float (synth-unique a′ a))
  synth-unique (s-arith-float-ir _ _ b) (s-arith-float _ _ b′)   = ⊥-elim (Int≢Float (synth-unique b b′))
  synth-unique (s-arith-float-ir _ a _) (s-arith-float-il _ a′ _) = ⊥-elim (Int≢Float (synth-unique a′ a))
  synth-unique (s-arith-float-ir _ _ _) (s-arith-float-ir _ _ _) = refl
  synth-unique (s-arith-float-ir fa _ _) (s-compare c _ _)       = ⊥-elim (fa≢cmp fa c)
  synth-unique (s-compare c _ _)        (s-arith ia _ _)         = ⊥-elim (ia≢cmp ia c)
  synth-unique (s-compare c _ _)        (s-arith-float fa _ _)   = ⊥-elim (fa≢cmp fa c)
  synth-unique (s-compare c _ _)        (s-arith-float-il fa _ _) = ⊥-elim (fa≢cmp fa c)
  synth-unique (s-compare c _ _)        (s-arith-float-ir fa _ _) = ⊥-elim (fa≢cmp fa c)
  synth-unique (s-compare _ _ _)        (s-compare _ _ _)        = refl
  -- the generators applied
  synth-unique (s-id-app d)       (s-id-app d′)       = synth-unique d d′
  synth-unique (s-fst-app d)      (s-fst-app d′)      = proj₁ (*-inj (synth-unique d d′))
  synth-unique (s-snd-app d)      (s-snd-app d′)      = proj₂ (*-inj (synth-unique d d′))
  synth-unique (s-terminal-app d) (s-terminal-app d′) = refl
  synth-unique (s-apply-app d)    (s-apply-app d′)    = proj₂ (proj₂ (⇒-inj (proj₁ (*-inj (synth-unique d d′)))))
  synth-unique (s-apply-app d)    (s-apply-eff-app g d′) =
    ⊥-elim (effPure g (sym (kind-π (proj₁ (proj₂ (⇒-inj (proj₁ (*-inj (synth-unique d d′)))))))))
  synth-unique (s-apply-eff-app g d) (s-apply-app d′) =
    ⊥-elim (effPure g (kind-π (proj₁ (proj₂ (⇒-inj (proj₁ (*-inj (synth-unique d d′))))))))
  synth-unique (s-apply-eff-app g d) (s-apply-eff-app g′ d′) =
    let e = ⇒-inj (proj₁ (*-inj (synth-unique d d′)))
    in cong₂ (λ π B → Unit ⇒[ mk-kind Many π ] B) (kind-π (proj₁ (proj₂ e))) (proj₂ (proj₂ e))
  synth-unique (s-Out-app _ d)     (s-Out-app _ d′)     = cong (λ F → ⟦ F ⟧F (ν F pureᶠ)) (proj₁ (ν-inj (synth-unique d d′)))
  synth-unique (s-Out-app _ d)     (s-Out-act-app _ d′) = ⊥-elim (pa (proj₂ (ν-inj (synth-unique d d′))))
    where pa : pureᶠ ≡ actᶠ → ⊥
          pa ()
  synth-unique (s-Out-act-app _ d) (s-Out-app _ d′)     = ⊥-elim (ap (proj₂ (ν-inj (synth-unique d d′))))
    where ap : actᶠ ≡ pureᶠ → ⊥
          ap ()
  synth-unique (s-Out-act-app _ d) (s-Out-act-app _ d′) =
    cong (λ F → Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (ν F actᶠ)) (proj₁ (ν-inj (synth-unique d d′)))
  -- an ordinary application: the function's type decides
  synth-unique (s-app _ df _) (s-app _ df′ _) = proj₂ (proj₂ (⇒-inj (synth-unique df df′)))
  synth-unique (s-app _ df _) (s-effApp _ g df′ _) =
    ⊥-elim (effPure g (sym (kind-π (proj₁ (proj₂ (⇒-inj (synth-unique df df′)))))))
  synth-unique (s-app _ df _) (s-app-spine _ _ dg) =
    let (A′ , π′ , e , _) = agree dg df in proj₂ (proj₂ (⇒-inj e))
  synth-unique (s-effApp _ g df _) (s-app _ df′ _) =
    ⊥-elim (effPure g (kind-π (proj₁ (proj₂ (⇒-inj (synth-unique df df′))))))
  synth-unique (s-effApp _ g df _) (s-effApp _ g′ df′ _) =
    let e = ⇒-inj (synth-unique df df′)
    in cong₂ (λ π B → Unit ⇒[ mk-kind Many π ] B) (kind-π (proj₁ (proj₂ e))) (proj₂ (proj₂ e))
  synth-unique (s-effApp _ g df _) (s-app-spine _ _ dg) =
    let (A′ , π′ , e , p) = agree dg df
    in ⊥-elim (effPure g (trans (kind-π (proj₁ (proj₂ (⇒-inj e)))) (⊑pure p)))
  synth-unique (s-app-spine _ _ dg) (s-app _ df _) =
    let (A′ , π′ , e , _) = agree dg df in sym (proj₂ (proj₂ (⇒-inj e)))
  synth-unique (s-app-spine _ _ dg) (s-effApp _ g df _) =
    let (A′ , π′ , e , p) = agree dg df
    in ⊥-elim (effPure g (trans (kind-π (proj₁ (proj₂ (⇒-inj e)))) (⊑pure p)))
  synth-unique (s-app-spine _ dx dg) (s-app-spine _ dx′ dg′) = domUnder (synth-unique dx dx′) dg dg′
  -- a special head never takes the ordinary rules
  synth-unique (s-id-app _)       (s-app h _ _)        = ⊥-elim (h (sh-gen sid))
  synth-unique (s-id-app _)       (s-effApp h _ _ _)   = ⊥-elim (h (sh-gen sid))
  synth-unique (s-id-app _)       (s-app-spine h _ _)  = ⊥-elim (h (sh-gen sid))
  synth-unique (s-fst-app _)      (s-app h _ _)        = ⊥-elim (h (sh-gen sfst))
  synth-unique (s-fst-app _)      (s-effApp h _ _ _)   = ⊥-elim (h (sh-gen sfst))
  synth-unique (s-fst-app _)      (s-app-spine h _ _)  = ⊥-elim (h (sh-gen sfst))
  synth-unique (s-snd-app _)      (s-app h _ _)        = ⊥-elim (h (sh-gen ssnd))
  synth-unique (s-snd-app _)      (s-effApp h _ _ _)   = ⊥-elim (h (sh-gen ssnd))
  synth-unique (s-snd-app _)      (s-app-spine h _ _)  = ⊥-elim (h (sh-gen ssnd))
  synth-unique (s-terminal-app _) (s-app h _ _)        = ⊥-elim (h (sh-gen sterminal))
  synth-unique (s-terminal-app _) (s-effApp h _ _ _)   = ⊥-elim (h (sh-gen sterminal))
  synth-unique (s-terminal-app _) (s-app-spine h _ _)  = ⊥-elim (h (sh-gen sterminal))
  synth-unique (s-apply-app _)    (s-app h _ _)        = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-apply-app _)    (s-effApp h _ _ _)   = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-apply-app _)    (s-app-spine h _ _)  = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-apply-eff-app _ _) (s-app h _ _)       = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-apply-eff-app _ _) (s-effApp h _ _ _)  = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-apply-eff-app _ _) (s-app-spine h _ _) = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-Out-app _ _)    (s-app h _ _)        = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-Out-app _ _)    (s-effApp h _ _ _)   = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-Out-app _ _)    (s-app-spine h _ _)  = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-Out-act-app _ _) (s-app h _ _)       = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-Out-act-app _ _) (s-effApp h _ _ _)  = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-Out-act-app _ _) (s-app-spine h _ _) = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-app h _ _)        (s-id-app _)          = ⊥-elim (h (sh-gen sid))
  synth-unique (s-app h _ _)        (s-fst-app _)         = ⊥-elim (h (sh-gen sfst))
  synth-unique (s-app h _ _)        (s-snd-app _)         = ⊥-elim (h (sh-gen ssnd))
  synth-unique (s-app h _ _)        (s-terminal-app _)    = ⊥-elim (h (sh-gen sterminal))
  synth-unique (s-app h _ _)        (s-apply-app _)       = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-app h _ _)        (s-apply-eff-app _ _) = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-app h _ _)        (s-Out-app _ _)       = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-app h _ _)        (s-Out-act-app _ _) = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-effApp h _ _ _)   (s-id-app _)          = ⊥-elim (h (sh-gen sid))
  synth-unique (s-effApp h _ _ _)   (s-fst-app _)         = ⊥-elim (h (sh-gen sfst))
  synth-unique (s-effApp h _ _ _)   (s-snd-app _)         = ⊥-elim (h (sh-gen ssnd))
  synth-unique (s-effApp h _ _ _)   (s-terminal-app _)    = ⊥-elim (h (sh-gen sterminal))
  synth-unique (s-effApp h _ _ _)   (s-apply-app _)       = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-effApp h _ _ _)   (s-apply-eff-app _ _) = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-effApp h _ _ _)   (s-Out-app _ _)       = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-effApp h _ _ _)   (s-Out-act-app _ _) = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-app-spine h _ _)  (s-id-app _)          = ⊥-elim (h (sh-gen sid))
  synth-unique (s-app-spine h _ _)  (s-fst-app _)         = ⊥-elim (h (sh-gen sfst))
  synth-unique (s-app-spine h _ _)  (s-snd-app _)         = ⊥-elim (h (sh-gen ssnd))
  synth-unique (s-app-spine h _ _)  (s-terminal-app _)    = ⊥-elim (h (sh-gen sterminal))
  synth-unique (s-app-spine h _ _)  (s-apply-app _)       = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-app-spine h _ _)  (s-apply-eff-app _ _) = ⊥-elim (h (sh-gen sapply))
  synth-unique (s-app-spine h _ _)  (s-Out-app _ _)       = ⊥-elim (h (sh-gen sOut))
  synth-unique (s-app-spine h _ _)  (s-Out-act-app _ _) = ⊥-elim (h (sh-gen sOut))

  -- The domain-given mode.
  domain-exact (d-infer dg _ _) (d-infer dg′ _ _) = proj₂ (proj₂ (⇒-inj (synth-unique dg dg′)))
  domain-exact (d-infer dg _ _) (d-poly d e lt _ _ _ _ _ _ _) = ⊥-elim (noSyn-poly d e lt dg)
  domain-exact (d-infer dg _ _) (d-lam _)        = ⊥-elim (noLam dg)
  domain-exact (d-infer dg _ _) (d-compose _ _)    = ⊥-elim (noSyn-compose dg)
  domain-exact (d-infer dg _ _) d-id           = ⊥-elim (noSyn-gen id∈ (λ ()) dg)
  domain-exact (d-infer dg _ _) d-fst          = ⊥-elim (noSyn-gen fst∈ (λ ()) dg)
  domain-exact (d-infer dg _ _) d-snd          = ⊥-elim (noSyn-gen snd∈ (λ ()) dg)
  domain-exact (d-infer dg _ _) d-terminal     = ⊥-elim (noSyn-gen terminal∈ (λ ()) dg)
  domain-exact (d-infer dg _ _) d-initial      = ⊥-elim (noSyn-gen initial∈ (λ ()) dg)
  domain-exact (d-infer dg _ _) (d-case _ _ _)       = ⊥-elim (noSyn-case dg)
  domain-exact (d-infer dg _ _) (d-pair _ _)       = ⊥-elim (noSyn-pair dg)
  domain-exact (d-infer dg _ _) (d-cata _ _)     = ⊥-elim (noSyn-cata dg)
  domain-exact (d-poly d e lt _ _ _ _ _ _ _) (d-infer dg _ _) = ⊥-elim (noSyn-poly d e lt dg)
  domain-exact (d-poly d e _ ty occ τ _ sdA scB _) (d-poly d′ e′ _ ty′ _ τ′ _ sdA′ scB′ _) =
    poly-exact (def-inj (trans e (sym e′))) ty ty′ occ τ τ′ sdA sdA′ scB scB′
  domain-exact (d-poly d e _ _ _ _ _ _ _ _) d-id       = ⊥-elim (def-gen d id∈ e)
  domain-exact (d-poly d e _ _ _ _ _ _ _ _) d-fst      = ⊥-elim (def-gen d fst∈ e)
  domain-exact (d-poly d e _ _ _ _ _ _ _ _) d-snd      = ⊥-elim (def-gen d snd∈ e)
  domain-exact (d-poly d e _ _ _ _ _ _ _ _) d-terminal = ⊥-elim (def-gen d terminal∈ e)
  domain-exact (d-poly d e _ _ _ _ _ _ _ _) d-initial  = ⊥-elim (def-gen d initial∈ e)
  domain-exact d-id       (d-poly d e _ _ _ _ _ _ _ _) = ⊥-elim (def-gen d id∈ e)
  domain-exact d-fst      (d-poly d e _ _ _ _ _ _ _ _) = ⊥-elim (def-gen d fst∈ e)
  domain-exact d-snd      (d-poly d e _ _ _ _ _ _ _ _) = ⊥-elim (def-gen d snd∈ e)
  domain-exact d-terminal (d-poly d e _ _ _ _ _ _ _ _) = ⊥-elim (def-gen d terminal∈ e)
  domain-exact d-initial  (d-poly d e _ _ _ _ _ _ _ _) = ⊥-elim (def-gen d initial∈ e)
  domain-exact (d-lam b)    (d-lam b′)       = synth-unique b b′
  domain-exact (d-lam _)    (d-infer dg _ _)   = ⊥-elim (noLam dg)
  domain-exact (d-compose dg df) (d-compose dg′ df′) = domUnder (domain-exact dg dg′) df df′
  domain-exact (d-compose _ _) (d-infer dg _ _)  = ⊥-elim (noSyn-compose dg)
  domain-exact d-id       d-id           = refl
  domain-exact d-id       (d-infer dg _ _)   = ⊥-elim (noSyn-gen id∈ (λ ()) dg)
  domain-exact d-fst      d-fst          = refl
  domain-exact d-fst      (d-infer dg _ _)   = ⊥-elim (noSyn-gen fst∈ (λ ()) dg)
  domain-exact d-snd      d-snd          = refl
  domain-exact d-snd      (d-infer dg _ _)   = ⊥-elim (noSyn-gen snd∈ (λ ()) dg)
  domain-exact d-terminal d-terminal     = refl
  domain-exact d-terminal (d-infer dg _ _)   = ⊥-elim (noSyn-gen terminal∈ (λ ()) dg)
  domain-exact d-initial  d-initial      = refl
  domain-exact d-initial  (d-infer dg _ _)   = ⊥-elim (noSyn-gen initial∈ (λ ()) dg)
  domain-exact (d-case df dg j) (d-case df′ dg′ j′) = joinUnder (domain-exact df df′) (domain-exact dg dg′) j j′
  domain-exact (d-case _ _ _)   (d-infer dg _ _)   = ⊥-elim (noSyn-case dg)
  domain-exact (d-pair df dg) (d-pair df′ dg′)   = cong₂ _*_ (domain-exact df df′) (domain-exact dg dg′)
  domain-exact (d-pair _ _)   (d-infer dg _ _)   = ⊥-elim (noSyn-pair dg)
  domain-exact (d-cata _ da) (d-cata _ da′)  = proj₂ (proj₂ (⇒-inj (synth-unique da da′)))
  domain-exact (d-cata _ _) (d-infer dg _ _)   = ⊥-elim (noSyn-cata dg)

  -- Both modes at once.
  agree (d-infer dg _ p) s = _ , _ , synth-unique s dg , p
  agree (d-poly d e lt _ _ _ _ _ _ _) s = ⊥-elim (noSyn-poly d e lt s)
  agree (d-lam _) ()
  agree (d-compose _ _) s = ⊥-elim (noSyn-compose s)
  agree d-id        s = ⊥-elim (noSyn-gen id∈ (λ ()) s)
  agree d-fst       s = ⊥-elim (noSyn-gen fst∈ (λ ()) s)
  agree d-snd       s = ⊥-elim (noSyn-gen snd∈ (λ ()) s)
  agree d-terminal  s = ⊥-elim (noSyn-gen terminal∈ (λ ()) s)
  agree d-initial   s = ⊥-elim (noSyn-gen initial∈ (λ ()) s)
  agree (d-case _ _ _)    s = ⊥-elim (noSyn-case s)
  agree (d-pair _ _)    s = ⊥-elim (noSyn-pair s)
  agree (d-cata _ _)  s = ⊥-elim (noSyn-cata s)

surface : Surface Σ S nm
surface = record
  { synth-unique        = λ {m} {Δ} → Modes.synth-unique Δ
  ; domain-exact        = λ {m} {Δ} → Modes.domain-exact Δ
  ; domain-agrees-synth = λ {m} {Δ} → Modes.agree Δ
  }
