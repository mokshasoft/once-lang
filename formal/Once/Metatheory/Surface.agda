{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Surface — the surface judgment's modes agree
-- (`Spec.Metatheory.Surface`).
--
-- Under distinct names (`Distinct`, D249) each expression form has one rule
-- per mode (`one-rule`), read from the form; synthesis is unique; the
-- domain-given mode is exact; and where an expression both synthesizes and
-- checks against a domain, the two agree. One induction on the first
-- derivation, the uniqueness statements mutually.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Metatheory using (Distinct)

module Once.Metatheory.Surface (Σ : Signature) {s} (S : Defs s) (nm : Fin s → CanonicalName)
                               (dist : Distinct Σ nm) where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Purity; Many; mk-kind; _⊑π_)
open import Once.Spec.Surface.Generators
  using (is-combinator)
open import Once.Spec.Core.Derived using (𝕋)
open import Once.Metatheory.Types using (<:-antisym; <:ᶜ⇒<:)
open import Once.Spec.Type
  using (Ty; KCtx; _*_; _⇒[_]_)
open import Once.Spec.Signature using (_∶_; ⌜_⌝ᵈ)
open import Once.Spec.Core.Syntax using (_!!_; module Schema)
open Schema using (arity)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Typing Σ S nm
open import Once.Spec.Metatheory using (Surface)

open Distinct dist
import Once.Metatheory.Surface.Basics Σ S nm as B
open B hiding (module Modes)
open import Once.Metatheory.OneName using (decl-unique)
open import Once.Spec.Theory using (symCod)
open import Once.Spec.Surface.Operator using (binSym; BinSym)
open BinSym using (shape)
open import Once.Metatheory.Types using (join-unique)
open import Once.Spec.Sub using (_⊔_≔_)

------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

module _ where
  def-sig : ∀ d {c t} → nm d ≡ c → ¬ ((c ∶ t) ∈ Σ)
  def-sig d refl = def-not-sig d


------------------------------------------------------------------------
-- The modes
------------------------------------------------------------------------

module Modes {m} (Δ : KCtx m) where
  Syn : ∀ {n} → Locals m n → Expr → Ty m → _ → Set
  Syn = _⊢_⇒_↝_ Δ
  Chk : ∀ {n} → Locals m n → Expr → Ty m → _ → Set
  Chk = _⊢_⇐_↝_ Δ
  Dom : ∀ {n} → Locals m n → Expr → Ty m → Purity → Ty m → _ → Set
  Dom = _⊢_⇐_⇒[_]↦_↝_ Δ

  open B.Modes Δ hiding (Syn; Dom)

  module _ where
    noSyn-poly : ∀ {n} {L : Locals m n} {c T t} (d : Fin s) → nm d ≡ c → 0 < arity (S !! d) → ¬ Syn L (RResolved c) T t
    noSyn-poly d e lt (s-sigop mem)      = def-sig d e mem
    noSyn-poly d e lt (s-def d′ e′ _ a0) = 0<0 (subst (λ x → arity (S !! x) ≡ 0) (sym (def-inj (trans e (sym e′)))) a0) lt

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
  synth-unique (s-float _ _ _ _) (s-float _ _ _ _) = refl
  synth-unique s-unit        s-unit          = refl
  synth-unique (s-const c)   (s-const c′)    = const-unique c c′
  synth-unique (s-var p)     (s-var q)       = ∋-unique p q
  synth-unique (s-sigop m₁)  (s-sigop m₂)    = cong ⌜_⌝ᵈ (decl-unique one-name m₁ m₂)
  synth-unique (s-sigop mem) (s-def d e _ _) = ⊥-elim (def-sig d e mem)
  synth-unique (s-def d e τ a0) (s-def d′ e′ τ′ _) = mono (def-inj (trans e (sym e′))) τ τ′ a0
  synth-unique (s-def d e _ _) (s-sigop mem) = ⊥-elim (def-sig d e mem)
  synth-unique (s-annot _)   (s-annot _)     = refl
  synth-unique (s-pair a b)  (s-pair a′ b′)  = cong₂ _*_ (synth-unique a a′) (synth-unique b b′)
  synth-unique (s-neg _ a)   (s-neg _ a′)    = synth-unique a a′
  synth-unique (s-binop {op = op} _ a _) (s-binop _ a′ _) =
    cong (λ X → symCod X (shape (binSym op))) (⌜⌝ⁿ-inj (synth-unique a a′))
  synth-unique (s-let q d₁ d₂) (s-let q′ d₁′ d₂′) = under (synth-unique d₁ d₁′) d₂ d₂′
  synth-unique (s-case ql qr ds dl dr j) (s-case ql′ qr′ ds′ dl′ dr′ j′) =
    joinUnder (under (proj₁ (+-inj (synth-unique ds ds′))) dl dl′)
              (under (proj₂ (+-inj (synth-unique ds ds′))) dr dr′) j j′
  -- an application: the head's type decides, its grade picks `𝕋`
  synth-unique (s-app _ _ df _) (s-app _ _ df′ _) =
    let e = ⇒-inj (synth-unique df df′) in cong₂ 𝕋 (kind-π (proj₁ (proj₂ e))) (proj₂ (proj₂ e))
  synth-unique (s-app _ ch _ _) (s-app-spine ch′ _ _) = ⊥-elim (ch ch′)
  synth-unique (s-app-spine ch _ _) (s-app _ ch′ _ _) = ⊥-elim (ch′ ch)
  synth-unique (s-app-spine _ dx dg) (s-app-spine _ dx′ dg′) = domUnder (synth-unique dx dx′) dg dg′

  -- The domain-given mode.
  domain-exact (d-infer dg _ _) (d-infer dg′ _ _) = proj₂ (proj₂ (⇒-inj (synth-unique dg dg′)))
  domain-exact (d-infer dg _ _) d′@(d-poly _ _ _ _ _ _ _ _ _ _) = proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d′ dg))))))
  domain-exact (d-infer dg _ _) d′@(d-lam _) = proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d′ dg))))))
  domain-exact (d-infer dg _ _) d′@(d-map _ _ _) = proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d′ dg))))))
  domain-exact (d-infer dg _ _) d′@(d-compose _ _) = proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d′ dg))))))
  domain-exact (d-infer dg _ _) d′@(d-case _ _ _) = proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d′ dg))))))
  domain-exact (d-infer dg _ _) d′@(d-pair _ _) = proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d′ dg))))))
  domain-exact (d-infer dg _ _) d′@(d-cata _ _ _ _) = proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d′ dg))))))
  domain-exact d@(d-poly _ _ _ _ _ _ _ _ _ _) (d-infer dg′ _ _) = sym (proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d dg′)))))))
  domain-exact d@(d-lam _) (d-infer dg′ _ _) = sym (proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d dg′)))))))
  domain-exact d@(d-map _ _ _) (d-infer dg′ _ _) = sym (proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d dg′)))))))
  domain-exact d@(d-compose _ _) (d-infer dg′ _ _) = sym (proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d dg′)))))))
  domain-exact d@(d-case _ _ _) (d-infer dg′ _ _) = sym (proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d dg′)))))))
  domain-exact d@(d-pair _ _) (d-infer dg′ _ _) = sym (proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d dg′)))))))
  domain-exact d@(d-cata _ _ _ _) (d-infer dg′ _ _) = sym (proj₂ (proj₂ (⇒-inj (proj₁ (proj₂ (proj₂ (agree d dg′)))))))
  domain-exact (d-poly d e _ ty occ τ _ sdA scB _) (d-poly d′ e′ _ ty′ _ τ′ _ sdA′ scB′ _) =
    poly-exact (def-inj (trans e (sym e′))) ty ty′ occ τ τ′ sdA sdA′ scB scB′
  domain-exact (d-lam b)    (d-lam b′)       = synth-unique b b′
  domain-exact (d-map _ mo least) (d-map _ mo′ least′) = <:-antisym (<:ᶜ⇒<: (least mo′)) (<:ᶜ⇒<: (least′ mo))
  domain-exact (d-compose dg df) (d-compose dg′ df′) = domUnder (domain-exact dg dg′) df df′
  domain-exact (d-case df dg j) (d-case df′ dg′ j′) = joinUnder (domain-exact df df′) (domain-exact dg dg′) j j′
  domain-exact (d-pair df dg) (d-pair df′ dg′)   = cong₂ _*_ (domain-exact df df′) (domain-exact dg dg′)
  domain-exact (d-cata _ da _ _) (d-cata _ da′ _ _) = proj₂ (proj₂ (⇒-inj (synth-unique da da′)))

  -- Both modes at once: only `d-infer` synthesizes.
  agree (d-infer dg _ p) s = _ , _ , synth-unique s dg , p
  agree (d-poly d e lt _ _ _ _ _ _ _) s = ⊥-elim (noSyn-poly d e lt s)
  agree (d-lam _) ()
  agree (d-map fd _ _)  s = ⊥-elim (noSyn-map (fd-map fd) s)
  agree (d-compose _ _) s = ⊥-elim (noSyn-comb₂ is-combinator s)
  agree (d-case _ _ _)  s = ⊥-elim (noSyn-comb₂ is-combinator s)
  agree (d-pair _ _)    s = ⊥-elim (noSyn-comb₂ is-combinator s)
  agree (d-cata _ _ _ _) s = ⊥-elim (noSyn-comb₁ is-combinator s)

  -- One rule per form and mode, whatever the types.
  one-rule⇒ : ∀ {n} {L : Locals m n} {e A A′ t t′} (d : Syn L e A t) (d′ : Syn L e A′ t′) → ruleOf⇒ d ≡ ruleOf⇒ d′
  one-rule⇒ (s-int _)            (s-int _)            = refl
  one-rule⇒ (s-float _ _ _ _)    (s-float _ _ _ _)    = refl
  one-rule⇒ s-unit               s-unit               = refl
  one-rule⇒ (s-const _)          (s-const _)          = refl
  one-rule⇒ (s-var _)            (s-var _)            = refl
  one-rule⇒ (s-sigop _)          (s-sigop _)          = refl
  one-rule⇒ (s-sigop mem)        (s-def d e _ _)      = ⊥-elim (def-sig d e mem)
  one-rule⇒ (s-def _ _ _ _)      (s-def _ _ _ _)      = refl
  one-rule⇒ (s-def d e _ _)      (s-sigop mem)        = ⊥-elim (def-sig d e mem)
  one-rule⇒ (s-annot _)          (s-annot _)          = refl
  one-rule⇒ (s-pair _ _)         (s-pair _ _)         = refl
  one-rule⇒ (s-neg _ _)          (s-neg _ _)          = refl
  one-rule⇒ (s-let _ _ _)        (s-let _ _ _)        = refl
  one-rule⇒ (s-case _ _ _ _ _ _) (s-case _ _ _ _ _ _) = refl
  one-rule⇒ (s-binop _ _ _)      (s-binop _ _ _)      = refl
  one-rule⇒ (s-app _ _ _ _)      (s-app _ _ _ _)      = refl
  one-rule⇒ (s-app _ ch _ _)     (s-app-spine ch′ _ _) = ⊥-elim (ch ch′)
  one-rule⇒ (s-app-spine ch _ _) (s-app _ ch′ _ _)    = ⊥-elim (ch′ ch)
  one-rule⇒ (s-app-spine _ _ _)  (s-app-spine _ _ _)  = refl

  -- `c-sub` is never the rule of a form with a rule of its own.
  private
    sub-vs : ∀ {n} {L : Locals m n} {e A t} (d : Chk L e A t) {B t′} → ¬ OwnCheck e → Syn L e B t′
           → ruleOf⇐ d ≡ Rule.c-sub
    sub-vs (c-map {k = k} _)         _   s = ⊥-elim (noSyn-map k s)
    sub-vs (c-map-app fc _ _)        noc _ = ⊥-elim (noc (oc-map fc))
    sub-vs (c-compose-g _ _ _)       _   s = ⊥-elim (noSyn-comb₂ is-combinator s)
    sub-vs (c-compose-f _ _ _ _)     _   s = ⊥-elim (noSyn-comb₂ is-combinator s)
    sub-vs (c-case _ _)              _   s = ⊥-elim (noSyn-comb₂ is-combinator s)
    sub-vs (c-pair _ _)              _   s = ⊥-elim (noSyn-comb₂ is-combinator s)
    sub-vs (c-curry _)               _   s = ⊥-elim (noSyn-comb₁ is-combinator s)
    sub-vs (c-cata _ _)              _   s = ⊥-elim (noSyn-comb₁ is-combinator s)
    sub-vs (c-ana _ _)               _   s = ⊥-elim (noSyn-comb₁ is-combinator s)
    sub-vs (c-sub _ _ _)             _   _ = refl
    sub-vs (c-lam _)                 _   ()
    sub-vs (c-pair-lit _ _)          noc _ = ⊥-elim (noc oc-pair)
    sub-vs (c-poly d e lt _ _)       _   s = ⊥-elim (noSyn-poly d e lt s)

  one-rule⇐ : ∀ {n} {L : Locals m n} {e A A′ t t′} (d : Chk L e A t) (d′ : Chk L e A′ t′) → ruleOf⇐ d ≡ ruleOf⇐ d′
  one-rule⇐ (c-sub _ _ _) (c-sub _ _ _) = refl
  one-rule⇐ d@(c-map _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-map-app _ _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-compose-g _ _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-compose-f _ _ _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-case _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-pair _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-curry _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-cata _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-ana _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-lam _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-pair-lit _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ d@(c-poly _ _ _ _ _) (c-sub noc s _) = sub-vs d noc s
  one-rule⇐ (c-sub noc s _) d′@(c-map _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-map-app _ _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-compose-g _ _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-compose-f _ _ _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-case _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-pair _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-curry _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-cata _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-ana _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-lam _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-pair-lit _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-sub noc s _) d′@(c-poly _ _ _ _ _) = sym (sub-vs d′ noc s)
  one-rule⇐ (c-map _)              (c-map _)              = refl
  one-rule⇐ (c-map-app _ _ _)      (c-map-app _ _ _)      = refl
  one-rule⇐ (c-compose-g _ _ _)    (c-compose-g _ _ _)    = refl
  one-rule⇐ (c-compose-g df _ _)   (c-compose-f ndf _ _ _) = ⊥-elim (ndf df)
  one-rule⇐ (c-compose-f ndf _ _ _) (c-compose-g df _ _)  = ⊥-elim (ndf df)
  one-rule⇐ (c-compose-f _ _ _ _)  (c-compose-f _ _ _ _)  = refl
  one-rule⇐ (c-case _ _)           (c-case _ _)           = refl
  one-rule⇐ (c-pair _ _)           (c-pair _ _)           = refl
  one-rule⇐ (c-curry _)            (c-curry _)            = refl
  one-rule⇐ (c-cata _ _)           (c-cata _ _)           = refl
  one-rule⇐ (c-ana _ _)            (c-ana _ _)            = refl
  one-rule⇐ (c-lam _)              (c-lam _)              = refl
  one-rule⇐ (c-pair-lit _ _)       (c-pair-lit _ _)       = refl
  one-rule⇐ (c-poly _ _ _ _ _)     (c-poly _ _ _ _ _)     = refl

  -- `d-infer` is never the rule of a form with a domain-given rule of its own.
  private
    infer-vs : ∀ {n} {L : Locals m n} {e A π B t} (d : Dom L e A π B t) {T t′} → Syn L e T t′
             → ruleOf↦ d ≡ Rule.d-infer
    infer-vs (d-infer _ _ _)               _ = refl
    infer-vs (d-poly d e lt _ _ _ _ _ _ _) s = ⊥-elim (noSyn-poly d e lt s)
    infer-vs (d-lam _)                     ()
    infer-vs (d-map fd _ _)                s = ⊥-elim (noSyn-map (fd-map fd) s)
    infer-vs (d-compose _ _)               s = ⊥-elim (noSyn-comb₂ is-combinator s)
    infer-vs (d-case _ _ _)                s = ⊥-elim (noSyn-comb₂ is-combinator s)
    infer-vs (d-pair _ _)                  s = ⊥-elim (noSyn-comb₂ is-combinator s)
    infer-vs (d-cata _ _ _ _)              s = ⊥-elim (noSyn-comb₁ is-combinator s)

  one-rule↦ : ∀ {n} {L : Locals m n} {e A A′ B B′ π π′ t t′} (d : Dom L e A π B t) (d′ : Dom L e A′ π′ B′ t′)
            → ruleOf↦ d ≡ ruleOf↦ d′
  one-rule↦ (d-infer _ _ _) (d-infer _ _ _) = refl
  one-rule↦ d@(d-poly _ _ _ _ _ _ _ _ _ _) (d-infer s _ _) = infer-vs d s
  one-rule↦ d@(d-lam _) (d-infer s _ _) = infer-vs d s
  one-rule↦ d@(d-map _ _ _) (d-infer s _ _) = infer-vs d s
  one-rule↦ d@(d-compose _ _) (d-infer s _ _) = infer-vs d s
  one-rule↦ d@(d-case _ _ _) (d-infer s _ _) = infer-vs d s
  one-rule↦ d@(d-pair _ _) (d-infer s _ _) = infer-vs d s
  one-rule↦ d@(d-cata _ _ _ _) (d-infer s _ _) = infer-vs d s
  one-rule↦ (d-infer s _ _) d′@(d-poly _ _ _ _ _ _ _ _ _ _) = sym (infer-vs d′ s)
  one-rule↦ (d-infer s _ _) d′@(d-lam _) = sym (infer-vs d′ s)
  one-rule↦ (d-infer s _ _) d′@(d-map _ _ _) = sym (infer-vs d′ s)
  one-rule↦ (d-infer s _ _) d′@(d-compose _ _) = sym (infer-vs d′ s)
  one-rule↦ (d-infer s _ _) d′@(d-case _ _ _) = sym (infer-vs d′ s)
  one-rule↦ (d-infer s _ _) d′@(d-pair _ _) = sym (infer-vs d′ s)
  one-rule↦ (d-infer s _ _) d′@(d-cata _ _ _ _) = sym (infer-vs d′ s)
  one-rule↦ (d-poly _ _ _ _ _ _ _ _ _ _) (d-poly _ _ _ _ _ _ _ _ _ _) = refl
  one-rule↦ (d-lam _)        (d-lam _)        = refl
  one-rule↦ (d-map _ _ _)    (d-map _ _ _)    = refl
  one-rule↦ (d-compose _ _)  (d-compose _ _)  = refl
  one-rule↦ (d-case _ _ _)   (d-case _ _ _)   = refl
  one-rule↦ (d-pair _ _)     (d-pair _ _)     = refl
  one-rule↦ (d-cata _ _ _ _) (d-cata _ _ _ _) = refl

surface : Surface Σ S nm
surface = record
  { synth-unique        = λ {m} {Δ} → Modes.synth-unique Δ
  ; domain-exact        = λ {m} {Δ} → Modes.domain-exact Δ
  ; domain-agrees-synth = λ {m} {Δ} → Modes.agree Δ
  ; one-rule⇒           = λ {m} {Δ} → Modes.one-rule⇒ Δ
  ; one-rule⇐           = λ {m} {Δ} → Modes.one-rule⇐ Δ
  ; one-rule↦           = λ {m} {Δ} → Modes.one-rule↦ Δ
  }
