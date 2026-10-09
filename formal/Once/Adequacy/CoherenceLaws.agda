-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoherenceLaws — the SURFACE MEANING laws coherence uses
-- (plan 0.103, `realize-invariant`).
--
-- Two families, both about `SD.⟦_⟧ˢ`:
--
--   * CONGRUENCE: every term former's meaning is a function of its
--     subterms' meanings. One lemma per former `realize` emits; each is the
--     former's `⟦_⟧ˢ` clause with the subterms' meanings abstracted.
--   * COERCION: a conversion `coerce p` commutes with the formers the way
--     its meaning `fmapT ⟦ p ⟧<:` says. These are what make two routes
--     through the bidirectional judgment mean the same: one route converts a
--     subterm, the other converts the whole.
--
-- Meanings are compared as FUNCTIONS (`_≈_`), so a congruence is one `cong₂`
-- over the clause body and needs no extensionality.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.CoherenceLaws (fmt : TargetNum) where

open import Data.Bool using (true)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Postulates using (extensionality)
open import Once.Type using (Type; Void; Int; Float; _*_; _+_; _⇒[_]_; mk-kind; Many; One; Zero; Purity; Quantity; _≤q_; μ-type; ⟦_⟧T)
open import Once.Type.Sub using (_<:_; sub-arr; sub-prod; sub-void; <:-refl; <:-trans; <:-unique;
  _⊑π_; ⊑π-refl)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; _∷_; _,_^_; zeroUsage; _*ᵘ_; _⊔ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; lam; app; effApp; pair; let'; case'; neg; i2f; add; sub; mul; div; mod'; fadd; fsub; fmul; fdiv; lt; le; gt; ge; eq; ne; coerce; morph-app; comp'; copair'; fork'; curry'; cata; ana; lift-morphism)
open import Once.Denotation.TraceMonad using (T; ret; returnT; _>>=T_; >>=T-assoc; fmapT)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.Sub using (⟦_⟧<:; <:-refl-id; <:-trans-∘)
open import Once.Denotation.TraceMonad using (fmapT-id; fmapT-cong; fmapT-∘)
open import Once.Semantics.Machine using (sem-cata; sem-fmap; coerce-μ-out; ⟦_⟧F; ⟦μ⟧)
open import Once.Word using (Carrier)
open import Once.Functor.Translate using (translateF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Type using (K; Id; _⊕_; _⊗_)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Data.Empty using (⊥)
open import Once.Denotation.ValueDomain using (seqF; coerce-functor⁻¹-D; cohᴰ; anaFᵈ; coerce-functor-D; ⟦_⟧ᴰ)
open import Once.Arith.SigOp.Builders using (add-info; sub-info; mul-info; div-info; mod-info;
  fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info; neg-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.Functor.Translate using (WellFormedF)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.IR as IR
open import Relation.Binary.PropositionalEquality using (subst)
import Once.Denotation.SourceDenote as SD
open SD using (⟦_⟧ˢ; cata-ev-algˢ)
open SD.DefsSem using (calls)

infix 4 _≈ˢ_ _≈_
_≈ˢ_ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → Expr Γ Ψ A → Set
a ≈ˢ b = ⟦ a ⟧ˢ fmt ≡ ⟦ b ⟧ˢ fmt

-- Two terms MEAN the same. A record rather than the bare equation so that it
-- is injective for unification: from `a ≈ b` Agda can read off `a` and `b`,
-- which it cannot from `⟦ a ⟧ˢ fmt ≡ ⟦ b ⟧ˢ fmt`.
record _≈_ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (a b : Expr Γ Ψ A) : Set where
  constructor ≈-intro
  field ≈-out : a ≈ˢ b

≈-refl : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} {a : Expr Γ Ψ A} → a ≈ a
≈-refl = ≈-intro refl

≈-sym : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} {a b : Expr Γ Ψ A} → a ≈ b → b ≈ a
≈-sym (≈-intro e) = ≈-intro (sym e)

≈-trans : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} {a b c : Expr Γ Ψ A} → a ≈ b → b ≈ c → a ≈ c
≈-trans (≈-intro e) (≈-intro f) = ≈-intro (trans e f)

------------------------------------------------------------------------
-- The monad facts the coercion laws rest on: equalities of trees, each one
-- associativity law (plan 0.105).
------------------------------------------------------------------------

fmap-bind : ∀ {X Y Z : Set} (f : Y → Z) (m : T X) (k : X → T Y)
          → fmapT f (m >>=T k) ≡ (m >>=T λ x → fmapT f (k x))
fmap-bind f m k = >>=T-assoc m k (λ y → ret (f y))

bind-fmap : ∀ {X Y Z : Set} (f : X → Y) (m : T X) (k : Y → T Z)
          → (fmapT f m >>=T k) ≡ (m >>=T λ x → k (f x))
bind-fmap f m k = >>=T-assoc m (λ x → ret (f x)) k

ret-bind : ∀ {X Y : Set} (h : X) (f : X → T Y) → (returnT h >>=T f) ≡ f h
ret-bind h f = refl

bind-congʳ : ∀ {X Y : Set} (m : T X) {k k′ : X → T Y} → (∀ x → k x ≡ k′ x) → (m >>=T k) ≡ (m >>=T k′)
bind-congʳ m h = cong (m >>=T_) (extensionality h)

------------------------------------------------------------------------
-- Congruence
------------------------------------------------------------------------

module _ {n} {Γ : Ctx n} where

  pair-congˢ : ∀ {Ψ₁ Ψ₂ A B} {a a′ : Expr Γ Ψ₁ A} {b b′ : Expr Γ Ψ₂ B}
            → a ≈ˢ a′ → b ≈ˢ b′ → pair a b ≈ˢ pair a′ b′
  pair-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → returnT (va , vb))

  -- The binary primitives: one clause shape, one `cong₂` each.
  add-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → add a b ≈ˢ add a′ b′
  add-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ add-info (va , vb))
  sub-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → sub a b ≈ˢ sub a′ b′
  sub-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ sub-info (va , vb))
  mul-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → mul a b ≈ˢ mul a′ b′
  mul-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ mul-info (va , vb))
  div-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → div a b ≈ˢ div a′ b′
  div-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ div-info (va , vb))
  mod-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → mod' a b ≈ˢ mod' a′ b′
  mod-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ mod-info (va , vb))
  fadd-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fadd a b ≈ˢ fadd a′ b′
  fadd-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ fadd-info (va , vb))
  fsub-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fsub a b ≈ˢ fsub a′ b′
  fsub-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ fsub-info (va , vb))
  fmul-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fmul a b ≈ˢ fmul a′ b′
  fmul-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ fmul-info (va , vb))
  fdiv-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fdiv a b ≈ˢ fdiv a′ b′
  fdiv-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ fdiv-info (va , vb))
  lt-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → lt a b ≈ˢ lt a′ b′
  lt-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ lt-info (va , vb))
  le-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → le a b ≈ˢ le a′ b′
  le-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ le-info (va , vb))
  gt-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → gt a b ≈ˢ gt a′ b′
  gt-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ gt-info (va , vb))
  ge-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → ge a b ≈ˢ ge a′ b′
  ge-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ ge-info (va , vb))
  eq-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → eq a b ≈ˢ eq a′ b′
  eq-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ eq-info (va , vb))
  ne-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → ne a b ≈ˢ ne a′ b′
  ne-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → SD.sigOpˢ fmt σ ne-info (va , vb))

  neg-congˢ : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ˢ a′ → neg a ≈ˢ neg a′
  neg-congˢ = cong (λ X σ dγ → X σ dγ >>=T λ v → SD.sigOpˢ fmt σ neg-info v)

  i2f-congˢ : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ˢ a′ → i2f a ≈ˢ i2f a′
  i2f-congˢ = cong (λ X σ dγ → X σ dγ >>=T λ va → SD.sigOpˢ fmt σ i2f-info va)

  coerce-congˢ : ∀ {Ψ A B} (p : A <: B) {a a′ : Expr Γ Ψ A} → a ≈ˢ a′ → coerce p a ≈ˢ coerce p a′
  coerce-congˢ p = cong (λ X σ dγ → fmapT ⟦ p ⟧<: (X σ dγ))

  morph-app-congˢ : ∀ {Ψ A B} (ir : IR ⌊ A ⌋ ⌊ B ⌋) {a a′ : Expr Γ Ψ A} → a ≈ˢ a′ → morph-app {A = A} {B = B} ir a ≈ˢ morph-app {A = A} {B = B} ir a′
  morph-app-congˢ {Ψ} {A} {B} ir = cong (λ X σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))) dγ)
    >>=T λ v → subst T (cohᴰ B) (evalᴰ fmt (calls σ) ir (subst (λ z → z) (sym (cohᴰ A)) v)))

  app-congˢ : ∀ {Ψ₁ Ψ₂ A B q} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind q Once.Type.pure ] B)} {x x′ : Expr Γ Ψ₂ A}
           → f ≈ˢ f′ → x ≈ˢ x′ → app f x ≈ˢ app f′ x′
  app-congˢ {Ψ₁} {Ψ₂} {q = Zero} ef ex = cong (λ X σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ) >>=T λ vf → vf _) ef
  app-congˢ {Ψ₁} {Ψ₂} {q = One} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx)
  app-congˢ {Ψ₁} {Ψ₂} {q = Many} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx)

  effApp-congˢ : ∀ {Ψ₁ Ψ₂ A B} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many Once.Type.eff ] B)} {x x′ : Expr Γ Ψ₂ A}
              → f ≈ˢ f′ → x ≈ˢ x′ → effApp f x ≈ˢ effApp f′ x′
  effApp-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ → returnT (λ _ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx))

  comp-congˢ : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)}
            → f ≈ˢ f′ → g ≈ˢ g′ → comp' f g ≈ˢ comp' f′ g′
  comp-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vg →
    returnT (λ a → vg a >>=T vf))

  copair-congˢ : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)}
              → f ≈ˢ f′ → g ≈ˢ g′ → copair' f g ≈ˢ copair' f′ g′
  copair-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vg →
    returnT (λ ab → [ vf , vg ]′ ab))

  fork-congˢ : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)}
            → f ≈ˢ f′ → g ≈ˢ g′ → fork' f g ≈ˢ fork' f′ g′
  fork-congˢ {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vg →
    returnT (λ a → vf a >>=T λ b → vg a >>=T λ c → returnT (b , c)))

  curry-congˢ : ∀ {Ψ A B C π₀ π} {f f′ : Expr Γ Ψ ((A * B) ⇒[ mk-kind Many π ] C)}
             → f ≈ˢ f′ → curry' {π₀ = π₀} f ≈ˢ curry' f′
  curry-congˢ = cong (λ X σ dγ → X σ dγ >>=T λ vf → returnT (λ a → returnT (λ b → vf (a , b))))

  cata-congˢ : ∀ {Ψ F A π} (wf : WellFormedF F) {g g′ : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
            → g ≈ˢ g′ → cata {Γ = Γ} wf g ≈ˢ cata wf g′
  cata-congˢ {F = F} {A} wf = cong (λ X σ dγ → X σ dγ >>=T λ valg →
    returnT (λ x → sem-cata wf (cata-ev-algˢ {F} {A} wf (returnT valg)) x))

  -- D273: the coalgebra lives in the context and is bound once, as `cata`'s.
  ana-congˢ : ∀ {Ψ F A π₀ π} (wf : WellFormedF F) {g g′ : Expr Γ Ψ (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A)}
           → g ≈ˢ g′ → ana {Γ = Γ} {π₀ = π₀} wf g ≈ˢ ana wf g′
  ana-congˢ {F = F} {A} wf = cong (λ X σ dγ → X σ dγ >>=T λ clo →
    returnT (λ a → returnT (anaFᵈ F (λ a' → fmapT (coerce-functor-D wf A) (clo a')) a)))

  let-congˢ : ∀ {Ψ₁ Ψ₂ A B q} {e₁ e₁′ : Expr Γ Ψ₁ A} {e₂ e₂′ : Expr (_,_^_ Γ A Many) (q ∷ Ψ₂) B}
           → e₁ ≈ˢ e₁′ → e₂ ≈ˢ e₂′ → let' e₁ e₂ ≈ˢ let' e₁′ e₂′
  let-congˢ {Ψ₁} {Ψ₂} {A} {q = Zero} _ = cong (λ Y σ dγ →
    Y σ (bindᴰ0 {Γ = Γ} {A = A} (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ)))
  let-congˢ {Ψ₁} {Ψ₂} {A} {q = One} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) dγ) >>=T λ v1 →
    Y σ (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) dγ) v1))
  let-congˢ {Ψ₁} {Ψ₂} {A} {q = Many} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) dγ) >>=T λ v1 →
    Y σ (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) dγ) v1))

  case-congˢ : ∀ {Ψs Ψₗ Ψᵣ qℓ qr A B C} {s s′ : Expr Γ Ψs (A + B)}
                {l l′ : Expr (_,_^_ Γ A Many) (qℓ ∷ Ψₗ) C} {r r′ : Expr (_,_^_ Γ B Many) (qr ∷ Ψᵣ) C}
            → s ≈ˢ s′ → l ≈ˢ l′ → r ≈ˢ r′ → case' s l r ≈ˢ case' s′ l′ r′
  case-congˢ {Ψs} {Ψₗ} {Ψᵣ} {qℓ} {qr} {A} {B} {s′ = s′} {l′ = l′} {r = r} es el er =
    trans (cong₂ (λ X Y σ dγ →
      X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ) >>=T λ v →
      [ (λ a → Y σ (bindᴰ {Γ = Γ} {A = A} qℓ (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
      , (λ b → ⟦ r ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = B} qr (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b)) ]′ v) es el)
          (cong (λ Z σ dγ →
      ⟦ s′ ⟧ˢ fmt σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ) >>=T λ v →
      [ (λ a → ⟦ l′ ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = A} qℓ (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
      , (λ b → Z σ (bindᴰ {Γ = Γ} {A = B} qr (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b)) ]′ v) er)

  lam-congˢ : ∀ {Ψ q' π A B} (q : Quantity) (≤p : (q' ≤q q) ≡ true) {b b′ : Expr (_,_^_ Γ A Many) (q' ∷ Ψ) B}
           → b ≈ˢ b′ → lam {π = π} q ≤p b ≈ˢ lam q ≤p b′
  lam-congˢ {q' = Zero} {A = A} Zero ≤p = cong (λ X σ dγ → returnT (λ _ → X σ (bindᴰ0 {Γ = Γ} {A = A} dγ)))
  lam-congˢ {q' = Zero} {A = A} One  ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ0 {Γ = Γ} {A = A} dγ)))
  lam-congˢ {q' = Zero} {A = A} Many ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ0 {Γ = Γ} {A = A} dγ)))
  lam-congˢ {q' = One}  {A = A} One  ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ {Γ = Γ} {A = A} One dγ a)))
  lam-congˢ {q' = One}  {A = A} Many ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ {Γ = Γ} {A = A} One dγ a)))
  lam-congˢ {q' = Many} {A = A} Many ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ {Γ = Γ} {A = A} Many dγ a)))
  lam-congˢ {q' = One}  Zero ()
  lam-congˢ {q' = Many} Zero ()
  lam-congˢ {q' = Many} One  ()

------------------------------------------------------------------------
-- Coercion
------------------------------------------------------------------------

-- A conversion's meaning on a reflexive witness is the identity.
fmap-refl : ∀ (A : Type) (m : T ⟦ A ⟧ᴰ) → fmapT ⟦ <:-refl A ⟧<: m ≡ m
fmap-refl A m = trans (fmapT-cong (<:-refl-id A) m) (fmapT-id m)

module _ {n} {Γ : Ctx n} where

  coerce-reflˢ : ∀ {Ψ A} (e : Expr Γ Ψ A) → coerce (<:-refl A) e ≈ˢ e
  coerce-reflˢ {A = A} e = extensionality λ σ → extensionality λ dγ → fmap-refl A _

  coerce-transˢ : ∀ {Ψ A B C} (p : A <: B) (q : B <: C) (e : Expr Γ Ψ A)
               → coerce q (coerce p e) ≈ˢ coerce (<:-trans p q) e
  coerce-transˢ p q e = extensionality λ σ → extensionality λ dγ →
    trans (fmapT-∘ ⟦ q ⟧<: ⟦ p ⟧<: (⟦ e ⟧ˢ fmt σ dγ)) (fmapT-cong (λ x → sym (<:-trans-∘ p q x)) (⟦ e ⟧ˢ fmt σ dγ))

  coerce-uniqˢ : ∀ {Ψ A B} (p q : A <: B) (e : Expr Γ Ψ A) → coerce p e ≈ˢ coerce q e
  coerce-uniqˢ p q e = cong (λ r → ⟦ coerce r e ⟧ˢ fmt) (<:-unique p q)

  pair-coerceˢ : ∀ {Ψ₁ Ψ₂ A A′ B B′} (pa : A <: A′) (pb : B <: B′) (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
              → pair (coerce pa a) (coerce pb b) ≈ˢ coerce (sub-prod pa pb) (pair a b)
  pair-coerceˢ pa pb a b = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap ⟦ pa ⟧<: (⟦ a ⟧ˢ fmt σ _) _)
     (trans (bind-congʳ (⟦ a ⟧ˢ fmt σ _) (λ va → bind-fmap ⟦ pb ⟧<: (⟦ b ⟧ˢ fmt σ _) _))
      (sym (trans (fmap-bind _ (⟦ a ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ a ⟧ˢ fmt σ _) (λ va → fmap-bind _ (⟦ b ⟧ˢ fmt σ _) _)))))

  -- Converting the head's domain is converting the argument.
  app-coerceˢ : ∀ {Ψ₁ Ψ₂ X A′ B} (a : X <: A′) (g : Once.Type.pure ⊑π Once.Type.pure)
                 (f : Expr Γ Ψ₁ (A′ ⇒[ mk-kind Many Once.Type.pure ] B)) (x : Expr Γ Ψ₂ X)
             → app (coerce (sub-arr a (<:-refl B) g) f) x ≈ˢ app f (coerce a x)
  app-coerceˢ {B = B} a g f x = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ (⟦ f ⟧ˢ fmt σ _) _)
     (bind-congʳ (⟦ f ⟧ˢ fmt σ _) λ vf → trans (bind-congʳ (⟦ x ⟧ˢ fmt σ _) (λ vx → fmap-refl B _)) (sym (bind-fmap ⟦ a ⟧<: (⟦ x ⟧ˢ fmt σ _) _)))

  -- Converting the outer arm's codomain is converting the composite's.
  comp-postˢ : ∀ {Ψ₁ Ψ₂ A M B B′ π} (p : B <: B′) (r r′ : π ⊑π π)
                (f : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M))
            → comp' (coerce (sub-arr (<:-refl M) p r) f) g ≈ˢ coerce (sub-arr (<:-refl A) p r′) (comp' f g)
  comp-postˢ {A = A} {M} p r r′ f g = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ (⟦ f ⟧ˢ fmt σ _) _)
     (sym (trans (fmap-bind _ (⟦ f ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ f ⟧ˢ fmt σ _) λ vf → trans (fmap-bind _ (⟦ g ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ g ⟧ˢ fmt σ _) λ vg →
       cong returnT (extensionality λ x →
         trans (cong (λ y → fmapT ⟦ p ⟧<: (vg y >>=T vf)) (<:-refl-id A x))
          (trans (fmap-bind _ (vg x) vf)
                 (bind-congʳ (vg x) λ m → cong (λ z → fmapT ⟦ p ⟧<: (vf z)) (sym (<:-refl-id M m)))))))))

  -- Converting the outer arm's domain is converting the inner arm's codomain.
  comp-preˢ : ∀ {Ψ₁ Ψ₂ A B B′ C C′ π π′} (q : B <: B′) (c : C′ <: C) (g : π′ ⊑π π)
               (f : Expr Γ Ψ₁ (B′ ⇒[ mk-kind Many π′ ] C′)) (h : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B))
           → comp' (coerce (sub-arr q c g) f) h
             ≈ˢ comp' (coerce (sub-arr (<:-refl B′) c g) f) (coerce (sub-arr (<:-refl A) q (⊑π-refl π)) h)
  comp-preˢ {A = A} {B′ = B′} q c g f h = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ (⟦ f ⟧ˢ fmt σ _) _)
     (sym (trans (bind-fmap _ (⟦ f ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ f ⟧ˢ fmt σ _) λ vf → trans (bind-fmap _ (⟦ h ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ h ⟧ˢ fmt σ _) λ vh →
       cong returnT (extensionality λ x →
         trans (bind-fmap ⟦ q ⟧<: (vh _) _)
          (trans (cong (λ y → vh y >>=T λ z → fmapT ⟦ c ⟧<: (vf (⟦ <:-refl B′ ⟧<: (⟦ q ⟧<: z)))) (<:-refl-id A x))
                 (bind-congʳ (vh x) λ z → cong (λ w → fmapT ⟦ c ⟧<: (vf w)) (<:-refl-id B′ (⟦ q ⟧<: z)))))))))

  -- Converting a lambda's body is converting the lambda.
  lam-coerceˢ : ∀ {Ψ q' π A B B′} (≤p : (q' ≤q Many) ≡ true) (p : B <: B′) (b : Expr (_,_^_ Γ A Many) (q' ∷ Ψ) B)
             → lam {π = π} Many ≤p (coerce p b) ≈ˢ coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (lam Many ≤p b)
  lam-coerceˢ {q' = Zero} ≤p p b = refl
  lam-coerceˢ {q' = One} {A = A} ≤p p b = extensionality λ σ → extensionality λ dγ →
    cong returnT (extensionality λ x →
      cong (λ y → fmapT ⟦ p ⟧<: (⟦ b ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = A} One dγ y))) (sym (<:-refl-id A x)))
  lam-coerceˢ {q' = Many} {A = A} ≤p p b = extensionality λ σ → extensionality λ dγ →
    cong returnT (extensionality λ x →
      cong (λ y → fmapT ⟦ p ⟧<: (⟦ b ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = A} Many dγ y))) (sym (<:-refl-id A x)))

  copair-coerceˢ : ∀ {Ψ₁ Ψ₂ A B C C′ π} (p : C <: C′) (r : π ⊑π π)
                    (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)) (g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C))
                → copair' (coerce (sub-arr (<:-refl A) p r) f) (coerce (sub-arr (<:-refl B) p r) g)
                  ≈ˢ coerce (sub-arr (<:-refl (A + B)) p r) (copair' f g)
  copair-coerceˢ p r f g = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ (⟦ f ⟧ˢ fmt σ _) _) (trans (bind-congʳ (⟦ f ⟧ˢ fmt σ _) (λ vf → bind-fmap _ (⟦ g ⟧ˢ fmt σ _) _))
      (sym (trans (fmap-bind _ (⟦ f ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ f ⟧ˢ fmt σ _) λ vf → trans (fmap-bind _ (⟦ g ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ g ⟧ˢ fmt σ _) λ vg →
        cong returnT (extensionality λ { (inj₁ a) → refl ; (inj₂ b) → refl }))))))

  fork-coerceˢ : ∀ {Ψ₁ Ψ₂ A B B′ C C′ π} (pb : B <: B′) (pc : C <: C′) (r : π ⊑π π)
                  (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C))
              → fork' (coerce (sub-arr (<:-refl A) pb r) f) (coerce (sub-arr (<:-refl A) pc r) g)
                ≈ˢ coerce (sub-arr (<:-refl A) (sub-prod pb pc) r) (fork' f g)
  fork-coerceˢ pb pc r f g = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ (⟦ f ⟧ˢ fmt σ _) _) (trans (bind-congʳ (⟦ f ⟧ˢ fmt σ _) (λ vf → bind-fmap _ (⟦ g ⟧ˢ fmt σ _) _))
      (sym (trans (fmap-bind _ (⟦ f ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ f ⟧ˢ fmt σ _) λ vf → trans (fmap-bind _ (⟦ g ⟧ˢ fmt σ _) _) (bind-congʳ (⟦ g ⟧ˢ fmt σ _) λ vg →
        cong returnT (extensionality λ x →
          trans (fmap-bind _ (vf _) _) (sym (trans (bind-fmap ⟦ pb ⟧<: (vf _) _) (bind-congʳ (vf _) λ b →
            trans (bind-fmap ⟦ pc ⟧<: (vg _) _) (sym (trans (fmap-bind _ (vg _) _) (bind-congʳ (vg _) λ c → refl))))))))))))

  -- `initial` at any codomain: a function out of `Void` is unique.
  initial-coerceˢ : ∀ {A π} (r : π ⊑π π)
                 → coerce (sub-arr sub-void sub-void r) (lift-morphism {Γ = Γ} {A = Void} {B = Void} {π = π} IR.initial)
                   ≈ˢ lift-morphism {Γ = Γ} {A = Void} {B = A} {π = π} IR.initial
  initial-coerceˢ r = extensionality λ σ → extensionality λ dγ → cong returnT (extensionality λ ())

------------------------------------------------------------------------
-- `cata` fuses with a conversion of its carrier.
--
-- The algebra `alg : ⟦F⟧A ⇒ A`, converted to `⟦F⟧A′ ⇒ A′` (domain `d`,
-- codomain `p`), folds to the conversion of `alg`'s fold. The relational fold
-- (`cataS-rel`) at `R t₁ t₂ = t₁ ≡ fmapT ⟦ p ⟧<: t₂` carries it: sequencing a
-- related layer is mapping the sequenced layer (`seq-rel`), and a layer
-- converted up and back down is unchanged (`layer-id`, since `d` after the
-- lifted `p` converts a type to ITSELF, and that conversion is the identity).
------------------------------------------------------------------------

-- The functor-lifted relation on `⟦ F ⟧F`.
RelF : ∀ F {X₁ X₂ : Set} (R : X₁ → X₂ → Set) → ⟦ F ⟧F X₁ → ⟦ F ⟧F X₂ → Set
RelF (K A)   R x y = x ≡ y
RelF Id      R x y = R x y
RelF (F ⊕ G) R (inj₁ x) (inj₁ y) = RelF F R x y
RelF (F ⊕ G) R (inj₂ x) (inj₂ y) = RelF G R x y
RelF (F ⊕ G) R (inj₁ _) (inj₂ _) = ⊥
RelF (F ⊕ G) R (inj₂ _) (inj₁ _) = ⊥
RelF (F ⊗ G) R (x₁ , y₁) (x₂ , y₂) = RelF F R x₁ x₂ × RelF G R y₁ y₂

out-rel : ∀ {F} (wf : WellFormedF F) {X₁ X₂ : Set} (R : X₁ → X₂ → Set) {y₁ y₂}
        → RelSF (translateF Carrier Carrier F) R y₁ y₂
        → RelF F R (coerce-μ-out wf X₁ y₁) (coerce-μ-out wf X₂ y₂)
out-rel (wf-K pA) R refl = refl
out-rel wf-Id R r = r
out-rel (wf-Sum wfF wfG) R {inj₁ _} {inj₁ _} r = out-rel wfF R r
out-rel (wf-Sum wfF wfG) R {inj₂ _} {inj₂ _} r = out-rel wfG R r
out-rel (wf-Sum wfF wfG) R {inj₁ _} {inj₂ _} ()
out-rel (wf-Sum wfF wfG) R {inj₂ _} {inj₁ _} ()
out-rel (wf-Prod wfF wfG) R {_ , _} {_ , _} (r₁ , r₂) = out-rel wfF R r₁ , out-rel wfG R r₂

seq-rel : ∀ F {A A′ : Type} (p : A <: A′) {fc₁ : ⟦ F ⟧F (T ⟦ A′ ⟧ᴰ)} {fc₂ : ⟦ F ⟧F (T ⟦ A ⟧ᴰ)}
        → RelF F (λ t₁ t₂ → t₁ ≡ fmapT ⟦ p ⟧<: t₂) fc₁ fc₂
        → seqF F fc₁ ≡ fmapT (sem-fmap F ⟦ p ⟧<:) (seqF F fc₂)
seq-rel (K B) p refl = refl
seq-rel Id p r = r
seq-rel (F ⊕ G) p {inj₁ _} {inj₁ x₂} r =
  trans (cong (fmapT inj₁) (seq-rel F p r)) (trans (fmapT-∘ inj₁ (sem-fmap F ⟦ p ⟧<:) (seqF F x₂)) (sym (fmapT-∘ (sem-fmap (F ⊕ G) ⟦ p ⟧<:) inj₁ (seqF F x₂))))
seq-rel (F ⊕ G) p {inj₂ _} {inj₂ y₂} r =
  trans (cong (fmapT inj₂) (seq-rel G p r)) (trans (fmapT-∘ inj₂ (sem-fmap G ⟦ p ⟧<:) (seqF G y₂)) (sym (fmapT-∘ (sem-fmap (F ⊕ G) ⟦ p ⟧<:) inj₂ (seqF G y₂))))
seq-rel (F ⊕ G) p {inj₁ _} {inj₂ _} ()
seq-rel (F ⊕ G) p {inj₂ _} {inj₁ _} ()
seq-rel (F ⊗ G) p {_ , _} {x₂ , y₂} (r₁ , r₂) rewrite seq-rel F p r₁ | seq-rel G p r₂ =
  trans (bind-fmap _ (seqF F x₂) _) (trans (bind-congʳ (seqF F x₂) (λ u → bind-fmap _ (seqF G y₂) _))
    (sym (trans (fmap-bind _ (seqF F x₂) _) (bind-congʳ (seqF F x₂) λ u → fmap-bind _ (seqF G y₂) _))))

layer-id : ∀ {F} (wf : WellFormedF F) {A A′ : Type} (d : ⟦ F ⟧T A′ <: ⟦ F ⟧T A) (p : A <: A′) (l : ⟦ F ⟧F ⟦ A ⟧ᴰ)
         → ⟦ d ⟧<: (coerce-functor⁻¹-D wf A′ (sem-fmap F ⟦ p ⟧<: l)) ≡ coerce-functor⁻¹-D wf A l
layer-id {K B} (wf-K b) d p l = trans (cong (λ r → ⟦ r ⟧<: _) (<:-unique d (<:-refl B))) (<:-refl-id B _)
layer-id wf-Id {A} d p l =
  trans (sym (<:-trans-∘ p d l)) (trans (cong (λ r → ⟦ r ⟧<: l) (<:-unique (<:-trans p d) (<:-refl A))) (<:-refl-id A l))
layer-id (wf-Sum w₁ w₂) (Once.Type.Sub.sub-sum d₁ d₂) p (inj₁ x) = cong inj₁ (layer-id w₁ d₁ p x)
layer-id (wf-Sum w₁ w₂) (Once.Type.Sub.sub-sum d₁ d₂) p (inj₂ y) = cong inj₂ (layer-id w₂ d₂ p y)
layer-id (wf-Prod w₁ w₂) (sub-prod d₁ d₂) p (x , y) = cong₂ _,_ (layer-id w₁ d₁ p x) (layer-id w₂ d₂ p y)

cata-core : ∀ {F} (wf : WellFormedF F) {A A′ : Type} {π π′ : Purity}
              (d : ⟦ F ⟧T A′ <: ⟦ F ⟧T A) (p : A <: A′) (g : π ⊑π π′)
              (valg : ⟦ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ⟧ᴰ) (x : ⟦μ⟧ F)
          → sem-cata wf (cata-ev-algˢ {F} {A′} wf (returnT (⟦ sub-arr {q = Many} d p g ⟧<: valg))) x
            ≡ fmapT ⟦ p ⟧<: (sem-cata wf (cata-ev-algˢ {F} {A} wf (returnT valg)) x)
cata-core {F} wf {A} {A′} d p g valg x =
  cataS-rel {translateF Carrier Carrier F} (λ t₁ t₂ → t₁ ≡ fmapT ⟦ p ⟧<: t₂) algR x
  where
    algR : ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) (λ t₁ t₂ → t₁ ≡ fmapT ⟦ p ⟧<: t₂) y₁ y₂
         → cata-ev-algˢ {F} {A′} wf (returnT (⟦ sub-arr {q = Many} d p g ⟧<: valg)) (coerce-μ-out wf _ y₁)
           ≡ fmapT ⟦ p ⟧<: (cata-ev-algˢ {F} {A} wf (returnT valg) (coerce-μ-out wf _ y₂))
    S₂ : ∀ y₂ → T (⟦ F ⟧F ⟦ A ⟧ᴰ)
    S₂ y₂ = seqF F (coerce-μ-out wf _ y₂)
    algR {y₁} {y₂} r =
      trans (bind-congʳ (seqF F (coerce-μ-out wf _ y₁)) (λ l → ret-bind (⟦ sub-arr {q = Many} d p g ⟧<: valg) (λ c → c (coerce-functor⁻¹-D wf A′ l))))
      (trans (cong (λ m → m >>=T λ l → ⟦ sub-arr {q = Many} d p g ⟧<: valg (coerce-functor⁻¹-D wf A′ l)) (seq-rel F p (out-rel wf _ r)))
      (trans (bind-fmap (sem-fmap F ⟦ p ⟧<:) (S₂ y₂) (λ l → ⟦ sub-arr {q = Many} d p g ⟧<: valg (coerce-functor⁻¹-D wf A′ l)))
      (trans (bind-congʳ (S₂ y₂) (λ l → cong (λ z → fmapT ⟦ p ⟧<: (valg z)) (layer-id wf d p l)))
      (trans (sym (fmap-bind ⟦ p ⟧<: (S₂ y₂) (λ l → valg (coerce-functor⁻¹-D wf A l))))
             (cong (fmapT ⟦ p ⟧<:) (sym (bind-congʳ (S₂ y₂) (λ l → ret-bind valg (λ c → c (coerce-functor⁻¹-D wf A l))))))))))

module _ {n} {Γ : Ctx n} where

  cata-coerceˢ : ∀ {Ψ F A A′ π} (wf : WellFormedF F) (d : ⟦ F ⟧T A′ <: ⟦ F ⟧T A) (p : A <: A′) (g : π ⊑π π)
                  (alg : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
              → cata {Γ = Γ} wf (coerce (sub-arr {q = Many} d p g) alg)
                ≈ˢ coerce (sub-arr (<:-refl (μ-type F)) p (⊑π-refl π)) (cata {Γ = Γ} wf alg)
  cata-coerceˢ wf d p g alg = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ (⟦ alg ⟧ˢ fmt σ dγ) _)
     (trans (bind-congʳ (⟦ alg ⟧ˢ fmt σ dγ) λ valg → cong returnT (extensionality λ x → cata-core wf d p g valg x))
            (sym (fmap-bind _ (⟦ alg ⟧ˢ fmt σ dγ) _)))

-- The same laws at `_≈_` live in `CoherenceLawsWrap` (split for the 30 s
-- per-module check budget).
