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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Postulates using (extensionality)
open import Once.Res using (Res; returns; stopped; mapRes)
open import Once.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; mk-kind; Many; One; Zero;
  Purity; Quantity; _≤q_; Functor; μ-type; ν-type; ⟦_⟧T)
open import Once.Type.Sub using (_<:_; sub-arr; sub-prod; sub-void; <:-refl; <:-trans; <:-unique;
  _⊑π_; ⊑π-refl)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; ∅; _∷_; _,_^_; zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_;
  ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many;
  lam; app; effApp; pair; let'; case'; neg; i2f; add; sub; mul; div; mod'; fadd; fsub; fmul; fdiv;
  lt; le; gt; ge; eq; ne; coerce; morph-app; comp'; copair'; fork'; curry'; cata; ana; lift-morphism)
open import Once.Denotation.TraceMonad using (T; mkT; returnT; _>>=T_; fmapT; resT-lift)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; cohᴰ; anaFᵈ; coerce-functor-D)
open import Once.Denotation.Sub using (⟦_⟧<:; <:-refl-id; <:-trans-∘; fmapT-id; fmapT-cong; fmapT-∘)
open import Once.Denotation.DenotTrace using (liftFn)
open import Once.Semantics.Machine using (sem-cata; sem-fmap; coerce-μ-out; ⟦_⟧F; ⟦μ⟧)
open import Once.Word using (Carrier)
open import Once.Functor.Translate using (translateF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Type using (K; Id; _⊕_; _⊗_)
open import Once.Semantics.Functor using (⟦_⟧SF; cataS)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Data.Empty using (⊥)
open import Once.Denotation.ValueDomain using (seqF; coerce-functor⁻¹-D)
open import Once.SigOp.Info using (semM)
open import Once.Arith.SigOp.Builders using (add-info; sub-info; mul-info; div-info; mod-info;
  fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info; neg-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.Functor.Translate using (WellFormedF)
open import Once.IR using (IR; ⌊_⌋)
import Once.IR as IR
open import Relation.Binary.PropositionalEquality using (subst)
import Once.Denotation.SourceDenote as SD
open SD using (⟦_⟧ˢ; calls; cata-ev-algˢ; liftD)

infix 4 _≈_
_≈_ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → Expr Γ Ψ A → Set
a ≈ b = ⟦ a ⟧ˢ fmt ≡ ⟦ b ⟧ˢ fmt

------------------------------------------------------------------------
-- The monad facts the coercion laws rest on (equalities, not budget views:
-- `fmapT` leaves the trace untouched, so both hold by cases on the result).
------------------------------------------------------------------------

fmap-bind : ∀ {X Y Z : Set} (f : Y → Z) (m : T X) (k : X → T Y)
          → fmapT f (m >>=T k) ≡ (m >>=T λ x → fmapT f (k x))
fmap-bind f (mkT tr stopped)     k = refl
fmap-bind f (mkT tr (returns x)) k = refl

bind-fmap : ∀ {X Y Z : Set} (f : X → Y) (m : T X) (k : Y → T Z)
          → (fmapT f m >>=T k) ≡ (m >>=T λ x → k (f x))
bind-fmap f (mkT tr stopped)     k = refl
bind-fmap f (mkT tr (returns x)) k = refl

ret-bind : ∀ {X Y : Set} (h : X) (f : X → T Y) → (returnT h >>=T f) ≡ f h
ret-bind h f = refl

bind-congʳ : ∀ {X Y : Set} (m : T X) {k k′ : X → T Y} → (∀ x → k x ≡ k′ x) → (m >>=T k) ≡ (m >>=T k′)
bind-congʳ m h = cong (m >>=T_) (extensionality h)

------------------------------------------------------------------------
-- Congruence
------------------------------------------------------------------------

module _ {n} {Γ : Ctx n} where

  pair-cong : ∀ {Ψ₁ Ψ₂ A B} {a a′ : Expr Γ Ψ₁ A} {b b′ : Expr Γ Ψ₂ B}
            → a ≈ a′ → b ≈ b′ → pair a b ≈ pair a′ b′
  pair-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → returnT (va , vb))

  -- The binary primitives: one clause shape, one `cong₂` each.
  add-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → add a b ≈ add a′ b′
  add-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM add-info fmt (va , vb)))
  sub-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → sub a b ≈ sub a′ b′
  sub-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM sub-info fmt (va , vb)))
  mul-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → mul a b ≈ mul a′ b′
  mul-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM mul-info fmt (va , vb)))
  div-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → div a b ≈ div a′ b′
  div-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM div-info fmt (va , vb)))
  mod-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → mod' a b ≈ mod' a′ b′
  mod-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM mod-info fmt (va , vb)))
  fadd-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fadd a b ≈ fadd a′ b′
  fadd-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM fadd-info fmt (va , vb)))
  fsub-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fsub a b ≈ fsub a′ b′
  fsub-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM fsub-info fmt (va , vb)))
  fmul-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fmul a b ≈ fmul a′ b′
  fmul-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM fmul-info fmt (va , vb)))
  fdiv-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fdiv a b ≈ fdiv a′ b′
  fdiv-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM fdiv-info fmt (va , vb)))
  lt-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → lt a b ≈ lt a′ b′
  lt-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM lt-info fmt (va , vb)))
  le-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → le a b ≈ le a′ b′
  le-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM le-info fmt (va , vb)))
  gt-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → gt a b ≈ gt a′ b′
  gt-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM gt-info fmt (va , vb)))
  ge-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → ge a b ≈ ge a′ b′
  ge-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM ge-info fmt (va , vb)))
  eq-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → eq a b ≈ eq a′ b′
  eq-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM eq-info fmt (va , vb)))
  ne-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → ne a b ≈ ne a′ b′
  ne-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → resT-lift (semM ne-info fmt (va , vb)))

  neg-cong : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ a′ → neg a ≈ neg a′
  neg-cong = cong (λ X σ dγ → X σ dγ >>=T λ v → resT-lift (semM neg-info fmt v))

  i2f-cong : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ a′ → i2f a ≈ i2f a′
  i2f-cong = cong (λ X σ dγ → X σ dγ >>=T λ va → resT-lift (semM i2f-info fmt va))

  coerce-cong : ∀ {Ψ A B} (p : A <: B) {a a′ : Expr Γ Ψ A} → a ≈ a′ → coerce p a ≈ coerce p a′
  coerce-cong p = cong (λ X σ dγ → fmapT ⟦ p ⟧<: (X σ dγ))

  morph-app-cong : ∀ {Ψ A B} (ir : IR ⌊ A ⌋ ⌊ B ⌋) {a a′ : Expr Γ Ψ A} → a ≈ a′ → morph-app {A = A} {B = B} ir a ≈ morph-app {A = A} {B = B} ir a′
  morph-app-cong {Ψ} {A} {B} ir = cong (λ X σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))) dγ)
    >>=T λ v → subst T (cohᴰ B) (evalᴰ fmt (calls σ) ir (subst (λ z → z) (sym (cohᴰ A)) v)))

  app-cong : ∀ {Ψ₁ Ψ₂ A B q} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind q Once.Type.pure ] B)} {x x′ : Expr Γ Ψ₂ A}
           → f ≈ f′ → x ≈ x′ → app f x ≈ app f′ x′
  app-cong {Ψ₁} {Ψ₂} {q = Zero} ef ex = cong (λ X σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ) >>=T λ vf → vf _) ef
  app-cong {Ψ₁} {Ψ₂} {q = One} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx)
  app-cong {Ψ₁} {Ψ₂} {q = Many} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx)

  effApp-cong : ∀ {Ψ₁ Ψ₂ A B} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many Once.Type.eff ] B)} {x x′ : Expr Γ Ψ₂ A}
              → f ≈ f′ → x ≈ x′ → effApp f x ≈ effApp f′ x′
  effApp-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ → returnT (λ _ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vx → vf vx))

  comp-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)}
            → f ≈ f′ → g ≈ g′ → comp' f g ≈ comp' f′ g′
  comp-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=T λ vg →
    returnT (λ a → vg a >>=T vf))

  copair-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)}
              → f ≈ f′ → g ≈ g′ → copair' f g ≈ copair' f′ g′
  copair-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vg →
    returnT (λ ab → [ vf , vg ]′ ab))

  fork-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)}
            → f ≈ f′ → g ≈ g′ → fork' f g ≈ fork' f′ g′
  fork-cong {Ψ₁} {Ψ₂} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ vf →
    Y σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vg →
    returnT (λ a → vf a >>=T λ b → vg a >>=T λ c → returnT (b , c)))

  curry-cong : ∀ {Ψ A B C π₀ π} {f f′ : Expr Γ Ψ ((A * B) ⇒[ mk-kind Many π ] C)}
             → f ≈ f′ → curry' {π₀ = π₀} f ≈ curry' f′
  curry-cong = cong (λ X σ dγ → X σ dγ >>=T λ vf → returnT (λ a → returnT (λ b → vf (a , b))))

  cata-cong : ∀ {F A π} (wf : WellFormedF F) {g g′ : Expr ∅ zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
            → g ≈ g′ → cata {Γ = Γ} wf g ≈ cata wf g′
  cata-cong {F} {A} wf = cong (λ X σ dγ → X σ _ >>=T λ valg →
    returnT (λ x → sem-cata wf (cata-ev-algˢ {F} {A} (returnT valg)) x))

  ana-cong : ∀ {F A π₀ π} (wf : WellFormedF F) {g g′ : Expr ∅ zeroUsage (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A)}
           → g ≈ g′ → ana {Γ = Γ} {π₀ = π₀} wf g ≈ ana wf g′
  ana-cong {F} {A} wf = cong (λ X σ dγ → returnT (λ a → returnT (anaFᵈ F
            (λ a' → fmapT (coerce-functor-D F A) (X σ _ >>=T λ clo → clo a')) a)))

  let-cong : ∀ {Ψ₁ Ψ₂ A B q} {e₁ e₁′ : Expr Γ Ψ₁ A} {e₂ e₂′ : Expr (_,_^_ Γ A Many) (q ∷ Ψ₂) B}
           → e₁ ≈ e₁′ → e₂ ≈ e₂′ → let' e₁ e₂ ≈ let' e₁′ e₂′
  let-cong {Ψ₁} {Ψ₂} {A} {q = Zero} _ = cong (λ Y σ dγ →
    Y σ (bindᴰ0 {Γ = Γ} {A = A} (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ)))
  let-cong {Ψ₁} {Ψ₂} {A} {q = One} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) dγ) >>=T λ v1 →
    Y σ (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) dγ) v1))
  let-cong {Ψ₁} {Ψ₂} {A} {q = Many} = cong₂ (λ X Y σ dγ →
    X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) dγ) >>=T λ v1 →
    Y σ (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) dγ) v1))

  case-cong : ∀ {Ψs Ψₗ Ψᵣ qℓ qr A B C} {s s′ : Expr Γ Ψs (A + B)}
                {l l′ : Expr (_,_^_ Γ A Many) (qℓ ∷ Ψₗ) C} {r r′ : Expr (_,_^_ Γ B Many) (qr ∷ Ψᵣ) C}
            → s ≈ s′ → l ≈ l′ → r ≈ r′ → case' s l r ≈ case' s′ l′ r′
  case-cong {Ψs} {Ψₗ} {Ψᵣ} {qℓ} {qr} {A} {B} {s′ = s′} {l′ = l′} {r = r} es el er =
    trans (cong₂ (λ X Y σ dγ →
      X σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ) >>=T λ v →
      [ (λ a → Y σ (bindᴰ {Γ = Γ} {A = A} qℓ (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
      , (λ b → ⟦ r ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = B} qr (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b)) ]′ v) es el)
          (cong (λ Z σ dγ →
      ⟦ s′ ⟧ˢ fmt σ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ) >>=T λ v →
      [ (λ a → ⟦ l′ ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = A} qℓ (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
      , (λ b → Z σ (bindᴰ {Γ = Γ} {A = B} qr (restrictᴰ {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b)) ]′ v) er)

  lam-cong : ∀ {Ψ q' π A B} (q : Quantity) (≤p : (q' ≤q q) ≡ true) {b b′ : Expr (_,_^_ Γ A Many) (q' ∷ Ψ) B}
           → b ≈ b′ → lam {π = π} q ≤p b ≈ lam q ≤p b′
  lam-cong {q' = Zero} {A = A} Zero ≤p = cong (λ X σ dγ → returnT (λ _ → X σ (bindᴰ0 {Γ = Γ} {A = A} dγ)))
  lam-cong {q' = Zero} {A = A} One  ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ0 {Γ = Γ} {A = A} dγ)))
  lam-cong {q' = Zero} {A = A} Many ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ0 {Γ = Γ} {A = A} dγ)))
  lam-cong {q' = One}  {A = A} One  ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ {Γ = Γ} {A = A} One dγ a)))
  lam-cong {q' = One}  {A = A} Many ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ {Γ = Γ} {A = A} One dγ a)))
  lam-cong {q' = Many} {A = A} Many ≤p = cong (λ X σ dγ → returnT (λ a → X σ (bindᴰ {Γ = Γ} {A = A} Many dγ a)))
  lam-cong {q' = One}  Zero ()
  lam-cong {q' = Many} Zero ()
  lam-cong {q' = Many} One  ()

------------------------------------------------------------------------
-- Coercion
------------------------------------------------------------------------

-- A conversion's meaning on a reflexive witness is the identity.
fmap-refl : ∀ (A : Type) (m : T ⟦ A ⟧ᴰ) → fmapT ⟦ <:-refl A ⟧<: m ≡ m
fmap-refl A m = trans (fmapT-cong (<:-refl-id A) m) (fmapT-id m)

module _ {n} {Γ : Ctx n} where

  coerce-refl : ∀ {Ψ A} (e : Expr Γ Ψ A) → coerce (<:-refl A) e ≈ e
  coerce-refl {A = A} e = extensionality λ σ → extensionality λ dγ → fmap-refl A _

  coerce-trans : ∀ {Ψ A B C} (p : A <: B) (q : B <: C) (e : Expr Γ Ψ A)
               → coerce q (coerce p e) ≈ coerce (<:-trans p q) e
  coerce-trans p q e = extensionality λ σ → extensionality λ dγ →
    trans (fmapT-∘ ⟦ q ⟧<: ⟦ p ⟧<: _) (fmapT-cong (λ x → sym (<:-trans-∘ p q x)) _)

  coerce-uniq : ∀ {Ψ A B} (p q : A <: B) (e : Expr Γ Ψ A) → coerce p e ≈ coerce q e
  coerce-uniq p q e = cong (λ r → ⟦ coerce r e ⟧ˢ fmt) (<:-unique p q)

  pair-coerce : ∀ {Ψ₁ Ψ₂ A A′ B B′} (pa : A <: A′) (pb : B <: B′) (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
              → pair (coerce pa a) (coerce pb b) ≈ coerce (sub-prod pa pb) (pair a b)
  pair-coerce pa pb a b = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap ⟦ pa ⟧<: _ _)
     (trans (bind-congʳ _ (λ va → bind-fmap ⟦ pb ⟧<: _ _))
      (sym (trans (fmap-bind _ _ _) (bind-congʳ _ (λ va → fmap-bind _ _ _)))))

  -- Converting the head's domain is converting the argument.
  app-coerce : ∀ {Ψ₁ Ψ₂ X A′ B} (a : X <: A′) (g : Once.Type.pure ⊑π Once.Type.pure)
                 (f : Expr Γ Ψ₁ (A′ ⇒[ mk-kind Many Once.Type.pure ] B)) (x : Expr Γ Ψ₂ X)
             → app (coerce (sub-arr a (<:-refl B) g) f) x ≈ app f (coerce a x)
  app-coerce {B = B} a g f x = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ _ _)
     (bind-congʳ _ λ vf → trans (bind-congʳ _ (λ vx → fmap-refl B _)) (sym (bind-fmap ⟦ a ⟧<: _ _)))

  -- Converting the outer arm's codomain is converting the composite's.
  comp-post : ∀ {Ψ₁ Ψ₂ A M B B′ π} (p : B <: B′) (r r′ : π ⊑π π)
                (f : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M))
            → comp' (coerce (sub-arr (<:-refl M) p r) f) g ≈ coerce (sub-arr (<:-refl A) p r′) (comp' f g)
  comp-post {A = A} {M} p r r′ f g = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ _ _)
     (sym (trans (fmap-bind _ _ _) (bind-congʳ _ λ vf → trans (fmap-bind _ _ _) (bind-congʳ _ λ vg →
       cong returnT (extensionality λ x →
         trans (cong (λ y → fmapT ⟦ p ⟧<: (vg y >>=T vf)) (<:-refl-id A x))
          (trans (fmap-bind _ (vg x) vf)
                 (bind-congʳ (vg x) λ m → cong (λ z → fmapT ⟦ p ⟧<: (vf z)) (sym (<:-refl-id M m)))))))))

  -- Converting the outer arm's domain is converting the inner arm's codomain.
  comp-pre : ∀ {Ψ₁ Ψ₂ A B B′ C C′ π π′} (q : B <: B′) (c : C′ <: C) (g : π′ ⊑π π)
               (f : Expr Γ Ψ₁ (B′ ⇒[ mk-kind Many π′ ] C′)) (h : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B))
           → comp' (coerce (sub-arr q c g) f) h
             ≈ comp' (coerce (sub-arr (<:-refl B′) c g) f) (coerce (sub-arr (<:-refl A) q (⊑π-refl π)) h)
  comp-pre {A = A} {B′ = B′} q c g f h = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ _ _)
     (sym (trans (bind-fmap _ _ _) (bind-congʳ _ λ vf → trans (bind-fmap _ _ _) (bind-congʳ _ λ vh →
       cong returnT (extensionality λ x →
         trans (bind-fmap ⟦ q ⟧<: _ _)
          (trans (cong (λ y → vh y >>=T λ z → fmapT ⟦ c ⟧<: (vf (⟦ <:-refl B′ ⟧<: (⟦ q ⟧<: z)))) (<:-refl-id A x))
                 (bind-congʳ (vh x) λ z → cong (λ w → fmapT ⟦ c ⟧<: (vf w)) (<:-refl-id B′ (⟦ q ⟧<: z)))))))))

  -- Converting a lambda's body is converting the lambda.
  lam-coerce : ∀ {Ψ q' π A B B′} (≤p : (q' ≤q Many) ≡ true) (p : B <: B′) (b : Expr (_,_^_ Γ A Many) (q' ∷ Ψ) B)
             → lam {π = π} Many ≤p (coerce p b) ≈ coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (lam Many ≤p b)
  lam-coerce {q' = Zero} ≤p p b = refl
  lam-coerce {q' = One} {A = A} ≤p p b = extensionality λ σ → extensionality λ dγ →
    cong returnT (extensionality λ x →
      cong (λ y → fmapT ⟦ p ⟧<: (⟦ b ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = A} One dγ y))) (sym (<:-refl-id A x)))
  lam-coerce {q' = Many} {A = A} ≤p p b = extensionality λ σ → extensionality λ dγ →
    cong returnT (extensionality λ x →
      cong (λ y → fmapT ⟦ p ⟧<: (⟦ b ⟧ˢ fmt σ (bindᴰ {Γ = Γ} {A = A} Many dγ y))) (sym (<:-refl-id A x)))

  copair-coerce : ∀ {Ψ₁ Ψ₂ A B C C′ π} (p : C <: C′) (r : π ⊑π π)
                    (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)) (g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C))
                → copair' (coerce (sub-arr (<:-refl A) p r) f) (coerce (sub-arr (<:-refl B) p r) g)
                  ≈ coerce (sub-arr (<:-refl (A + B)) p r) (copair' f g)
  copair-coerce p r f g = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ _ _) (trans (bind-congʳ _ (λ vf → bind-fmap _ _ _))
      (sym (trans (fmap-bind _ _ _) (bind-congʳ _ λ vf → trans (fmap-bind _ _ _) (bind-congʳ _ λ vg →
        cong returnT (extensionality λ { (inj₁ a) → refl ; (inj₂ b) → refl }))))))

  fork-coerce : ∀ {Ψ₁ Ψ₂ A B B′ C C′ π} (pb : B <: B′) (pc : C <: C′) (r : π ⊑π π)
                  (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C))
              → fork' (coerce (sub-arr (<:-refl A) pb r) f) (coerce (sub-arr (<:-refl A) pc r) g)
                ≈ coerce (sub-arr (<:-refl A) (sub-prod pb pc) r) (fork' f g)
  fork-coerce pb pc r f g = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ _ _) (trans (bind-congʳ _ (λ vf → bind-fmap _ _ _))
      (sym (trans (fmap-bind _ _ _) (bind-congʳ _ λ vf → trans (fmap-bind _ _ _) (bind-congʳ _ λ vg →
        cong returnT (extensionality λ x →
          trans (fmap-bind _ _ _) (sym (trans (bind-fmap ⟦ pb ⟧<: _ _) (bind-congʳ _ λ b →
            trans (bind-fmap ⟦ pc ⟧<: _ _) (sym (trans (fmap-bind _ _ _) (bind-congʳ _ λ c → refl))))))))))))

  -- `initial` at any codomain: a function out of `Void` is unique.
  initial-coerce : ∀ {A π} (r : π ⊑π π)
                 → coerce (sub-arr sub-void sub-void r) (lift-morphism {Γ = Γ} {A = Void} {B = Void} {π = π} IR.initial)
                   ≈ lift-morphism {Γ = Γ} {A = Void} {B = A} {π = π} IR.initial
  initial-coerce r = extensionality λ σ → extensionality λ dγ → cong returnT (extensionality λ ())

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
  trans (cong (fmapT inj₁) (seq-rel F p r)) (trans (fmapT-∘ inj₁ _ _) (sym (fmapT-∘ _ inj₁ (seqF F x₂))))
seq-rel (F ⊕ G) p {inj₂ _} {inj₂ y₂} r =
  trans (cong (fmapT inj₂) (seq-rel G p r)) (trans (fmapT-∘ inj₂ _ _) (sym (fmapT-∘ _ inj₂ (seqF G y₂))))
seq-rel (F ⊕ G) p {inj₁ _} {inj₂ _} ()
seq-rel (F ⊕ G) p {inj₂ _} {inj₁ _} ()
seq-rel (F ⊗ G) p {_ , _} {x₂ , y₂} (r₁ , r₂) rewrite seq-rel F p r₁ | seq-rel G p r₂ =
  trans (bind-fmap _ (seqF F x₂) _) (trans (bind-congʳ (seqF F x₂) (λ u → bind-fmap _ (seqF G y₂) _))
    (sym (trans (fmap-bind _ (seqF F x₂) _) (bind-congʳ (seqF F x₂) λ u → fmap-bind _ (seqF G y₂) _))))

layer-id : ∀ F {A A′ : Type} (d : ⟦ F ⟧T A′ <: ⟦ F ⟧T A) (p : A <: A′) (l : ⟦ F ⟧F ⟦ A ⟧ᴰ)
         → ⟦ d ⟧<: (coerce-functor⁻¹-D F A′ (sem-fmap F ⟦ p ⟧<: l)) ≡ coerce-functor⁻¹-D F A l
layer-id (K B) d p l = trans (cong (λ r → ⟦ r ⟧<: _) (<:-unique d (<:-refl B))) (<:-refl-id B _)
layer-id Id {A} d p l =
  trans (sym (<:-trans-∘ p d l)) (trans (cong (λ r → ⟦ r ⟧<: l) (<:-unique (<:-trans p d) (<:-refl A))) (<:-refl-id A l))
layer-id (F ⊕ G) (Once.Type.Sub.sub-sum d₁ d₂) p (inj₁ x) = cong inj₁ (layer-id F d₁ p x)
layer-id (F ⊕ G) (Once.Type.Sub.sub-sum d₁ d₂) p (inj₂ y) = cong inj₂ (layer-id G d₂ p y)
layer-id (F ⊗ G) (sub-prod d₁ d₂) p (x , y) = cong₂ _,_ (layer-id F d₁ p x) (layer-id G d₂ p y)

cata-core : ∀ {F} (wf : WellFormedF F) {A A′ : Type} {π π′ : Purity}
              (d : ⟦ F ⟧T A′ <: ⟦ F ⟧T A) (p : A <: A′) (g : π ⊑π π′)
              (valg : ⟦ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ⟧ᴰ) (x : ⟦μ⟧ F)
          → sem-cata wf (cata-ev-algˢ {F} {A′} (returnT (⟦ sub-arr {q = Many} d p g ⟧<: valg))) x
            ≡ fmapT ⟦ p ⟧<: (sem-cata wf (cata-ev-algˢ {F} {A} (returnT valg)) x)
cata-core {F} wf {A} {A′} d p g valg x =
  cataS-rel {translateF Carrier Carrier F} (λ t₁ t₂ → t₁ ≡ fmapT ⟦ p ⟧<: t₂) algR x
  where
    algR : ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) (λ t₁ t₂ → t₁ ≡ fmapT ⟦ p ⟧<: t₂) y₁ y₂
         → cata-ev-algˢ {F} {A′} (returnT (⟦ sub-arr {q = Many} d p g ⟧<: valg)) (coerce-μ-out wf _ y₁)
           ≡ fmapT ⟦ p ⟧<: (cata-ev-algˢ {F} {A} (returnT valg) (coerce-μ-out wf _ y₂))
    S₂ : ∀ y₂ → T (⟦ F ⟧F ⟦ A ⟧ᴰ)
    S₂ y₂ = seqF F (coerce-μ-out wf _ y₂)
    algR {y₁} {y₂} r =
      trans (bind-congʳ (seqF F (coerce-μ-out wf _ y₁)) (λ l → ret-bind (⟦ sub-arr {q = Many} d p g ⟧<: valg) (λ c → c (coerce-functor⁻¹-D F A′ l))))
      (trans (cong (λ m → m >>=T λ l → ⟦ sub-arr {q = Many} d p g ⟧<: valg (coerce-functor⁻¹-D F A′ l)) (seq-rel F p (out-rel wf _ r)))
      (trans (bind-fmap (sem-fmap F ⟦ p ⟧<:) (S₂ y₂) (λ l → ⟦ sub-arr {q = Many} d p g ⟧<: valg (coerce-functor⁻¹-D F A′ l)))
      (trans (bind-congʳ (S₂ y₂) (λ l → cong (λ z → fmapT ⟦ p ⟧<: (valg z)) (layer-id F d p l)))
      (trans (sym (fmap-bind ⟦ p ⟧<: (S₂ y₂) (λ l → valg (coerce-functor⁻¹-D F A l))))
             (cong (fmapT ⟦ p ⟧<:) (sym (bind-congʳ (S₂ y₂) (λ l → ret-bind valg (λ c → c (coerce-functor⁻¹-D F A l))))))))))

module _ {n} {Γ : Ctx n} where

  cata-coerce : ∀ {F A A′ π} (wf : WellFormedF F) (d : ⟦ F ⟧T A′ <: ⟦ F ⟧T A) (p : A <: A′) (g : π ⊑π π)
                  (alg : Expr ∅ zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
              → cata {Γ = Γ} wf (coerce (sub-arr {q = Many} d p g) alg)
                ≈ coerce (sub-arr (<:-refl (μ-type F)) p (⊑π-refl π)) (cata {Γ = Γ} wf alg)
  cata-coerce wf d p g alg = extensionality λ σ → extensionality λ dγ →
    trans (bind-fmap _ _ _)
     (trans (bind-congʳ _ λ valg → cong returnT (extensionality λ x → cata-core wf d p g valg x))
            (sym (fmap-bind _ _ _)))
