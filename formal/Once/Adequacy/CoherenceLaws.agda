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
-- Plan 0.119 D5: meanings are `T∞` runs, compared step for step. Two terms
-- mean the same (`_≈ˢ_`) when, in every self-related definitions environment,
-- related environments give related runs — the two-term form of the source
-- semantics' fundamental lemma (`SourceRefl.SD-rel`, which is `≈-refl`). A
-- congruence is then a bind congruence; a coercion law is relational
-- naturality, by associativity on either side.
------------------------------------------------------------------------

import Once.Spec.Type as SpT

open import Data.Nat using (ℕ)
open import Once.Internal.Weaken using (RelD-bool)
open import Once.Denotation.ValueRel using (RelS-mono)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun)
open import Once.Spec.Numerics using (TargetNum)

open import Once.Type.Grade using (_≤qᵇ_)
module Once.Adequacy.CoherenceLaws (fmt : TargetNum) where

open import Data.Bool using (true)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (mk-kind; Many; One; Zero; Purity; Quantity; fin; act)
open import Once.Spec.Type using (Type; Void; Int; Float; _*_; _+_; _⇒[_]_; K; Id; _⊕_; _⊗_)
open import Once.Spec.Type using (μ)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-void)
open import Once.Internal.Type.Sub using (sub-prod)
open import Once.Spec.Grade using (_⊑π_)
open import Once.Internal.Laws.SubLaws using (<:-trans; <:-unique)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl)
open import Once.Internal.Context using (Ctx; Usage; ⟦_⟧ᶜ; _↾_; zeroUsage; _*ᵘ_; _⊔ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Spec.Context using (_∷_; _▸_)
open import Once.Surface.Syntax using (Expr; lam; app; effApp; pair; let'; case'; neg; i2f; add; sub; mul; div; mod'; fadd; fsub; fmul; fdiv; lt; le; gt; ge; eq; ne; coerce; morph-app; comp'; copair'; fork'; curry'; cata; ana; loop; lift-morphism)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; seqF∞)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0)
open import Once.Denotation.Sub using (⟦_⟧<:; <:-refl-rel)
open import Once.Semantics.Machine using (sem-cata; coerce-μ-out; ⟦_⟧F; ⟦μ⟧)
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Internal.Type.WellFormed using (WellFormedF; wf-Sum; wf-Prod)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Internal.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Once.Denotation.ValueDomain using (coerce-functor⁻¹-D; ⟦_⟧ᴰ)
open import Once.Arith.SigOp.Builders using (add-info; sub-info; mul-info; div-info; mod-info;
  fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info; neg-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.IR as IR
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelS-bind; relS-ret; RelS-iter∞)
open import Once.Denotation.ValueRel using (RelD; base-refl; RelS-fmap; RelS-fmapˡ; RelS-assocˡ; RelS-assocʳ; RelS-assoc₂; RelS-unfmapʳ;
  retargetˡ; retargetʳ; seqF∞-rel; FRel; fr-K; fr-Id; fr-inl; fr-inr; fr-pair; cfD⁻¹-rel)
open import Once.Denotation.ValueRelPER using (RelS-sym; RelS-trans; RelS-pairʳ; RelD-sym; RelD-trans; RelD-rightself)
open import Once.Denotation.EvalRel using (liftFn-rel)
open import Once.Adequacy.EnvRel using (restrict-rel; bind-rel)
open import Once.Adequacy.SourceRefl fmt using (RelDefs; SD-rel; sigOp-rel; <:-rel; <:-trans-rel; <:-refl-relʳ; cata-clo-rel; ana-clo-rel)
import Once.Denotation.SourceDenote as SD
open SD using (⟦_⟧ˢ; cata-ev-algˢ; DefsSem)
open SD.DefsSem using (calls)

infix 4 _≈ˢ_ _≈_
_≈ˢ_ : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → Expr Γ Ψ A → Expr Γ Ψ A → Set
_≈ˢ_ {Γ = Γ} {Ψ = Ψ} {A = A} a b =
  ∀ (σ : DefsSem) → RelDefs σ σ → ∀ {dγ dγ′ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ} → RelD ⟦ Γ ↾ Ψ ⟧ᶜ dγ dγ′
  → RelS (RelD A) (⟦ a ⟧ˢ fmt σ dγ) (⟦ b ⟧ˢ fmt σ dγ′)

-- Two terms MEAN the same. A record rather than the bare relation so that it
-- is injective for unification: from `a ≈ b` Agda can read off `a` and `b`.
record _≈_ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (a b : Expr Γ Ψ A) : Set where
  constructor ≈-intro
  field ≈-out : a ≈ˢ b

≈-refl : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {a : Expr Γ Ψ A} → a ≈ a
≈-refl {a = a} = ≈-intro (λ σ rσ r → SD-rel rσ a r)

≈-sym : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {a b : Expr Γ Ψ A} → a ≈ b → b ≈ a
≈-sym {Γ = Γ} {Ψ = Ψ} {A = A} (≈-intro e) = ≈-intro (λ σ rσ r → RelS-sym (RelD-sym A) (e σ rσ (RelD-sym ⟦ Γ ↾ Ψ ⟧ᶜ r)))

≈-trans : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {a b c : Expr Γ Ψ A} → a ≈ b → b ≈ c → a ≈ c
≈-trans {Γ = Γ} {Ψ = Ψ} {A = A} (≈-intro e) (≈-intro f) =
  ≈-intro (λ σ rσ r → RelS-trans (RelD-trans A) (e σ rσ r) (f σ rσ (RelD-rightself ⟦ Γ ↾ Ψ ⟧ᶜ r)))

-- Equal terms mean the same.
≡→≈ : ∀ {m} {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} {a b : Expr Γ Ψ A} → a ≡ b → a ≈ b
≡→≈ refl = ≈-refl

------------------------------------------------------------------------
-- Congruence
------------------------------------------------------------------------

module _ {m n} {Γ : Ctx m n} where

  pair-congˢ : ∀ {Ψ₁ Ψ₂ A B} {a a′ : Expr Γ Ψ₁ A} {b b′ : Expr Γ Ψ₂ B}
            → a ≈ˢ a′ → b ≈ˢ b′ → pair a b ≈ˢ pair a′ b′
  pair-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → relS-ret (ra , rb)

  -- The binary primitives: one clause shape, one bind congruence each.
  add-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → add a b ≈ˢ add a′ b′
  add-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ add-info (ra , rb)
  sub-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → sub a b ≈ˢ sub a′ b′
  sub-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ sub-info (ra , rb)
  mul-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → mul a b ≈ˢ mul a′ b′
  mul-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ mul-info (ra , rb)
  div-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → div a b ≈ˢ div a′ b′
  div-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ div-info (ra , rb)
  mod-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → mod' a b ≈ˢ mod' a′ b′
  mod-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ mod-info (ra , rb)
  fadd-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fadd a b ≈ˢ fadd a′ b′
  fadd-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ fadd-info (ra , rb)
  fsub-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fsub a b ≈ˢ fsub a′ b′
  fsub-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ fsub-info (ra , rb)
  fmul-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fmul a b ≈ˢ fmul a′ b′
  fmul-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ fmul-info (ra , rb)
  fdiv-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ˢ a′ → b ≈ˢ b′ → fdiv a b ≈ˢ fdiv a′ b′
  fdiv-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → sigOp-rel rσ fdiv-info (ra , rb)
  lt-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → lt a b ≈ˢ lt a′ b′
  lt-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → RelD-bool {x = x} {y = y}) (sigOp-rel rσ lt-info (ra , rb))
  le-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → le a b ≈ˢ le a′ b′
  le-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → RelD-bool {x = x} {y = y}) (sigOp-rel rσ le-info (ra , rb))
  gt-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → gt a b ≈ˢ gt a′ b′
  gt-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → RelD-bool {x = x} {y = y}) (sigOp-rel rσ gt-info (ra , rb))
  ge-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → ge a b ≈ˢ ge a′ b′
  ge-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → RelD-bool {x = x} {y = y}) (sigOp-rel rσ ge-info (ra , rb))
  eq-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → eq a b ≈ˢ eq a′ b′
  eq-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → RelD-bool {x = x} {y = y}) (sigOp-rel rσ eq-info (ra , rb))
  ne-congˢ : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ˢ a′ → b ≈ˢ b′ → ne a b ≈ˢ ne a′ b′
  ne-congˢ ea eb σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) λ ra → RelS-bind (eb σ rσ (restrict-rel {Γ = Γ} _ r)) λ rb → RelS-mono (λ {x} {y} → RelD-bool {x = x} {y = y}) (sigOp-rel rσ ne-info (ra , rb))

  neg-congˢ : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ˢ a′ → neg a ≈ˢ neg a′
  neg-congˢ ea σ rσ r = RelS-bind (ea σ rσ r) (sigOp-rel rσ neg-info)

  i2f-congˢ : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ˢ a′ → i2f a ≈ˢ i2f a′
  i2f-congˢ ea σ rσ r = RelS-bind (ea σ rσ r) (sigOp-rel rσ i2f-info)

  coerce-congˢ : ∀ {A B : Ty m} {Ψ} (p : A <: B) {a a′ : Expr Γ Ψ A} → a ≈ˢ a′ → coerce p a ≈ˢ coerce p a′
  coerce-congˢ p ea σ rσ r = RelS-fmap (ea σ rσ r) (<:-rel p)

  morph-app-congˢ : ∀ {Ψ A B} (ir : IR ⌊ A ⌋ ⌊ B ⌋) {a a′ : Expr Γ Ψ A} → a ≈ˢ a′ → morph-app {A = A} {B = B} ir a ≈ˢ morph-app {A = A} {B = B} ir a′
  morph-app-congˢ {Ψ} {A} {B} ir ea σ rσ r =
    RelS-bind (ea σ rσ (restrict-rel {Γ = Γ} _ r)) (liftFn-rel fmt (proj₁ rσ) {A} {B} ir)

  app-congˢ : ∀ {Ψ₁ Ψ₂ A B q} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind q Once.Spec.Grade.pure ] B)} {x x′ : Expr Γ Ψ₂ A}
           → f ≈ˢ f′ → x ≈ˢ x′ → app f x ≈ˢ app f′ x′
  app-congˢ {q = Zero} ef ex σ rσ r = RelS-bind (ef σ rσ (restrict-rel {Γ = Γ} _ r)) (λ rf → rf)
  app-congˢ {q = One} ef ex σ rσ r =
    RelS-bind (ef σ rσ (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (ex σ rσ (restrict-rel {Γ = Γ} _ r)) λ rx → rf rx
  app-congˢ {q = Many} ef ex σ rσ r =
    RelS-bind (ef σ rσ (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (ex σ rσ (restrict-rel {Γ = Γ} _ r)) λ rx → rf rx

  effApp-congˢ : ∀ {Ψ₁ Ψ₂ A B π} {g : Once.Spec.Grade.EffGrade π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {x x′ : Expr Γ Ψ₂ A}
              → f ≈ˢ f′ → x ≈ˢ x′ → effApp {g = g} f x ≈ˢ effApp {g = g} f′ x′
  effApp-congˢ ef ex σ rσ r =
    relS-ret λ _ → RelS-bind (ef σ rσ (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (ex σ rσ (restrict-rel {Γ = Γ} _ r)) λ rx → rf rx

  comp-congˢ : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)}
            → f ≈ˢ f′ → g ≈ˢ g′ → comp' f g ≈ˢ comp' f′ g′
  comp-congˢ ef eg σ rσ r =
    RelS-bind (ef σ rσ (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (eg σ rσ (restrict-rel {Γ = Γ} _ r)) λ rg →
    relS-ret (λ ra → RelS-bind (rg ra) rf)

  copair-congˢ : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)}
              → f ≈ˢ f′ → g ≈ˢ g′ → copair' f g ≈ˢ copair' f′ g′
  copair-congˢ ef eg σ rσ r =
    RelS-bind (ef σ rσ (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (eg σ rσ (restrict-rel {Γ = Γ} _ r)) λ rg →
    relS-ret λ { {inj₁ _} {inj₁ _} ra → rf ra ; {inj₂ _} {inj₂ _} rb → rg rb ; {inj₁ _} {inj₂ _} () ; {inj₂ _} {inj₁ _} () }

  fork-congˢ : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)}
            → f ≈ˢ f′ → g ≈ˢ g′ → fork' f g ≈ˢ fork' f′ g′
  fork-congˢ ef eg σ rσ r =
    RelS-bind (ef σ rσ (restrict-rel {Γ = Γ} _ r)) λ rf → RelS-bind (eg σ rσ (restrict-rel {Γ = Γ} _ r)) λ rg →
    relS-ret (λ ra → RelS-bind (rf ra) λ rb → RelS-bind (rg ra) λ rc → relS-ret (rb , rc))

  curry-congˢ : ∀ {Ψ A B C π₀ π} {f f′ : Expr Γ Ψ ((A * B) ⇒[ mk-kind Many π ] C)}
             → f ≈ˢ f′ → curry' {π₀ = π₀} f ≈ˢ curry' f′
  curry-congˢ ef σ rσ r = RelS-bind (ef σ rσ r) λ rf → relS-ret (λ ra → relS-ret (λ rb → rf (ra , rb)))

  cata-congˢ : ∀ {Δₖ : KCtx m} {A : Ty m} {F : Fun m} {Ψ π} (wf : WFFun Δₖ F) {g g′ : Expr Γ Ψ (SpT.⟦ F ⟧F A ⇒[ mk-kind Many π ] A)}
            → g ≈ˢ g′ → cata {Γ = Γ} wf g ≈ˢ cata wf g′
  cata-congˢ {A = A} {F = F} {π = π} wf eg σ rσ r =
    RelS-bind (eg σ rσ (restrict-rel {Γ = Γ} _ r)) λ ralg → relS-ret (cata-clo-rel {A = A} {F = F} {π = π} wf ralg)

  -- D273: the coalgebra lives in the context and is bound once, as `cata`'s.
  ana-congˢ : ∀ {Δₖ : KCtx m} {A : Ty m} {F : Fun m} {Ψ π₀ φ} (wf : WFFun Δₖ F) {g g′ : Expr Γ Ψ (A ⇒[ mk-kind Many (fin φ) ] SpT.⟦ F ⟧F A)}
           → g ≈ˢ g′ → ana {Γ = Γ} {π₀ = π₀} {φ = φ} wf g ≈ˢ ana wf g′
  ana-congˢ {A = A} {F = F} {φ = φ} wf eg σ rσ r =
    RelS-bind (eg σ rσ (restrict-rel {Γ = Γ} _ r)) λ rc → relS-ret (λ ra → relS-ret (ana-clo-rel {A = A} {F = F} {φ = φ} wf rc ra))

  -- the loop: related rounds, bound once, iterate to related loops.
  loop-congˢ : ∀ {Ψ A B} {g g′ : Expr Γ Ψ (A ⇒[ mk-kind Many act ] (B + A))}
            → g ≈ˢ g′ → loop {Γ = Γ} g ≈ˢ loop g′
  loop-congˢ {A = A} {B} eg σ rσ r =
    RelS-bind (eg σ rσ (restrict-rel {Γ = Γ} _ r)) λ {c} {c′} rc →
      relS-ret (λ ra → RelS-iter∞ {RB = RelD B} {S = RelD (B + A)} {f = c} {f′ = c′}
                                  (λ rb → rb) rc (λ ()) (λ ()) ra)

  let-congˢ : ∀ {Ψ₁ Ψ₂ A B q} {e₁ e₁′ : Expr Γ Ψ₁ A} {e₂ e₂′ : Expr ((Γ ▸ A)) (q ∷ Ψ₂) B}
           → e₁ ≈ˢ e₁′ → e₂ ≈ˢ e₂′ → let' e₁ e₂ ≈ˢ let' e₁′ e₂′
  let-congˢ {q = Zero} _ e₂ σ rσ r = e₂ σ rσ (restrict-rel {Γ = Γ} _ r)
  let-congˢ {q = One} e₁ e₂ σ rσ r =
    RelS-bind (e₁ σ rσ (restrict-rel {Γ = Γ} _ r)) λ rv → e₂ σ rσ (restrict-rel {Γ = Γ} _ r , rv)
  let-congˢ {q = Many} e₁ e₂ σ rσ r =
    RelS-bind (e₁ σ rσ (restrict-rel {Γ = Γ} _ r)) λ rv → e₂ σ rσ (restrict-rel {Γ = Γ} _ r , rv)

  case-congˢ : ∀ {Ψs Ψₗ Ψᵣ qℓ qr A B C} {s s′ : Expr Γ Ψs (A + B)}
                {l l′ : Expr ((Γ ▸ A)) (qℓ ∷ Ψₗ) C} {r r′ : Expr ((Γ ▸ B)) (qr ∷ Ψᵣ) C}
            → s ≈ˢ s′ → l ≈ˢ l′ → r ≈ˢ r′ → case' s l r ≈ˢ case' s′ l′ r′
  case-congˢ {qℓ = qℓ} {qr} es el er σ rσ re =
    RelS-bind (es σ rσ (restrict-rel {Γ = Γ} _ re))
      λ { {inj₁ _} {inj₁ _} ra → el σ rσ (bind-rel {Γ = Γ} qℓ (restrict-rel {Γ = Γ} _ (restrict-rel {Γ = Γ} _ re)) ra)
        ; {inj₂ _} {inj₂ _} rb → er σ rσ (bind-rel {Γ = Γ} qr (restrict-rel {Γ = Γ} _ (restrict-rel {Γ = Γ} _ re)) rb)
        ; {inj₁ _} {inj₂ _} ()
        ; {inj₂ _} {inj₁ _} () }

  lam-congˢ : ∀ {Ψ q' π A B} (q : Quantity) (≤p : (q' ≤qᵇ q) ≡ true) {b b′ : Expr ((Γ ▸ A)) (q' ∷ Ψ) B}
           → b ≈ˢ b′ → lam {π = π} q ≤p b ≈ˢ lam q ≤p b′
  lam-congˢ {q' = Zero} Zero ≤p eb σ rσ r = relS-ret (eb σ rσ r)
  lam-congˢ {q' = Zero} One  ≤p eb σ rσ r = relS-ret (λ _ → eb σ rσ r)
  lam-congˢ {q' = Zero} Many ≤p eb σ rσ r = relS-ret (λ _ → eb σ rσ r)
  lam-congˢ {q' = One}  One  ≤p eb σ rσ r = relS-ret (λ ra → eb σ rσ (r , ra))
  lam-congˢ {q' = One}  Many ≤p eb σ rσ r = relS-ret (λ ra → eb σ rσ (r , ra))
  lam-congˢ {q' = Many} Many ≤p eb σ rσ r = relS-ret (λ ra → eb σ rσ (r , ra))
  lam-congˢ {q' = One}  Zero ()
  lam-congˢ {q' = Many} Zero ()
  lam-congˢ {q' = Many} One  ()

------------------------------------------------------------------------
-- Coercion
------------------------------------------------------------------------

module _ {m n} {Γ : Ctx m n} where

  coerce-reflˢ : ∀ {A : Ty m} {Ψ} (e : Expr Γ Ψ A) → coerce (<:-refl A) e ≈ˢ e
  coerce-reflˢ {A = A} e σ rσ r = RelS-fmapˡ (SD-rel rσ e r) (<:-refl-rel A)

  coerce-transˢ : ∀ {A B C : Ty m} {Ψ} (p : A <: B) (q : B <: C) (e : Expr Γ Ψ A)
               → coerce q (coerce p e) ≈ˢ coerce (<:-trans p q) e
  coerce-transˢ {C = C} p q e σ rσ r =
    RelS-fmapˡ (RelS-fmap {R′ = λ u v → RelD C (⟦ q ⟧<: u) v} (SD-rel rσ e r) (<:-trans-rel p q)) (λ z → z)

  coerce-uniqˢ : ∀ {A B : Ty m} {Ψ} (p q : A <: B) (e : Expr Γ Ψ A) → coerce p e ≈ˢ coerce q e
  coerce-uniqˢ p q e rewrite <:-unique p q = λ σ rσ r → SD-rel rσ (coerce q e) r

  pair-coerceˢ : ∀ {A A′ B B′ : Ty m} {Ψ₁ Ψ₂} (pa : A <: A′) (pb : B <: B′) (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
              → pair (coerce pa a) (coerce pb b) ≈ˢ coerce (sub-prod pa pb) (pair a b)
  pair-coerceˢ pa pb a b σ rσ r =
    RelS-assoc₂ (SD-rel rσ a (restrict-rel {Γ = Γ} _ r)) λ ra →
      retargetˡ refl (RelS-assoc₂ (SD-rel rσ b (restrict-rel {Γ = Γ} _ r)) λ rb →
        retargetˡ refl (retargetʳ refl (relS-ret (<:-rel pa ra , <:-rel pb rb))))

  -- Converting the head's domain is converting the argument.
  app-coerceˢ : ∀ {A′ B : Ty m} {Ψ₁ Ψ₂ X} (a : X <: A′) (g : Once.Spec.Grade.pure ⊑π Once.Spec.Grade.pure)
                 (f : Expr Γ Ψ₁ (A′ ⇒[ mk-kind Many Once.Spec.Grade.pure ] B)) (x : Expr Γ Ψ₂ X)
             → app (coerce (sub-arr a (<:-refl B) g) f) x ≈ˢ app f (coerce a x)
  app-coerceˢ {B = B} a g f x σ rσ r =
    RelS-assocˡ (SD-rel rσ f (restrict-rel {Γ = Γ} _ r)) λ rf →
      retargetˡ refl (RelS-assocʳ (SD-rel rσ x (restrict-rel {Γ = Γ} _ r)) λ rx →
        retargetʳ refl (RelS-fmapˡ (rf (<:-rel a rx)) (<:-refl-rel B)))

  -- Converting the outer arm's codomain is converting the composite's.
  comp-postˢ : ∀ {A B B′ : Ty m} {Ψ₁ Ψ₂ M π} (p : B <: B′) (r r′ : π ⊑π π)
                (f : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M))
            → comp' (coerce (sub-arr (<:-refl M) p r) f) g ≈ˢ coerce (sub-arr (<:-refl A) p r′) (comp' f g)
  comp-postˢ {A = A} {M = M} p r r′ f g σ rσ re =
    RelS-assoc₂ (SD-rel rσ f (restrict-rel {Γ = Γ} _ re)) λ rf →
      retargetˡ refl (RelS-assocʳ (SD-rel rσ g (restrict-rel {Γ = Γ} _ re)) λ rg →
        retargetʳ refl (relS-ret λ ra →
          RelS-assocʳ (rg (<:-refl-relʳ A ra)) λ rm → retargetʳ refl (RelS-fmap (rf (<:-refl-rel M rm)) (<:-rel p))))

  -- Converting the outer arm's domain is converting the inner arm's codomain.
  comp-preˢ : ∀ {A B B′ C C′ : Ty m} {Ψ₁ Ψ₂ π π′} (q : B <: B′) (c : C′ <: C) (g : π′ ⊑π π)
               (f : Expr Γ Ψ₁ (B′ ⇒[ mk-kind Many π′ ] C′)) (h : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B))
           → comp' (coerce (sub-arr q c g) f) h
             ≈ˢ comp' (coerce (sub-arr (<:-refl B′) c g) f) (coerce (sub-arr (<:-refl A) q (⊑π-refl π)) h)
  comp-preˢ {A = A} {B′ = B′} q c g f h σ rσ re =
    RelS-assoc₂ (SD-rel rσ f (restrict-rel {Γ = Γ} _ re)) λ rf →
      retargetˡ refl (retargetʳ refl (RelS-assocʳ (SD-rel rσ h (restrict-rel {Γ = Γ} _ re)) λ rh →
        retargetʳ refl (relS-ret λ ra →
          RelS-assocʳ (rh (<:-refl-relʳ A ra)) λ rb → retargetʳ refl (RelS-fmap (rf (<:-refl-relʳ B′ (<:-rel q rb))) (<:-rel c)))))

  -- Converting a lambda's body is converting the lambda.
  lam-coerceˢ : ∀ {A B B′ : Ty m} {Ψ q' π} (≤p : (q' ≤qᵇ Many) ≡ true) (p : B <: B′) (b : Expr ((Γ ▸ A)) (q' ∷ Ψ) B)
             → lam {π = π} Many ≤p (coerce p b) ≈ˢ coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (lam Many ≤p b)
  lam-coerceˢ {q' = Zero} ≤p p b σ rσ r = retargetʳ refl (relS-ret (λ _ → RelS-fmap (SD-rel rσ b r) (<:-rel p)))
  lam-coerceˢ {A = A} {q' = One} ≤p p b σ rσ r =
    retargetʳ refl (relS-ret (λ ra → RelS-fmap (SD-rel rσ b (r , <:-refl-relʳ A ra)) (<:-rel p)))
  lam-coerceˢ {A = A} {q' = Many} ≤p p b σ rσ r =
    retargetʳ refl (relS-ret (λ ra → RelS-fmap (SD-rel rσ b (r , <:-refl-relʳ A ra)) (<:-rel p)))

  copair-coerceˢ : ∀ {A B C C′ : Ty m} {Ψ₁ Ψ₂ π} (p : C <: C′) (r : π ⊑π π)
                    (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)) (g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C))
                → copair' (coerce (sub-arr (<:-refl A) p r) f) (coerce (sub-arr (<:-refl B) p r) g)
                  ≈ˢ coerce (sub-arr (<:-refl (A + B)) p r) (copair' f g)
  copair-coerceˢ {A = A} {B = B} p r f g σ rσ re =
    RelS-assoc₂ (SD-rel rσ f (restrict-rel {Γ = Γ} _ re)) λ rf →
      retargetˡ refl (RelS-assoc₂ (SD-rel rσ g (restrict-rel {Γ = Γ} _ re)) λ rg →
        retargetˡ refl (retargetʳ refl (relS-ret
          λ { {inj₁ _} {inj₁ _} ra → RelS-fmap (rf (<:-rel (<:-refl A) ra)) (<:-rel p)
            ; {inj₂ _} {inj₂ _} rb → RelS-fmap (rg (<:-rel (<:-refl B) rb)) (<:-rel p)
            ; {inj₁ _} {inj₂ _} ()
            ; {inj₂ _} {inj₁ _} () })))

  fork-coerceˢ : ∀ {A B B′ C C′ : Ty m} {Ψ₁ Ψ₂ π} (pb : B <: B′) (pc : C <: C′) (r : π ⊑π π)
                  (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C))
              → fork' (coerce (sub-arr (<:-refl A) pb r) f) (coerce (sub-arr (<:-refl A) pc r) g)
                ≈ˢ coerce (sub-arr (<:-refl A) (sub-prod pb pc) r) (fork' f g)
  fork-coerceˢ {A = A} pb pc r f g σ rσ re =
    RelS-assoc₂ (SD-rel rσ f (restrict-rel {Γ = Γ} _ re)) λ rf →
      retargetˡ refl (RelS-assoc₂ (SD-rel rσ g (restrict-rel {Γ = Γ} _ re)) λ rg →
        retargetˡ refl (retargetʳ refl (relS-ret λ ra →
          RelS-assoc₂ (rf (<:-rel (<:-refl A) ra)) λ rb →
            retargetˡ refl (RelS-assoc₂ (rg (<:-rel (<:-refl A) ra)) λ rc →
              retargetˡ refl (retargetʳ refl (relS-ret (<:-rel pb rb , <:-rel pc rc)))))))

  -- `initial` at any codomain: a function out of `Void` is unique.
  initial-coerceˢ : ∀ {A π} (r : π ⊑π π)
                 → coerce (sub-arr sub-void sub-void r) (lift-morphism {Γ = Γ} {A = Void} {B = Void} {π = π} IR.initial)
                   ≈ˢ lift-morphism {Γ = Γ} {A = Void} {B = A} {π = π} IR.initial
  initial-coerceˢ r σ rσ re = retargetˡ refl (relS-ret λ { {()} })

------------------------------------------------------------------------
-- `cata` fuses with a conversion of its carrier.
--
-- The algebra `alg : ⟦F⟧A ⇒ A`, converted to `⟦F⟧A′ ⇒ A′` (domain `d`,
-- codomain `p`), folds to the conversion of `alg`'s fold. The relational fold
-- (`cataS-rel`) carries, for each subtree, the converted fold related to the
-- original fold mapped by `⟦ p ⟧<:` — and the original fold related to itself,
-- which the layer step needs (`d` after `p` converts a type to ITSELF, and that
-- conversion relates a self-related value to itself).
------------------------------------------------------------------------

-- The functor-lifted relation on `⟦ F ⟧F`.
RelF : ∀ {m} (F : Fun m) {X₁ X₂ : Set} (R : X₁ → X₂ → Set) → ⟦ F ⟧F X₁ → ⟦ F ⟧F X₂ → Set
RelF (K A)   R x y = x ≡ y
RelF Id      R x y = R x y
RelF (F ⊕ G) R (inj₁ x) (inj₁ y) = RelF F R x y
RelF (F ⊕ G) R (inj₂ x) (inj₂ y) = RelF G R x y
RelF (F ⊕ G) R (inj₁ _) (inj₂ _) = ⊥
RelF (F ⊕ G) R (inj₂ _) (inj₁ _) = ⊥
RelF (F ⊗ G) R (x₁ , y₁) (x₂ , y₂) = RelF F R x₁ x₂ × RelF G R y₁ y₂

out-rel : ∀ {m} {Δ : KCtx m} {F : Fun m} (wf : WFFun Δ F) {X₁ X₂ : Set} (R : X₁ → X₂ → Set) {y₁ y₂}
        → RelSF (translateF Carrier Carrier F) R y₁ y₂
        → RelF F R (coerce-μ-out wf X₁ y₁) (coerce-μ-out wf X₂ y₂)
out-rel (wf-K pA) R refl = refl
out-rel wf-Id R r = r
out-rel (wf-Sum wfF wfG) R {inj₁ _} {inj₁ _} r = out-rel wfF R r
out-rel (wf-Sum wfF wfG) R {inj₂ _} {inj₂ _} r = out-rel wfG R r
out-rel (wf-Sum wfF wfG) R {inj₁ _} {inj₂ _} ()
out-rel (wf-Sum wfF wfG) R {inj₂ _} {inj₁ _} ()
out-rel (wf-Prod wfF wfG) R {_ , _} {_ , _} (r₁ , r₂) = out-rel wfF R r₁ , out-rel wfG R r₂

module _ {m : ℕ} {A A′ : Ty m} (p : A <: A′) where
  -- The carrier relation: converted fold against the original fold mapped,
  -- and the original fold related to itself.
  Rc : T∞ ⟦ A′ ⟧ᴰ → T∞ ⟦ A ⟧ᴰ → Set
  Rc t₁ t₂ = RelS (RelD A′) t₁ (fmap∞ ⟦ p ⟧<: t₂) × RelS (RelD A) t₂ t₂

  -- …and on a sequenced layer.
  Rl : ∀ (F : Fun m) → ⟦ F ⟧F ⟦ A′ ⟧ᴰ → ⟦ F ⟧F ⟦ A ⟧ᴰ → Set
  Rl F = RelF F (λ a b → RelD A′ a (⟦ p ⟧<: b) × RelD A b b)

  seq-rel : ∀ (F : Fun m) {fc₁ : ⟦ F ⟧F (T∞ ⟦ A′ ⟧ᴰ)} {fc₂ : ⟦ F ⟧F (T∞ ⟦ A ⟧ᴰ)}
          → RelF F Rc fc₁ fc₂ → RelS (Rl F) (seqF∞ F fc₁) (seqF∞ F fc₂)
  seq-rel (K B) e = relS-ret e
  seq-rel Id (r , s) = RelS-pairʳ (RelS-unfmapʳ r) s
  seq-rel (F ⊕ G) {inj₁ _} {inj₁ _} r = RelS-fmap {f = inj₁} {g = inj₁} (seq-rel F r) (λ z → z)
  seq-rel (F ⊕ G) {inj₂ _} {inj₂ _} r = RelS-fmap {f = inj₂} {g = inj₂} (seq-rel G r) (λ z → z)
  seq-rel (F ⊕ G) {inj₁ _} {inj₂ _} ()
  seq-rel (F ⊕ G) {inj₂ _} {inj₁ _} ()
  seq-rel (F ⊗ G) {_ , _} {_ , _} (r₁ , r₂) =
    RelS-bind (seq-rel F r₁) λ ru → RelS-bind (seq-rel G r₂) λ rv → relS-ret (ru , rv)

  -- The original layer's own relation, read off the paired one.
  seq-self : ∀ (F : Fun m) {fc₁ : ⟦ F ⟧F (T∞ ⟦ A′ ⟧ᴰ)} {fc₂ : ⟦ F ⟧F (T∞ ⟦ A ⟧ᴰ)} → RelF F Rc fc₁ fc₂ → FRel (RelS (RelD A)) F fc₂ fc₂
  seq-self (K B) e = fr-K
  seq-self Id (r , s) = fr-Id s
  seq-self (F ⊕ G) {inj₁ _} {inj₁ _} r = fr-inl (seq-self F r)
  seq-self (F ⊕ G) {inj₂ _} {inj₂ _} r = fr-inr (seq-self G r)
  seq-self (F ⊕ G) {inj₁ _} {inj₂ _} ()
  seq-self (F ⊕ G) {inj₂ _} {inj₁ _} ()
  seq-self (F ⊗ G) {_ , _} {_ , _} (r₁ , r₂) = fr-pair (seq-self F r₁) (seq-self G r₂)

-- A layer converted up by `p` and back down by `d` relates to the layer.
layer-rel : ∀ {m} {Δ : KCtx m} {F : Fun m} (wf : WFFun Δ F) {A A′ : Ty m} (d : SpT.⟦ F ⟧F A′ <: SpT.⟦ F ⟧F A) (p : A <: A′)
              {l₁ : ⟦ F ⟧F ⟦ A′ ⟧ᴰ} {l₂ : ⟦ F ⟧F ⟦ A ⟧ᴰ}
          → Rl p F l₁ l₂ → RelD (SpT.⟦ F ⟧F A) (⟦ d ⟧<: (coerce-functor⁻¹-D wf A′ l₁)) (coerce-functor⁻¹-D wf A l₂)
layer-rel {F = K B} (wf-K b) d p {l₁} refl rewrite <:-unique d (<:-refl B) = <:-refl-rel B (base-refl b _)
layer-rel wf-Id {A} d p {l₁} {l₂} (ra , rb) = RelD-trans A (<:-rel d ra) back
  where
    back : RelD A (⟦ d ⟧<: (⟦ p ⟧<: l₂)) l₂
    back with <:-trans-rel p d rb
    ... | t rewrite <:-unique (<:-trans p d) (<:-refl A) = RelD-trans A t (<:-refl-rel A rb)
layer-rel (wf-Sum w₁ w₂) (Once.Internal.Type.Sub.sub-sum d₁ d₂) p {inj₁ _} {inj₁ _} r = layer-rel w₁ d₁ p r
layer-rel (wf-Sum w₁ w₂) (Once.Internal.Type.Sub.sub-sum d₁ d₂) p {inj₂ _} {inj₂ _} r = layer-rel w₂ d₂ p r
layer-rel (wf-Sum w₁ w₂) (Once.Internal.Type.Sub.sub-sum d₁ d₂) p {inj₁ _} {inj₂ _} ()
layer-rel (wf-Sum w₁ w₂) (Once.Internal.Type.Sub.sub-sum d₁ d₂) p {inj₂ _} {inj₁ _} ()
layer-rel (wf-Prod w₁ w₂) (sub-prod d₁ d₂) p {_ , _} {_ , _} (r₁ , r₂) = layer-rel w₁ d₁ p r₁ , layer-rel w₂ d₂ p r₂

cata-core : ∀ {m} {Δ : KCtx m} {F : Fun m} (wf : WFFun Δ F) {A A′ : Ty m} {π π′ : Purity}
              (d : SpT.⟦ F ⟧F A′ <: SpT.⟦ F ⟧F A) (p : A <: A′) (g : π ⊑π π′)
              {valg valg′ : ⟦ SpT.⟦ F ⟧F A ⇒[ mk-kind Many π ] A ⟧ᴰ}
          → RelD (SpT.⟦ F ⟧F A ⇒[ mk-kind Many π ] A) valg valg′
          → ∀ (x : ⟦μ⟧ F)
          → Rc p (sem-cata wf (cata-ev-algˢ {C = A′} {F = F} wf (return∞ (⟦ sub-arr {q = Many} d p g ⟧<: valg))) x)
                 (sem-cata wf (cata-ev-algˢ {C = A} {F = F} wf (return∞ valg′)) x)
cata-core {F = F} wf {A} {A′} {π} d p g {valg} {valg′} ralg x =
  cataS-rel {translateF Carrier Carrier F} (Rc p) algR x
  where
    self′ = RelD-rightself (SpT.⟦ F ⟧F A ⇒[ mk-kind Many π ] A) ralg
    algR : ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) (Rc p) y₁ y₂
         → Rc p (cata-ev-algˢ {C = A′} {F = F} wf (return∞ (⟦ sub-arr {q = Many} d p g ⟧<: valg)) (coerce-μ-out wf _ y₁))
                (cata-ev-algˢ {C = A} {F = F} wf (return∞ valg′) (coerce-μ-out wf _ y₂))
    algR {y₁} {y₂} r =
      RelS-assocʳ (seq-rel p F (out-rel wf _ r))
        (λ rl → retargetˡ refl (retargetʳ refl (RelS-fmap (ralg (layer-rel wf d p rl)) (<:-rel p))))
      , RelS-bind (seqF∞-rel F (seq-self p F (out-rel wf _ r)))
          (λ fl → retargetˡ refl (retargetʳ refl (self′ (cfD⁻¹-rel wf A fl))))

module _ {m n} {Γ : Ctx m n} where

  cata-coerceˢ : ∀ {Δₖ : KCtx m} {A A′ : Ty m} {F : Fun m} {Ψ π} (wf : WFFun Δₖ F) (d : SpT.⟦ F ⟧F A′ <: SpT.⟦ F ⟧F A) (p : A <: A′) (g : π ⊑π π)
                  (alg : Expr Γ Ψ (SpT.⟦ F ⟧F A ⇒[ mk-kind Many π ] A))
              → cata {Γ = Γ} wf (coerce (sub-arr {q = Many} d p g) alg)
                ≈ˢ coerce (sub-arr (<:-refl (μ F)) p (⊑π-refl π)) (cata {Γ = Γ} wf alg)
  cata-coerceˢ wf d p g alg σ rσ re =
    RelS-assoc₂ (SD-rel rσ alg (restrict-rel {Γ = Γ} _ re)) λ ralg →
      retargetˡ refl (retargetʳ refl (relS-ret λ { {x} refl → proj₁ (cata-core wf d p g ralg x) }))

-- The same laws at `_≈_` live in `CoherenceLawsWrap` (split for the 30 s
-- per-module check budget).
