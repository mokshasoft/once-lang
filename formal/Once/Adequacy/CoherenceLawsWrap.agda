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

open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun)
open import Once.Spec.Type using (WFFun; ∅ₖ)
open import Once.Spec.Numerics using (TargetNum)

open import Once.Type.Grade using (_≤qᵇ_)
import Once.Spec.Grade
module Once.Adequacy.CoherenceLawsWrap (fmt : TargetNum) where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Grade using (mk-kind; Many; Quantity)
open import Once.Spec.Type using (Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.Spec.Type using (μ; ⟦_⟧F)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-void)
open import Once.Spec.Grade using (_⊑π_)
open import Once.Internal.Laws.SubLaws using (<:-trans)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl)
open import Once.Spec.Sub using (sub-*)
open import Once.Internal.Context using (Ctx)
open import Once.Spec.Context using (_∷_; _▸_)
open import Once.Surface.Syntax using (Expr; lam; app; effApp; pair; let'; case'; neg; i2f; add; sub; mul; div; mod'; fadd; fsub; fmul; fdiv; lt; le; gt; ge; eq; ne; coerce; morph-app; comp'; copair'; fork'; curry'; cata; ana; loop; lift-morphism)
import Once.Type
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.IR as IR
import Once.Denotation.SourceDenote as SD


-- The raw laws (at `_≈ˢ_`) and `_≈_` itself.
open import Once.Adequacy.CoherenceLaws fmt

------------------------------------------------------------------------
-- The laws at `_≈_` (implicits passed through explicitly).
------------------------------------------------------------------------

module _ {m n} {Γ : Ctx m n} where
  pair-cong : ∀ {Ψ₁ Ψ₂ A B} {a a′ : Expr Γ Ψ₁ A} {b b′ : Expr Γ Ψ₂ B} → a ≈ a′ → b ≈ b′ → pair a b ≈ pair a′ b′
  pair-cong {Ψ₁} {Ψ₂} {A} {B} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (pair-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  add-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → add a b ≈ add a′ b′
  add-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (add-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  sub-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → sub a b ≈ sub a′ b′
  sub-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (sub-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  mul-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → mul a b ≈ mul a′ b′
  mul-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (mul-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  div-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → div a b ≈ div a′ b′
  div-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (div-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  mod-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → mod' a b ≈ mod' a′ b′
  mod-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (mod-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  fadd-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fadd a b ≈ fadd a′ b′
  fadd-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fadd-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  fsub-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fsub a b ≈ fsub a′ b′
  fsub-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fsub-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  fmul-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fmul a b ≈ fmul a′ b′
  fmul-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fmul-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  fdiv-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fdiv a b ≈ fdiv a′ b′
  fdiv-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fdiv-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  lt-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → lt a b ≈ lt a′ b′
  lt-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (lt-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  le-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → le a b ≈ le a′ b′
  le-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (le-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  gt-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → gt a b ≈ gt a′ b′
  gt-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (gt-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  ge-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → ge a b ≈ ge a′ b′
  ge-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (ge-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  eq-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → eq a b ≈ eq a′ b′
  eq-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (eq-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  ne-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → ne a b ≈ ne a′ b′
  ne-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (ne-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {a = a} {a′ = a′} {b = b} {b′ = b′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  neg-cong : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ a′ → neg a ≈ neg a′
  neg-cong {Ψ} {a} {a′} (≈-intro h1) = ≈-intro (neg-congˢ {Γ = Γ} {Ψ = Ψ} {a = a} {a′ = a′} h1)

module _ {m n} {Γ : Ctx m n} where
  i2f-cong : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ a′ → i2f a ≈ i2f a′
  i2f-cong {Ψ} {a} {a′} (≈-intro h1) = ≈-intro (i2f-congˢ {Γ = Γ} {Ψ = Ψ} {a = a} {a′ = a′} h1)

module _ {m n} {Γ : Ctx m n} where
  coerce-cong : ∀ {A B : Ty m} {Ψ} (p : A <: B) {a a′ : Expr Γ Ψ A} → a ≈ a′ → coerce p a ≈ coerce p a′
  coerce-cong {A = A} {B = B} {Ψ = Ψ} p {a} {a′} (≈-intro h1) = ≈-intro (coerce-congˢ {Γ = Γ} {A = A} {B = B} {Ψ = Ψ} p {a} {a′} h1)

module _ {m n} {Γ : Ctx m n} where
  morph-app-cong : ∀ {Ψ A B} (ir : IR ⌊ A ⌋ ⌊ B ⌋) {a a′ : Expr Γ Ψ A} → a ≈ a′ → morph-app {A = A} {B = B} ir a ≈ morph-app {A = A} {B = B} ir a′
  morph-app-cong {Ψ} {A} {B} ir {a} {a′} (≈-intro h1) = ≈-intro (morph-app-congˢ {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} ir {a} {a′} h1)

module _ {m n} {Γ : Ctx m n} where
  app-cong : ∀ {Ψ₁ Ψ₂ A B q} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind q Once.Spec.Grade.pure ] B)} {x x′ : Expr Γ Ψ₂ A} → f ≈ f′ → x ≈ x′ → app f x ≈ app f′ x′
  app-cong {Ψ₁} {Ψ₂} {A} {B} {q} {f} {f′} {x} {x′} (≈-intro h1) (≈-intro h2) = ≈-intro (app-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = q} {f = f} {f′ = f′} {x = x} {x′ = x′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  effApp-cong : ∀ {Ψ₁ Ψ₂ A B π} {g : Once.Spec.Grade.EffGrade π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {x x′ : Expr Γ Ψ₂ A} → f ≈ f′ → x ≈ x′ → effApp {g = g} f x ≈ effApp {g = g} f′ x′
  effApp-cong {Ψ₁} {Ψ₂} {A} {B} {π} {g} {f} {f′} {x} {x′} (≈-intro h1) (≈-intro h2) = ≈-intro (effApp-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {π = π} {g = g} {f = f} {f′ = f′} {x = x} {x′ = x′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  comp-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)} → f ≈ f′ → g ≈ g′ → comp' f g ≈ comp' f′ g′
  comp-cong {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} (≈-intro h1) (≈-intro h2) = ≈-intro (comp-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} {f = f} {f′ = f′} {g = g} {g′ = g′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  copair-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)} → f ≈ f′ → g ≈ g′ → copair' f g ≈ copair' f′ g′
  copair-cong {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} (≈-intro h1) (≈-intro h2) = ≈-intro (copair-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} {f = f} {f′ = f′} {g = g} {g′ = g′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  fork-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)} → f ≈ f′ → g ≈ g′ → fork' f g ≈ fork' f′ g′
  fork-cong {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} (≈-intro h1) (≈-intro h2) = ≈-intro (fork-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} {f = f} {f′ = f′} {g = g} {g′ = g′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  curry-cong : ∀ {Ψ A B C π₀ π} {f f′ : Expr Γ Ψ ((A * B) ⇒[ mk-kind Many π ] C)} → f ≈ f′ → curry' {π₀ = π₀} f ≈ curry' f′
  curry-cong {Ψ} {A} {B} {C} {π₀} {π} {f} {f′} (≈-intro h1) = ≈-intro (curry-congˢ {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} {f = f} {f′ = f′} h1)

module _ {m n} {Γ : Ctx m n} where
  cata-cong : ∀ {Δₖ : KCtx m} {A : Ty m} {F : Fun m} {Ψ π} (wf : WFFun Δₖ F) {g g′ : Expr Γ Ψ (⟦ F ⟧F A ⇒[ mk-kind Many π ] A)} → g ≈ g′ → cata {Γ = Γ} wf g ≈ cata wf g′
  cata-cong {A = A} {F = F} {Ψ = Ψ} {π = π} wf {g} {g′} (≈-intro h1) = ≈-intro (cata-congˢ {Γ = Γ} {A = A} {F = F} {Ψ = Ψ} {π = π} wf {g} {g′} h1)

module _ {m n} {Γ : Ctx m n} where
  ana-cong : ∀ {Δₖ : KCtx m} {A : Ty m} {F : Fun m} {Ψ π₀ φ} (wf : WFFun Δₖ F) {g g′ : Expr Γ Ψ (A ⇒[ mk-kind Many (Once.Spec.Grade.fin φ) ] ⟦ F ⟧F A)} → g ≈ g′ → ana {Γ = Γ} {π₀ = π₀} {φ = φ} wf g ≈ ana wf g′
  ana-cong {A = A} {F = F} {Ψ = Ψ} {π₀ = π₀} {φ = φ} wf {g} {g′} (≈-intro h1) = ≈-intro (ana-congˢ {Γ = Γ} {A = A} {F = F} {Ψ = Ψ} {π₀ = π₀} {φ = φ} wf {g} {g′} h1)
  loop-cong : ∀ {Ψ A B} {g g′ : Expr Γ Ψ (A ⇒[ mk-kind Many Once.Spec.Grade.act ] (B Once.Spec.Type.+ A))} → g ≈ g′ → loop {Γ = Γ} g ≈ loop g′
  loop-cong {Ψ} {A} {B} {g} {g′} (≈-intro h1) = ≈-intro (loop-congˢ {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} {g = g} {g′ = g′} h1)

module _ {m n} {Γ : Ctx m n} where
  let-cong : ∀ {Ψ₁ Ψ₂ A B q} {e₁ e₁′ : Expr Γ Ψ₁ A} {e₂ e₂′ : Expr ((Γ ▸ A)) (q ∷ Ψ₂) B} → e₁ ≈ e₁′ → e₂ ≈ e₂′ → let' e₁ e₂ ≈ let' e₁′ e₂′
  let-cong {Ψ₁} {Ψ₂} {A} {B} {q} {e₁} {e₁′} {e₂} {e₂′} (≈-intro h1) (≈-intro h2) = ≈-intro (let-congˢ {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = q} {e₁ = e₁} {e₁′ = e₁′} {e₂ = e₂} {e₂′ = e₂′} h1 h2)

module _ {m n} {Γ : Ctx m n} where
  case-cong : ∀ {Ψs Ψₗ Ψᵣ qℓ qr A B C} {s s′ : Expr Γ Ψs (A + B)} {l l′ : Expr ((Γ ▸ A)) (qℓ ∷ Ψₗ) C} {r r′ : Expr ((Γ ▸ B)) (qr ∷ Ψᵣ) C} → s ≈ s′ → l ≈ l′ → r ≈ r′ → case' s l r ≈ case' s′ l′ r′
  case-cong {Ψs} {Ψₗ} {Ψᵣ} {qℓ} {qr} {A} {B} {C} {s} {s′} {l} {l′} {r} {r′} (≈-intro h1) (≈-intro h2) (≈-intro h3) = ≈-intro (case-congˢ {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} {C = C} {s = s} {s′ = s′} {l = l} {l′ = l′} {r = r} {r′ = r′} h1 h2 h3)

module _ {m n} {Γ : Ctx m n} where
  lam-cong : ∀ {Ψ q' π A B} (q : Quantity) (≤p : (q' ≤qᵇ q) ≡ true) {b b′ : Expr ((Γ ▸ A)) (q' ∷ Ψ) B} → b ≈ b′ → lam {π = π} q ≤p b ≈ lam q ≤p b′
  lam-cong {Ψ} {q'} {π} {A} {B} q ≤p {b} {b′} (≈-intro h1) = ≈-intro (lam-congˢ {Γ = Γ} {Ψ = Ψ} {q' = q'} {π = π} {A = A} {B = B} q ≤p {b} {b′} h1)

module _ {m n} {Γ : Ctx m n} where
  coerce-refl : ∀ {A : Ty m} {Ψ} (e : Expr Γ Ψ A) → coerce (<:-refl A) e ≈ e
  coerce-refl {A = A} {Ψ = Ψ} e = ≈-intro (coerce-reflˢ {Γ = Γ} {A = A} {Ψ = Ψ} e)

module _ {m n} {Γ : Ctx m n} where
  coerce-trans : ∀ {A B C : Ty m} {Ψ} (p : A <: B) (q : B <: C) (e : Expr Γ Ψ A) → coerce q (coerce p e) ≈ coerce (<:-trans p q) e
  coerce-trans {A = A} {B = B} {C = C} {Ψ = Ψ} p q e = ≈-intro (coerce-transˢ {Γ = Γ} {A = A} {B = B} {C = C} {Ψ = Ψ} p q e)

module _ {m n} {Γ : Ctx m n} where
  coerce-uniq : ∀ {A B : Ty m} {Ψ} (p q : A <: B) (e : Expr Γ Ψ A) → coerce p e ≈ coerce q e
  coerce-uniq {A = A} {B = B} {Ψ = Ψ} p q e = ≈-intro (coerce-uniqˢ {Γ = Γ} {A = A} {B = B} {Ψ = Ψ} p q e)

module _ {m n} {Γ : Ctx m n} where
  pair-coerce : ∀ {A A′ B B′ : Ty m} {Ψ₁ Ψ₂} (pa : A <: A′) (pb : B <: B′) (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B) → pair (coerce pa a) (coerce pb b) ≈ coerce (sub-* pa pb) (pair a b)
  pair-coerce {A = A} {A′ = A′} {B = B} {B′ = B′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} pa pb a b = ≈-intro (pair-coerceˢ {Γ = Γ} {A = A} {A′ = A′} {B = B} {B′ = B′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} pa pb a b)

module _ {m n} {Γ : Ctx m n} where
  app-coerce : ∀ {A′ B : Ty m} {Ψ₁ Ψ₂ X} (a : X <: A′) (g : Once.Spec.Grade.pure ⊑π Once.Spec.Grade.pure) (f : Expr Γ Ψ₁ (A′ ⇒[ mk-kind Many Once.Spec.Grade.pure ] B)) (x : Expr Γ Ψ₂ X) → app (coerce (sub-arr a (<:-refl B) g) f) x ≈ app f (coerce a x)
  app-coerce {A′ = A′} {B = B} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {X = X} a g f x = ≈-intro (app-coerceˢ {Γ = Γ} {A′ = A′} {B = B} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {X = X} a g f x)

module _ {m n} {Γ : Ctx m n} where
  comp-post : ∀ {A B B′ : Ty m} {Ψ₁ Ψ₂ M π} (p : B <: B′) (r r′ : π ⊑π π) (f : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M)) → comp' (coerce (sub-arr (<:-refl M) p r) f) g ≈ coerce (sub-arr (<:-refl A) p r′) (comp' f g)
  comp-post {A = A} {B = B} {B′ = B′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {M = M} {π = π} p r r′ f g = ≈-intro (comp-postˢ {Γ = Γ} {A = A} {B = B} {B′ = B′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {M = M} {π = π} p r r′ f g)

module _ {m n} {Γ : Ctx m n} where
  comp-pre : ∀ {A B B′ C C′ : Ty m} {Ψ₁ Ψ₂ π π′} (q : B <: B′) (c : C′ <: C) (g : π′ ⊑π π) (f : Expr Γ Ψ₁ (B′ ⇒[ mk-kind Many π′ ] C′)) (h : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)) → comp' (coerce (sub-arr q c g) f) h ≈ comp' (coerce (sub-arr (<:-refl B′) c g) f) (coerce (sub-arr (<:-refl A) q (⊑π-refl π)) h)
  comp-pre {A = A} {B = B} {B′ = B′} {C = C} {C′ = C′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} {π′ = π′} q c g f h = ≈-intro (comp-preˢ {Γ = Γ} {A = A} {B = B} {B′ = B′} {C = C} {C′ = C′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} {π′ = π′} q c g f h)

module _ {m n} {Γ : Ctx m n} where
  lam-coerce : ∀ {A B B′ : Ty m} {Ψ q' π} (≤p : (q' ≤qᵇ Many) ≡ true) (p : B <: B′) (b : Expr ((Γ ▸ A)) (q' ∷ Ψ) B) → lam {π = π} Many ≤p (coerce p b) ≈ coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (lam Many ≤p b)
  lam-coerce {A = A} {B = B} {B′ = B′} {Ψ = Ψ} {q' = q'} {π = π} ≤p p b = ≈-intro (lam-coerceˢ {Γ = Γ} {A = A} {B = B} {B′ = B′} {Ψ = Ψ} {q' = q'} {π = π} ≤p p b)

module _ {m n} {Γ : Ctx m n} where
  copair-coerce : ∀ {A B C C′ : Ty m} {Ψ₁ Ψ₂ π} (p : C <: C′) (r : π ⊑π π) (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)) (g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)) → copair' (coerce (sub-arr (<:-refl A) p r) f) (coerce (sub-arr (<:-refl B) p r) g) ≈ coerce (sub-arr (<:-refl (A + B)) p r) (copair' f g)
  copair-coerce {A = A} {B = B} {C = C} {C′ = C′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} p r f g = ≈-intro (copair-coerceˢ {Γ = Γ} {A = A} {B = B} {C = C} {C′ = C′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} p r f g)

module _ {m n} {Γ : Ctx m n} where
  fork-coerce : ∀ {A B B′ C C′ : Ty m} {Ψ₁ Ψ₂ π} (pb : B <: B′) (pc : C <: C′) (r : π ⊑π π) (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)) → fork' (coerce (sub-arr (<:-refl A) pb r) f) (coerce (sub-arr (<:-refl A) pc r) g) ≈ coerce (sub-arr (<:-refl A) (sub-* pb pc) r) (fork' f g)
  fork-coerce {A = A} {B = B} {B′ = B′} {C = C} {C′ = C′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} pb pc r f g = ≈-intro (fork-coerceˢ {Γ = Γ} {A = A} {B = B} {B′ = B′} {C = C} {C′ = C′} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} pb pc r f g)

module _ {m n} {Γ : Ctx m n} where
  initial-coerce : ∀ {A π} (r : π ⊑π π) → coerce (sub-arr sub-void sub-void r) (lift-morphism {Γ = Γ} {A = Void} {B = Void} {π = π} IR.initial) ≈ lift-morphism {Γ = Γ} {A = Void} {B = A} {π = π} IR.initial
  initial-coerce {A} {π} r = ≈-intro (initial-coerceˢ {Γ = Γ} {A = A} {π = π} r)

module _ {m n} {Γ : Ctx m n} where
  cata-coerce : ∀ {Δₖ : KCtx m} {A A′ : Ty m} {F : Fun m} {Ψ π} (wf : WFFun Δₖ F) (d : ⟦ F ⟧F A′ <: ⟦ F ⟧F A) (p : A <: A′) (g : π ⊑π π) (alg : Expr Γ Ψ (⟦ F ⟧F A ⇒[ mk-kind Many π ] A)) → cata {Γ = Γ} wf (coerce (sub-arr {q = Many} d p g) alg) ≈ coerce (sub-arr (<:-refl (μ F)) p (⊑π-refl π)) (cata {Γ = Γ} wf alg)
  cata-coerce {A = A} {A′ = A′} {F = F} {Ψ = Ψ} {π = π} wf d p g alg = ≈-intro (cata-coerceˢ {Γ = Γ} {A = A} {A′ = A′} {F = F} {Ψ = Ψ} {π = π} wf d p g alg)
