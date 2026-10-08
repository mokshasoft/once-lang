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

module Once.Adequacy.CoherenceLawsWrap (fmt : TargetNum) where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Void; Int; Float; _*_; _+_; _⇒[_]_; mk-kind; Many; Quantity; _≤q_; μ-type; ⟦_⟧T)
open import Once.Type.Sub using (_<:_; sub-arr; sub-prod; sub-void; <:-refl; <:-trans; _⊑π_; ⊑π-refl)
open import Once.Surface.Syntax using (Expr; Ctx; _∷_; _,_^_; lam; app; effApp; pair; let'; case'; neg; i2f; add; sub; mul; div; mod'; fadd; fsub; fmul; fdiv; lt; le; gt; ge; eq; ne; coerce; morph-app; comp'; copair'; fork'; curry'; cata; ana; lift-morphism)
import Once.Type
open import Once.Functor.Translate using (WellFormedF)
open import Once.IR using (IR; ⌊_⌋)
import Once.IR as IR
import Once.Denotation.SourceDenote as SD


-- The raw laws (at `_≈ˢ_`) and `_≈_` itself.
open import Once.Adequacy.CoherenceLaws fmt

------------------------------------------------------------------------
-- The laws at `_≈_` (implicits passed through explicitly).
------------------------------------------------------------------------

module _ {n} {Γ : Ctx n} where
  pair-cong : ∀ {Ψ₁ Ψ₂ A B} {a a′ : Expr Γ Ψ₁ A} {b b′ : Expr Γ Ψ₂ B} → a ≈ a′ → b ≈ b′ → pair a b ≈ pair a′ b′
  pair-cong {Ψ₁} {Ψ₂} {A} {B} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (pair-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  add-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → add a b ≈ add a′ b′
  add-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (add-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  sub-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → sub a b ≈ sub a′ b′
  sub-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (sub-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  mul-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → mul a b ≈ mul a′ b′
  mul-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (mul-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  div-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → div a b ≈ div a′ b′
  div-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (div-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  mod-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → mod' a b ≈ mod' a′ b′
  mod-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (mod-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  fadd-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fadd a b ≈ fadd a′ b′
  fadd-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fadd-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  fsub-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fsub a b ≈ fsub a′ b′
  fsub-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fsub-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  fmul-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fmul a b ≈ fmul a′ b′
  fmul-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fmul-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  fdiv-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Float} {b b′ : Expr Γ Ψ₂ Float} → a ≈ a′ → b ≈ b′ → fdiv a b ≈ fdiv a′ b′
  fdiv-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (fdiv-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  lt-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → lt a b ≈ lt a′ b′
  lt-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (lt-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  le-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → le a b ≈ le a′ b′
  le-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (le-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  gt-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → gt a b ≈ gt a′ b′
  gt-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (gt-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  ge-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → ge a b ≈ ge a′ b′
  ge-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (ge-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  eq-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → eq a b ≈ eq a′ b′
  eq-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (eq-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  ne-cong : ∀ {Ψ₁ Ψ₂} {a a′ : Expr Γ Ψ₁ Int} {b b′ : Expr Γ Ψ₂ Int} → a ≈ a′ → b ≈ b′ → ne a b ≈ ne a′ b′
  ne-cong {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} (≈-intro h1) (≈-intro h2) = ≈-intro (ne-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {a} {a′} {b} {b′} h1 h2)

module _ {n} {Γ : Ctx n} where
  neg-cong : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ a′ → neg a ≈ neg a′
  neg-cong {Ψ} {a} {a′} (≈-intro h1) = ≈-intro (neg-congˢ {Γ = Γ} {Ψ} {a} {a′} h1)

module _ {n} {Γ : Ctx n} where
  i2f-cong : ∀ {Ψ} {a a′ : Expr Γ Ψ Int} → a ≈ a′ → i2f a ≈ i2f a′
  i2f-cong {Ψ} {a} {a′} (≈-intro h1) = ≈-intro (i2f-congˢ {Γ = Γ} {Ψ} {a} {a′} h1)

module _ {n} {Γ : Ctx n} where
  coerce-cong : ∀ {Ψ A B} (p : A <: B) {a a′ : Expr Γ Ψ A} → a ≈ a′ → coerce p a ≈ coerce p a′
  coerce-cong {Ψ} {A} {B} p {a} {a′} (≈-intro h1) = ≈-intro (coerce-congˢ {Γ = Γ} {Ψ} {A} {B} p {a} {a′} h1)

module _ {n} {Γ : Ctx n} where
  morph-app-cong : ∀ {Ψ A B} (ir : IR ⌊ A ⌋ ⌊ B ⌋) {a a′ : Expr Γ Ψ A} → a ≈ a′ → morph-app {A = A} {B = B} ir a ≈ morph-app {A = A} {B = B} ir a′
  morph-app-cong {Ψ} {A} {B} ir {a} {a′} (≈-intro h1) = ≈-intro (morph-app-congˢ {Γ = Γ} {Ψ} {A} {B} ir {a} {a′} h1)

module _ {n} {Γ : Ctx n} where
  app-cong : ∀ {Ψ₁ Ψ₂ A B q} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind q Once.Type.pure ] B)} {x x′ : Expr Γ Ψ₂ A} → f ≈ f′ → x ≈ x′ → app f x ≈ app f′ x′
  app-cong {Ψ₁} {Ψ₂} {A} {B} {q} {f} {f′} {x} {x′} (≈-intro h1) (≈-intro h2) = ≈-intro (app-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {q} {f} {f′} {x} {x′} h1 h2)

module _ {n} {Γ : Ctx n} where
  effApp-cong : ∀ {Ψ₁ Ψ₂ A B} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many Once.Type.eff ] B)} {x x′ : Expr Γ Ψ₂ A} → f ≈ f′ → x ≈ x′ → effApp f x ≈ effApp f′ x′
  effApp-cong {Ψ₁} {Ψ₂} {A} {B} {f} {f′} {x} {x′} (≈-intro h1) (≈-intro h2) = ≈-intro (effApp-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {f} {f′} {x} {x′} h1 h2)

module _ {n} {Γ : Ctx n} where
  comp-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)} → f ≈ f′ → g ≈ g′ → comp' f g ≈ comp' f′ g′
  comp-cong {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} (≈-intro h1) (≈-intro h2) = ≈-intro (comp-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} h1 h2)

module _ {n} {Γ : Ctx n} where
  copair-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)} {g g′ : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)} → f ≈ f′ → g ≈ g′ → copair' f g ≈ copair' f′ g′
  copair-cong {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} (≈-intro h1) (≈-intro h2) = ≈-intro (copair-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} h1 h2)

module _ {n} {Γ : Ctx n} where
  fork-cong : ∀ {Ψ₁ Ψ₂ A B C π} {f f′ : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)} {g g′ : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)} → f ≈ f′ → g ≈ g′ → fork' f g ≈ fork' f′ g′
  fork-cong {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} (≈-intro h1) (≈-intro h2) = ≈-intro (fork-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} {π} {f} {f′} {g} {g′} h1 h2)

module _ {n} {Γ : Ctx n} where
  curry-cong : ∀ {Ψ A B C π₀ π} {f f′ : Expr Γ Ψ ((A * B) ⇒[ mk-kind Many π ] C)} → f ≈ f′ → curry' {π₀ = π₀} f ≈ curry' f′
  curry-cong {Ψ} {A} {B} {C} {π₀} {π} {f} {f′} (≈-intro h1) = ≈-intro (curry-congˢ {Γ = Γ} {Ψ} {A} {B} {C} {π₀} {π} {f} {f′} h1)

module _ {n} {Γ : Ctx n} where
  cata-cong : ∀ {Ψ F A π} (wf : WellFormedF F) {g g′ : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)} → g ≈ g′ → cata {Γ = Γ} wf g ≈ cata wf g′
  cata-cong {Ψ} {F} {A} {π} wf {g} {g′} (≈-intro h1) = ≈-intro (cata-congˢ {Γ = Γ} {Ψ} {F} {A} {π} wf {g} {g′} h1)

module _ {n} {Γ : Ctx n} where
  ana-cong : ∀ {Ψ F A π₀ π} (wf : WellFormedF F) {g g′ : Expr Γ Ψ (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A)} → g ≈ g′ → ana {Γ = Γ} {π₀ = π₀} wf g ≈ ana wf g′
  ana-cong {Ψ} {F} {A} {π₀} {π} wf {g} {g′} (≈-intro h1) = ≈-intro (ana-congˢ {Γ = Γ} {Ψ} {F} {A} {π₀} {π} wf {g} {g′} h1)

module _ {n} {Γ : Ctx n} where
  let-cong : ∀ {Ψ₁ Ψ₂ A B q} {e₁ e₁′ : Expr Γ Ψ₁ A} {e₂ e₂′ : Expr (_,_^_ Γ A Many) (q ∷ Ψ₂) B} → e₁ ≈ e₁′ → e₂ ≈ e₂′ → let' e₁ e₂ ≈ let' e₁′ e₂′
  let-cong {Ψ₁} {Ψ₂} {A} {B} {q} {e₁} {e₁′} {e₂} {e₂′} (≈-intro h1) (≈-intro h2) = ≈-intro (let-congˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {q} {e₁} {e₁′} {e₂} {e₂′} h1 h2)

module _ {n} {Γ : Ctx n} where
  case-cong : ∀ {Ψs Ψₗ Ψᵣ qℓ qr A B C} {s s′ : Expr Γ Ψs (A + B)} {l l′ : Expr (_,_^_ Γ A Many) (qℓ ∷ Ψₗ) C} {r r′ : Expr (_,_^_ Γ B Many) (qr ∷ Ψᵣ) C} → s ≈ s′ → l ≈ l′ → r ≈ r′ → case' s l r ≈ case' s′ l′ r′
  case-cong {Ψs} {Ψₗ} {Ψᵣ} {qℓ} {qr} {A} {B} {C} {s} {s′} {l} {l′} {r} {r′} (≈-intro h1) (≈-intro h2) (≈-intro h3) = ≈-intro (case-congˢ {Γ = Γ} {Ψs} {Ψₗ} {Ψᵣ} {qℓ} {qr} {A} {B} {C} {s} {s′} {l} {l′} {r} {r′} h1 h2 h3)

module _ {n} {Γ : Ctx n} where
  lam-cong : ∀ {Ψ q' π A B} (q : Quantity) (≤p : (q' ≤q q) ≡ true) {b b′ : Expr (_,_^_ Γ A Many) (q' ∷ Ψ) B} → b ≈ b′ → lam {π = π} q ≤p b ≈ lam q ≤p b′
  lam-cong {Ψ} {q'} {π} {A} {B} q ≤p {b} {b′} (≈-intro h1) = ≈-intro (lam-congˢ {Γ = Γ} {Ψ} {q'} {π} {A} {B} q ≤p {b} {b′} h1)

module _ {n} {Γ : Ctx n} where
  coerce-refl : ∀ {Ψ A} (e : Expr Γ Ψ A) → coerce (<:-refl A) e ≈ e
  coerce-refl {Ψ} {A} e = ≈-intro (coerce-reflˢ {Γ = Γ} {Ψ} {A} e)

module _ {n} {Γ : Ctx n} where
  coerce-trans : ∀ {Ψ A B C} (p : A <: B) (q : B <: C) (e : Expr Γ Ψ A) → coerce q (coerce p e) ≈ coerce (<:-trans p q) e
  coerce-trans {Ψ} {A} {B} {C} p q e = ≈-intro (coerce-transˢ {Γ = Γ} {Ψ} {A} {B} {C} p q e)

module _ {n} {Γ : Ctx n} where
  coerce-uniq : ∀ {Ψ A B} (p q : A <: B) (e : Expr Γ Ψ A) → coerce p e ≈ coerce q e
  coerce-uniq {Ψ} {A} {B} p q e = ≈-intro (coerce-uniqˢ {Γ = Γ} {Ψ} {A} {B} p q e)

module _ {n} {Γ : Ctx n} where
  pair-coerce : ∀ {Ψ₁ Ψ₂ A A′ B B′} (pa : A <: A′) (pb : B <: B′) (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B) → pair (coerce pa a) (coerce pb b) ≈ coerce (sub-prod pa pb) (pair a b)
  pair-coerce {Ψ₁} {Ψ₂} {A} {A′} {B} {B′} pa pb a b = ≈-intro (pair-coerceˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {A′} {B} {B′} pa pb a b)

module _ {n} {Γ : Ctx n} where
  app-coerce : ∀ {Ψ₁ Ψ₂ X A′ B} (a : X <: A′) (g : Once.Type.pure ⊑π Once.Type.pure) (f : Expr Γ Ψ₁ (A′ ⇒[ mk-kind Many Once.Type.pure ] B)) (x : Expr Γ Ψ₂ X) → app (coerce (sub-arr a (<:-refl B) g) f) x ≈ app f (coerce a x)
  app-coerce {Ψ₁} {Ψ₂} {X} {A′} {B} a g f x = ≈-intro (app-coerceˢ {Γ = Γ} {Ψ₁} {Ψ₂} {X} {A′} {B} a g f x)

module _ {n} {Γ : Ctx n} where
  comp-post : ∀ {Ψ₁ Ψ₂ A M B B′ π} (p : B <: B′) (r r′ : π ⊑π π) (f : Expr Γ Ψ₁ (M ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] M)) → comp' (coerce (sub-arr (<:-refl M) p r) f) g ≈ coerce (sub-arr (<:-refl A) p r′) (comp' f g)
  comp-post {Ψ₁} {Ψ₂} {A} {M} {B} {B′} {π} p r r′ f g = ≈-intro (comp-postˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {M} {B} {B′} {π} p r r′ f g)

module _ {n} {Γ : Ctx n} where
  comp-pre : ∀ {Ψ₁ Ψ₂ A B B′ C C′ π π′} (q : B <: B′) (c : C′ <: C) (g : π′ ⊑π π) (f : Expr Γ Ψ₁ (B′ ⇒[ mk-kind Many π′ ] C′)) (h : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B)) → comp' (coerce (sub-arr q c g) f) h ≈ comp' (coerce (sub-arr (<:-refl B′) c g) f) (coerce (sub-arr (<:-refl A) q (⊑π-refl π)) h)
  comp-pre {Ψ₁} {Ψ₂} {A} {B} {B′} {C} {C′} {π} {π′} q c g f h = ≈-intro (comp-preˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {B′} {C} {C′} {π} {π′} q c g f h)

module _ {n} {Γ : Ctx n} where
  lam-coerce : ∀ {Ψ q' π A B B′} (≤p : (q' ≤q Many) ≡ true) (p : B <: B′) (b : Expr (_,_^_ Γ A Many) (q' ∷ Ψ) B) → lam {π = π} Many ≤p (coerce p b) ≈ coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (lam Many ≤p b)
  lam-coerce {Ψ} {q'} {π} {A} {B} {B′} ≤p p b = ≈-intro (lam-coerceˢ {Γ = Γ} {Ψ} {q'} {π} {A} {B} {B′} ≤p p b)

module _ {n} {Γ : Ctx n} where
  copair-coerce : ∀ {Ψ₁ Ψ₂ A B C C′ π} (p : C <: C′) (r : π ⊑π π) (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C)) (g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C)) → copair' (coerce (sub-arr (<:-refl A) p r) f) (coerce (sub-arr (<:-refl B) p r) g) ≈ coerce (sub-arr (<:-refl (A + B)) p r) (copair' f g)
  copair-coerce {Ψ₁} {Ψ₂} {A} {B} {C} {C′} {π} p r f g = ≈-intro (copair-coerceˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} {C′} {π} p r f g)

module _ {n} {Γ : Ctx n} where
  fork-coerce : ∀ {Ψ₁ Ψ₂ A B B′ C C′ π} (pb : B <: B′) (pc : C <: C′) (r : π ⊑π π) (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] B)) (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] C)) → fork' (coerce (sub-arr (<:-refl A) pb r) f) (coerce (sub-arr (<:-refl A) pc r) g) ≈ coerce (sub-arr (<:-refl A) (sub-prod pb pc) r) (fork' f g)
  fork-coerce {Ψ₁} {Ψ₂} {A} {B} {B′} {C} {C′} {π} pb pc r f g = ≈-intro (fork-coerceˢ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {B′} {C} {C′} {π} pb pc r f g)

module _ {n} {Γ : Ctx n} where
  initial-coerce : ∀ {A π} (r : π ⊑π π) → coerce (sub-arr sub-void sub-void r) (lift-morphism {Γ = Γ} {A = Void} {B = Void} {π = π} IR.initial) ≈ lift-morphism {Γ = Γ} {A = Void} {B = A} {π = π} IR.initial
  initial-coerce {A} {π} r = ≈-intro (initial-coerceˢ {Γ = Γ} {A} {π} r)

module _ {n} {Γ : Ctx n} where
  cata-coerce : ∀ {Ψ F A A′ π} (wf : WellFormedF F) (d : ⟦ F ⟧T A′ <: ⟦ F ⟧T A) (p : A <: A′) (g : π ⊑π π) (alg : Expr Γ Ψ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)) → cata {Γ = Γ} wf (coerce (sub-arr {q = Many} d p g) alg) ≈ coerce (sub-arr (<:-refl (μ-type F)) p (⊑π-refl π)) (cata {Γ = Γ} wf alg)
  cata-coerce {Ψ} {F} {A} {A′} {π} wf d p g alg = ≈-intro (cata-coerceˢ {Γ = Γ} {Ψ} {F} {A} {A′} {π} wf d p g alg)
