-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.ModeSub — CHECKING ACCEPTS ONLY SUPERTYPES OF WHAT IS
-- INFERRED (plan 0.103, coherence).
--
-- `ModeAgreement` shows that the modes agree on USAGE. This module shows the
-- type half of the same fact: whenever a term both synthesizes `A` and checks
-- at `B`, `A <: B`; and whenever it is domain-given at `A ↦ B` and checks at
-- `A ⇒ B′`, `B <: B′`. Inference reports the least type, and the conversion is
-- the one `t-sub` would insert — with one exception (D313): a generator
-- also checks at its declared arrow's guard, which is incomparable with the
-- declaration, so the lemmas conclude `_≼_` and each consumer rules the guard
-- out from the grade evidence it holds.
--
-- The coherence proof (`Adequacy.Coherence`) needs the witness exactly where
-- two derivations of one term take different routes: `t-app` against the
-- spine, and `t-compose-check-g` against `t-compose-check-f` (whose middle
-- types differ, related by this lemma).
--
-- The induction follows `agree-ic` / `agree-dc` clause for clause.
------------------------------------------------------------------------

module Once.TypeCheck.ModeSub where

import Once.TypeCheck.Classify
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Spec.Type as T using (Type; _*_; _⇒[_]_)
import Once.Spec.Type.Poly as T
import Once.Spec.Type.Grade as T
open import Once.Spec.Type.Sub using (_<:_; _⊑π_; sub-arr; sub-prod; sub-void)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Once.Spec.Type.Sub using (<:-refl)
open import Once.Spec.Syntax using (RawExpr)
open import Once.Spec.Typing.Scope using (NamedCtx)
import Once.Spec.Typing.Scope
open import Once.Spec.Typing
open import Once.Metatheory.ModeAgreement
import Once.Spec.Context as Surface

private
  just≢nothing : ∀ {ℓ} {X : Set ℓ} {x : X} → just x ≡ nothing → ⊥
  just≢nothing ()

  -- Refute by an absurd pattern on an equation's or agreement's value.
  ex : ∀ {ℓ} {P : Set ℓ} → P → (P → ⊥) → ⊥
  ex p f = f p

-- An instance of an arrow schema has the schema's grade.
arrow-at : ∀ {s sd sc : T.PolyType} {π′ π : T.Purity} {A B : Type} (θ : _)
         → T.ArrowSchema s sd sc π′ → T.substPoly θ s ≡ (A ⇒[ T.mk-kind T.Many π ] B)
         → T.ArrowSchema s sd sc π
arrow-at θ T.as-pure refl = T.as-pure
arrow-at θ T.as-eff  refl = T.as-eff
arrow-at θ T.as-act  refl = T.as-act

-- The domain half of an arrow conversion (contravariant).
sub-dom : ∀ {A A′ B B′ : Type} {k k′} → (A ⇒[ k ] B) <: (A′ ⇒[ k′ ] B′) → A′ <: A
sub-dom (sub-arr a _ _) = a

-- The codomain half of an arrow conversion.
sub-cod : ∀ {A A′ B B′ : Type} {k k′} → (A ⇒[ k ] B) <: (A′ ⇒[ k′ ] B′) → B <: B′
sub-cod (sub-arr _ b _) = b

-- D313 (plan 0.117 F3a): what checking accepts beyond the inferred type. A
-- generator inferred at its declared effectful arrow also checks at that
-- arrow's GUARD, which is not a supertype (`act` and `eff⁺` are incomparable);
-- a pair literal carries such a step into a component. Every consumer meets
-- this at an arrow whose grade evidence rules the guard out (below).
infix 4 _≼_
data _≼_ : Type → Type → Set where
  ≼-sub   : ∀ {A B} → A <: B → A ≼ B
  ≼-guard : ∀ {A B q π} → T.EffGrade π
          → (A ⇒[ T.mk-kind q π ] B) ≼ (A ⇒[ T.mk-kind q T.eff⁺ ] B)
  ≼-prod  : ∀ {A A′ B B′} → A ≼ A′ → B ≼ B′ → (A * B) ≼ (A′ * B′)

-- At arrows: the inferred grade below the checked one rules the guard out…
≼-g : ∀ {A A′ B B′ q π₀ π} → (A ⇒[ T.mk-kind q π₀ ] B) ≼ (A′ ⇒[ T.mk-kind q π ] B′) → π₀ ⊑π π
    → (A ⇒[ T.mk-kind q π₀ ] B) <: (A′ ⇒[ T.mk-kind q π ] B′)
≼-g (≼-sub p) _ = p
≼-g (≼-guard T.eg-act) ()
≼-g (≼-guard T.eg-eff) ()

-- …as does one grade on both sides…
≼-same : ∀ {A A′ B B′ q π} → (A ⇒[ T.mk-kind q π ] B) ≼ (A′ ⇒[ T.mk-kind q π ] B′)
       → (A ⇒[ T.mk-kind q π ] B) <: (A′ ⇒[ T.mk-kind q π ] B′)
≼-same (≼-sub p) = p

-- …and a conversion of the inferred type to an arrow at the checked grade.
≼-s : ∀ {D M M′ B B′ q π} → D ≼ (M′ ⇒[ T.mk-kind q π ] B′) → D <: (M ⇒[ T.mk-kind q π ] B)
    → D <: (M′ ⇒[ T.mk-kind q π ] B′)
≼-s (≼-sub p) _ = p
≼-s (≼-guard T.eg-act) (sub-arr _ _ ())
≼-s (≼-guard T.eg-eff) (sub-arr _ _ ())

-- A domain-given term that also synthesizes: its given domain is below the
-- synthesized one (the spine's argument conversion).
di-dom : ∀ {ctx : NamedCtx} {e : RawExpr} {X T₀ A B : Type} {π : T.Purity} {k : T.ArrowKind}
           {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
       → ctx ⊢ᵈ e ∶ X ⇒[ π ]↦ T₀ ⨾ Ψ → ctx ⊢ᵢ e ∶ (A ⇒[ k ] B) ⨾ Ψ′ → X <: A
di-dom (d-infer w a _) d = dom-along (agree-ii w d) a
  where
    dom-along : ∀ {X A₀ A B₀ B : Type} {k₀ k : T.ArrowKind} {Y : Set}
              → ((A₀ ⇒[ k₀ ] B₀) ≡ (A ⇒[ k ] B)) × Y → X <: A₀ → X <: A
    dom-along (refl , _) a = a
di-dom (d-lam _) ()
di-dom (d-compose _ _) d = ⊥-elim (noinf-compose d)
di-dom d-id d = ⊥-elim (noinf-id d)
di-dom d-fst d = ⊥-elim (noinf-fst d)
di-dom d-snd d = ⊥-elim (noinf-snd d)
di-dom d-terminal d = ⊥-elim (noinf-terminal d)
di-dom d-initial d = ⊥-elim (noinf-initial d)
di-dom (d-case _ _) d = ⊥-elim (noinf-case d)
di-dom (d-pair _ _) d = ⊥-elim (noinf-pair d)
di-dom (d-cata _ _) d = ⊥-elim (noinf-cata-app d)
di-dom (d-poly ln _ _ _ _ _ _ _) (t-var-local l) = ⊥-elim (just≢nothing (trans (sym l) ln))
di-dom (d-poly _ inn _ _ _ _ _ _) (t-var-import _ _ i _) = ⊥-elim (just≢nothing (trans (sym i) inn))
di-dom (d-poly _ _ p ¬g _ _ _ _) (t-var-poly-instantiate-infer _ _ p′ g _) =
  ⊥-elim (ex (trans (sym p) p′) λ { refl → ¬g g })

-- The steps below take `ModeAgreement`'s equations as ARGUMENTS (no `with`).
private
  ≡-sub : ∀ {A B : Type} → A ≡ B → A <: B
  ≡-sub refl = <:-refl _

  sub-along : ∀ {A A′ B : Type} {X : Set} → (A ≡ A′ × X) → A′ <: B → A <: B
  sub-along (refl , _) p = p

  apply-sub : ∀ {A A′ B B′ : Type} {X : Set}
            → ((A ⇒[ T.mk-kind T.Many T.pure ] B) * A) ≡ ((A′ ⇒[ T.mk-kind T.Many T.pure ] B′) * A′) × X → B <: B′
  apply-sub (refl , _) = <:-refl _

  di-cod : ∀ {S A₁ B B′ : Type} {π : T.Purity} {P : Type → T.Purity → Set}
         → Σ Type (λ A′ → Σ T.Purity (λ π′ → (S ≡ (A′ ⇒[ T.mk-kind T.Many π′ ] B)) × P A′ π′))
         → S <: (A₁ ⇒[ T.mk-kind T.Many π ] B′) → B <: B′
  di-cod (_ , _ , refl , _) p = sub-cod p

  guard-pair : ∀ {D A B : Type} {q : T.Quantity} {π : T.Purity}
             → just D ≡ just (A ⇒[ T.mk-kind q π ] B) → T.EffGrade π
             → D ≼ (A ⇒[ T.mk-kind q T.eff⁺ ] B)
  guard-pair refl g = ≼-guard g

  poly-sub : ∀ {s s′ sd sc : T.PolyType} {b b′ : RawExpr} {pr pr′ : Once.Spec.Typing.Scope.PolyCtx} {A B B′ : Type} {π π′ : T.Purity}
             (ep : just (s , b , pr) ≡ just (s′ , b′ , pr′)) (as : T.ArrowSchema s sd sc π′) (inc : T.CodVarsInDom sd sc)
             (θ : _) (e : T.substPoly θ s ≡ (A ⇒[ T.mk-kind T.Many π′ ] B))
             (θ′ : _) (e′ : T.substPoly θ′ s′ ≡ (A ⇒[ T.mk-kind T.Many π ] B′))
           → B <: B′
  poly-sub refl as inc θ e θ′ e′ = ≡-sub (dpoly-det as (arrow-at θ′ as e′) inc θ θ′ e e′)

mutual
  ic-sub : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
         → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → A ≼ B
  ic-sub d (t-sub d′ p) = ≼-sub (sub-along (agree-ii d d′) p)
  ic-sub (t-pair a b) (t-pair-lit-check a′ b′) = ≼-prod (ic-sub a a′) (ic-sub b b′)
  ic-sub (t-apply-app-infer d) (t-apply-check d′) = ≼-sub (apply-sub (agree-ii d d′))
  ic-sub (t-var-resolved _ l _) (t-var-resolved-guard _ l′ g _) = guard-pair (trans (sym l) l′) g
  ic-sub t-unit-var (t-var-resolved-guard (_ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ ¬u ∷ᴬ _) _ _ _) = ⊥-elim (¬u refl)
  ic-sub (t-var-own n _ _) (t-var-resolved-guard _ l _ _) = ⊥-elim (just≢nothing (trans (sym l) n))
  ic-sub (t-apply-eff-app-infer {g = T.eg-act} d) (t-apply-check d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  ic-sub (t-apply-eff-app-infer {g = T.eg-eff} d) (t-apply-check d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  ic-sub (t-app () _ _) (t-apply-check _)
  ic-sub (t-effApp () _ _) (t-apply-check _)
  ic-sub (t-app-spine () _ _) (t-apply-check _)
  ic-sub (t-var-local l) (t-var-poly-instantiate ln _ _ _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  ic-sub (t-var-import _ _ i _) (t-var-poly-instantiate _ inn _ _ _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  ic-sub (t-var-poly-instantiate-infer _ _ p g _) (t-var-poly-instantiate _ _ p′ ¬g _) =
    ⊥-elim (ex (trans (sym p) p′) λ { refl → ¬g g })
  ic-sub () (t-lam _ _)
  ic-sub d t-id-check = ⊥-elim (noinf-id d)
  ic-sub d t-fst-check = ⊥-elim (noinf-fst d)
  ic-sub d t-snd-check = ⊥-elim (noinf-snd d)
  ic-sub d t-terminal-morph-check = ⊥-elim (noinf-terminal d)
  ic-sub d t-initial-morph-check = ⊥-elim (noinf-initial d)
  ic-sub d t-inl-morph-check = ⊥-elim (noinf-inl d)
  ic-sub d t-inr-morph-check = ⊥-elim (noinf-inr d)
  ic-sub d (t-compose-check-g _ _) = ⊥-elim (noinf-compose d)
  ic-sub d (t-compose-check-f _ _ _) = ⊥-elim (noinf-compose d)
  ic-sub d (t-case-copair-check _ _) = ⊥-elim (noinf-case d)
  ic-sub d (t-pair-morph-check _ _) = ⊥-elim (noinf-pair d)
  ic-sub d (t-curry-check _) = ⊥-elim (noinf-curry-app d)
  ic-sub d (t-cata-check _ _) = ⊥-elim (noinf-cata-app d)
  ic-sub d (t-ana-check _ _) = ⊥-elim (noinf-ana-app d)
  ic-sub d (t-In-app-check _ _) = ⊥-elim (noinf-In-app d)
  ic-sub d (t-inl-app-check _) = ⊥-elim (noinf-inl-app d)
  ic-sub d (t-inr-app-check _) = ⊥-elim (noinf-inr-app d)
  ic-sub d (t-initial-app-check _) = ⊥-elim (noinf-initial-app d)

  dc-sub : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : T.Purity}
             {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
         → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′ → B ≼ B′
  dc-sub (d-infer w _ g) c = ≼-sub (sub-cod (≼-g (ic-sub w c) g))
  {-# CATCHALL #-}
  dc-sub dd (t-sub d p) = ≼-sub (di-cod (agree-di dd d) p)
  dc-sub (d-lam b) (t-lam _ b′) = ic-sub b b′
  dc-sub (d-compose dg df) (t-compose-check-g dg′ df′) = cg-sub (proj₁ (agree-dd dg dg′)) df df′
  dc-sub (d-compose dg df) (t-compose-check-f wf s dg′) = ≼-sub (di-cod (agree-di df wf) s)
  dc-sub d-id t-id-check = ≼-sub (<:-refl _)
  dc-sub d-fst t-fst-check = ≼-sub (<:-refl _)
  dc-sub d-snd t-snd-check = ≼-sub (<:-refl _)
  dc-sub d-terminal t-terminal-morph-check = ≼-sub (<:-refl _)
  dc-sub d-initial t-initial-morph-check = ≼-sub sub-void
  dc-sub (d-case df dg) (t-case-copair-check df′ dg′) = dc-sub df df′
  dc-sub (d-pair df dg) (t-pair-morph-check df′ dg′) = ≼-prod (dc-sub df df′) (dc-sub dg dg′)
  dc-sub (d-cata _ a) (t-cata-check _ a′) = ≼-sub (sub-cod (≼-same (ic-sub a a′)))
  dc-sub (d-poly _ _ p _ as inc (θ , e , _) _) (t-var-poly-instantiate _ _ p′ _ (θ′ , e′ , _)) =
    ≼-sub (poly-sub (trans (sym p) p′) as inc θ e θ′ e′)

  -- The outer arm against the `g` route: its domain is the middle `g` determines.
  cg-sub : ∀ {ctx : NamedCtx} {e : RawExpr} {M M′ B B′ : Type} {π : T.Purity} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
         → M ≡ M′ → ctx ⊢ᵈ e ∶ M ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (M′ ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′ → B ≼ B′
  cg-sub refl df df′ = dc-sub df df′
