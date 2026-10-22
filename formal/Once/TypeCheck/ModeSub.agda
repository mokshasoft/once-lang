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
-- the one `t-sub` would insert.
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
open import Once.Spec.Type using (Ty)
open import Once.Internal.Type.Join using (least-<:)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Spec.Type as T using (Type; _*_; _⇒[_]_)
import Once.Internal.Type.Poly as T
import Once.Spec.Grade as T
open import Once.Spec.Sub using (_<:_; sub-arr; sub-void)
open import Once.Internal.Type.Sub using (sub-prod)
open import Once.Spec.Grade using (_⊑π_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Once.Internal.Type.Sub using (<:-refl)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Internal.Typing.Scope using (NamedCtx)
import Once.Internal.Typing.Scope
open import Once.Internal.Typing
open import Once.Internal.Laws.ModeAgreement
import Once.Internal.Context as Surface

private
  just≢nothing : ∀ {ℓ} {X : Set ℓ} {x : X} → just x ≡ nothing → ⊥
  just≢nothing ()

  -- Refute by an absurd pattern on an equation's or agreement's value.
  ex : ∀ {ℓ} {P : Set ℓ} → P → (P → ⊥) → ⊥
  ex p f = f p

-- An instance of an arrow schema has the schema's grade.
arrow-at : ∀ {m} {s sd sc : T.PolyType} {π′ π : T.Purity} {A B : Ty m} (θ : _)
         → T.ArrowSchema s sd sc π′ → T.substPoly θ s ≡ (A ⇒[ T.mk-kind T.Many π ] B)
         → T.ArrowSchema s sd sc π
arrow-at θ T.as-pure refl = T.as-pure
arrow-at θ T.as-eff  refl = T.as-eff
arrow-at θ T.as-act  refl = T.as-act

-- The domain half of an arrow conversion (contravariant).
sub-dom : ∀ {m} {A A′ B B′ : Ty m} {k k′} → (A ⇒[ k ] B) <: (A′ ⇒[ k′ ] B′) → A′ <: A
sub-dom (sub-arr a _ _) = a

-- The codomain half of an arrow conversion.
sub-cod : ∀ {m} {A A′ B B′ : Ty m} {k k′} → (A ⇒[ k ] B) <: (A′ ⇒[ k′ ] B′) → B <: B′
sub-cod (sub-arr _ b _) = b

-- A domain-given term that also synthesizes: its given domain is below the
-- synthesized one (the spine's argument conversion).
di-dom : ∀ {m} {ctx : NamedCtx m} {e : RawExpr} {X T₀ A B : Ty m} {π : T.Purity} {k : T.ArrowKind}
           {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
       → ctx ⊢ᵈ e ∶ X ⇒[ π ]↦ T₀ ⨾ Ψ → ctx ⊢ᵢ e ∶ (A ⇒[ k ] B) ⨾ Ψ′ → X <: A
di-dom (d-infer w a _) d = dom-along (agree-ii w d) a
  where
    dom-along : ∀ {X A₀ A B₀ B : Ty _} {k₀ k : T.ArrowKind} {Y : Set}
              → ((A₀ ⇒[ k₀ ] B₀) ≡ (A ⇒[ k ] B)) × Y → X <: A₀ → X <: A
    dom-along (refl , _) a = a
di-dom (d-lam _) ()
di-dom (d-compose _ _) d = ⊥-elim (noinf-compose d)
di-dom d-id d = ⊥-elim (noinf-id d)
di-dom d-fst d = ⊥-elim (noinf-fst d)
di-dom d-snd d = ⊥-elim (noinf-snd d)
di-dom d-terminal d = ⊥-elim (noinf-terminal d)
di-dom d-initial d = ⊥-elim (noinf-initial d)
di-dom (d-case _ _ _) d = ⊥-elim (noinf-case d)
di-dom (d-pair _ _) d = ⊥-elim (noinf-pair d)
di-dom (d-cata _ _) d = ⊥-elim (noinf-cata-app d)
di-dom (d-poly ns _ _ _ _ _ _ _) (t-var-resolved _ _ l _ _) = ⊥-elim (just≢nothing (trans (sym l) ns))
di-dom (d-poly _ inn _ _ _ _ _ _) (t-var-own _ i _) = ⊥-elim (just≢nothing (trans (sym i) inn))
di-dom (d-poly _ _ p ¬g _ _ _ _) (t-var-poly-instantiate-infer _ _ p′ g _) =
  ⊥-elim (ex (trans (sym p) p′) λ { refl → ¬g g })

-- The steps below take `ModeAgreement`'s equations as ARGUMENTS (no `with`).
private
  ≡-sub : ∀ {m} {A B : Ty m} → A ≡ B → A <: B
  ≡-sub refl = <:-refl _

  sub-along : ∀ {m} {A A′ B : Ty m} {X : Set} → (A ≡ A′ × X) → A′ <: B → A <: B
  sub-along (refl , _) p = p

  apply-sub : ∀ {m} {A A′ B B′ : Ty m} {X : Set}
            → ((A ⇒[ T.mk-kind T.Many T.pure ] B) * A) ≡ ((A′ ⇒[ T.mk-kind T.Many T.pure ] B′) * A′) × X → B <: B′
  apply-sub (refl , _) = <:-refl _

  di-cod : ∀ {m} {S A₁ B B′ : Ty m} {π : T.Purity} {P : Ty m → T.Purity → Set}
         → Σ (Ty m) (λ A′ → Σ T.Purity (λ π′ → (S ≡ (A′ ⇒[ T.mk-kind T.Many π′ ] B)) × P A′ π′))
         → S <: (A₁ ⇒[ T.mk-kind T.Many π ] B′) → B <: B′
  di-cod (_ , _ , refl , _) p = sub-cod p


  poly-sub : ∀ {m} {s s′ sd sc : T.PolyType} {b b′ : RawExpr} {pr pr′ : Once.Internal.Typing.Scope.PolyCtx} {A B B′ : Ty m} {π π′ : T.Purity}
             (ep : just (s , b , pr) ≡ just (s′ , b′ , pr′)) (as : T.ArrowSchema s sd sc π′) (inc : T.CodVarsInDom sd sc)
             (θ : _) (e : T.substPoly θ s ≡ (A ⇒[ T.mk-kind T.Many π′ ] B))
             (θ′ : _) (e′ : T.substPoly θ′ s′ ≡ (A ⇒[ T.mk-kind T.Many π ] B′))
           → B <: B′
  poly-sub refl as inc θ e θ′ e′ = ≡-sub (dpoly-det as (arrow-at θ′ as e′) inc θ θ′ e e′)

mutual
  ic-sub : ∀ {m} {ctx : NamedCtx m} {e : RawExpr} {A B : Ty m} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
         → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → A <: B
  ic-sub d (t-sub d′ p) = sub-along (agree-ii d d′) p
  ic-sub (t-pair a b) (t-pair-lit-check a′ b′) = sub-prod (ic-sub a a′) (ic-sub b b′)
  ic-sub (t-apply-app-infer d) (t-apply-check d′) = apply-sub (agree-ii d d′)
  ic-sub (t-apply-eff-app-infer {g = T.eg-act} d) (t-apply-check d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  ic-sub (t-apply-eff-app-infer {g = T.eg-eff} d) (t-apply-check d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  ic-sub (t-app () _ _) (t-apply-check _)
  ic-sub (t-effApp () _ _) (t-apply-check _)
  ic-sub (t-app-spine () _ _) (t-apply-check _)
  ic-sub (t-var-resolved _ _ l _ _) (t-var-poly-instantiate ns _ _ _ _) = ⊥-elim (just≢nothing (trans (sym l) ns))
  ic-sub (t-var-own _ i _) (t-var-poly-instantiate _ inn _ _ _) = ⊥-elim (just≢nothing (trans (sym i) inn))
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
  ic-sub d (t-loop-check _) = ⊥-elim (noinf-ana-app d)
  ic-sub d (t-In-app-check _ _) = ⊥-elim (noinf-In-app d)
  ic-sub d (t-inl-app-check _) = ⊥-elim (noinf-inl-app d)
  ic-sub d (t-inr-app-check _) = ⊥-elim (noinf-inr-app d)
  ic-sub d (t-initial-app-check _) = ⊥-elim (noinf-initial-app d)

  dc-sub : ∀ {m} {ctx : NamedCtx m} {e : RawExpr} {A B B′ : Ty m} {π : T.Purity}
             {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
         → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′ → B <: B′
  dc-sub (d-infer w _ g) c = sub-cod (ic-sub w c)
  {-# CATCHALL #-}
  dc-sub dd (t-sub d p) = di-cod (agree-di dd d) p
  dc-sub (d-lam b) (t-lam _ b′) = ic-sub b b′
  dc-sub (d-compose dg df) (t-compose-check-g dg′ df′) = cg-sub (proj₁ (agree-dd dg dg′)) df df′
  dc-sub (d-compose dg df) (t-compose-check-f wf s dg′) = di-cod (agree-di df wf) s
  dc-sub d-id t-id-check = <:-refl _
  dc-sub d-fst t-fst-check = <:-refl _
  dc-sub d-snd t-snd-check = <:-refl _
  dc-sub d-terminal t-terminal-morph-check = <:-refl _
  dc-sub d-initial t-initial-morph-check = sub-void
  dc-sub (d-case df dg J) (t-case-copair-check df′ dg′) = least-<: J (dc-sub df df′) (dc-sub dg dg′)
  dc-sub (d-pair df dg) (t-pair-morph-check df′ dg′) = sub-prod (dc-sub df df′) (dc-sub dg dg′)
  dc-sub (d-cata _ a) (t-cata-check _ a′) = sub-cod (ic-sub a a′)
  dc-sub (d-poly _ _ p _ as inc (θ , e , _) _) (t-var-poly-instantiate _ _ p′ _ (θ′ , e′ , _)) =
    (poly-sub (trans (sym p) p′) as inc θ e θ′ e′)

  -- The outer arm against the `g` route: its domain is the middle `g` determines.
  cg-sub : ∀ {m} {ctx : NamedCtx m} {e : RawExpr} {M M′ B B′ : Ty m} {π : T.Purity} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
         → M ≡ M′ → ctx ⊢ᵈ e ∶ M ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (M′ ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′ → B <: B′
  cg-sub refl df df′ = dc-sub df df′
