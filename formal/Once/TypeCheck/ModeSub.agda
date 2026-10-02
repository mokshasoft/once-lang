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

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Type as T using (Type; _*_; _⇒[_]_)
open import Once.Type.Sub using (_<:_; sub-arr; sub-prod; sub-void; <:-refl; _⊑π_)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment
open import Once.TypeCheck.ModeAgreement
import Once.Surface.Context as Surface

private
  just≢nothing : ∀ {ℓ} {X : Set ℓ} {x : X} → just x ≡ nothing → ⊥
  just≢nothing ()

-- An instance of an arrow schema has the schema's grade.
arrow-at : ∀ {s sd sc : T.PolyType} {π′ π : T.Purity} {A B : Type} (θ : _)
         → T.ArrowSchema s sd sc π′ → T.substPoly θ s ≡ (A ⇒[ T.mk-kind T.Many π ] B)
         → T.ArrowSchema s sd sc π
arrow-at θ T.as-pure refl = T.as-pure
arrow-at θ T.as-eff  refl = T.as-eff

-- The codomain half of an arrow conversion.
sub-cod : ∀ {A A′ B B′ : Type} {k k′} → (A ⇒[ k ] B) <: (A′ ⇒[ k′ ] B′) → B <: B′
sub-cod (sub-arr _ b _) = b

mutual
  ic-sub : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
         → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → A <: B
  ic-sub d (t-sub d′ p) with agree-ii d d′
  ... | refl , _ = p
  ic-sub (t-pair a b) (t-pair-lit-check a′ b′) = sub-prod (ic-sub a a′) (ic-sub b b′)
  ic-sub (t-apply-app-infer d) (t-apply-check d′) with agree-ii d d′
  ... | refl , _ = <:-refl _
  ic-sub (t-apply-eff-app-infer d) (t-apply-check d′) with agree-ii d d′
  ... | () , _
  ic-sub (t-app () _ _) (t-apply-check _)
  ic-sub (t-effApp () _ _) (t-apply-check _)
  ic-sub (t-app-spine () _ _) (t-apply-check _)
  ic-sub (t-var-local l) (t-var-poly-instantiate ln _ _ _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  ic-sub (t-var-import _ _ i _) (t-var-poly-instantiate _ inn _ _ _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  ic-sub (t-var-poly-instantiate-infer _ _ p g _) (t-var-poly-instantiate _ _ p′ ¬g _) with trans (sym p) p′
  ... | refl = ⊥-elim (¬g g)
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
         → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′ → B <: B′
  dc-sub (d-infer w _ _) c = sub-cod (ic-sub w c)
  dc-sub dd (t-sub d p) with agree-di dd d
  ... | _ , _ , refl , _ , _ = sub-cod p
  dc-sub (d-lam _ b) (t-lam _ b′) = ic-sub b b′
  dc-sub (d-compose dg df) (t-compose-check-g dg′ df′) with agree-dd dg dg′
  ... | refl , _ = dc-sub df df′
  dc-sub (d-compose dg df) (t-compose-check-f wf s dg′) with agree-di df wf
  ... | _ , _ , refl , _ , _ = sub-cod s
  dc-sub d-id t-id-check = <:-refl _
  dc-sub d-fst t-fst-check = <:-refl _
  dc-sub d-snd t-snd-check = <:-refl _
  dc-sub d-terminal t-terminal-morph-check = <:-refl _
  dc-sub d-initial t-initial-morph-check = sub-void
  dc-sub (d-case df dg) (t-case-copair-check df′ dg′) = dc-sub df df′
  dc-sub (d-pair df dg) (t-pair-morph-check df′ dg′) = sub-prod (dc-sub df df′) (dc-sub dg dg′)
  dc-sub (d-cata _ a) (t-cata-check _ a′) = sub-cod (ic-sub a a′)
  dc-sub (d-poly _ _ p _ as inc (θ , e , _) _) (t-var-poly-instantiate _ _ p′ _ (θ′ , e′ , _)) with trans (sym p) p′
  ... | refl with dpoly-det as (arrow-at θ′ as e′) inc θ θ′ e e′
  ...   | refl = <:-refl _
