-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.RouteBuild — EVERY TWO DERIVATIONS OF ONE TERM HAVE A
-- ROUTE (plan 0.103, coherence).
--
-- The case split over pairs of derivations, in the shape of `ModeAgreement`.
-- A possible pair is a route constructor applied to the routes of its
-- premises; routes are heterogeneous, so no alignment is needed except where
-- a premise's context or check type depends on an index (a binder, an
-- argument checked at the head's domain, a middle type). Those few align by
-- a top-level helper that takes `ModeAgreement`'s equation as an ARGUMENT —
-- no `with`. An impossible pair is refuted by applying an absurd pattern to
-- `ModeAgreement`'s result. Nothing here mentions a meaning.
------------------------------------------------------------------------

module Once.TypeCheck.RouteBuild where

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Type as T using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Type.Sub using (_<:_; _⊑π_; ⊑-pure; ⊑-eff; ⊑-pe)
open import Once.TypeCheck.Raw as Raw using (RawExpr; RResolved; RApp; BinOp; isArithmeticOp; isComparisonOp)
open import Once.CanonicalName using (gen)
open import Once.TypeCheck.Classify using (NamedCtx; extendNamedCtx; classifyAppHead)
open import Data.Maybe using (Maybe)
open import Once.TypeCheck.Judgment
open import Once.TypeCheck.ModeAgreement
open import Once.TypeCheck.ModeSub using (arrow-at)
open import Once.TypeCheck.Route
import Once.Surface.Context as Surface
open Surface using (zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)

private
  just≢nothing : ∀ {ℓ} {X : Set ℓ} {x : X} → just x ≡ nothing → ⊥
  just≢nothing ()

  cod-≡ : ∀ {A A′ B B′ : Type} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → B ≡ B′
  cod-≡ refl = refl

  arith-not-cmp : ∀ (op : BinOp) → isArithmeticOp op ≡ true → isComparisonOp op ≡ true → ⊥
  arith-not-cmp Raw.OpAdd refl ()
  arith-not-cmp Raw.OpSub refl ()
  arith-not-cmp Raw.OpMul refl ()
  arith-not-cmp Raw.OpDiv refl ()
  arith-not-cmp Raw.OpMod refl ()
  arith-not-cmp Raw.OpLt () _
  arith-not-cmp Raw.OpLe () _
  arith-not-cmp Raw.OpGt () _
  arith-not-cmp Raw.OpGe () _
  arith-not-cmp Raw.OpEq () _
  arith-not-cmp Raw.OpNe () _

  -- Refute a pair by an absurd pattern on what `ModeAgreement` returns for it.
  ex : ∀ {ℓ} {P : Set ℓ} → P → (P → ⊥) → ⊥
  ex p f = f p

------------------------------------------------------------------------
-- THE CASE SPLIT
------------------------------------------------------------------------

private U : NamedCtx → Set
        U ctx = Surface.Usage (NamedCtx.size ctx)

mutual
  route-ii : ∀ {ctx e A A′ Ψ Ψ′} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ) (d′ : ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′) → Rii d d′
  route-cc : ∀ {ctx e A Ψ Ψ′} (c : ctx ⊢ᶜ e ∶ A ⨾ Ψ) (c′ : ctx ⊢ᶜ e ∶ A ⨾ Ψ′) → Rcc c c′
  route-ic : ∀ {ctx e A B Ψ Ψ′} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ) (c : ctx ⊢ᶜ e ∶ B ⨾ Ψ′) → Ric d c
  route-dc : ∀ {ctx e A B B′ π Ψ Ψ′} (dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) (c : ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′) → Rdc dd c
  route-di : ∀ {ctx e A A′ B B′ π q π′ Ψ Ψ′} (dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) (d : ctx ⊢ᵢ e ∶ (A′ ⇒[ T.mk-kind q π′ ] B′) ⨾ Ψ′) → Rdi dd d
  route-dd : ∀ {ctx e A B B′ π Ψ Ψ′} (dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) (dd′ : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′) → Rdd dd dd′

  ----------------------------------------------------------------------
  -- The alignments, each taking `ModeAgreement`'s equation as an argument.

  let-r : ∀ {ctx x e₁ e₂ A A′ B B′ q q′} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
          (d₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁) (d₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B ⨾ (q Surface.Usage.∷ Ψ₂))
          (d₁′ : ctx ⊢ᵢ e₁ ∶ A′ ⨾ Ψ₁′) (d₂′ : extendNamedCtx ctx x A′ ⊢ᵢ e₂ ∶ B′ ⨾ (q′ Surface.Usage.∷ Ψ₂′))
        → A ≡ A′ → Rii (t-let d₁ d₂) (t-let d₁′ d₂′)
  let-r d₁ d₂ d₁′ d₂′ refl = ii-let (route-ii d₁ d₁′) (route-ii d₂ d₂′)

  case-r : ∀ {ctx xL xR e₁ e₂ e₃ A A′ B B′ C C′ qL qL′ qR qR′} {Ψs Ψs′ Ψl Ψl′ Ψr Ψr′ : U ctx}
           (s : ctx ⊢ᵢ e₁ ∶ (A + B) ⨾ Ψs) (l : extendNamedCtx ctx xL A ⊢ᵢ e₂ ∶ C ⨾ (qL Surface.Usage.∷ Ψl))
           (r : extendNamedCtx ctx xR B ⊢ᵢ e₃ ∶ C ⨾ (qR Surface.Usage.∷ Ψr))
           (s′ : ctx ⊢ᵢ e₁ ∶ (A′ + B′) ⨾ Ψs′) (l′ : extendNamedCtx ctx xL A′ ⊢ᵢ e₂ ∶ C′ ⨾ (qL′ Surface.Usage.∷ Ψl′))
           (r′ : extendNamedCtx ctx xR B′ ⊢ᵢ e₃ ∶ C′ ⨾ (qR′ Surface.Usage.∷ Ψr′))
         → (A + B) ≡ (A′ + B′) → Rii (t-case s l r) (t-case s′ l′ r′)
  case-r s l r s′ l′ r′ refl = ii-case (route-ii s s′) (route-ii l l′) (route-ii r r′)

  app-r : ∀ {ctx e₁ e₂ A A′ B B′ q q′} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
          (h : classifyAppHead e₁ ≡ nothing) (f : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind q T.pure ] B) ⨾ Ψ₁) (x : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂)
          (h′ : classifyAppHead e₁ ≡ nothing) (f′ : ctx ⊢ᵢ e₁ ∶ (A′ ⇒[ T.mk-kind q′ T.pure ] B′) ⨾ Ψ₁′) (x′ : ctx ⊢ᶜ e₂ ∶ A′ ⨾ Ψ₂′)
        → (A ⇒[ T.mk-kind q T.pure ] B) ≡ (A′ ⇒[ T.mk-kind q′ T.pure ] B′) → Rii (t-app h f x) (t-app h′ f′ x′)
  app-r h f x h′ f′ x′ refl = ii-app (route-ii f f′) (route-cc x x′)

  effApp-r : ∀ {ctx e₁ e₂ A A′ B B′} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
             (h : classifyAppHead e₁ ≡ nothing) (f : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind T.Many T.eff ] B) ⨾ Ψ₁) (x : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂)
             (h′ : classifyAppHead e₁ ≡ nothing) (f′ : ctx ⊢ᵢ e₁ ∶ (A′ ⇒[ T.mk-kind T.Many T.eff ] B′) ⨾ Ψ₁′) (x′ : ctx ⊢ᶜ e₂ ∶ A′ ⨾ Ψ₂′)
           → (A ⇒[ T.mk-kind T.Many T.eff ] B) ≡ (A′ ⇒[ T.mk-kind T.Many T.eff ] B′) → Rii (t-effApp h f x) (t-effApp h′ f′ x′)
  effApp-r h f x h′ f′ x′ refl = ii-effApp (route-ii f f′) (route-cc x x′)

  spine-r : ∀ {ctx e₁ e₂ X X′ T T′} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
            (h : classifyAppHead e₁ ≡ nothing) (dX : ctx ⊢ᵢ e₂ ∶ X ⨾ Ψ₂) (dF : ctx ⊢ᵈ e₁ ∶ X ⇒[ T.pure ]↦ T ⨾ Ψ₁)
            (h′ : classifyAppHead e₁ ≡ nothing) (dX′ : ctx ⊢ᵢ e₂ ∶ X′ ⨾ Ψ₂′) (dF′ : ctx ⊢ᵈ e₁ ∶ X′ ⇒[ T.pure ]↦ T′ ⨾ Ψ₁′)
          → X ≡ X′ → Rii (t-app-spine h dX dF) (t-app-spine h′ dX′ dF′)
  spine-r h dX dF h′ dX′ dF′ refl = ii-spine (route-ii dX dX′) (route-dd dF dF′)

  gg-r : ∀ {ctx e₁ e₂ A B B′ C π} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
         (dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ B ⨾ Ψ₂) (df : ctx ⊢ᶜ e₁ ∶ (B ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁)
         (dg′ : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ B′ ⨾ Ψ₂′) (df′ : ctx ⊢ᶜ e₁ ∶ (B′ ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁′)
       → B ≡ B′ → Rcc (t-compose-check-g dg df) (t-compose-check-g dg′ df′)
  gg-r dg df dg′ df′ refl = cc-gg (route-dd dg dg′) (route-cc df df′)

  ff-r : ∀ {ctx e₁ e₂ A B B″ C C′ C″ π π′ π″} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
         (wf : ctx ⊢ᵢ e₁ ∶ (B ⇒[ T.mk-kind T.Many π′ ] C′) ⨾ Ψ₁)
         (s : (B ⇒[ T.mk-kind T.Many π′ ] C′) <: (B ⇒[ T.mk-kind T.Many π ] C)) (dg : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] B) ⨾ Ψ₂)
         (wf′ : ctx ⊢ᵢ e₁ ∶ (B″ ⇒[ T.mk-kind T.Many π″ ] C″) ⨾ Ψ₁′)
         (s′ : (B″ ⇒[ T.mk-kind T.Many π″ ] C″) <: (B″ ⇒[ T.mk-kind T.Many π ] C)) (dg′ : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] B″) ⨾ Ψ₂′)
       → (B ⇒[ T.mk-kind T.Many π′ ] C′) ≡ (B″ ⇒[ T.mk-kind T.Many π″ ] C″)
       → Rcc (t-compose-check-f wf s dg) (t-compose-check-f wf′ s′ dg′)
  ff-r wf s dg wf′ s′ dg′ refl = cc-ff (route-ii wf wf′) (route-cc dg dg′)

  dcsub-r : ∀ {ctx e A B B′ S π} {Ψ Ψ′ : U ctx}
            (dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) (d : ctx ⊢ᵢ e ∶ S ⨾ Ψ′) (p : S <: (A ⇒[ T.mk-kind T.Many π ] B′))
          → Σ[ A₁ ∈ Type ] Σ[ π₁ ∈ T.Purity ] (S ≡ (A₁ ⇒[ T.mk-kind T.Many π₁ ] B)) × π₁ ⊑π π × Ψ ≡ Ψ′
          → Rdc dd (t-sub d p)
  dcsub-r dd d p (_ , _ , refl , _ , _) = dc-sub (route-di dd d)

  cg-r : ∀ {ctx e₁ e₂ A M M′ B B′ π} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
         (dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M ⨾ Ψ₂) (df : ctx ⊢ᵈ e₁ ∶ M ⇒[ π ]↦ B ⨾ Ψ₁)
         (dg′ : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M′ ⨾ Ψ₂′) (df′ : ctx ⊢ᶜ e₁ ∶ (M′ ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ₁′)
       → M ≡ M′ → Rdc (d-compose dg df) (t-compose-check-g dg′ df′)
  cg-r dg df dg′ df′ refl = dc-cg (route-dd dg dg′) (route-dc df df′)

  comp-r : ∀ {ctx e₁ e₂ A M M′ B B′ π} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : U ctx}
           (dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M ⨾ Ψ₂) (df : ctx ⊢ᵈ e₁ ∶ M ⇒[ π ]↦ B ⨾ Ψ₁)
           (dg′ : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M′ ⨾ Ψ₂′) (df′ : ctx ⊢ᵈ e₁ ∶ M′ ⇒[ π ]↦ B′ ⨾ Ψ₁′)
         → M ≡ M′ → Rdd (d-compose dg df) (d-compose dg′ df′)
  comp-r dg df dg′ df′ refl = dd-compose (route-dd dg dg′) (route-dd df df′)

  ----------------------------------------------------------------------
  -- The pairs (in `ModeAgreement`'s order).

  route-ii (t-int _) (t-int _) = ii-int
  route-ii (t-float _ _ _ _) (t-float _ _ _ _) = ii-float
  route-ii t-unit t-unit = ii-unit
  route-ii t-unit-var t-unit-var = ii-unit-var
  route-ii t-unit-var (t-var-resolved (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ ¬u ∷ _) _ _) = ⊥-elim (¬u refl)
  route-ii (t-var-resolved (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ ¬u ∷ _) _ _) t-unit-var = ⊥-elim (¬u refl)
  route-ii (t-var-resolved _ _ _) (t-var-resolved _ _ _) = ii-resolved
  route-ii (t-var-qualified _ _) (t-var-qualified _ _) = ii-qualified
  route-ii (t-var-local _) (t-var-local _) = ii-local
  route-ii (t-var-local l) (t-var-import _ ln _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  route-ii (t-var-local l) (t-var-poly-instantiate-infer ln _ _ _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  route-ii (t-var-import _ ln _ _) (t-var-local l) = ⊥-elim (just≢nothing (trans (sym l) ln))
  route-ii (t-var-import _ _ _ _) (t-var-import _ _ _ _) = ii-import
  route-ii (t-var-import _ _ i _) (t-var-poly-instantiate-infer _ inn _ _ _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  route-ii (t-var-poly-instantiate-infer ln _ _ _ _) (t-var-local l) = ⊥-elim (just≢nothing (trans (sym l) ln))
  route-ii (t-var-poly-instantiate-infer _ inn _ _ _) (t-var-import _ _ i _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  route-ii (t-var-poly-instantiate-infer _ _ _ _ _) (t-var-poly-instantiate-infer _ _ _ _ _) = ii-poly-infer
  route-ii (t-annot _ c) (t-annot _ c′) = ii-annot (route-cc c c′)
  route-ii (t-pair a b) (t-pair a′ b′) = ii-pair (route-ii a a′) (route-ii b b′)
  route-ii (t-neg d) (t-neg d′) = ii-neg (route-ii d d′)
  route-ii (t-neg ()) (t-neg-float _ _ _ _)
  route-ii (t-neg-float _ _ _ _) (t-neg ())
  route-ii (t-neg-float _ _ _ _) (t-neg-float _ _ _ _) = ii-neg-float
  route-ii (t-let d₁ d₂) (t-let d₁′ d₂′) = let-r d₁ d₂ d₁′ d₂′ (proj₁ (agree-ii d₁ d₁′))
  route-ii (t-case dS dL dR) (t-case dS′ dL′ dR′) = case-r dS dL dR dS′ dL′ dR′ (proj₁ (agree-ii dS dS′))
  route-ii (t-binop-arith _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) = ii-arith (route-ii d₁ d₁′) (route-ii d₂ d₂′)
  route-ii (t-binop-arith _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₂ d₂′) λ { (() , _) })
  route-ii (t-binop-arith _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith {op = op} a _ _) (t-binop-cmp c _ _) = ⊥-elim (arith-not-cmp op a c)
  route-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) = ii-farith (route-ii d₁ d₁′) (route-ii d₂ d₂′)
  route-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₂ d₂′) λ { (() , _) })
  route-ii (t-binop-arith-float _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₂ d₂′) λ { (() , _) })
  route-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) = ii-il (route-ii d₁ d₁′) (route-ii d₂ d₂′)
  route-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₂ d₂′) λ { (() , _) })
  route-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₂ d₂′) λ { (() , _) })
  route-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) = ii-ir (route-ii d₁ d₁′) (route-ii d₂ d₂′)
  route-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-cmp {op = op} c _ _) (t-binop-arith a _ _) = ⊥-elim (arith-not-cmp op a c)
  route-ii (t-binop-cmp _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-cmp _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₂ d₂′) λ { (() , _) })
  route-ii (t-binop-cmp _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) = ⊥-elim (ex (agree-ii d₁ d₁′) λ { (() , _) })
  route-ii (t-binop-cmp _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) = ii-cmp (route-ii d₁ d₁′) (route-ii d₂ d₂′)
  route-ii (t-id-app d) (t-id-app d′) = ii-id-app (route-ii d d′)
  route-ii (t-fst-app d) (t-fst-app d′) = ii-fst-app (route-ii d d′)
  route-ii (t-snd-app d) (t-snd-app d′) = ii-snd-app (route-ii d d′)
  route-ii (t-terminal-app d) (t-terminal-app d′) = ii-terminal-app (route-ii d d′)
  route-ii (t-apply-app-infer d) (t-apply-app-infer d′) = ii-apply (route-ii d d′)
  route-ii (t-apply-app-infer d) (t-apply-eff-app-infer d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  route-ii (t-apply-eff-app-infer d) (t-apply-app-infer d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  route-ii (t-apply-eff-app-infer d) (t-apply-eff-app-infer d′) = ii-apply-eff (route-ii d d′)
  route-ii (t-Out-app-infer _ refl d) (t-Out-app-infer _ refl d′) = ii-Out (route-ii d d′)
  route-ii (t-Out-eff-app-infer _ refl d) (t-Out-eff-app-infer _ refl d′) = ii-Out-eff (route-ii d d′)
  route-ii (t-Out-eff-app-infer _ _ d) (t-Out-app-infer _ _ d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  route-ii (t-Out-app-infer _ _ d) (t-Out-eff-app-infer _ _ d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  route-ii (t-Out-eff-app-infer _ _ _) (t-app () _ _)
  route-ii (t-app () _ _) (t-Out-eff-app-infer _ _ _)
  route-ii (t-Out-eff-app-infer _ _ _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-Out-eff-app-infer _ _ _)
  route-ii (t-Out-eff-app-infer _ _ _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-Out-eff-app-infer _ _ _)
  route-ii (t-id-app _) (t-app () _ _)
  route-ii (t-app () _ _) (t-id-app _)
  route-ii (t-id-app _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-id-app _)
  route-ii (t-id-app _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-id-app _)
  route-ii (t-fst-app _) (t-app () _ _)
  route-ii (t-app () _ _) (t-fst-app _)
  route-ii (t-fst-app _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-fst-app _)
  route-ii (t-fst-app _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-fst-app _)
  route-ii (t-snd-app _) (t-app () _ _)
  route-ii (t-app () _ _) (t-snd-app _)
  route-ii (t-snd-app _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-snd-app _)
  route-ii (t-snd-app _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-snd-app _)
  route-ii (t-terminal-app _) (t-app () _ _)
  route-ii (t-app () _ _) (t-terminal-app _)
  route-ii (t-terminal-app _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-terminal-app _)
  route-ii (t-terminal-app _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-terminal-app _)
  route-ii (t-apply-app-infer _) (t-app () _ _)
  route-ii (t-app () _ _) (t-apply-app-infer _)
  route-ii (t-apply-app-infer _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-apply-app-infer _)
  route-ii (t-apply-app-infer _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-apply-app-infer _)
  route-ii (t-apply-eff-app-infer _) (t-app () _ _)
  route-ii (t-app () _ _) (t-apply-eff-app-infer _)
  route-ii (t-apply-eff-app-infer _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-apply-eff-app-infer _)
  route-ii (t-apply-eff-app-infer _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-apply-eff-app-infer _)
  route-ii (t-Out-app-infer _ _ _) (t-app () _ _)
  route-ii (t-app () _ _) (t-Out-app-infer _ _ _)
  route-ii (t-Out-app-infer _ _ _) (t-effApp () _ _)
  route-ii (t-effApp () _ _) (t-Out-app-infer _ _ _)
  route-ii (t-Out-app-infer _ _ _) (t-app-spine () _ _)
  route-ii (t-app-spine () _ _) (t-Out-app-infer _ _ _)
  route-ii (t-app h wF dX) (t-app h′ wF′ dX′) = app-r h wF dX h′ wF′ dX′ (proj₁ (agree-ii wF wF′))
  route-ii (t-app _ wF _) (t-effApp _ wF′ _) = ⊥-elim (ex (agree-ii wF wF′) λ { (() , _) })
  route-ii (t-effApp _ wF _) (t-app _ wF′ _) = ⊥-elim (ex (agree-ii wF wF′) λ { (() , _) })
  route-ii (t-effApp h wF dX) (t-effApp h′ wF′ dX′) = effApp-r h wF dX h′ wF′ dX′ (proj₁ (agree-ii wF wF′))
  route-ii (t-app _ wF dX) (t-app-spine _ dX′ dF′) = ii-app-spine (route-ic dX′ dX) (route-di dF′ wF)
  route-ii (t-app-spine _ dX dF) (t-app _ wF′ dX′) = ii-spine-app (route-ic dX dX′) (route-di dF wF′)
  route-ii (t-effApp _ wF _) (t-app-spine _ _ dF′) = ⊥-elim (ex (agree-di dF′ wF) λ { (_ , _ , refl , () , _) })
  route-ii (t-app-spine _ _ dF) (t-effApp _ wF′ _) = ⊥-elim (ex (agree-di dF wF′) λ { (_ , _ , refl , () , _) })
  route-ii (t-app-spine h dX dF) (t-app-spine h′ dX′ dF′) = spine-r h dX dF h′ dX′ dF′ (proj₁ (agree-ii dX dX′))
  route-cc (t-sub d _) c = cc-sub-l (route-ic d c)
  route-cc c (t-sub d _) = cc-sub-r (route-ic d c)
  route-cc t-id-check t-id-check = cc-id
  route-cc t-fst-check t-fst-check = cc-fst
  route-cc t-snd-check t-snd-check = cc-snd
  route-cc t-terminal-morph-check t-terminal-morph-check = cc-terminal
  route-cc t-initial-morph-check t-initial-morph-check = cc-initial
  route-cc t-inl-morph-check t-inl-morph-check = cc-inl
  route-cc t-inr-morph-check t-inr-morph-check = cc-inr
  route-cc (t-compose-check-g dg df) (t-compose-check-g dg′ df′) = gg-r dg df dg′ df′ (proj₁ (agree-dd dg dg′))
  route-cc (t-compose-check-g dg df) (t-compose-check-f wf _ dg′) = cc-gf (route-dc dg dg′) (route-ic wf df)
  route-cc (t-compose-check-f wf _ dg) (t-compose-check-g dg′ df′) = cc-fg (route-dc dg′ dg) (route-ic wf df′)
  route-cc (t-compose-check-f wf s dg) (t-compose-check-f wf′ s′ dg′) = ff-r wf s dg wf′ s′ dg′ (proj₁ (agree-ii wf wf′))
  route-cc (t-case-copair-check df dg) (t-case-copair-check df′ dg′) = cc-copair (route-cc df df′) (route-cc dg dg′)
  route-cc (t-pair-morph-check df dg) (t-pair-morph-check df′ dg′) = cc-fork (route-cc df df′) (route-cc dg dg′)
  route-cc (t-curry-check d) (t-curry-check d′) = cc-curry (route-cc d d′)
  route-cc (t-cata-check _ a) (t-cata-check _ a′) = cc-cata (route-cc a a′)
  route-cc (t-ana-check _ a) (t-ana-check _ a′) = cc-ana (route-cc a a′)
  route-cc (t-lam _ b) (t-lam _ b′) = cc-lam (route-cc b b′)
  route-cc (t-pair-lit-check a b) (t-pair-lit-check a′ b′) = cc-pair-lit (route-cc a a′) (route-cc b b′)
  route-cc (t-In-app-check _ d) (t-In-app-check _ d′) = cc-In (route-cc d d′)
  route-cc (t-apply-check d) (t-apply-check d′) = cc-apply (route-ii d d′)
  route-cc (t-inl-app-check d) (t-inl-app-check d′) = cc-inl-app (route-cc d d′)
  route-cc (t-inr-app-check d) (t-inr-app-check d′) = cc-inr-app (route-cc d d′)
  route-cc (t-initial-app-check d) (t-initial-app-check d′) = cc-initial-app (route-cc d d′)
  route-cc (t-var-poly-instantiate _ _ _ _ _) (t-var-poly-instantiate _ _ _ _ _) = cc-poly
  route-ic d (t-sub d′ _) = ic-sub (route-ii d d′)
  route-ic (t-pair a b) (t-pair-lit-check a′ b′) = ic-pair (route-ic a a′) (route-ic b b′)
  route-ic (t-apply-app-infer d) (t-apply-check d′) = ic-apply (route-ii d d′)
  route-ic (t-apply-eff-app-infer d) (t-apply-check d′) = ⊥-elim (ex (agree-ii d d′) λ { (() , _) })
  route-ic (t-app () _ _) (t-apply-check _)
  route-ic (t-effApp () _ _) (t-apply-check _)
  route-ic (t-app-spine () _ _) (t-apply-check _)
  route-ic (t-var-local l) (t-var-poly-instantiate ln _ _ _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  route-ic (t-var-import _ _ i _) (t-var-poly-instantiate _ inn _ _ _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  route-ic (t-var-poly-instantiate-infer _ _ p g _) (t-var-poly-instantiate _ _ p′ ¬g _) = ⊥-elim (ex (trans (sym p) p′) λ { refl → (¬g g) })
  route-ic () (t-lam _ _)
  route-ic d t-id-check = ⊥-elim (noinf-id d)
  route-ic d t-fst-check = ⊥-elim (noinf-fst d)
  route-ic d t-snd-check = ⊥-elim (noinf-snd d)
  route-ic d t-terminal-morph-check = ⊥-elim (noinf-terminal d)
  route-ic d t-initial-morph-check = ⊥-elim (noinf-initial d)
  route-ic d t-inl-morph-check = ⊥-elim (noinf-inl d)
  route-ic d t-inr-morph-check = ⊥-elim (noinf-inr d)
  route-ic d (t-compose-check-g _ _) = ⊥-elim (noinf-compose d)
  route-ic d (t-compose-check-f _ _ _) = ⊥-elim (noinf-compose d)
  route-ic d (t-case-copair-check _ _) = ⊥-elim (noinf-case d)
  route-ic d (t-pair-morph-check _ _) = ⊥-elim (noinf-pair d)
  route-ic d (t-curry-check _) = ⊥-elim (noinf-curry-app d)
  route-ic d (t-cata-check _ _) = ⊥-elim (noinf-cata-app d)
  route-ic d (t-ana-check _ _) = ⊥-elim (noinf-ana-app d)
  route-ic d (t-In-app-check _ _) = ⊥-elim (noinf-In-app d)
  route-ic d (t-inl-app-check _) = ⊥-elim (noinf-inl-app d)
  route-ic d (t-inr-app-check _) = ⊥-elim (noinf-inr-app d)
  route-ic d (t-initial-app-check _) = ⊥-elim (noinf-initial-app d)
  route-dc (d-infer w _ _) c = dc-infer (route-ic w c)
  route-dc dd (t-sub d p) = dcsub-r dd d p (agree-di dd d)
  route-dc (d-lam _ b) (t-lam _ b′) = dc-lam (route-ic b b′)
  route-dc (d-compose dg df) (t-compose-check-g dg′ df′) = cg-r dg df dg′ df′ (proj₁ (agree-dd dg dg′))
  route-dc (d-compose dg df) (t-compose-check-f wf _ dg′) = dc-cf (route-di df wf) (route-dc dg dg′)
  route-dc d-id t-id-check = dc-id
  route-dc d-fst t-fst-check = dc-fst
  route-dc d-snd t-snd-check = dc-snd
  route-dc d-terminal t-terminal-morph-check = dc-terminal
  route-dc d-initial t-initial-morph-check = dc-initial
  route-dc (d-case df dg) (t-case-copair-check df′ dg′) = dc-case (route-dc df df′) (route-dc dg dg′)
  route-dc (d-pair df dg) (t-pair-morph-check df′ dg′) = dc-pair (route-dc df df′) (route-dc dg dg′)
  route-dc (d-cata _ a) (t-cata-check _ a′) = dc-cata (route-ic a a′)
  route-dc (d-poly _ _ _ _ _ _ _ _) (t-var-poly-instantiate _ _ _ _ _) = dc-poly
  route-di (d-infer w _ _) d = di-infer (route-ii w d)
  route-di (d-lam _ _) ()
  route-di (d-compose _ _) d = ⊥-elim (noinf-compose d)
  route-di d-id d = ⊥-elim (noinf-id d)
  route-di d-fst d = ⊥-elim (noinf-fst d)
  route-di d-snd d = ⊥-elim (noinf-snd d)
  route-di d-terminal d = ⊥-elim (noinf-terminal d)
  route-di d-initial d = ⊥-elim (noinf-initial d)
  route-di (d-case _ _) d = ⊥-elim (noinf-case d)
  route-di (d-pair _ _) d = ⊥-elim (noinf-pair d)
  route-di (d-cata _ _) d = ⊥-elim (noinf-cata-app d)
  route-di (d-poly ln _ _ _ _ _ _ _) (t-var-local l) = ⊥-elim (just≢nothing (trans (sym l) ln))
  route-di (d-poly _ inn _ _ _ _ _ _) (t-var-import _ _ i _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  route-di (d-poly _ _ p ¬g _ _ _ _) (t-var-poly-instantiate-infer _ _ p′ g _) = ⊥-elim (ex (trans (sym p) p′) λ { refl → (¬g g) })
  route-dd (d-infer w _ _) dd′ = dd-infer-l (route-di dd′ w)
  route-dd dd (d-infer w _ _) = dd-infer-r (route-di dd w)
  route-dd (d-lam _ b) (d-lam _ b′) = dd-lam (route-ii b b′)
  route-dd (d-compose dg df) (d-compose dg′ df′) = comp-r dg df dg′ df′ (proj₁ (agree-dd dg dg′))
  route-dd d-id d-id = dd-id
  route-dd d-fst d-fst = dd-fst
  route-dd d-snd d-snd = dd-snd
  route-dd d-terminal d-terminal = dd-terminal
  route-dd d-initial d-initial = dd-initial
  route-dd (d-case df dg) (d-case df′ dg′) = dd-case (route-dd df df′) (route-dd dg dg′)
  route-dd (d-pair df dg) (d-pair df′ dg′) = dd-pair (route-dd df df′) (route-dd dg dg′)
  route-dd (d-cata _ a) (d-cata _ a′) = dd-cata (route-ii a a′)
  route-dd (d-poly _ _ _ _ _ _ _ _) (d-poly _ _ _ _ _ _ _ _) = dd-poly
