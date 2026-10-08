-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Route — HOW TWO DERIVATIONS OF ONE TERM RELATE
-- (plan 0.103, coherence).
--
-- A route between two derivations of the same judgment records, rule by
-- rule, which of the judgment's overlaps they took: the same rule (with
-- routes between the premises), or one of the genuine two-way choices —
-- `t-sub` against a direct check rule, `t-app` against the spine, `d-infer`
-- against a domain-given rule, the two compose-check routes. Both
-- derivations sit at the SAME indices: the route is built after
-- `ModeAgreement` has aligned them.
--
-- Two routes (as `ModeAgreement` has two pairs) per pair of modes:
--   Rii  infer/infer       Rcc  check/check       Ric  infer/check
--   Rdc  domain/check      Rdi  domain/infer      Rdd  domain/domain
--
-- Every pair of derivations of one judgment has a route (`route-*`, below,
-- the case split). Coherence (`Adequacy.Coherence`) is then a structural
-- induction on the route, with no case split of its own: the syntax of the
-- overlap is settled here, its meaning there.
------------------------------------------------------------------------

module Once.TypeCheck.Route where

open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Type as T using (Type; Int; Float; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; Purity; Quantity)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx; extendNamedCtx)
open import Once.TypeCheck.Judgment
import Once.Surface.Context as Surface

private
  variable
    ctx : NamedCtx
    e e₁ e₂ e₃ : RawExpr
    A A′ A₀ B B′ B₀ B₁ C C′ C₁ M M′ T T′ X X′ : Type
    π π′ π₀ : Purity
    q q′ : Quantity

------------------------------------------------------------------------
-- The routes
------------------------------------------------------------------------

mutual
  data Rii : ∀ {ctx e A A′ Ψ Ψ′} → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′ → Set where
    ii-int   : ∀ {n} → Rii {ctx} (t-int n) (t-int n)
    ii-float : ∀ {i f l p} → Rii {ctx} (t-float i f l p) (t-float i f l p)
    ii-unit  : Rii {ctx} t-unit t-unit
    ii-unit-var : Rii {ctx} t-unit-var t-unit-var
    ii-resolved : ∀ {cn n n′ l l′ c c′} → Rii {ctx} (t-var-resolved {cn = cn} {T = T} n l c) (t-var-resolved {T = T′} n′ l′ c′)
    ii-own : ∀ {x ns ns′ l l′ c c′} → Rii {ctx} (t-var-own {x = x} {T = T} ns l c) (t-var-own {T = T′} ns′ l′ c′)
    ii-qualified : ∀ {nm al l l′ c c′}
      → Rii {ctx} (t-var-qualified {name = nm} {alias = al} {T = T} l c) (t-var-qualified {T = T′} l′ c′)
    ii-local : ∀ {x Ψ Ψ′ eV eV′ l l′}
      → Rii {ctx} (t-var-local {x = x} {A = A} {Ψ = Ψ} {eV = eV} l) (t-var-local {A = A′} {Ψ = Ψ′} {eV = eV′} l′)
    ii-import : ∀ {x g g′ ln ln′ i i′ c c′} → Rii {ctx} (t-var-import {x = x} {T = T} g ln i c) (t-var-import {T = T′} g′ ln′ i′ c′)
    ii-poly-infer : ∀ {x s s′ b b′ pr pr′ g g′ ln ln′ li li′ p p′ gr gr′ eq eq′}
      → Rii {ctx} (t-var-poly-instantiate-infer {x = x} {T = T} {schema = s} {body = b} {prefix = pr} {g = g} ln li p gr eq)
                  (t-var-poly-instantiate-infer {T = T′} {schema = s′} {body = b′} {prefix = pr′} {g = g′} ln′ li′ p′ gr′ eq′)
    ii-annot : ∀ {Ψ Ψ′ r r′} {c : ctx ⊢ᶜ e ∶ T ⨾ Ψ} {c′ : ctx ⊢ᶜ e ∶ T ⨾ Ψ′} → Rcc c c′ → Rii (t-annot r c) (t-annot r′ c′)
    ii-pair : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {a : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁} {a′ : ctx ⊢ᵢ e₁ ∶ A′ ⨾ Ψ₁′} {b : ctx ⊢ᵢ e₂ ∶ B ⨾ Ψ₂} {b′ : ctx ⊢ᵢ e₂ ∶ B′ ⨾ Ψ₂′}
            → Rii a a′ → Rii b b′ → Rii (t-pair a b) (t-pair a′ b′)
    ii-neg : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ Int ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ Int ⨾ Ψ′} → Rii d d′ → Rii (t-neg d) (t-neg d′)
    ii-neg-float : ∀ {i f l p} → Rii {ctx} (t-neg-float i f l p) (t-neg-float i f l p)
    ii-let : ∀ {x Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {d₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁′}
               {d₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B ⨾ (q Surface.Usage.∷ Ψ₂)} {d₂′ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B′ ⨾ (q′ Surface.Usage.∷ Ψ₂′)}
           → Rii d₁ d₁′ → Rii d₂ d₂′ → Rii (t-let d₁ d₂) (t-let d₁′ d₂′)
    ii-case : ∀ {xL xR qL qL′ qR qR′ Ψs Ψs′ Ψl Ψl′ Ψr Ψr′} {s : ctx ⊢ᵢ e₁ ∶ (A + B) ⨾ Ψs} {s′ : ctx ⊢ᵢ e₁ ∶ (A + B) ⨾ Ψs′}
                {l : extendNamedCtx ctx xL A ⊢ᵢ e₂ ∶ C ⨾ (qL Surface.Usage.∷ Ψl)} {l′ : extendNamedCtx ctx xL A ⊢ᵢ e₂ ∶ C′ ⨾ (qL′ Surface.Usage.∷ Ψl′)}
                {r : extendNamedCtx ctx xR B ⊢ᵢ e₃ ∶ C ⨾ (qR Surface.Usage.∷ Ψr)} {r′ : extendNamedCtx ctx xR B ⊢ᵢ e₃ ∶ C′ ⨾ (qR′ Surface.Usage.∷ Ψr′)}
            → Rii s s′ → Rii l l′ → Rii r r′ → Rii (t-case s l r) (t-case s′ l′ r′)
    ii-arith : ∀ {op a a′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {d₁ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂′}
             → Rii d₁ d₁′ → Rii d₂ d₂′ → Rii (t-binop-arith {op = op} a d₁ d₂) (t-binop-arith a′ d₁′ d₂′)
    ii-farith : ∀ {op a a′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {d₁ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂′}
              → Rii d₁ d₁′ → Rii d₂ d₂′ → Rii (t-binop-arith-float {op = op} a d₁ d₂) (t-binop-arith-float a′ d₁′ d₂′)
    ii-il : ∀ {op a a′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {d₁ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Float ⨾ Ψ₂′}
          → Rii d₁ d₁′ → Rii d₂ d₂′ → Rii (t-binop-arith-float-il {op = op} a d₁ d₂) (t-binop-arith-float-il a′ d₁′ d₂′)
    ii-ir : ∀ {op a a′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {d₁ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Float ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂′}
          → Rii d₁ d₁′ → Rii d₂ d₂′ → Rii (t-binop-arith-float-ir {op = op} a d₁ d₂) (t-binop-arith-float-ir a′ d₁′ d₂′)
    ii-cmp : ∀ {op a a′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {d₁ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁} {d₁′ : ctx ⊢ᵢ e₁ ∶ Int ⨾ Ψ₁′} {d₂ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂} {d₂′ : ctx ⊢ᵢ e₂ ∶ Int ⨾ Ψ₂′}
           → Rii d₁ d₁′ → Rii d₂ d₂′ → Rii (t-binop-cmp {op = op} a d₁ d₂) (t-binop-cmp a′ d₁′ d₂′)
    ii-id-app : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′} → Rii d d′ → Rii (t-id-app d) (t-id-app d′)
    ii-fst-app : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ (A * B) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ (A′ * B′) ⨾ Ψ′} → Rii d d′ → Rii (t-fst-app d) (t-fst-app d′)
    ii-snd-app : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ (A * B) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ (A′ * B′) ⨾ Ψ′} → Rii d d′ → Rii (t-snd-app d) (t-snd-app d′)
    ii-terminal-app : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′} → Rii d d′ → Rii (t-terminal-app d) (t-terminal-app d′)
    ii-apply : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ T.mk-kind T.Many T.pure ] B) * A) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ T.mk-kind T.Many T.pure ] B′) * A′) ⨾ Ψ′}
             → Rii d d′ → Rii (t-apply-app-infer d) (t-apply-app-infer d′)
    ii-apply-eff : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ T.mk-kind T.Many T.eff ] B) * A) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ T.mk-kind T.Many T.eff ] B′) * A′) ⨾ Ψ′}
                 → Rii d d′ → Rii (t-apply-eff-app-infer d) (t-apply-eff-app-infer d′)
    ii-Out : ∀ {F F′ w w′ Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ ν-type F T.pure ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ν-type F′ T.pure ⨾ Ψ′}
           → Rii d d′ → Rii (t-Out-app-infer w refl d) (t-Out-app-infer w′ refl d′)
    ii-Out-eff : ∀ {F F′ w w′ Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ ν-type F T.eff ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ν-type F′ T.eff ⨾ Ψ′}
               → Rii d d′ → Rii (t-Out-eff-app-infer w refl d) (t-Out-eff-app-infer w′ refl d′)
    -- `t-app` / `t-effApp`: the argument is CHECKED at the head's domain, so the
    -- two heads' types are aligned (the argument's context does not depend on it,
    -- but the check type does).
    ii-app : ∀ {h h′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {f : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind q T.pure ] B) ⨾ Ψ₁} {f′ : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind q T.pure ] B) ⨾ Ψ₁′}
               {x : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂} {x′ : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂′}
           → Rii f f′ → Rcc x x′ → Rii (t-app h f x) (t-app h′ f′ x′)
    ii-effApp : ∀ {h h′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {f : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind T.Many T.eff ] B) ⨾ Ψ₁} {f′ : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind T.Many T.eff ] B) ⨾ Ψ₁′}
                  {x : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂} {x′ : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂′}
              → Rii f f′ → Rcc x x′ → Rii (t-effApp h f x) (t-effApp h′ f′ x′)
    ii-app-spine : ∀ {h h′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {wF : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind q T.pure ] B) ⨾ Ψ₁} {dX : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂}
                     {dX′ : ctx ⊢ᵢ e₂ ∶ X ⨾ Ψ₂′} {dF′ : ctx ⊢ᵈ e₁ ∶ X ⇒[ T.pure ]↦ T ⨾ Ψ₁′}
                 → Ric dX′ dX → Rdi dF′ wF → Rii (t-app h wF dX) (t-app-spine h′ dX′ dF′)
    ii-spine-app : ∀ {h h′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {wF : ctx ⊢ᵢ e₁ ∶ (A ⇒[ T.mk-kind q T.pure ] B) ⨾ Ψ₁} {dX : ctx ⊢ᶜ e₂ ∶ A ⨾ Ψ₂}
                     {dX′ : ctx ⊢ᵢ e₂ ∶ X ⨾ Ψ₂′} {dF′ : ctx ⊢ᵈ e₁ ∶ X ⇒[ T.pure ]↦ T ⨾ Ψ₁′}
                 → Ric dX′ dX → Rdi dF′ wF → Rii (t-app-spine h′ dX′ dF′) (t-app h wF dX)
    -- The spine: the head is domain-given at the argument's type, aligned.
    ii-spine : ∀ {h h′ Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {dX : ctx ⊢ᵢ e₂ ∶ X ⨾ Ψ₂} {dX′ : ctx ⊢ᵢ e₂ ∶ X ⨾ Ψ₂′}
                 {dF : ctx ⊢ᵈ e₁ ∶ X ⇒[ T.pure ]↦ T ⨾ Ψ₁} {dF′ : ctx ⊢ᵈ e₁ ∶ X ⇒[ T.pure ]↦ T′ ⨾ Ψ₁′}
             → Rii dX dX′ → Rdd dF dF′ → Rii (t-app-spine h dX dF) (t-app-spine h′ dX′ dF′)

  data Rcc : ∀ {ctx e A Ψ Ψ′} → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ A ⨾ Ψ′ → Set where
    cc-sub-l : ∀ {Ψ Ψ′ p} {d : ctx ⊢ᵢ e ∶ A₀ ⨾ Ψ} {c : ctx ⊢ᶜ e ∶ A ⨾ Ψ′} → Ric d c → Rcc (t-sub d p) c
    cc-sub-r : ∀ {Ψ Ψ′ p} {d : ctx ⊢ᵢ e ∶ A₀ ⨾ Ψ′} {c : ctx ⊢ᶜ e ∶ A ⨾ Ψ} → Ric d c → Rcc c (t-sub d p)
    cc-id : Rcc {ctx} (t-id-check {T = A} {π = π}) t-id-check
    cc-fst : Rcc {ctx} (t-fst-check {A = A} {B = B} {π = π}) t-fst-check
    cc-snd : Rcc {ctx} (t-snd-check {A = A} {B = B} {π = π}) t-snd-check
    cc-terminal : Rcc {ctx} (t-terminal-morph-check {A = A} {π = π}) t-terminal-morph-check
    cc-initial : Rcc {ctx} (t-initial-morph-check {A = A} {π = π}) t-initial-morph-check
    cc-inl : Rcc {ctx} (t-inl-morph-check {A = A} {B = B} {π = π}) t-inl-morph-check
    cc-inr : Rcc {ctx} (t-inr-morph-check {A = A} {B = B} {π = π}) t-inr-morph-check
    -- Both `g` routes: the outer arm is checked at the middle `g` determines, aligned.
    cc-gg : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ B ⨾ Ψ₂} {dg′ : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ B ⨾ Ψ₂′}
              {df : ctx ⊢ᶜ e₁ ∶ (B ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁} {df′ : ctx ⊢ᶜ e₁ ∶ (B ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁′}
          → Rdd dg dg′ → Rcc df df′ → Rcc (t-compose-check-g dg df) (t-compose-check-g dg′ df′)
    cc-gf : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ s} {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ B ⨾ Ψ₂} {df : ctx ⊢ᶜ e₁ ∶ (B ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁}
              {wf : ctx ⊢ᵢ e₁ ∶ (B′ ⇒[ T.mk-kind T.Many π′ ] C′) ⨾ Ψ₁′} {dg′ : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ₂′}
          → Rdc dg dg′ → Ric wf df → Rcc (t-compose-check-g dg df) (t-compose-check-f wf s dg′)
    cc-fg : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ s} {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ B ⨾ Ψ₂} {df : ctx ⊢ᶜ e₁ ∶ (B ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁}
              {wf : ctx ⊢ᵢ e₁ ∶ (B′ ⇒[ T.mk-kind T.Many π′ ] C′) ⨾ Ψ₁′} {dg′ : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ₂′}
          → Rdc dg dg′ → Ric wf df → Rcc (t-compose-check-f wf s dg′) (t-compose-check-g dg df)
    -- Both `f` routes: the inner arm is checked at the middle `f` synthesizes, aligned.
    cc-ff : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ s s′} {wf : ctx ⊢ᵢ e₁ ∶ (B ⇒[ T.mk-kind T.Many π′ ] C′) ⨾ Ψ₁} {wf′ : ctx ⊢ᵢ e₁ ∶ (B ⇒[ T.mk-kind T.Many π′ ] C′) ⨾ Ψ₁′}
              {dg : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] B) ⨾ Ψ₂} {dg′ : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] B) ⨾ Ψ₂′}
          → Rii wf wf′ → Rcc dg dg′ → Rcc (t-compose-check-f {C = C} wf s dg) (t-compose-check-f wf′ s′ dg′)
    cc-copair : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {df : ctx ⊢ᶜ e₁ ∶ (A ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁} {df′ : ctx ⊢ᶜ e₁ ∶ (A ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₁′}
                  {dg : ctx ⊢ᶜ e₂ ∶ (B ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₂} {dg′ : ctx ⊢ᶜ e₂ ∶ (B ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₂′}
              → Rcc df df′ → Rcc dg dg′ → Rcc (t-case-copair-check df dg) (t-case-copair-check df′ dg′)
    cc-fork : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {df : ctx ⊢ᶜ e₁ ∶ (A ⇒[ T.mk-kind T.Many π ] B) ⨾ Ψ₁} {df′ : ctx ⊢ᶜ e₁ ∶ (A ⇒[ T.mk-kind T.Many π ] B) ⨾ Ψ₁′}
                {dg : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₂} {dg′ : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ₂′}
            → Rcc df df′ → Rcc dg dg′ → Rcc (t-pair-morph-check df dg) (t-pair-morph-check df′ dg′)
    cc-curry : ∀ {Ψ Ψ′} {d : ctx ⊢ᶜ e ∶ ((A * B) ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ ((A * B) ⇒[ T.mk-kind T.Many π ] C) ⨾ Ψ′}
             → Rcc d d′ → Rcc (t-curry-check {π₀ = π₀} d) (t-curry-check d′)
    cc-cata : ∀ {F w w′ Ψ Ψ′} {a : ctx ⊢ᶜ e ∶ ((T.⟦ F ⟧T A) ⇒[ T.mk-kind T.Many π ] A) ⨾ Ψ}
                {a′ : ctx ⊢ᶜ e ∶ ((T.⟦ F ⟧T A) ⇒[ T.mk-kind T.Many π ] A) ⨾ Ψ′}
            → Rcc a a′ → Rcc (t-cata-check {ctx = ctx} {F = F} w a) (t-cata-check {F = F} w′ a′)
    cc-ana : ∀ {F w w′ Ψ Ψ′} {a : ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] (T.⟦ F ⟧T A)) ⨾ Ψ}
               {a′ : ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] (T.⟦ F ⟧T A)) ⨾ Ψ′}
           → Rcc a a′ → Rcc (t-ana-check {ctx = ctx} {F = F} {π₀ = π₀} w a) (t-ana-check {F = F} w′ a′)
    cc-lam : ∀ {x q₁ q₁′ Ψ Ψ′ ≤p ≤p′} {b : extendNamedCtx ctx x A ⊢ᶜ e ∶ B ⨾ (q₁ Surface.Usage.∷ Ψ)}
               {b′ : extendNamedCtx ctx x A ⊢ᶜ e ∶ B ⨾ (q₁′ Surface.Usage.∷ Ψ′)}
           → Rcc b b′ → Rcc (t-lam {q = q} {π = π} ≤p b) (t-lam ≤p′ b′)
    cc-pair-lit : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {a : ctx ⊢ᶜ e₁ ∶ A ⨾ Ψ₁} {a′ : ctx ⊢ᶜ e₁ ∶ A ⨾ Ψ₁′} {b : ctx ⊢ᶜ e₂ ∶ B ⨾ Ψ₂} {b′ : ctx ⊢ᶜ e₂ ∶ B ⨾ Ψ₂′}
                → Rcc a a′ → Rcc b b′ → Rcc (t-pair-lit-check a b) (t-pair-lit-check a′ b′)
    cc-In : ∀ {F w w′ Ψ Ψ′} {d : ctx ⊢ᶜ e ∶ T.⟦ F ⟧T (μ-type F) ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ T.⟦ F ⟧T (μ-type F) ⨾ Ψ′}
          → Rcc d d′ → Rcc (t-In-app-check {F = F} w d) (t-In-app-check {F = F} w′ d′)
    cc-apply : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ T.mk-kind T.Many T.pure ] B) * A) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ T.mk-kind T.Many T.pure ] B) * A′) ⨾ Ψ′}
             → Rii d d′ → Rcc (t-apply-check d) (t-apply-check d′)
    cc-inl-app : ∀ {Ψ Ψ′} {d : ctx ⊢ᶜ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ A ⨾ Ψ′} → Rcc d d′ → Rcc (t-inl-app-check {B = B} d) (t-inl-app-check d′)
    cc-inr-app : ∀ {Ψ Ψ′} {d : ctx ⊢ᶜ e ∶ B ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ B ⨾ Ψ′} → Rcc d d′ → Rcc (t-inr-app-check {A = A} d) (t-inr-app-check d′)
    cc-initial-app : ∀ {Ψ Ψ′} {d : ctx ⊢ᶜ e ∶ Void ⨾ Ψ} {d′ : ctx ⊢ᶜ e ∶ Void ⨾ Ψ′} → Rcc d d′ → Rcc (t-initial-app-check {T = A} d) (t-initial-app-check d′)
    cc-poly : ∀ {x s s′ b b′ pr pr′ ln ln′ li li′ p p′ g g′ k k′}
      → Rcc {ctx} (t-var-poly-instantiate {x = x} {T = A} {schema = s} {body = b} {prefix = pr} ln li p g k)
                  (t-var-poly-instantiate {schema = s′} {body = b′} {prefix = pr′} ln′ li′ p′ g′ k′)

  data Ric : ∀ {ctx e A B Ψ Ψ′} → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → Set where
    ic-sub : ∀ {Ψ Ψ′ p} {d : ctx ⊢ᵢ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′} → Rii d d′ → Ric d (t-sub {B = B} d′ p)
    ic-pair : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {a : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁} {a′ : ctx ⊢ᶜ e₁ ∶ A′ ⨾ Ψ₁′} {b : ctx ⊢ᵢ e₂ ∶ B ⨾ Ψ₂} {b′ : ctx ⊢ᶜ e₂ ∶ B′ ⨾ Ψ₂′}
            → Ric a a′ → Ric b b′ → Ric (t-pair a b) (t-pair-lit-check a′ b′)
    ic-apply : ∀ {Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ ((A ⇒[ T.mk-kind T.Many T.pure ] B) * A) ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ ((A′ ⇒[ T.mk-kind T.Many T.pure ] B′) * A′) ⨾ Ψ′}
             → Rii d d′ → Ric (t-apply-app-infer d) (t-apply-check d′)

  data Rdc : ∀ {ctx e A B B′ π Ψ Ψ′} → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′ → Set where
    dc-infer : ∀ {Ψ Ψ′ a g} {w : ctx ⊢ᵢ e ∶ (A₀ ⇒[ T.mk-kind T.Many π₀ ] B) ⨾ Ψ} {c : ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′}
             → Ric w c → Rdc (d-infer w a g) c
    -- The check is a conversion of a synthesis; its type is the arrow `d-infer` reads, aligned.
    dc-sub : ∀ {Ψ Ψ′ p} {dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ} {d : ctx ⊢ᵢ e ∶ (A₀ ⇒[ T.mk-kind T.Many π₀ ] B) ⨾ Ψ′}
           → Rdi dd d → Rdc {B′ = B′} dd (t-sub d p)
    dc-lam : ∀ {x q₁ q₁′ Ψ Ψ′ ≤p ≤p′} {b : extendNamedCtx ctx x A ⊢ᵢ e ∶ B ⨾ (q₁ Surface.Usage.∷ Ψ)}
               {b′ : extendNamedCtx ctx x A ⊢ᶜ e ∶ B′ ⨾ (q₁′ Surface.Usage.∷ Ψ′)}
           → Ric b b′ → Rdc (d-lam {π = π} ≤p b) (t-lam ≤p′ b′)
    -- `d-compose` against the `g` route: the outer arm's domain is aligned.
    dc-cg : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M ⨾ Ψ₂} {dg′ : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M ⨾ Ψ₂′}
              {df : ctx ⊢ᵈ e₁ ∶ M ⇒[ π ]↦ B ⨾ Ψ₁} {df′ : ctx ⊢ᶜ e₁ ∶ (M ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ₁′}
          → Rdd dg dg′ → Rdc df df′ → Rdc (d-compose dg df) (t-compose-check-g dg′ df′)
    dc-cf : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ s} {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M ⨾ Ψ₂} {df : ctx ⊢ᵈ e₁ ∶ M ⇒[ π ]↦ B ⨾ Ψ₁}
              {wf : ctx ⊢ᵢ e₁ ∶ (A′ ⇒[ T.mk-kind T.Many π′ ] C′) ⨾ Ψ₁′} {dg′ : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] A′) ⨾ Ψ₂′}
          → Rdi df wf → Rdc dg dg′ → Rdc {B′ = B′} (d-compose dg df) (t-compose-check-f wf s dg′)
    dc-id : Rdc {ctx} (d-id {A = A} {π = π}) t-id-check
    dc-fst : Rdc {ctx} (d-fst {A = A} {B = B} {π = π}) t-fst-check
    dc-snd : Rdc {ctx} (d-snd {A = A} {B = B} {π = π}) t-snd-check
    dc-terminal : Rdc {ctx} (d-terminal {A = A} {π = π}) t-terminal-morph-check
    dc-initial : Rdc {ctx} (d-initial {π = π}) (t-initial-morph-check {A = A})
    dc-case : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {df : ctx ⊢ᵈ e₁ ∶ A ⇒[ π ]↦ C ⨾ Ψ₁} {df′ : ctx ⊢ᶜ e₁ ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ₁′}
                {dg : ctx ⊢ᵈ e₂ ∶ B ⇒[ π ]↦ C ⨾ Ψ₂} {dg′ : ctx ⊢ᶜ e₂ ∶ (B ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ₂′}
            → Rdc df df′ → Rdc dg dg′ → Rdc (d-case df dg) (t-case-copair-check df′ dg′)
    dc-pair : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {df : ctx ⊢ᵈ e₁ ∶ A ⇒[ π ]↦ B ⨾ Ψ₁} {df′ : ctx ⊢ᶜ e₁ ∶ (A ⇒[ T.mk-kind T.Many π ] B₁) ⨾ Ψ₁′}
                {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ C ⨾ Ψ₂} {dg′ : ctx ⊢ᶜ e₂ ∶ (A ⇒[ T.mk-kind T.Many π ] C₁) ⨾ Ψ₂′}
            → Rdc df df′ → Rdc dg dg′ → Rdc (d-pair df dg) (t-pair-morph-check df′ dg′)
    dc-cata : ∀ {F w w′ Ψ Ψ′} {a : ctx ⊢ᵢ e ∶ ((T.⟦ F ⟧T A) ⇒[ T.mk-kind T.Many π ] A) ⨾ Ψ}
                {a′ : ctx ⊢ᶜ e ∶ ((T.⟦ F ⟧T A′) ⇒[ T.mk-kind T.Many π ] A′) ⨾ Ψ′}
            → Ric a a′ → Rdc (d-cata {ctx = ctx} {F = F} w a) (t-cata-check {F = F} w′ a′)
    dc-poly : ∀ {x s s′ sd sc b b′ pr pr′ ln ln′ li li′ p p′ g g′ as ki ki′ gr} {inc : T.CodVarsInDom sd sc}
      → Rdc {ctx} (d-poly {x = x} {A = A} {B = B} {π = π} {π′ = π′} {schema = s} {sd = sd} {sc = sc} {body = b} {prefix = pr}
                          ln li p g as inc ki gr)
                  (t-var-poly-instantiate {T = A ⇒[ T.mk-kind T.Many π ] B′} {schema = s′} {body = b′} {prefix = pr′} ln′ li′ p′ g′ ki′)

  -- A domain-given derivation of a term that also synthesizes an arrow.
  data Rdi : ∀ {ctx e A A′ B B′ π q π′ Ψ Ψ′} → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵢ e ∶ (A′ ⇒[ T.mk-kind q π′ ] B′) ⨾ Ψ′ → Set where
    di-infer : ∀ {Ψ Ψ′ a g} {w : ctx ⊢ᵢ e ∶ (A₀ ⇒[ T.mk-kind T.Many π₀ ] B) ⨾ Ψ} {d : ctx ⊢ᵢ e ∶ (A′ ⇒[ T.mk-kind q π′ ] B′) ⨾ Ψ′}
             → Rii w d → Rdi (d-infer {A = A} {π = π} w a g) d

  data Rdd : ∀ {ctx e A B B′ π Ψ Ψ′} → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′ → Set where
    dd-infer-l : ∀ {Ψ Ψ′ a g} {w : ctx ⊢ᵢ e ∶ (A₀ ⇒[ T.mk-kind T.Many π₀ ] B) ⨾ Ψ} {dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′}
               → Rdi dd w → Rdd (d-infer w a g) dd
    dd-infer-r : ∀ {Ψ Ψ′ a g} {w : ctx ⊢ᵢ e ∶ (A₀ ⇒[ T.mk-kind T.Many π₀ ] B′) ⨾ Ψ′} {dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ}
               → Rdi dd w → Rdd dd (d-infer w a g)
    dd-lam : ∀ {x q₁ q₁′ Ψ Ψ′ ≤p ≤p′} {b : extendNamedCtx ctx x A ⊢ᵢ e ∶ B ⨾ (q₁ Surface.Usage.∷ Ψ)}
               {b′ : extendNamedCtx ctx x A ⊢ᵢ e ∶ B′ ⨾ (q₁′ Surface.Usage.∷ Ψ′)}
           → Rii b b′ → Rdd (d-lam {π = π} ≤p b) (d-lam ≤p′ b′)
    -- The outer half is domain-given at the middle the inner half determines, aligned.
    dd-compose : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M ⨾ Ψ₂} {dg′ : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ M ⨾ Ψ₂′}
                   {df : ctx ⊢ᵈ e₁ ∶ M ⇒[ π ]↦ B ⨾ Ψ₁} {df′ : ctx ⊢ᵈ e₁ ∶ M ⇒[ π ]↦ B′ ⨾ Ψ₁′}
               → Rdd dg dg′ → Rdd df df′ → Rdd (d-compose dg df) (d-compose dg′ df′)
    dd-id : Rdd {ctx} (d-id {A = A} {π = π}) d-id
    dd-fst : Rdd {ctx} (d-fst {A = A} {B = B} {π = π}) d-fst
    dd-snd : Rdd {ctx} (d-snd {A = A} {B = B} {π = π}) d-snd
    dd-terminal : Rdd {ctx} (d-terminal {A = A} {π = π}) d-terminal
    dd-initial : Rdd {ctx} (d-initial {π = π}) d-initial
    dd-case : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {df : ctx ⊢ᵈ e₁ ∶ A ⇒[ π ]↦ C ⨾ Ψ₁} {df′ : ctx ⊢ᵈ e₁ ∶ A ⇒[ π ]↦ C′ ⨾ Ψ₁′}
                {dg : ctx ⊢ᵈ e₂ ∶ B ⇒[ π ]↦ C ⨾ Ψ₂} {dg′ : ctx ⊢ᵈ e₂ ∶ B ⇒[ π ]↦ C′ ⨾ Ψ₂′}
            → Rdd df df′ → Rdd dg dg′ → Rdd (d-case df dg) (d-case df′ dg′)
    dd-pair : ∀ {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′} {df : ctx ⊢ᵈ e₁ ∶ A ⇒[ π ]↦ B ⨾ Ψ₁} {df′ : ctx ⊢ᵈ e₁ ∶ A ⇒[ π ]↦ B′ ⨾ Ψ₁′}
                {dg : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ C ⨾ Ψ₂} {dg′ : ctx ⊢ᵈ e₂ ∶ A ⇒[ π ]↦ C′ ⨾ Ψ₂′}
            → Rdd df df′ → Rdd dg dg′ → Rdd (d-pair df dg) (d-pair df′ dg′)
    dd-cata : ∀ {F w w′ Ψ Ψ′} {a : ctx ⊢ᵢ e ∶ ((T.⟦ F ⟧T A) ⇒[ T.mk-kind T.Many π ] A) ⨾ Ψ}
                {a′ : ctx ⊢ᵢ e ∶ ((T.⟦ F ⟧T A′) ⇒[ T.mk-kind T.Many π ] A′) ⨾ Ψ′}
            → Rii a a′ → Rdd (d-cata {ctx = ctx} {F = F} w a) (d-cata {F = F} w′ a′)
    dd-poly : ∀ {x s s′ sd sc sd′ sc′ b b′ pr pr′ ln ln′ li li′ p p′ g g′ as as′ ki ki′ gr gr′}
                {inc : T.CodVarsInDom sd sc} {inc′ : T.CodVarsInDom sd′ sc′}
      → Rdd {ctx} (d-poly {x = x} {A = A} {B = B} {π = π} {π′ = π′} {schema = s} {sd = sd} {sc = sc} {body = b} {prefix = pr}
                          ln li p g as inc ki gr)
                  (d-poly {B = B′} {π′ = π₀} {schema = s′} {sd = sd′} {sc = sc′} {body = b′} {prefix = pr′} ln′ li′ p′ g′ as′ inc′ ki′ gr′)
