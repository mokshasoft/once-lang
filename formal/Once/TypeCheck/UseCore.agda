-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.UseCore — the core term an annotated derivation names is
-- typed at its usage (plan 0.122 §2b-3).
--
-- The Spec's surface rule names the core term; `Use` says how many times the
-- expression uses each local. The term is then typed by the core judgment at
-- that usage and at grade `pure` (a surface expression's effects live on its
-- arrows), rule by rule: a combinator by its `Derived` typing, an applied
-- generator as the closed definition applied, arithmetic by the saturated
-- primitive, a reference by the table's entry or the signature's declaration.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx; Type)

module Once.TypeCheck.UseCore (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set) {m : ℕ} (Δ : KCtx m) where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (mk-kind; Many; pure; ⊑-pure)
open import Once.Spec.Type using (Ty; TySub; _⇒[_]_; Respects; _⟨_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.Spec.Core.Syntax using (num; p-i2f; prim; pair; ref)
open import Once.Spec.Theory using (NumTy; int; float; ⌜_⌝ⁿ; symDom; symCod; ‵neg; float-rounded)
open import Once.TypeCheck.NumTableAgree Σ S nm using (binDom; mixedDom)
open import Once.Spec.Context using (Ctx; _+ᵘ_; zeroUsage)
open import Once.Spec.Type using (Int; Float; Unit; _+_)
open import Once.Spec.Sub using (sub-arr; _⊔_≔_)
open _⊔_≔_ using (left; right)
open import Once.Spec.Core.Syntax using (module Schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Core.DerivedTyping Σ S
open import Once.Type.Sub using (·p-diag; pure-⊑; <:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Type.Grade using (≤q-Many; ≤qᵇ→≤q)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals; binSym; asFloat)
open SU.BinSym using (symbol; shape)
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ

-- An entry with no type variables respects any kinds.
no-kinds : ∀ (d : Fin s) (τ : TySub (arity (S !! d)) m) → arity (S !! d) ≡ 0 → Respects (kinds (S !! d)) Δ τ
no-kinds d τ a i = ⊥-elim (fin0 (subst Fin a i))
  where fin0 : Fin 0 → ⊥
        fin0 ()

private

  -- A binary symbol's primitive, on the pair of its operands.
  bin : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ t₁ t₂} op (A : NumTy) (h : _)
      → Δ ⊩ Γ ⊢[ Ψ₁ ] t₁ ∷ ⌜ A ⌝ⁿ ! pure → Δ ⊩ Γ ⊢[ Ψ₂ ] t₂ ∷ ⌜ A ⌝ⁿ ! pure
      → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] prim (num {A} h (symbol (binSym op))) (pair t₁ t₂) ∷ symCod A (shape (binSym op)) ! pure
  bin op A h d e = ⊢prim (num h (symbol (binSym op))) (subst (λ X → Δ ⊩ _ ⊢[ _ ] _ ∷ X ! pure) (sym (binDom op A)) (⊢pair d e))

  -- A mixed operand, widened.
  widen : ∀ {n} {Γ : Ctx m n} {Ψ t} (a : NumTy) → Δ ⊩ Γ ⊢[ Ψ ] t ∷ ⌜ a ⌝ⁿ ! pure → Δ ⊩ Γ ⊢[ Ψ ] asFloat a t ∷ Float ! pure
  widen int   d = ⊢prim p-i2f d
  widen float d = d

-- A polymorphic arrow's instance, from its domain and codomain's.
poly-inst : ∀ (d : Fin s) (τ : TySub (arity (S !! d)) m) {sd sc A B π′}
          → type (S !! d) ≡ sd ⇒[ mk-kind Many π′ ] sc → sd ⟨ τ ⟩ ≡ A → sc ⟨ τ ⟩ ≡ B
          → type (S !! d) ⟨ τ ⟩ ≡ A ⇒[ mk-kind Many π′ ] B
poly-inst d τ ty ea eb = trans (cong (_⟨ τ ⟩) ty) (cong₂ (λ X Y → X ⇒[ mk-kind Many _ ] Y) ea eb)

-- In a context of the locals' shape (`typ` at their own context, below).
typS⇒ : ∀ {n} {L : Locals m n} {Γ} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Shape L Γ → Use⇒ d Ψ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! pure
typS⇐ : ∀ {n} {L : Locals m n} {Γ} {e A t Ψ} {d : L ⊢ e ⇐ A ↝ t} → Shape L Γ → Use⇐ d Ψ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! pure
typS↦ : ∀ {n} {L : Locals m n} {Γ} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Shape L Γ → Use↦ d Ψ
      → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ⇒[ mk-kind Many π ] B ! pure

typS⇒ sh u-int                       = ⊢lit-int
typS⇒ sh u-float                     = ⊢lit-float
typS⇒ sh u-unit                      = ⊢unit
typS⇒ sh u-unit-g                    = ⊢unit
typS⇒ sh (u-var {v = v})             = subst (λ X → Δ ⊩ _ ⊢[ _ ] _ ∷ X ! pure) (lookup-shape sh v) (⊢var _)
typS⇒ sh (u-sigop {mem = mem} k h)   = ⊢sigop mem
typS⇒ sh (u-def {d = d} {τ = τ} {a = a}) = ⊢ref d τ (no-kinds d τ a)
typS⇒ sh (u-annot u)                 = typS⇐ sh u
typS⇒ sh (u-pair ua ub)              = ⊢pair (typS⇒ sh ua) (typS⇒ sh ub)
typS⇒ sh (u-neg {h = h} u)           = ⊢prim (num h ‵neg) (typS⇒ sh u)
typS⇒ sh (u-let {q = q} u₁ u₂)       = ⊢let-pure q (typS⇒ sh u₁) (typS⇒ (sh-▸ sh) u₂)
-- Each branch composed with its conversion into the join (D322).
typS⇒ sh (u-case {j = j} us ul ur)   =
  ⊢case⊔ (typS⇒ sh us) (⊢coerce (<:ᶜ⇒<: (left j)) (typS⇒ (sh-▸ sh) ul)) (⊢coerce (<:ᶜ⇒<: (right j)) (typS⇒ (sh-▸ sh) ur))
typS⇒ sh (u-binop {op = op} {A = A} {h = h} u₁ u₂) = bin op A h (typS⇒ sh u₁) (typS⇒ sh u₂)
typS⇒ sh (u-binop-mixed {op = op} {k = k} {o = o} {a₁ = a₁} {a₂ = a₂} {eq = eq} u₁ u₂) =
  ⊢prim (num float-rounded o) (subst (λ X → Δ ⊩ _ ⊢[ _ ] _ ∷ X ! pure) (sym (mixedDom eq)) (⊢pair (widen a₁ (typS⇒ sh u₁)) (widen a₂ (typS⇒ sh u₂))))
typS⇒ sh (u-id-app u)                = ⊢app (⊢idᶜ ⊑-pure) (typS⇒ sh u)
typS⇒ sh (u-fst-app u)               = ⊢app (⊢fstᶜ ⊑-pure) (typS⇒ sh u)
typS⇒ sh (u-snd-app u)               = ⊢app (⊢sndᶜ ⊑-pure) (typS⇒ sh u)
typS⇒ sh (u-terminal-app u)          = ⊢app (⊢terminalᶜ ⊑-pure) (typS⇒ sh u)
typS⇒ sh (u-apply-app u)             = ⊢app ⊢applyᶜ (typS⇒ sh u)
typS⇒ sh (u-apply-eff-app u)         = ⊢app ⊢applyEffᶜ (typS⇒ sh u)
typS⇒ sh (u-Out-app {w = w} u)       = ⊢app (⊢outᶜ w) (typS⇒ sh u)
typS⇒ sh (u-Out-act-app {w = w} u)   = ⊢app (⊢outActᶜ w) (typS⇒ sh u)
typS⇒ sh (u-app {q = q} uf ux)       = ⊢app-pure q (typS⇒ sh uf) (typS⇐ sh ux)
typS⇒ sh (u-effApp uf ux)            = ⊢effAppᶜ (typS⇒ sh uf) (typS⇐ sh ux)
typS⇒ sh (u-app-spine ux uf)         = ⊢app (typS↦ sh uf) (typS⇒ sh ux)

typS⇐ sh (u-id {π = π})              = ⊢idᶜ (pure-⊑ π)
typS⇐ sh (u-fst {π = π})             = ⊢fstᶜ (pure-⊑ π)
typS⇐ sh (u-snd {π = π})             = ⊢sndᶜ (pure-⊑ π)
typS⇐ sh (u-terminal {π = π})        = ⊢terminalᶜ (pure-⊑ π)
typS⇐ sh (u-initial {π = π})         = ⊢initialᶜ (pure-⊑ π)
typS⇐ sh (u-inl {π = π})             = ⊢inlᶜ (pure-⊑ π)
typS⇐ sh (u-inr {π = π})             = ⊢inrᶜ (pure-⊑ π)
typS⇐ sh (u-compose-g ug uf)         = ⊢composeᶜ (·p-diag _) (typS⇐ sh uf) (typS↦ sh ug)
typS⇐ sh (u-compose-f {p = p} uf ug) = ⊢composeᶜ (·p-diag _) (⊢coerce p (typS⇒ sh uf)) (typS⇐ sh ug)
typS⇐ sh (u-case uf ug)              = ⊢caseᶜ (typS⇐ sh uf) (typS⇐ sh ug)
typS⇐ sh (u-pair uf ug)              = ⊢pairᶜ (·p-diag _) (typS⇐ sh uf) (typS⇐ sh ug)
typS⇐ sh (u-curry {π₀ = π₀} u)       = ⊢curryᶜ (pure-⊑ π₀) (typS⇐ sh u)
typS⇐ sh (u-cata {w = w} u)          = ⊢cataᶜ w (typS⇐ sh u)
typS⇐ sh (u-ana {π₀ = π₀} {w = w} u) = ⊢anaᶜ (pure-⊑ π₀) w (typS⇐ sh u)
typS⇐ sh (u-loop u)                  = ⊢loopᶜ (typS⇐ sh u)
typS⇐ sh (u-sub {p = p} u)           = ⊢coerce p (typS⇒ sh u)
typS⇐ sh (u-lam {q = q} {π = π} {q′ = q′} ≤p u) = ⊢lam (≤qᵇ→≤q q′ q ≤p) (⊢sub-eff (pure-⊑ π) (typS⇐ (sh-▸ sh) u))
typS⇐ sh (u-pair-lit ua ub)          = ⊢pair (typS⇐ sh ua) (typS⇐ sh ub)
typS⇐ sh (u-In-app {w = w} u)        = ⊢app (⊢inᶜ w) (typS⇐ sh u)
typS⇐ sh (u-apply-app u)             = ⊢app ⊢applyᶜ (typS⇒ sh u)
typS⇐ sh (u-inl-app u)               = ⊢app (⊢inlᶜ ⊑-pure) (typS⇐ sh u)
typS⇐ sh (u-inr-app u)               = ⊢app (⊢inrᶜ ⊑-pure) (typS⇐ sh u)
typS⇐ sh (u-initial-app u)           = ⊢app (⊢initialᶜ ⊑-pure) (typS⇐ sh u)
typS⇐ sh (u-poly {d = d} {τ = τ} {r = r}) = ⊢ref d τ r

typS↦ sh (u-infer {B = B} {p = p} {o = o} u) = ⊢coerce (sub-arr p (<:-refl B) o) (typS⇒ sh u)
typS↦ {Γ = Γ} sh (u-poly {d = d} {A = A} {B = B} {ty = ty} {τ = τ} {r = r} {ea = ea} {eb = eb} {o = o}) =
  ⊢coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o)
          (subst (λ X → Δ ⊩ Γ ⊢[ zeroUsage ] ref d τ ∷ X ! pure) (poly-inst d τ ty ea eb) (⊢ref d τ r))
typS↦ sh (u-lam {π = π} {q′ = q′} u) = ⊢lam (≤qᵇ→≤q q′ Many (≤q-Many q′)) (⊢sub-eff (pure-⊑ π) (typS⇒ (sh-▸ sh) u))
typS↦ sh (u-compose ug uf)           = ⊢composeᶜ (·p-diag _) (typS↦ sh uf) (typS↦ sh ug)
typS↦ sh (u-id {π = π})              = ⊢idᶜ (pure-⊑ π)
typS↦ sh (u-fst {π = π})             = ⊢fstᶜ (pure-⊑ π)
typS↦ sh (u-snd {π = π})             = ⊢sndᶜ (pure-⊑ π)
typS↦ sh (u-terminal {π = π})        = ⊢terminalᶜ (pure-⊑ π)
typS↦ sh (u-initial {π = π})         = ⊢initialᶜ (pure-⊑ π)
typS↦ sh (u-case {j = j} uf ug)      =
  ⊢caseᶜ (⊢coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (left j)) (⊑π-refl _)) (typS↦ sh uf))
         (⊢coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (right j)) (⊑π-refl _)) (typS↦ sh ug))
typS↦ sh (u-pair uf ug)              = ⊢pairᶜ (·p-diag _) (typS↦ sh uf) (typS↦ sh ug)
typS↦ sh (u-cata {w = w} u)          = ⊢cataᶜ w (typS⇒ sh u)

-- At the locals' own context.
typ⇒ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Use⇒ d Ψ → Δ ⊩ ctxOf L ⊢[ Ψ ] t ∷ A ! pure
typ⇒ = typS⇒ (shape-of _)

typ⇐ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇐ A ↝ t} → Use⇐ d Ψ → Δ ⊩ ctxOf L ⊢[ Ψ ] t ∷ A ! pure
typ⇐ = typS⇐ (shape-of _)

typ↦ : ∀ {n} {L : Locals m n} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Use↦ d Ψ
     → Δ ⊩ ctxOf L ⊢[ Ψ ] t ∷ A ⇒[ mk-kind Many π ] B ! pure
typ↦ = typS↦ (shape-of _)
