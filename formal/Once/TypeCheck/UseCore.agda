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
open import Once.Spec.Type using (KCtx)

module Once.TypeCheck.UseCore (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) {m : ℕ} (Δ : KCtx m) where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (mk-kind; Many; pure; ⊑-pure)
open import Once.Spec.Type using (Ty; TySub; _⇒[_]_; Respects; _⟨_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.Spec.Core.Syntax using (p-neg; p-i2f; p-add; p-sub; p-mul; p-div; p-mod; p-fadd; p-fsub; p-fmul; p-fdiv;
                                         p-lt; p-le; p-gt; p-ge; p-eq; p-ne; prim; pair; ref)
open import Once.Spec.Context using (Ctx; _+ᵘ_; zeroUsage)
open import Once.Spec.Type using (Int; Float; Unit; _+_)
open import Once.Spec.Sub using (sub-arr; _⊔_≔_)
open _⊔_≔_ using (left; right)
open import Once.Spec.Core.Syntax using (module Schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Internal.Core.DerivedTyping Σ S
open import Once.Internal.Type.Sub using (·p-diag; pure-⊑; <:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Type.Grade using (≤q-Many; ≤qᵇ→≤q)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals; ia-add; ia-sub; ia-mul; ia-div; ia-mod; fa-add; fa-sub; fa-mul; fa-div;
               cmp-lt; cmp-le; cmp-gt; cmp-ge; cmp-eq; cmp-ne)
open import Once.TypeCheck.Use Σ S nm Δ

-- An entry with no type variables respects any kinds.
private
  no-kinds : ∀ (d : Fin s) (τ : TySub (arity (S !! d)) m) → arity (S !! d) ≡ 0 → Respects (kinds (S !! d)) Δ τ
  no-kinds d τ a i = ⊥-elim (fin0 (subst Fin a i))
    where fin0 : Fin 0 → ⊥
          fin0 ()

  -- The saturated primitive of a binary operator, on the pair of its operands.
  module _ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ t₁ t₂} where
    ar : ∀ {op p} → SU.IntArith op p → Δ ⊩ Γ ⊢[ Ψ₁ ] t₁ ∷ Int ! pure → Δ ⊩ Γ ⊢[ Ψ₂ ] t₂ ∷ Int ! pure
       → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] prim p (pair t₁ t₂) ∷ Int ! pure
    ar ia-add d e = ⊢prim p-add (⊢pair d e)
    ar ia-sub d e = ⊢prim p-sub (⊢pair d e)
    ar ia-mul d e = ⊢prim p-mul (⊢pair d e)
    ar ia-div d e = ⊢prim p-div (⊢pair d e)
    ar ia-mod d e = ⊢prim p-mod (⊢pair d e)

    far : ∀ {op p} → SU.FloatArith op p → Δ ⊩ Γ ⊢[ Ψ₁ ] t₁ ∷ Float ! pure → Δ ⊩ Γ ⊢[ Ψ₂ ] t₂ ∷ Float ! pure
        → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] prim p (pair t₁ t₂) ∷ Float ! pure
    far fa-add d e = ⊢prim p-fadd (⊢pair d e)
    far fa-sub d e = ⊢prim p-fsub (⊢pair d e)
    far fa-mul d e = ⊢prim p-fmul (⊢pair d e)
    far fa-div d e = ⊢prim p-fdiv (⊢pair d e)

    cm : ∀ {op p} → SU.Compare op p → Δ ⊩ Γ ⊢[ Ψ₁ ] t₁ ∷ Int ! pure → Δ ⊩ Γ ⊢[ Ψ₂ ] t₂ ∷ Int ! pure
       → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] prim p (pair t₁ t₂) ∷ Unit + Unit ! pure
    cm cmp-lt d e = ⊢prim p-lt (⊢pair d e)
    cm cmp-le d e = ⊢prim p-le (⊢pair d e)
    cm cmp-gt d e = ⊢prim p-gt (⊢pair d e)
    cm cmp-ge d e = ⊢prim p-ge (⊢pair d e)
    cm cmp-eq d e = ⊢prim p-eq (⊢pair d e)
    cm cmp-ne d e = ⊢prim p-ne (⊢pair d e)

typ⇒ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Use⇒ d Ψ → Δ ⊩ ctxOf L ⊢[ Ψ ] t ∷ A ! pure
typ⇐ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇐ A ↝ t} → Use⇐ d Ψ → Δ ⊩ ctxOf L ⊢[ Ψ ] t ∷ A ! pure
typ↦ : ∀ {n} {L : Locals m n} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Use↦ d Ψ
     → Δ ⊩ ctxOf L ⊢[ Ψ ] t ∷ A ⇒[ mk-kind Many π ] B ! pure

typ⇒ u-int                       = ⊢lit-int
typ⇒ u-float                     = ⊢lit-float
typ⇒ u-unit                      = ⊢unit
typ⇒ u-unit-g                    = ⊢unit
typ⇒ (u-var {v = v})             = subst (λ X → Δ ⊩ _ ⊢[ _ ] _ ∷ X ! pure) (lookup-at v) (⊢var _)
typ⇒ (u-sigop {mem = mem} k e)   = ⊢sigop mem
typ⇒ (u-def {d = d} {τ = τ} {a = a}) = ⊢ref d τ (no-kinds d τ a)
typ⇒ (u-annot u)                 = typ⇐ u
typ⇒ (u-pair ua ub)              = ⊢pair (typ⇒ ua) (typ⇒ ub)
typ⇒ (u-neg u)                   = ⊢prim p-neg (typ⇒ u)
typ⇒ u-neg-float                 = ⊢lit-float
typ⇒ (u-let {q = q} u₁ u₂)       = ⊢let-pure q (typ⇒ u₁) (typ⇒ u₂)
-- Each branch composed with its conversion into the join (D322).
typ⇒ (u-case {j = j} us ul ur)   =
  ⊢case⊔ (typ⇒ us) (⊢coerce (<:ᶜ⇒<: (left j)) (typ⇒ ul)) (⊢coerce (<:ᶜ⇒<: (right j)) (typ⇒ ur))
typ⇒ (u-arith {o = o} u₁ u₂)            = ar o (typ⇒ u₁) (typ⇒ u₂)
typ⇒ (u-arith-float {o = o} u₁ u₂)      = far o (typ⇒ u₁) (typ⇒ u₂)
typ⇒ (u-arith-float-il {o = o} u₁ u₂)   = far o (⊢prim p-i2f (typ⇒ u₁)) (typ⇒ u₂)
typ⇒ (u-arith-float-ir {o = o} u₁ u₂)   = far o (typ⇒ u₁) (⊢prim p-i2f (typ⇒ u₂))
typ⇒ (u-compare {o = o} u₁ u₂)          = cm o (typ⇒ u₁) (typ⇒ u₂)
typ⇒ (u-id-app u)                = ⊢app (⊢idᶜ ⊑-pure) (typ⇒ u)
typ⇒ (u-fst-app u)               = ⊢app (⊢fstᶜ ⊑-pure) (typ⇒ u)
typ⇒ (u-snd-app u)               = ⊢app (⊢sndᶜ ⊑-pure) (typ⇒ u)
typ⇒ (u-terminal-app u)          = ⊢app (⊢terminalᶜ ⊑-pure) (typ⇒ u)
typ⇒ (u-apply-app u)             = ⊢app ⊢applyᶜ (typ⇒ u)
typ⇒ (u-apply-eff-app u)         = ⊢app ⊢applyEffᶜ (typ⇒ u)
typ⇒ (u-Out-app {w = w} u)       = ⊢app (⊢outᶜ w) (typ⇒ u)
typ⇒ (u-Out-act-app {w = w} u)   = ⊢app (⊢outActᶜ w) (typ⇒ u)
typ⇒ (u-app {q = q} uf ux)       = ⊢app-pure q (typ⇒ uf) (typ⇐ ux)
typ⇒ (u-effApp uf ux)            = ⊢effAppᶜ (typ⇒ uf) (typ⇐ ux)
typ⇒ (u-app-spine ux uf)         = ⊢app (typ↦ uf) (typ⇒ ux)

typ⇐ (u-id {π = π})              = ⊢idᶜ (pure-⊑ π)
typ⇐ (u-fst {π = π})             = ⊢fstᶜ (pure-⊑ π)
typ⇐ (u-snd {π = π})             = ⊢sndᶜ (pure-⊑ π)
typ⇐ (u-terminal {π = π})        = ⊢terminalᶜ (pure-⊑ π)
typ⇐ (u-initial {π = π})         = ⊢initialᶜ (pure-⊑ π)
typ⇐ (u-inl {π = π})             = ⊢inlᶜ (pure-⊑ π)
typ⇐ (u-inr {π = π})             = ⊢inrᶜ (pure-⊑ π)
typ⇐ (u-compose-g ug uf)         = ⊢composeᶜ (·p-diag _) (typ⇐ uf) (typ↦ ug)
typ⇐ (u-compose-f {p = p} uf ug) = ⊢composeᶜ (·p-diag _) (⊢coerce p (typ⇒ uf)) (typ⇐ ug)
typ⇐ (u-case uf ug)              = ⊢caseᶜ (typ⇐ uf) (typ⇐ ug)
typ⇐ (u-pair uf ug)              = ⊢pairᶜ (·p-diag _) (typ⇐ uf) (typ⇐ ug)
typ⇐ (u-curry {π₀ = π₀} u)       = ⊢curryᶜ (pure-⊑ π₀) (typ⇐ u)
typ⇐ (u-cata {w = w} u)          = ⊢cataᶜ w (typ⇐ u)
typ⇐ (u-ana {π₀ = π₀} {w = w} u) = ⊢anaᶜ (pure-⊑ π₀) w (typ⇐ u)
typ⇐ (u-loop u)                  = ⊢loopᶜ (typ⇐ u)
typ⇐ (u-sub {p = p} u)           = ⊢coerce p (typ⇒ u)
typ⇐ (u-lam {q = q} {π = π} {q′ = q′} ≤p u) = ⊢lam (≤qᵇ→≤q q′ q ≤p) (⊢sub-eff (pure-⊑ π) (typ⇐ u))
typ⇐ (u-pair-lit ua ub)          = ⊢pair (typ⇐ ua) (typ⇐ ub)
typ⇐ (u-In-app {w = w} u)        = ⊢app (⊢inᶜ w) (typ⇐ u)
typ⇐ (u-apply-app u)             = ⊢app ⊢applyᶜ (typ⇒ u)
typ⇐ (u-inl-app u)               = ⊢app (⊢inlᶜ ⊑-pure) (typ⇐ u)
typ⇐ (u-inr-app u)               = ⊢app (⊢inrᶜ ⊑-pure) (typ⇐ u)
typ⇐ (u-initial-app u)           = ⊢app (⊢initialᶜ ⊑-pure) (typ⇐ u)
typ⇐ (u-poly {d = d} {τ = τ} {r = r}) = ⊢ref d τ r

typ↦ (u-infer {B = B} {p = p} {o = o} u) = ⊢coerce (sub-arr p (<:-refl B) o) (typ⇒ u)
typ↦ {L = L} (u-poly {d = d} {A = A} {B = B} {ty = ty} {τ = τ} {r = r} {ea = ea} {eb = eb} {o = o}) =
  ⊢coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o) (subst (λ X → Δ ⊩ ctxOf L ⊢[ zeroUsage ] ref d τ ∷ X ! pure) (inst ty ea eb) (⊢ref d τ r))
  where
    inst : ∀ {sd sc π′} → type (S !! d) ≡ sd ⇒[ mk-kind Many π′ ] sc → sd ⟨ τ ⟩ ≡ A → sc ⟨ τ ⟩ ≡ B
         → type (S !! d) ⟨ τ ⟩ ≡ A ⇒[ mk-kind Many π′ ] B
    inst ty ea eb = trans (cong (_⟨ τ ⟩) ty) (cong₂ (λ X Y → X ⇒[ mk-kind Many _ ] Y) ea eb)
typ↦ (u-lam {π = π} {q′ = q′} u) = ⊢lam (≤qᵇ→≤q q′ Many (≤q-Many q′)) (⊢sub-eff (pure-⊑ π) (typ⇒ u))
typ↦ (u-compose ug uf)           = ⊢composeᶜ (·p-diag _) (typ↦ uf) (typ↦ ug)
typ↦ (u-id {π = π})              = ⊢idᶜ (pure-⊑ π)
typ↦ (u-fst {π = π})             = ⊢fstᶜ (pure-⊑ π)
typ↦ (u-snd {π = π})             = ⊢sndᶜ (pure-⊑ π)
typ↦ (u-terminal {π = π})        = ⊢terminalᶜ (pure-⊑ π)
typ↦ (u-initial {π = π})         = ⊢initialᶜ (pure-⊑ π)
typ↦ (u-case {j = j} uf ug)      =
  ⊢caseᶜ (⊢coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (left j)) (⊑π-refl _)) (typ↦ uf))
         (⊢coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (right j)) (⊑π-refl _)) (typ↦ ug))
typ↦ (u-pair uf ug)              = ⊢pairᶜ (·p-diag _) (typ↦ uf) (typ↦ ug)
typ↦ (u-cata {w = w} u)          = ⊢cataᶜ w (typ⇒ u)
