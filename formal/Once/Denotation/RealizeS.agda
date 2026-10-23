-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.RealizeS — the realization of the Spec's derivation
-- (plan 0.122 §2b-3, stage b).
--
-- An expression the Spec types (`Spec.Surface.Typing`), with how many times
-- it uses each local (`TypeCheck.Use`), is realized as the intrinsically
-- typed surface term it denotes, point-free where the source is: each rule's
-- combinator is the term former of the same name. The realization reads the
-- derivation, never the elaborator's output.
--
-- What the Spec's derivation does not say, the table of earlier definitions
-- does: a reference to entry `d` is a call of a compiled function or the
-- inlined telescope definition (`inline d`), named `nm d`.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx; Type)

module Once.Denotation.RealizeS (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set)
  (inline : Fin s → Bool) {m : ℕ} (Δ : KCtx m) where

open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Once.Spec.Grade using (Many; Purity; mk-kind; pureᶠ; actᶠ; act)
open import Once.Spec.Type using (Ty; _⇒[_]_; _⟨_⟩; μ; ν; Unit)
open import Once.Spec.Sub using (sub-arr; _⊔_≔_)
open _⊔_≔_ using (left; right)
open import Once.Spec.Core.Syntax using (module Schema; _!!_)
open Schema using (type)
open import Once.Spec.Context using (Usage)
open import Once.Spec.Float.Decimal using (decimalOf; negate)
open import Once.Internal.Name using (showCanonical)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Type.Grade using (≤q-Many)
open import Once.IR as IR using (IR)
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Surface.Syntax
  using (Expr; var; lam; app; effApp; pair; neg; let'; case'; int; float; unit; add; sub; mul; div; mod';
         fadd; fsub; fmul; fdiv; i2f; lt; le; gt; ge; eq; ne; sigOp; closure; poly; lift-morphism;
         morph-app; coerce; cata; ana; loop; comp'; copair'; fork'; curry')
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals; ia-add; ia-sub; ia-mul; ia-div; ia-mod; fa-add; fa-sub; fa-mul; fa-div;
               cmp-lt; cmp-le; cmp-gt; cmp-ge; cmp-eq; cmp-ne)
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ
open import Once.Internal.Core.Decl using (⌜declS⌝)

-- A reference to entry `d` at type `T`.
ref : ∀ {n} {Γ : Once.Spec.Context.Ctx m n} (d : Fin s) (T : Ty m) → Bool → Expr Γ Once.Spec.Context.zeroUsage T
ref d T true  = poly (showCanonical (nm d)) T
ref d T false = closure (showCanonical (nm d))

realize⇒ : ∀ {n} {L : Locals m n} {Γ} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Shape L Γ → Use⇒ d Ψ → Expr Γ Ψ A
realize⇐ : ∀ {n} {L : Locals m n} {Γ} {e A t Ψ} {d : L ⊢ e ⇐ A ↝ t} → Shape L Γ → Use⇐ d Ψ → Expr Γ Ψ A
realize↦ : ∀ {n} {L : Locals m n} {Γ} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Shape L Γ → Use↦ d Ψ
         → Expr Γ Ψ (A ⇒[ mk-kind Many π ] B)

realize⇒ sh (u-int {i})             = int i
realize⇒ sh (u-float {i} {f} {l})   = float (decimalOf i f l)
realize⇒ sh u-unit                  = unit
realize⇒ sh u-unit-g                = unit
realize⇒ sh (u-var {v = v})         = subst (Expr _ _) (lookup-shape sh v) (var _)
realize⇒ sh (u-sigop {c = c} k h)   = subst (Expr _ _) (sym (⌜declS⌝ k h)) (sigOp c k)
realize⇒ sh (u-def {d = d} {τ = τ}) = ref d (type (S !! d) ⟨ τ ⟩) (inline d)
realize⇒ sh (u-annot u)             = realize⇐ sh u
realize⇒ sh (u-pair ua ub)          = pair (realize⇒ sh ua) (realize⇒ sh ub)
realize⇒ sh (u-neg u)               = neg (realize⇒ sh u)
realize⇒ sh (u-neg-float {i} {f} {l}) = float (negate (decimalOf i f l))
realize⇒ sh (u-let u₁ u₂)           = let' (realize⇒ sh u₁) (realize⇒ (sh-▸ sh) u₂)
realize⇒ sh (u-case {j = j} us ul ur) =
  case' (realize⇒ sh us) (coerce (<:ᶜ⇒<: (left j)) (realize⇒ (sh-▸ sh) ul)) (coerce (<:ᶜ⇒<: (right j)) (realize⇒ (sh-▸ sh) ur))
realize⇒ sh (u-arith {o = ia-add} u₁ u₂) = add  (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith {o = ia-sub} u₁ u₂) = sub  (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith {o = ia-mul} u₁ u₂) = mul  (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith {o = ia-div} u₁ u₂) = div  (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith {o = ia-mod} u₁ u₂) = mod' (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float {o = fa-add} u₁ u₂) = fadd (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float {o = fa-sub} u₁ u₂) = fsub (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float {o = fa-mul} u₁ u₂) = fmul (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float {o = fa-div} u₁ u₂) = fdiv (realize⇒ sh u₁) (realize⇒ sh u₂)
-- D125: the `Int` side of a mixed operation widens.
realize⇒ sh (u-arith-float-il {o = fa-add} u₁ u₂) = fadd (i2f (realize⇒ sh u₁)) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float-il {o = fa-sub} u₁ u₂) = fsub (i2f (realize⇒ sh u₁)) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float-il {o = fa-mul} u₁ u₂) = fmul (i2f (realize⇒ sh u₁)) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float-il {o = fa-div} u₁ u₂) = fdiv (i2f (realize⇒ sh u₁)) (realize⇒ sh u₂)
realize⇒ sh (u-arith-float-ir {o = fa-add} u₁ u₂) = fadd (realize⇒ sh u₁) (i2f (realize⇒ sh u₂))
realize⇒ sh (u-arith-float-ir {o = fa-sub} u₁ u₂) = fsub (realize⇒ sh u₁) (i2f (realize⇒ sh u₂))
realize⇒ sh (u-arith-float-ir {o = fa-mul} u₁ u₂) = fmul (realize⇒ sh u₁) (i2f (realize⇒ sh u₂))
realize⇒ sh (u-arith-float-ir {o = fa-div} u₁ u₂) = fdiv (realize⇒ sh u₁) (i2f (realize⇒ sh u₂))
realize⇒ sh (u-compare {o = cmp-lt} u₁ u₂) = lt (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-compare {o = cmp-le} u₁ u₂) = le (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-compare {o = cmp-gt} u₁ u₂) = gt (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-compare {o = cmp-ge} u₁ u₂) = ge (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-compare {o = cmp-eq} u₁ u₂) = eq (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-compare {o = cmp-ne} u₁ u₂) = ne (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-id-app u)            = morph-app IR.id (realize⇒ sh u)
realize⇒ sh (u-fst-app u)           = morph-app IR.fst (realize⇒ sh u)
realize⇒ sh (u-snd-app u)           = morph-app IR.snd (realize⇒ sh u)
realize⇒ sh (u-terminal-app u)      = morph-app IR.terminal (realize⇒ sh u)
realize⇒ sh (u-apply-app u)         = morph-app IR.apply (realize⇒ sh u)
-- D222: `apply` at an effectful arrow builds the suspension `curry (apply ∘ fst)`.
realize⇒ sh (u-apply-eff-app u)     = morph-app (IR.curry (IR.apply IR.∘ IR.fst)) (realize⇒ sh u)
-- D194: the ν eliminator; D233: at an acting stream the force is suspended.
realize⇒ sh (u-Out-app {F = F} {w = w} u) =
  morph-app (subst (λ o → IR ⌊ ν F pureᶠ ⌋ o) (sym (⌊⟧T-commute F (ν F pureᶠ))) (IR.Out (wf-⌊⌋ w))) (realize⇒ sh u)
realize⇒ sh (u-Out-act-app {F = F} {w = w} u) =
  morph-app (IR.curry (subst (λ o → IR ⌊ ν F actᶠ ⌋ o) (sym (⌊⟧T-commute F (ν F actᶠ))) (IR.Out (wf-⌊⌋ w)) IR.∘ IR.fst))
            (realize⇒ sh u)
realize⇒ sh (u-app uf ux)           = app (realize⇒ sh uf) (realize⇐ sh ux)
realize⇒ sh (u-effApp {g = g} uf ux) = effApp {g = g} (realize⇒ sh uf) (realize⇐ sh ux)
realize⇒ sh (u-app-spine ux uf)     = app (realize↦ sh uf) (realize⇒ sh ux)

realize⇐ sh u-id                    = lift-morphism IR.id
realize⇐ sh u-fst                   = lift-morphism IR.fst
realize⇐ sh u-snd                   = lift-morphism IR.snd
realize⇐ sh u-terminal              = lift-morphism IR.terminal
realize⇐ sh u-initial               = lift-morphism IR.initial
realize⇐ sh u-inl                   = lift-morphism IR.inl
realize⇐ sh u-inr                   = lift-morphism IR.inr
realize⇐ sh (u-compose-g ug uf)     = comp' (realize⇐ sh uf) (realize↦ sh ug)
realize⇐ sh (u-compose-f {p = p} uf ug) = comp' (coerce p (realize⇒ sh uf)) (realize⇐ sh ug)
realize⇐ sh (u-case uf ug)          = copair' (realize⇐ sh uf) (realize⇐ sh ug)
realize⇐ sh (u-pair uf ug)          = fork' (realize⇐ sh uf) (realize⇐ sh ug)
realize⇐ sh (u-curry u)             = curry' (realize⇐ sh u)
realize⇐ sh (u-cata {w = w} u)      = cata w (realize⇐ sh u)
realize⇐ sh (u-ana {w = w} u)       = ana w (realize⇐ sh u)
realize⇐ sh (u-loop u)              = loop (realize⇐ sh u)
realize⇐ sh (u-sub {p = p} u)       = coerce p (realize⇒ sh u)
realize⇐ sh (u-lam {q = q} ≤p u)    = lam q ≤p (realize⇐ (sh-▸ sh) u)
realize⇐ sh (u-pair-lit ua ub)      = pair (realize⇐ sh ua) (realize⇐ sh ub)
realize⇐ sh (u-In-app {F = F} {w = w} u) =
  morph-app (subst (λ o → IR o ⌊ μ F ⌋) (sym (⌊⟧T-commute F (μ F))) (IR.In (wf-⌊⌋ w))) (realize⇐ sh u)
realize⇐ sh (u-apply-app u)         = morph-app IR.apply (realize⇒ sh u)
realize⇐ sh (u-inl-app u)           = morph-app IR.inl (realize⇐ sh u)
realize⇐ sh (u-inr-app u)           = morph-app IR.inr (realize⇐ sh u)
realize⇐ sh (u-initial-app u)       = morph-app IR.initial (realize⇐ sh u)
realize⇐ sh (u-poly {d = d} {τ = τ}) = ref d (type (S !! d) ⟨ τ ⟩) (inline d)

realize↦ sh (u-infer {B = B} {p = p} {o = o} u) = coerce (sub-arr p (<:-refl B) o) (realize⇒ sh u)
realize↦ sh (u-poly {d = d} {π′ = π′} {A = A} {B = B} {o = o}) =
  coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o) (ref d (A ⇒[ mk-kind Many π′ ] B) (inline d))
realize↦ sh (u-lam {q′ = q′} u)     = lam Many (≤q-Many q′) (realize⇒ (sh-▸ sh) u)
realize↦ sh (u-compose ug uf)       = comp' (realize↦ sh uf) (realize↦ sh ug)
realize↦ sh u-id                    = lift-morphism IR.id
realize↦ sh u-fst                   = lift-morphism IR.fst
realize↦ sh u-snd                   = lift-morphism IR.snd
realize↦ sh u-terminal              = lift-morphism IR.terminal
realize↦ sh u-initial               = lift-morphism IR.initial
realize↦ sh (u-case {j = j} uf ug)  =
  copair' (coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (left j)) (⊑π-refl _)) (realize↦ sh uf))
          (coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (right j)) (⊑π-refl _)) (realize↦ sh ug))
realize↦ sh (u-pair uf ug)          = fork' (realize↦ sh uf) (realize↦ sh ug)
realize↦ sh (u-cata {w = w} u)      = cata w (realize⇒ sh u)
