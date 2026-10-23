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
open import Once.Spec.Type using (KCtx)

module Once.Denotation.RealizeS (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName)
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
open import Once.TypeCheck.Use Σ S nm Δ

-- A reference to entry `d` at type `T`.
ref : ∀ {n} {Γ : Once.Spec.Context.Ctx m n} (d : Fin s) (T : Ty m) → Bool → Expr Γ Once.Spec.Context.zeroUsage T
ref d T true  = poly (showCanonical (nm d)) T
ref d T false = closure (showCanonical (nm d))

realize⇒ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Use⇒ d Ψ → Expr (ctxOf L) Ψ A
realize⇐ : ∀ {n} {L : Locals m n} {e A t Ψ} {d : L ⊢ e ⇐ A ↝ t} → Use⇐ d Ψ → Expr (ctxOf L) Ψ A
realize↦ : ∀ {n} {L : Locals m n} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Use↦ d Ψ
         → Expr (ctxOf L) Ψ (A ⇒[ mk-kind Many π ] B)

realize⇒ (u-int {i})             = int i
realize⇒ (u-float {i} {f} {l})   = float (decimalOf i f l)
realize⇒ u-unit                  = unit
realize⇒ u-unit-g                = unit
realize⇒ (u-var {v = v})         = subst (Expr _ _) (lookup-at v) (var _)
realize⇒ (u-sigop {c = c} k e)   = subst (Expr _ _) (sym e) (sigOp c k)
realize⇒ (u-def {d = d} {τ = τ}) = ref d (type (S !! d) ⟨ τ ⟩) (inline d)
realize⇒ (u-annot u)             = realize⇐ u
realize⇒ (u-pair ua ub)          = pair (realize⇒ ua) (realize⇒ ub)
realize⇒ (u-neg u)               = neg (realize⇒ u)
realize⇒ (u-neg-float {i} {f} {l}) = float (negate (decimalOf i f l))
realize⇒ (u-let u₁ u₂)           = let' (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-case {j = j} us ul ur) =
  case' (realize⇒ us) (coerce (<:ᶜ⇒<: (left j)) (realize⇒ ul)) (coerce (<:ᶜ⇒<: (right j)) (realize⇒ ur))
realize⇒ (u-arith {o = ia-add} u₁ u₂) = add  (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith {o = ia-sub} u₁ u₂) = sub  (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith {o = ia-mul} u₁ u₂) = mul  (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith {o = ia-div} u₁ u₂) = div  (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith {o = ia-mod} u₁ u₂) = mod' (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith-float {o = fa-add} u₁ u₂) = fadd (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith-float {o = fa-sub} u₁ u₂) = fsub (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith-float {o = fa-mul} u₁ u₂) = fmul (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-arith-float {o = fa-div} u₁ u₂) = fdiv (realize⇒ u₁) (realize⇒ u₂)
-- D125: the `Int` side of a mixed operation widens.
realize⇒ (u-arith-float-il {o = fa-add} u₁ u₂) = fadd (i2f (realize⇒ u₁)) (realize⇒ u₂)
realize⇒ (u-arith-float-il {o = fa-sub} u₁ u₂) = fsub (i2f (realize⇒ u₁)) (realize⇒ u₂)
realize⇒ (u-arith-float-il {o = fa-mul} u₁ u₂) = fmul (i2f (realize⇒ u₁)) (realize⇒ u₂)
realize⇒ (u-arith-float-il {o = fa-div} u₁ u₂) = fdiv (i2f (realize⇒ u₁)) (realize⇒ u₂)
realize⇒ (u-arith-float-ir {o = fa-add} u₁ u₂) = fadd (realize⇒ u₁) (i2f (realize⇒ u₂))
realize⇒ (u-arith-float-ir {o = fa-sub} u₁ u₂) = fsub (realize⇒ u₁) (i2f (realize⇒ u₂))
realize⇒ (u-arith-float-ir {o = fa-mul} u₁ u₂) = fmul (realize⇒ u₁) (i2f (realize⇒ u₂))
realize⇒ (u-arith-float-ir {o = fa-div} u₁ u₂) = fdiv (realize⇒ u₁) (i2f (realize⇒ u₂))
realize⇒ (u-compare {o = cmp-lt} u₁ u₂) = lt (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-compare {o = cmp-le} u₁ u₂) = le (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-compare {o = cmp-gt} u₁ u₂) = gt (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-compare {o = cmp-ge} u₁ u₂) = ge (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-compare {o = cmp-eq} u₁ u₂) = eq (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-compare {o = cmp-ne} u₁ u₂) = ne (realize⇒ u₁) (realize⇒ u₂)
realize⇒ (u-id-app u)            = morph-app IR.id (realize⇒ u)
realize⇒ (u-fst-app u)           = morph-app IR.fst (realize⇒ u)
realize⇒ (u-snd-app u)           = morph-app IR.snd (realize⇒ u)
realize⇒ (u-terminal-app u)      = morph-app IR.terminal (realize⇒ u)
realize⇒ (u-apply-app u)         = morph-app IR.apply (realize⇒ u)
-- D222: `apply` at an effectful arrow builds the suspension `curry (apply ∘ fst)`.
realize⇒ (u-apply-eff-app u)     = morph-app (IR.curry (IR.apply IR.∘ IR.fst)) (realize⇒ u)
-- D194: the ν eliminator; D233: at an acting stream the force is suspended.
realize⇒ (u-Out-app {F = F} {w = w} u) =
  morph-app (subst (λ o → IR ⌊ ν F pureᶠ ⌋ o) (sym (⌊⟧T-commute F (ν F pureᶠ))) (IR.Out (wf-⌊⌋ w))) (realize⇒ u)
realize⇒ (u-Out-act-app {F = F} {w = w} u) =
  morph-app (IR.curry (subst (λ o → IR ⌊ ν F actᶠ ⌋ o) (sym (⌊⟧T-commute F (ν F actᶠ))) (IR.Out (wf-⌊⌋ w)) IR.∘ IR.fst))
            (realize⇒ u)
realize⇒ (u-app uf ux)           = app (realize⇒ uf) (realize⇐ ux)
realize⇒ (u-effApp {g = g} uf ux) = effApp {g = g} (realize⇒ uf) (realize⇐ ux)
realize⇒ (u-app-spine ux uf)     = app (realize↦ uf) (realize⇒ ux)

realize⇐ u-id                    = lift-morphism IR.id
realize⇐ u-fst                   = lift-morphism IR.fst
realize⇐ u-snd                   = lift-morphism IR.snd
realize⇐ u-terminal              = lift-morphism IR.terminal
realize⇐ u-initial               = lift-morphism IR.initial
realize⇐ u-inl                   = lift-morphism IR.inl
realize⇐ u-inr                   = lift-morphism IR.inr
realize⇐ (u-compose-g ug uf)     = comp' (realize⇐ uf) (realize↦ ug)
realize⇐ (u-compose-f {p = p} uf ug) = comp' (coerce p (realize⇒ uf)) (realize⇐ ug)
realize⇐ (u-case uf ug)          = copair' (realize⇐ uf) (realize⇐ ug)
realize⇐ (u-pair uf ug)          = fork' (realize⇐ uf) (realize⇐ ug)
realize⇐ (u-curry u)             = curry' (realize⇐ u)
realize⇐ (u-cata {w = w} u)      = cata w (realize⇐ u)
realize⇐ (u-ana {w = w} u)       = ana w (realize⇐ u)
realize⇐ (u-loop u)              = loop (realize⇐ u)
realize⇐ (u-sub {p = p} u)       = coerce p (realize⇒ u)
realize⇐ (u-lam {q = q} ≤p u)    = lam q ≤p (realize⇐ u)
realize⇐ (u-pair-lit ua ub)      = pair (realize⇐ ua) (realize⇐ ub)
realize⇐ (u-In-app {F = F} {w = w} u) =
  morph-app (subst (λ o → IR o ⌊ μ F ⌋) (sym (⌊⟧T-commute F (μ F))) (IR.In (wf-⌊⌋ w))) (realize⇐ u)
realize⇐ (u-apply-app u)         = morph-app IR.apply (realize⇒ u)
realize⇐ (u-inl-app u)           = morph-app IR.inl (realize⇐ u)
realize⇐ (u-inr-app u)           = morph-app IR.inr (realize⇐ u)
realize⇐ (u-initial-app u)       = morph-app IR.initial (realize⇐ u)
realize⇐ (u-poly {d = d} {τ = τ}) = ref d (type (S !! d) ⟨ τ ⟩) (inline d)

realize↦ (u-infer {B = B} {p = p} {o = o} u) = coerce (sub-arr p (<:-refl B) o) (realize⇒ u)
realize↦ (u-poly {d = d} {π′ = π′} {A = A} {B = B} {o = o}) =
  coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o) (ref d (A ⇒[ mk-kind Many π′ ] B) (inline d))
realize↦ (u-lam {q′ = q′} u)     = lam Many (≤q-Many q′) (realize⇒ u)
realize↦ (u-compose ug uf)       = comp' (realize↦ uf) (realize↦ ug)
realize↦ u-id                    = lift-morphism IR.id
realize↦ u-fst                   = lift-morphism IR.fst
realize↦ u-snd                   = lift-morphism IR.snd
realize↦ u-terminal              = lift-morphism IR.terminal
realize↦ u-initial               = lift-morphism IR.initial
realize↦ (u-case {j = j} uf ug)  =
  copair' (coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (left j)) (⊑π-refl _)) (realize↦ uf))
          (coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (right j)) (⊑π-refl _)) (realize↦ ug))
realize↦ (u-pair uf ug)          = fork' (realize↦ uf) (realize↦ ug)
realize↦ (u-cata {w = w} u)      = cata w (realize⇒ u)
