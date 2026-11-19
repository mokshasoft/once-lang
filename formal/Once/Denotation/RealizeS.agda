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
open import Once.Spec.Grade using (Many; mk-kind; pure)
open import Once.Spec.Type using (Ty; _⇒[_]_; _⟨_⟩)
open import Once.Spec.Surface.Generators using (Constant; Final; k-unit; k-toFloat; final-ν; final-T∞)
open import Once.TypeCheck.Table using (morphIR)
open import Once.Spec.Sub using (sub-arr; _⊔_≔_)
open _⊔_≔_ using (left; right)
open import Once.Spec.Core.Syntax using (module Schema; _!!_)
open Schema using (type)
import Once.Spec.Context
open import Once.Name using (showCanonical)
open import Once.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Type.Grade using (≤q-Many)
open import Once.IR as IR using ()
open import Once.Surface.Syntax
  using (Expr; var; lam; app; appT; pair; num; let'; case'; int; float; unit; sigOp; closure; poly; lift-morphism;
         morph-app; coerce; cata; ana; loop; comp'; copair'; fork'; curry')
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals)
open import Once.Spec.Float.Decimal using (signedDecimal)
open import Once.Spec.Theory using (‵neg)
open import Once.Surface.Numeric using (numBin; toFloatIR)
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ
open import Once.Core.Decl using (⌜declS⌝)

-- A reference to entry `d` at type `T`.
ref : ∀ {n} {Γ : Once.Spec.Context.Ctx m n} (d : Fin s) (T : Ty m) → Bool → Expr Γ Once.Spec.Context.zeroUsage T
ref d T true  = poly (showCanonical (nm d)) T
ref d T false = closure (showCanonical (nm d))

-- A constant of the table.
constE : ∀ {n} {Γ : Once.Spec.Context.Ctx m n} {g k T} {t : Once.Spec.Core.Syntax.Tm S m n}
       → Constant Δ g k T t → Expr Γ Once.Spec.Context.zeroUsage T
constE k-unit    = unit
constE k-toFloat = lift-morphism toFloatIR

-- The unfold into a final coalgebra of the table.
anaE : ∀ {n} {Γ : Once.Spec.Context.Ctx m n} {Ψ A π₀ X G ρ k}
     → Final {S = S} Δ {n = n} A π₀ X G ρ k → Expr Γ Ψ (A ⇒[ mk-kind Many ρ ] G A)
     → Expr Γ (Many Once.Spec.Context.*ᵘ Ψ) (A ⇒[ mk-kind Many π₀ ] X)
anaE (final-ν _ w) c = ana w c
anaE final-T∞      c = loop c

realize⇒ : ∀ {n} {L : Locals m n} {Γ} {e A t Ψ} {d : L ⊢ e ⇒ A ↝ t} → Shape L Γ → Use⇒ d Ψ → Expr Γ Ψ A
realize⇐ : ∀ {n} {L : Locals m n} {Γ} {e A t Ψ} {d : L ⊢ e ⇐ A ↝ t} → Shape L Γ → Use⇐ d Ψ → Expr Γ Ψ A
realize↦ : ∀ {n} {L : Locals m n} {Γ} {e A π B t Ψ} {d : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t} → Shape L Γ → Use↦ d Ψ
         → Expr Γ Ψ (A ⇒[ mk-kind Many π ] B)
-- The spine's head applied: a structure map is applied as a morphism (the
-- compiled `morph-app`), any other head as an arrow.
spineE : ∀ {n} {L : Locals m n} {Γ} {e A T t Ψ₁ Ψ₂} {d : L ⊢ e ⇐ A ⇒[ pure ]↦ T ↝ t} → Shape L Γ
       → Expr Γ Ψ₂ A → Use↦ d Ψ₁ → Expr Γ (Ψ₁ Once.Spec.Context.+ᵘ (Many Once.Spec.Context.*ᵘ Ψ₂)) T

realize⇒ sh (u-int {i})             = int i
realize⇒ sh (u-float {sg} {i} {f} {l}) = float (signedDecimal sg i f l)
realize⇒ sh u-unit                  = unit
realize⇒ sh (u-const {c = c})       = constE c
realize⇒ sh (u-var {v = v})         = subst (Expr _ _) (lookup-shape sh v) (var _)
realize⇒ sh (u-sigop {c = c} k h)   = subst (Expr _ _) (sym (⌜declS⌝ k h)) (sigOp c k)
realize⇒ sh (u-def {d = d} {τ = τ}) = ref d (type (S !! d) ⟨ τ ⟩) (inline d)
realize⇒ sh (u-annot u)             = realize⇐ sh u
realize⇒ sh (u-pair ua ub)          = pair (realize⇒ sh ua) (realize⇒ sh ub)
realize⇒ sh (u-neg {h = h} u)       = num h ‵neg (realize⇒ sh u)
realize⇒ sh (u-let u₁ u₂)           = let' (realize⇒ sh u₁) (realize⇒ (sh-▸ sh) u₂)
realize⇒ sh (u-case {j = j} us ul ur) =
  case' (realize⇒ sh us) (coerce (<:ᶜ⇒<: (left j)) (realize⇒ (sh-▸ sh) ul)) (coerce (<:ᶜ⇒<: (right j)) (realize⇒ (sh-▸ sh) ur))
realize⇒ sh (u-binop {op = op} {A = A} {h = h} u₁ u₂) = numBin op A h (realize⇒ sh u₁) (realize⇒ sh u₂)
realize⇒ sh (u-app {π = π} uf ux)   = appT π (realize⇒ sh uf) (realize⇐ sh ux)
realize⇒ sh (u-app-spine ux uf)     = spineE sh (realize⇒ sh ux) uf

realize⇐ sh (u-map {mo = mo})       = lift-morphism (morphIR mo)
realize⇐ sh (u-map-app {mo = mo} u) = morph-app (morphIR mo) (realize⇐ sh u)
realize⇐ sh (u-compose-g ug uf)     = comp' (realize⇐ sh uf) (realize↦ sh ug)
realize⇐ sh (u-compose-f {p = p} uf ug) = comp' (coerce p (realize⇒ sh uf)) (realize⇐ sh ug)
realize⇐ sh (u-case uf ug)          = copair' (realize⇐ sh uf) (realize⇐ sh ug)
realize⇐ sh (u-pair uf ug)          = fork' (realize⇐ sh uf) (realize⇐ sh ug)
realize⇐ sh (u-curry u)             = curry' (realize⇐ sh u)
realize⇐ sh (u-cata {w = w} u)      = cata w (realize⇐ sh u)
realize⇐ sh (u-ana {fi = fi} u)     = anaE fi (realize⇐ sh u)
realize⇐ sh (u-sub {p = p} u)       = coerce p (realize⇒ sh u)
realize⇐ sh (u-lam {q = q} ≤p u)    = lam q ≤p (realize⇐ (sh-▸ sh) u)
realize⇐ sh (u-pair-lit ua ub)      = pair (realize⇐ sh ua) (realize⇐ sh ub)
realize⇐ sh (u-poly {d = d} {τ = τ}) = ref d (type (S !! d) ⟨ τ ⟩) (inline d)

realize↦ sh (u-infer {B = B} {p = p} {o = o} u) = coerce (sub-arr p (<:-refl B) o) (realize⇒ sh u)
realize↦ sh (u-poly {d = d} {π′ = π′} {A = A} {B = B} {o = o}) =
  coerce (sub-arr {q = Many} (<:-refl A) (<:-refl B) o) (ref d (A ⇒[ mk-kind Many π′ ] B) (inline d))
realize↦ sh (u-lam {q′ = q′} u)     = lam Many (≤q-Many q′) (realize⇒ (sh-▸ sh) u)
realize↦ sh (u-compose ug uf)       = comp' (realize↦ sh uf) (realize↦ sh ug)
realize↦ sh (u-map {mo = mo})       = lift-morphism (morphIR mo)
realize↦ sh (u-case {j = j} uf ug)  =
  copair' (coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (left j)) (⊑π-refl _)) (realize↦ sh uf))
          (coerce (sub-arr (<:-refl _) (<:ᶜ⇒<: (right j)) (⊑π-refl _)) (realize↦ sh ug))
realize↦ sh (u-pair uf ug)          = fork' (realize↦ sh uf) (realize↦ sh ug)
realize↦ sh (u-cata {A = A} {w = w} {p = p} {o = o} u) = cata w (coerce (sub-arr p (<:-refl A) o) (realize⇒ sh u))

spineE sh x (u-map {mo = mo})      = morph-app (morphIR mo) x
spineE sh x u@(u-infer _)          = app (realize↦ sh u) x
spineE sh x u@u-poly               = app (realize↦ sh u) x
spineE sh x u@(u-lam _)            = app (realize↦ sh u) x
spineE sh x u@(u-compose _ _)      = app (realize↦ sh u) x
spineE sh x u@(u-case _ _)         = app (realize↦ sh u) x
spineE sh x u@(u-pair _ _)         = app (realize↦ sh u) x
spineE sh x u@(u-cata _)           = app (realize↦ sh u) x
