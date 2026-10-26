-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.SurfaceRefs — the references of a surface term (plan
-- 0.103 6a‴; plan 0.122 §5.6: the checker proves its term's).
--
-- `Refs Ps Pc Pp e`: every FFI reference, call and spliced telescope
-- reference in `e` satisfies its predicate, and every embedded IR morphism is
-- call-free. In a scope (`InScope`): each is one the scope declares — a
-- declaration of its signature at its type, an import at its type, a
-- telescope definition at a kinded instance of its schema.
------------------------------------------------------------------------

module Once.Denotation.SurfaceRefs where

open import Data.Unit using (⊤)
open import Data.List using ([])
open import Data.Product using (_×_; Σ)
open import Data.Maybe using (just)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Name using (CanonicalName)
open import Once.Name using (showCanonical)
open import Once.Spec.Type using (Ty; Type; KCtx)
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Type.Core using (wk₀)
open import Once.Type.Instance using (KindedInstance)
open import Once.TypeCheck.Scope using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Context hiding (_,_)
open import Once.Spec.Context using (Ctx; Usage)
open import Once.Surface.Context
open import Once.Surface.Syntax
open import Once.Denotation.Program using (Linked)

-- `Refs Ps Pc Pp e`: every `closure x : A` in `e` satisfies `Pc x A`, every
-- `poly x A` satisfies `Pp x A`, and every embedded IR morphism is call-free.
Refs : ∀ {m} → (Ps : CanonicalName → Type → Set) (Pc Pp : String → Ty m → Set) → ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → Expr Γ Ψ A → Set
Refs Ps Pc Pp (var _)             = ⊤
Refs Ps Pc Pp (lam _ _ b)         = Refs Ps Pc Pp b
Refs Ps Pc Pp (app f x)           = Refs Ps Pc Pp f × Refs Ps Pc Pp x
Refs Ps Pc Pp (effApp f x)        = Refs Ps Pc Pp f × Refs Ps Pc Pp x
Refs Ps Pc Pp (pair a b)          = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (fst' p)            = Refs Ps Pc Pp p
Refs Ps Pc Pp (snd' p)            = Refs Ps Pc Pp p
Refs Ps Pc Pp (inl' a)            = Refs Ps Pc Pp a
Refs Ps Pc Pp (inr' a)            = Refs Ps Pc Pp a
Refs Ps Pc Pp (case' s l r)       = Refs Ps Pc Pp s × Refs Ps Pc Pp l × Refs Ps Pc Pp r
Refs Ps Pc Pp unit                = ⊤
Refs Ps Pc Pp (absurd e)          = Refs Ps Pc Pp e
Refs Ps Pc Pp (let' e₁ e₂)        = Refs Ps Pc Pp e₁ × Refs Ps Pc Pp e₂
Refs Ps Pc Pp (int _)             = ⊤
Refs Ps Pc Pp (float _)           = ⊤
Refs Ps Pc Pp (add a b)           = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (sub a b)           = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (mul a b)           = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (fadd a b)          = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (fsub a b)          = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (fmul a b)          = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (fdiv a b)          = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (i2f a)             = Refs Ps Pc Pp a
Refs Ps Pc Pp (div a b)           = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (mod' a b)          = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (neg a)             = Refs Ps Pc Pp a
Refs Ps Pc Pp (lt a b)            = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (le a b)            = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (gt a b)            = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (ge a b)            = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (eq a b)            = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (ne a b)            = Refs Ps Pc Pp a × Refs Ps Pc Pp b
Refs Ps Pc Pp (coerce _ e)        = Refs Ps Pc Pp e
-- plan 0.105: every FFI reference satisfies `Ps` (in the end: it is declared in
-- the signatures the program is compiled against, D257 amendment 2).
Refs Ps Pc Pp (sigOp {A = A} name _) = Ps name A
Refs Ps Pc Pp {A = A} (closure x) = Pc x A
Refs Ps Pc Pp (poly x T)          = Pp x T
Refs Ps Pc Pp (closed e)          = Refs Ps Pc Pp e
Refs Ps Pc Pp (lift-morphism m)   = Linked [] [] m
Refs Ps Pc Pp (morph-app m a)     = Linked [] [] m × Refs Ps Pc Pp a
Refs Ps Pc Pp (comp' f g)         = Refs Ps Pc Pp f × Refs Ps Pc Pp g
Refs Ps Pc Pp (copair' f g)       = Refs Ps Pc Pp f × Refs Ps Pc Pp g
Refs Ps Pc Pp (fork' f g)         = Refs Ps Pc Pp f × Refs Ps Pc Pp g
Refs Ps Pc Pp (curry' f)          = Refs Ps Pc Pp f
Refs Ps Pc Pp (cata _ alg)        = Refs Ps Pc Pp alg
Refs Ps Pc Pp (ana _ coalg)       = Refs Ps Pc Pp coalg
Refs Ps Pc Pp (loop round)        = Refs Ps Pc Pp round


------------------------------------------------------------------------
-- In a scope
------------------------------------------------------------------------

-- A declaration of the scope's signature, at its type.
FFIRef : Imports → CanonicalName → Type → Set
FFIRef sg c A = lookupImport sg (showCanonical c) ≡ just A

-- An import, at its type.
ImpRef : ∀ {m} → Imports → String → Ty m → Set
ImpRef imps x A = Σ Type (λ T → (lookupImport imps x ≡ just T) × (A ≡ wk₀ T))

-- A telescope definition, at a kinded instance of its schema.
PolyRef : ∀ {m} → PolyCtx → KCtx m → String → Ty m → Set
PolyRef polys Δ x A = Σ (PolyType × Once.Spec.Surface.Syntax.Expr × PolyCtx) (λ r → (lookupPolyPrefix polys x ≡ just r) × KindedInstance Δ (Data.Product.proj₁ r) A)
  where import Data.Product

InScope : ∀ {m} → (ctx : NamedCtx m) → ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → Expr Γ Ψ A → Set
InScope ctx = Refs (FFIRef (NamedCtx.sig ctx)) (ImpRef (NamedCtx.imports ctx)) (PolyRef (NamedCtx.polys ctx) (NamedCtx.kinds ctx))
