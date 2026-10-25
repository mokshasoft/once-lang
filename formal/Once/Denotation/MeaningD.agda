-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.MeaningD — the implementation-side operations the bridges
-- read: the event-tracking fold, the force of a stream, the constructor, a
-- declaration's reference, all over the Kleisli domain `⟦_⟧ᴰ` (plan 0.122
-- §5.5 M2).
------------------------------------------------------------------------

module Once.Denotation.MeaningD where

import Once.Spec.Type

import Data.Integer as ℤ
import Once.Spec.Word as OnceWord
import Once.Spec.Type as SpT
open import Once.Spec.Type using (∅ₖ; KCtx)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; Base)
open import Once.Spec.Float.Decimal using (decimalOf; round; negate)
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open TargetNum using (int-bits; float-format)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (_++_)

open import Once.Spec.Grade using (Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; Unit; _⇒[_]_)
open import Once.Spec.Type using (μ)
open import Once.Internal.Type.Poly using (extractGround)
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Internal.Name using (showCanonical; WordName)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (id; _$_)
open import Data.Maybe using (just)
open import Once.Internal.Trace using (T; fmapT; Interp; module Interp)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; seqF∞; embed; loop)
open import Once.Internal.StreamInf using (anaFᴵ; module νᴵ)
open νᴵ using (forceᴵ)
open import Data.List.Membership.Propositional using (_∈_)
-- P5: the value-domain vocabulary comes from the IR-free `ValueDomain`
-- (NOT `DenotTrace`, whose `evalᴰ` is implementation).

open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; injectᵇ; forgetᵇ; coerce-functor⁻¹-D; coerce-functor-D)

open import Once.Denotation.DenotTrace using (sigOpT)
open import Once.Denotation.Phase using (lookupᴰUsed)
open import Once.Semantics.Machine using (sem-In; sem-cata; coerce-ν-out; ⟦_⟧F)
open import Once.Internal.Type.WellFormed using (IsConcrete; con-base; con-fun)
open import Once.Spec.Type using (Base; WFFun; b-Unit; ∅ₖ)
import Data.List as L
open import Once.Internal.Context using (Ctx; svar; SVar; Usage; _↾_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; _*ᵘ_; _⊔ᵘ_; zeroUsage) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ; lookup to lookupᵗ)
open import Once.Spec.Context using (_▸_)
open import Once.Internal.Typing.Scope using (NamedCtx; PolyCtx; Imports; lookupImport)
open import Once.Denotation.DefEnv using (DefEnvOf; defAt; ImpEnvOf; impAt)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (semP; int-prim)
open import Once.Spec.Sub using (sub-arr)
open import Once.Spec.Sub using (_⊔_≔_)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open _⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.Internal.Trace using (FFIAnswers)
open SigOpInfo using (conB)
open import Once.Arith.SigOp.Builders
  using (value-info; arrow-info;
         add-info; sub-info; mul-info; div-info; mod-info; neg-info;
         fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info;
         lt-info; le-info; gt-info; ge-info; eq-info; ne-info)

------------------------------------------------------------------------
-- P1 scaffolds (discharged in P2). NAMED and narrow — each is exactly one
-- rule's semantics that needs machinery this file does not yet set up.
------------------------------------------------------------------------

-- m-cata: the event-tracking structural fold, IR-free — a direct-algebra mirror
-- of SD's `cata-ev-algᴰ` (`evalᴰ alg` replaced by the direct algebra `dalg`).
-- DEFINITIONALLY matches `evalᴰ (Cata wf alg)` when `dalg = evalᴰ alg`, so the
-- `bridgeᵈ` cata case reduces to the (recursive) morphism bridge.
-- D179: carrier is a COMPUTATION and the layer is sequenced (`seqF∞`) before
-- the algebra runs, so the children share ONE budget. The `ℕ` is gone — it
-- lives in `T` now. Mirrors `DenotTrace.cata-ev-algᴰ` exactly.
-- Plan 0.105: the layer crosses by the FIRST-ORDER coercion, so it takes the
-- functor's well-formedness (as `DenotTrace.cata-ev-algᴰ` does).
cata-ev-algᴰ-D : ∀ {m} {Δₖ : KCtx m} {F : Fun m} {A : Ty m} → WFFun Δₖ F → (⟦ SpT.⟦ F ⟧F A ⟧ᴰ → T∞ ⟦ A ⟧ᴰ)
               → ⟦ F ⟧F (T∞ ⟦ A ⟧ᴰ) → T∞ ⟦ A ⟧ᴰ
cata-ev-algᴰ-D {F = F} {A = A} wf dalg fc =
  seqF∞ F fc >>=∞ λ layer → dalg (coerce-functor⁻¹-D wf A layer)

-- `⟦ μ-type F ⟧ᴰ` IS the machine's μ (first-order data), so the fold reads it
-- as it is.
cata-sem : ∀ {m} {Δₖ : KCtx m} {F : Fun m} {A : Ty m} → WFFun Δₖ F
         → (⟦ SpT.⟦ F ⟧F A ⟧ᴰ → T∞ ⟦ A ⟧ᴰ) → ⟦ μ F ⟧ᴰ → T∞ ⟦ A ⟧ᴰ
cata-sem {F = F} {A = A} wf dalg v = sem-cata wf (cata-ev-algᴰ-D {F = F} {A = A} wf dalg) v

-- D194: FORCING a layer — the ν's eliminator, and the one place a ν emits.
-- `ana-sem` stores the coalgebra; this is where it runs. Mirrors
-- `evalᴰ (Out wf)` exactly, minus the IRTy transports (those live on the
-- other side of `⌈_⌉`).
out-sem : ∀ {m} {Δₖ : KCtx m} {F : Fun m} {π : Once.Spec.Grade.Finite} → WFFun Δₖ F
        → ⟦ Once.Spec.Type.ν F π ⟧ᴰ → T∞ ⟦ SpT.⟦ F ⟧F (Once.Spec.Type.ν F π) ⟧ᴰ
out-sem {F = F} {π = π} wf v =
  fmap∞ (λ layer → coerce-functor⁻¹-D wf (Once.Spec.Type.ν F π)
                     (coerce-ν-out wf _ layer))
        (forceᴵ v)

-- g-In: the initial-algebra constructor `⟦F⟧T (μF) → μF` at the value level,
-- through the first-order layer coercion (plan 0.105: `forget` is gone; a μ
-- layer holds base values and children only).
in-value : ∀ {m} {Δₖ : KCtx m} {F : Fun m} → WFFun Δₖ F → ⟦ SpT.⟦ F ⟧F (μ F) ⟧ᴰ → ⟦ μ F ⟧ᴰ
in-value {F = F} wf x = sem-In F (coerce-functor-D wf (μ F) x)

-- m-named / m-named-resolved: the named arrow's meaning, IR-free — a pure
-- FFI contract (`value-info` is `ffiV`, plan 0.105), so its value is the
-- interpretation's pure half at the argument.
named-sem : ∀ {A B : Type} → TargetNum → FFIAnswers → CanonicalName → Base ∅ₖ A → Base ∅ₖ B → ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ
named-sem {A = A} {B = B} fmt φ cn bA bB a =
  embed (fmapT (injectᵇ bB) (sigOpT fmt φ (value-info {A} {B} cn bA bB) (forgetᵇ bA a)))

------------------------------------------------------------------------
-- (P3) The env — IR-free positional lookup into `⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ`.
------------------------------------------------------------------------

lookupᴰ : ∀ {m} {n} (Γ : Ctx m n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ lookupᵗ Γ i ⟧ᴰ
lookupᴰ (Γ ▸ A) zero    (dγ , a) = a
lookupᴰ (Γ ▸ A) (suc i) (dγ , a) = lookupᴰ Γ i dγ

svarᴰ : ∀ {m} {n} {Γ : Ctx m n} {A : Ty m} {Ψ} → SVar Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ A ⟧ᴰ
svarᴰ {Γ = Γ} (svar i) dγ = lookupᴰ Γ i dγ

-- A closed named/sigop value reference, IR-free: the contract's computation
-- (`sigOpT`, the IR's own dispatch), read into the value domain.
sigOpValᴰ : ∀ {B : Type} → TargetNum → FFIAnswers → SigOpInfo Unit B → T∞ ⟦ B ⟧ᴰ
sigOpValᴰ fmt φ si = embed (fmapT (injectᵇ (conB si)) (sigOpT fmt φ si tt))

-- An EXTERNAL sigop reference (`t-var-resolved/import`). At an ARROW
-- type the reference is a first-order function POINTER whose effect fires on
-- APPLICATION (`arrow-info` respects the arrow's `Purity`). Split on the
-- WITNESS (not `A`'s shape) so `con-base` reduces at an abstract base `A`.
sigOpRefᴰ : ∀ {A : Type} → TargetNum → FFIAnswers → CanonicalName → IsConcrete A → T∞ ⟦ A ⟧ᴰ
sigOpRefᴰ {A = A} fmt φ cn (con-base ib) = sigOpValᴰ fmt φ (value-info {Unit} {A} cn b-Unit ib)
-- D143: at an ERASED arrow the symbol never receives its argument, so the
-- reference degenerates to the value form, as in `Elaborate` and `SourceDenote`.
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Zero Once.Spec.Grade.pure} bDom bCod) =
  return∞ (λ _ → sigOpValᴰ fmt φ (value-info cn b-Unit bCod))
-- plan 0.113 A3: only a PURE erased arrow is a value; an effectful one is a call
-- with the erased slot `tt` (as `Elaborate` and `SourceDenote`).
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Zero Once.Spec.Grade.eff} bDom bCod) =
  return∞ (λ _ → embed (fmapT (injectᵇ bCod) (sigOpT fmt φ (arrow-info {Unit} {Cod} (mk-kind Zero Once.Spec.Grade.eff) cn b-Unit bCod) tt)))
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Zero Once.Spec.Grade.act} bDom bCod) =
  return∞ (λ _ → embed (fmapT (injectᵇ bCod) (sigOpT fmt φ (arrow-info {Unit} {Cod} (mk-kind Zero Once.Spec.Grade.act) cn b-Unit bCod) tt)))
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One π} bDom bCod) =
  return∞ (λ arg → embed (fmapT (injectᵇ bCod) (sigOpT fmt φ (arrow-info {Dom} {Cod} (mk-kind One π) cn bDom bCod) (forgetᵇ bDom arg))))
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many π} bDom bCod) =
  return∞ (λ arg → embed (fmapT (injectᵇ bCod) (sigOpT fmt φ (arrow-info {Dom} {Cod} (mk-kind Many π) cn bDom bCod) (forgetᵇ bDom arg))))

