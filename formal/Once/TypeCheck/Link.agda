-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Link — linking: a reference to a polymorphic definition is
-- replaced by the definition's body, checked at the reference's instance.
--
-- Compiler code (it runs; the proofs about it are in
-- `TypeCheck.ElaborateProofs` and `Adequacy.ResolveFaithful`).
------------------------------------------------------------------------

module Once.TypeCheck.Link where

open import Data.List using (length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Once.Spec.Context as SCx
open import Once.Spec.Type using (Ty)
open import Once.Spec.Surface.Syntax using (PolyType)
import Once.Spec.Surface.Syntax as Syn
import Once.Spec.Context as Surface
open import Once.Surface.Syntax as Surface using ()
open import Once.TypeCheck.Scope
open import Once.TypeCheck.Classify using (lookupPolyPrefix-decreases; ctxAt; baseKinds; TopCtx)
open import Once.TypeCheck.Elaborate using (checkElab; CheckElabResult; success; failure)

-- Plan 0.103 phase 1c: LINKING. A definition reference `poly x A` is replaced
-- by the definition's body elaborated in ITS DECLARATION CONTEXT — its
-- telescope tail (`lookupPolyPrefix`) and the monomorphic defs declared before
-- it (`impsOf x`) — exactly the context `Spec.Module.PolysTyped` types it in,
-- so a ground definition is compiled as it was typed, once. The spliced term
-- is CLOSED (`closed`), so linking is substitution of closed terms.
resolveExprWF : ∀ {m} {n} {Γ : Surface.Ctx m n} {Ψ : Surface.Usage n} {A : Ty m}
              → (polys : PolyCtx) → Acc _<_ (length polys)
              → (String → TopCtx) → Imports → ℕ
              → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolvePolyCase : ∀ {m} {n} {Γ : Surface.Ctx m n}
                → (polys : PolyCtx) → Acc _<_ (length polys)
                → (String → TopCtx) → Imports → ℕ → (x : String) (A : Ty m)
                → (look : Maybe (PolyType × Syn.Expr × PolyCtx))
                → lookupPolyPrefix polys x ≡ look
                → Surface.Expr Γ Surface.zeroUsage A
applySplice : ∀ {m} {n} {Γ : Surface.Ctx m n}
            → (polys : PolyCtx) → Acc _<_ (length polys)
            → (imps : String → TopCtx) → Imports → ℕ → (x : String) (A : Ty m)
            → {schema : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
            → lookupPolyPrefix polys x ≡ just (schema , body , prefix)
            → CheckElabResult (NamedCtx.debruijn (ctxAt baseKinds (imps x) prefix)) A
            → Surface.Expr Γ Surface.zeroUsage A

resolveExprWF polys _ imps userFns _ (Surface.var i) = Surface.var i
resolveExprWF polys pAcc imps userFns fresh (Surface.lam q prf b) =
  Surface.lam q prf (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.app f a) =
  Surface.app (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh a)
resolveExprWF polys pAcc imps userFns fresh (Surface.effApp {g = g} f a) =
  Surface.effApp {g = g} (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh a)
resolveExprWF polys pAcc imps userFns fresh (Surface.pair a b) =
  Surface.pair (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
-- D127: the combinators resolve componentwise, like `pair`.
resolveExprWF polys pAcc imps userFns fresh (Surface.comp' f g) =
  Surface.comp' (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh g)
resolveExprWF polys pAcc imps userFns fresh (Surface.copair' f g) =
  Surface.copair' (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh g)
resolveExprWF polys pAcc imps userFns fresh (Surface.fork' f g) =
  Surface.fork' (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh g)
resolveExprWF polys pAcc imps userFns fresh (Surface.curry' f) = Surface.curry' (resolveExprWF polys pAcc imps userFns fresh f)
resolveExprWF polys pAcc imps userFns fresh (Surface.fst' p) = Surface.fst' (resolveExprWF polys pAcc imps userFns fresh p)
resolveExprWF polys pAcc imps userFns fresh (Surface.snd' p) = Surface.snd' (resolveExprWF polys pAcc imps userFns fresh p)
resolveExprWF polys pAcc imps userFns fresh (Surface.inl' e) = Surface.inl' (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.inr' e) = Surface.inr' (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.case' s l r) =
  Surface.case' (resolveExprWF polys pAcc imps userFns fresh s)
                (resolveExprWF polys pAcc imps userFns fresh l)
                (resolveExprWF polys pAcc imps userFns fresh r)
resolveExprWF polys pAcc imps userFns fresh (Surface.closed e) = Surface.closed (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys _ imps userFns _ Surface.unit = Surface.unit
resolveExprWF polys pAcc imps userFns fresh (Surface.absurd e) = Surface.absurd (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.let' e₁ e₂) =
  Surface.let' (resolveExprWF polys pAcc imps userFns fresh e₁) (resolveExprWF polys pAcc imps userFns fresh e₂)
resolveExprWF polys _ imps userFns _ (Surface.int z) = Surface.int z
-- A float literal has no names to resolve, exactly like the other literals;
-- the witness passes through untouched.
resolveExprWF polys _ imps userFns _ (Surface.float d) = Surface.float d
resolveExprWF polys pAcc imps userFns fresh (Surface.add a b) =
  Surface.add (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.sub a b) =
  Surface.sub (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.mul a b) =
  Surface.mul (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
resolveExprWF polys pAcc imps userFns fresh (Surface.fadd a b) =
  Surface.fadd (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.fsub a b) =
  Surface.fsub (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.fmul a b) =
  Surface.fmul (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.fdiv a b) =
  Surface.fdiv (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.i2f a) =
  Surface.i2f (resolveExprWF polys pAcc imps userFns fresh a)
resolveExprWF polys pAcc imps userFns fresh (Surface.div a b) =
  Surface.div (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.mod' a b) =
  Surface.mod' (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.neg e) = Surface.neg (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.lt a b) =
  Surface.lt (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.le a b) =
  Surface.le (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.gt a b) =
  Surface.gt (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.ge a b) =
  Surface.ge (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.eq a b) =
  Surface.eq (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.ne a b) =
  Surface.ne (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.coerce p e) = Surface.coerce p (resolveExprWF polys pAcc imps userFns fresh e)
-- Plan 0.19: discriminate sigOp by whether the name is a user-defined
-- top-level fn (in `userFns`) or an external primitive (in `imps`).
-- The typechecker emits `Surface.sigOp` for every named-entry RVar
-- lookup that hits imports; the resolver post-processes by rewriting
-- to `Surface.closure` when the name belongs to the user-defined set,
-- so the elaborator's asm-emission picks the right calling convention.
-- Semantic preservation: `evalSurface (sigOp x) ≡ evalSurface (closure x)`
-- by construction (both go through `generic-semI`); the rewrite is a
-- no-op in the denotation.
-- D246: a module entry's reference is ALREADY a call (`closure`) when it reaches
-- the resolver, so a `sigOp` is a real SigOp (a qualified external or a
-- compiler-minted one) and passes through. (The old sigOp→closure rewrite at a
-- user-fn name is gone, and with it its faithfulness residual — false once a
-- definition's call means its body.)
resolveExprWF polys _ imps userFns _ (Surface.sigOp s conc) = Surface.sigOp s conc
-- Plan 0.19: closure already classified. Pass through unchanged.
resolveExprWF polys _ imps userFns _ (Surface.closure s) = Surface.closure s
-- Plan 0.2.4.5 D2: morphism-realm forms carry CCC IR directly (no
-- polymorphic-def references to splice in). Pass through unchanged.
resolveExprWF polys _ imps userFns _ (Surface.lift-morphism m) = Surface.lift-morphism m
resolveExprWF polys pAcc imps userFns fresh (Surface.morph-app m a) =
  Surface.morph-app m (resolveExprWF polys pAcc imps userFns fresh a)
-- Plan 0.36 Phase 2a: recurse into the cata algebra (empty-context Expr)
-- so its named/poly refs get inlined like any expression. Context-
-- polymorphic, so the ∅-context algebra resolves fine.
resolveExprWF polys pAcc imps userFns fresh (Surface.cata wfF alg) =
  Surface.cata wfF (resolveExprWF polys pAcc imps userFns fresh alg)
-- `ana` (dual of cata): recurse into the coalgebra likewise.
resolveExprWF polys pAcc imps userFns fresh (Surface.ana wfF coalg) =
  Surface.ana wfF (resolveExprWF polys pAcc imps userFns fresh coalg)
-- the loop: recurse into the round likewise.
resolveExprWF polys pAcc imps userFns fresh (Surface.loop round) =
  Surface.loop (resolveExprWF polys pAcc imps userFns fresh round)
-- Poly = unresolved placeholder from Phase 1. Delegate to helper that
-- takes the lookup result + equation explicitly, so external proofs
-- about the sigOp case can `rewrite` the premise cleanly.
resolveExprWF {A = A} polys pAcc imps userFns fresh (Surface.poly x _) =
  resolvePolyCase polys pAcc imps userFns fresh x A (lookupPolyPrefix polys x) refl

resolvePolyCase polys _ imps userFns _ x A nothing _ = Surface.poly x A
resolvePolyCase polys pAcc imps userFns fresh x A (just (_ , body , prefix)) polyEq =
  applySplice polys pAcc imps userFns fresh x A polyEq
              (checkElab (ctxAt baseKinds (imps x) prefix) body A)

-- D254, plan 0.122: the spliced body is the checker's term at the instance.
applySplice polys _ imps userFns _ x A _ (failure _) = Surface.poly x A
applySplice polys (acc rec) imps userFns fresh x A {prefix = prefix} polyEq (success SCx.[] eE _ _) =
  Surface.closed (resolveExprWF prefix (rec (lookupPolyPrefix-decreases x polys polyEq)) imps userFns fresh eE)

-- Public entry. Computes `<-wellFounded` once; no callers need updating.
-- Plan 0.19: `userFns` carries the set of user-defined top-level fn
-- names. The resolver rewrites `Surface.sigOp x` to `Surface.closure x`
-- when `x ∈ userFns` (distinguishing user-defined entries from
-- external primitives). Semantically a no-op (`evalSurface (sigOp x) ≡
-- evalSurface (closure x)` by construction); the rewrite enables the
-- elaborator to emit the correct asm calling convention downstream.
resolveExpr : ∀ {m} {n} {Γ : Surface.Ctx m n} {Ψ : Surface.Usage n} {A : Ty m}
            → (polys : PolyCtx) → (String → TopCtx) → Imports → ℕ
            → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolveExpr polys imps userFns fresh e = resolveExprWF polys (<-wellFounded (length polys)) imps userFns fresh e
