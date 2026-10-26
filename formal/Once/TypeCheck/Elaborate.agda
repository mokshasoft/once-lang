-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Elaborate
--
-- THE CHECKER IS PLAIN CODE (plan 0.122 §7, D340): it returns its result —
-- the elaborated term, or the error — and nothing else. That the result is
-- the Spec's derivation is a theorem about it, `TypeCheck.ElaborateSound`,
-- by the same patterns; it is type-checked, never extracted (D334). A rule
-- named below (`wt-…`, `wd-…`) is the Spec rule the clause's soundness uses.
--
-- Combined type inference and elaboration.
-- Produces intrinsically-typed Surface.Syntax.Expr directly from Syn.Expr.
--
-- This avoids the problem with separate Resolve step needing subexpression
-- types that aren't available.
--
-- Part of OCP-0004: MAlonzo Compiler Replacement
------------------------------------------------------------------------

module Once.TypeCheck.Elaborate where

import Once.Spec.Context
open import Once.Type.Core using (wk₀)
open import Once.Spec.Type using (μ; ν; ⟦_⟧F)
open import Once.Spec.Type using (var; Ty; KCtx; Base)
open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Integer using (ℤ; -_)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc)
open import Data.Fin using (zero; suc)
open import Data.Bool using (Bool; true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Type.Core
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PInt; PFloat; PTVar)
open import Once.Type.Poly
open import Once.Type
-- Plan 0.52 M2: IR re-exports the ungraded IRTy, whose Unit/K/μ-type/… clash
-- with Once.Type's (opened above). Hide the IRTy object/functor constructors
-- from the unqualified open (they stay available as `IR.*`); the surface-type
-- names resolve unambiguously to `Once.Type`.
open import Once.IR as IR
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Spec.Name using (CanonicalName; canonical; own; bare; gen; NotGenerator; GenWord)
open import Once.Name using (showCanonical; WordName; wordNameB)
open import Once.CanonicalName using (genWord?)
import Once.Spec.Surface.Syntax as Syn
open import Once.Spec.Surface.Syntax as Raw using (BinOp; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.TypeCheck.Raw using (isComparisonOp; isArithmeticOp; isFloatArithmeticOp)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Error using (TypeError; ComposeMiddleUndetermined; AnnotationMentionsParameter;
  LambdaInInferMode; LambdaRequiresFunctionType;
  InlInInferMode; InrInInferMode; InitialInInferMode;
  InlNeedsSumType; InrNeedsSumType;
  FstNeedsPair; SndNeedsPair;
  CaseScrutineeNotSum; CaseBranchMismatch; TypeMismatch; NotFunction;
  UsageViolation; BuiltinTypeMismatch;
  BinOpLeftError; BinOpRightError;
  UnboundVariable; UnboundQualified; NonConcreteSigOpType)
import Once.TypeCheck.Context
open import Once.Context as Surface using ()
import Once.Spec.Context as Surface
open import Once.Spec.Context using () renaming (Ctx to SCtx; ∅ to S∅)
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)
open import Once.Spec.Context using () renaming (_∷_ to _∷ᵘ_)
open import Once.Surface.Elaborate as Elab using ()

open import Once.TypeCheck.Scope
open import Once.TypeCheck.Classify
import Once.Type.Concrete
open import Once.Spec.Type using (Base; ∅ₖ)
import Once.Spec.Type
open import Once.Type.Concrete using (IsConcrete; con-fun)
open import Once.Functor.Decide using (wellFormedF?; wfFun?; isConcrete?; isBaseType?)
open import Once.Spec.Float.Decimal using (decimalOf)
import Once.Spec.Float.Decimal as Decimal
open import Once.Spec.Sub using (_<:_; sub-arr)
open import Once.Spec.Grade using (_⊑π_)
open import Once.Type.SubDecide using (_<:?_; _⊑π?_)
open import Once.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Join using (Join?; joined; apart; join?; sound)
open Once.Spec.Sub._⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)
open import Once.Type.Match using (Subst; instantiate)
open import Once.Type.MatchCorrect using (instantiate-sound)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Rigid using (kindedInstance?)
open import Once.Type.Determined using (ArrowView; arrowSchema?; codVarsInDom?)
open import Once.TypeCheck.DeciderComplete using (isGround-complete-at)
open import Once.TypeCheck.TargetView

------------------------------------------------------------------------
-- Type Equality (Decidable with proof)
------------------------------------------------------------------------

-- Plan 0.99: decidable Functor/Type equality lives in `Once.Type.DecEq`.

-- | Decide whether `T` is a pure-arrow-to-`Int` — the value-lift target for
-- an integer literal (Plan 0.41 / D018). Returning the equality witness as a
-- `just`/`nothing` gives `checkElabV (RInt n) T` ONE named scrutinee to route
-- through, instead of a specific-arrow clause overlapping the generic
-- catch-all (which left `checkElabV (RInt n) T` stuck for variable `T`, and
-- made `ErrorProofs`' "RInt at T≠Int fails" claim false). Proofs — and the
-- Plan 0.45 frontend trace induction — `with isRIntVliftTarget? T` to dispatch.
-- D069: grade-poly — a constant `Int` value inhabits `X ⇒[Many π] Int` at ANY π.
isRIntVliftTarget? :
  (T : Type) →
  Maybe (∃-syntax (λ X → ∃-syntax (λ π → T ≡ (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Int))))
isRIntVliftTarget? (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Int) =
  just (X , π , refl)
{-# CATCHALL #-}
isRIntVliftTarget? _ = nothing

-- …and the same view for a float literal. `gd-completeV` is what forces this
-- to exist: without it, `g-float` at a pure-arrow-to-Float target would take
-- the generic infer-and-match path and report a TypeMismatch, so the value
-- realm would accept a derivation the checker rejects — completeness false in
-- the same direction the acceptance premise fixes elsewhere.
isRFloatVliftTarget? :
  (T : Type) →
  Maybe (∃-syntax (λ X → ∃-syntax (λ π → T ≡ (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Once.Spec.Type.Float))))
isRFloatVliftTarget? (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Once.Spec.Type.Float) =
  just (X , π , refl)
{-# CATCHALL #-}
isRFloatVliftTarget? _ = nothing

-- | Classify a check-mode target type for a pair literal: a product `A * B`
-- (bidirectional component check), a pure-arrow-to-product
-- `X ⇒[Many,pure] (A * B)` (value-lift / global element via `checkG`), or
-- anything else (generic infer-and-match). One named view so
-- `checkElabV (RPair a b) T` routes through a single scrutinee instead of two
-- specific clauses overlapping the catch-all (same gate as RInt; Plan 0.45).
data RPairTarget {m} : Ty m → Set where
  rpt-prod  : (A B : Ty m) → RPairTarget (A Once.Spec.Type.* B)
  -- D069: grade-poly — a closed pair value inhabits the arrow at any π.
  rpt-vlift : (X A B : Ty m) (π : Once.Spec.Grade.Purity) →
              RPairTarget (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] (A Once.Spec.Type.* B))
  rpt-other : (T : Ty m) → RPairTarget T

classifyRPairTarget : ∀ {m} → (T : Ty m) → RPairTarget T
classifyRPairTarget (A Once.Spec.Type.* B) = rpt-prod A B
classifyRPairTarget
  (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] (A Once.Spec.Type.* B)) =
  rpt-vlift X A B π
{-# CATCHALL #-}
classifyRPairTarget T = rpt-other T

------------------------------------------------------------------------
-- PolyType Equality (for type checking during inference)
------------------------------------------------------------------------

-- | Decidable PolyFunctor and PolyType equality (mutually recursive)
-- Type Matching with Unification (for polymorphic inference)
------------------------------------------------------------------------

-- | Check if two PolyTypes can be unified
-- Returns the result type (with TVars replaced) and an updated substitution
--
-- Simpler than full unification: TVars match anything, and we return
-- the more concrete type.
--
-- For `matches expected actual`:
-- - If expected is a TVar, return actual (TVar gets instantiated)
-- - If actual is a TVar, return expected (shouldn't happen in well-typed code)
-- - Otherwise, check structural equality
--
------------------------------------------------------------------------
-- Bidirectional Type Checking Results
------------------------------------------------------------------------

-- | Result of type inference (compute the type)
-- The usage vector Ψ is now part of the SExpr's type index — linearity is
-- by construction, not a side field.
data InferElabResult {m} {n : ℕ} (Δ : SCtx m n) : Set where
  success : (A : Ty m) (Ψ : Surface.Usage n) → SExpr Δ Ψ A
          → (depth : ℕ) → (fresh : ℕ)
          → InferElabResult Δ
  failure : TypeError → InferElabResult Δ

-- | Result of type checking (verify against expected type)
data CheckElabResult {m} {n : ℕ} (Δ : SCtx m n) (A : Ty m) : Set where
  success : (Ψ : Surface.Usage n) → SExpr Δ Ψ A
          → (depth : ℕ) → (fresh : ℕ)
          → CheckElabResult Δ A
  failure : TypeError → CheckElabResult Δ A

-- | WHICH literal, if any, is this unary minus applied to? (`RInt`: plan 0.74
-- J6 step 3, D120. `RFloat`: plan 0.73 F3.)
--
-- Indexed by `e`, so matching `nov-int n` rewrites `e` to `Raw.RInt n` and the
-- dispatch can build `wt-neg (wt-int n)` — the same refinement the earlier
-- `Maybe (Σ ℤ (λ n → e ≡ Raw.RInt n))` carried by hand.
--
-- ONE view, not two `Maybe`s. Two would make every downstream proof split on a
-- four-cell matrix whose fourth cell — `e` both an `RInt` and an `RFloat` —
-- cannot occur, with nothing in the types saying so. Three constructors, three
-- cases, no absurd cell.
--
-- `Syn.Expr` is a plain datatype, so the catch-all is safe: it reduces for every
-- concrete head, and the caller never matches on `e`. (Non-exact under
-- `--exact-split`, as its `isRIntView` predecessor was; see the census target.)
data NegOperandView : Syn.Expr → Set where
  nov-int   : (n : ℤ)       → NegOperandView (Raw.RInt n)
  nov-float : (i f l : ℕ) → NegOperandView (Raw.RFloat i f l)
  nov-other : (e : Syn.Expr) → NegOperandView e

negOperandView : (e : Syn.Expr) → NegOperandView e
negOperandView (Raw.RInt n)         = nov-int n
negOperandView (Raw.RFloat i f l) = nov-float i f l
{-# CATCHALL #-}
negOperandView e                    = nov-other e


-- Plan 0.94 §10: the DOMAIN-GIVEN mode — given the input type `A` (and grade),
-- the output type `B` is the elaborator's answer, witnessed by `⊢ᵈ`.
data GivenElabResult {m} {n : ℕ} (Δ : SCtx m n) (A : Ty m) (π : Once.Spec.Grade.Purity) : Set where
  success : (B : Ty m) (Ψ : Surface.Usage n)
          → SExpr Δ Ψ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
          → (depth : ℕ) → (fresh : ℕ)
          → GivenElabResult Δ A π
  failure : TypeError → GivenElabResult Δ A π


-- The `wd-infer` step: an inferred arrow, its domain converted backwards and its
-- grade raised. Every decision is an ARGUMENT, so a proof can reduce this.
given-infer-dec : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (A A′ B : Ty m) (π π′ : Once.Spec.Grade.Purity)
                    {Ψ : Surface.Usage (NamedCtx.size ctx)}
                → (eE : SExpr (NamedCtx.debruijn ctx) Ψ (A′ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B))
                → (depth fresh : ℕ)
                → Dec (A <: A′) → Dec (π′ ⊑π π) → GivenElabResult (NamedCtx.debruijn ctx) A π
given-infer-dec ctx e A A′ B π π′ eE d fr (yes a) (yes g) =
  success B _ (Surface.coerce (sub-arr {q = Once.Spec.Grade.Many} a (<:-refl B) g) eE) d fr
given-infer-dec ctx e A A′ B π π′ eE d fr (no _) _ =
  failure (TypeMismatch (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
                        (A′ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B))
given-infer-dec ctx e A A′ B π π′ eE d fr (yes _) (no _) =
  failure (TypeMismatch (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
                        (A′ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B))

-- The inferred result, viewed: only a `Many` arrow has a determined output.
given-infer : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
            → InferElabResult (NamedCtx.debruijn ctx) → GivenElabResult (NamedCtx.debruijn ctx) A π
given-infer ctx e A π (failure err) = failure err
given-infer ctx e A π (success (A′ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B) Ψ eE d fr) =
  given-infer-dec ctx e A A′ B π π′ eE d fr (A <:? A′) (π′ ⊑π? π)
{-# CATCHALL #-}
given-infer ctx e A π (success T Ψ eE d fr) = failure ComposeMiddleUndetermined

-- A rule that builds a VALUE at an arrow's grade needs the grade's unit
-- (`pure ⊑π π`). Decided once, here.
withUnit : ∀ {R : Set} → R → (π : Once.Spec.Grade.Purity) → (Once.Spec.Grade.pure ⊑π π → R) → R
withUnit-aux : ∀ {R : Set} {π} → R → Dec (Once.Spec.Grade.pure ⊑π π) → (Once.Spec.Grade.pure ⊑π π → R) → R
withUnit-aux r (yes u) k = k u
withUnit-aux r (no _)  k = r
withUnit r π k = withUnit-aux r (Once.Spec.Grade.pure ⊑π? π) k

-- The `wd-cata` step: the algebra's synthesized arrow must be `⟦ F ⟧T A ⇒ A` at
-- the given grade; then its codomain `A` is the fold's output.
given-cata-dec : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity)
                   (wfF : Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F) (X A : Ty m) (k : Once.Spec.Grade.ArrowKind)
                   (Ψ : Surface.Usage (NamedCtx.size ctx))
               → (algE : SExpr (NamedCtx.debruijn ctx) Ψ (X Once.Spec.Type.⇒[ k ] A))
               → (depth : ℕ) → (fr : ℕ)
               → Dec ((X Once.Spec.Type.⇒[ k ] A)
                        ≡ (⟦ F ⟧F A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A))
               → GivenElabResult (NamedCtx.debruijn ctx) (Once.Spec.Type.μ F) π
given-cata-dec ctx alg F π wfF X A k Ψ algE d fr (yes refl) = withUnit (failure (BuiltinTypeMismatch "cata")) π λ u →
  success A (Once.Spec.Grade.Many Surface.*ᵘ Ψ) (Surface.cata wfF algE) (suc d) fr
given-cata-dec ctx alg F π wfF X A k Ψ algE d fr (no _) = failure (BuiltinTypeMismatch "cata")

given-cata : ∀ {m} (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity)
               (wfF : Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F)
           → InferElabResult (NamedCtx.debruijn ctx)
           → GivenElabResult (NamedCtx.debruijn ctx) (Once.Spec.Type.μ F) π
given-cata ctx alg F π wfF (failure err) = failure err
given-cata ctx alg F π wfF (success (X Once.Spec.Type.⇒[ k ] A) Ψ algE d fr) =
  given-cata-dec ctx alg F π wfF X A k Ψ algE d fr
    ((X Once.Spec.Type.⇒[ k ] A) ≟T (⟦ F ⟧F A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A))
{-# CATCHALL #-}
given-cata ctx alg F π wfF (success _ _ _ _ _) = failure (BuiltinTypeMismatch "cata")


-- The universal "infer-then-check" combinator — THE MODE SWITCH (D226 / plan
-- 0.99). Given the expected check type `T` and the result of inferring `e`, it
-- succeeds exactly when the inferred `T'` is a SUBTYPE of `T`, emitting the
-- conversion (`coerce p`); its soundness is `wt-sub`. Equal types are the
-- reflexive instance (the former `t-embed`); pure ⊑ eff is the grade instance
-- (the former `t-subsume`); `Void <: T` is what lets `exit@S x` stand where
-- `Unit` is expected. Every check-mode "fall back to infer" site routes through
-- here, so conversion is uniform and `check-complete` has a single bridge.
-- The decision is an ARGUMENT (not a `with`), so a proof holding an abstract
-- inferred type can still reduce this.
embedOrSubsume-dec : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr)
                       {Ψ : Surface.Usage (NamedCtx.size ctx)} (T T' : Ty m)
                   → (eE : SExpr (NamedCtx.debruijn ctx) Ψ T') → (depth fresh : ℕ)
                   → Dec (T' <: T) → CheckElabResult (NamedCtx.debruijn ctx) T
embedOrSubsume-dec ctx e T T' eE depth fresh (yes p) = success _ (Surface.coerce p eE) depth fresh
embedOrSubsume-dec ctx e T T' eE depth fresh (no _)  = failure (TypeMismatch T T')

embedOrSubsume : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
               → InferElabResult (NamedCtx.debruijn ctx) → CheckElabResult (NamedCtx.debruijn ctx) T
embedOrSubsume ctx e T (failure err) = failure err
embedOrSubsume ctx e T (success T' Ψ eE d fr) = embedOrSubsume-dec ctx e T T' eE d fr (T' <:? T)

------------------------------------------------------------------------
-- QTT Usage Helpers
------------------------------------------------------------------------

-- Import usage operations from Surface.Syntax

------------------------------------------------------------------------
-- Per-Builtin Body Specializers
------------------------------------------------------------------------
--
-- The 13 builtin generators have known polymorphic bodies. Rather than
-- writing a generic PolyExpr→Expr specialization walk, we produce each
-- builtin's specialized body directly given the ground type arguments.
-- This is more principled: each builtin's body is a fixed small term
-- and its specialization is a one-line function over ground types.

-- Plan 0.2.4.5 D2: morphism-realm spec helpers.
--
-- Each builtin's specialization is now a `lift-morphism` wrapping the
-- corresponding CCC primitive, instead of a Surface lambda body.
-- Combined with `morph-app` at the application sites (see specX-app
-- below), this routes "categorical-style" code (id, fst, snd,
-- terminal, initial, compose chains) directly to the morphism realm:
-- pure CCC compose at elaborate time, no closure record, no apply, no
-- dangling-pointer apply-chain bug.

specId : ∀ {m} → (T : Ty m) → SExpr S∅ Surface.zeroUsage (T ⇒ T)
specId T = Surface.lift-morphism IR.id

specFst : ∀ {m} → (A B : Ty m) → SExpr S∅ Surface.zeroUsage (A Once.Spec.Type.* B ⇒ A)
specFst A B = Surface.lift-morphism IR.fst

specSnd : ∀ {m} → (A B : Ty m) → SExpr S∅ Surface.zeroUsage (A Once.Spec.Type.* B ⇒ B)
specSnd A B = Surface.lift-morphism IR.snd

specInl : ∀ {m} → (A B : Ty m) → SExpr S∅ Surface.zeroUsage (A ⇒ (A Once.Spec.Type.+ B))
specInl A B = Surface.lift-morphism (IR.inl)

specInr : ∀ {m} → (A B : Ty m) → SExpr S∅ Surface.zeroUsage (B ⇒ (A Once.Spec.Type.+ B))
specInr A B = Surface.lift-morphism (IR.inr)

specUnitGen : SExpr (Once.Spec.Context.∅ {0}) Surface.zeroUsage Unit
specUnitGen = Surface.unit

-- pair : (a → b) → (a → c) → a → (b × c)
specPair : ∀ {m} → (A B C : Ty m)
         → SExpr S∅ Surface.zeroUsage ((A ⇒ B) ⇒ (A ⇒ C) ⇒ A ⇒ (B Once.Spec.Type.* C))
specPair A B C =
  Surface.lam Many refl (Surface.lam Many refl (Surface.lam Many refl
    (Surface.pair
      (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero))
      (Surface.app (Surface.var (suc zero)) (Surface.var zero)))))

-- terminal : a → Unit
specTerminal : ∀ {m} → (A : Ty m) → SExpr S∅ Surface.zeroUsage (A ⇒ Unit)
specTerminal A = Surface.lift-morphism IR.terminal

-- initial : Void → a
specInitial : ∀ {m} → (A : Ty m) → SExpr S∅ Surface.zeroUsage (Void ⇒ A)
specInitial A = Surface.lift-morphism IR.initial

-- curry : ((a × b) → c) → a → b → c
specCurry : ∀ {m} → (A B C : Ty m)
          → SExpr S∅ Surface.zeroUsage ((A Once.Spec.Type.* B ⇒ C) ⇒ A ⇒ B ⇒ C)
specCurry A B C =
  Surface.lam Many refl (Surface.lam Many refl (Surface.lam Many refl
    (Surface.app (Surface.var (suc (suc zero)))
                 (Surface.pair (Surface.var (suc zero)) (Surface.var zero)))))

-- apply : ((a → b) × a) → b
specApply : ∀ {m} → (A B : Ty m)
          → SExpr S∅ Surface.zeroUsage (((A ⇒ B) Once.Spec.Type.* A) ⇒ B)
specApply A B =
  Surface.lam Many refl
    (Surface.app (Surface.fst' (Surface.var zero))
                 (Surface.snd' (Surface.var zero)))

-- compose : (b → c) → (a → b) → a → c
specCompose : ∀ {m} → (A B C : Ty m)
            → SExpr S∅ Surface.zeroUsage ((B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
specCompose A B C =
  Surface.lam Many refl (Surface.lam Many refl (Surface.lam Many refl
    (Surface.app (Surface.var (suc (suc zero)))
                 (Surface.app (Surface.var (suc zero)) (Surface.var zero)))))

-- case (copair) : (a → c) → (b → c) → (a + b) → c
-- Closure-realm fallback for `case f g` when the arms are not
-- morphism-realm values (the morphism-realm fast-path emits
-- `lift-morphism (IR.case m_f m_g)` directly; see `checkCase`).
-- Body: λ f. λ g. λ s. case' s (f x) (g y).
specCase : ∀ {m} → (A B C : Ty m)
         → SExpr S∅ Surface.zeroUsage ((A ⇒ C) ⇒ (B ⇒ C) ⇒ (A Once.Spec.Type.+ B) ⇒ C)
specCase A B C =
  Surface.lam Many refl (Surface.lam Many refl (Surface.lam Many refl
    (Surface.case' (Surface.var zero)
      (Surface.app (Surface.var (suc (suc (suc zero)))) (Surface.var zero))
      (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero)))))

------------------------------------------------------------------------
-- Plan 0.2.4.5 D2: morphism-realm extractor
--
-- Recognise a Surface expression that is a `lift-morphism m`,
-- returning the underlying CCC IR. Used by `checkComposeWithBg` to
-- emit `lift-morphism (m_f ∘ m_g)` directly when both arms of
-- `compose f g` are morphism-realm values, bypassing the closure-
-- realm `app (app specCompose f) g` form.
--
-- Implementation note (`feedback_generic_codomain_trick`): a direct
-- `extract-morph (lift-morphism m) = just m / _ = nothing` definition
-- hits an Agda SplitError because `var i`'s opaque index `lookup Γ i`
-- can't be unified against `A ⇒ B`. The codomain trick parameterises
-- over a free type T plus an equality proof T ≡ A ⇒ B, which lets
-- the catch-all wildcard sidestep the dependent-pattern obligation.
------------------------------------------------------------------------

-- The `Σ`-result pairs the IR with `Ψ ≡ zeroUsage` because
-- `lift-morphism`'s constructor type forces Ψ = zeroUsage on success.
-- Callers use the equation to discharge usage-mismatch obligations
-- when bridging the bypass form to a judgment whose claimed usage
-- depends on the discarded inputs' Ψ.
-- Plan 0.36 Phase 1: grade-polymorphic — extracts the IR from a
-- `lift-morphism m` at ANY purity π (pure callers infer π = pure). The grade
-- rides in the arrow; the extracted `IR A B` is grade-erased.
extract-morph-aux : ∀ {mₜ} {n} {Γ : SCtx mₜ n} {Ψ : Surface.Usage n} {T : Ty mₜ} {A B : Ty mₜ}
                    {π : Once.Spec.Grade.Purity}
                  → SExpr Γ Ψ T
                  → T ≡ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
                  → Maybe (∃-syntax (λ (m : IR ⌊ A ⌋ ⌊ B ⌋) → Ψ ≡ Surface.zeroUsage))
extract-morph-aux (Surface.lift-morphism m) refl = just (m , refl)
{-# CATCHALL #-}
extract-morph-aux _ _ = nothing

extract-morph : ∀ {mₜ} {n} {Γ : SCtx mₜ n} {Ψ : Surface.Usage n} {A B : Ty mₜ}
                {π : Once.Spec.Grade.Purity}
              → SExpr Γ Ψ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
              → Maybe (∃-syntax (λ (m : IR ⌊ A ⌋ ⌊ B ⌋) → Ψ ≡ Surface.zeroUsage))
extract-morph e = extract-morph-aux e refl

-- D127/D131: `extract-morph-eff` and `extract-morph-eff-aux` are DELETED.
-- They recovered a closed `IR` morphism out of an already-elaborated term, so
-- that a `compose`/`case`/`cata` arm could be re-read as a morphism. Both
-- reasons are gone: arms are ordinary context-indexed terms (D127), and the
-- cata algebra is a closure the fold carries rather than a morphism inlined
-- into it (D131). `Once.TypeCheck.Completeness` still names them and loses
-- them with its own D127 rework.


-- View bundling `wellFormedF? F`'s outcome with its equation (mirrors
-- `inspectLookupLocal`) so proofs sidestep the `with … in` opacity.
data WellFormedFView {m} (Δ : Once.Spec.Type.KCtx m) (F : Once.Spec.Type.Fun m) : Set where
  wfv-yes : ∀ {wfF} → wfFun? Δ F ≡ just wfF → WellFormedFView Δ F
  wfv-no  : wfFun? Δ F ≡ nothing → WellFormedFView Δ F

inspectWellFormedF : ∀ {m} (Δ : Once.Spec.Type.KCtx m) (F : Once.Spec.Type.Fun m) → WellFormedFView Δ F
inspectWellFormedF Δ F with wfFun? Δ F in eq
... | just wfF = wfv-yes eq
... | nothing  = wfv-no eq


-- | Look up a variable by name and return its de Bruijn indexed expression
--
-- Priority order:
-- 1. Local context (bound variables)
-- 2. Built-in generators (id, fst, snd, etc.)
-- 3. Imported primitives (from qualified imports)
------------------------------------------------------------------------
-- New Ground Inference (Phase B: wired-up alongside old)
------------------------------------------------------------------------
--
-- These functions implement bidirectional type-checking producing ground
-- Type and SExpr directly, without going through PolyExpr or InferSubst.
-- Polymorphic builtins are specialized at their use site via spine
-- detection of App chains whose head is a builtin name.
--
-- The new implementation is additive; old code is retained until
-- coverage is complete and the switch is made.

-- | Walk the left spine of Raw.RApp to extract the head and argument list.
record AppSpine : Set where
  constructor mkSpine
  field
    head : Syn.Expr
    args : List Syn.Expr

spineOf : Syn.Expr → AppSpine
spineOf e = go e []
  where
    go : Syn.Expr → List Syn.Expr → AppSpine
    go (Raw.RApp f x)        args = go f (x ∷ args)
    go (Raw.RVar n)          args = mkSpine (Raw.RVar n) args
    go (Raw.RQualified m n)  args = mkSpine (Raw.RQualified m n) args
    go (Raw.RResolved cn)    args = mkSpine (Raw.RResolved cn) args
    go (Raw.RLam x b)        args = mkSpine (Raw.RLam x b) args
    go (Raw.RLet x e₁ e₂)    args = mkSpine (Raw.RLet x e₁ e₂) args
    go (Raw.RPair x y)       args = mkSpine (Raw.RPair x y) args
    go (Raw.RDestruct e a b c d) args = mkSpine (Raw.RDestruct e a b c d) args
    go Raw.RUnit             args = mkSpine Raw.RUnit args
    go (Raw.RInt n)          args = mkSpine (Raw.RInt n) args
    go (Raw.RFloat i f l)    args = mkSpine (Raw.RFloat i f l) args
    go (Raw.RAnnot e t)      args = mkSpine (Raw.RAnnot e t) args
    go (Raw.RBinOp op x y)   args = mkSpine (Raw.RBinOp op x y) args
    go (Raw.RNeg x)   args = mkSpine (Raw.RNeg x) args

-- | Is this name one of the 13 polymorphic builtins?
isPolyBuiltin : String → Bool
isPolyBuiltin "id"       = true
isPolyBuiltin "fst"      = true
isPolyBuiltin "snd"      = true
isPolyBuiltin "inl"      = true
isPolyBuiltin "inr"      = true
isPolyBuiltin "unit"     = true
isPolyBuiltin "pair"     = true
isPolyBuiltin "terminal" = true
isPolyBuiltin "initial"  = true
isPolyBuiltin "curry"    = true
isPolyBuiltin "apply"    = true
isPolyBuiltin "compose"  = true
isPolyBuiltin _          = false

-- | Look up a local variable by name in a NamedCtx.
-- Returns (A , Ψ , e) where Ψ is the usage vector of the resulting expression.

------------------------------------------------------------------------
-- Function-type and Int-type projections (for inference branching)
------------------------------------------------------------------------

-- | Match an `InferElabResult` against an expected ground type and
-- produce a `CheckElabResult`. Pure, non-recursive — caller passes
-- the inferred result explicitly. Encapsulates the generic check-
-- via-infer fallback so proofs can reason about it without fighting
-- with-abstractions inside `checkElab`.
matchInferResult : ∀ {m} {n} {Δ : SCtx m n}
  → InferElabResult Δ
  → (T : Ty m)
  → CheckElabResult Δ T
matchInferResult (failure err) _ = failure err
matchInferResult (success T' Ψ eE d f) T with T ≟T T'
... | yes refl = success _ eE d f
... | no _     = failure (TypeMismatch T T')

-- | Projection used by RApp inference. A successful application can
-- come from either a regular arrow (`A ⇒[q] B`) or an effectful arrow
-- (`Eff A B`); the two elaborate to different `Surface.app` /
-- `Surface.effApp` nodes, so we surface them as distinct constructors
-- rather than forcing a coercion at this layer.
data FunProjection {m} {n : ℕ} (Δ : SCtx m n) : Set where
  isFun  : (A : Ty m) (q : Quantity) (B : Ty m) (Ψ : Surface.Usage n)
         → SExpr Δ Ψ (A ⇒[ mk-kind q pure ] B) → ℕ → ℕ → FunProjection Δ
  isEff  : (π : Purity) (g : EffGrade π) (A B : Ty m) (Ψ : Surface.Usage n)
         → SExpr Δ Ψ (A ⇒[ mk-kind Many π ] B) → ℕ → ℕ → FunProjection Δ
  notFun : TypeError → FunProjection Δ

asFun : ∀ {m} {n} {Δ : SCtx m n} → InferElabResult Δ → FunProjection Δ
asFun (failure err)                                      = notFun err
asFun (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q Once.Spec.Grade.pure ] B) Ψ se d f) = isFun A q B Ψ se d f
asFun (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.eff ] B) Ψ se d f)                       = isEff Once.Spec.Grade.eff Once.Spec.Grade.eg-eff A B Ψ se d f
asFun (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.eff ] B) _ _ _ _) = notFun (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.eff ] B))
asFun (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.eff ] B) _ _ _ _) = notFun (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.eff ] B))
-- D311: no surface application of a `prod` arrow yet (plan 0.117 F).
asFun (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] B) Ψ se d f)                       = isEff Once.Spec.Grade.act Once.Spec.Grade.eg-act A B Ψ se d f
asFun (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.act ] B) _ _ _ _) = notFun (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.act ] B))
asFun (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.act ] B) _ _ _ _) = notFun (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.act ] B))
asFun (success Unit Ψ _ _ _)                             = notFun (NotFunction {0} Unit)
asFun (success Void Ψ _ _ _)                             = notFun (NotFunction {0} Void)
asFun (success Int Ψ _ _ _)                              = notFun (NotFunction {0} Int)
asFun (success Float Ψ _ _ _)                            = notFun (NotFunction {0} Float)
asFun (success (var iᵣ) Ψ _ _ _)                           = notFun (NotFunction (var iᵣ))
asFun (success (A Once.Spec.Type.* B) _ _ _ _)                = notFun (NotFunction (A Once.Spec.Type.* B))
asFun (success (A Once.Spec.Type.+ B) _ _ _ _)                = notFun (NotFunction (A Once.Spec.Type.+ B))
asFun (success (μ F) _ _ _ _)                       = notFun (NotFunction (μ F))
asFun (success (ν F π) _ _ _ _)                       = notFun (NotFunction (ν F π))

data IntProjection {m} {n : ℕ} (Δ : SCtx m n) : Set where
  isInt  : (Ψ : Surface.Usage n) → SExpr Δ Ψ Int → ℕ → ℕ → IntProjection Δ
  notInt : TypeError → IntProjection Δ

-- | `asInt` emits `TypeMismatch Int actual` for the non-Int success
-- cases (since semantically: expected Int, got `actual`).
asInt : ∀ {m} {n} {Δ : SCtx m n} → InferElabResult Δ → IntProjection Δ
asInt (failure err)                                      = notInt err
asInt (success Int Ψ se d f)                             = isInt Ψ se d f
asInt (success Unit _ _ _ _)                             = notInt (TypeMismatch {0} Int Unit)
asInt (success Void _ _ _ _)                             = notInt (TypeMismatch {0} Int Void)
asInt (success Float _ _ _ _)                            = notInt (TypeMismatch {0} Int Float)
asInt (success (var iᵣ) _ _ _ _)                           = notInt (TypeMismatch Int (var iᵣ))
asInt (success (A Once.Spec.Type.* B) _ _ _ _)                = notInt (TypeMismatch Int (A Once.Spec.Type.* B))
asInt (success (A Once.Spec.Type.+ B) _ _ _ _)                = notInt (TypeMismatch Int (A Once.Spec.Type.+ B))
asInt (success (A ⇒[ k ] B) _ _ _ _)                     = notInt (TypeMismatch Int (A ⇒[ k ] B))
asInt (success (μ F) _ _ _ _)                       = notInt (TypeMismatch Int (μ F))
asInt (success (ν F π) _ _ _ _)                       = notInt (TypeMismatch Int (ν F π))

-- | NOT NUMERIC — neither `Int` nor `Float` — with the error the elaborator
-- wraps in that case (plan 0.75 F4).
--
-- `asInt` can no longer stand in for this. It answers `notInt` on a `Float`,
-- and a `Float` operand is now a perfectly good binop operand: `1.5 + "x"`
-- reports `BinOpRightError (TypeMismatch Float Str)`, NOT
-- `BinOpLeftError (TypeMismatch {0} Int Float)`. The error-shape lemmas were
-- stated over `asInt`'s failure and became FALSE at exactly that type, so they
-- move to this projection, which is the hypothesis they always meant: the left
-- operand is not a number at all.
--
-- The errors are `asInt`'s verbatim, so no message changes.
notNumeric : ∀ {m} {n} {Δ : SCtx m n} → InferElabResult Δ → Maybe TypeError
notNumeric (failure err)                                 = just err
notNumeric (success Int _ _ _ _)                         = nothing
notNumeric (success Once.Spec.Type.Float _ _ _ _)             = nothing
notNumeric (success Unit _ _ _ _)                        = just (TypeMismatch {0} Int Unit)
notNumeric (success Void _ _ _ _)                        = just (TypeMismatch {0} Int Void)
notNumeric (success (var iᵣ) _ _ _ _)                      = just (TypeMismatch Int (var iᵣ))
notNumeric (success (A Once.Spec.Type.* B) _ _ _ _)           = just (TypeMismatch Int (A Once.Spec.Type.* B))
notNumeric (success (A Once.Spec.Type.+ B) _ _ _ _)           = just (TypeMismatch Int (A Once.Spec.Type.+ B))
notNumeric (success (A ⇒[ k ] B) _ _ _ _)                = just (TypeMismatch Int (A ⇒[ k ] B))
notNumeric (success (μ F) _ _ _ _)                  = just (TypeMismatch Int (μ F))
notNumeric (success (ν F π) _ _ _ _)                  = just (TypeMismatch Int (ν F π))

------------------------------------------------------------------------
-- Decide-with-proof helpers
------------------------------------------------------------------------

-- | Decide `q' ≤q q`, returning the propositional proof on success.
--
-- This is the Bool-decision packaged with its equality witness, as
-- the `just`/`nothing` distinction. The elaborator uses this in the
-- lambda case where the `Surface.lam` constructor requires a proof
-- `(q' ≤qᵇ q) ≡ true`. Using this helper (instead of stdlib's
-- `with q' ≤q q | inspect (q' ≤q_) q`) avoids producing an opaque
-- internal `with`-function that downstream proofs cannot unify with.
-- See `docs/formal/historical/lessons-learned.md` § "`with` patterns
-- block computation" for background.
-- | Pattern-match directly on the two quantities rather than on
-- the Bool `q' ≤qᵇ q` to keep the definition transparent to external
-- reduction (no opaque internal `with`-helper).
decideLeq : (q' q : Quantity) → Maybe ((q' ≤qᵇ q) ≡ true)
decideLeq Zero Zero = just refl
decideLeq Zero One  = just refl
decideLeq Zero Many = just refl
decideLeq One  Zero = nothing
decideLeq One  One  = just refl
decideLeq One  Many = just refl
decideLeq Many Zero = nothing
decideLeq Many One  = nothing
decideLeq Many Many = just refl


------------------------------------------------------------------------
-- Bare polymorphic-builtin classifier (plan 0.6 Phase C.7)
------------------------------------------------------------------------
-- (Was used by the deleted `checkElab-RVar`; see D136.)
-- per builtin name. The view-constructor index exposes the concrete
-- string in each case, so Agda reductions proceed cleanly and proof
-- `with classifyBareBuiltin x` mirrors the elaborator's dispatch.


------------------------------------------------------------------------
-- Plan 0.4 T0 Option A POC: per-shape RApp dispatch as top-level
-- helpers taking the precomputed `inferElab ctx x` result. By moving
-- the body OUT of `inferElab`'s `with classifyAppHeadView f` block,
-- soundness proofs (e.g. `sound-RApp-id`) can reduce through a plain
-- top-level function call instead of the with-helper that the case
-- tree compiler keeps opaque. POC scope: `ahv-id` only.
------------------------------------------------------------------------

inferElab-RApp-id : ∀ {m} → (ctx : NamedCtx m)
                  → InferElabResult (NamedCtx.debruijn ctx)
                  → InferElabResult (NamedCtx.debruijn ctx)
inferElab-RApp-id ctx (failure err) = failure err
inferElab-RApp-id ctx (success T Ψ argE d f') =
  success T _ (Surface.morph-app IR.id argE) (suc d) f'

------------------------------------------------------------------------
-- Bidirectional Inference (produces usage-indexed Expr)
------------------------------------------------------------------------

-- Plan 0.6.2 Phase 4: two-phase architecture. Phase 1 (this mutual
-- block) is purely structural on `Syn.Expr` — at user-polymorphic
-- references, it emits a `Surface.poly x T` placeholder rather than
-- recursing into the def's body. Phase 2 (`resolveExpr` below)
-- tree-walks the emitted Expr and splices bodies at `poly` nodes,
-- well-founded on `length polys`.
------------------------------------------------------------------------
-- Plan 0.4 T0 Option B — postulates referenced by the merged
-- mutual block. Placed BEFORE the block so V bodies inside can see
-- them.
------------------------------------------------------------------------

isGround-inj₂→¬Ground : ∀ (s : PolyType) → isGround s ≡ inj₂ tt → ¬ Ground s
isGround-inj₂→¬Ground s eq g with trans (sym eq) (isGround-complete-at s g)
... | ()

-- Plan 0.103 phase 2b: the domain-given POLYMORPHIC head (`wd-poly`), de-withed:
-- each decision is an explicit argument with its equation.
given-poly-k : ∀ {m} (ctx : NamedCtx m) (x : String) (A B : Ty m) (π π′ : Once.Spec.Grade.Purity) (err : TypeError)
  {schema sd sc : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ Ground schema → ArrowSchema schema sd sc π′ → CodVarsInDom sd sc → π′ ⊑π π
  → Dec (KindedInstance (NamedCtx.kinds ctx) schema (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B))
  → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly-k ctx x A B π π′ err eL eI eP ¬g as inc g (no _) = failure err
given-poly-k ctx x A B π π′ err eL eI eP ¬g as inc g (yes ki) =
  success B Surface.zeroUsage
    (Surface.coerce (sub-arr {q = Once.Spec.Grade.Many} (<:-refl A) (<:-refl B) g)
                    (Surface.poly x (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B)))
    0 0

given-poly-π : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
  {schema sd sc : PolyType} {π′ : Once.Spec.Grade.Purity} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ Ground schema → ArrowSchema schema sd sc π′ → CodVarsInDom sd sc
  → (θ : String → Ty m) → substPoly θ sd ≡ A
  → Dec (π′ ⊑π π) → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly-π ctx x A π err eL eI eP ¬g as inc θ eθ (no _) = failure err
given-poly-π ctx x A π err {schema = schema} {sc = sc} {π′ = π′} eL eI eP ¬g as inc θ eθ (yes g) =
  given-poly-k ctx x A (substPoly θ sc) π π′ err eL eI eP ¬g as inc g
    (kindedInstance? (NamedCtx.kinds ctx) schema (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] substPoly θ sc))

given-poly-m : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
  {schema sd sc : PolyType} {π′ : Once.Spec.Grade.Purity} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ Ground schema → ArrowSchema schema sd sc π′ → CodVarsInDom sd sc
  → (mσ : Maybe (Subst m)) → instantiate sd A ≡ mσ → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly-m ctx x A π err eL eI eP ¬g as inc nothing _ = failure err
given-poly-m ctx x A π err {sd = sd} {π′ = π′} eL eI eP ¬g as inc (just σ) eS =
  given-poly-π ctx x A π err eL eI eP ¬g as inc
    (Data.Product.proj₁ (instantiate-sound sd A eS)) (Data.Product.proj₂ (instantiate-sound sd A eS)) (π′ ⊑π? π)

given-poly-d : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
  {schema sd sc : PolyType} {π′ : Once.Spec.Grade.Purity} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ Ground schema → ArrowSchema schema sd sc π′
  → Dec (CodVarsInDom sd sc) → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly-d ctx x A π err eL eI eP ¬g as (no _) = failure err
given-poly-d ctx x A π err {sd = sd} eL eI eP ¬g as (yes inc) =
  given-poly-m ctx x A π err eL eI eP ¬g as inc (instantiate sd A) refl

given-poly-a : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
  {schema : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ Ground schema → Maybe (ArrowView schema) → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly-a ctx x A π err eL eI eP ¬g nothing = failure err
given-poly-a ctx x A π err eL eI eP ¬g (just (sd , sc , π′ , as)) =
  given-poly-d ctx x A π err eL eI eP ¬g as (codVarsInDom? sd sc)

given-poly-g : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
  (schema : PolyType) {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → (ig : Ground schema ⊎ ⊤) → isGround schema ≡ ig → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly-g ctx x A π err schema eL eI eP (inj₁ _) _ = failure err
given-poly-g ctx x A π err schema eL eI eP (inj₂ tt) eG =
  given-poly-a ctx x A π err eL eI eP (isGround-inj₂→¬Ground schema eG) (arrowSchema? schema)

given-poly : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
  → (ls : Maybe Type) → lookupImport (NamedCtx.sig ctx) x ≡ ls
  → (li : Maybe Type) → lookupImport (NamedCtx.imports ctx) x ≡ li
  → (lp : Maybe (PolyType × Syn.Expr × PolyCtx)) → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ lp
  → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly ctx x A π err (just _) _ _ _ _ _ = failure err
given-poly ctx x A π err nothing _ (just _) _ _ _ = failure err
given-poly ctx x A π err nothing _ nothing _ nothing _ = failure err
given-poly ctx x A π err nothing eL nothing eI (just (schema , body , prefix)) eP =
  given-poly-g ctx x A π err schema eL eI eP (isGround schema) refl

-- A resolved head: inferred when it infers (`wd-infer`); otherwise, an own
-- name, a polymorphic telescope entry at the given domain (`wd-poly`).
given-res : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (A : Ty m) (π : Once.Spec.Grade.Purity)
          → InferElabResult (NamedCtx.debruijn ctx) → GivenElabResult (NamedCtx.debruijn ctx) A π
given-res ctx cn A π r@(success _ _ _ _ _) = given-infer ctx (Raw.RResolved cn) A π r
given-res ctx (canonical [])            A π (failure err) = failure err
given-res ctx (own x)                   A π (failure err) =
  given-poly ctx x A π err (lookupImport (NamedCtx.sig ctx) x) refl (lookupImport (NamedCtx.imports ctx) x) refl
    (lookupPolyPrefix (NamedCtx.polys ctx) x) refl
given-res ctx (canonical (_ ∷ _ ∷ _))   A π (failure err) = failure err

-- The check-mode polymorphic reference, de-withed: each decision is an
-- explicit argument with its equation, so the proofs reduce each stage.
checkElabV-RVar-poly-inst-aux : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError)
    {schema : PolyType} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ Ground schema
  → Dec (KindedInstance (NamedCtx.kinds ctx) schema T)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-poly-inst-aux ctx x T err eL eI eP ¬g (no _) = failure err
checkElabV-RVar-poly-inst-aux ctx x T err eL eI eP ¬g (yes ki) =
  success Surface.zeroUsage (Surface.poly x T) 0 0

checkElabV-RVar-poly-ground-aux : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError)
    (schema : PolyType) {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → (ig : Ground schema ⊎ ⊤) → isGround schema ≡ ig
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-poly-ground-aux ctx x T err schema eL eI eP (inj₁ _) _ = failure err
checkElabV-RVar-poly-ground-aux ctx x T err schema eL eI eP (inj₂ tt) eG =
  checkElabV-RVar-poly-inst-aux ctx x T err eL eI eP (isGround-inj₂→¬Ground schema eG) (kindedInstance? (NamedCtx.kinds ctx) schema T)

checkElabV-RVar-poly-check-aux : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m) (err : TypeError)
  → (ls : Maybe Type) → lookupImport (NamedCtx.sig ctx) x ≡ ls
  → (li : Maybe Type) → lookupImport (NamedCtx.imports ctx) x ≡ li
  → (lp : Maybe (PolyType × Syn.Expr × PolyCtx)) → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ lp
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-poly-check-aux ctx x T err (just _) _ _ _ _ _ = failure err
checkElabV-RVar-poly-check-aux ctx x T err nothing _ (just _) _ _ _ = failure err
checkElabV-RVar-poly-check-aux ctx x T err nothing _ nothing _ nothing _ = failure err
checkElabV-RVar-poly-check-aux ctx x T err nothing eL nothing eI (just (schema , body , prefix)) eP =
  checkElabV-RVar-poly-ground-aux ctx x T err schema eL eI eP (isGround schema) refl

------------------------------------------------------------------------
-- Plan 0.58 / D071: infer-mode ground telescope reference (the poly fallback
-- of `inferElabV` for an own reference, R11/D330).
--
-- After the signature and definition lookups fail, an own name may still
-- be a telescope def (`lookupPoly`). A GROUND schema has exactly
-- one type, so the reference INFERS at its declaration (`extractGround`) —
-- emitting the same `Surface.poly` placeholder Phase 2 (`resolveExpr`)
-- splices. A NON-ground schema stays check-mode-only
-- (`wt-var-poly-instantiate`), so infer still fails with `UnboundVariable`.
--
-- De-withed (classify / lookup / isGround as explicit args + equations), so
-- external proofs reduce each stage J-style ([[de-with pattern]]).
------------------------------------------------------------------------

inferElabV-RVar-poly-ground-aux : ∀ {m} (ctx : NamedCtx m) (x : String)
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → (schema : PolyType) (body : Syn.Expr) → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  → (ig : (Ground schema) ⊎ ⊤) → isGround schema ≡ ig
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RVar-poly-ground-aux ctx x eL eI schema body eqLp (inj₂ tt) _ =
  failure (UnboundVariable x)
-- Plan 0.103 phase 1c: the witness is the telescope-variable rule itself —
-- the lookups ARE its premises (the body is typed at the declaration).
inferElabV-RVar-poly-ground-aux ctx x eL eI schema body eqLp (inj₁ g) _ =
  success (extractGround schema g) Surface.zeroUsage
          (Surface.poly x (extractGround schema g)) 0 0

inferElabV-RVar-poly-lookup-aux : ∀ {m} (ctx : NamedCtx m) (x : String)
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → (lp : Maybe (PolyType × Syn.Expr)) → lookupPoly (NamedCtx.polys ctx) x ≡ lp
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RVar-poly-lookup-aux ctx x eL eI nothing _ = failure (UnboundVariable x)
inferElabV-RVar-poly-lookup-aux ctx x eL eI (just (schema , body)) eqLp =
  inferElabV-RVar-poly-ground-aux ctx x eL eI schema body eqLp (isGround schema) refl

inferElabV-RVar-poly-aux : ∀ {m} (ctx : NamedCtx m) (x : String)
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RVar-poly-aux ctx x eL eI =
  inferElabV-RVar-poly-lookup-aux ctx x eL eI (lookupPoly (NamedCtx.polys ctx) x) refl


-- Not mutually recursive with the block below: these never call back into
-- it, so they stand outside it (its positivity and termination graphs span
-- only what actually recurses).

elabGivenLeaf : ∀ {m} → (ctx : NamedCtx m) (cn : CanonicalName) (A : Ty m) (π : Once.Spec.Grade.Purity)
              → AppHeadView (Raw.RResolved cn) → InferElabResult (NamedCtx.debruijn ctx)
              → GivenElabResult (NamedCtx.debruijn ctx) A π
-- The generators, read off the same head view the application dispatch uses.
elabGivenLeaf ctx .(gen "id") A π ahv-id _ = withUnit (failure (BuiltinTypeMismatch "id")) π λ u →
  success A _ (Surface.lift-morphism IR.id) 0 0
elabGivenLeaf ctx .(gen "fst") (A Once.Spec.Type.* B) π ahv-fst _ = withUnit (failure (BuiltinTypeMismatch "fst")) π λ u →
  success A _ (Surface.lift-morphism IR.fst) 0 0
{-# CATCHALL #-}
elabGivenLeaf ctx .(gen "fst") _ π ahv-fst _ = failure (BuiltinTypeMismatch "fst")
elabGivenLeaf ctx .(gen "snd") (A Once.Spec.Type.* B) π ahv-snd _ = withUnit (failure (BuiltinTypeMismatch "snd")) π λ u →
  success B _ (Surface.lift-morphism IR.snd) 0 0
{-# CATCHALL #-}
elabGivenLeaf ctx .(gen "snd") _ π ahv-snd _ = failure (BuiltinTypeMismatch "snd")
elabGivenLeaf ctx .(gen "terminal") A π ahv-terminal _ = withUnit (failure (BuiltinTypeMismatch "terminal")) π λ u →
  success Unit _ (Surface.lift-morphism IR.terminal) 0 0
elabGivenLeaf ctx .(gen "initial") Void π ahv-initial _ = withUnit (failure (BuiltinTypeMismatch "initial")) π λ u →
  success Void _ (Surface.lift-morphism IR.initial) 0 0
{-# CATCHALL #-}
elabGivenLeaf ctx .(gen "initial") _ π ahv-initial _ = failure (BuiltinTypeMismatch "initial")
{-# CATCHALL #-}
elabGivenLeaf ctx cn A π _ r = given-res ctx cn A π r

-- Recursion-scheme generators (Plan 0.28 Commit 2). The `…Go`/`…A/B/C`
-- helpers take each decidable result as an explicit argument with its
-- `refl` witness (no `with … in`), so the completeness fallbacks
-- reduce them with plain nested `with | eq` — like `checkPair`.
-- D194: `Out v` — the ν eliminator, INFER-mode (a check rule would have to
-- invert `⟦ F ⟧T (ν-type F) ≡ T` to recover `F`).
-- The IR `Out` at a stream of grade `φ`, retyped to the layer's surface type.
outIR : ∀ {m} {Δ : Once.Spec.Type.KCtx m} (F : Once.Spec.Type.Fun m) (φ : Once.Spec.Grade.Finite) → Once.Spec.Type.WFFun Δ F
      → IR ⌊ Once.Spec.Type.ν F φ ⌋ ⌊ ⟦ F ⟧F (Once.Spec.Type.ν F φ) ⌋
outIR F φ wfF =
  subst (λ o → IR ⌊ Once.Spec.Type.ν F φ ⌋ o)
        (sym (⌊⟧T-commute F (Once.Spec.Type.ν F φ)))
        (IR.Out (wf-⌊⌋ wfF))

inferOutGo : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) (F : Once.Spec.Type.Fun m) (φ : Once.Spec.Grade.Finite)
             (Ψ : Surface.Usage (NamedCtx.size ctx))
             (argE : SExpr (NamedCtx.debruijn ctx) Ψ (Once.Spec.Type.ν F φ))
             (d fr : ℕ)
             → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F)) → wfFun? (NamedCtx.kinds ctx) F ≡ mw
           → InferElabResult (NamedCtx.debruijn ctx)
inferOutGo ctx arg F φ Ψ argE d fr nothing _ = failure (BuiltinTypeMismatch "Out")
inferOutGo ctx arg F Once.Spec.Grade.pureᶠ Ψ argE d fr (just wfF) eqW =
  success (⟦ F ⟧F (Once.Spec.Type.ν F Once.Spec.Grade.pureᶠ)) _
    (Surface.morph-app (outIR F Once.Spec.Grade.pureᶠ wfF) argE)
    (suc d) fr
-- D233/D318: an ACTING stream — the stream is evaluated now, the force is
-- suspended (`curry (Out ∘ fst)`), as `wt-apply-eff-app-infer` suspends `apply`.
inferOutGo ctx arg F Once.Spec.Grade.actᶠ Ψ argE d fr (just wfF) eqW =
  success (Once.Spec.Type.Unit Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ]
             ⟦ F ⟧F (Once.Spec.Type.ν F Once.Spec.Grade.actᶠ)) _
    (Surface.morph-app (IR.curry (outIR F Once.Spec.Grade.actᶠ wfF IR.∘ IR.fst)) argE)
    (suc d) fr
-- D311: no surface `Out` of a `prod` stream yet (plan 0.117 F).

inferOutAt : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx))
             (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ) → NuView T
           → InferElabResult (NamedCtx.debruijn ctx)
inferOutAt ctx arg Ψ argE d fr (nu-at F π) = inferOutGo ctx arg F π Ψ argE d fr (wfFun? (NamedCtx.kinds ctx) F) refl
inferOutAt ctx arg Ψ argE d fr nu-other = failure (BuiltinTypeMismatch "Out")

-- `Out` / `apply` at the argument's result, then at its type's view.
inferOutOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
           → InferElabResult (NamedCtx.debruijn ctx)
inferOutOn ctx arg (failure err) = failure err
inferOutOn ctx arg (success T Ψ argE d fr) = inferOutAt ctx arg Ψ argE d fr (nuView T)

inferFstAt : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx))
             (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ) → ProdView T
           → InferElabResult (NamedCtx.debruijn ctx)
inferFstAt ctx arg Ψ argE d fr (prod-at A B) =
  success A _ (Surface.morph-app (IR.fst) argE) (suc d) fr
inferFstAt ctx arg Ψ argE d fr prod-other = failure FstNeedsPair

inferFstOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
           → InferElabResult (NamedCtx.debruijn ctx)
inferFstOn ctx arg (failure err) = failure err
inferFstOn ctx arg (success T Ψ argE d fr) = inferFstAt ctx arg Ψ argE d fr (prodView T)

inferSndAt : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx))
             (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ) → ProdView T
           → InferElabResult (NamedCtx.debruijn ctx)
inferSndAt ctx arg Ψ argE d fr (prod-at A B) =
  success B _ (Surface.morph-app (IR.snd) argE) (suc d) fr
inferSndAt ctx arg Ψ argE d fr prod-other = failure SndNeedsPair

inferSndOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
           → InferElabResult (NamedCtx.debruijn ctx)
inferSndOn ctx arg (failure err) = failure err
inferSndOn ctx arg (success T Ψ argE d fr) = inferSndAt ctx arg Ψ argE d fr (prodView T)

inferApplyAt : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m} (Ψ : Surface.Usage (NamedCtx.size ctx))
               (argE : SExpr (NamedCtx.debruijn ctx) Ψ T) (d fr : ℕ) → ApplyView T
             → InferElabResult (NamedCtx.debruijn ctx)
inferApplyAt ctx arg Ψ argE d fr (apply-at A Once.Spec.Grade.pure B A') with A ≟T A'
... | yes refl = success B _ (Surface.morph-app IR.apply argE) (suc d) fr
... | no _     = failure (BuiltinTypeMismatch "apply")
-- D222 / plan 0.95 A′: an EFFECTFUL closure. The result is a SUSPENSION
-- `Unit ⇒[eff] B`, so the morphism is the thunk-builder `curry (apply ∘ fst)`
-- rather than `apply` — the same shape `elaborate` gives `effApp`. The IR
-- arrow is UNGRADED, so no new Surface former is needed.
inferApplyAt ctx arg Ψ argE d fr (apply-at A Once.Spec.Grade.eff B A') with A ≟T A'
... | yes refl =
  success (Once.Spec.Type.Unit Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.eff ] B) _
          (Surface.morph-app (IR.curry (IR.apply IR.∘ IR.fst)) argE) (suc d) fr
... | no _ = failure (BuiltinTypeMismatch "apply")
inferApplyAt ctx arg Ψ argE d fr (apply-at A Once.Spec.Grade.act B A') with A ≟T A'
... | yes refl =
  success (Once.Spec.Type.Unit Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] B) _
          (Surface.morph-app (IR.curry (IR.apply IR.∘ IR.fst)) argE) (suc d) fr
... | no _ = failure (BuiltinTypeMismatch "apply")
-- D311: no surface application of a `prod` closure yet (plan 0.117 F).
inferApplyAt ctx arg Ψ argE d fr apply-other = failure (BuiltinTypeMismatch "apply")

inferApplyOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
             → InferElabResult (NamedCtx.debruijn ctx)
inferApplyOn ctx arg (failure err) = failure err
inferApplyOn ctx arg (success T Ψ argE d fr) = inferApplyAt ctx arg Ψ argE d fr (applyView T)

-- RPair dispatch as a top-level aux taking the two sub-results explicitly
-- (no inline `with` → no opaque `with`-helper → downstream proofs recurse
-- directly; [[feedback_with_clauses_painful]]).
inferElabV-RPair-aux : ∀ {m} → (ctx : NamedCtx m) (a b : Syn.Expr)
  → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
  → InferElabResult (NamedCtx.debruijn ctx)
-- RPair: pair the two sub-results (a-failure short-circuits without forcing
-- b's result, matching the old left-to-right `with`).
inferElabV-RPair-aux ctx a b (success A Ψ₁ aE da fa) (success B Ψ₂ bE db fb) =
  success (A Once.Spec.Type.* B) _ (Surface.pair aE bE) (da ⊔ db) fb
inferElabV-RPair-aux ctx a b (failure err) _ = failure err
inferElabV-RPair-aux ctx a b (success _ _ _ _ _) (failure err) = failure err

-- D252: an annotation is a ground type, checked at its weakening.
inferElabV-RAnnot-aux : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (T : Type)
  → CheckElabResult (NamedCtx.debruijn ctx) (wk₀ T) → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RAnnot-aux ctx e T (success Ψ eE d fr) = success (wk₀ T) Ψ eE d fr
inferElabV-RAnnot-aux ctx e T (failure err)             = failure err

inferElabV-RNeg-aux : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr)
  → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RNeg-aux ctx e (failure err)                = failure err
inferElabV-RNeg-aux ctx e (success Unit   _ _ _ _)     = failure (TypeMismatch {0} Int Unit)
inferElabV-RNeg-aux ctx e (success Void   _ _ _ _)     = failure (TypeMismatch {0} Int Void)
inferElabV-RNeg-aux ctx e (success Int    Ψ eE d fr)   = success Int _ (Surface.neg eE) (suc d) fr
inferElabV-RNeg-aux ctx e (success Float  _ _ _ _)     = failure (TypeMismatch {0} Int Float)
inferElabV-RNeg-aux ctx e (success (var iᵣ) _ _ _ _)     = failure (TypeMismatch Int (var iᵣ))
inferElabV-RNeg-aux ctx e (success (A Once.Spec.Type.* B)      _ _ _ _) = failure (TypeMismatch Int (A Once.Spec.Type.* B))
inferElabV-RNeg-aux ctx e (success (A Once.Spec.Type.+ B)      _ _ _ _) = failure (TypeMismatch Int (A Once.Spec.Type.+ B))
inferElabV-RNeg-aux ctx e (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) = failure (TypeMismatch Int (A Once.Spec.Type.⇒[ k ] B))
inferElabV-RNeg-aux ctx e (success (Once.Spec.Type.μ F)   _ _ _ _) = failure (TypeMismatch Int (Once.Spec.Type.μ F))
inferElabV-RNeg-aux ctx e (success (Once.Spec.Type.ν F π)   _ _ _ _) = failure (TypeMismatch Int (Once.Spec.Type.ν F π))

checkElabV-neg-int-aux : ∀ {m} → (ctx : NamedCtx m) (n : ℤ) (T : Ty m)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- Written out rather than routed through `inferElabV ctx (RNeg (RInt n))`,
-- which would be the same term but would stop reducing wherever the view has
-- been abstracted.
checkElabV-neg-int-aux ctx n T with Int <:? T
... | yes p = success Surface.zeroUsage (Surface.coerce p (Surface.neg (Surface.int n))) 2 0
... | no _  = failure (TypeMismatch T Int)

checkElabV-neg-float-aux : ∀ {m} → (ctx : NamedCtx m) (i f l : ℕ) (T : Ty m)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-neg-float-aux ctx i f l T with Once.Spec.Type.Float <:? T
... | yes s = success Surface.zeroUsage
                      (Surface.coerce s (Surface.float (Decimal.negate (decimalOf i f l)))) 1
                      0
... | no _  = failure (TypeMismatch T Once.Spec.Type.Float)

inferElabV-RBinOp-aux : ∀ {m} → (ctx : NamedCtx m) (op : Raw.BinOp) (e₁ e₂ : Syn.Expr)
  → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
  → InferElabResult (NamedCtx.debruijn ctx)
-- left non-Int → BinOpLeftError
inferElabV-RBinOp-aux ctx op e₁ e₂ (failure err) _ = failure (BinOpLeftError err)
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Unit   _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch {0} Int Unit))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Void   _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch {0} Int Void))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success (var iᵣ) _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch Int (var iᵣ)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success (A Once.Spec.Type.* B)      _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Spec.Type.* B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success (A Once.Spec.Type.+ B)      _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Spec.Type.+ B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Spec.Type.⇒[ k ] B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success (Once.Spec.Type.μ F)   _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch Int (Once.Spec.Type.μ F)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success (Once.Spec.Type.ν F π)   _ _ _ _) _ = failure (BinOpLeftError (TypeMismatch Int (Once.Spec.Type.ν F π)))
-- left Int, right non-Int → BinOpRightError
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (failure err) = failure (BinOpRightError err)
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success Unit   _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Unit))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success Void   _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Void))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success (var iᵣ) _ _ _ _) = failure (BinOpRightError (TypeMismatch Int (var iᵣ)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success (A Once.Spec.Type.* B)      _ _ _ _) = failure (BinOpRightError (TypeMismatch Int (A Once.Spec.Type.* B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success (A Once.Spec.Type.+ B)      _ _ _ _) = failure (BinOpRightError (TypeMismatch Int (A Once.Spec.Type.+ B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) = failure (BinOpRightError (TypeMismatch Int (A Once.Spec.Type.⇒[ k ] B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success (Once.Spec.Type.μ F)   _ _ _ _) = failure (BinOpRightError (TypeMismatch Int (Once.Spec.Type.μ F)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _) (success (Once.Spec.Type.ν F π)   _ _ _ _) = failure (BinOpRightError (TypeMismatch Int (Once.Spec.Type.ν F π)))
-- both Int → op dispatch
inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Int _ (Surface.add e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Int _ (Surface.sub e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Int _ (Surface.mul e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Int _ (Surface.div e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Int _ (Surface.mod' e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success (Unit Once.Spec.Type.+ Unit) _ (Surface.lt e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success (Unit Once.Spec.Type.+ Unit) _ (Surface.le e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success (Unit Once.Spec.Type.+ Unit) _ (Surface.gt e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success (Unit Once.Spec.Type.+ Unit) _ (Surface.ge e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success (Unit Once.Spec.Type.+ Unit) _ (Surface.eq e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success (Unit Once.Spec.Type.+ Unit) _ (Surface.ne e₁E e₂E) (d₁ ⊔ d₂) f₂
----------------------------------------------------------------------
-- PLAN 0.75 F4: `Float` ON THE LEFT SELECTS THE FLOAT FAMILY.
--
-- It used to be `BinOpLeftError (TypeMismatch {0} Int Float)` with a catch-all
-- for the right operand — "arithmetic means Int" — which is what made
-- `1.5 - 2.1` report `expected Int but got Float`. The OPERAND TYPES decide
-- which arithmetic runs; `+` is the same operator either way.
--
-- A MIXED PAIR IS STILL AN ERROR, and that is the decision, not a gap:
-- there is no implicit widening, so `1 + 1.5` reports rather than silently
-- promoting. A coercion the programmer did not write is a value
-- substitution, which is D115's objection to a wrapped literal one type
-- over.
----------------------------------------------------------------------
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (failure err) = failure (BinOpRightError err)
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success Unit _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Unit))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success Void _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Void))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success (var iᵣ) _ _ _ _) = failure (BinOpRightError (TypeMismatch Float (var iᵣ)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success (A Once.Spec.Type.* B) _ _ _ _) = failure (BinOpRightError (TypeMismatch Float (A Once.Spec.Type.* B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success (A Once.Spec.Type.+ B) _ _ _ _) = failure (BinOpRightError (TypeMismatch Float (A Once.Spec.Type.+ B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success (A Once.Spec.Type.⇒[ k ] B) _ _ _ _) = failure (BinOpRightError (TypeMismatch Float (A Once.Spec.Type.⇒[ k ] B)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success (Once.Spec.Type.μ F) _ _ _ _) = failure (BinOpRightError (TypeMismatch Float (Once.Spec.Type.μ F)))
inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _) (success (Once.Spec.Type.ν F π) _ _ _ _) = failure (BinOpRightError (TypeMismatch Float (Once.Spec.Type.ν F π)))
-- both Float → op dispatch. Only `+`, `−` and `×` exist here
-- (`isFloatArithmeticOp`), and `Once.Spec.Float.Arith` records why.
inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fadd e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fsub e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fmul e₁E e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fdiv e₁E e₂E) (d₁ ⊔ d₂) f₂
-- `%` still has no float lowering — IEEE's `fmod` is a different function and
-- needs its own decision — and a float comparison needs the Bool encoding
-- `Int`'s own comparisons are STILL postulated over. Those six keep exactly
-- the error they gave before this clause family existed.
inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Float _ _ _ _) (success Float _ _ _ _) = failure (BinOpLeftError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Float _ _ _ _) (success Float _ _ _ _) = failure (BinOpLeftError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Float _ _ _ _) (success Float _ _ _ _) = failure (BinOpLeftError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Float _ _ _ _) (success Float _ _ _ _) = failure (BinOpLeftError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Float _ _ _ _) (success Float _ _ _ _) = failure (BinOpLeftError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Float _ _ _ _) (success Float _ _ _ _) = failure (BinOpLeftError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Float _ _ _ _) (success Float _ _ _ _) = failure (BinOpLeftError (TypeMismatch {0} Int Float))
----------------------------------------------------------------------
-- MIXED OPERANDS — the `Int` side WIDENS (D125).
--
-- `1 + 1.5` compiles, and the conversion is an explicit `Surface.i2f` node
-- so it lowers to a real instruction rather than being a silent retyping.
-- The widening is CORRECTLY ROUNDED (IEEE lists `convertFromInt` beside
-- `+`), the error is bounded by half an ulp like every other rounding, and
-- both targets already agree bit-for-bit — measured, so no D055-style
-- decision and no backend guard.
--
-- Only `Int → Float`. `Float → Int` stays explicit: the hardware DIVERGES
-- (x86 "integer indefinite", RISC-V saturates) and it is a narrowing where
-- truncate-versus-round is the programmer's call.
----------------------------------------------------------------------
inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fadd (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fsub (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fmul (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁) (success Float Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fdiv (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fadd e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fsub e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fmul e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂
inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁) (success Int Ψ₂ e₂E d₂ f₂) = success Float _ (Surface.fdiv e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂
-- `/`, `%` and the comparisons keep the error they gave before.
inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Int _ _ _ _) (success Float _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Int _ _ _ _) (success Float _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Int _ _ _ _) (success Float _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Int _ _ _ _) (success Float _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Int _ _ _ _) (success Float _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Int _ _ _ _) (success Float _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Int _ _ _ _) (success Float _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Int Float))
inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Float _ _ _ _) (success Int _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Int))
inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Float _ _ _ _) (success Int _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Int))
inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Float _ _ _ _) (success Int _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Int))
inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Float _ _ _ _) (success Int _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Int))
inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Float _ _ _ _) (success Int _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Int))
inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Float _ _ _ _) (success Int _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Int))
inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Float _ _ _ _) (success Int _ _ _ _) = failure (BinOpRightError (TypeMismatch {0} Float Int))

inferElabV-RLet-aux2 : ∀ {m} → (ctx : NamedCtx m) (x : String) (e₁ e₂ : Syn.Expr)
  {A : Ty m} {Ψ₁ : Surface.Usage (NamedCtx.size ctx)}
  (e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ A) (d₁ f₁ : ℕ)
  → InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx x A))
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ (failure err) = failure err
inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ (success B (q ∷ᵘ Ψ₂) e₂E d₂ f₂) =
  success B _ (Surface.let' e₁E e₂E) (d₁ ⊔ suc d₂) f₂

-- D322: the branches meet at their join, each converted into it; branches
-- with no upper bound are a mismatch.
inferElabV-RDestruct-join : ∀ {m} → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
  (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)}
  (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds : ℕ)
  {C₁ : Ty m} {qℓ : _} {Ψₗ : Surface.Usage (NamedCtx.size ctx)}
  (eLE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xL A)) (qℓ ∷ᵘ Ψₗ) C₁) (dL : ℕ)
  {C₂ : Ty m} {qr : _} {Ψᵣ : Surface.Usage (NamedCtx.size ctx)}
  (eRE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xR B)) (qr ∷ᵘ Ψᵣ) C₂) (dR fR : ℕ)
  → Join? C₁ C₂
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RDestruct-join ctx scrut xL eL xR eR A B scrutE ds eLE dL eRE dR fR (joined C J) =
  success C _ (Surface.case' scrutE (Surface.coerce (<:ᶜ⇒<: (⊔-left (sound J))) eLE) (Surface.coerce (<:ᶜ⇒<: (⊔-right (sound J))) eRE))
          (ds ⊔ suc dL ⊔ suc dR) fR
inferElabV-RDestruct-join ctx scrut xL eL xR eR A B scrutE ds eLE dL eRE dR fR (apart _) =
  failure CaseBranchMismatch

-- D322: the arms of a copair meet at the join of their outputs, each
-- converted into it; arms with no upper bound are a mismatch.
given-case-join : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (A B : Ty m) (π : Once.Spec.Grade.Purity)
  {C : Ty m} {Ψf : Surface.Usage (NamedCtx.size ctx)}
  (fE : SExpr (NamedCtx.debruijn ctx) Ψf (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C))
  (df : ℕ) {C′ : Ty m} {Ψg : Surface.Usage (NamedCtx.size ctx)}
  (gE : SExpr (NamedCtx.debruijn ctx) Ψg (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C′))
  (dg frg : ℕ) → Join? C C′
  → GivenElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.+ B) π
given-case-join ctx f g A B π {C} fE df {C′} gE dg frg (apart _) = failure (TypeMismatch C C′)
given-case-join ctx f g A B π fE df gE dg frg (joined D J) =
  success D _ (Surface.copair' (Surface.coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (⊔-left (sound J))) (⊑π-refl π)) fE)
                               (Surface.coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (⊔-right (sound J))) (⊑π-refl π)) gE))
          (suc (df Data.Nat.⊔ dg)) frg

inferElabV-RDestruct-auxR : ∀ {m} → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
  (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)}
  (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds fs : ℕ)
  {C₁ : Ty m} {qℓ : _} {Ψₗ : Surface.Usage (NamedCtx.size ctx)}
  (eLE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xL A)) (qℓ ∷ᵘ Ψₗ) C₁) (dL fL : ℕ)
  → InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xR B))
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RDestruct-auxR ctx scrut xL eL xR eR A B scrutE ds fs eLE dL fL (failure err) = failure err
inferElabV-RDestruct-auxR ctx scrut xL eL xR eR A B scrutE ds fs {C₁ = C₁} eLE dL fL (success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR) =
  inferElabV-RDestruct-join ctx scrut xL eL xR eR A B scrutE ds eLE dL eRE dR fR (join? C₁ C₂)


-- D274: a resolved reference found in Σ is a generator — a SigOp, own or not:
-- the Spec's `sigOp` at its concrete type (plan 0.122 §5.6: the realization's
-- term). Its lowering builds the operation's IR (`Surface.Elaborate.sigOpIR`).

-- D329: a generator is keyed by its rendered name, which names it alone only
-- for a word name; a name that is no word is bound to nothing written.
inferElabV-RResolved-word : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → (WordName cn → InferElabResult (NamedCtx.debruijn ctx))
  → (b : Bool) → wordNameB cn ≡ b → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RResolved-word ctx cn k false _ = failure (UnboundVariable (showCanonical cn))
inferElabV-RResolved-word ctx cn k true  e = k (subst T (sym e) tt)

inferElabV-RResolved-arrow-aux : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → NotGenerator cn → ∀ {A B : Type} {π : Once.Spec.Grade.Purity}
  → lookupImport (NamedCtx.sig ctx) (showCanonical cn)
      ≡ just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
  → (mbA : Maybe (Base ∅ₖ A)) → isBaseType? A ≡ mbA
  → (mcB : Maybe (Base ∅ₖ B)) → isBaseType? B ≡ mcB
  → InferElabResult (NamedCtx.debruijn ctx)
-- Concreteness-driven arrow value emission (de-withed for Completeness).
inferElabV-RResolved-arrow-aux ctx cn ng {A} {B} {π} eq (just bA) _ (just cB) _ =
  inferElabV-RResolved-word ctx cn (λ wn →
    success (wk₀ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) _
      (Surface.sigOp cn (con-fun bA cB))
      0 0) (wordNameB cn) refl
inferElabV-RResolved-arrow-aux ctx cn ng {A} {B} {π} eq nothing _ _ _ =
  failure (NonConcreteSigOpType (showCanonical cn)
            (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B))
inferElabV-RResolved-arrow-aux ctx cn ng {A} {B} {π} eq (just _) _ nothing _ =
  failure (NonConcreteSigOpType (showCanonical cn)
            (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B))

inferElabV-RResolved-value-aux : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → NotGenerator cn → ∀ (ty : Type)
  → lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just ty
  → (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RResolved-value-aux ctx cn ng ty eq (just conc) _ =
  inferElabV-RResolved-word ctx cn (λ wn → success (wk₀ ty) _ (Surface.sigOp cn conc) 0 0)
    (wordNameB cn) refl
inferElabV-RResolved-value-aux ctx cn ng ty eq nothing _ =
  failure (NonConcreteSigOpType (showCanonical cn) ty)

-- D248/D274: not in Σ — an OWN reference (`own x`) may name a monomorphic
-- definition, and is then a CALL of it (D246).
inferElabV-RResolved-def : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ nothing
                         → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RResolved-own-aux : ∀ {m} (ctx : NamedCtx m) (x : String) → lookupImport (NamedCtx.sig ctx) x ≡ nothing → (lhs : Maybe Type)
  → lookupImport (NamedCtx.imports ctx) x ≡ lhs
  → InferElabResult (NamedCtx.debruijn ctx)

-- Plan 0.50: resolved-ref lookup, keyed by the canonical dotted path.
inferElabV-RResolved-aux : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → NotGenerator cn → (lhs : Maybe Type)
  → lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ lhs
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RResolved-aux ctx cn ng
  (just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) eq =
  inferElabV-RResolved-arrow-aux ctx cn ng eq (isBaseType? A) refl (isBaseType? B) refl
{-# CATCHALL #-}
inferElabV-RResolved-aux ctx cn ng (just ty) eq =
  inferElabV-RResolved-value-aux ctx cn ng ty eq (isConcrete? ty) refl
inferElabV-RResolved-aux ctx cn ng nothing eq = inferElabV-RResolved-def ctx cn eq

inferElabV-RResolved-def ctx (own x) ns = inferElabV-RResolved-own-aux ctx x ns (lookupImport (NamedCtx.imports ctx) x) refl
{-# CATCHALL #-}
inferElabV-RResolved-def ctx cn _ = failure (UnboundVariable (showCanonical cn))
-- D327: a definition's reference at any type (no concreteness gate).
inferElabV-RResolved-own-aux ctx x ns (just ty) eq = success (wk₀ ty) _ (Surface.closure x) 0 0
-- R11 (D330): an own POLYMORPHIC definition — the telescope.
inferElabV-RResolved-own-aux ctx x ns nothing eq = inferElabV-RVar-poly-aux ctx x ns eq

-- A bare name is a local: the resolver resolves every other name (a global is
-- referred to by its canonical name, R11/D330), so one bound by no local is
-- bound to nothing — the Spec's `s-var` is the only rule for a bare name.
inferElabV-RVar-lookup-aux : ∀ {m} (ctx : NamedCtx m) (x : String)
  → (locLhs : Maybe (∃[ A ] ∃[ Ψ ] (Surface.SVar (NamedCtx.debruijn ctx) Ψ A)))
  → lookupLocal ctx x ≡ locLhs
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RVar-lookup-aux ctx x (just (A , Ψ , eV)) eq-loc =
  success A Ψ (Surface.svar→expr eV) 0 0
inferElabV-RVar-lookup-aux ctx x nothing eq-loc = failure (UnboundVariable x)

-- Plan 0.4 T2: bbc-X failure-branch aux helpers. Each is hardcoded
-- to its builtin name (forced by the `bbc-X` constructor at the call
-- site). Takes lookupLocal/lookupImport results + equations as
-- explicit args (eliminating `with...in eq-loc/eq-imp` opacity).
-- Returns success at the canonical builtin type if all conditions
-- match, failure otherwise.
checkElabV-RVar-bbc-id-failure-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- bbc-X failure-branch aux bodies. Each pattern-matches on T to the
-- canonical builtin shape and on the lookup results. Success iff
-- T = canonical & both lookups nothing & inner type-checks pass.
checkElabV-RVar-bbc-id-failure-aux ctx (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Y) err with X ≟T Y
... | yes refl = withUnit (failure (BuiltinTypeMismatch "id")) π λ u →
      success Surface.zeroUsage (Surface.lift-morphism IR.id) 0 0
... | no _ = failure (BuiltinTypeMismatch "id")
checkElabV-RVar-bbc-id-failure-aux ctx Unit err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx Void err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx Int err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx Float err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx (var iᵣ) err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Spec.Type.* _) err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Spec.Type.+ _) err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx (Once.Spec.Type.μ _) err = failure err
checkElabV-RVar-bbc-id-failure-aux ctx (Once.Spec.Type.ν _ _) err = failure err

checkElabV-RVar-bbc-fst-failure-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-fst-failure-aux ctx ((A Once.Spec.Type.* B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A') err with A ≟T A'
... | yes refl = withUnit (failure (BuiltinTypeMismatch "fst")) π λ u →
      success Surface.zeroUsage (Surface.lift-morphism IR.fst) 0 0
... | no _ = failure (BuiltinTypeMismatch "fst")
checkElabV-RVar-bbc-fst-failure-aux ctx Unit err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx Void err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx Int err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx Float err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (var iᵣ) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (Unit Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (Void Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (Int Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (Float Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx ((var iᵣ) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Spec.Type.+ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Spec.Type.⇒[ _ ] _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx ((Once.Spec.Type.μ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx ((Once.Spec.Type.ν _ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (_ Once.Spec.Type.* _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (_ Once.Spec.Type.+ _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (Once.Spec.Type.μ _) err = failure err
checkElabV-RVar-bbc-fst-failure-aux ctx (Once.Spec.Type.ν _ _) err = failure err

checkElabV-RVar-bbc-snd-failure-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- bbc-snd: canonical T = (A * B) ⇒[Many,pure] B'
checkElabV-RVar-bbc-snd-failure-aux ctx ((A Once.Spec.Type.* B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B') err with B ≟T B'
... | yes refl = withUnit (failure (BuiltinTypeMismatch "snd")) π λ u →
      success Surface.zeroUsage (Surface.lift-morphism IR.snd) 0 0
... | no _ = failure (BuiltinTypeMismatch "snd")
checkElabV-RVar-bbc-snd-failure-aux ctx Unit err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx Void err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx Int err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx Float err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (var iᵣ) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (Unit Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (Void Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (Int Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (Float Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx ((var iᵣ) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Spec.Type.+ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Spec.Type.⇒[ _ ] _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx ((Once.Spec.Type.μ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx ((Once.Spec.Type.ν _ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (_ Once.Spec.Type.* _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (_ Once.Spec.Type.+ _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (Once.Spec.Type.μ _) err = failure err
checkElabV-RVar-bbc-snd-failure-aux ctx (Once.Spec.Type.ν _ _) err = failure err

checkElabV-RVar-bbc-terminal-failure-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- bbc-terminal: canonical T = A ⇒[Many,pure] Unit
checkElabV-RVar-bbc-terminal-failure-aux ctx (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] Unit) err =
  withUnit (failure (BuiltinTypeMismatch "terminal")) π λ u →
  success Surface.zeroUsage (Surface.lift-morphism IR.terminal) 0 0
checkElabV-RVar-bbc-terminal-failure-aux ctx Unit err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx Void err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx Int err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx Float err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx (var iᵣ) err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.* _) err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.+ _) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Void) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Int) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Float) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (var iᵣ)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (_ Once.Spec.Type.* _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (_ Once.Spec.Type.+ _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (_ Once.Spec.Type.⇒[ _ ] _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (Once.Spec.Type.μ _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (Once.Spec.Type.ν _ _)) err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] Unit) err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] Unit) err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx (Once.Spec.Type.μ _) err = failure err
checkElabV-RVar-bbc-terminal-failure-aux ctx (Once.Spec.Type.ν _ _) err = failure err

checkElabV-RVar-bbc-initial-failure-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- bbc-initial: canonical T = Void ⇒[Many,pure] A
checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A) err =
  withUnit (failure (BuiltinTypeMismatch "initial")) π λ u →
  success Surface.zeroUsage (Surface.lift-morphism IR.initial) 0 0
checkElabV-RVar-bbc-initial-failure-aux ctx Unit err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx Void err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx Int err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx Float err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (var iᵣ) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (_ Once.Spec.Type.* _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (_ Once.Spec.Type.+ _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (Unit Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (Int Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (Float Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx ((var iᵣ) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Spec.Type.* _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Spec.Type.+ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Spec.Type.⇒[ _ ] _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx ((Once.Spec.Type.μ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx ((Once.Spec.Type.ν _ _) Once.Spec.Type.⇒[ _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (Once.Spec.Type.μ _) err = failure err
checkElabV-RVar-bbc-initial-failure-aux ctx (Once.Spec.Type.ν _ _) err = failure err

checkElabV-RVar-bbc-inl-failure-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- bbc-inl: canonical T = A ⇒[Many,pure] (A' + B)
checkElabV-RVar-bbc-inl-failure-aux ctx (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] (A' Once.Spec.Type.+ B)) err with A ≟T A'
... | yes refl = withUnit (failure (BuiltinTypeMismatch "inl")) π λ u →
      success Surface.zeroUsage (Surface.lift-morphism (IR.inl)) 0 0
... | no _ = failure (BuiltinTypeMismatch "inl")
checkElabV-RVar-bbc-inl-failure-aux ctx Unit err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx Void err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx Int err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx Float err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx (var iᵣ) err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.* _) err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.+ _) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Unit) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Void) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Int) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Float) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (var iᵣ)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (_ Once.Spec.Type.* _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (_ Once.Spec.Type.⇒[ _ ] _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (Once.Spec.Type.μ _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (Once.Spec.Type.ν _ _)) err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] (_ Once.Spec.Type.+ _)) err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] (_ Once.Spec.Type.+ _)) err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx (Once.Spec.Type.μ _) err = failure err
checkElabV-RVar-bbc-inl-failure-aux ctx (Once.Spec.Type.ν _ _) err = failure err

checkElabV-RVar-bbc-inr-failure-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m) (err : TypeError)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- bbc-inr: canonical T = B ⇒[Many,pure] (A + B')
checkElabV-RVar-bbc-inr-failure-aux ctx (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] (A Once.Spec.Type.+ B')) err with B ≟T B'
... | yes refl = withUnit (failure (BuiltinTypeMismatch "inr")) π λ u →
      success Surface.zeroUsage (Surface.lift-morphism (IR.inr)) 0 0
... | no _ = failure (BuiltinTypeMismatch "inr")
checkElabV-RVar-bbc-inr-failure-aux ctx Unit err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx Void err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx Int err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx Float err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx (var iᵣ) err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.* _) err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.+ _) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Unit) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Void) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Int) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] Float) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (var iᵣ)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (_ Once.Spec.Type.* _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (_ Once.Spec.Type.⇒[ _ ] _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (Once.Spec.Type.μ _)) err = failure err
{-# CATCHALL #-}
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ _ ] (Once.Spec.Type.ν _ _)) err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero _ ] (_ Once.Spec.Type.+ _)) err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One _ ] (_ Once.Spec.Type.+ _)) err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx (Once.Spec.Type.μ _) err = failure err
checkElabV-RVar-bbc-inr-failure-aux ctx (Once.Spec.Type.ν _ _) err = failure err

-- Per-bbc-X aux taking the inferElab result explicitly. Eliminates
-- the inner with-helper opacity. Each bbc-X's success-via-infer path
-- uses t-embed; the failure path delegates to bbc-X-failure-aux.
checkElabV-RVar-bbc-id-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- Per-bbc-X auxes: pattern-match on the inference result. The success
-- path converts it (`embedOrSubsume`); the failure path delegates to
-- bbc-X-failure-aux.
checkElabV-RVar-bbc-id-aux ctx T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved (gen "id")) T r
checkElabV-RVar-bbc-id-aux ctx T (failure err) =
  checkElabV-RVar-bbc-id-failure-aux ctx T err

checkElabV-RVar-bbc-fst-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-fst-aux ctx T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved (gen "fst")) T r
checkElabV-RVar-bbc-fst-aux ctx T (failure err) =
  checkElabV-RVar-bbc-fst-failure-aux ctx T err

checkElabV-RVar-bbc-snd-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-snd-aux ctx T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved (gen "snd")) T r
checkElabV-RVar-bbc-snd-aux ctx T (failure err) =
  checkElabV-RVar-bbc-snd-failure-aux ctx T err

checkElabV-RVar-bbc-terminal-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-terminal-aux ctx T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved (gen "terminal")) T r
checkElabV-RVar-bbc-terminal-aux ctx T (failure err) =
  checkElabV-RVar-bbc-terminal-failure-aux ctx T err

checkElabV-RVar-bbc-initial-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-initial-aux ctx T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved (gen "initial")) T r
checkElabV-RVar-bbc-initial-aux ctx T (failure err) =
  checkElabV-RVar-bbc-initial-failure-aux ctx T err

checkElabV-RVar-bbc-inl-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-inl-aux ctx T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved (gen "inl")) T r
checkElabV-RVar-bbc-inl-aux ctx T (failure err) =
  checkElabV-RVar-bbc-inl-failure-aux ctx T err

checkElabV-RVar-bbc-inr-aux : ∀ {m} (ctx : NamedCtx m) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-inr-aux ctx T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved (gen "inr")) T r
checkElabV-RVar-bbc-inr-aux ctx T (failure err) =
  checkElabV-RVar-bbc-inr-failure-aux ctx T err

-- D136 dispatchers. View + its defining equation, so a caller can recover
-- `classifyGen cn ≡ gv` after a `with`-match (the `viewBundle` idiom).
inferElabV-RResolved-dispatch : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → GenView cn
  → InferElabResult (NamedCtx.debruijn ctx)
-- `unit` is the one generator that INFERS; the rest are polymorphic and only
-- check, so they fall to the ordinary resolved path (which reports the right
-- error for a bare use).
inferElabV-RResolved-dispatch ctx _ gv-unit =
  success Unit _ Surface.unit 0 0
-- D136: a generator's canonical name is COMPILER-OWNED, so looking it up in
-- the user's import table is meaningless — these fail directly rather than
-- routing through `inferElabV-RResolved-aux`. The seven point-free
-- generators are polymorphic and do not infer; they must appear applied or
-- in check mode, which is what `UnboundVariable` has always reported here.
-- Failing directly is also what lets the `checkElab-fallback-RVar-*` lemmas
-- reduce without a "Generators.* is not imported" premise nobody could supply.
inferElabV-RResolved-dispatch ctx cn gv-id       = failure (UnboundVariable "id")
inferElabV-RResolved-dispatch ctx cn gv-fst      = failure (UnboundVariable "fst")
inferElabV-RResolved-dispatch ctx cn gv-snd      = failure (UnboundVariable "snd")
inferElabV-RResolved-dispatch ctx cn gv-terminal = failure (UnboundVariable "terminal")
inferElabV-RResolved-dispatch ctx cn gv-initial  = failure (UnboundVariable "initial")
inferElabV-RResolved-dispatch ctx cn gv-inl      = failure (UnboundVariable "inl")
inferElabV-RResolved-dispatch ctx cn gv-inr      = failure (UnboundVariable "inr")
inferElabV-RResolved-dispatch ctx cn (gv-other ng) = inferElabV-RResolved-aux ctx cn ng _ refl

-- A resolved reference that infers is embedded; one that does not may be an
-- own polymorphic definition, checked at an instance of its schema (R11/D330).
checkElabV-RResolved-other : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RResolved-other ctx cn T r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RResolved cn) T r
checkElabV-RResolved-other ctx (canonical []) T (failure err) = failure err
-- Plan 0.103 phase 2a: the rule's premises are DECIDED — not a declaration nor
-- a monomorphic definition, a non-ground telescope entry, at an instance of
-- its schema.
checkElabV-RResolved-other ctx (own x) T (failure err) =
  checkElabV-RVar-poly-check-aux ctx x T err
    (lookupImport (NamedCtx.sig ctx) x) refl (lookupImport (NamedCtx.imports ctx) x) refl
    (lookupPolyPrefix (NamedCtx.polys ctx) x) refl
checkElabV-RResolved-other ctx (canonical (_ ∷ _ ∷ _)) T (failure err) = failure err

checkElabV-RResolved-dispatch : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) (T : Ty m) → GenView cn
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RResolved-dispatch ctx _ T gv-id rInfV =
  checkElabV-RVar-bbc-id-aux ctx T rInfV
checkElabV-RResolved-dispatch ctx _ T gv-fst rInfV =
  checkElabV-RVar-bbc-fst-aux ctx T rInfV
checkElabV-RResolved-dispatch ctx _ T gv-snd rInfV =
  checkElabV-RVar-bbc-snd-aux ctx T rInfV
checkElabV-RResolved-dispatch ctx _ T gv-terminal rInfV =
  checkElabV-RVar-bbc-terminal-aux ctx T rInfV
checkElabV-RResolved-dispatch ctx _ T gv-initial rInfV =
  checkElabV-RVar-bbc-initial-aux ctx T rInfV
checkElabV-RResolved-dispatch ctx _ T gv-inl rInfV =
  checkElabV-RVar-bbc-inl-aux ctx T rInfV
checkElabV-RResolved-dispatch ctx _ T gv-inr rInfV =
  checkElabV-RVar-bbc-inr-aux ctx T rInfV
checkElabV-RResolved-dispatch ctx cn T gv-unit  rInfV = embedOrSubsume ctx (Raw.RResolved cn) T rInfV
checkElabV-RResolved-dispatch ctx cn T (gv-other ng) rInfV = checkElabV-RResolved-other ctx cn T rInfV

checkElabV-RVar-bbc-other-aux : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-other-aux ctx x T r = embedOrSubsume ctx (Raw.RVar x) T r


checkElabV-RFloat-aux : ∀ {m} (ctx : NamedCtx m) (i f l : ℕ) (T : Ty m)
  → CheckElabResult (NamedCtx.debruijn ctx) T
-- RInt: value-lift on a pure-arrow-to-Int target, else generic infer+match.
-- `refl` refines `T` to the arrow so `t-value-lift (g-int n)` types; the
-- `nothing` branch reproduces the old generic clause for RInt verbatim.
-- RFloat: value-lift on a pure-arrow-to-Float target; otherwise embed at
-- `Float` or report a genuine type mismatch. The only failure left is a type
-- mismatch — representability is no longer a way to fail.
checkElabV-RFloat-aux ctx i f l T with Once.Spec.Type.Float <:? T
... | yes s = success Surface.zeroUsage (Surface.coerce s (Surface.float (decimalOf i f l))) 0 0
... | no _  = failure (TypeMismatch T Once.Spec.Type.Float)

-- RFloat infer-mode. No dispatch left at all — it is the `RInt` clause with
-- `decimalOf` in place of the digit.
inferElabV-RFloat-aux : ∀ {m} (ctx : NamedCtx m) (i f l : ℕ)
  → InferElabResult (NamedCtx.debruijn ctx)
-- RFloat: F4's decision, made once and passed in.
--
-- The accepted branch builds the Surface node from the literal the Spec's
-- `wt-float` types, so the elaborated term and its typing derivation cannot
-- disagree about which literals are legal.
--
-- The rejected branch is a REAL ERROR carrying the digits the user wrote,
-- not a rounded value. That is the whole point of plan 0.71: `0.1` does not
-- become the nearest double, it fails to compile.
-- TOTAL. `FloatNotRepresentable` is unreachable from here now; the literal
-- always elaborates and the target rounds it.
inferElabV-RFloat-aux ctx i f l =
  success Float _ (Surface.float (decimalOf i f l)) 0 0

mutual
  -- RVar dispatch helper (plan 0.6 Phase C.7 POC-1). Separates
  -- specialised bare-builtin handling from the generic lookup path.
  -- `pair f g` in check mode, at its target view (`Once.TypeCheck.TargetView`);
  -- likewise below. The dispatch has already read the head (`ahv-pair-applied`).
  checkPairOn : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) → PairTarget T
              → CheckElabResult (NamedCtx.debruijn ctx) T
  -- Plan 0.36 Phase 2a follow-up: check-mode for the pair LITERAL
  -- `(a , b)` at a product type — checks components bidirectionally.
  checkPairLit : ∀ {m} → (ctx : NamedCtx m) → (a b : Syn.Expr) → (A B : Ty m)
               → CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.* B)
  -- `case f g` (the copair) in check mode, at `(A + B) ⇒[Many] C`.
  checkCaseOn : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) → CaseTarget T
              → CheckElabResult (NamedCtx.debruijn ctx) T
  -- The arm-checking core of `case`, parameterised by the copair domains A B, codomain C, and grade π.
  -- Extracting it lets the eff-subsumption clause of `checkCaseOn` call it at two
  -- grades (try eff; else pure + arr'/t-subsume) without duplicating the body.
  checkCaseGo : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (A B C : Ty m) (π : Once.Spec.Grade.Purity)
              → CheckElabResult (NamedCtx.debruijn ctx) ((A Once.Spec.Type.+ B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  -- Compose / curry / apply classifier helpers (plan 0.6 Phase C.7
  -- POC-3).
  checkComposeOn : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) → ArrowTarget T
                 → CheckElabResult (NamedCtx.debruijn ctx) T
  -- Plan 0.94 §10: the middle type, locally determined. `g`'s side first (the
  -- domain-given mode), then `f`'s (its synthesized input), else an annotation
  -- is needed.
  elabGiven : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
             → GivenElabResult (NamedCtx.debruijn ctx) A π
  elabGivenApp : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
               → AppHeadView f → InferElabResult (NamedCtx.debruijn ctx)
               → GivenElabResult (NamedCtx.debruijn ctx) A π
  checkCompose-g : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity)
                 → GivenElabResult (NamedCtx.debruijn ctx) A π
                 → CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  checkCompose-f : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity)
                 → CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  checkCurry : ∀ {m} → (ctx : NamedCtx m) → (arg : Syn.Expr) → (T : Ty m)
             → CheckElabResult (NamedCtx.debruijn ctx) T
  checkCurryOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) → CurryTarget T
               → CheckElabResult (NamedCtx.debruijn ctx) T
  inferOut : ∀ {m} → (ctx : NamedCtx m) → (arg : Syn.Expr)
           → InferElabResult (NamedCtx.debruijn ctx)

  checkIn : ∀ {m} → (ctx : NamedCtx m) → (arg : Syn.Expr) → (T : Ty m)
          → CheckElabResult (NamedCtx.debruijn ctx) T
  checkInOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) → InTarget T
            → CheckElabResult (NamedCtx.debruijn ctx) T
  checkInGo : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) (F : Once.Spec.Type.Fun m)
            → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
            → wfFun? (NamedCtx.kinds ctx) F ≡ mw
            → CheckElabResult (NamedCtx.debruijn ctx) (Once.Spec.Type.μ F)
  checkCata : ∀ {m} → (ctx : NamedCtx m) → (arg : Syn.Expr) → (T : Ty m)
            → CheckElabResult (NamedCtx.debruijn ctx) T
  checkCataOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) → CataTarget T
              → CheckElabResult (NamedCtx.debruijn ctx) T
  -- Plan 0.36 Phase 2a: dispatch on `wellFormedF? F`; the algebra is
  -- elaborated as an ordinary function in the EMPTY context (see clause).
  checkCataGo : ∀ {m} → (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m)
                (π : Once.Spec.Grade.Purity)
              → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F)) → wfFun? (NamedCtx.kinds ctx) F ≡ mw
              → CheckElabResult (NamedCtx.debruijn ctx) (Once.Spec.Type.μ F Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A)

  -- D192: `ana coalg` — `checkCata`'s dual, declared beside it so the mirror
  -- is visible. `F` is read from the expected `A ⇒ ν-type F`, exactly as the
  -- cata reads it from `μ-type F ⇒ A`.
  checkAna : ∀ {m} → (ctx : NamedCtx m) → (arg : Syn.Expr) → (T : Ty m)
           → CheckElabResult (NamedCtx.debruijn ctx) T
  checkAnaOn : ∀ {m} → (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) → AnaTarget T
             → CheckElabResult (NamedCtx.debruijn ctx) T
  checkAnaGo : ∀ {m} → (ctx : NamedCtx m) (coalg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m)
               (π₀ : Once.Spec.Grade.Purity) (φ : Once.Spec.Grade.Finite)
             → π₀ ⊑π Once.Spec.Grade.act
             → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F)) → wfFun? (NamedCtx.kinds ctx) F ≡ mw
             → CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π₀ ] Once.Spec.Type.ν F φ)
  -- D317/D319: `ana round` at `A ⇒[eff] B` — the loop. Decided on the round's
  -- own check result (a helper, not a `with`).
  checkLoop : ∀ {m} → (ctx : NamedCtx m) (round : Syn.Expr) (A B : Ty m)
            → CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] (B Once.Spec.Type.+ A))
            → CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.eff ] B)


  -- Plan 0.4 T0 Option B — verified elaborator declarations.
  inferElab : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
  checkElab : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T
  -- Plan 0.58 E1-full: the WORKER carries a well-founded `Acc` on `length polys`
  -- so the poly-reference case can resolve INLINE (re-elaborate the def body in its
  -- strictly-smaller prefix). Non-poly recursion goes through the Acc-free wrapper
  -- `checkElabV` (which re-derives a FRESH `<-wellFounded` — sound per POC-B), so the
  -- ~300 existing call sites are unchanged.
  checkElab-wf : ∀ {m} → (ctx : NamedCtx m) → Acc _<_ (length (NamedCtx.polys ctx))
                → (e : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T
  -- compose check-mode helper, threading the inner checkElabV results
  -- as explicit arguments + (unused) equations. The eqs are unused in
  -- the body (they're just placeholders for the J-style bridge in
  -- proofs). This lets external proofs substitute checkElab-success
  -- premises into the dispatch chain without navigating opaque
  -- `with`-helpers.
  inferElabV-RApp-other : ∀ {m} → (ctx : NamedCtx m) (f x : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
  -- PLAN 0.74 J6 step 3: a minus directly on a NUMERAL is one literal, not a
  -- runtime negation of another one. Split out as a named dispatch (the
  -- file's `inferElabV-RApp-dispatch` convention) so the definitional
  -- reduction that stops holding is confined to this function.
  inferElabV-neg-dispatch : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr)
    → InferElabResult (NamedCtx.debruijn ctx)
  inferElabV-neg-aux : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr)
    → NegOperandView e
    → InferElabResult (NamedCtx.debruijn ctx)
  -- CHECK-mode twin of the same dispatch. A negated literal at a pure-arrow
  -- target is its constant morphism, exactly as a bare literal is; anything
  -- else falls to the generic infer-and-match the `RNeg` clause used
  -- before. ONE scrutinee per aux, the `checkElabV-RInt-aux` convention.
  --
  -- EACH BRANCH IS SELF-CONTAINED — no shared `inferElabV ctx (RNeg
  -- e)` threaded in, and that is forced twice over. Once by TERMINATION: the
  -- dispatch receives the OPERAND, so rebuilding `RNeg e` inside it
  -- is growth to foetus. Once by REDUCTION: a downstream proof that has
  -- with-abstracted `negOperandView e` needs the branch body to mention only
  -- terms that still reduce under that abstraction, and
  -- `inferElabV ctx (RNeg e)` does not — it unfolds back into the
  -- view. So the literal branches state their folded result outright (they
  -- know it: the fold has no premise) and only the non-literal branch calls
  -- into inference, at the OPERAND, which is what `inferElabV-RNeg-aux`
  -- takes anyway.
  checkElabV-neg-dispatch : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
    → NegOperandView e
    → CheckElabResult (NamedCtx.debruijn ctx) T
  -- RLet/RDestruct: the later sub-expressions live in EXTENDED contexts whose
  -- types come from the earlier sub-results, so they fold through nested auxes
  -- (each takes the prior result's data explicitly — no inline `with`).
  inferElabV-RLet-aux : ∀ {m} → (ctx : NamedCtx m) (x : String) (e₁ e₂ : Syn.Expr)
    → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
  -- RDestruct de-withed into three nested auxes (one per `with` level):
  -- `-aux` dispatches the scrutinee type, `-auxL` the left branch (in `ctx,xL:A`),
  -- `-auxR` the right branch (in `ctx,xR:B`) + the branch-type match. Behaviour-
  -- preserving extraction of the old inline `with` chain so external proofs can
  -- case the dispatch without `with`-opacity.
  inferElabV-RDestruct-aux : ∀ {m} → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
    → InferElabResult (NamedCtx.debruijn ctx)
    → InferElabResult (NamedCtx.debruijn ctx)
  inferElabV-RDestruct-auxL : ∀ {m} → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
    (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)}
    (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds fs : ℕ)
    → InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))
    → InferElabResult (NamedCtx.debruijn ctx)
  inferElabV-RApp-other-aux : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (lhs : Maybe PolyBuiltinApp)
    → classifyAppHead f ≡ lhs
    → InferElabResult (NamedCtx.debruijn ctx)
  inferElabV-RApp-dispatch : ∀ {m} (ctx : NamedCtx m) (f arg : Syn.Expr) (vw : AppHeadView f)
    → classifyAppHeadView f ≡ vw
    → InferElabResult (NamedCtx.debruijn ctx)
  checkElabV-RApp-dispatch : ∀ {m} (ctx : NamedCtx m) (f arg : Syn.Expr) (T : Ty m) (vw : AppHeadView f)
    → classifyAppHeadView f ≡ vw
    → CheckElabResult (NamedCtx.debruijn ctx) T
  -- D230: the spine — the head's domain-given mode at the argument's synthesized type.
  inferSpine : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) → classifyAppHead f ≡ nothing
    → InferElabResult (NamedCtx.debruijn ctx)
    → InferElabResult (NamedCtx.debruijn ctx)

  -- D127: NO value-lift dispatch. A literal has ONE meaning at ONE type, so
  -- check mode is infer-and-match and nothing about the literal is decided by
  -- the expected type. The `Maybe (X , π , T ≡ X ⇒ Int)` scrutinee these two
  -- carried WAS the target-directedness, and it is gone with the lift.
  checkElabV-RInt-aux : ∀ {m} (ctx : NamedCtx m) (n : ℤ) (T : Ty m)
    → CheckElabResult (NamedCtx.debruijn ctx) T


  -- RPair check-mode dispatch, taking the target classification explicitly
  -- (product / pure-arrow-to-product / other). One scrutinee, no overlap.
  checkElabV-RPair-aux : ∀ {m} (ctx : NamedCtx m) (a b : Syn.Expr) (T : Ty m)
    → RPairTarget T
    → CheckElabResult (NamedCtx.debruijn ctx) T

  -- ===== inferElab =====


  -- ===== checkElab =====


  -- D136: `checkElab-RVar` DELETED. It dispatched a bare `RVar` on
  -- `classifyBareBuiltin`, i.e. it decided "is this name a generator?" from the
  -- string — which is the collision this plan removes. It was also dead: the
  -- mutual block declared it and nothing ever called it.

  -- Plan 0.6 Phase C.7 POC-2: bare `pair f g` check-mode.
  -- Expected type must be `A ⇒[Many] (B * C)`. Checks each
  -- component function at its projected arrow shape, then emits
  -- `app (app specPair fE) gE`. No lookup-first branch: the
  -- classifier's `ahv-pair-applied` dispatch already establishes
  -- disjointness with `t-embed (wt-app …)` — wt-app's premise
  -- `classifyAppHead f ≡ nothing` fails for the pair-applied shape.
  -- D222: ONE grade-poly clause. `π` is matched from the TARGET and the arms are
  -- checked at that same `π` — applying the pair's arrow runs both arms, so
  -- their grade IS the result's. This replaces the former pure clause plus an
  -- eff clause that checked the arms at `pure` and wrapped the result in
  -- `arr'`/`t-subsume`: that route could type an effectful pair EXPRESSION but
  -- never an effectful ARM, which is what an emitting `ana` coalgebra needs.
  checkPairOn ctx f_inner arg _ (pair-at A π B C)
    with checkElab ctx f_inner (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
  ... | failure err = failure err
  ... | success Ψf fE df frf with checkElab ctx arg (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...     | failure err = failure err
  ...     | success Ψg gE dg frg =
              success _ (Surface.fork' fE gE)
                (suc (df Data.Nat.⊔ dg)) frg
  -- Any other shape fails.
  checkPairOn _ _ _ _ pair-other = failure (BuiltinTypeMismatch "pair")

  -- Plan 0.36 Phase 2a follow-up: pair literal `(a , b)` at `A * B`.
  -- CHECK each component against its expected type (so check-only
  -- constructs like `In` get a type), emit the same `Surface.pair`.
  checkPairLit ctx a b A B with checkElab ctx a A
  ... | failure err = failure err
  ... | success Ψ₁ aE da fa with checkElab ctx b B
  ...   | failure err = failure err
  ...   | success Ψ₂ bE db fb =
          success _ (Surface.pair aE bE) (da Data.Nat.⊔ db) fb

  -- Plan 0.28 Commit 1: bare `case f g` (categorical copair) check-mode.
  -- Expected type must be `(A + B) ⇒[Many] C`. Each arm is checked at
  -- its sum-projected arrow shape. Morphism-realm fast-path: when both
  -- arms are `lift-morphism m`, emit `lift-morphism (IR.case m_f m_g)`
  -- directly — a closed CCC morphism usable as a `cata` algebra
  -- (`extract-morph` succeeds on it). Otherwise fall through to the
  -- closure-realm `app (app specCase fE) gE` form. Mirrors the
  -- `checkComposeWithBg` morphism-realm bypass but with no dependent
  -- `composeArgB` premise (so completeness stays fully proved).
  -- Plan 0.49 / D063: ONE grade-polymorphic clause (D056 — the bespoke eff
  -- copy is gone). Both arms must be morphisms (`extractMorphWitness`); emit the
  -- direct `lift-morphism (IR.case m_f m_g)`; no closure fallback.
  -- Plan 0.52 (pure⊑eff): case at an EFF outer arrow — mirror of the compose
  -- eff-clause. Try eff arms; else check the whole case at PURE and subsume.
  checkCaseOn ctx f_inner arg _ (case-at A B π C) = checkCaseGo ctx f_inner arg A B C π
  checkCaseOn _ _ _ _ case-other = failure (BuiltinTypeMismatch "case")

  checkCaseGo ctx f g A B C π
    with checkElab ctx f (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ... | failure err = failure err
  ... | success Ψf fE df frf with checkElab ctx g (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...     | failure err = failure err
  ...     | success Ψg gE dg frg =
                success _ (Surface.copair' fE gE)
                  (suc (df Data.Nat.⊔ dg)) frf

  -- `compose f g` at `A ⇒[Many π] C` (plan 0.94 §10): the middle type is
  -- determined LOCALLY — by `g` given `A` (`elabGivenV`), else by `f`'s own
  -- synthesized input — and otherwise needs an annotation.
  checkComposeOn ctx f_inner arg _ (arrow-at A π C) =
    checkCompose-g ctx f_inner arg A C π (elabGiven ctx arg A π)
  checkComposeOn _ _ _ _ arrow-other = failure (BuiltinTypeMismatch "compose")

  -- `g` determined the middle: check `f` there; if `f` does not fit, `f`'s own
  -- synthesized input may still (it can name a LARGER middle `g` converts to).
  checkCompose-g ctx f g A C π (success B Ψg gE dg frg)
        with checkElab ctx f (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ... | success Ψf fE df frf =
          success _ (Surface.comp' fE gE) (suc (df Data.Nat.⊔ dg)) frf
  ... | failure _ = checkCompose-f ctx f g A C π
  checkCompose-g ctx f g A C π (failure _) = checkCompose-f ctx f g A C π

  checkCompose-f ctx f g A C π with inferElab ctx f
  ... | success (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] C′) Ψf fE df frf with (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] C′)
               <:? (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ...   | no _ = failure ComposeMiddleUndetermined
  ...   | yes p with checkElab ctx g (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
  ...     | failure err = failure err
  ...     | success Ψg gE dg frg =
              success _ (Surface.comp' (Surface.coerce p fE) gE) (suc (df Data.Nat.⊔ dg)) frg
  {-# CATCHALL #-}
  checkCompose-f ctx f g A C π | _ = failure ComposeMiddleUndetermined

  -- The domain-given mode, one clause per `⊢ᵈ` rule.
  elabGiven ctx (Raw.RLam x body) A π with inferElab (extendNamedCtx ctx x A) body
  ... | failure err = failure err
  ... | success B (q' ∷ᵘ Ψ) bodyE d fr with decideLeq q' Once.Spec.Grade.Many
  ...   | just _ = withUnit (failure (BuiltinTypeMismatch "lambda")) π λ u →
                    success B Ψ (Surface.lam Once.Spec.Grade.Many (≤q-Many q') bodyE) (suc d) fr
  ...   | nothing = failure (UsageViolation x Once.Spec.Grade.Many q')
  elabGiven ctx (Raw.RResolved cn) A π = elabGivenLeaf ctx cn A π (classifyAppHeadView (Raw.RResolved cn)) (inferElab ctx (Raw.RResolved cn))
  elabGiven ctx (Raw.RApp f g) A π = elabGivenApp ctx f g A π (classifyAppHeadView f) (inferElab ctx (Raw.RApp f g))
  {-# CATCHALL #-}
  elabGiven ctx e A π = given-infer ctx e A π (inferElab ctx e)


  -- The combinators: each arm is given ITS input, and the outputs assemble.
  elabGivenApp ctx .(Raw.RApp (Raw.RResolved (gen "compose")) f) g A π (ahv-compose-applied {f}) _
        with elabGiven ctx g A π
  ... | failure err = failure err
  ... | success M Ψg gE dg frg with elabGiven ctx f M π
  ...   | failure err = failure err
  ...   | success B Ψf fE df frf =
            success B _ (Surface.comp' fE gE) (suc (df Data.Nat.⊔ dg)) frf
  elabGivenApp ctx .(Raw.RApp (Raw.RResolved (gen "case")) f) g (A Once.Spec.Type.+ B) π (ahv-case-applied {f}) _
        with elabGiven ctx f A π
  ... | failure err = failure err
  ... | success C Ψf fE df frf with elabGiven ctx g B π
  ...   | failure err = failure err
  ...   | success C′ Ψg gE dg frg = given-case-join ctx f g A B π fE df gE dg frg (join? C C′)
  {-# CATCHALL #-}
  elabGivenApp ctx .(Raw.RApp (Raw.RResolved (gen "case")) f) g _ π (ahv-case-applied {f}) _ =
    failure (BuiltinTypeMismatch "case")
  elabGivenApp ctx .(Raw.RApp (Raw.RResolved (gen "pair")) f) g A π (ahv-pair-applied {f}) _
        with elabGiven ctx f A π
  ... | failure err = failure err
  ... | success B Ψf fE df frf with elabGiven ctx g A π
  ...   | failure err = failure err
  ...   | success C Ψg gE dg frg =
            success (B Once.Spec.Type.* C) _ (Surface.fork' fE gE) (suc (df Data.Nat.⊔ dg)) frg
  elabGivenApp ctx .(Raw.RResolved (gen "cata")) alg (Once.Spec.Type.μ F) π ahv-cata _ with wfFun? (NamedCtx.kinds ctx) F
  ... | nothing = failure (BuiltinTypeMismatch "cata")
  ... | just wfF =
          given-cata ctx alg F π wfF (inferElab ctx alg)
  {-# CATCHALL #-}
  elabGivenApp ctx .(Raw.RResolved (gen "cata")) alg _ π ahv-cata _ = failure (BuiltinTypeMismatch "cata")
  {-# CATCHALL #-}
  elabGivenApp ctx f g A π _ r = given-infer ctx (Raw.RApp f g) A π r

  -- Plan 0.6 Phase C.7 POC-3: `curry f` check-mode.
  -- Expected `A ⇒[Many] (B ⇒[Many] C)`. Check f at `(A * B) ⇒[Many] C`.
  -- D222: ONE clause, with the two purities read off the denotation. The OUTER
  -- grade `π₀` is matched and otherwise ignored — `evalᴰ (curry f)` is a
  -- `returnT`, so building the closure emits nothing at any grade. The BODY is
  -- checked at the INNER arrow's `π`, because that is the arrow `apply` runs.
  --
  -- The former pair of clauses had this backwards: both fixed the inner arrow
  -- (and the body) to `pure` and varied the OUTER one, so `Eff Int (Int -> Int)`
  -- was accepted while `Int -> Eff Int Unit` — a curried effectful
  -- continuation, the case that actually needs a grade — was rejected.
  checkCurry ctx arg T = checkCurryOn ctx arg T (curryTarget T)
  checkCurryOn ctx arg _ (curry-at A π₀ B π C)
    with checkElab ctx arg ((A Once.Spec.Type.* B) Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] C)
  ... | failure err = failure err
  ... | success Ψ argE d fr =
          withUnit (failure (BuiltinTypeMismatch "curry")) π₀ λ u →
          success _ (Surface.curry' argE) (suc d) fr
  checkCurryOn _ _ _ curry-other = failure (BuiltinTypeMismatch "curry")


  -- Plan 0.28 Commit 2: `In arg` (μ-introduction) check-mode at `μ-type F`.
  -- Read F from the expected μ-type, gate on `wellFormedF? F` (threaded
  -- through `checkInGo`), check the argument at the functor layer, emit
  -- `morph-app (IR.In wfF Heap) argE`.
  checkIn ctx arg T = checkInOn ctx arg T (inTarget T)
  checkInOn ctx arg _ (in-at F) = checkInGo ctx arg F (wfFun? (NamedCtx.kinds ctx) F) refl
  -- D127: `In arg` at an ARROW type is no longer a lift. It falls through to
  -- the mismatch below, and the program writes `\_ -> In arg`.
  checkInOn _ _ _ in-other = failure (BuiltinTypeMismatch "In")

  -- D194: `Out v` — INFER. The argument is inferred, `ν-type F` read off its
  -- type, and `F`'s well-formedness decided exactly as `In`/`cata`/`ana` do.
  -- `Go` takes the decision as an explicit argument with its `refl` witness,
  -- for `checkInGo`'s reason: the completeness fallbacks reduce it with plain
  -- nested `with | eq`.
  inferOut ctx arg = inferOutOn ctx arg (inferElab ctx arg)


  checkInGo ctx arg F nothing _ = failure (BuiltinTypeMismatch "In")
  checkInGo ctx arg F (just wfF) eqW with checkElab ctx arg (⟦ F ⟧F (Once.Spec.Type.μ F))
  ... | failure err = failure err
  ... | success Ψ argE d fr =
        success _ (Surface.morph-app (subst (λ o → IR o ⌊ Once.Spec.Type.μ F ⌋) (sym (⌊⟧T-commute F (Once.Spec.Type.μ F))) (IR.In (wf-⌊⌋ wfF))) argE) (suc d) fr

  -- Plan 0.28 Commit 2: `cata alg` (catamorphism) check-mode at
  -- `μ-type F ⇒[Many] A`. The algebra is compiled by the self-contained
  -- `morphRaw?`/`morphToIR` (no elaborator extraction); the three
  -- decidable results are threaded through `checkCataA/B/C` so the
  -- witness carries the equations and completeness reduces cleanly.
  -- Emits `lift-morphism (IR.Cata wfF algIR)`.
  -- Plan 0.54 (pure⊑eff): cata at an EFF outer arrow. A cata is just another
  -- morphism whose grade FOLLOWS its algebra — so mirror checkCompose/checkCurry:
  -- first try the genuinely-eff Go (algebra checked at eff); if that fails (a
  -- PURE algebra, whose eff-check subsumes to a `t-subsume` that carries no
  -- `extractMorphWitness`), check the whole cata at PURE and subsume via
  -- arr'/t-subsume. This ACCEPTS `cata pureAlg` at an eff position (soundness of
  -- the `subsume-complete` m-cata bridge).
  checkCata ctx alg T = checkCataOn ctx alg T (cataTarget T)
  checkCataOn ctx alg _ (cata-at F π A) = checkCataGo ctx alg F A π (wfFun? (NamedCtx.kinds ctx) F) refl
  checkCataOn _ _ _ cata-other = failure (BuiltinTypeMismatch "cata")

  -- Plan 0.36 Phase 2a: the algebra is ANY function `⟦F⟧T A → A`.
  -- PLAN 0.101 (D265): checked in the AMBIENT context — it may capture
  -- locals — and its usage is the cata's.
  checkCataGo ctx alg F A π nothing _ = failure (BuiltinTypeMismatch "cata")
  checkCataGo ctx alg F A π (just wfF) eqW
    with checkElab ctx alg (⟦ F ⟧F A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] A)
  ... | failure err = failure err
  -- D127: no witness extraction. The algebra's own check-derivation IS the
  -- premise, and the empty debruijn context is what `Surface.cata` demands of
  -- the algebra it carries — the closedness is enforced by the CONTEXT, as it
  -- always was, not by a realm.
  ... | success Ψ algE d fr = withUnit (failure (BuiltinTypeMismatch "cata")) π λ u →
          success _ (Surface.cata wfF algE) (suc d) fr
            -- PLAN 0.80 A1: the rule takes the WITNESS, not the decider
            -- equation. `wfF` is the decider's own output, bound by the
            -- `just wfF` pattern above — so the elaborator hands over exactly
            -- what it computed, and `eqW` is now only bookkeeping for the
            -- completeness proof's `J`-style helpers.

  -- D192: the unfold. Same three moves as the fold — read `F` from the
  -- expected type, decide `WFFun ∅ₖ F`, check the coalgebra — with the
  -- coalgebra's arrow pointing the other way. PLAN 0.101 (D273): checked in
  -- the AMBIENT context — it may capture locals — and its usage is the ana's.
  checkAna ctx coalg T = checkAnaOn ctx coalg T (anaTarget T)
  checkAnaOn ctx coalg _ (ana-at A π₀ F π ua) = checkAnaGo ctx coalg F A π₀ π ua (wfFun? (NamedCtx.kinds ctx) F) refl
  checkAnaOn ctx round _ (loop-at A B) =
    checkLoop ctx round A B
      (checkElab ctx round (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] (B Once.Spec.Type.+ A)))
  checkAnaOn _ _ _ ana-other = failure (BuiltinTypeMismatch "ana")

  checkAnaGo ctx coalg F A π₀ φ ua nothing _ = failure (BuiltinTypeMismatch "ana")
  checkAnaGo ctx coalg F A π₀ φ ua (just wfF) eqW
    with checkElab ctx coalg (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many (Once.Spec.Grade.fin φ) ] ⟦ F ⟧F A)
  ... | failure err = failure err
  ... | success Ψ coalgE d fr = withUnit (failure (BuiltinTypeMismatch "ana")) π₀ λ u →
          success _ (Surface.ana wfF coalgE) (suc d) fr

  checkLoop ctx round A B (failure err) = failure err
  checkLoop ctx round A B (success Ψ roundE d fr) =
    success _ (Surface.loop roundE) (suc d) fr


------------------------------------------------------------------------
-- Generic-fallback lemmas (G2 completeness — check-mode).
--
-- These hoisted-helpers say: for each Syn.Expr shape whose check-mode
-- clause is NOT specialised (i.e. falls through to the generic
-- `with inferElab ctx e` fallback at line ~895), a successful
-- inferElab result transports to a successful checkElab result at the
-- same type. The proof strategy in each case:
--
--   (1) Rewrite with the inferElab success equation, so the fallback's
--       `with inferElab ctx e` reduces to `success T Ψ eE d f`.
--   (2) Case-split on `T ≟T T`; the `yes refl` branch yields the
--       success; the `no` branch is absurd (`⊥-elim (¬refl refl)`).
--
-- The lemmas live in `Elaborate.agda` (not `Completeness.agda`) because
-- they are structural facts about `checkElab`'s operational behaviour,
-- proved by direct reduction — they belong alongside `decideLeq` and
-- `classifyAppHead`, the other elaborator-fact helpers hoisted here.
-- Dependency: downstream `Completeness.agda` uses these to complete
-- the `t-embed` case of the check-mode walk (G2 full-walk).
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G2.
------------------------------------------------------------------------


  -- ===== The elaborator bodies =====

  ----------------------------------------------------------------------
  -- Phase A — easy `inferElab` clauses (literals, RLam-failure,
  -- RAnnot, RPair).
  ----------------------------------------------------------------------

  inferElab ctx (Raw.RInt n) =
    success Int _ (Surface.int n) 0 0

  inferElab ctx (Raw.RFloat i f l) = inferElabV-RFloat-aux ctx i f l


  inferElab ctx Raw.RUnit =
    success Unit _ Surface.unit 0 0

  inferElab ctx (Raw.RLam _ _) =
    failure LambdaInInferMode

  inferElab ctx (Raw.RAnnot e T) = inferElabV-RAnnot-aux ctx e T (checkElab ctx e (wk₀ T))

  inferElab ctx (Raw.RPair a b) =
    inferElabV-RPair-aux ctx a b (inferElab ctx a) (inferElab ctx b)

  ----------------------------------------------------------------------
  -- Phase B — lookup-driven clauses (RQualified, RVar, RNeg,
  -- RLet, RDestruct). RBinOp deferred (more complex op + type
  -- dispatch).
  ----------------------------------------------------------------------

  -- The resolver reads every `name@alias` (an unknown alias as a path of one
  -- component), so an unresolved one is never well typed.
  inferElab ctx (Raw.RQualified name alias) = failure (UnboundQualified name alias)

  -- D136: ONE clause, routed through the `GenView`. Concrete
  -- `RResolved (gen "g")` clauses here would stop `checkElabV`/`inferElabV`
  -- reducing for an ABSTRACT `cn`, which the downstream proofs depend on —
  -- the same reason `checkElabV-RApp-dispatch` takes its view as a parameter.
  inferElab ctx (Raw.RResolved cn) =
    inferElabV-RResolved-dispatch ctx cn (classifyGen cn)

  -- D136: a bare `RVar` is NEVER a generator — the resolver has already turned
  -- an unshadowed generator into `RResolved (gen g)`. So this path is ordinary
  -- variables only, and the `"unit"` special case moved to `RResolved` below.
  inferElab ctx (Raw.RVar x) =
    inferElabV-RVar-lookup-aux ctx x _ refl

  inferElab ctx (Raw.RNeg e) = inferElabV-neg-dispatch ctx e

  inferElab ctx (Raw.RLet x e₁ e₂) =
    inferElabV-RLet-aux ctx x e₁ e₂ (inferElab ctx e₁)

  inferElab ctx (Raw.RDestruct scrut xL eL xR eR) =
    inferElabV-RDestruct-aux ctx scrut xL eL xR eR (inferElab ctx scrut)

  ----------------------------------------------------------------------
  -- Phase C — `inferElab` `RApp` (13 view branches).
  ----------------------------------------------------------------------

  inferElab ctx (Raw.RApp f arg) =
    inferElabV-RApp-dispatch ctx f arg _ refl

  ----------------------------------------------------------------------
  -- inferElabV `RBinOp` — both operands must be Int. The result type
  -- depends on `op`: arithmetic ops produce Int via `wt-binop-arith`,
  -- comparison ops produce Unit + Unit via `wt-binop-cmp`. The
  -- `isArithmeticOp` / `isComparisonOp` premises reduce to `refl` once
  -- `op` is concretely matched.
  ----------------------------------------------------------------------

  inferElab ctx (Raw.RBinOp op e₁ e₂) =
    inferElabV-RBinOp-aux ctx op e₁ e₂ (inferElab ctx e₁) (inferElab ctx e₂)

  ----------------------------------------------------------------------
  -- Phase D — `checkElab` clauses.
  -- Specialised Syn.Expr shapes (RVar, RApp, RLam) are still TODO; they
  -- delegate to the existing `checkElab`. Everything else uses the
  -- generic infer-and-match fallback, with the witness lifted via
  -- `t-embed`.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- Phase F migration of `checkElab` `RApp` (13 view branches).
  -- Specialised check-mode rules: `wt-inl-app-check`, `wt-inr-app-check`,
  -- `wt-initial-app-check`, `t-arr-app-check`.
  -- Fall-through branches convert the inferred result (`embedOrSubsume`).
  -- Helper-applied branches (pair / compose / curry / apply) delegate
  -- to the existing helpers.
  ----------------------------------------------------------------------

  checkElab-wf ctx ac (Raw.RApp f arg) T =
    checkElabV-RApp-dispatch ctx f arg T _ refl

  -- RLam check-mode at ANY arrow: `wt-lam` is grade-poly (D226 — abstraction
  -- introduces no effect; D069's principle).
  checkElab-wf ctx ac (Raw.RLam x body) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B) with checkElab (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success (q' ∷ᵘ Ψ) bodyE d fr with decideLeq q' q
  ...   | just eq = withUnit (failure (BuiltinTypeMismatch "lambda")) π λ u →
                    success _ (Surface.lam q eq bodyE) (suc d) fr
  ...   | nothing = failure (UsageViolation x q q')
  -- Non-arrow T: a lambda has no check-mode rule.
  {-# CATCHALL #-}
  checkElab-wf ctx ac (Raw.RLam _ _) _ = failure LambdaRequiresFunctionType

  ----------------------------------------------------------------------
  -- Phase E — `checkElab` `RVar` migration via `classifyBareBuiltin`
  -- dispatch: one `bbc-X` clause per generator.
  ----------------------------------------------------------------------

  -- Plan 0.4 T2 Phase 3: per-bbc-X aux takes inferElab result + eq
  -- explicitly. The outer with on classifyBareBuiltin remains, and
  -- we use a second with on inferElab (rather than eager-evaluation)
  -- so Agda's termination check sees the result as a with-helper
  -- value rather than an arbitrary argument.
  -- Plan 0.52 (OCP-0008): route the infer-SUCCESS path through the NAMED
  -- embedOrSubsume (uniform, x-agnostic); only the infer-FAILURE path needs the
  -- per-builtin failure-aux dispatch (and bbc-other's lookupPoly fallback).
  -- D136: a bare `RVar` is an ORDINARY VARIABLE and nothing else. The
  -- generator dispatch moved to the `RResolved` clauses below, where the
  -- resolver's decision is already recorded in the name.
  checkElab-wf ctx ac (Raw.RVar x) T with inferElab ctx (Raw.RVar x)
  ... | rInfV@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RVar x) T rInfV
  ... | rInfV@(failure _) = checkElabV-RVar-bbc-other-aux ctx x T rInfV

  -- D136: the point-free generator leaves, routed through the `GenView` so the
  -- clause stays SINGLE and `checkElabV (RResolved cn)` keeps reducing for an
  -- abstract `cn`. No `classifyBareBuiltin` guess and no shadowing check — a
  -- user's `fst` never reaches a generator branch, because the resolver never
  -- gave it this name.
  checkElab-wf ctx ac (Raw.RResolved cn) T =
    checkElabV-RResolved-dispatch ctx cn T (classifyGen cn)
      (inferElab ctx (Raw.RResolved cn))

  -- Plan 0.36 Phase 2a follow-up: pair literal `(a , b)` at a product
  -- type — check components bidirectionally so check-only constructs
  -- (notably `In`) work in pair slots (`In (inr (x , tail))`). Falls to
  -- the generic clause below for non-product target types.
  checkElab-wf ctx ac (Raw.RPair a b) T = checkElabV-RPair-aux ctx a b T (classifyRPairTarget T)

  -- Plan 0.41 / D018 leaf: an integer literal at a pure-arrow position is its
  -- constant morphism (global element `const n ∘ terminal`, via `intLit`),
  -- the `g-int` leaf of `⊢ᵍ` bridged by `t-value-lift`; otherwise the generic
  -- infer-and-match. Routed through ONE scrutinee (`isRIntVliftTarget? T`) so
  -- the two outcomes don't overlap (no stuck `checkElabV (RInt n) T` for
  -- variable `T`). Behaviour is unchanged; the dispatch is now analysable.
  checkElab-wf ctx ac (Raw.RInt n) T = checkElabV-RInt-aux ctx n T
  checkElab-wf ctx ac (Raw.RFloat i f l) T =
    checkElabV-RFloat-aux ctx i f l T
  -- PLAN 0.73 F3: `- <literal>` gets the same value-lift the bare literal
  -- does. Before this it fell through to the generic clause below, which
  -- infers `Int`/`Float` and then mismatches against the ARROW the position
  -- wants — which is why `compose emit@E (-5)` did not compile.
  checkElab-wf ctx ac (Raw.RNeg e) T =
    checkElabV-neg-dispatch ctx e T (negOperandView e)

  -- Generic infer-and-match fallback — covers RInt, RUnit,
  -- RPair, RBinOp, RNeg, RLet, RDestruct, RAnnot, RQualified, RResolved.
  -- NB: the `with inferElabV ctx e` here is LOAD-BEARING for termination — the
  -- mutual `checkElab`↔`inferElab` same-size call (`checkElab e → inferElab e`)
  -- is accepted by the foetus checker only as a `with`-scrutinee; extracting it
  -- to an explicit-arg aux breaks termination. NOT every `with` is removable.
  {-# CATCHALL #-}
  checkElab-wf ctx ac e T = embedOrSubsume ctx e T (inferElab ctx e)


  -- Acc-free wrapper (Plan 0.58 E1-full): re-derive a fresh well-founded Acc.
  -- Sound per POC-B — the poly-resolution recursion uses the RECEIVED Acc's `rec`;
  -- non-poly recursion (through this wrapper) resets to fresh, which foetus accepts.
  checkElab ctx e T = checkElab-wf ctx (<-wellFounded (length (NamedCtx.polys ctx))) e T

  ----------------------------------------------------------------------
  -- `inferElabV-RApp-other` body — verified counterpart of
  -- `inferElab-RApp-other`. Pattern-matches on `inferElabV ctx f`'s
  -- type to determine whether `f` is a pure-arrow (use `wt-app`),
  -- effect-arrow (use `wt-effApp`), or non-function (failure). The
  -- `notPoly : classifyAppHead f ≡ nothing` premise is captured via
  -- `with classifyAppHead f in eqAH` — the `nothing` branch carries
  -- it; the `just _` branch is unreachable because callers only
  -- invoke this helper when the view classifies `f` as `ahv-other`.
  ----------------------------------------------------------------------
  inferElabV-RApp-other ctx f x =
    inferElabV-RApp-other-aux ctx f x _ refl


  -- `-5` is `neg (int 5)`, as the Spec's realization builds it (plan 0.122
  -- §5.6: the checker's term IS the realization of the Spec's derivation). The build
  -- gate reads the SOURCE's literals (`admissibleM?`, `negLits`), so
  -- `-2147483648` still fits x86-32; the wrapped `neg` of the wrapped `int`
  -- is the same word (`Once.Word.Width.⊝-fromℤ`). Depth `suc 1`, as the
  -- generic `RNeg` clause gives.
  -- The decision is an ARGUMENT, not a `with` and not a pattern match on `e`,
  -- so `inferElabV ctx (RNeg e)` still unfolds for an ABSTRACT `e`.
  -- That is the difference between this and the first attempt: matching `e`
  -- here would have forced every downstream proof to enumerate all sixteen
  -- `Syn.Expr` heads just to make the dispatch reduce. Downstream now does
  -- `with negOperandView e` and handles three cases. Same convention as
  -- `cfm-build-gated` taking its `Dec`.
  inferElabV-neg-dispatch ctx e = inferElabV-neg-aux ctx e (negOperandView e)

  inferElabV-neg-aux ctx .(Raw.RInt n) (nov-int n) =
    success Int _ (Surface.neg (Surface.int n)) 2 0
  -- PLAN 0.73 F3: `-3.14` is the literal whose payload is `negate (decimalOf
  -- i f l)`. Not a runtime negation of `3.14` — there is no float `neg` to
  -- emit (`MArithIR` is Int-only, F4), which is why the fold is the only
  -- lowering rather than the better of two. Both this and `Once.Denotation.
  -- Meaning`'s `⟦ wt-neg-float ⟧ᵢ` name the SAME `negate ∘ decimalOf`, so
  -- agreement is `refl`-shaped and cannot falsify `round` — the pins in
  -- `Once.Spec.Float.Decimal` against externally computed patterns are the check
  -- that means something (D117).
  --
  -- Depth `1` and the untouched fresh counter: one constructor deeper than
  -- the bare literal, no name allocated.
  inferElabV-neg-aux ctx .(Raw.RFloat i f l) (nov-float i f l) =
    success Float _ (Surface.float (Decimal.negate (decimalOf i f l))) 1
            0
  inferElabV-neg-aux ctx e (nov-other .e) = inferElabV-RNeg-aux ctx e (inferElab ctx e)

  checkElabV-neg-dispatch ctx .(Raw.RInt n) T (nov-int n) =
    checkElabV-neg-int-aux ctx n T
  checkElabV-neg-dispatch ctx .(Raw.RFloat i f l) T (nov-float i f l) =
    checkElabV-neg-float-aux ctx i f l T
  -- NOT a literal: the old generic clause verbatim, `embedOrSubsume` included,
  -- so the pure→eff subsumption (`t-subsume`, plan 0.52 M1) is not lost.
  checkElabV-neg-dispatch ctx e T (nov-other .e) =
    embedOrSubsume ctx (Raw.RNeg e) T
                   (inferElabV-RNeg-aux ctx e (inferElab ctx e))


  inferElabV-RLet-aux ctx x e₁ e₂ (failure err) = failure err
  inferElabV-RLet-aux ctx x e₁ e₂ (success A Ψ₁ e₁E d₁ f₁) =
    inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ (inferElab (extendNamedCtx ctx x A) e₂)

  -- RDestruct bodies (de-withed). `-aux` dispatches the scrutinee type;
  -- non-sum scrutinees fail; a sum `A + B` feeds `-auxL` with the left branch
  -- inferred in `ctx,xL:A`. `-auxL` feeds `-auxR` with the right branch in
  -- `ctx,xR:B`. `-auxR` matches branch types (`C₁ ≟T C₂`) and emits `wt-case`.
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (failure err)            = failure err
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Unit   _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Void   _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Int    _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Float  _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (var iᵣ) _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (_ Once.Spec.Type.* _) _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (_ Once.Spec.Type.⇒[ _ ] _) _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (Once.Spec.Type.μ _) _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (Once.Spec.Type.ν _ _) _ _ _ _) = failure CaseScrutineeNotSum
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (A Once.Spec.Type.+ B) Ψs scrutE ds fs) =
    inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs (inferElab (extendNamedCtx ctx xL A) eL)
  inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs (failure err) = failure err
  inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs (success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL) =
    inferElabV-RDestruct-auxR ctx scrut xL eL xR eR A B scrutE ds fs eLE dL fL (inferElab (extendNamedCtx ctx xR B) eR)


  inferElabV-RApp-other-aux ctx f x (just _) _ =
    failure (BuiltinTypeMismatch "unreachable: ahv-other ⇒ classifyAppHead nothing")
  inferElabV-RApp-other-aux ctx f x nothing eqAH with inferElab ctx f
  -- D230: the head does not synthesize — the spine. The argument synthesizes,
  -- and the head, GIVEN that input, determines the result.
  ... | failure err = inferSpine ctx f x eqAH (inferElab ctx x)
  ... | success Unit       _ _ _ _ = failure (NotFunction {0} Unit)
  ... | success Void       _ _ _ _ = failure (NotFunction {0} Void)
  ... | success Int        _ _ _ _ = failure (NotFunction {0} Int)
  ... | success Float      _ _ _ _ = failure (NotFunction {0} Float)
  ... | success (var iᵣ)     _ _ _ _ = failure (NotFunction (var iᵣ))
  ... | success (A Once.Spec.Type.* B) _ _ _ _ = failure (NotFunction (A Once.Spec.Type.* B))
  ... | success (A Once.Spec.Type.+ B) _ _ _ _ = failure (NotFunction (A Once.Spec.Type.+ B))
  ... | success (Once.Spec.Type.μ F) _ _ _ _ = failure (NotFunction (Once.Spec.Type.μ F))
  ... | success (Once.Spec.Type.ν F π) _ _ _ _ = failure (NotFunction (Once.Spec.Type.ν F π))
  ... | success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q Once.Spec.Grade.pure ] B) Ψ₁ fE df ff with checkElab ctx x A
  ...   | failure err = failure err
  ...   | success Ψ₂ xE dx fx =
          success B _ (Surface.app fE xE) (df ⊔ dx) fx
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.eff ] B) Ψ₁ fE df ff with checkElab ctx x A
  ...   | failure err = failure err
  ...   | success Ψ₂ xE dx fx =
          success (Unit Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.eff ] B) _ (Surface.effApp {g = Once.Spec.Grade.eg-eff} fE xE) (df ⊔ dx) fx
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] B) Ψ₁ fE df ff with checkElab ctx x A
  ...   | failure err = failure err
  ...   | success Ψ₂ xE dx fx =
          success (Unit Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] B) _ (Surface.effApp {g = Once.Spec.Grade.eg-act} fE xE) (df ⊔ dx) fx
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.eff ] B) _ _ _ _ = failure (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.eff ] B))
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.eff ] B) _ _ _ _ = failure (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.eff ] B))
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.act ] B) _ _ _ _ = failure (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.act ] B))
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.act ] B) _ _ _ _ = failure (NotFunction (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.act ] B))

  -- ahv-id : argument can have any type, result has the same type.
  inferElabV-RApp-dispatch ctx f arg ahv-id _ with inferElab ctx arg
  ... | failure err = failure err
  ... | success T Ψ argE d fr =
    success T _ (Surface.morph-app IR.id argE) (suc d) fr
  -- ahv-fst : argument must have product type.
  inferElabV-RApp-dispatch ctx f arg ahv-fst _ = inferFstOn ctx arg (inferElab ctx arg)
  -- ahv-snd : argument must have product type.
  inferElabV-RApp-dispatch ctx f arg ahv-snd _ = inferSndOn ctx arg (inferElab ctx arg)
  -- ahv-terminal : any-typed argument, Unit result.
  inferElabV-RApp-dispatch ctx f arg ahv-terminal _ with inferElab ctx arg
  ... | failure err = failure err
  ... | success T Ψ argE d fr =
    success Unit _ (Surface.morph-app IR.terminal argE) (suc d) fr
  -- ahv-apply : argument must be `(A ⇒[Many] B) * A` (or `Void`).
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ = inferApplyOn ctx arg (inferElab ctx arg)
  -- ahv-inl / ahv-inr / ahv-initial : check-only builtins, infer fails.
  inferElabV-RApp-dispatch ctx f arg ahv-inl     _ = failure InlInInferMode
  inferElabV-RApp-dispatch ctx f arg ahv-inr     _ = failure InrInInferMode
  inferElabV-RApp-dispatch ctx f arg ahv-initial _ = failure InitialInInferMode
  -- ahv-pair-applied / ahv-compose-applied / ahv-curry : check-only.
  inferElabV-RApp-dispatch ctx f arg ahv-pair-applied    _ = failure (BuiltinTypeMismatch "pair")
  inferElabV-RApp-dispatch ctx f arg ahv-compose-applied _ = failure (BuiltinTypeMismatch "compose")
  inferElabV-RApp-dispatch ctx f arg ahv-case-applied    _ = failure (BuiltinTypeMismatch "case")
  inferElabV-RApp-dispatch ctx f arg ahv-In              _ = failure (BuiltinTypeMismatch "In")
  inferElabV-RApp-dispatch ctx f arg ahv-cata            _ = failure (BuiltinTypeMismatch "cata")
  inferElabV-RApp-dispatch ctx f arg ahv-ana             _ = failure (BuiltinTypeMismatch "ana")
  inferElabV-RApp-dispatch ctx f arg ahv-Out             _ = inferOut ctx arg
  inferElabV-RApp-dispatch ctx f arg ahv-curry           _ = failure (BuiltinTypeMismatch "curry")
  -- ahv-other : generic application via `inferElabV-RApp-other`.
  inferElabV-RApp-dispatch ctx f arg ahv-other _ = inferElabV-RApp-other ctx f arg

  -- checkElabV's RApp dispatch — mirror of inferElabV-RApp-dispatch.
  -- Plan 0.52 (OCP-0008): infer-then-check builtin-app heads route through the
  -- NAMED embedOrSubsume (was an inline with-tree). `with`-bind the inferElabV
  -- result (so the termination checker sees the recursive call) and hand it to
  -- embedOrSubsume; on infer failure, propagate failure.
  checkElabV-RApp-dispatch ctx f arg T ahv-id _       with inferElab ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err) = failure err
  checkElabV-RApp-dispatch ctx f arg T ahv-fst _      with inferElab ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err) = failure err
  checkElabV-RApp-dispatch ctx f arg T ahv-snd _      with inferElab ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err) = failure err
  -- D194: `Out v` infers, so its CHECK goes through the shared
  -- infer-then-check, exactly as `terminal`/`apply` do. That is what gives
  -- `Out v` at an eff position for free (`t-subsume`).
  checkElabV-RApp-dispatch ctx f arg T ahv-Out _ with inferElab ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err) = failure err
  checkElabV-RApp-dispatch ctx f arg T ahv-terminal _ with inferElab ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err) = failure err
  -- ahv-inl: T must be sum type A+B; check arg at A.
  -- D127: `inl arg` / `inr arg` at an ARROW type are no longer lifts; the
  -- value-type dispatch below is the only route.
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ with T
  ... | (A Once.Spec.Type.+ B) with checkElab ctx arg A
  ...   | failure err = failure err
  ...   | success Ψ argE d fr =
          success _ (Surface.morph-app (IR.inl) argE) (suc d) fr
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Unit = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Void = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Int = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Float = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (var iᵣ) = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (_ Once.Spec.Type.* _) = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (_ Once.Spec.Type.⇒[ _ ] _) = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (μ _) = failure InlNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (ν _ _) = failure InlNeedsSumType
  -- ahv-inr: T must be sum type A+B; check arg at B.
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ with T
  ... | (A Once.Spec.Type.+ B) with checkElab ctx arg B
  ...   | failure err = failure err
  ...   | success Ψ argE d fr =
          success _ (Surface.morph-app (IR.inr) argE) (suc d) fr
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Unit = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Void = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Int = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Float = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (var iᵣ) = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (_ Once.Spec.Type.* _) = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (_ Once.Spec.Type.⇒[ _ ] _) = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (μ _) = failure InrNeedsSumType
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (ν _ _) = failure InrNeedsSumType
  -- ahv-initial: arg must be Void; result has any expected T.
  checkElabV-RApp-dispatch ctx f arg T ahv-initial _ with checkElab ctx arg Once.Spec.Type.Void
  ... | failure err = failure err
  ... | success Ψ argE d fr =
        success _ (Surface.morph-app (IR.initial) argE) (suc d) fr
  -- Helper-applied branches.
  checkElabV-RApp-dispatch ctx f arg T (ahv-pair-applied {f'}) _ = checkPairOn ctx f' arg T (pairTarget T)
  checkElabV-RApp-dispatch ctx f arg T (ahv-compose-applied {f'}) _ = checkComposeOn ctx f' arg T (arrowTarget T)
  checkElabV-RApp-dispatch ctx f arg T (ahv-case-applied {f'}) _ = checkCaseOn ctx f' arg T (caseTarget T)
  checkElabV-RApp-dispatch ctx f arg T ahv-In _ = checkIn ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-cata _ = checkCata ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-ana _ = checkAna ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-curry _ = checkCurry ctx arg T
  -- Plan 0.52 (OCP-0008): `apply p` infers (wt-apply-app-infer), so route its
  -- CHECK through the named embedOrSubsume — this ADDS the subsume case (apply at
  -- an eff arrow) that the old `checkApply` (exact T ≟ codomain) rejected.
  checkElabV-RApp-dispatch ctx f arg T ahv-apply _ with inferElab ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err) = failure err
  -- ahv-other: infer-then-check via the NAMED `embedOrSubsume` (OCP-0008: route
  -- through the named combinator, not an inline with-tree, so completeness can
  -- reason through it). An application that does not synthesize does not check.
  checkElabV-RApp-dispatch ctx f arg T ahv-other _ with inferElab ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  checkElabV-RApp-dispatch ctx f arg T ahv-other _ | failure errInfer = failure errInfer

  inferSpine ctx f x eqAH (failure err) = failure err
  inferSpine ctx f x eqAH (success X Ψx xE dx frx) with elabGiven ctx f X Once.Spec.Grade.pure
  ... | failure err = failure err
  ... | success T Ψf fE df frf =
          success T _ (Surface.app fE xE) (suc (df ⊔ dx)) frf


  checkElabV-RInt-aux ctx n T with inferElab ctx (Raw.RInt n)
  ... | r = embedOrSubsume ctx (Raw.RInt n) T r

  -- RPair: product → bidirectional component check (checkPairLit);
  -- pure-arrow-to-product → value-lift via checkG (inspectCheckG); else the
  -- generic infer+match. The latter two are the old clauses verbatim.
  checkElabV-RPair-aux ctx a b _ (rpt-prod A B) = checkPairLit ctx a b A B
  -- D127: a pair literal at an ARROW type is no longer a lift.
  checkElabV-RPair-aux ctx a b _ (rpt-vlift X A B π) =
    failure (TypeMismatch (X Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] (A Once.Spec.Type.* B))
                          (A Once.Spec.Type.* B))
  checkElabV-RPair-aux ctx a b _ (rpt-other T) with inferElab ctx (Raw.RPair a b)
  ... | r = embedOrSubsume ctx (Raw.RPair a b) T r



checkApply : ∀ {m} → (ctx : NamedCtx m) → (arg : Syn.Expr) → (T : Ty m)
           → CheckElabResult (NamedCtx.debruijn ctx) T
-- Plan 0.6 Phase C.7 POC-3: `apply p` check-mode.
-- Check mode falls through to infer (apply's infer mode succeeds
-- when p has pair-of-function type). Matches result against T.
checkApply ctx arg T with inferElab ctx arg
... | failure err = failure err
... | success ((A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.pure ] B) Once.Spec.Type.* A') Ψ argE d fr with A ≟T A' | T ≟T B
...   | yes refl | yes refl =
        success _ (Surface.morph-app IR.apply argE) (suc d) fr
...   | yes refl | no _ = failure (TypeMismatch T B)
...   | no _ | _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success Unit _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success Void _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success Int _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success Float _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (var iᵣ) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (_ Once.Spec.Type.+ _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (_ Once.Spec.Type.⇒[ _ ] _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (Unit Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (Void Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (Int Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (Float Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((var iᵣ) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((_ Once.Spec.Type.* _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((_ Once.Spec.Type.+ _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.pure ] _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.pure ] _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
{-# CATCHALL #-}
checkApply ctx arg T | success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind _ Once.Spec.Grade.eff ] _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero Once.Spec.Grade.act ] _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One Once.Spec.Grade.act ] _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((_ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((Once.Spec.Type.μ _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success ((Once.Spec.Type.ν _ _) Once.Spec.Type.* _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (Once.Spec.Type.μ _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")
checkApply ctx arg T | success (Once.Spec.Type.ν _ _) _ _ _ _ = failure (BuiltinTypeMismatch "apply")

-- Plan 0.4 T0 Option A: hoist the `ahv-other` (generic application)
-- branch of `inferElab RApp` into its own top-level mutual member.
-- The body is structurally identical to the previous in-place
-- clause; the win is that `inferElab ctx (RApp f x) | ahv-other`
-- now reduces to a *named* function call rather than to the
-- `inferElab` case tree's anonymous with-helper. Soundness for the
-- `ahv-other` view branch (`spec-gap-RApp-ahv-other`) can pattern-
-- match through this helper transparently.
inferElab-RApp-other : ∀ {m} → (ctx : NamedCtx m) (f x : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
-- Body for the hoisted `ahv-other` (generic application) branch.
inferElab-RApp-other ctx f x with asFun (inferElab ctx f)
... | notFun err = failure err
... | isFun A q B Ψ₁ fE df ff with checkElab ctx x A
...   | failure err = failure err
...   | success Ψ₂ xE dx fx = success B _ (Surface.app fE xE) (df ⊔ dx) fx
inferElab-RApp-other ctx f x | isEff π g A B Ψ₁ fE df ff with checkElab ctx x A
...   | failure err = failure err
...   | success Ψ₂ xE dx fx = success (Unit ⇒[ mk-kind Many π ] B) _ (Surface.effApp {g = g} fE xE) (df ⊔ dx) fx
