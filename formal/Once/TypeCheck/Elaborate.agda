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

open import Once.Type.Core using (wk₀)
open import Once.Spec.Type using (μ; ν; ⟦_⟧F)
open import Once.Spec.Type using (var; Ty; Base)
open import Data.String using (String)
open import Data.String.Properties as StrProp using ()
open import Data.Nat using (ℕ; suc; _⊔_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc)
open import Data.Fin using (suc)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_; length)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Spec.Type using (Type; Unit; Void; _⇒[_]_; Int; Float)
open import Once.Spec.Surface.Type using (PolyType; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PTVar)
open import Once.Type.Poly
open import Once.Type
-- Plan 0.52 M2: IR re-exports the ungraded IRTy, whose Unit/K/μ-type/… clash
-- with Once.Type's (opened above). Hide the IRTy object/functor constructors
-- from the unqualified open (they stay available as `IR.*`); the surface-type
-- names resolve unambiguously to `Once.Type`.
open import Once.IR as IR
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Name using (CanonicalName; canonical; own)
import Once.Spec.Surface.Generators as G
open import Once.Generators using (fromDomain?; fromCodomain?)
open import Once.TypeCheck.Table using (mapAt?; mapFrom?; mapTo?; MuV; muV; mu-at; mu-other; SumV; sumV; sum-at; sum-other)
open import Once.Name using (showCanonical; WordName; wordNameB)
import Once.Spec.Surface.Syntax as Syn
open import Once.Spec.Surface.Operator using (BinOp)
open import Once.Spec.Surface.Syntax as Raw using ()
open import Once.Spec.Float.Value using (Sign)
open import Once.Spec.Theory using (NumTy; ⌜_⌝ⁿ; Has; Neg; symCod; ‵neg)
  renaming (int to nint)
open import Once.TypeCheck.NumTable
  using (NumView; is-num; not-num; numView; _≟ⁿ_; has?; binDom;
         pairDom; binary?)
open import Once.Surface.Numeric using (numBin)
open import Once.Surface.Map using (Map; mp-toFloat)
open import Once.Spec.Surface.Operator using (binSym; BinSym)
open BinSym using (theory; shape)
open import Once.Spec.Float.Decimal using (signedDecimal)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Error using (TypeError; ComposeMiddleUndetermined;
  OperatorUndefined; MixedOperands; opText;
  LambdaInInferMode; LambdaRequiresFunctionType;
  InlInInferMode; InrInInferMode; InitialInInferMode; GeneratorInInferMode;
  InlNeedsSumType; InrNeedsSumType;
  FstNeedsPair; SndNeedsPair;
  CaseScrutineeNotSum; CaseBranchMismatch; TypeMismatch; NotFunction;
  UsageViolation; BuiltinTypeMismatch; NoInstance;
  BinOpLeftError; BinOpRightError;
  UnboundVariable; UnboundQualified; NonConcreteSigOpType)
open import Once.Context as Surface using ()
import Once.Spec.Context as Surface
open import Once.Spec.Context using () renaming (Ctx to SCtx)
open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)
open import Once.Spec.Context using () renaming (_∷_ to _∷ᵘ_)
open import Once.Surface.Elaborate as Elab using ()

open import Once.TypeCheck.Scope
open import Once.TypeCheck.Classify
open import Once.Spec.Type using (∅ₖ)
import Once.Spec.Type
open import Once.Type.Concrete using (IsConcrete; con-fun)
open import Once.Functor.Decide using (wfFun?; isConcrete?; isBaseType?)
open import Once.Spec.Sub using (_<:_; sub-arr)
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

-- View bundling `wellFormedF? F`'s outcome with its equation (mirrors
-- `inspectLookupLocal`) so proofs sidestep the `with … in` opacity.
data WellFormedFView {m} (Δ : Once.Spec.Type.KCtx m) (F : Once.Spec.Type.Fun m) : Set where
  wfv-yes : ∀ {wfF} → wfFun? Δ F ≡ just wfF → WellFormedFView Δ F
  wfv-no  : wfFun? Δ F ≡ nothing → WellFormedFView Δ F

inspectWellFormedF : ∀ {m} (Δ : Once.Spec.Type.KCtx m) (F : Once.Spec.Type.Fun m) → WellFormedFView Δ F
inspectWellFormedF Δ F with wfFun? Δ F in eq
... | just wfF = wfv-yes eq
... | nothing  = wfv-no eq


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
-- | The error for an operand of type `T` where a number of type `a` was
-- expected (`Unit` and `Void` stated at index 0, as before plan 0.150).
numErr : ∀ {m} → NumTy → Ty m → TypeError
numErr a Unit                       = TypeMismatch {0} ⌜ a ⌝ⁿ Unit
numErr a Void                       = TypeMismatch {0} ⌜ a ⌝ⁿ Void
numErr {m} a Int                    = TypeMismatch {m} ⌜ a ⌝ⁿ Int
numErr {m} a Float                  = TypeMismatch {m} ⌜ a ⌝ⁿ Float
numErr a (var i)                    = TypeMismatch ⌜ a ⌝ⁿ (var i)
numErr a (A Once.Spec.Type.* B)     = TypeMismatch ⌜ a ⌝ⁿ (A Once.Spec.Type.* B)
numErr a (A Once.Spec.Type.+ B)     = TypeMismatch ⌜ a ⌝ⁿ (A Once.Spec.Type.+ B)
numErr a (A ⇒[ k ] B)               = TypeMismatch ⌜ a ⌝ⁿ (A ⇒[ k ] B)
numErr a (μ F)                      = TypeMismatch ⌜ a ⌝ⁿ (μ F)
numErr a (ν F π)                    = TypeMismatch ⌜ a ⌝ⁿ (ν F π)

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
given-poly-k ctx x A B π π′ err {schema = schema} eL eI eP ¬g as inc g (no _) =
  failure (NoInstance x schema (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] B))
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
given-poly-π ctx x A π err {schema = schema} {sc = sc} eL eI eP ¬g as inc θ eθ (no _) =
  failure (NoInstance x schema (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] substPoly θ sc))
given-poly-π ctx x A π err {schema = schema} {sc = sc} {π′ = π′} eL eI eP ¬g as inc θ eθ (yes g) =
  given-poly-k ctx x A (substPoly θ sc) π π′ err eL eI eP ¬g as inc g
    (kindedInstance? (NamedCtx.kinds ctx) schema (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] substPoly θ sc))

given-poly-m : ∀ {m} (ctx : NamedCtx m) (x : String) (A : Ty m) (π : Once.Spec.Grade.Purity) (err : TypeError)
  {schema sd sc : PolyType} {π′ : Once.Spec.Grade.Purity} {body : Syn.Expr} {prefix : PolyCtx}
  → lookupImport (NamedCtx.sig ctx) x ≡ nothing → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (schema , body , prefix)
  → ¬ Ground schema → ArrowSchema schema sd sc π′ → CodVarsInDom sd sc
  → (mσ : Maybe (Subst m)) → instantiate sd A ≡ mσ → GivenElabResult (NamedCtx.debruijn ctx) A π
given-poly-m ctx x A π err {sd = sd} eL eI eP ¬g as inc nothing _ = failure (NoInstance x sd A)
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
checkElabV-RVar-poly-inst-aux ctx x T err {schema = schema} eL eI eP ¬g (no _) = failure (NoInstance x schema T)
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


-- Plan 0.139: the `g` route of `compose` failed with `err`. It determined a
-- middle when `g` synthesizes a type of its own; then `err` is the program's
-- error, otherwise the middle is still open.
determinedErr : ∀ {m} (ctx : NamedCtx m) → InferElabResult (NamedCtx.debruijn ctx) → TypeError → Maybe TypeError
determinedErr _ (success _ _ _ _ _) err = just err
determinedErr _ (failure _)         _   = nothing

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

------------------------------------------------------------------------
-- NUMERIC OPERATORS, over the Spec's table (plan 0.150 N10): an operand's
-- type is a number type or not (`numView`), the type has the operator's
-- theory or not (`has?`), and two number types that differ meet only under a
-- dotted operator, which widens the `Int` (`roundedView`, D125). One dispatch;
-- no case per operator or per type.
------------------------------------------------------------------------

-- `-e`: `s-neg`.
inferElabV-RNeg-has : ∀ {m} → (ctx : NamedCtx m) (a : NumTy) {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → SExpr (NamedCtx.debruijn ctx) Ψ ⌜ a ⌝ⁿ → (d fr : ℕ) → Dec (Has a Neg)
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RNeg-has ctx a eE d fr (yes h) = success ⌜ a ⌝ⁿ _ (Surface.num h ‵neg eE) (suc d) fr
inferElabV-RNeg-has ctx a eE d fr (no _)  = failure (OperatorUndefined "-" a)

inferElabV-RNeg-num : ∀ {m} → (ctx : NamedCtx m) {T : Ty m} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → SExpr (NamedCtx.debruijn ctx) Ψ T → (d fr : ℕ) → NumView T
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RNeg-num ctx eE d fr (is-num a)    = inferElabV-RNeg-has ctx a eE d fr (has? a Neg)
inferElabV-RNeg-num ctx {T} eE d fr not-num   = failure (numErr nint T)

inferElabV-RNeg-aux : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr)
  → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RNeg-aux ctx e (failure err)          = failure err
inferElabV-RNeg-aux ctx e (success T Ψ eE d fr)  = inferElabV-RNeg-num ctx eE d fr (numView T)

-- `e₁ op e₂` at one number type `a`: `s-binop`.
inferElabV-RBinOp-has : ∀ {m} → (ctx : NamedCtx m) (op : BinOp) (a : NumTy)
  {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
  → SExpr (NamedCtx.debruijn ctx) Ψ₁ ⌜ a ⌝ⁿ → SExpr (NamedCtx.debruijn ctx) Ψ₂ ⌜ a ⌝ⁿ → (d fr : ℕ)
  → Dec (Has a (theory (binSym op)))
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RBinOp-has ctx op a e₁E e₂E d fr (yes h) =
  success (symCod a (shape (binSym op))) _ (numBin op a h e₁E e₂E) d fr
inferElabV-RBinOp-has ctx op a e₁E e₂E d fr (no _) = failure (OperatorUndefined (opText op) a)

inferElabV-RBinOp-num : ∀ {m} → (ctx : NamedCtx m) (op : BinOp) (a₁ a₂ : NumTy)
  {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
  → SExpr (NamedCtx.debruijn ctx) Ψ₁ ⌜ a₁ ⌝ⁿ → SExpr (NamedCtx.debruijn ctx) Ψ₂ ⌜ a₂ ⌝ⁿ → (d fr : ℕ)
  → Dec (a₁ ≡ a₂)
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RBinOp-num ctx op a .a e₁E e₂E d fr (yes refl) = inferElabV-RBinOp-has ctx op a e₁E e₂E d fr (has? a (theory (binSym op)))
inferElabV-RBinOp-num ctx op a₁ a₂ e₁E e₂E d fr (no _)    = failure (MixedOperands (opText op))

-- The right operand.
inferElabV-RBinOp-R : ∀ {m} → (ctx : NamedCtx m) (op : BinOp) (a₁ : NumTy) {T₂ : Ty m}
  {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
  → SExpr (NamedCtx.debruijn ctx) Ψ₁ ⌜ a₁ ⌝ⁿ → SExpr (NamedCtx.debruijn ctx) Ψ₂ T₂ → (d fr : ℕ)
  → NumView T₂
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RBinOp-R ctx op a₁ e₁E e₂E d fr (is-num a₂) = inferElabV-RBinOp-num ctx op a₁ a₂ e₁E e₂E d fr (a₁ ≟ⁿ a₂)
inferElabV-RBinOp-R ctx op a₁ {T₂} e₁E e₂E d fr not-num = failure (BinOpRightError (numErr a₁ T₂))

-- The left operand, then the right's result.
inferElabV-RBinOp-L : ∀ {m} → (ctx : NamedCtx m) (op : BinOp) {T₁ : Ty m}
  {Ψ₁ : Surface.Usage (NamedCtx.size ctx)}
  → SExpr (NamedCtx.debruijn ctx) Ψ₁ T₁ → (d₁ : ℕ) → NumView T₁
  → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RBinOp-L ctx op {T₁} e₁E d₁ not-num r₂ = failure (BinOpLeftError (numErr nint T₁))
inferElabV-RBinOp-L ctx op e₁E d₁ (is-num a₁) (failure err) = failure (BinOpRightError err)
inferElabV-RBinOp-L ctx op e₁E d₁ (is-num a₁) (success T₂ Ψ₂ e₂E d₂ f₂) =
  inferElabV-RBinOp-R ctx op a₁ e₁E e₂E (d₁ ⊔ d₂) f₂ (numView T₂)

inferElabV-RBinOp-aux : ∀ {m} → (ctx : NamedCtx m) (op : BinOp) (e₁ e₂ : Syn.Expr)
  → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RBinOp-aux ctx op e₁ e₂ (failure err) _ = failure (BinOpLeftError err)
inferElabV-RBinOp-aux ctx op e₁ e₂ (success T₁ Ψ₁ e₁E d₁ f₁) r₂ = inferElabV-RBinOp-L ctx op e₁E d₁ (numView T₁) r₂

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

inferElabV-RResolved-arrow-aux : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → ∀ {A B : Type} {π : Once.Spec.Grade.Purity}
  → lookupImport (NamedCtx.sig ctx) (showCanonical cn)
      ≡ just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)
  → (mbA : Maybe (Base ∅ₖ A)) → isBaseType? A ≡ mbA
  → (mcB : Maybe (Base ∅ₖ B)) → isBaseType? B ≡ mcB
  → InferElabResult (NamedCtx.debruijn ctx)
-- Concreteness-driven arrow value emission (de-withed for Completeness).
inferElabV-RResolved-arrow-aux ctx cn {A} {B} {π} eq (just bA) _ (just cB) _ =
  inferElabV-RResolved-word ctx cn (λ wn →
    success (wk₀ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) _
      (Surface.sigOp cn (con-fun bA cB))
      0 0) (wordNameB cn) refl
inferElabV-RResolved-arrow-aux ctx cn {A} {B} {π} eq nothing _ _ _ =
  failure (NonConcreteSigOpType (showCanonical cn)
            (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B))
inferElabV-RResolved-arrow-aux ctx cn {A} {B} {π} eq (just _) _ nothing _ =
  failure (NonConcreteSigOpType (showCanonical cn)
            (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B))

inferElabV-RResolved-value-aux : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → ∀ (ty : Type)
  → lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ just ty
  → (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RResolved-value-aux ctx cn ty eq (just conc) _ =
  inferElabV-RResolved-word ctx cn (λ wn → success (wk₀ ty) _ (Surface.sigOp cn conc) 0 0)
    (wordNameB cn) refl
inferElabV-RResolved-value-aux ctx cn ty eq nothing _ =
  failure (NonConcreteSigOpType (showCanonical cn) ty)

-- D248/D274: not in Σ — an OWN reference (`own x`) may name a monomorphic
-- definition, and is then a CALL of it (D246).
inferElabV-RResolved-def : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ nothing
                         → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RResolved-own-aux : ∀ {m} (ctx : NamedCtx m) (x : String) → lookupImport (NamedCtx.sig ctx) x ≡ nothing → (lhs : Maybe Type)
  → lookupImport (NamedCtx.imports ctx) x ≡ lhs
  → InferElabResult (NamedCtx.debruijn ctx)

-- Plan 0.50: resolved-ref lookup, keyed by the canonical dotted path.
inferElabV-RResolved-aux : ∀ {m} (ctx : NamedCtx m) (cn : CanonicalName) → (lhs : Maybe Type)
  → lookupImport (NamedCtx.sig ctx) (showCanonical cn) ≡ lhs
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RResolved-aux ctx cn
  (just (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B)) eq =
  inferElabV-RResolved-arrow-aux ctx cn eq (isBaseType? A) refl (isBaseType? B) refl
{-# CATCHALL #-}
inferElabV-RResolved-aux ctx cn (just ty) eq =
  inferElabV-RResolved-value-aux ctx cn ty eq (isConcrete? ty) refl
inferElabV-RResolved-aux ctx cn nothing eq = inferElabV-RResolved-def ctx cn eq

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

checkElabV-RVar-bbc-other-aux : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m)
  → InferElabResult (NamedCtx.debruijn ctx)
  → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabV-RVar-bbc-other-aux ctx x T r = embedOrSubsume ctx (Raw.RVar x) T r


-- A float literal: its signed decimal (`s-float`; `-0.0` is the negative
-- zero). The target rounds it; representability is no way to fail.
-- Plan 0.150 N4: the sign is the literal's, built by the grammar.
inferElabV-RFloat-aux : ∀ {m} (ctx : NamedCtx m) (sg : Sign) (i f l : ℕ)
  → InferElabResult (NamedCtx.debruijn ctx)
inferElabV-RFloat-aux ctx sg i f l = success Float _ (Surface.float (signedDecimal sg i f l)) 0 0


------------------------------------------------------------------------
-- The generators (plan 0.151): one rule per mode over the table
-- (`Spec.Surface.Generators`), read by `TypeCheck.Table`.
------------------------------------------------------------------------

-- An arrow used `Many` times.
_⇒ω⟨_⟩_ : ∀ {m} → Ty m → Once.Spec.Grade.Purity → Ty m → Ty m
A ⇒ω⟨ π ⟩ B = A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B
infixr 30 _⇒ω⟨_⟩_

-- The error a generator reports where it has no rule.
genErr : G.Gen → TypeError
genErr G.inl     = InlInInferMode
genErr G.inr     = InrInInferMode
genErr G.initial = InitialInInferMode
{-# CATCHALL #-}
genErr g         = GeneratorInInferMode (G.word g)

-- …and a structure map applied to an argument of no instance's domain.
spineErr : G.Gen → TypeError
spineErr G.fst     = FstNeedsPair
spineErr G.snd     = SndNeedsPair
spineErr G.inl     = InlInInferMode
spineErr G.inr     = InrInInferMode
spineErr G.initial = InitialInInferMode
{-# CATCHALL #-}
spineErr g         = BuiltinTypeMismatch (G.word g)

-- D407: a structure map at a type it has no instance at is `NoInstance`,
-- naming its type as a schema (only the message reads it). `mapSchema` is the
-- map's arrow (checked at a type), `mapDomSchema` its domain (given one).
-- `F` names the functor in `In`/`Out`'s schemas; a schema has no functor
-- variable, so it is written as one.
private
  _⇒ω_ : PolyType → PolyType → PolyType
  A ⇒ω B = A P⇒[ Once.Spec.Grade.Many ] B
  infixr 30 _⇒ω_

mapDomSchema : G.Gen → PolyType
mapDomSchema G.fst      = PTVar "a" P* PTVar "b"
mapDomSchema G.snd      = PTVar "a" P* PTVar "b"
mapDomSchema G.initial  = PVoid
mapDomSchema G.inr      = PTVar "b"
mapDomSchema G.apply    = (PTVar "a" ⇒ω PTVar "b") P* PTVar "a"
mapDomSchema G.In       = PTVar "F (Mu F)"
mapDomSchema G.Out      = PTVar "Nu F"
{-# CATCHALL #-}
mapDomSchema _          = PTVar "a"

mapSchema : G.Gen → PolyType
mapSchema G.fst      = mapDomSchema G.fst ⇒ω PTVar "a"
mapSchema G.snd      = mapDomSchema G.snd ⇒ω PTVar "b"
mapSchema G.terminal = PTVar "a" ⇒ω PUnit
mapSchema G.initial  = PVoid ⇒ω PTVar "a"
mapSchema G.inl      = PTVar "a" ⇒ω (PTVar "a" P+ PTVar "b")
mapSchema G.inr      = PTVar "b" ⇒ω (PTVar "a" P+ PTVar "b")
mapSchema G.apply    = mapDomSchema G.apply ⇒ω PTVar "b"
mapSchema G.In       = PTVar "F (Mu F)" ⇒ω PTVar "Mu F"
mapSchema G.Out      = PTVar "Nu F" ⇒ω PTVar "F (Nu F)"
{-# CATCHALL #-}
mapSchema _          = PTVar "a" ⇒ω PTVar "a"

-- `s-const`: a constant synthesizes the type the table gives it; nothing else
-- of the table synthesizes.
inferConst : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) → G.IsConstant (G.kind g) → InferElabResult (NamedCtx.debruijn ctx)
inferConst ctx G.unit    _ = success Unit _ Surface.unit 0 0
inferConst ctx G.toFloat _ = success (Int ⇒ω⟨ Once.Spec.Grade.pure ⟩ Float) _ (Surface.lift-morphism mp-toFloat) 0 0
inferConst ctx G.id ()
inferConst ctx G.compose ()
inferConst ctx G.fst ()
inferConst ctx G.snd ()
inferConst ctx G.terminal ()
inferConst ctx G.pair ()
inferConst ctx G.inl ()
inferConst ctx G.inr ()
inferConst ctx G.initial ()
inferConst ctx G.case ()
inferConst ctx G.apply ()
inferConst ctx G.curry ()
inferConst ctx G.In ()
inferConst ctx G.cata ()
inferConst ctx G.Out ()
inferConst ctx G.ana ()

inferGen : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) → GenKindView g → InferElabResult (NamedCtx.debruijn ctx)
inferGen ctx g (gk-const c) = inferConst ctx g c
inferGen ctx g (gk-map _)   = failure (genErr g)
inferGen ctx g (gk-comb₁ _) = failure (genErr g)
inferGen ctx g (gk-comb₂ _) = failure (genErr g)

-- `d-map`: a structure map out of a given domain, at its least codomain.
givenMap : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (A : Ty m) (π : Once.Spec.Grade.Purity)
         → Maybe (Σ[ B ∈ Ty m ] Map A B) → GivenElabResult (NamedCtx.debruijn ctx) A π
givenMap ctx g A π (just (B , mI)) = success B Surface.zeroUsage (Surface.lift-morphism mI) 0 0
givenMap ctx g A π nothing         = failure (NoInstance (G.word g) (mapDomSchema g) A)

-- `c-map`: a structure map at a given arrow.
checkMapAt : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) {T : Ty m} → ArrowTarget T → CheckElabResult (NamedCtx.debruijn ctx) T
checkMapAt-go : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (A : Ty m) (π : Once.Spec.Grade.Purity) (B : Ty m)
              → Maybe (Map A B) → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ π ⟩ B)
checkMapAt-go ctx g A π B (just mI) = success Surface.zeroUsage (Surface.lift-morphism mI) 0 0
checkMapAt-go ctx g A π B nothing   = failure (NoInstance (G.word g) (mapSchema g) (A ⇒ω⟨ π ⟩ B))
checkMapAt ctx g (arrow-at A π B) = checkMapAt-go ctx g A π B (mapAt? (NamedCtx.kinds ctx) g A B)
checkMapAt ctx g {T} arrow-other  = failure (NoInstance (G.word g) (mapSchema g) T)

-- The spine at a structure map whose domain fixes it: the argument's type is
-- the map's domain, and the map is applied (`s-app-spine` over `d-map`).
inferMapSpine : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
inferMapSpine-go : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) {X : Ty m} {Ψ : Surface.Usage (NamedCtx.size ctx)}
                 → SExpr (NamedCtx.debruijn ctx) Ψ X → (d fr : ℕ) → Maybe (Σ[ B ∈ Ty m ] Map X B)
                 → InferElabResult (NamedCtx.debruijn ctx)
inferMapSpine-go ctx g xE d fr (just (B , mI)) = success B _ (Surface.morph-app mI xE) (suc d) fr
inferMapSpine-go ctx g xE d fr nothing         = failure (spineErr g)
inferMapSpine ctx g (failure err)           = failure err
inferMapSpine ctx g (success X Ψ xE d fr)   = inferMapSpine-go ctx g xE d fr (mapFrom? (NamedCtx.kinds ctx) g X)

-- `d-cata`: the fold out of `μ F`, at the algebra's codomain; the algebra's
-- domain may lie above the layer and its grade below the fold's.
givenCata : ∀ {m} (ctx : NamedCtx m) (A : Ty m) (π : Once.Spec.Grade.Purity) → InferElabResult (NamedCtx.debruijn ctx)
          → GivenElabResult (NamedCtx.debruijn ctx) A π
givenCata-mu : ∀ {m} (ctx : NamedCtx m) {A : Ty m} (π : Once.Spec.Grade.Purity) → MuV A → InferElabResult (NamedCtx.debruijn ctx)
             → GivenElabResult (NamedCtx.debruijn ctx) A π
givenCata-wf : ∀ {m} (ctx : NamedCtx m) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity)
             → Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F) → InferElabResult (NamedCtx.debruijn ctx)
             → GivenElabResult (NamedCtx.debruijn ctx) (Once.Spec.Type.μ F) π
givenCata-alg : ∀ {m} (ctx : NamedCtx m) (F : Once.Spec.Type.Fun m) (π : Once.Spec.Grade.Purity)
              → Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F
              → (A₁ A : Ty m) (π′ : Once.Spec.Grade.Purity) {Ψ : Surface.Usage (NamedCtx.size ctx)}
              → SExpr (NamedCtx.debruijn ctx) Ψ (A₁ ⇒ω⟨ π′ ⟩ A) → (d fr : ℕ)
              → Dec (⟦ F ⟧F A <: A₁) → Dec (π′ ⊑π π)
              → GivenElabResult (NamedCtx.debruijn ctx) (Once.Spec.Type.μ F) π
givenCata-alg ctx F π w A₁ A π′ algE d fr (yes p) (yes o) =
  success A _ (Surface.cata w (Surface.coerce (sub-arr {q = Once.Spec.Grade.Many} p (<:-refl A) o) algE)) (suc d) fr
givenCata-alg ctx F π w A₁ A π′ algE d fr (no _) _ = failure (BuiltinTypeMismatch "cata")
givenCata-alg ctx F π w A₁ A π′ algE d fr (yes _) (no _) = failure (BuiltinTypeMismatch "cata")
givenCata-wf ctx F π nothing  r = failure (BuiltinTypeMismatch "cata")
givenCata-wf ctx F π (just w) (failure err) = failure err
givenCata-wf ctx F π (just w) (success (A₁ Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] A) Ψ algE d fr) =
  givenCata-alg ctx F π w A₁ A π′ algE d fr (⟦ F ⟧F A <:? A₁) (π′ ⊑π? π)
{-# CATCHALL #-}
givenCata-wf ctx F π (just w) (success _ _ _ _ _) = failure (BuiltinTypeMismatch "cata")
givenCata-mu ctx π (mu-at F) r = givenCata-wf ctx F π (wfFun? (NamedCtx.kinds ctx) F) r
givenCata-mu ctx π mu-other  r = failure (BuiltinTypeMismatch "cata")
givenCata ctx A π r = givenCata-mu ctx π (muV A) r

------------------------------------------------------------------------
-- Which forms a domain-given type comes from (`DomainForm`, `SynthForm`)
------------------------------------------------------------------------

-- An own polymorphic definition, and whether its domain fixes its instance.
data PolyKind : Set where
  not-poly poly-dom poly-other : PolyKind

polyKind-c : ∀ {sd sco : PolyType} → Dec (CodVarsInDom sd sco) → PolyKind
polyKind-c (yes _) = poly-dom
polyKind-c (no _)  = poly-other

polyKind-a : ∀ {sc : PolyType} → Maybe (ArrowView sc) → PolyKind
polyKind-a nothing                    = poly-other
polyKind-a (just (sd , sco , π′ , _)) = polyKind-c {sd = sd} {sco = sco} (codVarsInDom? sd sco)

polyKind-g : (sc : PolyType) → Ground sc ⊎ ⊤ → PolyKind
polyKind-g sc (inj₁ _)  = not-poly
polyKind-g sc (inj₂ tt) = polyKind-a (arrowSchema? sc)

polyKind-own : Maybe Type → Maybe Type → Maybe (PolyType × Syn.Expr × PolyCtx) → PolyKind
polyKind-own nothing  nothing  nothing                 = not-poly
polyKind-own nothing  nothing  (just (sc , _ , _))     = polyKind-g sc (isGround sc)
polyKind-own (just _) _        _                       = not-poly
polyKind-own nothing  (just _) _                       = not-poly

polyKind : ∀ {m} (ctx : NamedCtx m) (c : CanonicalName) → PolyKind
polyKind ctx (canonical [])          = not-poly
polyKind ctx (own x)                 =
  polyKind-own (lookupImport (NamedCtx.sig ctx) x) (lookupImport (NamedCtx.imports ctx) x) (lookupPolyPrefix (NamedCtx.polys ctx) x)
polyKind ctx (canonical (_ ∷ _ ∷ _)) = not-poly

notPolyB : PolyKind → Bool
notPolyB not-poly   = true
notPolyB poly-dom   = false
notPolyB poly-other = false

domPolyB : PolyKind → Bool
domPolyB not-poly   = true
domPolyB poly-dom   = true
domPolyB poly-other = false

constB : ∀ {g} → GenKindView g → Bool
constB (gk-const _) = true
constB (gk-map _)   = false
constB (gk-comb₁ _) = false
constB (gk-comb₂ _) = false

isYesB : ∀ {P : Set} → Dec P → Bool
isYesB (yes _) = true
isYesB (no _)  = false

synthForm? : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) → Bool
domainForm? : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) → Bool
synthApp? : (f : Syn.Expr) → Head → Bool
domainApp? : ∀ {m} (ctx : NamedCtx m) (f a : Syn.Expr) → Bool
domainGen? : G.Gen → Bool
synthGenB : (g : G.Gen) → GenKindView g → Bool
notComb₂B : ∀ {g} → GenKindView g → Bool

synthGenB g (gk-map _)   = not (isYesB (fromCodomain? (G.kind g)))
synthGenB g (gk-const _) = true
synthGenB g (gk-comb₁ _) = false
synthGenB g (gk-comb₂ _) = false
notComb₂B (gk-comb₂ _) = false
notComb₂B (gk-map _)   = true
notComb₂B (gk-const _) = true
notComb₂B (gk-comb₁ _) = true

synthForm? ctx (Raw.RInt _)            = true
synthForm? ctx (Raw.RFloat _ _ _ _)    = true
synthForm? ctx Raw.RUnit               = true
synthForm? ctx (Raw.RVar _)            = true
synthForm? ctx (Raw.RResolved c)       = notPolyB (polyKind ctx c)
synthForm? ctx (Raw.RGen g)            = constB (genKindView g)
synthForm? ctx (Raw.RAnnot _ _)        = true
synthForm? ctx (Raw.RPair a b)         = synthForm? ctx a ∧ synthForm? ctx b
synthForm? ctx (Raw.RNeg _)            = true
synthForm? ctx (Raw.RBinOp _ _ _)      = true
synthForm? ctx (Raw.RLet _ _ _)        = true
synthForm? ctx (Raw.RDestruct _ _ _ _ _) = true
synthForm? ctx (Raw.RApp f x)          = synthApp? f (headView f)
synthForm? ctx (Raw.RQualified _ _)    = false
synthForm? ctx (Raw.RLam _ _)          = false

-- `RApp f x` is a `SynthForm` when `f` is no partial combinator and the
-- application is no codomain-fixed map applied.
synthApp? _ (hv-gen g) = synthGenB g (genKindView g)
synthApp? _ (hv-gen₁ g a) = notComb₂B (genKindView g)
synthApp? _ (hv-gen₂ g a b) = true
synthApp? _ hv-lam          = true
synthApp? _ hv-other        = true

domainGen? g = isYesB (fromDomain? (G.kind g))

domainForm? ctx (Raw.RLam _ b)    = synthForm? ctx b
domainForm? ctx (Raw.RResolved c) = domPolyB (polyKind ctx c)
domainForm? ctx (Raw.RGen g)      = synthForm? ctx (Raw.RGen g) ∨ domainGen? g
domainForm? ctx (Raw.RApp f a)    = synthForm? ctx (Raw.RApp f a) ∨ domainApp? ctx f a
{-# CATCHALL #-}
domainForm? ctx e                 = synthForm? ctx e

domainApp? ctx (Raw.RApp (Raw.RGen G.compose) f) g = domainForm? ctx f ∧ domainForm? ctx g
domainApp? ctx (Raw.RApp (Raw.RGen G.case) f) g    = domainForm? ctx f ∧ domainForm? ctx g
domainApp? ctx (Raw.RApp (Raw.RGen G.pair) f) g    = domainForm? ctx f ∧ domainForm? ctx g
domainApp? ctx (Raw.RGen G.cata) a                 = synthForm? ctx a
{-# CATCHALL #-}
domainApp? ctx _ _                                 = false

------------------------------------------------------------------------
-- The checker
------------------------------------------------------------------------

mutual
  inferElab : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
  checkElab : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T
  -- Plan 0.58 E1-full: the WORKER carries a well-founded `Acc` on `length polys`.
  checkElab-wf : ∀ {m} → (ctx : NamedCtx m) → Acc _<_ (length (NamedCtx.polys ctx))
                → (e : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T
  -- The domain-given mode, one clause per rule.
  elabGiven : ∀ {m} → (ctx : NamedCtx m) (e : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
            → GivenElabResult (NamedCtx.debruijn ctx) A π

  -- An application, by its head.
  inferApp : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
  inferAppGen : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (x : Syn.Expr) → GenKindView g → InferElabResult (NamedCtx.debruijn ctx)
  inferMapAt : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (x : Syn.Expr) → Dec (G.FromDomain (G.kind g)) → InferElabResult (NamedCtx.debruijn ctx)
  inferAppGen₁ : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) → GenKindView g → InferElabResult (NamedCtx.debruijn ctx)
  inferAppGen₂ : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) → GenKindView g → InferElabResult (NamedCtx.debruijn ctx)
  -- `s-app`: the head synthesized an arrow; the argument checked at its
  -- domain; the result is `𝕋` of the arrow's grade.
  appOn : ∀ {m} (ctx : NamedCtx m) (x : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
  appAt : ∀ {m} (ctx : NamedCtx m) (x : Syn.Expr) (A B : Ty m) (q : Quantity) (π : Once.Spec.Grade.Purity)
          {Ψ₁ : Surface.Usage (NamedCtx.size ctx)} → SExpr (NamedCtx.debruijn ctx) Ψ₁ (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B)
        → (d fr : ℕ) → CheckElabResult (NamedCtx.debruijn ctx) A → InferElabResult (NamedCtx.debruijn ctx)
  -- Any other head: synthesized (`s-app`), but an own polymorphic definition,
  -- which only checks (the spine).
  appOther : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx)
  appRes : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) → PolyKind → InferElabResult (NamedCtx.debruijn ctx)
  -- `s-app-spine`: the argument synthesizes, and the head, given it, determines the result.
  inferSpine : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
  spineAt : ∀ {m} (ctx : NamedCtx m) {X : Ty m} {Ψx : Surface.Usage (NamedCtx.size ctx)}
          → SExpr (NamedCtx.debruijn ctx) Ψx X → (dx : ℕ) → GivenElabResult (NamedCtx.debruijn ctx) X Once.Spec.Grade.pure
          → InferElabResult (NamedCtx.debruijn ctx)

  checkApp : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T
  checkAppGen : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) (T : Ty m) → GenKindView g → CheckElabResult (NamedCtx.debruijn ctx) T
  checkAppGen₁ : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (a x : Syn.Expr) (T : Ty m) → GenKindView g → CheckElabResult (NamedCtx.debruijn ctx) T
  -- `c-sub` at an application: it synthesizes, converted.
  checkSubApp : ∀ {m} (ctx : NamedCtx m) (f x : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T
  -- `c-map-app`: a map its codomain fixes, applied: the argument at the domain.
  checkMapApp : ∀ {m} (ctx : NamedCtx m) (f : Syn.Expr) (g : G.Gen) (x : Syn.Expr) (T : Ty m) → Dec (G.FromCodomain (G.kind g))
              → CheckElabResult (NamedCtx.debruijn ctx) T
  checkMapApp-go : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (x : Syn.Expr) (T : Ty m)
                 → Maybe (Σ[ A ∈ Ty m ] Map A T) → CheckElabResult (NamedCtx.debruijn ctx) T
  -- The mediators.
  checkComb₁ : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (arg : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T
  checkComb₂ : ∀ {m} (ctx : NamedCtx m) (g : G.Gen) (f h : Syn.Expr) (T : Ty m) → CheckElabResult (NamedCtx.debruijn ctx) T

  checkPairOn : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) → PairTarget T
              → CheckElabResult (NamedCtx.debruijn ctx) T
  checkPairLit : ∀ {m} → (ctx : NamedCtx m) → (a b : Syn.Expr) → (A B : Ty m)
               → CheckElabResult (NamedCtx.debruijn ctx) (A Once.Spec.Type.* B)
  checkCaseOn : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) → CaseTarget T
              → CheckElabResult (NamedCtx.debruijn ctx) T
  -- `compose f g`: the middle object from `g`'s domain-given form when it has
  -- one (`c-compose-g`), from `f`'s synthesized domain otherwise (`c-compose-f`).
  checkComposeOn : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (T : Ty m) → ArrowTarget T
                 → CheckElabResult (NamedCtx.debruijn ctx) T
  checkCompose-route : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity) → Bool
                     → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ π ⟩ C)
  checkCompose-g : ∀ {m} → (ctx : NamedCtx m) (f : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity)
                 → GivenElabResult (NamedCtx.debruijn ctx) A π
                 → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ π ⟩ C)
  checkCompose-f : ∀ {m} → (ctx : NamedCtx m) (g : Syn.Expr) (A C : Ty m) (π : Once.Spec.Grade.Purity)
                 → InferElabResult (NamedCtx.debruijn ctx)
                 → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ π ⟩ C)
  checkCompose-f-sub : ∀ {m} → (ctx : NamedCtx m) (g : Syn.Expr) (A B C C′ : Ty m) (π π′ : Once.Spec.Grade.Purity)
                       {Ψf : Surface.Usage (NamedCtx.size ctx)} → SExpr (NamedCtx.debruijn ctx) Ψf (B ⇒ω⟨ π′ ⟩ C′) → (df : ℕ)
                     → Dec ((B ⇒ω⟨ π′ ⟩ C′) <: (B ⇒ω⟨ π ⟩ C))
                     → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ π ⟩ C)
  checkCurryOn : ∀ {m} (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) → CurryTarget T
               → CheckElabResult (NamedCtx.debruijn ctx) T
  checkCataOn : ∀ {m} (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) → CataTarget T
              → CheckElabResult (NamedCtx.debruijn ctx) T
  checkCataGo : ∀ {m} → (ctx : NamedCtx m) (alg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m)
                (π : Once.Spec.Grade.Purity)
              → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
              → CheckElabResult (NamedCtx.debruijn ctx) (Once.Spec.Type.μ F ⇒ω⟨ π ⟩ A)
  -- `c-ana`: into the final coalgebra the type names (a stream, or `T∞ B` at `eff`).
  checkAnaOn : ∀ {m} (ctx : NamedCtx m) (arg : Syn.Expr) (T : Ty m) → AnaTarget T
             → CheckElabResult (NamedCtx.debruijn ctx) T
  checkAnaGo : ∀ {m} → (ctx : NamedCtx m) (coalg : Syn.Expr) (F : Once.Spec.Type.Fun m) (A : Ty m)
               (π₀ : Once.Spec.Grade.Purity) (φ : Once.Spec.Grade.Finite)
             → (mw : Maybe (Once.Spec.Type.WFFun (NamedCtx.kinds ctx) F))
             → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ π₀ ⟩ Once.Spec.Type.ν F φ)
  checkLoop : ∀ {m} → (ctx : NamedCtx m) (A B : Ty m)
            → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ Once.Spec.Grade.act ⟩ (B Once.Spec.Type.+ A))
            → CheckElabResult (NamedCtx.debruijn ctx) (A ⇒ω⟨ Once.Spec.Grade.eff ⟩ B)

  -- The combinators in the domain-given mode.
  givenApp : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) (A : Ty m) (π : Once.Spec.Grade.Purity)
           → InferElabResult (NamedCtx.debruijn ctx) → GivenElabResult (NamedCtx.debruijn ctx) A π
  givenCase : ∀ {m} → (ctx : NamedCtx m) (f g : Syn.Expr) {A : Ty m} (π : Once.Spec.Grade.Purity) → SumV A
            → GivenElabResult (NamedCtx.debruijn ctx) A π

  inferElabV-RLet-aux : ∀ {m} → (ctx : NamedCtx m) (x : String) (e₁ e₂ : Syn.Expr)
    → InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
  inferElabV-RDestruct-aux : ∀ {m} → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
    → InferElabResult (NamedCtx.debruijn ctx)
    → InferElabResult (NamedCtx.debruijn ctx)
  inferElabV-RDestruct-auxL : ∀ {m} → (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
    (A B : Ty m) {Ψs : Surface.Usage (NamedCtx.size ctx)}
    (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)) (ds fs : ℕ)
    → InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))
    → InferElabResult (NamedCtx.debruijn ctx)
  checkElabV-RPair-aux : ∀ {m} (ctx : NamedCtx m) (a b : Syn.Expr) (T : Ty m)
    → RPairTarget T
    → CheckElabResult (NamedCtx.debruijn ctx) T

  ----------------------------------------------------------------------
  -- Synthesis
  ----------------------------------------------------------------------

  inferElab ctx (Raw.RInt n) = success Int _ (Surface.int n) 0 0
  inferElab ctx (Raw.RFloat sg i f l) = inferElabV-RFloat-aux ctx sg i f l
  inferElab ctx Raw.RUnit = success Unit _ Surface.unit 0 0
  inferElab ctx (Raw.RLam _ _) = failure LambdaInInferMode
  inferElab ctx (Raw.RAnnot e T) = inferElabV-RAnnot-aux ctx e T (checkElab ctx e (wk₀ T))
  inferElab ctx (Raw.RPair a b) = inferElabV-RPair-aux ctx a b (inferElab ctx a) (inferElab ctx b)
  -- The resolver reads every `name@alias`, so an unresolved one is never well typed.
  inferElab ctx (Raw.RQualified name alias) = failure (UnboundQualified name alias)
  inferElab ctx (Raw.RResolved cn) = inferElabV-RResolved-aux ctx cn _ refl
  inferElab ctx (Raw.RGen g) = inferGen ctx g (genKindView g)
  -- A bare `RVar` is a local: the resolver resolved every other name.
  inferElab ctx (Raw.RVar x) = inferElabV-RVar-lookup-aux ctx x _ refl
  inferElab ctx (Raw.RNeg e) = inferElabV-RNeg-aux ctx e (inferElab ctx e)
  inferElab ctx (Raw.RLet x e₁ e₂) = inferElabV-RLet-aux ctx x e₁ e₂ (inferElab ctx e₁)
  inferElab ctx (Raw.RDestruct scrut xL eL xR eR) = inferElabV-RDestruct-aux ctx scrut xL eL xR eR (inferElab ctx scrut)
  inferElab ctx (Raw.RApp f arg) = inferApp ctx f arg
  inferElab ctx (Raw.RBinOp op e₁ e₂) = inferElabV-RBinOp-aux ctx op e₁ e₂ (inferElab ctx e₁) (inferElab ctx e₂)

  -- A generator as the head: a map (the spine), a constant (an ordinary
  -- application), a combinator (partial: no rule).
  inferApp ctx f@(Raw.RGen g) x                       = inferAppGen ctx g x (genKindView g)
  inferApp ctx f@(Raw.RApp (Raw.RGen g) a) x            = inferAppGen₁ ctx f g x (genKindView g)
  inferApp ctx f@(Raw.RApp (Raw.RApp (Raw.RGen g) a) b) x = inferAppGen₂ ctx f g x (genKindView g)
  inferApp ctx f@(Raw.RLam y b) x                       = inferSpine ctx f (inferElab ctx x)
  {-# CATCHALL #-}
  inferApp ctx f x                                      = appOther ctx f x

  inferAppGen ctx g x (gk-map _)   = inferMapAt ctx g x (fromDomain? (G.kind g))
  inferAppGen ctx g x (gk-const _) = appOn ctx x (inferGen ctx g (genKindView g))
  inferAppGen ctx g x (gk-comb₁ _) = failure (BuiltinTypeMismatch (G.word g))
  inferAppGen ctx g x (gk-comb₂ _) = failure (BuiltinTypeMismatch (G.word g))

  -- A map whose domain does not fix its instance has no rule here, whatever
  -- the argument (`d-map` needs `FromDomain`): the head is reported first.
  inferMapAt ctx g x (yes _) = inferMapSpine ctx g (inferElab ctx x)
  inferMapAt ctx g x (no _)  = failure (spineErr g)

  inferAppGen₁ ctx f g x (gk-comb₁ _) = inferSpine ctx f (inferElab ctx x)
  inferAppGen₁ ctx f g x (gk-comb₂ _) = failure (BuiltinTypeMismatch (G.word g))
  inferAppGen₁ ctx f g x (gk-map _)   = appOn ctx x (inferElab ctx f)
  inferAppGen₁ ctx f g x (gk-const _) = appOn ctx x (inferElab ctx f)

  inferAppGen₂ ctx f g x (gk-comb₂ _) = inferSpine ctx f (inferElab ctx x)
  inferAppGen₂ ctx f g x (gk-map _)   = appOn ctx x (inferElab ctx f)
  inferAppGen₂ ctx f g x (gk-const _) = appOn ctx x (inferElab ctx f)
  inferAppGen₂ ctx f g x (gk-comb₁ _) = appOn ctx x (inferElab ctx f)

  appOn ctx x (failure err) = failure err
  appOn ctx x (success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B) Ψ₁ fE df ff) =
    appAt ctx x A B q π fE df ff (checkElab ctx x A)
  appOn ctx x (success Unit _ _ _ _)           = failure (NotFunction {0} Unit)
  appOn ctx x (success Void _ _ _ _)           = failure (NotFunction {0} Void)
  appOn ctx x (success Int _ _ _ _)            = failure (NotFunction {0} Int)
  appOn ctx x (success Float _ _ _ _)          = failure (NotFunction {0} Float)
  appOn ctx x (success (var iᵣ) _ _ _ _)       = failure (NotFunction (var iᵣ))
  appOn ctx x (success (A Once.Spec.Type.* B) _ _ _ _) = failure (NotFunction (A Once.Spec.Type.* B))
  appOn ctx x (success (A Once.Spec.Type.+ B) _ _ _ _) = failure (NotFunction (A Once.Spec.Type.+ B))
  appOn ctx x (success (Once.Spec.Type.μ F) _ _ _ _)   = failure (NotFunction (Once.Spec.Type.μ F))
  appOn ctx x (success (Once.Spec.Type.ν F π) _ _ _ _) = failure (NotFunction (Once.Spec.Type.ν F π))

  appAt ctx x A B q π fE df ff (failure err) = failure err
  appAt ctx x A B q Once.Spec.Grade.pure fE df ff (success Ψ₂ xE dx fx) =
    success B _ (Surface.app fE xE) (df ⊔ dx) fx
  appAt ctx x A B q Once.Spec.Grade.act fE df ff (success Ψ₂ xE dx fx) =
    success (Unit ⇒ω⟨ Once.Spec.Grade.act ⟩ B) _ (Surface.effApp {g = Once.Spec.Grade.eg-act} fE xE) (df ⊔ dx) fx
  appAt ctx x A B q Once.Spec.Grade.eff fE df ff (success Ψ₂ xE dx fx) =
    success (Unit ⇒ω⟨ Once.Spec.Grade.eff ⟩ B) _ (Surface.effApp {g = Once.Spec.Grade.eg-eff} fE xE) (df ⊔ dx) fx

  appOther ctx f@(Raw.RResolved cn) x = appRes ctx f x (polyKind ctx cn)
  {-# CATCHALL #-}
  appOther ctx f x                     = appOn ctx x (inferElab ctx f)
  appRes ctx f x not-poly   = appOn ctx x (inferElab ctx f)
  appRes ctx f x poly-dom   = inferSpine ctx f (inferElab ctx x)
  appRes ctx f x poly-other = inferSpine ctx f (inferElab ctx x)

  inferSpine ctx f (failure err) = failure err
  inferSpine ctx f (success X Ψx xE dx frx) = spineAt ctx xE dx (elabGiven ctx f X Once.Spec.Grade.pure)
  spineAt ctx xE dx (failure err) = failure err
  spineAt ctx xE dx (success T Ψf fE df frf) = success T _ (Surface.app fE xE) (suc (df ⊔ dx)) frf

  ----------------------------------------------------------------------
  -- Checking
  ----------------------------------------------------------------------

  checkElab-wf ctx ac (Raw.RApp f arg) T = checkApp ctx f arg T
  -- `c-lam`, at any arrow.
  checkElab-wf ctx ac (Raw.RLam x body) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B) with checkElab (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success (q' ∷ᵘ Ψ) bodyE d fr with decideLeq q' q
  ...   | just eq = success _ (Surface.lam q eq bodyE) (suc d) fr
  ...   | nothing = failure (UsageViolation x q q')
  {-# CATCHALL #-}
  checkElab-wf ctx ac (Raw.RLam _ _) _ = failure LambdaRequiresFunctionType
  -- A local: synthesized, converted.
  checkElab-wf ctx ac (Raw.RVar x) T with inferElab ctx (Raw.RVar x)
  ... | r = embedOrSubsume ctx (Raw.RVar x) T r
  -- A resolved name: synthesized and converted, or (`c-poly`) an own
  -- polymorphic definition at an instance.
  checkElab-wf ctx ac (Raw.RResolved cn) T with inferElab ctx (Raw.RResolved cn)
  ... | r = checkElabV-RResolved-other ctx cn T r
  -- A generator: a map at an instance of the table (`c-map`), a constant
  -- converted (`c-sub`).
  checkElab-wf ctx ac (Raw.RGen g) T with genKindView g
  ... | gk-map _   = checkMapAt ctx g (arrowTarget T)
  ... | gk-const _ = embedOrSubsume ctx (Raw.RGen g) T (inferGen ctx g (genKindView g))
  ... | gk-comb₁ _ = failure (BuiltinTypeMismatch (G.word g))
  ... | gk-comb₂ _ = failure (BuiltinTypeMismatch (G.word g))
  -- `c-pair-lit`: a pair literal has its own rule, at a product only.
  checkElab-wf ctx ac (Raw.RPair a b) T = checkElabV-RPair-aux ctx a b T (classifyRPairTarget T)
  {-# CATCHALL #-}
  checkElab-wf ctx ac e T with inferElab ctx e
  ... | r = embedOrSubsume ctx e T r

  checkElab ctx e T = checkElab-wf ctx (<-wellFounded (length (NamedCtx.polys ctx))) e T

  checkApp ctx f@(Raw.RGen g) x T            = checkAppGen ctx f g x T (genKindView g)
  checkApp ctx f@(Raw.RApp (Raw.RGen g) a) x T = checkAppGen₁ ctx f g a x T (genKindView g)
  {-# CATCHALL #-}
  checkApp ctx f x T                         = checkSubApp ctx f x T

  checkAppGen ctx f g x T (gk-map _)   = checkMapApp ctx f g x T (fromCodomain? (G.kind g))
  checkAppGen ctx f g x T (gk-const _) = checkSubApp ctx f x T
  checkAppGen ctx f g x T (gk-comb₁ _) = checkComb₁ ctx g x T
  checkAppGen ctx f g x T (gk-comb₂ _) = checkSubApp ctx f x T

  checkAppGen₁ ctx f g a x T (gk-comb₂ _) = checkComb₂ ctx g a x T
  checkAppGen₁ ctx f g a x T (gk-map _)   = checkSubApp ctx f x T
  checkAppGen₁ ctx f g a x T (gk-const _) = checkSubApp ctx f x T
  checkAppGen₁ ctx f g a x T (gk-comb₁ _) = checkSubApp ctx f x T

  checkSubApp ctx f x T with inferElab ctx (Raw.RApp f x)
  ... | r = embedOrSubsume ctx (Raw.RApp f x) T r

  checkMapApp ctx f g x T (yes _) = checkMapApp-go ctx g x T (mapTo? (NamedCtx.kinds ctx) g T)
  checkMapApp ctx f g x T (no _)  = checkSubApp ctx f x T
  checkMapApp-go ctx g x T nothing = failure (mapToErr g)
    where
      mapToErr : G.Gen → TypeError
      mapToErr G.inl = InlNeedsSumType
      mapToErr G.inr = InrNeedsSumType
      {-# CATCHALL #-}
      mapToErr g′    = BuiltinTypeMismatch (G.word g′)
  checkMapApp-go ctx g x T (just (A , mI)) with checkElab ctx x A
  ... | failure err = failure err
  ... | success Ψ xE d fr = success _ (Surface.morph-app mI xE) (suc d) fr

  checkComb₁ ctx G.curry arg T = checkCurryOn ctx arg T (curryTarget T)
  checkComb₁ ctx G.cata  arg T = checkCataOn ctx arg T (cataTarget T)
  checkComb₁ ctx G.ana   arg T = checkAnaOn ctx arg T (anaTarget T)
  {-# CATCHALL #-}
  checkComb₁ ctx g arg T = failure (BuiltinTypeMismatch (G.word g))

  checkComb₂ ctx G.compose f h T = checkComposeOn ctx f h T (arrowTarget T)
  checkComb₂ ctx G.case    f h T = checkCaseOn ctx f h T (caseTarget T)
  checkComb₂ ctx G.pair    f h T = checkPairOn ctx f h T (pairTarget T)
  {-# CATCHALL #-}
  checkComb₂ ctx g f h T = failure (BuiltinTypeMismatch (G.word g))

  -- `c-pair`: both arms at the pair's grade (D222).
  checkPairOn ctx f_inner arg _ (pair-at A π B C)
    with checkElab ctx f_inner (A ⇒ω⟨ π ⟩ B)
  ... | failure err = failure err
  ... | success Ψf fE df frf with checkElab ctx arg (A ⇒ω⟨ π ⟩ C)
  ...     | failure err = failure err
  ...     | success Ψg gE dg frg = success _ (Surface.fork' fE gE) (suc (df Data.Nat.⊔ dg)) frg
  checkPairOn _ _ _ _ pair-other = failure (BuiltinTypeMismatch "pair")

  checkPairLit ctx a b A B with checkElab ctx a A
  ... | failure err = failure err
  ... | success Ψ₁ aE da fa with checkElab ctx b B
  ...   | failure err = failure err
  ...   | success Ψ₂ bE db fb = success _ (Surface.pair aE bE) (da Data.Nat.⊔ db) fb

  -- `c-case`.
  checkCaseOn ctx f g _ (case-at A B π C) with checkElab ctx f (A ⇒ω⟨ π ⟩ C)
  ... | failure err = failure err
  ... | success Ψf fE df frf with checkElab ctx g (B ⇒ω⟨ π ⟩ C)
  ...     | failure err = failure err
  ...     | success Ψg gE dg frg = success _ (Surface.copair' fE gE) (suc (df Data.Nat.⊔ dg)) frf
  checkCaseOn _ _ _ _ case-other = failure (BuiltinTypeMismatch "case")

  checkComposeOn ctx f g _ (arrow-at A π C) = checkCompose-route ctx f g A C π (domainForm? ctx g)
  checkComposeOn _ _ _ _ arrow-other = failure (BuiltinTypeMismatch "compose")

  checkCompose-route ctx f g A C π true  = checkCompose-g ctx f A C π (elabGiven ctx g A π)
  checkCompose-route ctx f g A C π false = checkCompose-f ctx g A C π (inferElab ctx f)

  checkCompose-g ctx f A C π (failure err) = failure err
  checkCompose-g ctx f A C π (success B Ψg gE dg frg) with checkElab ctx f (B ⇒ω⟨ π ⟩ C)
  ... | failure err = failure err
  ... | success Ψf fE df frf = success _ (Surface.comp' fE gE) (suc (df Data.Nat.⊔ dg)) frf

  checkCompose-f ctx g A C π (failure err) = failure err
  checkCompose-f ctx g A C π (success (B Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π′ ] C′) Ψf fE df frf) =
    checkCompose-f-sub ctx g A B C C′ π π′ fE df ((B ⇒ω⟨ π′ ⟩ C′) <:? (B ⇒ω⟨ π ⟩ C))
  {-# CATCHALL #-}
  checkCompose-f ctx g A C π (success _ _ _ _ _) = failure ComposeMiddleUndetermined

  checkCompose-f-sub ctx g A B C C′ π π′ fE df (no _) =
    failure (TypeMismatch (B ⇒ω⟨ π ⟩ C) (B ⇒ω⟨ π′ ⟩ C′))
  checkCompose-f-sub ctx g A B C C′ π π′ fE df (yes p) with checkElab ctx g (A ⇒ω⟨ π ⟩ B)
  ... | failure err = failure err
  ... | success Ψg gE dg frg = success _ (Surface.comp' (Surface.coerce p fE) gE) (suc (df Data.Nat.⊔ dg)) frg

  -- `c-curry` (D222: the body at the inner arrow's grade).
  checkCurryOn ctx arg _ (curry-at A π₀ B π C) with checkElab ctx arg ((A Once.Spec.Type.* B) ⇒ω⟨ π ⟩ C)
  ... | failure err = failure err
  ... | success Ψ argE d fr = success _ (Surface.curry' argE) (suc d) fr
  checkCurryOn _ _ _ curry-other = failure (BuiltinTypeMismatch "curry")

  -- `c-cata`.
  checkCataOn ctx alg _ (cata-at F π A) = checkCataGo ctx alg F A π (wfFun? (NamedCtx.kinds ctx) F)
  checkCataOn _ _ _ cata-other = failure (BuiltinTypeMismatch "cata")
  checkCataGo ctx alg F A π nothing = failure (BuiltinTypeMismatch "cata")
  checkCataGo ctx alg F A π (just wfF) with checkElab ctx alg (⟦ F ⟧F A ⇒ω⟨ π ⟩ A)
  ... | failure err = failure err
  ... | success Ψ algE d fr = success _ (Surface.cata wfF algE) (suc d) fr

  -- `c-ana`: at `eff`, into `T∞ B` (the round a block); otherwise a stream.
  checkAnaOn ctx coalg _ (ana-at A π₀ F π ua) = checkAnaGo ctx coalg F A π₀ π (wfFun? (NamedCtx.kinds ctx) F)
  checkAnaOn ctx round _ (loop-at A B) =
    checkLoop ctx A B (checkElab ctx round (A ⇒ω⟨ Once.Spec.Grade.act ⟩ (B Once.Spec.Type.+ A)))
  checkAnaOn _ _ _ ana-other = failure (BuiltinTypeMismatch "ana")
  checkAnaGo ctx coalg F A π₀ φ nothing = failure (BuiltinTypeMismatch "ana")
  checkAnaGo ctx coalg F A π₀ φ (just wfF) with checkElab ctx coalg (A ⇒ω⟨ Once.Spec.Grade.fin φ ⟩ ⟦ F ⟧F A)
  ... | failure err = failure err
  ... | success Ψ coalgE d fr = success _ (Surface.ana wfF coalgE) (suc d) fr
  checkLoop ctx A B (failure err) = failure err
  checkLoop ctx A B (success Ψ roundE d fr) = success _ (Surface.loop roundE) (suc d) fr

  -- `c-pair-lit` at a product; a pair literal has no other checking rule.
  checkElabV-RPair-aux ctx a b _ (rpt-prod A B) = checkPairLit ctx a b A B
  checkElabV-RPair-aux ctx a b _ (rpt-vlift X A B π) =
    failure (TypeMismatch (X ⇒ω⟨ π ⟩ (A Once.Spec.Type.* B)) (A Once.Spec.Type.* B))
  checkElabV-RPair-aux ctx a b _ (rpt-other T) = failure (BuiltinTypeMismatch "pair")

  ----------------------------------------------------------------------
  -- The domain-given mode
  ----------------------------------------------------------------------

  -- `d-lam`.
  elabGiven ctx (Raw.RLam x body) A π with inferElab (extendNamedCtx ctx x A) body
  ... | failure err = failure err
  ... | success B (q' ∷ᵘ Ψ) bodyE d fr = success B Ψ (Surface.lam Once.Spec.Grade.Many (≤q-Many q') bodyE) (suc d) fr
  -- `d-infer` or `d-poly`.
  elabGiven ctx (Raw.RResolved cn) A π = given-res ctx cn A π (inferElab ctx (Raw.RResolved cn))
  -- `d-map`, or a constant synthesized (`d-infer`).
  elabGiven ctx (Raw.RGen g) A π with genKindView g
  ... | gk-map _   = givenMap ctx g A π (mapFrom? (NamedCtx.kinds ctx) g A)
  ... | gk-const _ = given-infer ctx (Raw.RGen g) A π (inferGen ctx g (genKindView g))
  ... | gk-comb₁ _ = failure (BuiltinTypeMismatch (G.word g))
  ... | gk-comb₂ _ = failure (BuiltinTypeMismatch (G.word g))
  elabGiven ctx (Raw.RApp f g) A π = givenApp ctx f g A π (inferElab ctx (Raw.RApp f g))
  {-# CATCHALL #-}
  elabGiven ctx e A π = given-infer ctx e A π (inferElab ctx e)

  -- `d-compose`, `d-case`, `d-pair`, `d-cata`; any other application `d-infer`.
  givenApp ctx (Raw.RApp (Raw.RGen G.compose) f) g A π _ with elabGiven ctx g A π
  ... | failure err = failure err
  ... | success M Ψg gE dg frg with elabGiven ctx f M π
  ...   | failure err = failure err
  ...   | success B Ψf fE df frf = success B _ (Surface.comp' fE gE) (suc (df Data.Nat.⊔ dg)) frf
  givenApp ctx (Raw.RApp (Raw.RGen G.case) f) g A π _ = givenCase ctx f g π (sumV A)
  givenApp ctx (Raw.RApp (Raw.RGen G.pair) f) g A π _ with elabGiven ctx f A π
  ... | failure err = failure err
  ... | success B Ψf fE df frf with elabGiven ctx g A π
  ...   | failure err = failure err
  ...   | success C Ψg gE dg frg = success (B Once.Spec.Type.* C) _ (Surface.fork' fE gE) (suc (df Data.Nat.⊔ dg)) frg
  givenApp ctx (Raw.RGen G.cata) alg A π _ = givenCata ctx A π (inferElab ctx alg)
  {-# CATCHALL #-}
  givenApp ctx f g A π r = given-infer ctx (Raw.RApp f g) A π r

  givenCase ctx f g π (sum-at A B) with elabGiven ctx f A π
  ... | failure err = failure err
  ... | success C Ψf fE df frf with elabGiven ctx g B π
  ...   | failure err = failure err
  ...   | success C′ Ψg gE dg frg = given-case-join ctx f g A B π fE df gE dg frg (join? C C′)
  givenCase ctx f g π sum-other = failure (BuiltinTypeMismatch "case")

  ----------------------------------------------------------------------
  -- `let` and `destruct`
  ----------------------------------------------------------------------

  inferElabV-RLet-aux ctx x e₁ e₂ (failure err) = failure err
  inferElabV-RLet-aux ctx x e₁ e₂ (success A Ψ₁ e₁E d₁ f₁) =
    inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ (inferElab (extendNamedCtx ctx x A) e₂)

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
