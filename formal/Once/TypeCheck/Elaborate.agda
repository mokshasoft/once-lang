-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Elaborate
--
-- Combined type inference and elaboration.
-- Produces intrinsically-typed Surface.Syntax.Expr directly from RawExpr.
--
-- This avoids the problem with separate Resolve step needing subexpression
-- types that aren't available.
--
-- Part of OCP-0004: MAlonzo Compiler Replacement
------------------------------------------------------------------------

module Once.TypeCheck.Elaborate where

open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Integer using (ℤ; -_)
open import Data.Nat using (ℕ; zero; suc; _≤?_; _⊔_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)

open import Once.Type
open Once.Type using (showQuantity; showType) public
-- Plan 0.52 M2: IR re-exports the ungraded IRTy, whose Unit/K/μ-type/… clash
-- with Once.Type's (opened above). Hide the IRTy object/functor constructors
-- from the unqualified open (they stay available as `IR.*`); the surface-type
-- names resolve unambiguously to `Once.Type`.
open import Once.IR as IR hiding (Unit; Void; _*_; _+_; μ-type; ν-type; Int; Float; Str; Buffer; K; Id; _⊕_; _⊗_)
open import Once.IRTy.WF using (wf-⌊⌋)
-- Plan 0.36 Phase 1: `generic-info` reconstructs a SigOp's `SigOpInfo` from its
-- name, so `extract-morph-eff` can recover the direct `IR.SigOp` morphism of an
-- effectful sigOp used point-free (it elaborates as a closure otherwise).
-- Plan 0.38 M0.2: external arrow SigOps are built from their DECLARED
-- `! <shape>` effect (looked up in `NamedCtx.sigEffects`), never from a
-- hardcoded name. `generic-semM` supplies the (laundered) value ONLY for
-- the pure/value `pureV` positions — an effectful op carries a CONTRACT,
-- not a value, so `Emits`/`Halts` drop it entirely.
open import Once.Arith.SigOp.Builders using (generic-semM)
open import Once.SigOp.Info using (SigOpInfo; mk-info'; pureV; emitsV; haltsV; ffi-concrete)
open import Once.CanonicalName using (CanonicalName; bare; showCanonical; gen; NotGenerator; bare-NotGenerator; GenWord; genWord?)
open import Once.SigEffect using (SigEffect) renaming (halts to se-halts; emits to se-emits)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Error using (TypeError; renderError;
  LambdaInInferMode; LambdaRequiresFunctionType;
  InlInInferMode; InrInInferMode; InitialInInferMode;
  InlNeedsSumType; InrNeedsSumType;
  FstNeedsPair; SndNeedsPair; ArrNeedsFunction; NegationNotInt;
  CaseScrutineeNotSum; CaseBranchMismatch;
  ApplicationTypeMismatch; TypeMismatch; NotFunction;
  UsageViolation; BuiltinTypeMismatch;
  BinOpLeftError; BinOpRightError;
  UnboundVariable; UnboundQualified; NonConcreteSigOpType) public
open import Once.TypeCheck.Context using (Ctx; ∅; name)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookupUsage; tailUsage; _+ᵘ_)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)
open import Once.Surface.Thinning using (weaken; weakenFromEmpty)
open import Once.Surface.Properties using (+ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-zeroʳ)
open import Once.Surface.Elaborate as Elab using (elaborate; intLit; floatLit; strLit)

open import Once.TypeCheck.Classify public
import Once.Functor.Translate
open import Once.Functor.Translate using (IsConcrete; con-base; con-fun; IsBaseType)
open import Once.Functor.Decide using (wellFormedF?; isConcrete?; isBaseType?;
  isConcrete?-complete; isBaseType?-complete)
open import Once.TypeCheck.Morph using (MorphRaw; morphRaw?; morphToIR)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Float.Decimal using (Decimal; decimalOf)
import Once.Float.Decimal as Decimal
open import Once.TypeCheck.Judgment

------------------------------------------------------------------------
-- Weakening from Empty Context
------------------------------------------------------------------------

-- | Weaken from empty context to arbitrary context
--
-- Built-in expressions have no free variables, so we can weaken them
-- from ∅ to any context Γ by repeatedly applying weaken.
--
-- Note: weaken and exchange functions are now imported from Once.Surface.Thinning
--
-- weakenFromEmpty is now imported from Once.Surface.Thinning; it produces
-- SExpr Γ zeroUsage A from SExpr S∅ Surface.zeroUsage A, propagating the usage index.

------------------------------------------------------------------------
-- Type Equality (Decidable with proof)
------------------------------------------------------------------------

-- Helpers for ≟T / ≟F matching-constructor cases (avoid `with`-blocks).

≟F-K-aux : ∀ {A B} → Dec (A ≡ B) → Dec (K A ≡ K B)
≟F-K-aux (yes refl) = yes refl
≟F-K-aux (no ¬p)    = no λ { refl → ¬p refl }

≟F-⊕-aux : ∀ {F₁ G₁ F₂ G₂}
         → Dec (F₁ ≡ F₂) → Dec (G₁ ≡ G₂)
         → Dec ((F₁ ⊕ G₁) ≡ (F₂ ⊕ G₂))
≟F-⊕-aux (yes refl) (yes refl) = yes refl
≟F-⊕-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟F-⊕-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟F-⊕-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟F-⊗-aux : ∀ {F₁ G₁ F₂ G₂}
         → Dec (F₁ ≡ F₂) → Dec (G₁ ≡ G₂)
         → Dec ((F₁ ⊗ G₁) ≡ (F₂ ⊗ G₂))
≟F-⊗-aux (yes refl) (yes refl) = yes refl
≟F-⊗-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟F-⊗-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟F-⊗-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-*-aux : ∀ {A₁ B₁ A₂ B₂}
         → Dec (A₁ ≡ A₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ Once.Type.* B₁) ≡ (A₂ Once.Type.* B₂))
≟T-*-aux (yes refl) (yes refl) = yes refl
≟T-*-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟T-*-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟T-*-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-+-aux : ∀ {A₁ B₁ A₂ B₂}
         → Dec (A₁ ≡ A₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ Once.Type.+ B₁) ≡ (A₂ Once.Type.+ B₂))
≟T-+-aux (yes refl) (yes refl) = yes refl
≟T-+-aux (yes refl) (no ¬q)    = no λ { refl → ¬q refl }
≟T-+-aux (no ¬p)    (yes _)    = no λ { refl → ¬p refl }
≟T-+-aux (no ¬p)    (no _)     = no λ { refl → ¬p refl }

≟T-⇒-aux : ∀ {A₁ B₁ A₂ B₂ k₁ k₂}
         → Dec (A₁ ≡ A₂) → Dec (k₁ ≡ k₂) → Dec (B₁ ≡ B₂)
         → Dec ((A₁ ⇒[ k₁ ] B₁) ≡ (A₂ ⇒[ k₂ ] B₂))
-- Clause ORDER is load-bearing, not cosmetic: each `no` clause leaves the OTHER
-- two columns unsplit, so a kind clash (`pure` vs `eff`, `Many` vs `One`) decides
-- the arrow WITHOUT the domain/codomain deciders having to reduce first. With the
-- old all-eight-combinations order, `(A ⇒eff B) ≟T (A' ⇒pure B')` was stuck on
-- `A ≟T A'` for variable A/A' — and a stuck outer decision HIDES the inner ones
-- from a proof's `with`, which is what made D126's `embedOrSubsume-lifts`
-- unprovable. Same decisions, same results; just decided sooner.
≟T-⇒-aux _          (no ¬k)    _          = no λ { refl → ¬k refl }
≟T-⇒-aux (no ¬p)    _          _          = no λ { refl → ¬p refl }
≟T-⇒-aux _          _          (no ¬r)    = no λ { refl → ¬r refl }
≟T-⇒-aux (yes refl) (yes refl) (yes refl) = yes refl

≟T-μ-aux : ∀ {F₁ F₂} → Dec (F₁ ≡ F₂) → Dec (μ-type F₁ ≡ μ-type F₂)
≟T-μ-aux (yes refl) = yes refl
≟T-μ-aux (no ¬p)    = no λ { refl → ¬p refl }

≟T-ν-aux : ∀ {F₁ F₂} → Dec (F₁ ≡ F₂) → Dec (ν-type F₁ ≡ ν-type F₂)
≟T-ν-aux (yes refl) = yes refl
≟T-ν-aux (no ¬p)    = no λ { refl → ¬p refl }

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
  Maybe (∃-syntax (λ X → ∃-syntax (λ π → T ≡ (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Int))))
isRIntVliftTarget? (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Int) =
  just (X , π , refl)
isRIntVliftTarget? _ = nothing

-- …and the same view for a float literal. `gd-completeV` is what forces this
-- to exist: without it, `g-float` at a pure-arrow-to-Float target would take
-- the generic infer-and-match path and report a TypeMismatch, so the value
-- realm would accept a derivation the checker rejects — completeness false in
-- the same direction the acceptance premise fixes elsewhere.
isRFloatVliftTarget? :
  (T : Type) →
  Maybe (∃-syntax (λ X → ∃-syntax (λ π → T ≡ (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Once.Type.Float))))
isRFloatVliftTarget? (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Once.Type.Float) =
  just (X , π , refl)
isRFloatVliftTarget? _ = nothing

-- | Classify a check-mode target type for a pair literal: a product `A * B`
-- (bidirectional component check), a pure-arrow-to-product
-- `X ⇒[Many,pure] (A * B)` (value-lift / global element via `checkG`), or
-- anything else (generic infer-and-match). One named view so
-- `checkElabV (RPair a b) T` routes through a single scrutinee instead of two
-- specific clauses overlapping the catch-all (same gate as RInt; Plan 0.45).
data RPairTarget : Type → Set where
  rpt-prod  : (A B : Type) → RPairTarget (A Once.Type.* B)
  -- D069: grade-poly — a closed pair value inhabits the arrow at any π.
  rpt-vlift : (X A B : Type) (π : Once.Type.Purity) →
              RPairTarget (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A Once.Type.* B))
  rpt-other : (T : Type) → RPairTarget T

classifyRPairTarget : (T : Type) → RPairTarget T
classifyRPairTarget (A Once.Type.* B) = rpt-prod A B
classifyRPairTarget
  (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A Once.Type.* B)) =
  rpt-vlift X A B π
classifyRPairTarget T = rpt-other T

-- | Decidable functor and type equality (mutually recursive)
mutual
  -- | Decidable functor equality
  _≟F_ : (F G : Functor) → Dec (F ≡ G)
  K A ≟F K B = ≟F-K-aux (A ≟T B)
  Id ≟F Id = yes refl
  (F₁ ⊕ G₁) ≟F (F₂ ⊕ G₂) = ≟F-⊕-aux (F₁ ≟F F₂) (G₁ ≟F G₂)
  (F₁ ⊗ G₁) ≟F (F₂ ⊗ G₂) = ≟F-⊗-aux (F₁ ≟F F₂) (G₁ ≟F G₂)
  -- Mismatched constructors
  K _ ≟F Id = no λ ()
  K _ ≟F (_ ⊕ _) = no λ ()
  K _ ≟F (_ ⊗ _) = no λ ()
  Id ≟F K _ = no λ ()
  Id ≟F (_ ⊕ _) = no λ ()
  Id ≟F (_ ⊗ _) = no λ ()
  (_ ⊕ _) ≟F K _ = no λ ()
  (_ ⊕ _) ≟F Id = no λ ()
  (_ ⊕ _) ≟F (_ ⊗ _) = no λ ()
  (_ ⊗ _) ≟F K _ = no λ ()
  (_ ⊗ _) ≟F Id = no λ ()
  (_ ⊗ _) ≟F (_ ⊕ _) = no λ ()

  -- | Decidable type equality
  _≟T_ : (A B : Type) → Dec (A ≡ B)
  Unit ≟T Unit = yes refl
  Void ≟T Void = yes refl
  Int ≟T Int = yes refl
  Float ≟T Float = yes refl
  Str ≟T Str = yes refl
  Buffer ≟T Buffer = yes refl
  (A₁ Once.Type.* B₁) ≟T (A₂ Once.Type.* B₂) = ≟T-*-aux (A₁ ≟T A₂) (B₁ ≟T B₂)
  (A₁ Once.Type.+ B₁) ≟T (A₂ Once.Type.+ B₂) = ≟T-+-aux (A₁ ≟T A₂) (B₁ ≟T B₂)
  (A₁ ⇒[ k₁ ] B₁) ≟T (A₂ ⇒[ k₂ ] B₂) = ≟T-⇒-aux (A₁ ≟T A₂) (k₁ ≟k k₂) (B₁ ≟T B₂)
  -- OCP-0003: Fix removed
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- All other combinations are unequal
  Unit ≟T Void = no λ ()
  Unit ≟T Int = no λ ()
  Unit ≟T Float = no λ ()
  Unit ≟T Str = no λ ()
  Unit ≟T Buffer = no λ ()
  Unit ≟T (_ Once.Type.* _) = no λ ()
  Unit ≟T (_ Once.Type.+ _) = no λ ()
  Unit ≟T (_ ⇒[ _ ] _) = no λ ()
  Void ≟T Unit = no λ ()
  Void ≟T Int = no λ ()
  Void ≟T Float = no λ ()
  Void ≟T Str = no λ ()
  Void ≟T Buffer = no λ ()
  Void ≟T (_ Once.Type.* _) = no λ ()
  Void ≟T (_ Once.Type.+ _) = no λ ()
  Void ≟T (_ ⇒[ _ ] _) = no λ ()
  Int ≟T Unit = no λ ()
  Int ≟T Void = no λ ()
  Int ≟T Float = no λ ()
  Int ≟T Str = no λ ()
  Int ≟T Buffer = no λ ()
  Int ≟T (_ Once.Type.* _) = no λ ()
  Int ≟T (_ Once.Type.+ _) = no λ ()
  Int ≟T (_ ⇒[ _ ] _) = no λ ()
  Float ≟T Unit = no λ ()
  Float ≟T Void = no λ ()
  Float ≟T Int = no λ ()
  Float ≟T Str = no λ ()
  Float ≟T Buffer = no λ ()
  Float ≟T (_ Once.Type.* _) = no λ ()
  Float ≟T (_ Once.Type.+ _) = no λ ()
  Float ≟T (_ ⇒[ _ ] _) = no λ ()
  Str ≟T Unit = no λ ()
  Str ≟T Void = no λ ()
  Str ≟T Int = no λ ()
  Str ≟T Float = no λ ()
  Str ≟T Buffer = no λ ()
  Str ≟T (_ Once.Type.* _) = no λ ()
  Str ≟T (_ Once.Type.+ _) = no λ ()
  Str ≟T (_ ⇒[ _ ] _) = no λ ()
  Buffer ≟T Unit = no λ ()
  Buffer ≟T Void = no λ ()
  Buffer ≟T Int = no λ ()
  Buffer ≟T Float = no λ ()
  Buffer ≟T Str = no λ ()
  Buffer ≟T (_ Once.Type.* _) = no λ ()
  Buffer ≟T (_ Once.Type.+ _) = no λ ()
  Buffer ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.* _) ≟T Unit = no λ ()
  (_ Once.Type.* _) ≟T Void = no λ ()
  (_ Once.Type.* _) ≟T Int = no λ ()
  (_ Once.Type.* _) ≟T Float = no λ ()
  (_ Once.Type.* _) ≟T Str = no λ ()
  (_ Once.Type.* _) ≟T Buffer = no λ ()
  (_ Once.Type.* _) ≟T (_ Once.Type.+ _) = no λ ()
  (_ Once.Type.* _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.+ _) ≟T Unit = no λ ()
  (_ Once.Type.+ _) ≟T Void = no λ ()
  (_ Once.Type.+ _) ≟T Int = no λ ()
  (_ Once.Type.+ _) ≟T Float = no λ ()
  (_ Once.Type.+ _) ≟T Str = no λ ()
  (_ Once.Type.+ _) ≟T Buffer = no λ ()
  (_ Once.Type.+ _) ≟T (_ Once.Type.* _) = no λ ()
  (_ Once.Type.+ _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ ⇒[ _ ] _) ≟T Unit = no λ ()
  (_ ⇒[ _ ] _) ≟T Void = no λ ()
  (_ ⇒[ _ ] _) ≟T Int = no λ ()
  (_ ⇒[ _ ] _) ≟T Float = no λ ()
  (_ ⇒[ _ ] _) ≟T Str = no λ ()
  (_ ⇒[ _ ] _) ≟T Buffer = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.* _) = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.+ _) = no λ ()
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- OCP-0003: μ-type and ν-type cases
  (μ-type F₁) ≟T (μ-type F₂) = ≟T-μ-aux (F₁ ≟F F₂)
  (ν-type F₁) ≟T (ν-type F₂) = ≟T-ν-aux (F₁ ≟F F₂)
  μ-type _ ≟T Unit = no λ ()
  μ-type _ ≟T Void = no λ ()
  μ-type _ ≟T Int = no λ ()
  μ-type _ ≟T Float = no λ ()
  μ-type _ ≟T Str = no λ ()
  μ-type _ ≟T Buffer = no λ ()
  μ-type _ ≟T (_ Once.Type.* _) = no λ ()
  μ-type _ ≟T (_ Once.Type.+ _) = no λ ()
  μ-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  μ-type _ ≟T ν-type _ = no λ ()
  ν-type _ ≟T Unit = no λ ()
  ν-type _ ≟T Void = no λ ()
  ν-type _ ≟T Int = no λ ()
  ν-type _ ≟T Float = no λ ()
  ν-type _ ≟T Str = no λ ()
  ν-type _ ≟T Buffer = no λ ()
  ν-type _ ≟T (_ Once.Type.* _) = no λ ()
  ν-type _ ≟T (_ Once.Type.+ _) = no λ ()
  ν-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  ν-type _ ≟T μ-type _ = no λ ()
  Unit ≟T μ-type _ = no λ ()
  Unit ≟T ν-type _ = no λ ()
  Void ≟T μ-type _ = no λ ()
  Void ≟T ν-type _ = no λ ()
  Int ≟T μ-type _ = no λ ()
  Int ≟T ν-type _ = no λ ()
  Float ≟T μ-type _ = no λ ()
  Float ≟T ν-type _ = no λ ()
  Str ≟T μ-type _ = no λ ()
  Str ≟T ν-type _ = no λ ()
  Buffer ≟T μ-type _ = no λ ()
  Buffer ≟T ν-type _ = no λ ()
  (_ Once.Type.* _) ≟T μ-type _ = no λ ()
  (_ Once.Type.* _) ≟T ν-type _ = no λ ()
  (_ Once.Type.+ _) ≟T μ-type _ = no λ ()
  (_ Once.Type.+ _) ≟T ν-type _ = no λ ()
  (_ ⇒[ _ ] _) ≟T μ-type _ = no λ ()
  (_ ⇒[ _ ] _) ≟T ν-type _ = no λ ()
  -- GuardedT removed: productivity follows from IR totality
  -- TVar removed from Type; now in PolyType (see Once.Type)

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
data InferElabResult {n : ℕ} (Δ : SCtx n) : Set where
  success : (A : Type) (Ψ : Surface.Usage n) → SExpr Δ Ψ A
          → (depth : ℕ) → (fresh : ℕ)
          → InferElabResult Δ
  failure : TypeError → InferElabResult Δ

-- | Result of type checking (verify against expected type)
data CheckElabResult {n : ℕ} (Δ : SCtx n) (A : Type) : Set where
  success : (Ψ : Surface.Usage n) → SExpr Δ Ψ A
          → (depth : ℕ) → (fresh : ℕ)
          → CheckElabResult Δ A
  failure : TypeError → CheckElabResult Δ A

------------------------------------------------------------------------
-- Plan 0.4 T0 Option B (verified elaborator)
--
-- The intended typing for an inference result. `success` carries a
-- proof that the surface judgment holds; `failure` carries no
-- obligation (`⊤`). Pairing `inferElab`'s result with `soundOf` in a
-- `Σ` makes soundness a clause-level invariant the type checker
-- enforces — there is no separate `infer-sound` proof to drift out
-- of sync.
------------------------------------------------------------------------

open import Data.Unit using (⊤; tt) public

-- Soundness witness type. `success` carries an infer-mode judgment;
-- `failure` carries no obligation. The verified elaborator's `Σ`
-- result couples each `inferElab` clause with this witness directly.
-- | WHICH literal, if any, is this unary minus applied to? (`RInt`: plan 0.74
-- J6 step 3, D120. `RFloat`: plan 0.73 F3.)
--
-- Indexed by `e`, so matching `nov-int n` rewrites `e` to `Raw.RInt n` and the
-- dispatch can build `t-neg (t-int n)` — the same refinement the earlier
-- `Maybe (Σ ℤ (λ n → e ≡ Raw.RInt n))` carried by hand.
--
-- ONE view, not two `Maybe`s. Two would make every downstream proof split on a
-- four-cell matrix whose fourth cell — `e` both an `RInt` and an `RFloat` —
-- cannot occur, with nothing in the types saying so. Three constructors, three
-- cases, no absurd cell.
--
-- `RawExpr` is a plain datatype, so the catch-all is safe: it reduces for every
-- concrete head, and the caller never matches on `e`. (Non-exact under
-- `--exact-split`, as its `isRIntView` predecessor was; see the census target.)
data NegOperandView : RawExpr → Set where
  nov-int   : (n : ℤ)       → NegOperandView (Raw.RInt n)
  nov-float : (i f l p : ℕ) → NegOperandView (Raw.RFloat i f l p)
  nov-other : (e : RawExpr) → NegOperandView e

negOperandView : (e : RawExpr) → NegOperandView e
negOperandView (Raw.RInt n)         = nov-int n
negOperandView (Raw.RFloat i f l p) = nov-float i f l p
negOperandView e                    = nov-other e

soundOf : (ctx : NamedCtx) (e : RawExpr)
        → InferElabResult (NamedCtx.debruijn ctx) → Set
soundOf ctx e (success A Ψ eE d f) = ctx ⊢ᵢ e ∶ A ⨾ Ψ
soundOf ctx e (failure _) = ⊤

VerifiedInferResult : (ctx : NamedCtx) (e : RawExpr) → Set
VerifiedInferResult ctx e =
  ∃-syntax (λ r → soundOf ctx e r)

-- Check-mode dual: success carries a check-mode judgment.
checkSoundOf : (ctx : NamedCtx) (e : RawExpr) (T : Type)
             → CheckElabResult (NamedCtx.debruijn ctx) T → Set
checkSoundOf ctx e T (success Ψ eE d f) = ctx ⊢ᶜ e ∶ T ⨾ Ψ
checkSoundOf ctx e T (failure _) = ⊤

VerifiedCheckResult : (ctx : NamedCtx) (e : RawExpr) (T : Type) → Set
VerifiedCheckResult ctx e T =
  ∃-syntax (λ r → checkSoundOf ctx e T r)

-- The universal "infer-then-check" combinator (Plan 0.52 M1). Given the expected
-- check type `T` and the result of inferring `e` (`VerifiedInferResult`):
--   * inferred type matches `T`              → `t-embed`;
--   * `T` is the eff arrow of the inferred pure arrow (pure ⊑ eff SUBSUMPTION,
--     D068) → `t-subsume (t-embed w)` (se = `arr' eE`, identity denotation);
--   * otherwise                              → type mismatch.
-- Non-recursive (consumes an already-built infer witness), so no impact on the
-- `checkElabV`/`inferElabV` termination. Every check-mode "fall back to infer"
-- site (the generic catch-all + the `bbc-*` builtin auxes) routes through here,
-- so subsumption is uniform and `check-complete` has a single bridge.
-- The `T ≟T T'` = no recovery: pure ⊑ eff subsumption when `T` is an eff arrow
-- and the inferred `T'` is the matching pure arrow. Matched on the inferred `T'`
-- (concrete at most sites) FIRST, so a non-arrow `T'` (e.g. `Str`) fails without
-- splitting an abstract expected `T` (which would get stuck). Top-level so the
-- generic catch-all can inline `with T ≟T T'` (keeping that decision visible to
-- the agreement proofs) while still sharing this subsumption tail.
-- NOTE arg order: the inferred `T'` comes BEFORE the expected `T`, so Agda
-- splits the (concrete) `T'` first — a non-arrow `T'` hits the catch-all without
-- ever forcing a split of an abstract `T`.
-- Plan 0.52: a VIEW classifying whether a target is a Many-eff arrow. Lets the
-- argdriven dispatch (and its agreement proof) branch pure⊑eff uniformly for an
-- abstract `T` (OCP-0008: a view, not a stuck type-shape match / T-enumeration).
data EffArrowView : Type → Set where
  eav-eff   : (A B : Type) → EffArrowView (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
  eav-other : (T : Type) → EffArrowView T
classifyEffArrow : (T : Type) → EffArrowView T
classifyEffArrow (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) = eav-eff A B
classifyEffArrow T = eav-other T

-- ARGUMENT ORDER: the EXPECTED type `T` comes first, and it is the one every
-- clause discriminates on. With the inferred `T'` first, the subsumption clause
-- went stuck whenever `T'` was a variable — which hid every clause below it, so
-- a proof holding an ABSTRACT inferred type could not reduce this at all.
embedOrSubsume-no : ∀ (ctx : NamedCtx) (e : RawExpr)
                      {Ψ : Surface.Usage (NamedCtx.size ctx)} (T T' : Type)
                  → SExpr (NamedCtx.debruijn ctx) Ψ T' → (depth fresh : ℕ)
                  → ctx ⊢ᵢ e ∶ T' ⨾ Ψ → VerifiedCheckResult ctx e T
embedOrSubsume-no ctx e (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
                        (A' Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B')
                        eE depth fresh w with A ≟T A' | B ≟T B'
... | yes refl | yes refl = success _ (Surface.arr' eE) depth fresh , t-subsume (t-embed w)
-- D127: and when it is NOT a subsume, it is a type error. There is no lift to
-- fall through to any more — a value used where an arrow is expected is
-- written `\_ -> v`.
... | _        | _        =
      failure (TypeMismatch (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
                            (A' Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B')) , tt
-- D126: THE CLOSED-EXPRESSION LIFT. The expected type is a PURE arrow and the
-- expression infers at its codomain using no local variable, so it is a global
-- element and lifts to the constant morphism — which is what D018 decided
-- ("values with implicit lifting") and D056 spelled out ("a value `v : B` used
-- where a morphism is expected is the constant morphism `const v : Unit → B`").
--
-- Before this, `compose exit@S (1 + 1)` was `expected (Unit ω→ Int) but got
-- Int`, because `⊢ᵍ` enumerates the literal FORMS and `1 + 1` is not one of
-- them — an implementation narrower than the decision.
--
-- BOTH DECISIONS ARE ARGUMENTS, not `with`s: the codomain match and the
-- zero-usage check. Same convention as `cfm-build-gated`, and it keeps this
-- clause reducing for an abstract `e`.
embedOrSubsume-no ctx e T T' eE depth fresh w = failure (TypeMismatch T T') , tt

embedOrSubsume : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
               → VerifiedInferResult ctx e → VerifiedCheckResult ctx e T
embedOrSubsume ctx e T (failure err , _) = failure err , tt
embedOrSubsume ctx e T (success T' Ψ eE d fr , w) with T ≟T T'
... | yes refl = success Ψ eE d fr , t-embed w
... | no _     = embedOrSubsume-no ctx e T T' eE d fr w

------------------------------------------------------------------------
-- QTT Usage Helpers
------------------------------------------------------------------------

-- Import usage operations from Surface.Syntax
open Surface using (zeroUsage; singleUse; _+ᵘ_; _*ᵘ_) public

------------------------------------------------------------------------
-- Per-Builtin Body Specializers
------------------------------------------------------------------------
--
-- The 13 builtin generators have known polymorphic bodies. Rather than
-- writing a generic PolyExpr→Expr specialization walk, we produce each
-- builtin's specialized body directly given the ground type arguments.
-- This is more principled: each builtin's body is a fixed small term
-- and its specialization is a one-line function over ground types.
--
-- All return SExpr S∅ _ (closed expressions); weaken to the actual
-- context with weakenFromEmpty at the call site.

-- Plan 0.2.4.5 D2: morphism-realm spec helpers.
--
-- Each builtin's specialization is now a `lift-morphism` wrapping the
-- corresponding CCC primitive, instead of a Surface lambda body.
-- Combined with `morph-app` at the application sites (see specX-app
-- below), this routes "categorical-style" code (id, fst, snd,
-- terminal, initial, compose chains) directly to the morphism realm:
-- pure CCC compose at elaborate time, no closure record, no apply, no
-- dangling-pointer apply-chain bug.

specId : (T : Type) → SExpr S∅ Surface.zeroUsage (T ⇒ T)
specId T = Surface.lift-morphism IR.id

specFst : (A B : Type) → SExpr S∅ Surface.zeroUsage (A Once.Type.* B ⇒ A)
specFst A B = Surface.lift-morphism IR.fst

specSnd : (A B : Type) → SExpr S∅ Surface.zeroUsage (A Once.Type.* B ⇒ B)
specSnd A B = Surface.lift-morphism IR.snd

specInl : (A B : Type) → SExpr S∅ Surface.zeroUsage (A ⇒ (A Once.Type.+ B))
specInl A B = Surface.lift-morphism (IR.inl IR.Heap)

specInr : (A B : Type) → SExpr S∅ Surface.zeroUsage (B ⇒ (A Once.Type.+ B))
specInr A B = Surface.lift-morphism (IR.inr IR.Heap)

specUnitGen : SExpr S∅ Surface.zeroUsage Unit
specUnitGen = Surface.unit

-- pair : (a → b) → (a → c) → a → (b × c)
specPair : (A B C : Type)
         → SExpr S∅ Surface.zeroUsage ((A ⇒ B) ⇒ (A ⇒ C) ⇒ A ⇒ (B Once.Type.* C))
specPair A B C =
  Surface.lam Many refl (Surface.lam Many refl (Surface.lam Many refl
    (Surface.pair
      (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero))
      (Surface.app (Surface.var (suc zero)) (Surface.var zero)))))

-- terminal : a → Unit
specTerminal : (A : Type) → SExpr S∅ Surface.zeroUsage (A ⇒ Unit)
specTerminal A = Surface.lift-morphism IR.terminal

-- initial : Void → a
specInitial : (A : Type) → SExpr S∅ Surface.zeroUsage (Void ⇒ A)
specInitial A = Surface.lift-morphism IR.initial

-- curry : ((a × b) → c) → a → b → c
specCurry : (A B C : Type)
          → SExpr S∅ Surface.zeroUsage ((A Once.Type.* B ⇒ C) ⇒ A ⇒ B ⇒ C)
specCurry A B C =
  Surface.lam Many refl (Surface.lam Many refl (Surface.lam Many refl
    (Surface.app (Surface.var (suc (suc zero)))
                 (Surface.pair (Surface.var (suc zero)) (Surface.var zero)))))

-- apply : ((a → b) × a) → b
specApply : (A B : Type)
          → SExpr S∅ Surface.zeroUsage (((A ⇒ B) Once.Type.* A) ⇒ B)
specApply A B =
  Surface.lam Many refl
    (Surface.app (Surface.fst' (Surface.var zero))
                 (Surface.snd' (Surface.var zero)))

-- compose : (b → c) → (a → b) → a → c
specCompose : (A B C : Type)
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
specCase : (A B C : Type)
         → SExpr S∅ Surface.zeroUsage ((A ⇒ C) ⇒ (B ⇒ C) ⇒ (A Once.Type.+ B) ⇒ C)
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
extract-morph-aux : ∀ {n} {Γ : SCtx n} {Ψ : Surface.Usage n} {T : Type} {A B : Type}
                    {π : Once.Type.Purity}
                  → SExpr Γ Ψ T
                  → T ≡ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
                  → Maybe (∃-syntax (λ (m : IR ⌊ A ⌋ ⌊ B ⌋) → Ψ ≡ Surface.zeroUsage))
extract-morph-aux (Surface.lift-morphism m) refl = just (m , refl)
extract-morph-aux _ _ = nothing

extract-morph : ∀ {n} {Γ : SCtx n} {Ψ : Surface.Usage n} {A B : Type}
                {π : Once.Type.Purity}
              → SExpr Γ Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
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
data WellFormedFView (F : Once.Type.Functor) : Set where
  wfv-yes : ∀ {wfF} → wellFormedF? F ≡ just wfF → WellFormedFView F
  wfv-no  : wellFormedF? F ≡ nothing → WellFormedFView F

inspectWellFormedF : (F : Once.Type.Functor) → WellFormedFView F
inspectWellFormedF F with wellFormedF? F in eq
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
    head : RawExpr
    args : List RawExpr

spineOf : RawExpr → AppSpine
spineOf e = go e []
  where
    go : RawExpr → List RawExpr → AppSpine
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
    go (Raw.RFloat i f l p)    args = mkSpine (Raw.RFloat i f l p) args
    go (Raw.RStringLit s)    args = mkSpine (Raw.RStringLit s) args
    go (Raw.RAnnot e t)      args = mkSpine (Raw.RAnnot e t) args
    go (Raw.RBinOp op x y)   args = mkSpine (Raw.RBinOp op x y) args
    go (Raw.RUnaryOp op x)   args = mkSpine (Raw.RUnaryOp op x) args
    go (Raw.RAna F c)        args = mkSpine (Raw.RAna F c) args

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
matchInferResult :
  ∀ {n} {Δ : SCtx n}
  → InferElabResult Δ
  → (T : Type)
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
data FunProjection {n : ℕ} (Δ : SCtx n) : Set where
  isFun  : (A : Type) (q : Quantity) (B : Type) (Ψ : Surface.Usage n)
         → SExpr Δ Ψ (A ⇒[ mk-kind q pure ] B) → ℕ → ℕ → FunProjection Δ
  isEff  : (A B : Type) (Ψ : Surface.Usage n)
         → SExpr Δ Ψ (A ⇒[ mk-kind Many eff ] B) → ℕ → ℕ → FunProjection Δ
  notFun : TypeError → FunProjection Δ

asFun : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → FunProjection Δ
asFun (failure err)                                      = notFun err
asFun (success (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) Ψ se d f) = isFun A q B Ψ se d f
asFun (success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) Ψ se d f)                       = isEff A B Ψ se d f
asFun (success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.eff ] B) _ _ _ _) = notFun (NotFunction (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.eff ] B))
asFun (success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.eff ] B) _ _ _ _) = notFun (NotFunction (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.eff ] B))
asFun (success Unit Ψ _ _ _)                             = notFun (NotFunction Unit)
asFun (success Void Ψ _ _ _)                             = notFun (NotFunction Void)
asFun (success Int Ψ _ _ _)                              = notFun (NotFunction Int)
asFun (success Float Ψ _ _ _)                            = notFun (NotFunction Float)
asFun (success Str Ψ _ _ _)                              = notFun (NotFunction Str)
asFun (success Buffer Ψ _ _ _)                           = notFun (NotFunction Buffer)
asFun (success (A Once.Type.* B) _ _ _ _)                = notFun (NotFunction (A Once.Type.* B))
asFun (success (A Once.Type.+ B) _ _ _ _)                = notFun (NotFunction (A Once.Type.+ B))
asFun (success (μ-type F) _ _ _ _)                       = notFun (NotFunction (μ-type F))
asFun (success (ν-type F) _ _ _ _)                       = notFun (NotFunction (ν-type F))

data IntProjection {n : ℕ} (Δ : SCtx n) : Set where
  isInt  : (Ψ : Surface.Usage n) → SExpr Δ Ψ Int → ℕ → ℕ → IntProjection Δ
  notInt : TypeError → IntProjection Δ

-- | `asInt` emits `TypeMismatch Int actual` for the non-Int success
-- cases (since semantically: expected Int, got `actual`).
asInt : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → IntProjection Δ
asInt (failure err)                                      = notInt err
asInt (success Int Ψ se d f)                             = isInt Ψ se d f
asInt (success Unit _ _ _ _)                             = notInt (TypeMismatch Int Unit)
asInt (success Void _ _ _ _)                             = notInt (TypeMismatch Int Void)
asInt (success Float _ _ _ _)                            = notInt (TypeMismatch Int Float)
asInt (success Str _ _ _ _)                              = notInt (TypeMismatch Int Str)
asInt (success Buffer _ _ _ _)                           = notInt (TypeMismatch Int Buffer)
asInt (success (A Once.Type.* B) _ _ _ _)                = notInt (TypeMismatch Int (A Once.Type.* B))
asInt (success (A Once.Type.+ B) _ _ _ _)                = notInt (TypeMismatch Int (A Once.Type.+ B))
asInt (success (A ⇒[ k ] B) _ _ _ _)                     = notInt (TypeMismatch Int (A ⇒[ k ] B))
asInt (success (μ-type F) _ _ _ _)                       = notInt (TypeMismatch Int (μ-type F))
asInt (success (ν-type F) _ _ _ _)                       = notInt (TypeMismatch Int (ν-type F))

-- | NOT NUMERIC — neither `Int` nor `Float` — with the error the elaborator
-- wraps in that case (plan 0.75 F4).
--
-- `asInt` can no longer stand in for this. It answers `notInt` on a `Float`,
-- and a `Float` operand is now a perfectly good binop operand: `1.5 + "x"`
-- reports `BinOpRightError (TypeMismatch Float Str)`, NOT
-- `BinOpLeftError (TypeMismatch Int Float)`. The error-shape lemmas were
-- stated over `asInt`'s failure and became FALSE at exactly that type, so they
-- move to this projection, which is the hypothesis they always meant: the left
-- operand is not a number at all.
--
-- The errors are `asInt`'s verbatim, so no message changes.
notNumeric : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → Maybe TypeError
notNumeric (failure err)                                 = just err
notNumeric (success Int _ _ _ _)                         = nothing
notNumeric (success Once.Type.Float _ _ _ _)             = nothing
notNumeric (success Unit _ _ _ _)                        = just (TypeMismatch Int Unit)
notNumeric (success Void _ _ _ _)                        = just (TypeMismatch Int Void)
notNumeric (success Str _ _ _ _)                         = just (TypeMismatch Int Str)
notNumeric (success Buffer _ _ _ _)                      = just (TypeMismatch Int Buffer)
notNumeric (success (A Once.Type.* B) _ _ _ _)           = just (TypeMismatch Int (A Once.Type.* B))
notNumeric (success (A Once.Type.+ B) _ _ _ _)           = just (TypeMismatch Int (A Once.Type.+ B))
notNumeric (success (A ⇒[ k ] B) _ _ _ _)                = just (TypeMismatch Int (A ⇒[ k ] B))
notNumeric (success (μ-type F) _ _ _ _)                  = just (TypeMismatch Int (μ-type F))
notNumeric (success (ν-type F) _ _ _ _)                  = just (TypeMismatch Int (ν-type F))

------------------------------------------------------------------------
-- Decide-with-proof helpers
------------------------------------------------------------------------

-- | Decide `q' ≤q q`, returning the propositional proof on success.
--
-- This is the Bool-decision packaged with its equality witness, as
-- the `just`/`nothing` distinction. The elaborator uses this in the
-- lambda case where the `Surface.lam` constructor requires a proof
-- `(q' ≤q q) ≡ true`. Using this helper (instead of stdlib's
-- `with q' ≤q q | inspect (q' ≤q_) q`) avoids producing an opaque
-- internal `with`-function that downstream proofs cannot unify with.
-- See `docs/formal/historical/lessons-learned.md` § "`with` patterns
-- block computation" for background.
-- | Pattern-match directly on the two quantities rather than on
-- the Bool `q' ≤q q` to keep the definition transparent to external
-- reduction (no opaque internal `with`-helper).
decideLeq : (q' q : Quantity) → Maybe ((q' ≤q q) ≡ true)
decideLeq Zero Zero = just refl
decideLeq Zero One  = just refl
decideLeq Zero Many = just refl
decideLeq One  Zero = nothing
decideLeq One  One  = just refl
decideLeq One  Many = just refl
decideLeq Many Zero = nothing
decideLeq Many One  = nothing
decideLeq Many Many = just refl


-- composeArgB moved to Once.TypeCheck.Classify (so Judgment can
-- reference it as a t-compose-check premise).

------------------------------------------------------------------------
-- Bare polymorphic-builtin classifier (plan 0.6 Phase C.7)
------------------------------------------------------------------------
-- Used by `checkElab-RVar` to dispatch specialised check-mode clauses
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

inferElab-RApp-id : (ctx : NamedCtx)
                  → InferElabResult (NamedCtx.debruijn ctx)
                  → InferElabResult (NamedCtx.debruijn ctx)
inferElab-RApp-id ctx (failure err) = failure err
inferElab-RApp-id ctx (success T Ψ argE d f') =
  success T _ (Surface.morph-app IR.id argE) (suc d) f'

------------------------------------------------------------------------
-- Bidirectional Inference (produces usage-indexed Expr)
------------------------------------------------------------------------

-- Plan 0.6.2 Phase 4: two-phase architecture. Phase 1 (this mutual
-- block) is purely structural on `RawExpr` — at user-polymorphic
-- references, it emits a `Surface.poly x T` placeholder rather than
-- recursing into the def's body. Phase 2 (`resolveExpr` below)
-- tree-walks the emitted Expr and splices bodies at `poly` nodes,
-- well-founded on `length polys`.
------------------------------------------------------------------------
-- Plan 0.4 T0 Option B — postulates referenced by the merged
-- mutual block. Placed BEFORE the block so V bodies inside can see
-- them.
------------------------------------------------------------------------

postulate
  -- Witness for the `bbc-other` poly-instantiate case (Phase 2 gap).
  bbc-other-poly-witness :
    ∀ (ctx : NamedCtx) (x : String) (T : Type)
    → ctx ⊢ᶜ Raw.RVar x ∶ T ⨾ Surface.zeroUsage
  -- Plan 0.58 / D071: infer-mode twin (Phase 2 gap, premise-erased instance of
  -- `t-var-poly-instantiate-infer` — the premises hold at the emission site;
  -- the body derivation is the Phase-2 invariant, same as the check witness).
  bbc-other-poly-infer-witness :
    ∀ (ctx : NamedCtx) (x : String) (T : Type)
    → ctx ⊢ᵢ Raw.RVar x ∶ T ⨾ Surface.zeroUsage

------------------------------------------------------------------------
-- Plan 0.58 / D071: infer-mode ground telescope reference (the poly fallback
-- of `inferElabV` for a bare `RVar`).
--
-- After the local and import lookups fail, a bare `bbc-other` name may still
-- be an own-module telescope def (`lookupPoly`). A GROUND schema has exactly
-- one type, so the reference INFERS at its declaration (`extractGround`) —
-- emitting the same `Surface.poly` placeholder Phase 2 (`resolveExpr`)
-- splices. A NON-ground schema stays check-mode-only
-- (`t-var-poly-instantiate`), so infer still fails with `UnboundVariable`.
--
-- De-withed (classify / lookup / isGround as explicit args + equations), so
-- external proofs reduce each stage J-style ([[de-with pattern]]).
------------------------------------------------------------------------

inferElabV-RVar-poly-ground-aux :
  ∀ (ctx : NamedCtx) (x : String) (schema : PolyType)
  → (ig : (Ground schema) ⊎ ⊤) → isGround schema ≡ ig
  → VerifiedInferResult ctx (Raw.RVar x)
inferElabV-RVar-poly-ground-aux ctx x schema (inj₂ tt) _ =
  failure (UnboundVariable x) , tt
inferElabV-RVar-poly-ground-aux ctx x schema (inj₁ g) _ =
  success (extractGround schema g) Surface.zeroUsage
          (Surface.poly x (extractGround schema g)) 0 (NamedCtx.freshCounter ctx)
  , bbc-other-poly-infer-witness ctx x (extractGround schema g)

inferElabV-RVar-poly-lookup-aux :
  ∀ (ctx : NamedCtx) (x : String)
  → (lp : Maybe (PolyType × RawExpr)) → lookupPoly (NamedCtx.polys ctx) x ≡ lp
  → VerifiedInferResult ctx (Raw.RVar x)
inferElabV-RVar-poly-lookup-aux ctx x nothing _ = failure (UnboundVariable x) , tt
inferElabV-RVar-poly-lookup-aux ctx x (just (schema , body)) _ =
  inferElabV-RVar-poly-ground-aux ctx x schema (isGround schema) refl

inferElabV-RVar-poly-aux :
  ∀ (ctx : NamedCtx) (x : String)
  → (cls : BareBuiltinClass x) → classifyBareBuiltin x ≡ cls
  → VerifiedInferResult ctx (Raw.RVar x)
inferElabV-RVar-poly-aux ctx x bbc-other    _ =
  inferElabV-RVar-poly-lookup-aux ctx x (lookupPoly (NamedCtx.polys ctx) x) refl
inferElabV-RVar-poly-aux ctx x bbc-id       _ = failure (UnboundVariable x) , tt
inferElabV-RVar-poly-aux ctx x bbc-fst      _ = failure (UnboundVariable x) , tt
inferElabV-RVar-poly-aux ctx x bbc-snd      _ = failure (UnboundVariable x) , tt
inferElabV-RVar-poly-aux ctx x bbc-terminal _ = failure (UnboundVariable x) , tt
inferElabV-RVar-poly-aux ctx x bbc-initial  _ = failure (UnboundVariable x) , tt
inferElabV-RVar-poly-aux ctx x bbc-inl      _ = failure (UnboundVariable x) , tt
inferElabV-RVar-poly-aux ctx x bbc-inr      _ = failure (UnboundVariable x) , tt


mutual
  inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
  checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
  -- RVar dispatch helper (plan 0.6 Phase C.7 POC-1). Separates
  -- specialised bare-builtin handling from the generic lookup path.
  checkElab-RVar : (ctx : NamedCtx) → (x : String) → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
  -- Pair classifier helper (plan 0.6 Phase C.7 POC-2). Checks a
  -- 2-arg `pair f g` expression in check mode against the canonical
  -- `A ⇒[Many] (B * C)` shape.
  checkPair : (ctx : NamedCtx) → (pairHead arg : RawExpr) → (T : Type)
            → VerifiedCheckResult ctx (Raw.RApp pairHead arg) T
  -- Plan 0.36 Phase 2a follow-up: check-mode for the pair LITERAL
  -- `(a , b)` at a product type — checks components bidirectionally.
  checkPairLit : (ctx : NamedCtx) → (a b : RawExpr) → (A B : Type)
               → VerifiedCheckResult ctx (Raw.RPair a b) (A Once.Type.* B)
  -- Case (copair) classifier helper (Plan 0.28 Commit 1). Checks a
  -- 2-arg `case f g` expression in check mode against the canonical
  -- `(A + B) ⇒[Many] C` shape.
  checkCase : (ctx : NamedCtx) → (caseHead arg : RawExpr) → (T : Type)
            → VerifiedCheckResult ctx (Raw.RApp caseHead arg) T
  -- Argument-driven helper (mirror of `checkComposeGo`): the arm-checking core
  -- of `case`, parameterised by the copair domains A B, codomain C, and grade π.
  -- Extracting it lets the eff-subsumption clause of `checkCase` call it at two
  -- grades (try eff; else pure + arr'/t-subsume) without duplicating the body.
  checkCaseGo : (ctx : NamedCtx) (f g : RawExpr) (A B C : Type) (π : Once.Type.Purity)
              → VerifiedCheckResult ctx
                  (Raw.RApp (Raw.RApp (Raw.RResolved (gen "case")) f) g)
                  ((A Once.Type.+ B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  -- Compose / curry / apply classifier helpers (plan 0.6 Phase C.7
  -- POC-3).
  checkCompose : (ctx : NamedCtx) → (composeHead arg : RawExpr) → (T : Type)
               → VerifiedCheckResult ctx (Raw.RApp composeHead arg) T
  -- Argument-driven helper: takes `composeMid`'s result + the equation
  -- explicitly (no `with … in`), so the morph-complete proof can case the
  -- stuck `composeArgB` cleanly. See MorphComplete / feedback_with_abstraction.
  checkComposeGo : (ctx : NamedCtx) (f g : RawExpr) (A C : Type) (π : Once.Type.Purity)
                 → (mid : Maybe Type) → composeMid ctx f g A ≡ mid
                 → VerifiedCheckResult ctx
                     (Raw.RApp (Raw.RApp (Raw.RResolved (gen "compose")) f) g)
                     (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  checkCurry : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
             → VerifiedCheckResult ctx (Raw.RApp (Raw.RResolved (gen "curry")) arg) T
  checkApply : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
             → VerifiedCheckResult ctx (Raw.RApp (Raw.RResolved (gen "apply")) arg) T
  -- Recursion-scheme generators (Plan 0.28 Commit 2). The `…Go`/`…A/B/C`
  -- helpers take each decidable result as an explicit argument with its
  -- `refl` witness (no `with … in`), so the completeness fallbacks
  -- reduce them with plain nested `with | eq` — like `checkPair`.
  checkIn : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
          → VerifiedCheckResult ctx (Raw.RApp (Raw.RResolved (gen "In")) arg) T
  checkInGo : (ctx : NamedCtx) (arg : RawExpr) (F : Once.Type.Functor)
            → (mw : Maybe (Once.Functor.Translate.WellFormedF F))
            → wellFormedF? F ≡ mw
            → VerifiedCheckResult ctx (Raw.RApp (Raw.RResolved (gen "In")) arg) (Once.Type.μ-type F)
  checkCata : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
            → VerifiedCheckResult ctx (Raw.RApp (Raw.RResolved (gen "cata")) arg) T
  -- Plan 0.36 Phase 2a: dispatch on `wellFormedF? F`; the algebra is
  -- elaborated as an ordinary function in the EMPTY context (see clause).
  checkCataGo : (ctx : NamedCtx) (alg : RawExpr) (F : Once.Type.Functor) (A : Type)
                (π : Once.Type.Purity)
              → (mw : Maybe (Once.Functor.Translate.WellFormedF F)) → wellFormedF? F ≡ mw
              → VerifiedCheckResult ctx (Raw.RApp (Raw.RResolved (gen "cata")) alg)
                                        (Once.Type.μ-type F Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)

  -- Plan 0.4 T0 Option A: hoist the `ahv-other` (generic application)
  -- branch of `inferElab RApp` into its own top-level mutual member.
  -- The body is structurally identical to the previous in-place
  -- clause; the win is that `inferElab ctx (RApp f x) | ahv-other`
  -- now reduces to a *named* function call rather than to the
  -- `inferElab` case tree's anonymous with-helper. Soundness for the
  -- `ahv-other` view branch (`spec-gap-RApp-ahv-other`) can pattern-
  -- match through this helper transparently.
  inferElab-RApp-other : (ctx : NamedCtx) (f x : RawExpr) → InferElabResult (NamedCtx.debruijn ctx)

  -- Plan 0.4 T0 Option B — verified elaborator declarations.
  inferElabV : (ctx : NamedCtx) (e : RawExpr) → VerifiedInferResult ctx e
  checkElabV : (ctx : NamedCtx) (e : RawExpr) (T : Type) → VerifiedCheckResult ctx e T
  -- Plan 0.58 E1-full: the WORKER carries a well-founded `Acc` on `length polys`
  -- so the poly-reference case can resolve INLINE (re-elaborate the def body in its
  -- strictly-smaller prefix). Non-poly recursion goes through the Acc-free wrapper
  -- `checkElabV` (which re-derives a FRESH `<-wellFounded` — sound per POC-B), so the
  -- ~300 existing call sites are unchanged.
  checkElabV-wf : (ctx : NamedCtx) → Acc _<_ (length (NamedCtx.polys ctx))
                → (e : RawExpr) (T : Type) → VerifiedCheckResult ctx e T
  -- compose check-mode helper, threading the inner checkElabV results
  -- as explicit arguments + (unused) equations. The eqs are unused in
  -- the body (they're just placeholders for the J-style bridge in
  -- proofs). This lets external proofs substitute checkElab-success
  -- premises into the dispatch chain without navigating opaque
  -- `with`-helpers.
  inferElabV-RApp-other : (ctx : NamedCtx) (f x : RawExpr) → VerifiedInferResult ctx (Raw.RApp f x)
  -- RPair dispatch as a top-level aux taking the two sub-results explicitly
  -- (no inline `with` → no opaque `with`-helper → downstream proofs recurse
  -- directly; [[feedback_with_clauses_painful]]).
  inferElabV-RPair-aux : (ctx : NamedCtx) (a b : RawExpr)
    → VerifiedInferResult ctx a → VerifiedInferResult ctx b
    → VerifiedInferResult ctx (Raw.RPair a b)
  inferElabV-RAnnot-aux : (ctx : NamedCtx) (e : RawExpr) (T : Type)
    → VerifiedCheckResult ctx e T → VerifiedInferResult ctx (Raw.RAnnot e T)
  inferElabV-RUnaryOp-aux : (ctx : NamedCtx) (e : RawExpr)
    → VerifiedInferResult ctx e → VerifiedInferResult ctx (Raw.RUnaryOp Raw.OpNeg e)
  -- PLAN 0.74 J6 step 3: a minus directly on a NUMERAL is one literal, not a
  -- runtime negation of another one. Split out as a named dispatch (the
  -- file's `inferElabV-RApp-dispatch` convention) so the definitional
  -- reduction that stops holding is confined to this function.
  inferElabV-neg-dispatch : (ctx : NamedCtx) (e : RawExpr)
    → VerifiedInferResult ctx (Raw.RUnaryOp Raw.OpNeg e)
  inferElabV-neg-aux : (ctx : NamedCtx) (e : RawExpr)
    → NegOperandView e
    → VerifiedInferResult ctx (Raw.RUnaryOp Raw.OpNeg e)
  -- CHECK-mode twin of the same dispatch. A negated literal at a pure-arrow
  -- target is its constant morphism, exactly as a bare literal is; anything
  -- else falls to the generic infer-and-match the `RUnaryOp` clause used
  -- before. ONE scrutinee per aux, the `checkElabV-RInt-aux` convention.
  --
  -- EACH BRANCH IS SELF-CONTAINED — no shared `inferElabV ctx (RUnaryOp OpNeg
  -- e)` threaded in, and that is forced twice over. Once by TERMINATION: the
  -- dispatch receives the OPERAND, so rebuilding `RUnaryOp OpNeg e` inside it
  -- is growth to foetus. Once by REDUCTION: a downstream proof that has
  -- with-abstracted `negOperandView e` needs the branch body to mention only
  -- terms that still reduce under that abstraction, and
  -- `inferElabV ctx (RUnaryOp OpNeg e)` does not — it unfolds back into the
  -- view. So the literal branches state their folded result outright (they
  -- know it: the fold has no premise) and only the non-literal branch calls
  -- into inference, at the OPERAND, which is what `inferElabV-RUnaryOp-aux`
  -- takes anyway.
  checkElabV-neg-dispatch : (ctx : NamedCtx) (e : RawExpr) (T : Type)
    → NegOperandView e
    → VerifiedCheckResult ctx (Raw.RUnaryOp Raw.OpNeg e) T
  checkElabV-neg-int-aux : (ctx : NamedCtx) (n : ℤ) (T : Type)
    → VerifiedCheckResult ctx (Raw.RUnaryOp Raw.OpNeg (Raw.RInt n)) T
  checkElabV-neg-float-aux : (ctx : NamedCtx) (i f l p : ℕ) (T : Type)
    → VerifiedCheckResult ctx (Raw.RUnaryOp Raw.OpNeg (Raw.RFloat i f l p)) T
  inferElabV-RBinOp-aux : (ctx : NamedCtx) (op : Raw.BinOp) (e₁ e₂ : RawExpr)
    → VerifiedInferResult ctx e₁ → VerifiedInferResult ctx e₂
    → VerifiedInferResult ctx (Raw.RBinOp op e₁ e₂)
  -- RLet/RDestruct: the later sub-expressions live in EXTENDED contexts whose
  -- types come from the earlier sub-results, so they fold through nested auxes
  -- (each takes the prior result's data explicitly — no inline `with`).
  inferElabV-RLet-aux : (ctx : NamedCtx) (x : String) (e₁ e₂ : RawExpr)
    → VerifiedInferResult ctx e₁ → VerifiedInferResult ctx (Raw.RLet x e₁ e₂)
  inferElabV-RLet-aux2 : (ctx : NamedCtx) (x : String) (e₁ e₂ : RawExpr)
    {A : Type} {Ψ₁ : Surface.Usage (NamedCtx.size ctx)}
    (e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ A) (d₁ f₁ : ℕ)
    (w₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁)
    → VerifiedInferResult (extendNamedCtx ctx x A) e₂
    → VerifiedInferResult ctx (Raw.RLet x e₁ e₂)
  -- RDestruct de-withed into three nested auxes (one per `with` level):
  -- `-aux` dispatches the scrutinee type, `-auxL` the left branch (in `ctx,xL:A`),
  -- `-auxR` the right branch (in `ctx,xR:B`) + the branch-type match. Behaviour-
  -- preserving extraction of the old inline `with` chain so external proofs can
  -- case the dispatch without `with`-opacity.
  inferElabV-RDestruct-aux : (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr) (xR : String) (eR : RawExpr)
    → VerifiedInferResult ctx scrut
    → VerifiedInferResult ctx (Raw.RDestruct scrut xL eL xR eR)
  inferElabV-RDestruct-auxL : (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr) (xR : String) (eR : RawExpr)
    (A B : Type) {Ψs : Surface.Usage (NamedCtx.size ctx)}
    (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Type.+ B)) (ds fs : ℕ)
    (wS : ctx ⊢ᵢ scrut ∶ (A Once.Type.+ B) ⨾ Ψs)
    → VerifiedInferResult (extendNamedCtx ctx xL A) eL
    → VerifiedInferResult ctx (Raw.RDestruct scrut xL eL xR eR)
  inferElabV-RDestruct-auxR : (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr) (xR : String) (eR : RawExpr)
    (A B : Type) {Ψs : Surface.Usage (NamedCtx.size ctx)}
    (scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Type.+ B)) (ds fs : ℕ)
    (wS : ctx ⊢ᵢ scrut ∶ (A Once.Type.+ B) ⨾ Ψs)
    {C₁ : Type} {qℓ : _} {Ψₗ : Surface.Usage (NamedCtx.size ctx)}
    (eLE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xL A)) (qℓ ∷ᵘ Ψₗ) C₁) (dL fL : ℕ)
    (wL : (extendNamedCtx ctx xL A) ⊢ᵢ eL ∶ C₁ ⨾ (qℓ ∷ᵘ Ψₗ))
    → VerifiedInferResult (extendNamedCtx ctx xR B) eR
    → VerifiedInferResult ctx (Raw.RDestruct scrut xL eL xR eR)
  -- Aux helpers that take the lookup result + equation as explicit args,
  -- so external proofs can pattern-match on the Maybe and supply the eq
  -- without `with...in` opacity.
  inferElabV-RQualified-aux :
    ∀ (ctx : NamedCtx) (name alias : String) (lhs : Maybe Type)
    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs
    → VerifiedInferResult ctx (Raw.RQualified name alias)
  -- Plan 0.50: resolved-ref lookup, keyed by the canonical dotted path.
  inferElabV-RResolved-aux :
    ∀ (ctx : NamedCtx) (cn : CanonicalName) → NotGenerator cn → (lhs : Maybe Type)
    → lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ lhs
    → VerifiedInferResult ctx (Raw.RResolved cn)
  -- Plan 0.58: the arrow-value case DE-WITHES the concreteness decision
  -- (`isBaseType? A`/`isConcrete? B`) into explicit Maybe args + equations, so
  -- the Completeness proof can drive it to the `success` branch (mirroring the
  -- lookup de-with above). Without this the `with` is opaque to external proofs.
  inferElabV-RQualified-arrow-aux :
    ∀ (ctx : NamedCtx) (name alias : String) {A B : Type} {π : Once.Type.Purity}
    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)
        ≡ just (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
    → (mbA : Maybe (IsBaseType A)) → isBaseType? A ≡ mbA
    → (mcB : Maybe (IsConcrete B)) → isConcrete? B ≡ mcB
    → VerifiedInferResult ctx (Raw.RQualified name alias)
  inferElabV-RResolved-arrow-aux :
    ∀ (ctx : NamedCtx) (cn : CanonicalName) → NotGenerator cn → ∀ {A B : Type} {π : Once.Type.Purity}
    → lookupImport (NamedCtx.imports ctx) (showCanonical cn)
        ≡ just (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
    → (mbA : Maybe (IsBaseType A)) → isBaseType? A ≡ mbA
    → (mcB : Maybe (IsConcrete B)) → isConcrete? B ≡ mcB
    → VerifiedInferResult ctx (Raw.RResolved cn)
  -- Non-arrow-Many value refs: DE-WITH the single `isConcrete? ty` decision.
  inferElabV-RQualified-value-aux :
    ∀ (ctx : NamedCtx) (name alias : String) (ty : Type)
    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just ty
    → (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc
    → VerifiedInferResult ctx (Raw.RQualified name alias)
  inferElabV-RResolved-value-aux :
    ∀ (ctx : NamedCtx) (cn : CanonicalName) → NotGenerator cn → ∀ (ty : Type)
    → lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just ty
    → (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc
    → VerifiedInferResult ctx (Raw.RResolved cn)
  inferElabV-RVar-lookup-aux :
    ∀ (ctx : NamedCtx) (x : String)
    → (locLhs : Maybe (∃[ A ] ∃[ Ψ ] (Surface.SVar (NamedCtx.debruijn ctx) Ψ A)))
    → lookupLocal ctx x ≡ locLhs
    → (impLhs : Maybe Type)
    → lookupImport (NamedCtx.imports ctx) x ≡ impLhs
    → VerifiedInferResult ctx (Raw.RVar x)
  -- Plan 0.58: DE-WITH the import-value concreteness decision.
  -- D136: the reserved-word decision is DE-WITHED like the concreteness one,
  -- because it is what discharges `t-var-import`'s `¬ GenWord x`. A reserved
  -- word in the import table is unreachable bare (write `x@this`), so it
  -- reports the same `UnboundVariable` a missing name would.
  inferElabV-RVar-import-value-aux :
    ∀ (ctx : NamedCtx) (x : String)
    → lookupLocal ctx x ≡ nothing
    → (ty : Type) → lookupImport (NamedCtx.imports ctx) x ≡ just ty
    → (gw : Dec (GenWord x)) → genWord? x ≡ gw
    → (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc
    → VerifiedInferResult ctx (Raw.RVar x)
  inferElabV-RApp-other-aux :
    ∀ (ctx : NamedCtx) (f x : RawExpr) (lhs : Maybe PolyBuiltinApp)
    → classifyAppHead f ≡ lhs
    → VerifiedInferResult ctx (Raw.RApp f x)
  inferElabV-RApp-dispatch :
    ∀ (ctx : NamedCtx) (f arg : RawExpr) (vw : AppHeadView f)
    → classifyAppHeadView f ≡ vw
    → VerifiedInferResult ctx (Raw.RApp f arg)
  checkElabV-RApp-dispatch :
    ∀ (ctx : NamedCtx) (f arg : RawExpr) (T : Type) (vw : AppHeadView f)
    → classifyAppHeadView f ≡ vw
    → VerifiedCheckResult ctx (Raw.RApp f arg) T
  -- Arg-driven application fallback (the `ahv-other` failure branch), factored
  -- out so the `classifyAppHead f` split rides EXPLICIT `lhs`/`eqAH` arguments
  -- (no inline `with … in`); this lets the agreement proof mirror it with a
  -- companion aux, exactly like `inferElabV-RApp-other-aux`.
  checkElabV-RApp-other-argdriven-aux :
    ∀ (ctx : NamedCtx) (f arg : RawExpr) (T : Type) (errInfer : TypeError)
      (lhs : Maybe PolyBuiltinApp) → classifyAppHead f ≡ lhs
    → VerifiedCheckResult ctx (Raw.RApp f arg) T
  -- Plan 0.4 T2: bbc-X failure-branch aux helpers. Each is hardcoded
  -- to its builtin name (forced by the `bbc-X` constructor at the call
  -- site). Takes lookupLocal/lookupImport results + equations as
  -- explicit args (eliminating `with...in eq-loc/eq-imp` opacity).
  -- Returns success at the canonical builtin type if all conditions
  -- match, failure otherwise.
  checkElabV-RVar-bbc-id-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → VerifiedCheckResult ctx (Raw.RResolved (gen "id")) T
  checkElabV-RVar-bbc-fst-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → VerifiedCheckResult ctx (Raw.RResolved (gen "fst")) T
  checkElabV-RVar-bbc-snd-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → VerifiedCheckResult ctx (Raw.RResolved (gen "snd")) T
  checkElabV-RVar-bbc-terminal-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → VerifiedCheckResult ctx (Raw.RResolved (gen "terminal")) T
  checkElabV-RVar-bbc-initial-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → VerifiedCheckResult ctx (Raw.RResolved (gen "initial")) T
  checkElabV-RVar-bbc-inl-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → VerifiedCheckResult ctx (Raw.RResolved (gen "inl")) T
  checkElabV-RVar-bbc-inr-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → VerifiedCheckResult ctx (Raw.RResolved (gen "inr")) T
  -- Per-bbc-X aux taking the inferElab result explicitly. Eliminates
  -- the inner with-helper opacity. Each bbc-X's success-via-infer path
  -- uses t-embed; the failure path delegates to bbc-X-failure-aux.
  checkElabV-RVar-bbc-id-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RResolved (gen "id"))
    → VerifiedCheckResult ctx (Raw.RResolved (gen "id")) T
  checkElabV-RVar-bbc-fst-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RResolved (gen "fst"))
    → VerifiedCheckResult ctx (Raw.RResolved (gen "fst")) T
  checkElabV-RVar-bbc-snd-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RResolved (gen "snd"))
    → VerifiedCheckResult ctx (Raw.RResolved (gen "snd")) T
  checkElabV-RVar-bbc-terminal-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RResolved (gen "terminal"))
    → VerifiedCheckResult ctx (Raw.RResolved (gen "terminal")) T
  checkElabV-RVar-bbc-initial-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RResolved (gen "initial"))
    → VerifiedCheckResult ctx (Raw.RResolved (gen "initial")) T
  checkElabV-RVar-bbc-inl-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RResolved (gen "inl"))
    → VerifiedCheckResult ctx (Raw.RResolved (gen "inl")) T
  checkElabV-RVar-bbc-inr-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RResolved (gen "inr"))
    → VerifiedCheckResult ctx (Raw.RResolved (gen "inr")) T
  -- D136 dispatchers. View + its defining equation, so a caller can recover
  -- `classifyGen cn ≡ gv` after a `with`-match (the `viewBundle` idiom).
  inferElabV-RResolved-dispatch :
    ∀ (ctx : NamedCtx) (cn : CanonicalName) → GenView cn
    → VerifiedInferResult ctx (Raw.RResolved cn)
  checkElabV-RResolved-dispatch :
    ∀ (ctx : NamedCtx) (cn : CanonicalName) (T : Type) → GenView cn
    → VerifiedInferResult ctx (Raw.RResolved cn)
    → VerifiedCheckResult ctx (Raw.RResolved cn) T

  checkElabV-RVar-bbc-other-aux :
    ∀ (ctx : NamedCtx) (x : String) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar x)
    → VerifiedCheckResult ctx (Raw.RVar x) T
  -- D127: NO value-lift dispatch. A literal has ONE meaning at ONE type, so
  -- check mode is infer-and-match and nothing about the literal is decided by
  -- the expected type. The `Maybe (X , π , T ≡ X ⇒ Int)` scrutinee these two
  -- carried WAS the target-directedness, and it is gone with the lift.
  checkElabV-RInt-aux :
    ∀ (ctx : NamedCtx) (n : ℤ) (T : Type)
    → VerifiedCheckResult ctx (Raw.RInt n) T
  checkElabV-RFloat-aux :
    ∀ (ctx : NamedCtx) (i f l p : ℕ) (T : Type)
    → VerifiedCheckResult ctx (Raw.RFloat i f l p) T

  -- RFloat infer-mode. No dispatch _ left at all — it is the `RInt` clause with
  -- `decimalOf` in place of the digit.
  inferElabV-RFloat-aux :
    ∀ (ctx : NamedCtx) (i f l p : ℕ)
    → VerifiedInferResult ctx (Raw.RFloat i f l p)

  -- RPair check-mode dispatch, taking the target classification explicitly
  -- (product / pure-arrow-to-product / other). One scrutinee, no overlap.
  checkElabV-RPair-aux :
    ∀ (ctx : NamedCtx) (a b : RawExpr) (T : Type)
    → RPairTarget T
    → VerifiedCheckResult ctx (Raw.RPair a b) T

  -- ===== inferElab =====

  -- Literals
  -- inferElab as projection of the verified version.
  inferElab ctx e = proj₁ (inferElabV ctx e)
    where open import Data.Product using (proj₁)

  -- ===== checkElab =====

  -- Lambda in check mode: destruct expected function type
  --
  -- The body's first-position usage `q'` must satisfy `q' ≤q q`; we
  -- need the Bool decision *with its proof* to construct `Surface.lam`.
  -- Returning the decision via a `Maybe`-wrapping helper (`decideLeq`,
  -- defined above) avoids the stdlib `inspect` idiom, whose internal
  -- `with`-helper name is opaque to external proofs.
  -- checkElab as projection of the verified version.
  checkElab ctx e T = proj₁ (checkElabV ctx e T)
    where open import Data.Product using (proj₁)

  -- | Check-mode dispatch for bare `RVar` names (plan 0.6 Phase C.7).
  -- Each bare polymorphic builtin has a specialised clause that:
  --   1. Tries lookup first. On success, uses the bound definition —
  --      matches `t-embed (t-var-local/import …)` with the correct
  --      non-zero Ψ.
  --   2. On lookup failure at the canonical type shape, emits the
  --      `spec*` Surface IR with `zeroUsage` — matches the new
  --      `t-X-check` judgment rule.
  -- The two paths are disjoint by construction: each derivation
  -- uniquely identifies which elab path fires.
  --
  -- Dispatches on `classifyBareBuiltin x` so abstract `x` in
  -- downstream proofs reduces correctly (same idiom used by
  -- `classifyAppHeadView`).
  checkElab-RVar ctx x T with classifyBareBuiltin x
  -- Non-specialised names: lookup-then-match. On inferElab failure,
  -- try the polymorphic context (plan 0.6.2 Phase 3): if `x` is a
  -- user poly def, specialise it by check-mode-typechecking its
  -- body at the expected type `T`. Body is typechecked in a clean
  -- context (no user locals) because poly defs are top-level and
  -- can't reference user locals; the resulting SExpr is weakened
  -- from the empty-local context into the caller's ctx.
  ... | bbc-other with inferElab ctx (Raw.RVar x)
  ...   | success T' Ψ eE d f with T ≟T T'
  ...     | yes refl = success _ eE d f
  ...     | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx x T | bbc-other | failure err with lookupPoly (NamedCtx.polys ctx) x
  ... | nothing = failure err
  -- Plan 0.6.2 Phase 4: emit a proper `poly` placeholder constructor.
  -- Phase 2's `resolveExpr` pattern-matches on this constructor directly
  -- — no string encoding, no prefix check. Keeps Phase 1 structural (no
  -- TERMINATING pragma) and gives downstream consumers type-level
  -- visibility: an Expr with `poly` nodes hasn't been through Phase 2.
  -- Plan 0.58 / D071: NO concreteness gate — a same-module def reference is a
  -- context projection, not an FFI value, so it is emitted at ANY type `T`.
  ... | just _ = success Surface.zeroUsage (Surface.poly x T)
                     0 (NamedCtx.freshCounter ctx)
  -- id : T → T
  checkElab-RVar ctx _ T | bbc-id with inferElab ctx (Raw.RResolved (gen "id"))
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) | bbc-id | failure _ with A ≟T B
  ... | yes refl = success _ (weakenFromEmpty (specId A)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "id")
  checkElab-RVar ctx _ _ | bbc-id | failure err = failure err
  -- fst : (A * B) → A
  checkElab-RVar ctx _ T | bbc-fst with inferElab ctx (Raw.RResolved (gen "fst"))
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A') | bbc-fst | failure _ with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specFst A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "fst")
  checkElab-RVar ctx _ _ | bbc-fst | failure err = failure err
  -- snd : (A * B) → B
  checkElab-RVar ctx _ T | bbc-snd with inferElab ctx (Raw.RResolved (gen "snd"))
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B') | bbc-snd | failure _ with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specSnd A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "snd")
  checkElab-RVar ctx _ _ | bbc-snd | failure err = failure err
  -- terminal : A → Unit
  checkElab-RVar ctx _ T | bbc-terminal with inferElab ctx (Raw.RResolved (gen "terminal"))
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Unit) | bbc-terminal | failure _ =
    success _ (weakenFromEmpty (specTerminal A)) 0 (NamedCtx.freshCounter ctx)
  checkElab-RVar ctx _ _ | bbc-terminal | failure err = failure err
  -- initial : Void → A
  checkElab-RVar ctx _ T | bbc-initial with inferElab ctx (Raw.RResolved (gen "initial"))
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A) | bbc-initial | failure _ =
    success _ (weakenFromEmpty (specInitial A)) 0 (NamedCtx.freshCounter ctx)
  checkElab-RVar ctx _ _ | bbc-initial | failure err = failure err
  -- inl : A → (A + B)
  checkElab-RVar ctx _ T | bbc-inl with inferElab ctx (Raw.RResolved (gen "inl"))
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A' Once.Type.+ B)) | bbc-inl | failure _ with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specInl A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "inl")
  checkElab-RVar ctx _ _ | bbc-inl | failure err = failure err
  -- inr : B → (A + B)
  checkElab-RVar ctx _ T | bbc-inr with inferElab ctx (Raw.RResolved (gen "inr"))
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B')) | bbc-inr | failure _ with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specInr A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "inr")
  checkElab-RVar ctx _ _ | bbc-inr | failure err = failure err

  -- Plan 0.6 Phase C.7 POC-2: bare `pair f g` check-mode.
  -- Expected type must be `A ⇒[Many] (B * C)`. Checks each
  -- component function at its projected arrow shape, then emits
  -- `app (app specPair fE) gE`. No lookup-first branch: the
  -- classifier's `ahv-pair-applied` dispatch already establishes
  -- disjointness with `t-embed (t-app …)` — t-app's premise
  -- `classifyAppHead f ≡ nothing` fails for the pair-applied shape.
  checkPair ctx (Raw.RApp (Raw.RResolved (gen "pair")) f_inner) arg
            (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (B Once.Type.* C))
    with checkElabV ctx f_inner (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
  ... | failure err , _ = failure err , tt
  ... | success Ψf fE df frf , wF
        with checkElabV ctx arg (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C)
  ...     | failure err , _ = failure err , tt
  ...     | success Ψg gE dg frg , wG
            =
              success _ (Surface.fork' fE gE)
                (suc (df Data.Nat.⊔ dg)) frg , t-pair-morph-check wF wG
  -- Plan 0.52 (pure⊑eff): the pair morphism is grade-poly, so at an EFF arrow it
  -- is the pure pair wrapped in arr'/t-subsume (the m-pair morphism stays pure).
  checkPair ctx (Raw.RApp (Raw.RResolved (gen "pair")) f_inner) arg
            (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] (B Once.Type.* C))
    with checkElabV ctx f_inner (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
  ... | failure err , _ = failure err , tt
  ... | success Ψf fE df frf , wF
        with checkElabV ctx arg (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C)
  ...     | failure err , _ = failure err , tt
  ...     | success Ψg gE dg frg , wG
            =
              success _ (Surface.arr' (Surface.fork' fE gE))
                (suc (df Data.Nat.⊔ dg)) frg , t-subsume (t-pair-morph-check wF wG)
  -- Any other shape falls through to failure. Consistent with
  -- ahv-inl's per-shape exhaustive enumeration pattern.
  checkPair _ _ _ _ = failure (BuiltinTypeMismatch "pair") , tt

  -- Plan 0.36 Phase 2a follow-up: pair literal `(a , b)` at `A * B`.
  -- CHECK each component against its expected type (so check-only
  -- constructs like `In` get a type), emit the same `Surface.pair`.
  checkPairLit ctx a b A B with checkElabV ctx a A
  ... | failure err , _ = failure err , tt
  ... | success Ψ₁ aE da fa , wA with checkElabV ctx b B
  ...   | failure err , _ = failure err , tt
  ...   | success Ψ₂ bE db fb , wB =
          success _ (Surface.pair aE bE) (da Data.Nat.⊔ db) fb , t-pair-lit-check wA wB

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
  checkCase ctx (Raw.RApp (Raw.RResolved (gen "case")) f_inner) arg
            ((A Once.Type.+ B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] C)
    with checkCaseGo ctx f_inner arg A B C Once.Type.eff
  ... | (success Ψ eE d fr , w) = success Ψ eE d fr , w
  ... | (failure _ , _)
        with checkCaseGo ctx f_inner arg A B C Once.Type.pure
  ...     | (success Ψ eE d fr , w) = success Ψ (Surface.arr' eE) d fr , t-subsume w
  ...     | (failure err , _) = failure err , tt
  checkCase ctx (Raw.RApp (Raw.RResolved (gen "case")) f_inner) arg
            ((A Once.Type.+ B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) =
    checkCaseGo ctx f_inner arg A B C π
  checkCase _ _ _ _ = failure (BuiltinTypeMismatch "case") , tt

  checkCaseGo ctx f g A B C π
    with checkElabV ctx f (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  ... | failure err , _ = failure err , tt
  ... | success Ψf fE df frf , wF
        with checkElabV ctx g (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  ...     | failure err , _ = failure err , tt
  ...     | success Ψg gE dg frg , wG
            =
                success _ (Surface.copair' fE gE)
                  (suc (df Data.Nat.⊔ dg)) frf , t-case-copair-check wF wG

  -- Plan 0.6 Phase C.7 POC-3 + 0.6.2 Phase 3b: bare `compose f g`
  -- check-mode. Expected `A ⇒[Many] C`. Primary path: infer g's type
  -- to determine B, then check f at `B ⇒[Many] C`. Fallback: if g
  -- is a polymorphic name (user def), derive B via
  -- `composePolyArgB` (schema-instantiation at domain A), then
  -- checkElab both sub-expressions at the resolved types.
  -- Plan 0.4 T2 follow-up: rule-split. checkCompose now uses *only*
  -- composeArgB to recover B (the inferElab-driven path was dropped
  -- because the typing rule must be locally decidable in a
  -- no-unification bidirectional system). The witness `t-compose-check`
  -- takes the composeArgB equality directly.
  -- Plan 0.49 / D063: ONE grade-polymorphic clause (D056 — pure+eff unified, no
  -- closure fallback, `checkComposeWithB/g` retired). `composeMid` recovers B;
  -- both factors must be morphisms (`extractMorphWitness`); emit `lift-morphism
  -- (m_f ∘ m_g)`; witness `t-morph-lift (m-compose …)`.
  -- Plan 0.52 (pure⊑eff): compose at an EFF outer arrow. First try the genuinely
  -- eff path (arms checked at eff); if that fails (e.g. a pure-fixed arm like
  -- `pair`/`curry`/a named import), check the whole compose at PURE and subsume
  -- via arr'/t-subsume. This makes `checkElab (compose f g) (…eff…)` ACCEPT a
  -- subsumed pure compose (soundness of the subsume-complete bridge).
  checkCompose ctx (Raw.RApp (Raw.RResolved (gen "compose")) f_inner) arg
               (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] C)
    with checkComposeGo ctx f_inner arg A C Once.Type.eff (composeMid ctx f_inner arg A) refl
  ... | (success Ψ eE d fr , w) = success Ψ eE d fr , w
  ... | (failure _ , _)
        with checkComposeGo ctx f_inner arg A C Once.Type.pure (composeMid ctx f_inner arg A) refl
  ...     | (success Ψ eE d fr , w) = success Ψ (Surface.arr' eE) d fr , t-subsume w
  ...     | (failure err , _) = failure err , tt
  checkCompose ctx (Raw.RApp (Raw.RResolved (gen "compose")) f_inner) arg
               (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C) =
    checkComposeGo ctx f_inner arg A C π (composeMid ctx f_inner arg A) refl
  checkCompose _ _ _ _ = failure (BuiltinTypeMismatch "compose") , tt

  checkComposeGo ctx f g A C π nothing eqB = failure (BuiltinTypeMismatch "compose") , tt
  checkComposeGo ctx f g A C π (just B) eqB
        with checkElabV ctx g (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
  ...     | failure err , _ = failure err , tt
  ...     | success Ψg gE dg frg , wG
            with checkElabV ctx f (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  ...         | failure err , _ = failure err , tt
  ...         | success Ψf fE df frf , wF =
                  success _ (Surface.comp' fE gE) (suc (df Data.Nat.⊔ dg)) frf
                  , t-compose-check eqB wF wG

  -- Plan 0.6 Phase C.7 POC-3: `curry f` check-mode.
  -- Expected `A ⇒[Many] (B ⇒[Many] C)`. Check f at `(A * B) ⇒[Many] C`.
  checkCurry ctx arg (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C))
    with checkElabV ctx arg ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C)
  ... | failure err , _ = failure err , tt
  ... | success Ψ argE d fr , w =
          success _ (Surface.curry' argE) (suc d) fr , t-curry-check w
  -- Plan 0.52 (pure⊑eff): curry at an EFF outer arrow is the pure curry wrapped
  -- in arr'/t-subsume (the m-curry morphism stays pure; inner arrow unchanged).
  checkCurry ctx arg (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C))
    with checkElabV ctx arg ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C)
  ... | failure err , _ = failure err , tt
  ... | success Ψ argE d fr , w =
          success _ (Surface.arr' (Surface.curry' argE)) (suc d) fr
          , t-subsume (t-curry-check w)
  checkCurry _ _ _ = failure (BuiltinTypeMismatch "curry") , tt

  -- Plan 0.6 Phase C.7 POC-3: `apply p` check-mode.
  -- Check mode falls through to infer (apply's infer mode succeeds
  -- when p has pair-of-function type). Matches result against T.
  checkApply ctx arg T with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A') Ψ argE d fr , w
        with A ≟T A' | T ≟T B
  ...   | yes refl | yes refl =
          success _ (Surface.morph-app IR.apply argE) (suc d) fr , t-apply-check w
  ...   | yes refl | no _ = failure (TypeMismatch T B) , tt
  ...   | no _ | _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success Unit _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success Void _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success Int _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success Float _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success Str _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success Buffer _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (_ Once.Type.+ _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Unit Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Void Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Int Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Float Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Str Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Buffer Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success ((_ Once.Type.* _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success ((_ Once.Type.+ _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success ((_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.pure ] _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success ((_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.pure ] _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success ((_ Once.Type.⇒[ Once.Type.mk-kind _ Once.Type.eff ] _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success ((Once.Type.μ-type _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success ((Once.Type.ν-type _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Once.Type.μ-type _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  checkApply ctx arg T | success (Once.Type.ν-type _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt

  -- Plan 0.28 Commit 2: `In arg` (μ-introduction) check-mode at `μ-type F`.
  -- Read F from the expected μ-type, gate on `wellFormedF? F` (threaded
  -- through `checkInGo`), check the argument at the functor layer, emit
  -- `morph-app (IR.In wfF Heap) argE`.
  checkIn ctx arg (Once.Type.μ-type F) = checkInGo ctx arg F (wellFormedF? F) refl
  -- D127: `In arg` at an ARROW type is no longer a lift. It falls through to
  -- the mismatch below, and the program writes `\_ -> In arg`.
  checkIn _ _ _ = failure (BuiltinTypeMismatch "In") , tt

  checkInGo ctx arg F nothing _ = failure (BuiltinTypeMismatch "In") , tt
  checkInGo ctx arg F (just wfF) eqW with checkElabV ctx arg (⟦ F ⟧T (Once.Type.μ-type F))
  ... | failure err , _ = failure err , tt
  ... | success Ψ argE d fr , wArg =
        success _ (Surface.morph-app (subst (λ o → IR o ⌊ Once.Type.μ-type F ⌋) (sym (⌊⟧T-commute F (Once.Type.μ-type F))) (IR.In (wf-⌊⌋ wfF) IR.Heap)) argE) (suc d) fr , t-In-app-check wfF wArg

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
  checkCata ctx alg (Once.Type.μ-type F Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] A)
    with checkCataGo ctx alg F A Once.Type.eff (wellFormedF? F) refl
  ... | (success Ψ eE d fr , w) = success Ψ eE d fr , w
  ... | (failure _ , _)
        with checkCataGo ctx alg F A Once.Type.pure (wellFormedF? F) refl
  ...     | (success Ψ eE d fr , w) = success Ψ (Surface.arr' eE) d fr , t-subsume w
  ...     | (failure err , _) = failure err , tt
  checkCata ctx alg (Once.Type.μ-type F Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A) =
    checkCataGo ctx alg F A π (wellFormedF? F) refl
  checkCata _ _ _ = failure (BuiltinTypeMismatch "cata") , tt

  -- Plan 0.36 Phase 2a: the algebra is ANY closed function `⟦F⟧T A → A`.
  -- Elaborate it in the EMPTY debruijn context (closed ⇔ empty ctx),
  -- keeping the ambient imports/polys so named/arith/effectful refs
  -- resolve. The result `algE : Expr ∅ zeroUsage (⟦F⟧T A ⇒ A)` rides the
  -- `Surface.cata` node past `resolveExpr` (which inlines it); the closed
  -- `IR.Cata` is built later by `Surface.Elaborate.elaborate`. The empty
  -- context forces closedness: a non-closed algebra fails to elaborate
  -- here (true runtime closures are out of scope — see plan 0.36).
  checkCataGo ctx alg F A π nothing _ = failure (BuiltinTypeMismatch "cata") , tt
  checkCataGo ctx alg F A π (just wfF) eqW
    with checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
                    alg (⟦ F ⟧T A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A)
  ... | failure err , _ = failure err , tt
  -- D127: no witness extraction. The algebra's own check-derivation IS the
  -- premise, and the empty debruijn context is what `Surface.cata` demands of
  -- the algebra it carries — the closedness is enforced by the CONTEXT, as it
  -- always was, not by a realm.
  ... | success Surface.[] algE d fr , wArg =
          success _ (Surface.cata wfF algE) (suc d) (NamedCtx.freshCounter ctx)
            -- PLAN 0.80 A1: the rule takes the WITNESS, not the decider
            -- equation. `wfF` is the decider's own output, bound by the
            -- `just wfF` pattern above — so the elaborator hands over exactly
            -- what it computed, and `eqW` is now only bookkeeping for the
            -- completeness proof's `J`-style helpers.
            , t-cata-check wfF wArg

  -- Body for the hoisted `ahv-other` (generic application) branch.
  inferElab-RApp-other ctx f x with asFun (inferElab ctx f)
  ... | notFun err = failure err
  ... | isFun A q B Ψ₁ fE df ff with checkElab ctx x A
  ...   | failure err = failure err
  ...   | success Ψ₂ xE dx fx = success B _ (Surface.app fE xE) (df ⊔ dx) fx
  inferElab-RApp-other ctx f x | isEff A B Ψ₁ fE df ff with checkElab ctx x A
  ...   | failure err = failure err
  ...   | success Ψ₂ xE dx fx = success (Unit ⇒[ mk-kind Many eff ] B) _ (Surface.effApp fE xE) (df ⊔ dx) fx

------------------------------------------------------------------------
-- Generic-fallback lemmas (G2 completeness — check-mode).
--
-- These hoisted-helpers say: for each RawExpr shape whose check-mode
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


  -- ===== Verified-elaborator bodies (Plan 0.4 T0 Option B) =====

  ----------------------------------------------------------------------
  -- Phase A — easy `inferElab` clauses (literals, RLam-failure,
  -- RAnnot, RPair).
  ----------------------------------------------------------------------

  inferElabV ctx (Raw.RInt n) =
    success Int _ (Surface.int n) 0 (NamedCtx.freshCounter ctx) , t-int n

  inferElabV ctx (Raw.RFloat i f l p) = inferElabV-RFloat-aux ctx i f l p

  inferElabV ctx (Raw.RStringLit s) =
    success Str _ (Surface.str s) 0 (NamedCtx.freshCounter ctx) , t-str s

  inferElabV ctx Raw.RUnit =
    success Unit _ Surface.unit 0 (NamedCtx.freshCounter ctx) , t-unit

  inferElabV ctx (Raw.RLam _ _) =
    failure LambdaInInferMode , tt

  -- `RAna` is INTERNAL (erase of an already-elaborated `ana`); the parser never
  -- produces it, so `inferElabV` never legitimately sees it — reject for totality.
  inferElabV ctx (Raw.RAna _ _) =
    failure (BuiltinTypeMismatch "ana") , tt

  inferElabV ctx (Raw.RAnnot e T) = inferElabV-RAnnot-aux ctx e T (checkElabV ctx e T)

  inferElabV ctx (Raw.RPair a b) =
    inferElabV-RPair-aux ctx a b (inferElabV ctx a) (inferElabV ctx b)

  ----------------------------------------------------------------------
  -- Phase B — lookup-driven clauses (RQualified, RVar, RUnaryOp,
  -- RLet, RDestruct). RBinOp deferred (more complex op + type
  -- dispatch).
  ----------------------------------------------------------------------

  inferElabV ctx (Raw.RQualified name alias) =
    inferElabV-RQualified-aux ctx name alias _ refl

  -- D136: ONE clause, routed through the `GenView`. Concrete
  -- `RResolved (gen "g")` clauses here would stop `checkElabV`/`inferElabV`
  -- reducing for an ABSTRACT `cn`, which the downstream proofs depend on —
  -- the same reason `checkElabV-RApp-dispatch` takes its view as a parameter.
  inferElabV ctx (Raw.RResolved cn) =
    inferElabV-RResolved-dispatch ctx cn (classifyGen cn)

  -- D136: a bare `RVar` is NEVER a generator — the resolver has already turned
  -- an unshadowed generator into `RResolved (gen g)`. So this path is ordinary
  -- variables only, and the `"unit"` special case moved to `RResolved` below.
  inferElabV ctx (Raw.RVar x) =
    inferElabV-RVar-lookup-aux ctx x _ refl _ refl

  inferElabV ctx (Raw.RUnaryOp Raw.OpNeg e) = inferElabV-neg-dispatch ctx e

  inferElabV ctx (Raw.RLet x e₁ e₂) =
    inferElabV-RLet-aux ctx x e₁ e₂ (inferElabV ctx e₁)

  inferElabV ctx (Raw.RDestruct scrut xL eL xR eR) =
    inferElabV-RDestruct-aux ctx scrut xL eL xR eR (inferElabV ctx scrut)

  ----------------------------------------------------------------------
  -- Phase C — `inferElab` `RApp` (13 view branches).
  ----------------------------------------------------------------------

  inferElabV ctx (Raw.RApp f arg) =
    inferElabV-RApp-dispatch ctx f arg _ refl

  ----------------------------------------------------------------------
  -- inferElabV `RBinOp` — both operands must be Int. The result type
  -- depends on `op`: arithmetic ops produce Int via `t-binop-arith`,
  -- comparison ops produce Unit + Unit via `t-binop-cmp`. The
  -- `isArithmeticOp` / `isComparisonOp` premises reduce to `refl` once
  -- `op` is concretely matched.
  ----------------------------------------------------------------------

  inferElabV ctx (Raw.RBinOp op e₁ e₂) =
    inferElabV-RBinOp-aux ctx op e₁ e₂ (inferElabV ctx e₁) (inferElabV ctx e₂)

  ----------------------------------------------------------------------
  -- Phase D — `checkElab` clauses.
  -- Specialised RawExpr shapes (RVar, RApp, RLam) are still TODO; they
  -- delegate to the existing `checkElab`. Everything else uses the
  -- generic infer-and-match fallback, with the witness lifted via
  -- `t-embed`.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- Phase F migration of `checkElab` `RApp` (13 view branches).
  -- Specialised check-mode rules: `t-inl-app-check`, `t-inr-app-check`,
  -- `t-initial-app-check`, `t-arr-app-check`, `t-arg-driven-app-check`.
  -- Fall-through branches use `t-embed` of `inferElabV`'s witness.
  -- Helper-applied branches (pair / compose / curry / apply) delegate
  -- to the existing helpers; their soundness is supplied by per-helper
  -- witness postulates above.
  ----------------------------------------------------------------------

  checkElabV-wf ctx ac (Raw.RApp f arg) T =
    checkElabV-RApp-dispatch ctx f arg T _ refl

  -- RLam check-mode: only well-typed at a pure arrow type.
  checkElabV-wf ctx ac (Raw.RLam x body) (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) with checkElabV (extendNamedCtx ctx x A) body B
  ... | failure err , _ = failure err , tt
  ... | success (q' ∷ᵘ Ψ) bodyE d fr , wBody with decideLeq q' q
  ...   | just eq = success _ (Surface.lam q eq bodyE) (suc d) fr , t-lam eq wBody
  ...   | nothing = failure (UsageViolation x q q') , tt
  -- Eff arrow: pure ⊑ eff SUBSUMPTION (Plan 0.52 M1) — a lambda checks at the
  -- corresponding pure arrow and is lifted by `t-subsume` (no `arr` needed).
  checkElabV-wf ctx ac (Raw.RLam x body) (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) with checkElabV (extendNamedCtx ctx x A) body B
  ... | failure err , _ = failure err , tt
  ... | success (q' ∷ᵘ Ψ) bodyE d fr , wBody with decideLeq q' Once.Type.Many
  ...   | just eq = success _ (Surface.arr' (Surface.lam Once.Type.Many eq bodyE)) (suc d) fr , t-subsume (t-lam eq wBody)
  ...   | nothing = failure (UsageViolation x Once.Type.Many q') , tt
  -- Non-arrow T: lambda's only check-mode rules are t-lam (pure) / t-subsume (eff).
  checkElabV-wf ctx ac (Raw.RLam _ _) _ = failure LambdaRequiresFunctionType , tt

  ----------------------------------------------------------------------
  -- Phase E — `checkElab` `RVar` migration via `classifyBareBuiltin`
  -- dispatch. Each `bbc-X` clause produces both result and witness
  -- inline; the previously-postulated `spec-gap-sound-check-RVar-X`
  -- proofs become unnecessary once this phase replaces every clause.
  -- POC: bbc-fst migrated; other bbc-X still delegate.
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
  checkElabV-wf ctx ac (Raw.RVar x) T with inferElabV ctx (Raw.RVar x)
  ... | rInfV@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RVar x) T rInfV
  ... | rInfV@(failure _ , _) = checkElabV-RVar-bbc-other-aux ctx x T rInfV

  -- D136: the point-free generator leaves, routed through the `GenView` so the
  -- clause stays SINGLE and `checkElabV (RResolved cn)` keeps reducing for an
  -- abstract `cn`. No `classifyBareBuiltin` guess and no shadowing check — a
  -- user's `fst` never reaches a generator branch, because the resolver never
  -- gave it this name.
  checkElabV-wf ctx ac (Raw.RResolved cn) T =
    checkElabV-RResolved-dispatch ctx cn T (classifyGen cn)
      (inferElabV ctx (Raw.RResolved cn))

  -- Plan 0.36 Phase 2a follow-up: pair literal `(a , b)` at a product
  -- type — check components bidirectionally so check-only constructs
  -- (notably `In`) work in pair slots (`In (inr (x , tail))`). Falls to
  -- the generic clause below for non-product target types.
  checkElabV-wf ctx ac (Raw.RPair a b) T = checkElabV-RPair-aux ctx a b T (classifyRPairTarget T)

  -- Plan 0.41 / D018 leaf: an integer literal at a pure-arrow position is its
  -- constant morphism (global element `const n ∘ terminal`, via `intLit`),
  -- the `g-int` leaf of `⊢ᵍ` bridged by `t-value-lift`; otherwise the generic
  -- infer-and-match. Routed through ONE scrutinee (`isRIntVliftTarget? T`) so
  -- the two outcomes don't overlap (no stuck `checkElabV (RInt n) T` for
  -- variable `T`). Behaviour is unchanged; the dispatch is now analysable.
  checkElabV-wf ctx ac (Raw.RInt n) T = checkElabV-RInt-aux ctx n T
  checkElabV-wf ctx ac (Raw.RFloat i f l p) T =
    checkElabV-RFloat-aux ctx i f l p T
  -- PLAN 0.73 F3: `- <literal>` gets the same value-lift the bare literal
  -- does. Before this it fell through to the generic clause below, which
  -- infers `Int`/`Float` and then mismatches against the ARROW the position
  -- wants — which is why `compose emit@E (-5)` did not compile.
  checkElabV-wf ctx ac (Raw.RUnaryOp Raw.OpNeg e) T =
    checkElabV-neg-dispatch ctx e T (negOperandView e)

  -- Generic infer-and-match fallback — covers RInt, RStringLit, RUnit,
  -- RPair, RBinOp, RUnaryOp, RLet, RDestruct, RAnnot, RQualified, RResolved.
  -- NB: the `with inferElabV ctx e` here is LOAD-BEARING for termination — the
  -- mutual `checkElab`↔`inferElab` same-size call (`checkElab e → inferElab e`)
  -- is accepted by the foetus checker only as a `with`-scrutinee; extracting it
  -- to an explicit-arg aux breaks termination. NOT every `with` is removable.
  checkElabV-wf ctx ac e T = embedOrSubsume ctx e T (inferElabV ctx e)

  -- `unit` is the one generator that INFERS; the rest are polymorphic and only
  -- check, so they fall to the ordinary resolved path (which reports the right
  -- error for a bare use).
  inferElabV-RResolved-dispatch ctx _ gv-unit =
    success Unit _ Surface.unit 0 (NamedCtx.freshCounter ctx) , t-unit-var
  -- D136: a generator's canonical name is COMPILER-OWNED, so looking it up in
  -- the user's import table is meaningless — these fail directly rather than
  -- routing through `inferElabV-RResolved-aux`. The seven point-free
  -- generators are polymorphic and do not infer; they must appear applied or
  -- in check mode, which is what `UnboundVariable` has always reported here.
  -- Failing directly is also what lets the `checkElab-fallback-RVar-*` lemmas
  -- reduce without a "Generators.* is not imported" premise nobody could supply.
  inferElabV-RResolved-dispatch ctx cn gv-id       = failure (UnboundVariable "id") , tt
  inferElabV-RResolved-dispatch ctx cn gv-fst      = failure (UnboundVariable "fst") , tt
  inferElabV-RResolved-dispatch ctx cn gv-snd      = failure (UnboundVariable "snd") , tt
  inferElabV-RResolved-dispatch ctx cn gv-terminal = failure (UnboundVariable "terminal") , tt
  inferElabV-RResolved-dispatch ctx cn gv-initial  = failure (UnboundVariable "initial") , tt
  inferElabV-RResolved-dispatch ctx cn gv-inl      = failure (UnboundVariable "inl") , tt
  inferElabV-RResolved-dispatch ctx cn gv-inr      = failure (UnboundVariable "inr") , tt
  inferElabV-RResolved-dispatch ctx cn (gv-other ng) = inferElabV-RResolved-aux ctx cn ng _ refl

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
  checkElabV-RResolved-dispatch ctx cn T (gv-other _) rInfV = embedOrSubsume ctx (Raw.RResolved cn) T rInfV


  -- Acc-free wrapper (Plan 0.58 E1-full): re-derive a fresh well-founded Acc.
  -- Sound per POC-B — the poly-resolution recursion uses the RECEIVED Acc's `rec`;
  -- non-poly recursion (through this wrapper) resets to fresh, which foetus accepts.
  checkElabV ctx e T = checkElabV-wf ctx (<-wellFounded (length (NamedCtx.polys ctx))) e T

  ----------------------------------------------------------------------
  -- `inferElabV-RApp-other` body — verified counterpart of
  -- `inferElab-RApp-other`. Pattern-matches on `inferElabV ctx f`'s
  -- type to determine whether `f` is a pure-arrow (use `t-app`),
  -- effect-arrow (use `t-effApp`), or non-function (failure). The
  -- `notPoly : classifyAppHead f ≡ nothing` premise is captured via
  -- `with classifyAppHead f in eqAH` — the `nothing` branch carries
  -- it; the `just _` branch is unreachable because callers only
  -- invoke this helper when the view classifies `f` as `ahv-other`.
  ----------------------------------------------------------------------
  inferElabV-RApp-other ctx f x =
    inferElabV-RApp-other-aux ctx f x _ refl

  -- | Build an external arrow op's `SigOpInfo` from its DECLARED effect
  -- (Plan 0.38 M0.2). The compiler is interpretation-BLIND: the effect
  -- comes from the `! <shape>` annotation in the imported signature
  -- (looked up in `NamedCtx.sigEffects` by the same qualified key as the
  -- type), NEVER from a hardcoded name (the retired effect-from-name guess is
  -- gone). An effectful, `Unit`-codomain op carries a CONTRACT
  -- (`haltsV`/`emitsV`), no value. A pure arrow, or an `eff` op whose
  -- codomain is not `Unit` (the deferred data-returning-syscall
  -- boundary), falls back to a `pureV` value (the `closure`/`poly`-style
  -- function-linking opacity, a separate axis from the syscall contract).
  ext-arrow-info : ∀ {A B} → NamedCtx → (alias name : String) → Purity
                 → IsBaseType A → IsConcrete B → SigOpInfo A B
  ext-arrow-info ctx alias name pure bA cB = mk-info' (bare (alias ++ "." ++ name)) (pureV (generic-semM (alias ++ "." ++ name))) bA (ffi-concrete cB)
  ext-arrow-info {A} {B} ctx alias name eff bA cB with B ≟T Unit
  ... | no _ = mk-info' (bare (alias ++ "." ++ name)) (pureV (generic-semM (alias ++ "." ++ name))) bA (ffi-concrete cB)
  ... | yes refl with lookupSigEffect (NamedCtx.sigEffects ctx) (alias ++ "." ++ name)
  ...   | just se-halts = mk-info' (bare (alias ++ "." ++ name)) (haltsV refl) bA (ffi-concrete cB)
  ...   | just se-emits = mk-info' (bare (alias ++ "." ++ name)) (emitsV refl) bA (ffi-concrete cB)
  ...   | nothing       = mk-info' (bare (alias ++ "." ++ name)) (emitsV refl) bA (ffi-concrete cB)

  -- Aux helper bodies (placed after all main mutual members so that the
  -- `... | pat` continuations of inferElabV/checkElabV clauses don't
  -- conflict with the aux's own clauses).
  -- A qualified ref `name@alias` is ALWAYS genuinely external (from an
  -- import, never a local userFn). Used as a value at a `Many`-arrow type it
  -- IS the external `SigOp (generic-info name)`; emit it as `lift-morphism`
  -- so `extract-morph`/`extract-morph-eff` recover it BY CONSTRUCTION and the
  -- eff `case`/`compose` fuse the algebra to a DIRECT morphism (no apply, no
  -- effApp suspension). The distinguisher the laundering bug lacked: internal
  -- `seven` is unqualified → stays `sigOp` → resolver → closure; only genuine
  -- externals become `lift-morphism (SigOp …)`.
  inferElabV-RQualified-aux ctx name alias
    (just (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)) eq =
    inferElabV-RQualified-arrow-aux ctx name alias eq (isBaseType? A) refl (isConcrete? B) refl
  inferElabV-RQualified-aux ctx name alias (just ty) eq =
    inferElabV-RQualified-value-aux ctx name alias ty eq (isConcrete? ty) refl
  inferElabV-RQualified-aux ctx name alias nothing _ =
    failure (UnboundQualified name alias) , tt

  -- Concreteness-driven arrow value emission (de-withed for Completeness).
  inferElabV-RQualified-arrow-aux ctx name alias {A} {B} {π} eq (just bA) _ (just cB) _ =
    success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) _
      (Surface.lift-morphism {π = π} (IR.SigOp (ext-arrow-info ctx alias name π bA cB)))
      0 (NamedCtx.freshCounter ctx)
    , t-var-qualified eq (con-fun bA cB)
  inferElabV-RQualified-arrow-aux ctx name alias {A} {B} {π} eq nothing _ _ _ =
    failure (NonConcreteSigOpType (alias ++ "." ++ name)
              (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)) , tt
  inferElabV-RQualified-arrow-aux ctx name alias {A} {B} {π} eq (just _) _ nothing _ =
    failure (NonConcreteSigOpType (alias ++ "." ++ name)
              (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)) , tt

  inferElabV-RQualified-value-aux ctx name alias ty eq (just conc) _ =
    success ty _ (Surface.sigOp (bare (alias ++ "." ++ name)) conc) 0 (NamedCtx.freshCounter ctx)
    , t-var-qualified eq conc
  inferElabV-RQualified-value-aux ctx name alias ty eq nothing _ =
    failure (NonConcreteSigOpType (alias ++ "." ++ name) ty) , tt

  -- Plan 0.50: resolved external ref. The canonical name `cn` is carried
  -- straight into the `SigOpInfo` (NO `bare`, NO String render) — so the
  -- realize/elaborator/trace/codegen names agree by construction. Mirrors
  -- `ext-arrow-info`/`inferElabV-RQualified-aux` but keyed by `cn`.
  -- De-withed (so the realize-agrees masquerade can fold it): the `B ≟T Unit`
  -- decision + the `lookupSigEffect` result are explicit args.
  ext-resolved-info-aux : ∀ {A B} → CanonicalName → Purity
                        → Dec (B ≡ Unit) → Maybe SigEffect
                        → IsBaseType A → IsConcrete B → SigOpInfo A B
  ext-resolved-info-aux cn pure _ _ bA cB = mk-info' cn (pureV (generic-semM (showCanonical cn))) bA (ffi-concrete cB)
  ext-resolved-info-aux cn eff (no _) _ bA cB = mk-info' cn (pureV (generic-semM (showCanonical cn))) bA (ffi-concrete cB)
  ext-resolved-info-aux cn eff (yes refl) (just se-halts) bA cB = mk-info' cn (haltsV refl) bA (ffi-concrete cB)
  ext-resolved-info-aux cn eff (yes refl) (just se-emits) bA cB = mk-info' cn (emitsV refl) bA (ffi-concrete cB)
  ext-resolved-info-aux cn eff (yes refl) nothing         bA cB = mk-info' cn (emitsV refl) bA (ffi-concrete cB)

  ext-resolved-info : ∀ {A B} → NamedCtx → CanonicalName → Purity
                    → IsBaseType A → IsConcrete B → SigOpInfo A B
  ext-resolved-info {A} {B} ctx cn π bA cB =
    -- Use the SHARED low `isUnit?` (same decision SD's `arrow-info` uses), so
    -- the realize-agrees masquerade folds both with one case-split.
    ext-resolved-info-aux cn π (Once.Type.isUnit? B) (lookupSigEffect (NamedCtx.sigEffects ctx) (showCanonical cn)) bA cB

  inferElabV-RResolved-aux ctx cn ng
    (just (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)) eq =
    inferElabV-RResolved-arrow-aux ctx cn ng eq (isBaseType? A) refl (isConcrete? B) refl
  inferElabV-RResolved-aux ctx cn ng (just ty) eq =
    inferElabV-RResolved-value-aux ctx cn ng ty eq (isConcrete? ty) refl
  inferElabV-RResolved-aux ctx cn ng nothing _ =
    failure (UnboundVariable (showCanonical cn)) , tt

  -- Concreteness-driven arrow value emission (de-withed for Completeness).
  inferElabV-RResolved-arrow-aux ctx cn ng {A} {B} {π} eq (just bA) _ (just cB) _ =
    success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) _
      (Surface.lift-morphism {π = π} (IR.SigOp (ext-resolved-info ctx cn π bA cB)))
      0 (NamedCtx.freshCounter ctx)
    , t-var-resolved ng eq (con-fun bA cB)
  inferElabV-RResolved-arrow-aux ctx cn ng {A} {B} {π} eq nothing _ _ _ =
    failure (NonConcreteSigOpType (showCanonical cn)
              (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)) , tt
  inferElabV-RResolved-arrow-aux ctx cn ng {A} {B} {π} eq (just _) _ nothing _ =
    failure (NonConcreteSigOpType (showCanonical cn)
              (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)) , tt

  inferElabV-RResolved-value-aux ctx cn ng ty eq (just conc) _ =
    success ty _ (Surface.sigOp cn conc) 0 (NamedCtx.freshCounter ctx) , t-var-resolved ng eq conc
  inferElabV-RResolved-value-aux ctx cn ng ty eq nothing _ =
    failure (NonConcreteSigOpType (showCanonical cn) ty) , tt

  -- RPair: pair the two sub-results (a-failure short-circuits without forcing
  -- b's result, matching the old left-to-right `with`).
  inferElabV-RPair-aux ctx a b (success A Ψ₁ aE da fa , wA) (success B Ψ₂ bE db fb , wB) =
    success (A Once.Type.* B) _ (Surface.pair aE bE) (da ⊔ db) fb , t-pair wA wB
  inferElabV-RPair-aux ctx a b (failure err , _) _ = failure err , tt
  inferElabV-RPair-aux ctx a b (success _ _ _ _ _ , _) (failure err , _) = failure err , tt

  inferElabV-RAnnot-aux ctx e T (success Ψ eE d fr , witness) = success T Ψ eE d fr , t-annot witness
  inferElabV-RAnnot-aux ctx e T (failure err , _)             = failure err , tt

  -- `-5` IS A LITERAL. Emitting `neg (int 5)` would compile to "load 5; call
  -- arith.neg.int" -- a RUNTIME negation of a compile-time constant -- and it
  -- is also what made `Once.IRLits` disagree with the spec's `negLits`, so
  -- that `-2147483648` was refused on x86-32 though it fits. The depth and
  -- fresh counter match what the unfolded path produced (`suc 0`), so nothing
  -- reading them changes. Sound by `Once.Word.Width.⊝-fromℤ`, which
  -- `RealizeAgrees` spends.
  -- The decision is an ARGUMENT, not a `with` and not a pattern match on `e`,
  -- so `inferElabV ctx (RUnaryOp OpNeg e)` still unfolds for an ABSTRACT `e`.
  -- That is the difference between this and the first attempt: matching `e`
  -- here would have forced every downstream proof to enumerate all sixteen
  -- `RawExpr` heads just to make the dispatch reduce. Downstream now does
  -- `with negOperandView e` and handles three cases. Same convention as
  -- `cfm-build-gated` taking its `Dec`.
  inferElabV-neg-dispatch ctx e = inferElabV-neg-aux ctx e (negOperandView e)

  inferElabV-neg-aux ctx .(Raw.RInt n) (nov-int n) =
    success Int _ (Surface.int (- n)) 1 (NamedCtx.freshCounter ctx) , t-neg (t-int n)
  -- PLAN 0.73 F3: `-3.14` is the literal whose payload is `negate (decimalOf
  -- i f l)`. Not a runtime negation of `3.14` — there is no float `neg` to
  -- emit (`MArithIR` is Int-only, F4), which is why the fold is the only
  -- lowering rather than the better of two. Both this and `Once.Denotation.
  -- Meaning`'s `⟦ t-neg-float ⟧ᵢ` name the SAME `negate ∘ decimalOf`, so
  -- agreement is `refl`-shaped and cannot falsify `round` — the pins in
  -- `Once.Float.Decimal` against externally computed patterns are the check
  -- that means something (D117).
  --
  -- Depth `1` and the untouched fresh counter mirror the `RInt` fold: one
  -- constructor deeper than the bare literal, no name allocated.
  inferElabV-neg-aux ctx .(Raw.RFloat i f l p) (nov-float i f l p) =
    success Float _ (Surface.float (Decimal.negate (decimalOf i f l))) 1
            (NamedCtx.freshCounter ctx)
    , t-neg-float i f l p
  inferElabV-neg-aux ctx e (nov-other .e) = inferElabV-RUnaryOp-aux ctx e (inferElabV ctx e)

  checkElabV-neg-dispatch ctx .(Raw.RInt n) T (nov-int n) =
    checkElabV-neg-int-aux ctx n T
  checkElabV-neg-dispatch ctx .(Raw.RFloat i f l p) T (nov-float i f l p) =
    checkElabV-neg-float-aux ctx i f l p T
  -- NOT a literal: the old generic clause verbatim, `embedOrSubsume` included,
  -- so the pure→eff subsumption (`t-subsume`, plan 0.52 M1) is not lost.
  checkElabV-neg-dispatch ctx e T (nov-other .e) =
    embedOrSubsume ctx (Raw.RUnaryOp Raw.OpNeg e) T
                   (inferElabV-RUnaryOp-aux ctx e (inferElabV ctx e))

  -- Written out so the FOLDED literal is what gets embedded — routing through
  -- `inferElabV ctx (RUnaryOp OpNeg (RInt n))` would be the same term but
  -- would stop reducing wherever the view has been abstracted.
  checkElabV-neg-int-aux ctx n T with T ≟T Int
  ... | yes refl = success Surface.zeroUsage (Surface.int (- n)) 1 (NamedCtx.freshCounter ctx)
                 , t-embed (t-neg (t-int n))
  ... | no _     = failure (TypeMismatch T Int) , tt

  checkElabV-neg-float-aux ctx i f l p T with T ≟T Once.Type.Float
  ... | yes refl = success Surface.zeroUsage
                           (Surface.float (Decimal.negate (decimalOf i f l))) 1
                           (NamedCtx.freshCounter ctx)
                 , t-embed (t-neg-float i f l p)
  ... | no _     = failure (TypeMismatch T Once.Type.Float) , tt

  inferElabV-RUnaryOp-aux ctx e (failure err , _)                = failure err , tt
  inferElabV-RUnaryOp-aux ctx e (success Unit   _ _ _ _ , _)     = failure (TypeMismatch Int Unit) , tt
  inferElabV-RUnaryOp-aux ctx e (success Void   _ _ _ _ , _)     = failure (TypeMismatch Int Void) , tt
  inferElabV-RUnaryOp-aux ctx e (success Int    Ψ eE d fr , w)   = success Int _ (Surface.neg eE) (suc d) fr , t-neg w
  inferElabV-RUnaryOp-aux ctx e (success Float  _ _ _ _ , _)     = failure (TypeMismatch Int Float) , tt
  inferElabV-RUnaryOp-aux ctx e (success Str    _ _ _ _ , _)     = failure (TypeMismatch Int Str) , tt
  inferElabV-RUnaryOp-aux ctx e (success Buffer _ _ _ _ , _)     = failure (TypeMismatch Int Buffer) , tt
  inferElabV-RUnaryOp-aux ctx e (success (A Once.Type.* B)      _ _ _ _ , _) = failure (TypeMismatch Int (A Once.Type.* B)) , tt
  inferElabV-RUnaryOp-aux ctx e (success (A Once.Type.+ B)      _ _ _ _ , _) = failure (TypeMismatch Int (A Once.Type.+ B)) , tt
  inferElabV-RUnaryOp-aux ctx e (success (A Once.Type.⇒[ k ] B) _ _ _ _ , _) = failure (TypeMismatch Int (A Once.Type.⇒[ k ] B)) , tt
  inferElabV-RUnaryOp-aux ctx e (success (Once.Type.μ-type F)   _ _ _ _ , _) = failure (TypeMismatch Int (Once.Type.μ-type F)) , tt
  inferElabV-RUnaryOp-aux ctx e (success (Once.Type.ν-type F)   _ _ _ _ , _) = failure (TypeMismatch Int (Once.Type.ν-type F)) , tt

  -- left non-Int → BinOpLeftError
  inferElabV-RBinOp-aux ctx op e₁ e₂ (failure err , _) _ = failure (BinOpLeftError err) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Unit   _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int Unit)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Void   _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int Void)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Str    _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int Str)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Buffer _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int Buffer)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success (A Once.Type.* B)      _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Type.* B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success (A Once.Type.+ B)      _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Type.+ B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success (A Once.Type.⇒[ k ] B) _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Type.⇒[ k ] B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success (Once.Type.μ-type F)   _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int (Once.Type.μ-type F))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success (Once.Type.ν-type F)   _ _ _ _ , _) _ = failure (BinOpLeftError (TypeMismatch Int (Once.Type.ν-type F))) , tt
  -- left Int, right non-Int → BinOpRightError
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (failure err , _) = failure (BinOpRightError err) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success Unit   _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Unit)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success Void   _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Void)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success Str    _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Str)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success Buffer _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Buffer)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success (A Once.Type.* B)      _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int (A Once.Type.* B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success (A Once.Type.+ B)      _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int (A Once.Type.+ B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success (A Once.Type.⇒[ k ] B) _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int (A Once.Type.⇒[ k ] B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success (Once.Type.μ-type F)   _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int (Once.Type.μ-type F))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Int _ _ _ _ , _) (success (Once.Type.ν-type F)   _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int (Once.Type.ν-type F))) , tt
  -- both Int → op dispatch
  inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Int _ (Surface.add e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Int _ (Surface.sub e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Int _ (Surface.mul e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Int _ (Surface.div e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Int _ (Surface.mod' e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success (Unit Once.Type.+ Unit) _ (Surface.lt e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success (Unit Once.Type.+ Unit) _ (Surface.le e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success (Unit Once.Type.+ Unit) _ (Surface.gt e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success (Unit Once.Type.+ Unit) _ (Surface.ge e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success (Unit Once.Type.+ Unit) _ (Surface.eq e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success (Unit Once.Type.+ Unit) _ (Surface.ne e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂

  ----------------------------------------------------------------------
  -- PLAN 0.75 F4: `Float` ON THE LEFT SELECTS THE FLOAT FAMILY.
  --
  -- It used to be `BinOpLeftError (TypeMismatch Int Float)` with a catch-all
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
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (failure err , _) = failure (BinOpRightError err) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success Unit _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Unit)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success Void _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Void)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success Str _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Str)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success Buffer _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Buffer)) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success (A Once.Type.* B) _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float (A Once.Type.* B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success (A Once.Type.+ B) _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float (A Once.Type.+ B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success (A Once.Type.⇒[ k ] B) _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float (A Once.Type.⇒[ k ] B))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success (Once.Type.μ-type F) _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float (Once.Type.μ-type F))) , tt
  inferElabV-RBinOp-aux ctx op e₁ e₂ (success Float _ _ _ _ , _) (success (Once.Type.ν-type F) _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float (Once.Type.ν-type F))) , tt
  -- both Float → op dispatch. Only `+`, `−` and `×` exist here
  -- (`isFloatArithmeticOp`), and `Once.Float.Arith` records why.
  inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fadd e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fsub e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fmul e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fdiv e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float refl w₁ w₂
  -- `%` still has no float lowering — IEEE's `fmod` is a different function and
  -- needs its own decision — and a float comparison needs the Bool encoding
  -- `Int`'s own comparisons are STILL postulated over. Those six keep exactly
  -- the error they gave before this clause family existed.
  inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpLeftError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpLeftError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpLeftError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpLeftError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpLeftError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpLeftError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpLeftError (TypeMismatch Int Float)) , tt

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
  inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fadd (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-il refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fsub (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-il refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fmul (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-il refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Int Ψ₁ e₁E d₁ f₁ , w₁) (success Float Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fdiv (Surface.i2f e₁E) e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-il refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpAdd e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fadd e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-ir refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpSub e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fsub e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-ir refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpMul e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fmul e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-ir refl w₁ w₂
  inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Float Ψ₁ e₁E d₁ f₁ , w₁) (success Int Ψ₂ e₂E d₂ f₂ , w₂) = success Float _ (Surface.fdiv e₁E (Surface.i2f e₂E)) (d₁ ⊔ d₂) f₂ , t-binop-arith-float-ir refl w₁ w₂
  -- `/`, `%` and the comparisons keep the error they gave before.
  inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpDiv e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpMod e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpLt e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpLe e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpGt e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpGe e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpEq e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt
  inferElabV-RBinOp-aux ctx Raw.OpNe e₁ e₂ (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) = failure (BinOpRightError (TypeMismatch Float Int)) , tt

  inferElabV-RLet-aux ctx x e₁ e₂ (failure err , _) = failure err , tt
  inferElabV-RLet-aux ctx x e₁ e₂ (success A Ψ₁ e₁E d₁ f₁ , w₁) =
    inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ w₁ (inferElabV (extendNamedCtx ctx x A) e₂)
  inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ w₁ (failure err , _) = failure err , tt
  inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ w₁ (success B (q ∷ᵘ Ψ₂) e₂E d₂ f₂ , w₂) =
    success B _ (Surface.let' e₁E e₂E) (d₁ ⊔ suc d₂) f₂ , t-let w₁ w₂

  -- RDestruct bodies (de-withed). `-aux` dispatches the scrutinee type;
  -- non-sum scrutinees fail; a sum `A + B` feeds `-auxL` with the left branch
  -- inferred in `ctx,xL:A`. `-auxL` feeds `-auxR` with the right branch in
  -- `ctx,xR:B`. `-auxR` matches branch types (`C₁ ≟T C₂`) and emits `t-case`.
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (failure err , _)            = failure err , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Unit   _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Void   _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Int    _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Float  _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Str    _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success Buffer _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (_ Once.Type.* _) _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (Once.Type.μ-type _) _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (Once.Type.ν-type _) _ _ _ _ , _) = failure CaseScrutineeNotSum , tt
  inferElabV-RDestruct-aux ctx scrut xL eL xR eR (success (A Once.Type.+ B) Ψs scrutE ds fs , wS) =
    inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs wS (inferElabV (extendNamedCtx ctx xL A) eL)
  inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs wS (failure err , _) = failure err , tt
  inferElabV-RDestruct-auxL ctx scrut xL eL xR eR A B scrutE ds fs wS (success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , wL) =
    inferElabV-RDestruct-auxR ctx scrut xL eL xR eR A B scrutE ds fs wS eLE dL fL wL (inferElabV (extendNamedCtx ctx xR B) eR)
  inferElabV-RDestruct-auxR ctx scrut xL eL xR eR A B scrutE ds fs wS eLE dL fL wL (failure err , _) = failure err , tt
  inferElabV-RDestruct-auxR ctx scrut xL eL xR eR A B scrutE ds fs wS {C₁ = C₁} eLE dL fL wL (success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , wR)
    with C₁ ≟T C₂
  ... | yes refl = success C₁ _ (Surface.case' scrutE eLE eRE) (ds ⊔ suc dL ⊔ suc dR) fR , t-case wS wL wR
  ... | no _     = failure CaseBranchMismatch , tt

  inferElabV-RVar-lookup-aux ctx x (just (A , Ψ , eV)) eq-loc _ _ =
    success A Ψ (Surface.svar→expr eV) 0 (NamedCtx.freshCounter ctx) , t-var-local eq-loc
  inferElabV-RVar-lookup-aux ctx x nothing eq-loc (just ty) eq-imp =
    inferElabV-RVar-import-value-aux ctx x eq-loc ty eq-imp (genWord? x) refl (isConcrete? ty) refl
  -- Plan 0.58 / D071: both lookups failed — try the telescope (poly) fallback:
  -- a GROUND own-module def infers at its declared type; otherwise fail.
  inferElabV-RVar-lookup-aux ctx x nothing eq-loc nothing eq-imp =
    inferElabV-RVar-poly-aux ctx x (classifyBareBuiltin x) refl

  inferElabV-RVar-import-value-aux ctx x eq-loc ty eq-imp (no ¬gw) _ (just conc) _ =
    success ty _ (Surface.sigOp (bare x) conc) 0 (NamedCtx.freshCounter ctx)
    , t-var-import ¬gw eq-loc eq-imp conc
  inferElabV-RVar-import-value-aux ctx x eq-loc ty eq-imp (no _) _ nothing _ =
    failure (NonConcreteSigOpType x ty) , tt
  inferElabV-RVar-import-value-aux ctx x eq-loc ty eq-imp (yes _) _ _ _ =
    failure (UnboundVariable x) , tt

  inferElabV-RApp-other-aux ctx f x (just _) _ =
    failure (BuiltinTypeMismatch "unreachable: ahv-other ⇒ classifyAppHead nothing") , tt
  inferElabV-RApp-other-aux ctx f x nothing eqAH with inferElabV ctx f
  ... | failure err , _ = failure err , tt
  ... | success Unit       _ _ _ _ , _ = failure (NotFunction Unit) , tt
  ... | success Void       _ _ _ _ , _ = failure (NotFunction Void) , tt
  ... | success Int        _ _ _ _ , _ = failure (NotFunction Int) , tt
  ... | success Float      _ _ _ _ , _ = failure (NotFunction Float) , tt
  ... | success Str        _ _ _ _ , _ = failure (NotFunction Str) , tt
  ... | success Buffer     _ _ _ _ , _ = failure (NotFunction Buffer) , tt
  ... | success (A Once.Type.* B) _ _ _ _ , _ = failure (NotFunction (A Once.Type.* B)) , tt
  ... | success (A Once.Type.+ B) _ _ _ _ , _ = failure (NotFunction (A Once.Type.+ B)) , tt
  ... | success (Once.Type.μ-type F) _ _ _ _ , _ = failure (NotFunction (Once.Type.μ-type F)) , tt
  ... | success (Once.Type.ν-type F) _ _ _ _ , _ = failure (NotFunction (Once.Type.ν-type F)) , tt
  ... | success (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) Ψ₁ fE df ff , wF with checkElabV ctx x A
  ...   | failure err , _ = failure err , tt
  ...   | success Ψ₂ xE dx fx , wX =
          success B _ (Surface.app fE xE) (df ⊔ dx) fx , t-app eqAH wF wX
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) Ψ₁ fE df ff , wF with checkElabV ctx x A
  ...   | failure err , _ = failure err , tt
  ...   | success Ψ₂ xE dx fx , wX =
          success (Unit Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) _ (Surface.effApp fE xE) (df ⊔ dx) fx , t-effApp eqAH wF wX
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.eff ] B) _ _ _ _ , _ = failure (NotFunction (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.eff ] B)) , tt
  inferElabV-RApp-other-aux ctx f x nothing eqAH | success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.eff ] B) _ _ _ _ , _ = failure (NotFunction (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.eff ] B)) , tt

  -- ahv-id : argument can have any type, result has the same type.
  inferElabV-RApp-dispatch ctx f arg ahv-id _ with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success T Ψ argE d fr , w =
    success T _ (Surface.morph-app IR.id argE) (suc d) fr , t-id-app w
  -- ahv-fst : argument must have product type.
  inferElabV-RApp-dispatch ctx f arg ahv-fst _ with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success (A Once.Type.* B) Ψ argE d fr , w =
    success A _ (Surface.morph-app (IR.fst) argE) (suc d) fr , t-fst-app w
  ... | success Unit _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success Void _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success Int _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success Float _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success Str _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success Buffer _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success (_ Once.Type.+ _) _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success (Once.Type.μ-type _) _ _ _ _ , _ = failure FstNeedsPair , tt
  ... | success (Once.Type.ν-type _) _ _ _ _ , _ = failure FstNeedsPair , tt
  -- ahv-snd : argument must have product type.
  inferElabV-RApp-dispatch ctx f arg ahv-snd _ with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success (A Once.Type.* B) Ψ argE d fr , w =
    success B _ (Surface.morph-app (IR.snd) argE) (suc d) fr , t-snd-app w
  ... | success Unit _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success Void _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success Int _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success Float _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success Str _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success Buffer _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success (_ Once.Type.+ _) _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success (Once.Type.μ-type _) _ _ _ _ , _ = failure SndNeedsPair , tt
  ... | success (Once.Type.ν-type _) _ _ _ _ , _ = failure SndNeedsPair , tt
  -- ahv-terminal : any-typed argument, Unit result.
  inferElabV-RApp-dispatch ctx f arg ahv-terminal _ with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success T Ψ argE d fr , w =
    success Unit _ (Surface.morph-app IR.terminal argE) (suc d) fr , t-terminal-app w
  -- ahv-apply : argument must be `(A ⇒[Many,pure] B) * A`.
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A') Ψ argE d fr , w with A ≟T A'
  ...   | yes refl =
    success B _ (Surface.morph-app IR.apply argE) (suc d) fr , t-apply-app-infer w
  ...   | no _ =
    failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success Unit _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success Void _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success Int _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success Float _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success Str _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success Buffer _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (_ Once.Type.+ _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Unit Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Void Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Int Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Float Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Str Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Buffer Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success ((_ Once.Type.* _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success ((_ Once.Type.+ _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success ((_ Once.Type.⇒[ Once.Type.mk-kind _ Once.Type.eff ] _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success ((_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.pure ] _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success ((_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.pure ] _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success ((Once.Type.μ-type _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success ((Once.Type.ν-type _) Once.Type.* _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Once.Type.μ-type _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ | success (Once.Type.ν-type _) _ _ _ _ , _ = failure (BuiltinTypeMismatch "apply") , tt
  -- ahv-inl / ahv-inr / ahv-initial : check-only builtins, infer fails.
  inferElabV-RApp-dispatch ctx f arg ahv-inl     _ = failure InlInInferMode , tt
  inferElabV-RApp-dispatch ctx f arg ahv-inr     _ = failure InrInInferMode , tt
  inferElabV-RApp-dispatch ctx f arg ahv-initial _ = failure InitialInInferMode , tt
  -- ahv-pair-applied / ahv-compose-applied / ahv-curry : check-only.
  inferElabV-RApp-dispatch ctx f arg ahv-pair-applied    _ = failure (BuiltinTypeMismatch "pair") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-compose-applied _ = failure (BuiltinTypeMismatch "compose") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-case-applied    _ = failure (BuiltinTypeMismatch "case") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-In              _ = failure (BuiltinTypeMismatch "In") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-cata            _ = failure (BuiltinTypeMismatch "cata") , tt
  inferElabV-RApp-dispatch ctx f arg ahv-curry           _ = failure (BuiltinTypeMismatch "curry") , tt
  -- ahv-other : generic application via `inferElabV-RApp-other`.
  inferElabV-RApp-dispatch ctx f arg ahv-other _ = inferElabV-RApp-other ctx f arg

  -- checkElabV's RApp dispatch — mirror of inferElabV-RApp-dispatch.
  -- Plan 0.52 (OCP-0008): infer-then-check builtin-app heads route through the
  -- NAMED embedOrSubsume (was an inline with-tree). `with`-bind the inferElabV
  -- result (so the termination checker sees the recursive call) and hand it to
  -- embedOrSubsume; on infer failure, propagate failure.
  checkElabV-RApp-dispatch ctx f arg T ahv-id _       with inferElabV ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err , _) = failure err , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-fst _      with inferElabV ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err , _) = failure err , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-snd _      with inferElabV ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err , _) = failure err , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-terminal _ with inferElabV ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err , _) = failure err , tt
  -- ahv-inl: T must be sum type A+B; check arg at A.
  -- D127: `inl arg` / `inr arg` at an ARROW type are no longer lifts; the
  -- value-type dispatch below is the only route.
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ with T
  ... | (A Once.Type.+ B) with checkElabV ctx arg A
  ...   | failure err , _ = failure err , tt
  ...   | success Ψ argE d fr , w =
          success _ (Surface.morph-app (IR.inl IR.Heap) argE) (suc d) fr , t-inl-app-check w
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Unit = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Void = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Int = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Float = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Str = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | Buffer = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (_ Once.Type.* _) = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (_ Once.Type.⇒[ _ ] _) = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (μ-type _) = failure InlNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ | (ν-type _) = failure InlNeedsSumType , tt
  -- ahv-inr: T must be sum type A+B; check arg at B.
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ with T
  ... | (A Once.Type.+ B) with checkElabV ctx arg B
  ...   | failure err , _ = failure err , tt
  ...   | success Ψ argE d fr , w =
          success _ (Surface.morph-app (IR.inr IR.Heap) argE) (suc d) fr , t-inr-app-check w
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Unit = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Void = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Int = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Float = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Str = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | Buffer = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (_ Once.Type.* _) = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (_ Once.Type.⇒[ _ ] _) = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (μ-type _) = failure InrNeedsSumType , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-inr _ | (ν-type _) = failure InrNeedsSumType , tt
  -- ahv-initial: arg must be Void; result has any expected T.
  checkElabV-RApp-dispatch ctx f arg T ahv-initial _ with checkElabV ctx arg Once.Type.Void
  ... | failure err , _ = failure err , tt
  ... | success Ψ argE d fr , w =
        success _ (Surface.morph-app (IR.initial) argE) (suc d) fr , t-initial-app-check w
  -- Helper-applied branches.
  checkElabV-RApp-dispatch ctx f arg T ahv-pair-applied _ = checkPair ctx f arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-compose-applied _ = checkCompose ctx f arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-case-applied _ = checkCase ctx f arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-In _ = checkIn ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-cata _ = checkCata ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-curry _ = checkCurry ctx arg T
  -- Plan 0.52 (OCP-0008): `apply p` infers (t-apply-app-infer), so route its
  -- CHECK through the named embedOrSubsume — this ADDS the subsume case (apply at
  -- an eff arrow) that the old `checkApply` (exact T ≟ codomain) rejected.
  checkElabV-RApp-dispatch ctx f arg T ahv-apply _ with inferElabV ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  ... | (failure err , _) = failure err , tt
  -- ahv-other: infer-then-check via the NAMED `embedOrSubsume` (OCP-0008: route
  -- through the named combinator, not an inline with-tree, so completeness can
  -- reason through it); on infer failure, arg-driven application.
  checkElabV-RApp-dispatch ctx f arg T ahv-other _ with inferElabV ctx (Raw.RApp f arg)
  ... | r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RApp f arg) T r
  checkElabV-RApp-dispatch ctx f arg T ahv-other _ | failure errInfer , _ =
    checkElabV-RApp-other-argdriven-aux ctx f arg T errInfer (classifyAppHead f) refl

  checkElabV-RApp-other-argdriven-aux ctx f arg T errInfer (just _) eqAH = failure errInfer , tt
  -- Plan 0.52 (pure⊑eff): dispatch on the target via classifyEffArrow. At an EFF
  -- arrow, check `f` at its PURE codomain (its natural type — no nested
  -- subsumption) and wrap the app in arr'/t-subsume; otherwise the plain app.
  checkElabV-RApp-other-argdriven-aux ctx f arg T errInfer nothing eqAH with inferElabV ctx arg
  ... | failure errArg , _ = failure errArg , tt
  ... | success X Ψx argE dx frx , wArg with classifyEffArrow T
  ...   | eav-eff A B with checkElabV ctx f (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ]
                                              (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B))
  ...     | failure err , _ = failure err , tt
  ...     | success Ψf fE df frf , wF =
            success _ (Surface.arr' (Surface.app fE argE)) (suc (df ⊔ dx)) frf
            , t-subsume (t-arg-driven-app-check eqAH wArg wF)
  checkElabV-RApp-other-argdriven-aux ctx f arg T errInfer nothing eqAH | success X Ψx argE dx frx , wArg | eav-other _
          with checkElabV ctx f (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T)
  ...   | failure err , _ = failure err , tt
  ...   | success Ψf fE df frf , wF =
          success _ (Surface.app fE argE) (suc (df ⊔ dx)) frf , t-arg-driven-app-check eqAH wArg wF

  -- bbc-X failure-branch aux bodies. Each pattern-matches on T to the
  -- canonical builtin shape and on the lookup results. Success iff
  -- T = canonical & both lookups nothing & inner type-checks pass.
  checkElabV-RVar-bbc-id-failure-aux ctx (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Y) err with X ≟T Y
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism IR.id) 0 (NamedCtx.freshCounter ctx) , t-id-check
  ... | no _ = failure (BuiltinTypeMismatch "id") , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Unit err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Void err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Int err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Float err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Str err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Buffer err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.* _) err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.+ _) err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (Once.Type.μ-type _) err = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (Once.Type.ν-type _) err = failure err , tt

  checkElabV-RVar-bbc-fst-failure-aux ctx ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A') err with A ≟T A'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism IR.fst) 0 (NamedCtx.freshCounter ctx) , t-fst-check
  ... | no _ = failure (BuiltinTypeMismatch "fst") , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Unit err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Void err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Int err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Float err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Str err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Buffer err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Unit Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Void Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Int Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Float Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Str Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Buffer Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.+ _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.⇒[ _ ] _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((Once.Type.μ-type _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((Once.Type.ν-type _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (_ Once.Type.* _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (_ Once.Type.+ _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Once.Type.μ-type _) err = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Once.Type.ν-type _) err = failure err , tt

  -- bbc-snd: canonical T = (A * B) ⇒[Many,pure] B'
  checkElabV-RVar-bbc-snd-failure-aux ctx ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B') err with B ≟T B'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism IR.snd) 0 (NamedCtx.freshCounter ctx) , t-snd-check
  ... | no _ = failure (BuiltinTypeMismatch "snd") , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Unit err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Void err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Int err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Float err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Str err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Buffer err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Unit Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Void Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Int Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Float Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Str Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Buffer Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.+ _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.⇒[ _ ] _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((Once.Type.μ-type _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((Once.Type.ν-type _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (_ Once.Type.* _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (_ Once.Type.+ _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Once.Type.μ-type _) err = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Once.Type.ν-type _) err = failure err , tt

  -- bbc-terminal: canonical T = A ⇒[Many,pure] Unit
  checkElabV-RVar-bbc-terminal-failure-aux ctx (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit) err =
    success Surface.zeroUsage (Surface.lift-morphism IR.terminal) 0 (NamedCtx.freshCounter ctx) , t-terminal-morph-check
  checkElabV-RVar-bbc-terminal-failure-aux ctx Unit err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Void err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Int err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Float err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Str err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Buffer err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.* _) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.+ _) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Void) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Int) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Float) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Str) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Buffer) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.* _)) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.+ _)) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.⇒[ _ ] _)) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.μ-type _)) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.ν-type _)) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] Unit) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] Unit) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (Once.Type.μ-type _) err = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (Once.Type.ν-type _) err = failure err , tt

  -- bbc-initial: canonical T = Void ⇒[Many,pure] A
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A) err =
    success Surface.zeroUsage (Surface.lift-morphism IR.initial) 0 (NamedCtx.freshCounter ctx) , t-initial-morph-check
  checkElabV-RVar-bbc-initial-failure-aux ctx Unit err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Void err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Int err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Float err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Str err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Buffer err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (_ Once.Type.* _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (_ Once.Type.+ _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Unit Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Int Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Float Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Str Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Buffer Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Type.+ _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Type.⇒[ _ ] _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((Once.Type.μ-type _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((Once.Type.ν-type _) Once.Type.⇒[ _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Once.Type.μ-type _) err = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Once.Type.ν-type _) err = failure err , tt

  -- bbc-inl: canonical T = A ⇒[Many,pure] (A' + B)
  checkElabV-RVar-bbc-inl-failure-aux ctx (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A' Once.Type.+ B)) err with A ≟T A'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism (IR.inl IR.Heap)) 0 (NamedCtx.freshCounter ctx) , t-inl-morph-check
  ... | no _ = failure (BuiltinTypeMismatch "inl") , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Unit err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Void err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Int err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Float err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Str err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Buffer err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.* _) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.+ _) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Unit) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Void) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Int) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Float) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Str) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Buffer) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.* _)) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.⇒[ _ ] _)) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.μ-type _)) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.ν-type _)) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] (_ Once.Type.+ _)) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] (_ Once.Type.+ _)) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (Once.Type.μ-type _) err = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (Once.Type.ν-type _) err = failure err , tt

  -- bbc-inr: canonical T = B ⇒[Many,pure] (A + B')
  checkElabV-RVar-bbc-inr-failure-aux ctx (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A Once.Type.+ B')) err with B ≟T B'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism (IR.inr IR.Heap)) 0 (NamedCtx.freshCounter ctx) , t-inr-morph-check
  ... | no _ = failure (BuiltinTypeMismatch "inr") , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Unit err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Void err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Int err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Float err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Str err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Buffer err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.* _) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.+ _) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Unit) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Void) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Int) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Float) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Str) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Buffer) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.* _)) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.⇒[ _ ] _)) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.μ-type _)) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.ν-type _)) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] (_ Once.Type.+ _)) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] (_ Once.Type.+ _)) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (Once.Type.μ-type _) err = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (Once.Type.ν-type _) err = failure err , tt

  -- RFloat: F4's decision, made once and passed in.
  --
  -- The accepted branch hands the witness straight to BOTH the Surface node
  -- and `t-float` — the same evidence, so the elaborated term and its typing
  -- derivation cannot disagree about which literals are legal.
  --
  -- The rejected branch is a REAL ERROR carrying the digits the user wrote,
  -- not a rounded value. That is the whole point of plan 0.71: `0.1` does not
  -- become the nearest double, it fails to compile.
  -- TOTAL. `FloatNotRepresentable` is unreachable from here now; the literal
  -- always elaborates and the target rounds it.
  inferElabV-RFloat-aux ctx i f l p =
    success Float _ (Surface.float (decimalOf i f l)) 0 (NamedCtx.freshCounter ctx)
    , t-float i f l p

  -- RInt: value-lift on a pure-arrow-to-Int target, else generic infer+match.
  -- `refl` refines `T` to the arrow so `t-value-lift (g-int n)` types; the
  -- `nothing` branch reproduces the old generic clause for RInt verbatim.
  -- RFloat: value-lift on a pure-arrow-to-Float target; otherwise embed at
  -- `Float` or report a genuine type mismatch. The only failure left is a type
  -- mismatch — representability is no longer a way to fail.
  checkElabV-RFloat-aux ctx i f l p T with T ≟T Once.Type.Float
  ... | yes refl = success Surface.zeroUsage (Surface.float (decimalOf i f l)) 0 (NamedCtx.freshCounter ctx)
                 , t-embed (t-float i f l p)
  ... | no _     = failure (TypeMismatch T Once.Type.Float) , tt

  checkElabV-RInt-aux ctx n T with inferElabV ctx (Raw.RInt n)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt

  -- RPair: product → bidirectional component check (checkPairLit);
  -- pure-arrow-to-product → value-lift via checkG (inspectCheckG); else the
  -- generic infer+match. The latter two are the old clauses verbatim.
  checkElabV-RPair-aux ctx a b _ (rpt-prod A B) = checkPairLit ctx a b A B
  -- D127: a pair literal at an ARROW type is no longer a lift.
  checkElabV-RPair-aux ctx a b _ (rpt-vlift X A B π) =
    failure (TypeMismatch (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A Once.Type.* B))
                          (A Once.Type.* B)) , tt
  checkElabV-RPair-aux ctx a b _ (rpt-other T) with inferElabV ctx (Raw.RPair a b)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt

  -- Per-bbc-X auxes: pattern-match on the verified inferElabV result
  -- (Σ-pair). The success path uses t-embed of the witness; the
  -- failure path delegates to bbc-X-failure-aux.
  checkElabV-RVar-bbc-id-aux ctx T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RResolved (gen "id")) T r
  checkElabV-RVar-bbc-id-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-id-failure-aux ctx T err

  checkElabV-RVar-bbc-fst-aux ctx T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RResolved (gen "fst")) T r
  checkElabV-RVar-bbc-fst-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-fst-failure-aux ctx T err

  checkElabV-RVar-bbc-snd-aux ctx T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RResolved (gen "snd")) T r
  checkElabV-RVar-bbc-snd-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-snd-failure-aux ctx T err

  checkElabV-RVar-bbc-terminal-aux ctx T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RResolved (gen "terminal")) T r
  checkElabV-RVar-bbc-terminal-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-terminal-failure-aux ctx T err

  checkElabV-RVar-bbc-initial-aux ctx T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RResolved (gen "initial")) T r
  checkElabV-RVar-bbc-initial-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-initial-failure-aux ctx T err

  checkElabV-RVar-bbc-inl-aux ctx T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RResolved (gen "inl")) T r
  checkElabV-RVar-bbc-inl-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-inl-failure-aux ctx T err

  checkElabV-RVar-bbc-inr-aux ctx T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RResolved (gen "inr")) T r
  checkElabV-RVar-bbc-inr-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-inr-failure-aux ctx T err

  -- bbc-other: success-via-infer mirrors the others; failure goes
  -- through lookupPoly fallback (still postulate-witnessed).
  checkElabV-RVar-bbc-other-aux ctx x T r@(success _ _ _ _ _ , _) = embedOrSubsume ctx (Raw.RVar x) T r
  checkElabV-RVar-bbc-other-aux ctx x T (failure err , _) with lookupPoly (NamedCtx.polys ctx) x
  ... | nothing = failure err , tt
  ... | just _  = success Surface.zeroUsage (Surface.poly x T) 0 (NamedCtx.freshCounter ctx) , bbc-other-poly-witness ctx x T

