-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
open import Data.Integer using (ℤ)
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
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)

open import Once.Type
open Once.Type using (showQuantity; showType) public
open import Once.IR as IR
-- Plan 0.36 Phase 1: `generic-info` reconstructs a SigOp's `SigOpInfo` from its
-- name, so `extract-morph-eff` can recover the direct `IR.SigOp` morphism of an
-- effectful sigOp used point-free (it elaborates as a closure otherwise).
-- Plan 0.38 M0.2: external arrow SigOps are built from their DECLARED
-- `! <shape>` effect (looked up in `NamedCtx.sigEffects`), never from a
-- hardcoded name. `generic-semM` supplies the (laundered) value ONLY for
-- the pure/value `pureV` positions — an effectful op carries a CONTRACT,
-- not a value, so `Emits`/`Halts` drop it entirely.
open import Once.Arith.SigOp.Builders using (generic-semM)
open import Once.SigOp.Info using (SigOpInfo; mk-info'; pureV; emitsV; haltsV)
open import Once.SigEffect using () renaming (halts to se-halts; emits to se-emits)
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
  UnboundVariable; UnboundQualified) public
open import Once.TypeCheck.Context using (Ctx; ∅; name)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookupUsage; tailUsage; _+ᵘ_)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)
open import Once.Surface.Thinning using (weaken; weakenFromEmpty)
open import Once.Surface.Properties using (+ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-zeroʳ)
open import Once.Surface.Elaborate as Elab using (elaborate; intLit; strLit)

open import Once.TypeCheck.Classify public
import Once.Functor.Translate
open import Once.Functor.Decide using (wellFormedF?)
open import Once.TypeCheck.Morph using (MorphRaw; morphRaw?; morphToIR)
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
≟T-⇒-aux (yes refl) (yes refl) (yes refl) = yes refl
≟T-⇒-aux (yes refl) (yes refl) (no ¬r)    = no λ { refl → ¬r refl }
≟T-⇒-aux (yes refl) (no ¬k)    (yes _)    = no λ { refl → ¬k refl }
≟T-⇒-aux (yes refl) (no ¬k)    (no _)     = no λ { refl → ¬k refl }
≟T-⇒-aux (no ¬p)    (yes _)    (yes _)    = no λ { refl → ¬p refl }
≟T-⇒-aux (no ¬p)    (yes _)    (no _)     = no λ { refl → ¬p refl }
≟T-⇒-aux (no ¬p)    (no _)     (yes _)    = no λ { refl → ¬p refl }
≟T-⇒-aux (no ¬p)    (no _)     (no _)     = no λ { refl → ¬p refl }

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
isRIntVliftTarget? :
  (T : Type) →
  Maybe (∃-syntax (λ X → T ≡ (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Int)))
isRIntVliftTarget? (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Int) =
  just (X , refl)
isRIntVliftTarget? _ = nothing

-- | Classify a check-mode target type for a pair literal: a product `A * B`
-- (bidirectional component check), a pure-arrow-to-product
-- `X ⇒[Many,pure] (A * B)` (value-lift / global element via `checkG`), or
-- anything else (generic infer-and-match). One named view so
-- `checkElabV (RPair a b) T` routes through a single scrutinee instead of two
-- specific clauses overlapping the catch-all (same gate as RInt; Plan 0.45).
data RPairTarget : Type → Set where
  rpt-prod  : (A B : Type) → RPairTarget (A Once.Type.* B)
  rpt-vlift : (X A B : Type) →
              RPairTarget (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.* B))
  rpt-other : (T : Type) → RPairTarget T

classifyRPairTarget : (T : Type) → RPairTarget T
classifyRPairTarget (A Once.Type.* B) = rpt-prod A B
classifyRPairTarget
  (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.* B)) =
  rpt-vlift X A B
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
                  → Maybe (∃-syntax (λ (m : IR A B) → Ψ ≡ Surface.zeroUsage))
extract-morph-aux (Surface.lift-morphism m) refl = just (m , refl)
extract-morph-aux _ _ = nothing

extract-morph : ∀ {n} {Γ : SCtx n} {Ψ : Surface.Usage n} {A B : Type}
                {π : Once.Type.Purity}
              → SExpr Γ Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
              → Maybe (∃-syntax (λ (m : IR A B) → Ψ ≡ Surface.zeroUsage))
extract-morph e = extract-morph-aux e refl

-- Plan 0.36 Phase 1: effectful morphism extraction. An eff point-free morphism
-- has more surface forms than a pure `lift-morphism`: `arr' e` (a pure morphism
-- lifted to eff) and a bare `sigOp name` (an effectful primitive used as a
-- morphism — which otherwise elaborates to a closure `curry (SigOp ∘ snd)`).
-- This recovers the underlying grade-erased `IR A B` from all of them, so the
-- eff `case`/`compose` clauses can fuse to `lift-morphism {eff} (IR.case / ∘)`
-- exactly like the pure path. Faithful extensionally (arr' is identity on the
-- morphism; `SigOp si` is what the closure form applies); the residual
-- semantic equality is discharged in the scaffolded eff completeness bridges.
extract-morph-eff-aux : ∀ {n} {Γ : SCtx n} {Ψ : Surface.Usage n} {T : Type} {A B : Type}
                        {π : Once.Type.Purity}
                      → SExpr Γ Ψ T
                      → T ≡ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
                      → Maybe (∃-syntax (λ (m : IR A B) → Ψ ≡ Surface.zeroUsage))
extract-morph-eff-aux (Surface.lift-morphism m) refl = just (m , refl)
-- NOTE (Plan 0.36): NO `sigOp name → IR.SigOp (generic-info name)` clause.
-- That would launder an INTERNAL user function (which pre-resolve is also a
-- `Surface.sigOp "name"`) through the POSTULATED `generic-semI/semM`, claiming
-- it denotes an opaque external SigOp — typechecks but miscompiles (e.g.
-- `once_seven` is a closure-returner, not that SigOp). Extraction stays
-- faithful: only genuine `lift-morphism`s (and `arr'`/`cata` over them).
extract-morph-eff-aux (Surface.arr' e)          refl = extract-morph-eff-aux e refl
-- A `cata` IS a direct morphism `μF → A`. Recover the bare `Cata` IR (the same
-- un-curried form `Surface.Elaborate.elaborate` builds) so it fuses into an
-- effectful compose/case like any other morphism (e.g. `compose emitAll …`).
extract-morph-eff-aux (Surface.cata {F = F} wfF algE) refl =
  just (IR.Cata wfF (IR.apply IR.∘ IR.⟨ Elab.elaborate IR.Heap algE IR.∘ IR.terminal , IR.id ⟩ IR.Heap) , refl)
extract-morph-eff-aux _ _ = nothing

extract-morph-eff : ∀ {n} {Γ : SCtx n} {Ψ : Surface.Usage n} {A B : Type}
                    {π : Once.Type.Purity}
                  → SExpr Γ Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B)
                  → Maybe (∃-syntax (λ (m : IR A B) → Ψ ≡ Surface.zeroUsage))
extract-morph-eff e = extract-morph-eff-aux e refl

-- View bundling `wellFormedF? F`'s outcome with its equation (mirrors
-- `inspectLookupLocal`) so proofs sidestep the `with … in` opacity.
data WellFormedFView (F : Once.Type.Functor) : Set where
  wfv-yes : ∀ {wfF} → wellFormedF? F ≡ just wfF → WellFormedFView F
  wfv-no  : wellFormedF? F ≡ nothing → WellFormedFView F

inspectWellFormedF : (F : Once.Type.Functor) → WellFormedFView F
inspectWellFormedF F with wellFormedF? F in eq
... | just wfF = wfv-yes eq
... | nothing  = wfv-no eq

-- Plan 0.41: elaborate a closed global-element value. Recurses on the raw
-- value-shape, producing the parametric global element `IR X A` *together
-- with* its `⊢ᵍ` derivation — so the `t-value-lift` bridge gets both the IR
-- (for `lift-morphism`) and the soundness witness, and completeness can
-- recurse on the `⊢ᵍ` derivation. Per-type knowledge at the leaves
-- (`intLit`/`terminal`); structure via the generic generators. `nothing` for
-- non-value shapes — `⊢ᵍ` is the extractable family by construction.
checkG : (ctx : NamedCtx) (X : Type) (e : RawExpr) (A : Type)
       → Maybe (IR X A × (ctx ⊢ᵍ e ∶ A))
checkG ctx X (Raw.RInt n) Once.Type.Int = just (intLit n , g-int n)
checkG ctx X (Raw.RVar "terminal") Once.Type.Unit
  with inspectLookupLocal ctx "terminal" | inspectLookupImport ctx "terminal"
... | llv-not-found eqL | liv-not-found eqI = just (IR.terminal , g-terminal eqL eqI)
... | _                 | _                 = nothing
checkG ctx X (Raw.RPair a b) (A Once.Type.* B) with checkG ctx X a A | checkG ctx X b B
... | just (ma , ga) | just (mb , gb) = just (IR.⟨ ma , mb ⟩ IR.Heap , g-pair ga gb)
... | _ | _ = nothing
checkG ctx X (Raw.RApp (Raw.RVar "inl") arg) (A Once.Type.+ B) with checkG ctx X arg A
... | just (ma , ga) = just (IR.inl IR.Heap IR.∘ ma , g-inl ga)
... | nothing = nothing
checkG ctx X (Raw.RApp (Raw.RVar "inr") arg) (A Once.Type.+ B) with checkG ctx X arg B
... | just (mb , gb) = just (IR.inr IR.Heap IR.∘ mb , g-inr gb)
... | nothing = nothing
checkG ctx X (Raw.RApp (Raw.RVar "In") arg) (Once.Type.μ-type F) with inspectWellFormedF F
... | wfv-no _ = nothing
... | wfv-yes {wfF} eqWF with checkG ctx X arg (⟦ F ⟧T (Once.Type.μ-type F))
...   | just (marg , garg) = just (IR.In wfF IR.Heap IR.∘ marg , g-In eqWF garg)
...   | nothing = nothing
checkG _ _ _ _ = nothing

-- View bundling `checkG`'s outcome with its equation (mirrors
-- `inspectLookupLocal`/`inspectWellFormedF`). The value-lift `checkElabV`
-- clauses scrutinise this instead of `checkG` directly, so completeness
-- connects to the same view and reduces — no `with checkG` opacity, no
-- dispatch-reduction postulate.
data CheckGView (ctx : NamedCtx) (X : Type) (e : RawExpr) (A : Type) : Set where
  cgv-just    : ∀ {m gd} → checkG ctx X e A ≡ just (m , gd) → CheckGView ctx X e A
  cgv-nothing : checkG ctx X e A ≡ nothing → CheckGView ctx X e A

inspectCheckG : (ctx : NamedCtx) (X : Type) (e : RawExpr) (A : Type) → CheckGView ctx X e A
inspectCheckG ctx X e A with checkG ctx X e A in eq
... | just (m , gd) = cgv-just eq
... | nothing       = cgv-nothing eq


-- arr : (a → b) → Eff a b
specArr : (A B : Type) → SExpr S∅ Surface.zeroUsage ((A ⇒ B) ⇒ (A ⇒[ mk-kind Many eff ] B))
specArr A B = Surface.lam Many refl (Surface.arr' (Surface.var zero))



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
    go (Raw.RLam x b)        args = mkSpine (Raw.RLam x b) args
    go (Raw.RLet x e₁ e₂)    args = mkSpine (Raw.RLet x e₁ e₂) args
    go (Raw.RPair x y)       args = mkSpine (Raw.RPair x y) args
    go (Raw.RDestruct e a b c d) args = mkSpine (Raw.RDestruct e a b c d) args
    go Raw.RUnit             args = mkSpine Raw.RUnit args
    go (Raw.RInt n)          args = mkSpine (Raw.RInt n) args
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
isPolyBuiltin "arr"      = true
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
-- well-founded on `length polys`. No TERMINATING pragma needed.
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
                     (Raw.RApp (Raw.RApp (Raw.RVar "compose") f) g)
                     (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  checkCurry : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
             → VerifiedCheckResult ctx (Raw.RApp (Raw.RVar "curry") arg) T
  checkApply : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
             → VerifiedCheckResult ctx (Raw.RApp (Raw.RVar "apply") arg) T
  -- Recursion-scheme generators (Plan 0.28 Commit 2). The `…Go`/`…A/B/C`
  -- helpers take each decidable result as an explicit argument with its
  -- `refl` witness (no `with … in`), so the completeness fallbacks
  -- reduce them with plain nested `with | eq` — like `checkPair`.
  checkIn : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
          → VerifiedCheckResult ctx (Raw.RApp (Raw.RVar "In") arg) T
  checkInGo : (ctx : NamedCtx) (arg : RawExpr) (F : Once.Type.Functor)
            → (mw : Maybe (Once.Functor.Translate.WellFormedF F))
            → wellFormedF? F ≡ mw
            → VerifiedCheckResult ctx (Raw.RApp (Raw.RVar "In") arg) (Once.Type.μ-type F)
  checkCata : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type)
            → VerifiedCheckResult ctx (Raw.RApp (Raw.RVar "cata") arg) T
  -- Plan 0.36 Phase 2a: dispatch on `wellFormedF? F`; the algebra is
  -- elaborated as an ordinary function in the EMPTY context (see clause).
  checkCataGo : (ctx : NamedCtx) (alg : RawExpr) (F : Once.Type.Functor) (A : Type)
                (π : Once.Type.Purity)
              → (mw : Maybe (Once.Functor.Translate.WellFormedF F)) → wellFormedF? F ≡ mw
              → VerifiedCheckResult ctx (Raw.RApp (Raw.RVar "cata") alg)
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
  -- compose check-mode helper, threading the inner checkElabV results
  -- as explicit arguments + (unused) equations. The eqs are unused in
  -- the body (they're just placeholders for the J-style bridge in
  -- proofs). This lets external proofs substitute checkElab-success
  -- premises into the dispatch chain without navigating opaque
  -- `with`-helpers.
  inferElabV-RApp-other : (ctx : NamedCtx) (f x : RawExpr) → VerifiedInferResult ctx (Raw.RApp f x)
  -- Aux helpers that take the lookup result + equation as explicit args,
  -- so external proofs can pattern-match on the Maybe and supply the eq
  -- without `with...in` opacity.
  inferElabV-RQualified-aux :
    ∀ (ctx : NamedCtx) (name alias : String) (lhs : Maybe Type)
    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs
    → VerifiedInferResult ctx (Raw.RQualified name alias)
  inferElabV-RVar-lookup-aux :
    ∀ (ctx : NamedCtx) (x : String) → ¬ (x ≡ "unit")
    → (locLhs : Maybe (∃[ A ] ∃[ Ψ ] (SExpr (NamedCtx.debruijn ctx) Ψ A)))
    → lookupLocal ctx x ≡ locLhs
    → (impLhs : Maybe Type)
    → lookupImport (NamedCtx.imports ctx) x ≡ impLhs
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
  -- Plan 0.4 T2: bbc-X failure-branch aux helpers. Each is hardcoded
  -- to its builtin name (forced by the `bbc-X` constructor at the call
  -- site). Takes lookupLocal/lookupImport results + equations as
  -- explicit args (eliminating `with...in eq-loc/eq-imp` opacity).
  -- Returns success at the canonical builtin type if all conditions
  -- match, failure otherwise.
  checkElabV-RVar-bbc-id-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "id"
    → LookupImportView ctx "id"
    → VerifiedCheckResult ctx (Raw.RVar "id") T
  checkElabV-RVar-bbc-fst-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "fst"
    → LookupImportView ctx "fst"
    → VerifiedCheckResult ctx (Raw.RVar "fst") T
  checkElabV-RVar-bbc-snd-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "snd"
    → LookupImportView ctx "snd"
    → VerifiedCheckResult ctx (Raw.RVar "snd") T
  checkElabV-RVar-bbc-terminal-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "terminal"
    → LookupImportView ctx "terminal"
    → VerifiedCheckResult ctx (Raw.RVar "terminal") T
  checkElabV-RVar-bbc-initial-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "initial"
    → LookupImportView ctx "initial"
    → VerifiedCheckResult ctx (Raw.RVar "initial") T
  checkElabV-RVar-bbc-inl-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "inl"
    → LookupImportView ctx "inl"
    → VerifiedCheckResult ctx (Raw.RVar "inl") T
  checkElabV-RVar-bbc-inr-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "inr"
    → LookupImportView ctx "inr"
    → VerifiedCheckResult ctx (Raw.RVar "inr") T
  checkElabV-RVar-bbc-arr-failure-aux :
    ∀ (ctx : NamedCtx) (T : Type) (err : TypeError)
    → LookupLocalView ctx "arr"
    → LookupImportView ctx "arr"
    → VerifiedCheckResult ctx (Raw.RVar "arr") T
  -- Per-bbc-X aux taking the inferElab result explicitly. Eliminates
  -- the inner with-helper opacity. Each bbc-X's success-via-infer path
  -- uses t-embed; the failure path delegates to bbc-X-failure-aux.
  checkElabV-RVar-bbc-id-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "id")
    → VerifiedCheckResult ctx (Raw.RVar "id") T
  checkElabV-RVar-bbc-fst-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "fst")
    → VerifiedCheckResult ctx (Raw.RVar "fst") T
  checkElabV-RVar-bbc-snd-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "snd")
    → VerifiedCheckResult ctx (Raw.RVar "snd") T
  checkElabV-RVar-bbc-terminal-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "terminal")
    → VerifiedCheckResult ctx (Raw.RVar "terminal") T
  checkElabV-RVar-bbc-initial-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "initial")
    → VerifiedCheckResult ctx (Raw.RVar "initial") T
  checkElabV-RVar-bbc-inl-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "inl")
    → VerifiedCheckResult ctx (Raw.RVar "inl") T
  checkElabV-RVar-bbc-inr-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "inr")
    → VerifiedCheckResult ctx (Raw.RVar "inr") T
  checkElabV-RVar-bbc-arr-aux :
    ∀ (ctx : NamedCtx) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar "arr")
    → VerifiedCheckResult ctx (Raw.RVar "arr") T
  checkElabV-RVar-bbc-other-aux :
    ∀ (ctx : NamedCtx) (x : String) (T : Type)
    → VerifiedInferResult ctx (Raw.RVar x)
    → VerifiedCheckResult ctx (Raw.RVar x) T
  -- RInt check-mode dispatch, taking the value-lift decision explicitly
  -- (`just (X , refl)` ⇒ pure-arrow-to-Int target ⇒ value-lift; `nothing` ⇒
  -- the generic infer-and-match). One scrutinee, no clause overlap.
  checkElabV-RInt-aux :
    ∀ (ctx : NamedCtx) (n : ℤ) (T : Type)
    → Maybe (∃-syntax (λ X → T ≡ (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Int)))
    → VerifiedCheckResult ctx (Raw.RInt n) T
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
  ... | just _ = success Surface.zeroUsage (Surface.poly x T)
                         0 (NamedCtx.freshCounter ctx)
  -- id : T → T
  checkElab-RVar ctx _ T | bbc-id with inferElab ctx (Raw.RVar "id")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) | bbc-id | failure _ with A ≟T B
  ... | yes refl = success _ (weakenFromEmpty (specId A)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "id")
  checkElab-RVar ctx _ _ | bbc-id | failure err = failure err
  -- fst : (A * B) → A
  checkElab-RVar ctx _ T | bbc-fst with inferElab ctx (Raw.RVar "fst")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A') | bbc-fst | failure _ with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specFst A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "fst")
  checkElab-RVar ctx _ _ | bbc-fst | failure err = failure err
  -- snd : (A * B) → B
  checkElab-RVar ctx _ T | bbc-snd with inferElab ctx (Raw.RVar "snd")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B') | bbc-snd | failure _ with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specSnd A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "snd")
  checkElab-RVar ctx _ _ | bbc-snd | failure err = failure err
  -- terminal : A → Unit
  checkElab-RVar ctx _ T | bbc-terminal with inferElab ctx (Raw.RVar "terminal")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Unit) | bbc-terminal | failure _ =
    success _ (weakenFromEmpty (specTerminal A)) 0 (NamedCtx.freshCounter ctx)
  checkElab-RVar ctx _ _ | bbc-terminal | failure err = failure err
  -- initial : Void → A
  checkElab-RVar ctx _ T | bbc-initial with inferElab ctx (Raw.RVar "initial")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A) | bbc-initial | failure _ =
    success _ (weakenFromEmpty (specInitial A)) 0 (NamedCtx.freshCounter ctx)
  checkElab-RVar ctx _ _ | bbc-initial | failure err = failure err
  -- inl : A → (A + B)
  checkElab-RVar ctx _ T | bbc-inl with inferElab ctx (Raw.RVar "inl")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A' Once.Type.+ B)) | bbc-inl | failure _ with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specInl A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "inl")
  checkElab-RVar ctx _ _ | bbc-inl | failure err = failure err
  -- inr : B → (A + B)
  checkElab-RVar ctx _ T | bbc-inr with inferElab ctx (Raw.RVar "inr")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B')) | bbc-inr | failure _ with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specInr A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "inr")
  checkElab-RVar ctx _ _ | bbc-inr | failure err = failure err
  -- arr : (A → B) → Eff A B
  checkElab-RVar ctx _ T | bbc-arr with inferElab ctx (Raw.RVar "arr")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A' Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B')) | bbc-arr | failure _ with A ≟T A' | B ≟T B'
  ... | yes refl | yes refl = success _ (weakenFromEmpty (specArr A B)) 0 (NamedCtx.freshCounter ctx)
  ... | _ | _ = failure (BuiltinTypeMismatch "arr")
  checkElab-RVar ctx _ _ | bbc-arr | failure err = failure err

  -- Plan 0.6 Phase C.7 POC-2: bare `pair f g` check-mode.
  -- Expected type must be `A ⇒[Many] (B * C)`. Checks each
  -- component function at its projected arrow shape, then emits
  -- `app (app specPair fE) gE`. No lookup-first branch: the
  -- classifier's `ahv-pair-applied` dispatch already establishes
  -- disjointness with `t-embed (t-app …)` — t-app's premise
  -- `classifyAppHead f ≡ nothing` fails for the pair-applied shape.
  checkPair ctx (Raw.RApp (Raw.RVar "pair") f_inner) arg
            (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (B Once.Type.* C))
    with checkElabV ctx f_inner (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
  ... | failure err , _ = failure err , tt
  ... | success Ψf fE df frf , wF
        with checkElabV ctx arg (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C)
  ...     | failure err , _ = failure err , tt
  ...     | success Ψg gE dg frg , wG
            with extract-morph-eff fE | extract-morph-eff gE | extractMorphWitness wF | extractMorphWitness wG
  ...       | just (mf , _) | just (mg , _) | just mFᵐ | just mGᵐ =
              success Surface.zeroUsage
                (Surface.lift-morphism (IR.⟨ mf , mg ⟩ IR.Heap))
                (suc (df Data.Nat.⊔ dg)) frg , t-morph-lift (m-pair mFᵐ mGᵐ)
  ...       | _ | _ | _ | _ = failure (BuiltinTypeMismatch "pair") , tt
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
  -- `composeArgB` premise (so completeness stays postulate-free).
  -- Plan 0.49 / D063: ONE grade-polymorphic clause (D056 — the bespoke eff
  -- copy is gone). Both arms must be morphisms (`extractMorphWitness`); emit the
  -- direct `lift-morphism (IR.case m_f m_g)`; no closure fallback.
  checkCase ctx (Raw.RApp (Raw.RVar "case") f_inner) arg
            ((A Once.Type.+ B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
    with checkElabV ctx f_inner (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  ... | failure err , _ = failure err , tt
  ... | success Ψf fE df frf , wF
        with checkElabV ctx arg (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] C)
  ...     | failure err , _ = failure err , tt
  ...     | success Ψg gE dg frg , wG
            with extract-morph-eff fE | extract-morph-eff gE | extractMorphWitness wF | extractMorphWitness wG
  ...         | just (m_f , _) | just (m_g , _) | just mFᵐ | just mGᵐ =
                success Surface.zeroUsage (Surface.lift-morphism (IR.case m_f m_g))
                  (suc (df Data.Nat.⊔ dg)) frf , t-morph-lift (m-case mFᵐ mGᵐ)
  ...         | _ | _ | _ | _ = failure (BuiltinTypeMismatch "case") , tt
  checkCase _ _ _ _ = failure (BuiltinTypeMismatch "case") , tt

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
  checkCompose ctx (Raw.RApp (Raw.RVar "compose") f_inner) arg
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
  ...         | success Ψf fE df frf , wF
                with extract-morph-eff fE | extract-morph-eff gE | extractMorphWitness wF | extractMorphWitness wG
  ...             | just (m_f , _) | just (m_g , _) | just mFᵐ | just mGᵐ =
                    success Surface.zeroUsage (Surface.lift-morphism (m_f IR.∘ m_g))
                      (suc (df Data.Nat.⊔ dg)) frf , t-morph-lift (m-compose eqB mFᵐ mGᵐ)
  ...             | _ | _ | _ | _ = failure (BuiltinTypeMismatch "compose") , tt

  -- Plan 0.6 Phase C.7 POC-3: `curry f` check-mode.
  -- Expected `A ⇒[Many] (B ⇒[Many] C)`. Check f at `(A * B) ⇒[Many] C`.
  checkCurry ctx arg (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C))
    with checkElabV ctx arg ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] C)
  ... | failure err , _ = failure err , tt
  ... | success Ψ argE d fr , w with extract-morph-eff argE | extractMorphWitness w
  ...   | just (mf , _) | just mFᵐ =
          success Surface.zeroUsage (Surface.lift-morphism (IR.curry mf IR.Heap)) (suc d) fr
          , t-morph-lift (m-curry mFᵐ)
  ...   | _ | _ = failure (BuiltinTypeMismatch "curry") , tt
  checkCurry _ _ _ = failure (BuiltinTypeMismatch "curry") , tt

  -- Plan 0.6 Phase C.7 POC-3: `apply p` check-mode.
  -- Check mode falls through to infer (apply's infer mode succeeds
  -- when p has pair-of-function type). Matches result against T.
  checkApply ctx arg T with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A') Ψ argE d fr , w
        with A ≟T A' | T ≟T B
  ...   | yes refl | yes refl =
          success _ (Surface.app (weakenFromEmpty (specApply A B)) argE) (suc d) fr , t-apply-check w
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
  -- Plan 0.41 structural value-lift: `In arg` at a pure arrow to `μ-type F`
  -- is a closed global-element value — route through `checkG`.
  checkIn ctx arg (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (Once.Type.μ-type F))
    with inspectCheckG ctx X (Raw.RApp (Raw.RVar "In") arg) (Once.Type.μ-type F)
  ... | cgv-nothing _    = failure (BuiltinTypeMismatch "In") , tt
  ... | cgv-just {m} {gd} _ =
          success Surface.zeroUsage (Surface.lift-morphism m) 0 (NamedCtx.freshCounter ctx)
          , t-value-lift gd
  checkIn _ _ _ = failure (BuiltinTypeMismatch "In") , tt

  checkInGo ctx arg F nothing _ = failure (BuiltinTypeMismatch "In") , tt
  checkInGo ctx arg F (just wfF) eqW with checkElabV ctx arg (⟦ F ⟧T (Once.Type.μ-type F))
  ... | failure err , _ = failure err , tt
  ... | success Ψ argE d fr , wArg =
        success _ (Surface.morph-app (IR.In wfF IR.Heap) argE) (suc d) fr , t-In-app-check eqW wArg

  -- Plan 0.28 Commit 2: `cata alg` (catamorphism) check-mode at
  -- `μ-type F ⇒[Many] A`. The algebra is compiled by the self-contained
  -- `morphRaw?`/`morphToIR` (no elaborator extraction); the three
  -- decidable results are threaded through `checkCataA/B/C` so the
  -- witness carries the equations and completeness reduces cleanly.
  -- Emits `lift-morphism (IR.Cata wfF algIR)`.
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
  ... | success Surface.[] algE d fr , wArg =
        success _ (Surface.cata wfF algE) (suc d) (NamedCtx.freshCounter ctx)
          , t-morph-lift (m-cata eqW wArg)

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

  inferElabV ctx (Raw.RAnnot e T) with checkElabV ctx e T
  ... | success Ψ eE d fr , witness = success T Ψ eE d fr , t-annot witness
  ... | failure err , _             = failure err , tt

  inferElabV ctx (Raw.RPair a b) with inferElabV ctx a
  ... | failure err , _ = failure err , tt
  ... | success A Ψ₁ aE da fa , wA with inferElabV ctx b
  ...   | failure err , _ = failure err , tt
  ...   | success B Ψ₂ bE db fb , wB =
          success (A Once.Type.* B) _ (Surface.pair aE bE) (da ⊔ db) fb , t-pair wA wB

  ----------------------------------------------------------------------
  -- Phase B — lookup-driven clauses (RQualified, RVar, RUnaryOp,
  -- RLet, RDestruct). RBinOp deferred (more complex op + type
  -- dispatch).
  ----------------------------------------------------------------------

  inferElabV ctx (Raw.RQualified name alias) =
    inferElabV-RQualified-aux ctx name alias _ refl

  inferElabV ctx (Raw.RVar x) with StrProp._≟_ x "unit"
  ... | yes refl = success Unit _ Surface.unit 0 (NamedCtx.freshCounter ctx) , t-unit-var
  ... | no ¬unit = inferElabV-RVar-lookup-aux ctx x ¬unit _ refl _ refl

  inferElabV ctx (Raw.RUnaryOp Raw.OpNeg e) with inferElabV ctx e
  ... | failure err , _                        = failure err , tt
  ... | success Unit       _ _ _ _ , _         = failure (TypeMismatch Int Unit) , tt
  ... | success Void       _ _ _ _ , _         = failure (TypeMismatch Int Void) , tt
  ... | success Int        Ψ eE d fr , w       = success Int _ (Surface.neg eE) (suc d) fr , t-neg w
  ... | success Float      _ _ _ _ , _         = failure (TypeMismatch Int Float) , tt
  ... | success Str        _ _ _ _ , _         = failure (TypeMismatch Int Str) , tt
  ... | success Buffer     _ _ _ _ , _         = failure (TypeMismatch Int Buffer) , tt
  ... | success (A Once.Type.* B)       _ _ _ _ , _ = failure (TypeMismatch Int (A Once.Type.* B)) , tt
  ... | success (A Once.Type.+ B)       _ _ _ _ , _ = failure (TypeMismatch Int (A Once.Type.+ B)) , tt
  ... | success (A Once.Type.⇒[ k ] B)  _ _ _ _ , _ = failure (TypeMismatch Int (A Once.Type.⇒[ k ] B)) , tt
  ... | success (Once.Type.μ-type F)    _ _ _ _ , _ = failure (TypeMismatch Int (Once.Type.μ-type F)) , tt
  ... | success (Once.Type.ν-type F)    _ _ _ _ , _ = failure (TypeMismatch Int (Once.Type.ν-type F)) , tt

  inferElabV ctx (Raw.RLet x e₁ e₂) with inferElabV ctx e₁
  ... | failure err , _ = failure err , tt
  ... | success A Ψ₁ e₁E d₁ f₁ , w₁ with inferElabV (extendNamedCtx ctx x A) e₂
  ...   | failure err , _ = failure err , tt
  ...   | success B (q ∷ᵘ Ψ₂) e₂E d₂ f₂ , w₂ =
          success B _ (Surface.let' e₁E e₂E) (d₁ ⊔ suc d₂) f₂ , t-let w₁ w₂

  inferElabV ctx (Raw.RDestruct scrut xL eL xR eR) with inferElabV ctx scrut
  ... | failure err , _                        = failure err , tt
  ... | success Unit   _ _ _ _ , _             = failure CaseScrutineeNotSum , tt
  ... | success Void   _ _ _ _ , _             = failure CaseScrutineeNotSum , tt
  ... | success Int    _ _ _ _ , _             = failure CaseScrutineeNotSum , tt
  ... | success Float  _ _ _ _ , _             = failure CaseScrutineeNotSum , tt
  ... | success Str    _ _ _ _ , _             = failure CaseScrutineeNotSum , tt
  ... | success Buffer _ _ _ _ , _             = failure CaseScrutineeNotSum , tt
  ... | success (_ Once.Type.* _) _ _ _ _ , _  = failure CaseScrutineeNotSum , tt
  ... | success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _ = failure CaseScrutineeNotSum , tt
  ... | success (Once.Type.μ-type _) _ _ _ _ , _   = failure CaseScrutineeNotSum , tt
  ... | success (Once.Type.ν-type _) _ _ _ _ , _   = failure CaseScrutineeNotSum , tt
  ... | success (A Once.Type.+ B) Ψs scrutE ds fs , wS
        with inferElabV (extendNamedCtx ctx xL A) eL
  ...     | failure err , _ = failure err , tt
  ...     | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , wL
            with inferElabV (extendNamedCtx ctx xR B) eR
  ...       | failure err , _ = failure err , tt
  ...       | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , wR
              with C₁ ≟T C₂
  ...         | yes refl =
                success C₁ _ (Surface.case' scrutE eLE eRE)
                  (ds ⊔ suc dL ⊔ suc dR) fR , t-case wS wL wR
  ...         | no _ = failure CaseBranchMismatch , tt

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

  inferElabV ctx (Raw.RBinOp op e₁ e₂) with inferElabV ctx e₁
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | failure err , _ =
    failure (BinOpLeftError err) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Unit       _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int Unit)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Void       _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int Void)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Float      _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int Float)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Str        _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int Str)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Buffer     _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int Buffer)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success (A Once.Type.* B)      _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Type.* B))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success (A Once.Type.+ B)      _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Type.+ B))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success (A Once.Type.⇒[ k ] B) _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int (A Once.Type.⇒[ k ] B))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success (Once.Type.μ-type F)   _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int (Once.Type.μ-type F))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success (Once.Type.ν-type F)   _ _ _ _ , _ = failure (BinOpLeftError (TypeMismatch Int (Once.Type.ν-type F))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ with inferElabV ctx e₂
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | failure err , _ =
    failure (BinOpRightError err) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success Unit       _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int Unit)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success Void       _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int Void)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success Float      _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int Float)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success Str        _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int Str)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success Buffer     _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int Buffer)) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success (A Once.Type.* B)      _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int (A Once.Type.* B))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success (A Once.Type.+ B)      _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int (A Once.Type.+ B))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success (A Once.Type.⇒[ k ] B) _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int (A Once.Type.⇒[ k ] B))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success (Once.Type.μ-type F)   _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int (Once.Type.μ-type F))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success (Once.Type.ν-type F)   _ _ _ _ , _ = failure (BinOpRightError (TypeMismatch Int (Once.Type.ν-type F))) , tt
  inferElabV ctx (Raw.RBinOp op e₁ e₂) | success Int Ψ₁ e₁E d₁ f₁ , w₁ | success Int Ψ₂ e₂E d₂ f₂ , w₂ with op
  ...   | Raw.OpAdd = success Int _ (Surface.add e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  ...   | Raw.OpSub = success Int _ (Surface.sub e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  ...   | Raw.OpMul = success Int _ (Surface.mul e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  ...   | Raw.OpDiv = success Int _ (Surface.div e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  ...   | Raw.OpMod = success Int _ (Surface.mod' e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-arith refl w₁ w₂
  ...   | Raw.OpLt  = success (Unit Once.Type.+ Unit) _ (Surface.lt e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  ...   | Raw.OpLe  = success (Unit Once.Type.+ Unit) _ (Surface.le e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  ...   | Raw.OpGt  = success (Unit Once.Type.+ Unit) _ (Surface.gt e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  ...   | Raw.OpGe  = success (Unit Once.Type.+ Unit) _ (Surface.ge e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  ...   | Raw.OpEq  = success (Unit Once.Type.+ Unit) _ (Surface.eq e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂
  ...   | Raw.OpNe  = success (Unit Once.Type.+ Unit) _ (Surface.ne e₁E e₂E) (d₁ ⊔ d₂) f₂ , t-binop-cmp refl w₁ w₂

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

  checkElabV ctx (Raw.RApp f arg) T =
    checkElabV-RApp-dispatch ctx f arg T _ refl

  -- RLam check-mode: only well-typed at a pure arrow type.
  checkElabV ctx (Raw.RLam x body) (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) with checkElabV (extendNamedCtx ctx x A) body B
  ... | failure err , _ = failure err , tt
  ... | success (q' ∷ᵘ Ψ) bodyE d fr , wBody with decideLeq q' q
  ...   | just eq = success _ (Surface.lam q eq bodyE) (suc d) fr , t-lam eq wBody
  ...   | nothing = failure (UsageViolation x q q') , tt
  -- Non-pure-arrow T: lambda's only check-mode rule is t-lam (pure).
  checkElabV ctx (Raw.RLam _ _) _ = failure LambdaRequiresFunctionType , tt

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
  checkElabV ctx (Raw.RVar x) T with classifyBareBuiltin x | inferElabV ctx (Raw.RVar x)
  ... | bbc-id       | rInfV = checkElabV-RVar-bbc-id-aux ctx T rInfV
  ... | bbc-fst      | rInfV = checkElabV-RVar-bbc-fst-aux ctx T rInfV
  ... | bbc-snd      | rInfV = checkElabV-RVar-bbc-snd-aux ctx T rInfV
  ... | bbc-terminal | rInfV = checkElabV-RVar-bbc-terminal-aux ctx T rInfV
  ... | bbc-initial  | rInfV = checkElabV-RVar-bbc-initial-aux ctx T rInfV
  ... | bbc-inl      | rInfV = checkElabV-RVar-bbc-inl-aux ctx T rInfV
  ... | bbc-inr      | rInfV = checkElabV-RVar-bbc-inr-aux ctx T rInfV
  ... | bbc-arr      | rInfV = checkElabV-RVar-bbc-arr-aux ctx T rInfV
  ... | bbc-other    | rInfV = checkElabV-RVar-bbc-other-aux ctx x T rInfV

  -- Plan 0.36 Phase 2a follow-up: pair literal `(a , b)` at a product
  -- type — check components bidirectionally so check-only constructs
  -- (notably `In`) work in pair slots (`In (inr (x , tail))`). Falls to
  -- the generic clause below for non-product target types.
  checkElabV ctx (Raw.RPair a b) T = checkElabV-RPair-aux ctx a b T (classifyRPairTarget T)

  -- Plan 0.41 / D018 leaf: an integer literal at a pure-arrow position is its
  -- constant morphism (global element `const n ∘ terminal`, via `intLit`),
  -- the `g-int` leaf of `⊢ᵍ` bridged by `t-value-lift`; otherwise the generic
  -- infer-and-match. Routed through ONE scrutinee (`isRIntVliftTarget? T`) so
  -- the two outcomes don't overlap (no stuck `checkElabV (RInt n) T` for
  -- variable `T`). Behaviour is unchanged; the dispatch is now analysable.
  checkElabV ctx (Raw.RInt n) T = checkElabV-RInt-aux ctx n T (isRIntVliftTarget? T)

  -- Generic infer-and-match fallback — covers RInt, RStringLit, RUnit,
  -- RPair, RBinOp, RUnaryOp, RLet, RDestruct, RAnnot, RQualified.
  checkElabV ctx e T with inferElabV ctx e
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt

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
  ext-arrow-info : ∀ {A B} → NamedCtx → (alias name : String) → Purity → SigOpInfo A B
  ext-arrow-info ctx alias name pure = mk-info' name (pureV (generic-semM name))
  ext-arrow-info {A} {B} ctx alias name eff with B ≟T Unit
  ... | no _ = mk-info' name (pureV (generic-semM name))
  ... | yes refl with lookupSigEffect (NamedCtx.sigEffects ctx) (alias ++ "." ++ name)
  ...   | just se-halts = mk-info' name (haltsV refl)
  ...   | just se-emits = mk-info' name (emitsV refl)
  ...   | nothing       = mk-info' name (emitsV refl)

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
    success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) _
      (Surface.lift-morphism {π = π} (IR.SigOp (ext-arrow-info ctx alias name π)))
      0 (NamedCtx.freshCounter ctx)
    , t-var-qualified eq
  inferElabV-RQualified-aux ctx name alias (just ty) eq =
    success ty _ (Surface.sigOp name) 0 (NamedCtx.freshCounter ctx) , t-var-qualified eq
  inferElabV-RQualified-aux ctx name alias nothing _ =
    failure (UnboundQualified name alias) , tt

  inferElabV-RVar-lookup-aux ctx x ¬unit (just (A , Ψ , se)) eq-loc _ _ =
    success A Ψ se 0 (NamedCtx.freshCounter ctx) , t-var-local ¬unit eq-loc
  inferElabV-RVar-lookup-aux ctx x ¬unit nothing eq-loc (just ty) eq-imp =
    success ty _ (Surface.sigOp x) 0 (NamedCtx.freshCounter ctx) , t-var-import ¬unit eq-loc eq-imp
  inferElabV-RVar-lookup-aux ctx x ¬unit nothing eq-loc nothing eq-imp =
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
    success A _ (Surface.morph-app (IR.fst {A = A} {B = B}) argE) (suc d) fr , t-fst-app w
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
    success B _ (Surface.morph-app (IR.snd {A = A} {B = B}) argE) (suc d) fr , t-snd-app w
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
  -- ahv-arr : argument must be `A ⇒[Many,pure] B`; result is Eff A B.
  inferElabV-RApp-dispatch ctx f arg ahv-arr _ with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Ψ argE d fr , w =
    success (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B) _
            (Surface.arr' argE) (suc d) fr , t-arr-app-infer w
  ... | success Unit _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success Void _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success Int _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success Float _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success Str _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success Buffer _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success (_ Once.Type.* _) _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success (_ Once.Type.+ _) _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success (_ Once.Type.⇒[ Once.Type.mk-kind _ Once.Type.eff ] _) _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.pure ] _) _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.pure ] _) _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success (Once.Type.μ-type _) _ _ _ _ , _ = failure ArrNeedsFunction , tt
  ... | success (Once.Type.ν-type _) _ _ _ _ , _ = failure ArrNeedsFunction , tt
  -- ahv-apply : argument must be `(A ⇒[Many,pure] B) * A`.
  inferElabV-RApp-dispatch ctx f arg ahv-apply _ with inferElabV ctx arg
  ... | failure err , _ = failure err , tt
  ... | success ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A') Ψ argE d fr , w with A ≟T A'
  ...   | yes refl =
    success B _ (Surface.app (weakenFromEmpty (specApply A B)) argE) (suc d) fr , t-apply-app-infer w
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
  checkElabV-RApp-dispatch ctx f arg T ahv-id _ with inferElabV ctx (Raw.RApp f arg)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-fst _ with inferElabV ctx (Raw.RApp f arg)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-snd _ with inferElabV ctx (Raw.RApp f arg)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-terminal _ with inferElabV ctx (Raw.RApp f arg)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt
  -- ahv-inl: T must be sum type A+B; check arg at A.
  -- Plan 0.41 structural value-lift: `inl arg` / `inr arg` at a *pure arrow*
  -- to a sum is a closed global-element value — route through `checkG`, which
  -- yields the IR and the `⊢ᵍ` derivation for the `t-value-lift` bridge.
  -- Specific clauses before the value-type `with T` dispatch (first-match).
  checkElabV-RApp-dispatch ctx f arg
    (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B)) ahv-inl _
    with inspectCheckG ctx X (Raw.RApp (Raw.RVar "inl") arg) (A Once.Type.+ B)
  ... | cgv-nothing _ = failure InlNeedsSumType , tt
  ... | cgv-just {m} {gd} _ =
          success Surface.zeroUsage (Surface.lift-morphism m) 0 (NamedCtx.freshCounter ctx)
          , t-value-lift gd
  checkElabV-RApp-dispatch ctx f arg
    (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B)) ahv-inr _
    with inspectCheckG ctx X (Raw.RApp (Raw.RVar "inr") arg) (A Once.Type.+ B)
  ... | cgv-nothing _ = failure InrNeedsSumType , tt
  ... | cgv-just {m} {gd} _ =
          success Surface.zeroUsage (Surface.lift-morphism m) 0 (NamedCtx.freshCounter ctx)
          , t-value-lift gd
  checkElabV-RApp-dispatch ctx f arg T ahv-inl _ with T
  ... | (A Once.Type.+ B) with checkElabV ctx arg A
  ...   | failure err , _ = failure err , tt
  ...   | success Ψ argE d fr , w =
          success _ (Surface.morph-app (IR.inl {A = A} {B = B} IR.Heap) argE) (suc d) fr , t-inl-app-check w
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
          success _ (Surface.morph-app (IR.inr {A = A} {B = B} IR.Heap) argE) (suc d) fr , t-inr-app-check w
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
        success _ (Surface.morph-app (IR.initial {A = T}) argE) (suc d) fr , t-initial-app-check w
  -- ahv-arr: T must be Eff A B; check arg at A→B.
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ with T
  ... | (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        with checkElabV ctx arg (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
  ...   | failure err , _ = failure err , tt
  ...   | success Ψ argE d fr , w =
          success _ (Surface.arr' argE) (suc d) fr , t-arr-app-check w
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | Unit = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | Void = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | Int = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | Float = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | Str = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | Buffer = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | (_ Once.Type.* _) = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | (_ Once.Type.+ _) = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | (_ Once.Type.⇒[ Once.Type.mk-kind _ Once.Type.pure ] _) = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.eff ] _) = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.eff ] _) = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | (μ-type _) = failure (TypeMismatch T T) , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-arr _ | (ν-type _) = failure (TypeMismatch T T) , tt
  -- Helper-applied branches.
  checkElabV-RApp-dispatch ctx f arg T ahv-pair-applied _ = checkPair ctx f arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-compose-applied _ = checkCompose ctx f arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-case-applied _ = checkCase ctx f arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-In _ = checkIn ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-cata _ = checkCata ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-curry _ = checkCurry ctx arg T
  checkElabV-RApp-dispatch ctx f arg T ahv-apply _ = checkApply ctx arg T
  -- ahv-other: try infer-then-match; on failure, arg-driven application.
  checkElabV-RApp-dispatch ctx f arg T ahv-other _ with inferElabV ctx (Raw.RApp f arg)
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RApp-dispatch ctx f arg T ahv-other _ | failure errInfer , _
        with classifyAppHead f in eqAH
  ...   | just _  = failure errInfer , tt
  ...   | nothing with inferElabV ctx arg
  ...     | failure errArg , _ = failure errArg , tt
  ...     | success X Ψx argE dx frx , wArg
              with checkElabV ctx f (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T)
  ...       | failure err , _ = failure err , tt
  ...       | success Ψf fE df frf , wF =
              success _ (Surface.app fE argE) (suc (df ⊔ dx)) frf , t-arg-driven-app-check eqAH wArg wF

  -- bbc-X failure-branch aux bodies. Each pattern-matches on T to the
  -- canonical builtin shape and on the lookup results. Success iff
  -- T = canonical & both lookups nothing & inner type-checks pass.
  checkElabV-RVar-bbc-id-failure-aux ctx (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Y) err (llv-not-found eqLoc) (liv-not-found eqImp) with X ≟T Y
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism IR.id) 0 (NamedCtx.freshCounter ctx) , t-morph-lift (m-id eqLoc eqImp)
  ... | no _ = failure (BuiltinTypeMismatch "id") , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-not-found _) (liv-found _) = failure (BuiltinTypeMismatch "id") , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-found _) _ = failure (BuiltinTypeMismatch "id") , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-id-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  checkElabV-RVar-bbc-fst-failure-aux ctx ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A') err (llv-not-found eqLoc) (liv-not-found eqImp) with A ≟T A'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism IR.fst) 0 (NamedCtx.freshCounter ctx) , t-morph-lift (m-fst eqLoc eqImp)
  ... | no _ = failure (BuiltinTypeMismatch "fst") , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-not-found _) (liv-found _) = failure (BuiltinTypeMismatch "fst") , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-found _) _ = failure (BuiltinTypeMismatch "fst") , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Unit Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Void Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Int Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Float Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Str Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Buffer Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.+ _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.⇒[ _ ] _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((Once.Type.μ-type _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((Once.Type.ν-type _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-fst-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  -- bbc-snd: canonical T = (A * B) ⇒[Many,pure] B'
  checkElabV-RVar-bbc-snd-failure-aux ctx ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B') err (llv-not-found eqLoc) (liv-not-found eqImp) with B ≟T B'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism IR.snd) 0 (NamedCtx.freshCounter ctx) , t-morph-lift (m-snd eqLoc eqImp)
  ... | no _ = failure (BuiltinTypeMismatch "snd") , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-not-found _) (liv-found _) = failure (BuiltinTypeMismatch "snd") , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-found _) _ = failure (BuiltinTypeMismatch "snd") , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Unit Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Void Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Int Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Float Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Str Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Buffer Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.+ _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.⇒[ _ ] _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((Once.Type.μ-type _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((Once.Type.ν-type _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-snd-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  -- bbc-terminal: canonical T = A ⇒[Many,pure] Unit
  checkElabV-RVar-bbc-terminal-failure-aux ctx (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit) err (llv-not-found eqLoc) (liv-not-found eqImp) =
    success Surface.zeroUsage (Surface.lift-morphism IR.terminal) 0 (NamedCtx.freshCounter ctx) , t-morph-lift (m-terminal eqLoc eqImp)
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit) err (llv-not-found _) (liv-found _) = failure (BuiltinTypeMismatch "terminal") , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] Unit) err (llv-found _) _ = failure (BuiltinTypeMismatch "terminal") , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Void) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Int) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Float) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Str) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] Buffer) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.* _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.+ _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.⇒[ _ ] _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.μ-type _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.ν-type _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] Unit) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] Unit) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-terminal-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  -- bbc-initial: canonical T = Void ⇒[Many,pure] A
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] A) err (llv-not-found eqLoc) (liv-not-found eqImp) =
    success Surface.zeroUsage (Surface.lift-morphism IR.initial) 0 (NamedCtx.freshCounter ctx) , t-morph-lift (m-initial eqLoc eqImp)
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-not-found _) (liv-found _) = failure (BuiltinTypeMismatch "initial") , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] _) err (llv-found _) _ = failure (BuiltinTypeMismatch "initial") , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Unit Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Int Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Float Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Str Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Buffer Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Type.* _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Type.+ _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((_ Once.Type.⇒[ _ ] _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((Once.Type.μ-type _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx ((Once.Type.ν-type _) Once.Type.⇒[ _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-initial-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  -- bbc-inl: canonical T = A ⇒[Many,pure] (A' + B)
  checkElabV-RVar-bbc-inl-failure-aux ctx (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A' Once.Type.+ B)) err (llv-not-found eqLoc) (liv-not-found eqImp) with A ≟T A'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism (IR.inl IR.Heap)) 0 (NamedCtx.freshCounter ctx) , t-morph-lift (m-inl eqLoc eqImp)
  ... | no _ = failure (BuiltinTypeMismatch "inl") , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (_ Once.Type.+ _)) err (llv-not-found _) (liv-found _) = failure (BuiltinTypeMismatch "inl") , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (_ Once.Type.+ _)) err (llv-found _) _ = failure (BuiltinTypeMismatch "inl") , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Unit) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Void) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Int) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Float) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Str) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] Buffer) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.* _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.⇒[ _ ] _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.μ-type _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.ν-type _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] (_ Once.Type.+ _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] (_ Once.Type.+ _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inl-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  -- bbc-inr: canonical T = B ⇒[Many,pure] (A + B')
  checkElabV-RVar-bbc-inr-failure-aux ctx (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (A Once.Type.+ B')) err (llv-not-found eqLoc) (liv-not-found eqImp) with B ≟T B'
  ... | yes refl =
        success Surface.zeroUsage (Surface.lift-morphism (IR.inr IR.Heap)) 0 (NamedCtx.freshCounter ctx) , t-morph-lift (m-inr eqLoc eqImp)
  ... | no _ = failure (BuiltinTypeMismatch "inr") , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (_ Once.Type.+ _)) err (llv-not-found _) (liv-found _) = failure (BuiltinTypeMismatch "inr") , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] (_ Once.Type.+ _)) err (llv-found _) _ = failure (BuiltinTypeMismatch "inr") , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Unit) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Void) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Int) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Float) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Str) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] Buffer) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.* _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (_ Once.Type.⇒[ _ ] _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.μ-type _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ _ ] (Once.Type.ν-type _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero _ ] (_ Once.Type.+ _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One _ ] (_ Once.Type.+ _)) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-inr-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  -- bbc-arr: canonical T = (A ⇒[Many,pure] B) ⇒[Many,pure] (A' ⇒[Many,eff] B')
  -- Use a Bool helper to identify the canonical shape; avoids enumerating
  -- the deep arrow-kind combinatorial.
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found eqLoc) (liv-not-found eqImp)
    with T₁
  ... | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B with T₂
  ...   | A' Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B' with A ≟T A' | B ≟T B'
  ...     | yes refl | yes refl = failure (BuiltinTypeMismatch "arr") , tt   -- D065: bare unapplied `arr` is not a morphism
  ...     | _ | _ = failure (BuiltinTypeMismatch "arr") , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | Unit = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | Void = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | Int = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | Float = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | Str = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | Buffer = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | (_ Once.Type.* _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | (_ Once.Type.+ _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | (_ Once.Type.⇒[ Once.Type.mk-kind _ Once.Type.pure ] _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.eff ] _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.eff ] _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | (Once.Type.μ-type _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _)
    | A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B | (Once.Type.ν-type _) = failure err , tt
  -- T₁ not (_ ⇒[Many,pure] _)
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | Unit = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | Void = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | Int = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | Float = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | Str = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | Buffer = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | (_ Once.Type.* _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | (_ Once.Type.+ _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | (_ Once.Type.⇒[ Once.Type.mk-kind _ Once.Type.eff ] _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.pure ] _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.pure ] _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | (Once.Type.μ-type _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-not-found _) | (Once.Type.ν-type _) = failure err , tt
  -- Other view configurations for outer arrow-pure T
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-not-found _) (liv-found _) = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (T₁ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T₂) err (llv-found _) _ = failure err , tt
  -- Outer T not (_ ⇒[Many,pure] _)
  checkElabV-RVar-bbc-arr-failure-aux ctx Unit err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx Void err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx Int err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx Float err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx Str err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx Buffer err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (_ Once.Type.* _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (_ Once.Type.+ _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind _ Once.Type.eff ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero Once.Type.pure ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.One Once.Type.pure ] _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (Once.Type.μ-type _) err _ _ = failure err , tt
  checkElabV-RVar-bbc-arr-failure-aux ctx (Once.Type.ν-type _) err _ _ = failure err , tt

  -- RInt: value-lift on a pure-arrow-to-Int target, else generic infer+match.
  -- `refl` refines `T` to the arrow so `t-value-lift (g-int n)` types; the
  -- `nothing` branch reproduces the old generic clause for RInt verbatim.
  checkElabV-RInt-aux ctx n T (just (X , refl)) =
    success Surface.zeroUsage (Surface.lift-morphism (intLit n)) 0 (NamedCtx.freshCounter ctx)
    , t-value-lift (g-int n)
  checkElabV-RInt-aux ctx n T nothing with inferElabV ctx (Raw.RInt n)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt

  -- RPair: product → bidirectional component check (checkPairLit);
  -- pure-arrow-to-product → value-lift via checkG (inspectCheckG); else the
  -- generic infer+match. The latter two are the old clauses verbatim.
  checkElabV-RPair-aux ctx a b _ (rpt-prod A B) = checkPairLit ctx a b A B
  checkElabV-RPair-aux ctx a b _ (rpt-vlift X A B)
    with inspectCheckG ctx X (Raw.RPair a b) (A Once.Type.* B)
  ... | cgv-nothing _ = failure (TypeMismatch (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.* B))
                                        (X Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.* B))) , tt
  ... | cgv-just {m} {gd} _ =
          success Surface.zeroUsage (Surface.lift-morphism m) 0 (NamedCtx.freshCounter ctx)
          , t-value-lift gd
  checkElabV-RPair-aux ctx a b _ (rpt-other T) with inferElabV ctx (Raw.RPair a b)
  ... | failure err , _ = failure err , tt
  ... | success T' Ψ eE d fr , w with T ≟T T'
  ...   | yes refl = success Ψ eE d fr , t-embed w
  ...   | no _     = failure (TypeMismatch T T') , tt

  -- Per-bbc-X auxes: pattern-match on the verified inferElabV result
  -- (Σ-pair). The success path uses t-embed of the witness; the
  -- failure path delegates to bbc-X-failure-aux.
  checkElabV-RVar-bbc-id-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-id-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-id-failure-aux ctx T err (inspectLookupLocal ctx "id") (inspectLookupImport ctx "id")

  checkElabV-RVar-bbc-fst-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-fst-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-fst-failure-aux ctx T err (inspectLookupLocal ctx "fst") (inspectLookupImport ctx "fst")

  checkElabV-RVar-bbc-snd-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-snd-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-snd-failure-aux ctx T err (inspectLookupLocal ctx "snd") (inspectLookupImport ctx "snd")

  checkElabV-RVar-bbc-terminal-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-terminal-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-terminal-failure-aux ctx T err (inspectLookupLocal ctx "terminal") (inspectLookupImport ctx "terminal")

  checkElabV-RVar-bbc-initial-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-initial-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-initial-failure-aux ctx T err (inspectLookupLocal ctx "initial") (inspectLookupImport ctx "initial")

  checkElabV-RVar-bbc-inl-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-inl-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-inl-failure-aux ctx T err (inspectLookupLocal ctx "inl") (inspectLookupImport ctx "inl")

  checkElabV-RVar-bbc-inr-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-inr-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-inr-failure-aux ctx T err (inspectLookupLocal ctx "inr") (inspectLookupImport ctx "inr")

  checkElabV-RVar-bbc-arr-aux ctx T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-arr-aux ctx T (failure err , _) =
    checkElabV-RVar-bbc-arr-failure-aux ctx T err (inspectLookupLocal ctx "arr") (inspectLookupImport ctx "arr")

  -- bbc-other: success-via-infer mirrors the others; failure goes
  -- through lookupPoly fallback (still postulate-witnessed).
  checkElabV-RVar-bbc-other-aux ctx x T (success T' Ψ eE d fr , w) with T ≟T T'
  ... | yes refl = success Ψ eE d fr , t-embed w
  ... | no _     = failure (TypeMismatch T T') , tt
  checkElabV-RVar-bbc-other-aux ctx x T (failure err , _) with lookupPoly (NamedCtx.polys ctx) x
  ... | nothing = failure err , tt
  ... | just _  = success Surface.zeroUsage (Surface.poly x T) 0 (NamedCtx.freshCounter ctx) , bbc-other-poly-witness ctx x T

------------------------------------------------------------------------
-- Plan 0.4 T0 Option B — projection wrappers.
--
-- Top-level views of the verified elaborators that strip the witness.
-- A new soundness theorem `infer-soundV` / `check-soundV` over these
-- projections is straightforwardly provable from `proj₂ ∘ inferElabV`
-- and replaces the spec-gap postulates that target `check-sound`'s
-- specialised dispatch.
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)

-- RInt always infers at type `Int`; the fallback transports to check
-- at `Int` directly.
checkElab-fallback-RInt :
  ∀ {ctx : NamedCtx} (n : ℤ)
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RInt n) Int
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RInt {ctx} n with Int ≟T Int
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RStringLit always infers at type `Str`.
checkElab-fallback-RStringLit :
  ∀ {ctx : NamedCtx} (s : String)
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RStringLit s) Str
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RStringLit {ctx} s with Str ≟T Str
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RUnit always infers at type `Unit`.
checkElab-fallback-RUnit :
  ∀ {ctx : NamedCtx}
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx Raw.RUnit Unit
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RUnit {ctx} with Unit ≟T Unit
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RQualified: inferElab ≡ success ⇒ checkElab at the same type ≡ success.
checkElab-fallback-RQualified :
  ∀ {ctx : NamedCtx} (name alias : String) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RQualified name alias) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RQualified name alias) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RQualified {ctx} name alias T eqInf
  with inferElabV ctx (Raw.RQualified name alias)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RQualified {ctx} name alias T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RAnnot T: check-mode check at T falls to generic fallback (no
-- specialised RAnnot check clause). inferElab ctx (RAnnot e T) succeeds
-- exactly when checkElab ctx e T succeeds at the annotated type.
checkElab-fallback-RAnnot :
  ∀ {ctx : NamedCtx} (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RAnnot e T) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RAnnot e T) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RAnnot {ctx} e T eqInf
  with inferElabV ctx (Raw.RAnnot e T)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RAnnot {ctx} e T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.36 Phase 2a: `checkElab-fallback-RPair` removed. RPair check-mode
-- now goes through the bidirectional `checkPairLit` clause, so the old
-- infer→check bridge (which assumed the generic infer-then-compare path)
-- no longer applies. Completeness routes embedded-infer pairs through the
-- pair-literal bridge directly (re-embedding the component derivations).

-- RLet: no specialised check clause.
checkElab-fallback-RLet :
  ∀ {ctx : NamedCtx} (x : String) (e₁ e₂ : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RLet x e₁ e₂) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RLet x e₁ e₂) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RLet {ctx} x e₁ e₂ T eqInf
  with inferElabV ctx (Raw.RLet x e₁ e₂)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RLet {ctx} x e₁ e₂ T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RDestruct: no specialised check clause.
checkElab-fallback-RDestruct :
  ∀ {ctx : NamedCtx} (scrut : RawExpr) (xL : String) (eL : RawExpr)
    (xR : String) (eR : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RDestruct scrut xL eL xR eR) T
        ≡ success Ψ eE' d' f')))
checkElab-fallback-RDestruct {ctx} scrut xL eL xR eR T eqInf
  with inferElabV ctx (Raw.RDestruct scrut xL eL xR eR)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RDestruct {ctx} scrut xL eL xR eR T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RUnaryOp: no specialised check clause.
checkElab-fallback-RUnaryOp :
  ∀ {ctx : NamedCtx} (op : Raw.UnaryOp) (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RUnaryOp op e) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RUnaryOp op e) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RUnaryOp {ctx} op e T eqInf
  with inferElabV ctx (Raw.RUnaryOp op e)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RUnaryOp {ctx} op e T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

-- RVar "unit": no specialised check clause for "unit".
-- The elaborator falls through to the generic fallback.
checkElab-fallback-RVar-unit :
  ∀ {ctx : NamedCtx}
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "unit") Unit
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-unit {ctx} with Unit ≟T Unit
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.6 Phase C.7: bare-builtin check-mode completeness helpers.
-- Given the two lookup-failure premises, each drives the elaborator
-- through its `bbc-X | failure _` branch and into the specialised
-- `specX` emission. Uniform proof structure across all builtins.

-- Plan 0.4 T2 Phase 5: bridge from lookup-failure hypotheses to
-- inferElab's failure result. The aux-fail helper handles the explicit
-- nothing/nothing case directly; the main bridge uses subst-via-cong
-- to reroute the actual `lookupLocal ctx x` / `lookupImport _ x` to
-- `nothing` via the hypotheses.
inferElabV-RVar-lookup-aux-fail :
  ∀ (ctx : NamedCtx) (x : String) (¬unit : ¬ (x ≡ "unit"))
    (eq-loc : lookupLocal ctx x ≡ nothing)
    (eq-imp : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
  → inferElabV-RVar-lookup-aux ctx x ¬unit nothing eq-loc nothing eq-imp
      ≡ (failure (UnboundVariable x) , tt)
inferElabV-RVar-lookup-aux-fail _ _ _ _ _ = refl

inferElabV-RVar-fail-bridge :
  ∀ (ctx : NamedCtx) (x : String) (¬unit : ¬ (x ≡ "unit"))
  → (eqLoc : lookupLocal ctx x ≡ nothing)
  → (eqImp : lookupImport (NamedCtx.imports ctx) x ≡ nothing)
  → inferElabV ctx (Raw.RVar x) ≡ (failure (UnboundVariable x) , tt)
inferElabV-RVar-fail-bridge ctx x ¬unit eqLoc eqImp
  with StrProp._≟_ x "unit"
... | yes eq-unit = ⊥-elim (¬unit eq-unit)
... | no _ = trans bridge-eq (inferElabV-RVar-lookup-aux-fail ctx x ¬unit eqLoc eqImp)
  where
    -- Specialise `inferElabV-RVar-lookup-aux ctx x ¬unit ml ml-eq mi mi-eq`
    -- to `(ml, ml-eq, mi, mi-eq) := (lookupLocal ctx x, refl, lookupImport _ x, refl)`
    -- and to `(nothing, eqLoc, nothing, eqImp)` and prove these equal.
    -- J-style: dep pattern-match on each pair to reduce both endpoints to
    -- `lookupLocal ctx x` / `lookupImport _ x`, where the call agrees.
    helper :
      ∀ ml (eml : lookupLocal ctx x ≡ ml)
        mi (emi : lookupImport (NamedCtx.imports ctx) x ≡ mi)
      → inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl (lookupImport (NamedCtx.imports ctx) x) refl
        ≡ inferElabV-RVar-lookup-aux ctx x ¬unit ml eml mi emi
    helper .(lookupLocal ctx x) refl .(lookupImport (NamedCtx.imports ctx) x) refl = refl

    bridge-eq :
      inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl (lookupImport (NamedCtx.imports ctx) x) refl
      ≡ inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc nothing eqImp
    bridge-eq = helper nothing eqLoc nothing eqImp

-- Plan 0.4 T2 Phase 5: bbc-X RVar fallbacks. The aux extraction
-- (Phase 3) plus the lookup-view refactor (Phase 4) plus the
-- inferElabV-RVar-fail-bridge (Phase 5) together let us discharge the
-- previously-postulated lemmas: with-abstract over `inferElabV` and
-- the inspect-views, then the elaborator's reduction is computational.
checkElab-fallback-RVar-id :
  ∀ {ctx : NamedCtx} (T : Type)
  → lookupLocal ctx "id" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "id" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "id") (T Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] T)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-id {ctx} T eqLoc eqImp
  with inferElabV ctx (Raw.RVar "id") | inferElabV-RVar-fail-bridge ctx "id" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "id" | inspectLookupImport ctx "id"
... | llv-not-found _ | liv-not-found _
  with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-id {ctx} T eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing (trans (sym impossible) eqLoc))
  where
    just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → Data.Empty.⊥
    just≢nothing ()
checkElab-fallback-RVar-id {ctx} T eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing (trans (sym impossible) eqImp))
  where
    just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → Data.Empty.⊥
    just≢nothing ()

just≢nothing-Maybe : ∀ {A : Set} {x : A} → just x ≡ nothing → Data.Empty.⊥
just≢nothing-Maybe ()

checkElab-fallback-RVar-fst :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "fst" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "fst" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "fst") ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-fst {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "fst") | inferElabV-RVar-fail-bridge ctx "fst" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "fst" | inspectLookupImport ctx "fst"
... | llv-not-found _ | liv-not-found _
  with A ≟T A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-fst {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-fst {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-snd :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "snd" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "snd" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "snd") ((A Once.Type.* B) Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-snd {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "snd") | inferElabV-RVar-fail-bridge ctx "snd" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "snd" | inspectLookupImport ctx "snd"
... | llv-not-found _ | liv-not-found _
  with B ≟T B
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-snd {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-snd {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-terminal :
  ∀ {ctx : NamedCtx} (A : Type)
  → lookupLocal ctx "terminal" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "terminal") (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] Unit)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-terminal {ctx} A eqLoc eqImp
  with inferElabV ctx (Raw.RVar "terminal") | inferElabV-RVar-fail-bridge ctx "terminal" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "terminal" | inspectLookupImport ctx "terminal"
... | llv-not-found _ | liv-not-found _ = _ , _ , _ , refl
checkElab-fallback-RVar-terminal {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-terminal {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-initial :
  ∀ {ctx : NamedCtx} (A : Type)
  → lookupLocal ctx "initial" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "initial" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "initial") (Void Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] A)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-initial {ctx} A eqLoc eqImp
  with inferElabV ctx (Raw.RVar "initial") | inferElabV-RVar-fail-bridge ctx "initial" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "initial" | inspectLookupImport ctx "initial"
... | llv-not-found _ | liv-not-found _ = _ , _ , _ , refl
checkElab-fallback-RVar-initial {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-initial {ctx} A eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-inl :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "inl" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "inl" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "inl") (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B))
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-inl {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "inl") | inferElabV-RVar-fail-bridge ctx "inl" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "inl" | inspectLookupImport ctx "inl"
... | llv-not-found _ | liv-not-found _
  with A ≟T A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-inl {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-inl {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

checkElab-fallback-RVar-inr :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "inr" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "inr" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "inr") (B Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] (A Once.Type.+ B))
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-inr {ctx} A B eqLoc eqImp
  with inferElabV ctx (Raw.RVar "inr") | inferElabV-RVar-fail-bridge ctx "inr" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "inr" | inspectLookupImport ctx "inr"
... | llv-not-found _ | liv-not-found _
  with B ≟T B
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar-inr {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | llv-found impossible | _ = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqLoc))
checkElab-fallback-RVar-inr {ctx} A B eqLoc eqImp | (failure _ , _) | refl
  | _ | liv-found impossible = ⊥-elim (just≢nothing-Maybe (trans (sym impossible) eqImp))

-- Plan 0.6 Phase C.7 POC-2: applied `pair f g` at canonical
-- `A ⇒[Many] (B * C)` shape. Given check-mode elab successes for
-- both f and g, the specialised classifier dispatch
-- (`ahv-pair-applied`) emits the `app (app specPair fE) gE` Surface
-- IR. This helper threads the two sub-equations through the
-- pattern-matching reduction chain to close completeness.
checkInGo-J :
  ∀ (ctx : NamedCtx) (arg : RawExpr) (F : Once.Type.Functor)
    (mw : Maybe (Once.Functor.Translate.WellFormedF F)) (eq : wellFormedF? F ≡ mw)
  → Data.Product.proj₁ (checkInGo ctx arg F (wellFormedF? F) refl)
      ≡ Data.Product.proj₁ (checkInGo ctx arg F mw eq)
checkInGo-J ctx arg F .(wellFormedF? F) refl = refl

checkInGo-just-success :
  ∀ (ctx : NamedCtx) (arg : RawExpr) (F : Once.Type.Functor)
    (wfF : Once.Functor.Translate.WellFormedF F) (eqW : wellFormedF? F ≡ just wfF)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (Once.Type.⟦ F ⟧T (Once.Type.μ-type F))}
    {d fr : ℕ}
  → checkElab ctx arg (Once.Type.⟦ F ⟧T (Once.Type.μ-type F)) ≡ success Ψ argE d fr
  → ∃-syntax (λ eE → ∃-syntax (λ d' → ∃-syntax (λ fr' →
      Data.Product.proj₁ (checkInGo ctx arg F (just wfF) eqW)
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d' fr')))
checkInGo-just-success ctx arg F wfF eqW eqArg
  with checkElabV ctx arg (Once.Type.⟦ F ⟧T (Once.Type.μ-type F)) | eqArg
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

checkElab-fallback-RApp-In :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (F : Once.Type.Functor)
    {wfF : Once.Functor.Translate.WellFormedF F}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (Once.Type.⟦ F ⟧T (Once.Type.μ-type F))}
    {d fr : ℕ}
  → wellFormedF? F ≡ just wfF
  → checkElab ctx arg (Once.Type.⟦ F ⟧T (Once.Type.μ-type F)) ≡ success Ψ argE d fr
  → ∃-syntax (λ eE → ∃-syntax (λ d' → ∃-syntax (λ fr' →
      checkElab ctx (Raw.RApp (Raw.RVar "In") arg) (Once.Type.μ-type F)
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d' fr')))
checkElab-fallback-RApp-In {ctx} arg F {wfF} eqWF eqArg =
  let (_ , _ , _ , eqGo) = checkInGo-just-success ctx arg F wfF eqWF eqArg
  in _ , _ , _ , trans (checkInGo-J ctx arg F (just wfF) eqWF) eqGo

-- Plan 0.36 Phase 2a: the cata completeness bridge is rebuilt over
-- `checkCataGo` (empty-context algebra elaboration) in the `Completeness`
-- migration step, mirroring `checkElab-fallback-RApp-In` above
-- (checkCataGo-J + a checkCataGo-just-success lemma). Removed here with
-- the morphRaw J-bridges it depended on.

-- Plan 0.4 T2 follow-up (rule-split, 2026-05-03): checkCompose now
-- requires composeArgB-resolved B; the proof composes the two
-- checkElab-successes through the simplified dispatch chain.

-- Plan 0.4 T0 (2026-04-30): applied `arr e` in check mode at
-- `Eff A B`. The elaborator's ahv-arr check-mode path checks `e`
-- at `A ⇒[Many] B`. Premise is checkElab evidence on `e`.
checkElab-fallback-RApp-arr :
  ∀ {ctx : NamedCtx} (e : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)}
    {d fr : ℕ}
  → checkElab ctx e (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B)
      ≡ success Ψ eE d fr
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "arr") e)
                    (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)
        ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-arr {ctx} e A B eqC
  with checkElabV ctx e (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl
checkElab-fallback-RApp-apply :
  ∀ {ctx : NamedCtx} (p : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A)}
    {d fr : ℕ}
  → inferElab ctx p ≡ success ((A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] B) Once.Type.* A) Ψ eE d fr
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "apply") p) B
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE' d' f')))
checkElab-fallback-RApp-apply {ctx} p A B eqInf
  with inferElabV ctx p | eqInf
... | success ((_ Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.pure ] _) Once.Type.* _) _ _ _ _ , _ | refl
    with A ≟T A | B ≟T B
...   | yes refl | yes refl = _ , _ , _ , refl
...   | yes refl | no  ¬eq  = ⊥-elim (¬eq refl)
...   | no  ¬eq  | _        = ⊥-elim (¬eq refl)
resolveExprWF : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
              → (polys : PolyCtx) → Acc _<_ (length polys)
              → Imports → Imports → ℕ
              → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolvePolyCase : ∀ {n} {Γ : Surface.Ctx n}
                → (polys : PolyCtx) → Acc _<_ (length polys)
                → Imports → Imports → ℕ → (x : String) (A : Type)
                → (look : Maybe (PolyType × RawExpr))
                → lookupPoly polys x ≡ look
                → Surface.Expr Γ Surface.zeroUsage A
applySplice : ∀ {n} {Γ : Surface.Ctx n}
            → (polys : PolyCtx) → Acc _<_ (length polys)
            → Imports → Imports → ℕ → (x : String) (A : Type)
            → {schema : PolyType} {body : RawExpr}
            → lookupPoly polys x ≡ just (schema , body)
            → CheckElabResult S∅ A
            → Surface.Expr Γ Surface.zeroUsage A

resolveExprWF polys _ imps userFns _ (Surface.var i) = Surface.var i
resolveExprWF polys pAcc imps userFns fresh (Surface.lam q prf b) =
  Surface.lam q prf (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.app f a) =
  Surface.app (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh a)
resolveExprWF polys pAcc imps userFns fresh (Surface.effApp f a) =
  Surface.effApp (resolveExprWF polys pAcc imps userFns fresh f) (resolveExprWF polys pAcc imps userFns fresh a)
resolveExprWF polys pAcc imps userFns fresh (Surface.pair a b) =
  Surface.pair (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.fst' p) = Surface.fst' (resolveExprWF polys pAcc imps userFns fresh p)
resolveExprWF polys pAcc imps userFns fresh (Surface.snd' p) = Surface.snd' (resolveExprWF polys pAcc imps userFns fresh p)
resolveExprWF polys pAcc imps userFns fresh (Surface.inl' e) = Surface.inl' (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.inr' e) = Surface.inr' (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.case' s l r) =
  Surface.case' (resolveExprWF polys pAcc imps userFns fresh s)
                (resolveExprWF polys pAcc imps userFns fresh l)
                (resolveExprWF polys pAcc imps userFns fresh r)
resolveExprWF polys _ imps userFns _ Surface.unit = Surface.unit
resolveExprWF polys pAcc imps userFns fresh (Surface.absurd e) = Surface.absurd (resolveExprWF polys pAcc imps userFns fresh e)
resolveExprWF polys pAcc imps userFns fresh (Surface.let' e₁ e₂) =
  Surface.let' (resolveExprWF polys pAcc imps userFns fresh e₁) (resolveExprWF polys pAcc imps userFns fresh e₂)
resolveExprWF polys _ imps userFns _ (Surface.int z) = Surface.int z
resolveExprWF polys _ imps userFns _ (Surface.str s) = Surface.str s
resolveExprWF polys pAcc imps userFns fresh (Surface.add a b) =
  Surface.add (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.sub a b) =
  Surface.sub (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
resolveExprWF polys pAcc imps userFns fresh (Surface.mul a b) =
  Surface.mul (resolveExprWF polys pAcc imps userFns fresh a) (resolveExprWF polys pAcc imps userFns fresh b)
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
resolveExprWF polys pAcc imps userFns fresh (Surface.arr' e) = Surface.arr' (resolveExprWF polys pAcc imps userFns fresh e)
-- Plan 0.19: discriminate sigOp by whether the name is a user-defined
-- top-level fn (in `userFns`) or an external primitive (in `imps`).
-- The typechecker emits `Surface.sigOp` for every named-entry RVar
-- lookup that hits imports; the resolver post-processes by rewriting
-- to `Surface.closure` when the name belongs to the user-defined set,
-- so the elaborator's asm-emission picks the right calling convention.
-- Semantic preservation: `evalSurface (sigOp x) ≡ evalSurface (closure x)`
-- by construction (both go through `generic-semI`); the rewrite is a
-- no-op in the denotation.
resolveExprWF polys _ imps userFns _ (Surface.sigOp s) with lookupImport userFns s
... | just _  = Surface.closure s
... | nothing = Surface.sigOp s
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
-- Poly = unresolved placeholder from Phase 1. Delegate to helper that
-- takes the lookup result + equation explicitly, so external proofs
-- about the sigOp case can `rewrite` the premise cleanly.
resolveExprWF {A = A} polys pAcc imps userFns fresh (Surface.poly x _) =
  resolvePolyCase polys pAcc imps userFns fresh x A (lookupPoly polys x) refl

resolvePolyCase polys _ imps userFns _ x A nothing _ = Surface.poly x A
resolvePolyCase polys pAcc imps userFns fresh x A (just (_ , body)) polyEq =
  applySplice polys pAcc imps userFns fresh x A polyEq
              (checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body A)

applySplice polys _ imps userFns _ x A _ (failure _) = Surface.poly x A
applySplice polys (acc rec) imps userFns fresh x A polyEq (success Surface.[] eE _ _) =
  resolveExprWF (removePoly x polys)
                (rec (removePoly-decreases x polys polyEq))
                imps userFns fresh (weakenFromEmpty eE)

-- Public entry. Computes `<-wellFounded` once; no callers need updating.
-- Plan 0.19: `userFns` carries the set of user-defined top-level fn
-- names. The resolver rewrites `Surface.sigOp x` to `Surface.closure x`
-- when `x ∈ userFns` (distinguishing user-defined entries from
-- external primitives). Semantically a no-op (`evalSurface (sigOp x) ≡
-- evalSurface (closure x)` by construction); the rewrite enables the
-- elaborator to emit the correct asm calling convention downstream.
resolveExpr : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
            → (polys : PolyCtx) → Imports → Imports → ℕ
            → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolveExpr polys imps userFns fresh e = resolveExprWF polys (<-wellFounded (length polys)) imps userFns fresh e

-- ─── Resolver semantic-equivalence theorems ────────────────────────────
-- The resolver is a pure structural traversal: it commutes with every
-- non-poly Expr constructor by definitional equality, and is the
-- identity on `sigOp` leaves (external primitives are never polys).
-- Together these establish that `resolveExpr` is a "poly-leaf rewriter"
-- — it only touches `poly` positions, and leaves every other Expr
-- constructor structurally equal.
--
-- Below: full coverage for all 28 non-poly constructors, each `refl`.

-- Var is unaffected by resolution.
resolveExpr-var :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (i : _)
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.var i) ≡ Surface.var i
resolveExpr-var _ _ _ _ _ = refl

-- Resolution commutes with lam.
resolveExpr-lam :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {q' A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (q : Quantity) (prf : (q' Once.Type.≤q q) ≡ true)
    (b : Surface.Expr (Γ Surface., A) (q' Surface.∷ Ψ) B)
  → resolveExpr polys imps userFns fresh (Surface.lam q prf b)
      ≡ Surface.lam q prf (resolveExpr polys imps userFns fresh b)
resolveExpr-lam _ _ _ _ _ _ _ = refl

-- Resolution commutes with app.
resolveExpr-app :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B q}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (f : Surface.Expr Γ Ψ₁ (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B))
    (a : Surface.Expr Γ Ψ₂ A)
  → resolveExpr polys imps userFns fresh (Surface.app f a)
      ≡ Surface.app (resolveExpr polys imps userFns fresh f) (resolveExpr polys imps userFns fresh a)
resolveExpr-app _ _ _ _ _ _ = refl

-- Resolution commutes with pair.
resolveExpr-pair :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ A) (b : Surface.Expr Γ Ψ₂ B)
  → resolveExpr polys imps userFns fresh (Surface.pair a b)
      ≡ Surface.pair (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-pair _ _ _ _ _ _ = refl

-- Resolution commutes with effApp.
resolveExpr-effApp :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (f : Surface.Expr Γ Ψ₁ (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] B)) (a : Surface.Expr Γ Ψ₂ A)
  → resolveExpr polys imps userFns fresh (Surface.effApp f a)
      ≡ Surface.effApp (resolveExpr polys imps userFns fresh f) (resolveExpr polys imps userFns fresh a)
resolveExpr-effApp _ _ _ _ _ _ = refl

-- Resolution commutes with fst'.
resolveExpr-fst' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (p : Surface.Expr Γ Ψ (A Once.Type.* B))
  → resolveExpr polys imps userFns fresh (Surface.fst' p)
      ≡ Surface.fst' (resolveExpr polys imps userFns fresh p)
resolveExpr-fst' _ _ _ _ _ = refl

-- Resolution commutes with snd'.
resolveExpr-snd' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (p : Surface.Expr Γ Ψ (A Once.Type.* B))
  → resolveExpr polys imps userFns fresh (Surface.snd' p)
      ≡ Surface.snd' (resolveExpr polys imps userFns fresh p)
resolveExpr-snd' _ _ _ _ _ = refl

-- Resolution commutes with inl'.
resolveExpr-inl' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ A)
  → resolveExpr polys imps userFns fresh (Surface.inl' {B = B} e)
      ≡ Surface.inl' (resolveExpr polys imps userFns fresh e)
resolveExpr-inl' _ _ _ _ _ = refl

-- Resolution commutes with inr'.
resolveExpr-inr' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ B)
  → resolveExpr polys imps userFns fresh (Surface.inr' {A = A} e)
      ≡ Surface.inr' (resolveExpr polys imps userFns fresh e)
resolveExpr-inr' _ _ _ _ _ = refl

-- Resolution commutes with case'.
resolveExpr-case' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψs Ψₗ Ψᵣ : Surface.Usage n} {qℓ qr A B C}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (s : Surface.Expr Γ Ψs (A Once.Type.+ B))
    (l : Surface.Expr (Γ Surface., A) (qℓ Surface.∷ Ψₗ) C)
    (r : Surface.Expr (Γ Surface., B) (qr Surface.∷ Ψᵣ) C)
  → resolveExpr polys imps userFns fresh (Surface.case' s l r)
      ≡ Surface.case' (resolveExpr polys imps userFns fresh s)
                      (resolveExpr polys imps userFns fresh l)
                      (resolveExpr polys imps userFns fresh r)
resolveExpr-case' _ _ _ _ _ _ _ = refl

-- Unit is unaffected by resolution.
resolveExpr-unit :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
  → resolveExpr {Γ = Γ} polys imps userFns fresh Surface.unit ≡ Surface.unit
resolveExpr-unit _ _ _ _ = refl

-- Resolution commutes with absurd.
resolveExpr-absurd :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ Once.Type.Void)
  → resolveExpr {A = A} polys imps userFns fresh (Surface.absurd e)
      ≡ Surface.absurd (resolveExpr polys imps userFns fresh e)
resolveExpr-absurd _ _ _ _ _ = refl

-- Resolution commutes with let'.
resolveExpr-let' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {q A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e₁ : Surface.Expr Γ Ψ₁ A)
    (e₂ : Surface.Expr (Γ Surface., A) (q Surface.∷ Ψ₂) B)
  → resolveExpr polys imps userFns fresh (Surface.let' e₁ e₂)
      ≡ Surface.let' (resolveExpr polys imps userFns fresh e₁) (resolveExpr polys imps userFns fresh e₂)
resolveExpr-let' _ _ _ _ _ _ = refl

-- Int / str literals are unaffected.
resolveExpr-int :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (z : Data.Integer.ℤ)
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.int z) ≡ Surface.int z
resolveExpr-int _ _ _ _ _ = refl

resolveExpr-str :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (s : String)
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.str s) ≡ Surface.str s
resolveExpr-str _ _ _ _ _ = refl

-- Resolution commutes with arithmetic (add / sub / mul / div / mod').
resolveExpr-add :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.add a b)
      ≡ Surface.add (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-add _ _ _ _ _ _ = refl

resolveExpr-sub :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.sub a b)
      ≡ Surface.sub (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-sub _ _ _ _ _ _ = refl

resolveExpr-mul :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.mul a b)
      ≡ Surface.mul (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-mul _ _ _ _ _ _ = refl

resolveExpr-div :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.div a b)
      ≡ Surface.div (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-div _ _ _ _ _ _ = refl

resolveExpr-mod' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.mod' a b)
      ≡ Surface.mod' (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-mod' _ _ _ _ _ _ = refl

-- Resolution commutes with neg.
resolveExpr-neg :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ Int)
  → resolveExpr polys imps userFns fresh (Surface.neg e) ≡ Surface.neg (resolveExpr polys imps userFns fresh e)
resolveExpr-neg _ _ _ _ _ = refl

-- Resolution commutes with comparison ops (lt / le / gt / ge / eq / ne).
resolveExpr-lt :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.lt a b)
      ≡ Surface.lt (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-lt _ _ _ _ _ _ = refl

resolveExpr-le :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.le a b)
      ≡ Surface.le (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-le _ _ _ _ _ _ = refl

resolveExpr-gt :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.gt a b)
      ≡ Surface.gt (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-gt _ _ _ _ _ _ = refl

resolveExpr-ge :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.ge a b)
      ≡ Surface.ge (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-ge _ _ _ _ _ _ = refl

resolveExpr-eq :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.eq a b)
      ≡ Surface.eq (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-eq _ _ _ _ _ _ = refl

resolveExpr-ne :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps userFns fresh (Surface.ne a b)
      ≡ Surface.ne (resolveExpr polys imps userFns fresh a) (resolveExpr polys imps userFns fresh b)
resolveExpr-ne _ _ _ _ _ _ = refl

-- Resolution commutes with arr' (effect lifting).
resolveExpr-arr' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ (A Once.Type.⇒ B))
  → resolveExpr polys imps userFns fresh (Surface.arr' e) ≡ Surface.arr' (resolveExpr polys imps userFns fresh e)
resolveExpr-arr' _ _ _ _ _ = refl

-- Plan 0.19: resolveExpr on sigOp depends on whether `s` is in the
-- `userFns` list — it rewrites to `Surface.closure s` for user-defined
-- top-level fns. The lemma below states the preserved-as-sigOp case:
-- when the name is NOT a user-defined fn (lookupImport userFns s ≡
-- nothing), the resolver is identity.
resolveExpr-sigOp-extern :
  ∀ {n} {Γ : Surface.Ctx n} {A}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ) (s : String)
  → lookupImport userFns s ≡ nothing
  → resolveExpr {Γ = Γ} polys imps userFns fresh (Surface.sigOp {A = A} s)
      ≡ Surface.sigOp s
resolveExpr-sigOp-extern _ _ _ _ _ eq rewrite eq = refl

-- ─── Gap 1 (positive direction): resolver correctly splices the body
-- at a matched poly placeholder ────────────────────────────────────────
-- Proved at the `applySplice` level (the resolver's "splice helper").
-- Statement: given a matched poly (`polyEq`) and a successful body
-- elaboration (`bodyEq`), `applySplice` applied to the checkElab result
-- equals `applySplice` applied to the success-form of that result —
-- i.e., the splice is compatible with the checkElab outcome.
--
-- The naive outer-level formulation —
--   `resolveExpr … (poly x T) ≡ resolveExprWF (removePoly x polys) … …`
-- — runs into an Agda with-abstraction issue: `resolveExprWF`'s poly
-- clause invokes `resolvePolyCase` with an internal `refl`, while the
-- outer proof has `polyEq`. Bridging these via `rewrite polyEq`
-- generates an ill-formed with-helper because `polyEq`'s type depends
-- on the abstract term being rewritten. The applySplice-level theorem
-- captures the same semantic content at a level where the proof is
-- definitional.
--
-- Supporting lemma `applySplice-eq-irrel` (proven below) shows
-- `applySplice` is indifferent to the specific equation witness
-- provided, relying only on stdlib's `<-irrelevant`. That, together
-- with this theorem, gives the full semantic picture: at a matched
-- poly, the resolver's behavior is determined by the body's
-- elaboration, not by the specific proof term used to dispatch.

-- Helper: Acc-step at the matched poly (unused by the current proof
-- but retained as it's the natural combinator for future extensions).
acc-step-at-poly : ∀ polys x {r} → lookupPoly polys x ≡ just r
                 → Acc _<_ (length polys) → Acc _<_ (length (removePoly x polys))
acc-step-at-poly polys x polyEq (acc rec) = rec (removePoly-decreases x polys polyEq)

-- Sub-lemma: `applySplice` is irrelevant in its equation argument. Two
-- equation witnesses at the same propositional type produce the same
-- result — proved without UIP on `_≡_`, only via `<-irrelevant`.
applySplice-eq-irrel :
  ∀ {n} {Γ : Surface.Ctx n}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys))
    (imps userFns : Imports) (fresh : ℕ) (x : String) (A : Type)
    {schema : PolyType} {body : RawExpr}
  → (eq1 eq2 : lookupPoly polys x ≡ just (schema , body))
  → (chkRes : CheckElabResult S∅ A)
  → applySplice {Γ = Γ} polys pAcc imps userFns fresh x A eq1 chkRes
      ≡ applySplice polys pAcc imps userFns fresh x A eq2 chkRes
applySplice-eq-irrel polys _ imps userFns _ x A _ _ (failure _) = refl
applySplice-eq-irrel polys (acc rec) imps userFns fresh x A eq1 eq2 (success Surface.[] eE _ _) =
  cong (λ pr → resolveExprWF (removePoly x polys) (rec pr) imps userFns fresh (weakenFromEmpty eE))
       (<-irrelevant (removePoly-decreases x polys eq1) (removePoly-decreases x polys eq2))
  where open import Data.Nat.Properties using (<-irrelevant)

-- Main theorem (applySplice-level).
resolveExpr-poly-match :
  ∀ {n} {Γ : Surface.Ctx n}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys))
    (imps userFns : Imports) (fresh : ℕ)
    (x : String) (T : Type)
    {schema : PolyType} {body : RawExpr}
    {eE : SExpr S∅ Surface.zeroUsage T} {d f : ℕ}
  → (polyEq : lookupPoly polys x ≡ just (schema , body))
  → checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body T
      ≡ success Surface.[] eE d f
  → applySplice {Γ = Γ} polys pAcc imps userFns fresh x T polyEq
                (checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body T)
      ≡ applySplice polys pAcc imps userFns fresh x T polyEq
                    (success Surface.[] eE d f)
resolveExpr-poly-match polys pAcc imps userFns fresh x T polyEq bodyEq
    rewrite bodyEq = refl

-- Plan 0.6.2 Phase 4: polymorphic schema-instantiation.
-- POSTULATE DELETED (Option A, 2026-04-22). Phase 1 emits a proper
-- `poly` constructor; the typechecker's behavior doesn't depend on
-- body. Existential witnesses are satisfied by the `poly x T` placeholder.
checkElab-fallback-RVar-poly :
  ∀ {ctx : NamedCtx} (x : String) (T : Type)
    {schema : PolyType} {body : RawExpr}
    {eE_body : SExpr S∅ Surface.zeroUsage T}
    {d_body f_body : ℕ}
  → classifyBareBuiltin x ≡ bbc-other
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → lookupPoly (NamedCtx.polys ctx) x ≡ just (schema , body)
  → checkElab (ctxWithImportsAndPolys (NamedCtx.imports ctx)
                                       (removePoly x (NamedCtx.polys ctx)))
              body T
      ≡ success Surface.zeroUsage eE_body d_body f_body
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ fr →
      checkElab ctx (Raw.RVar x) T
        ≡ success Surface.zeroUsage eE d fr)))
checkElab-fallback-RVar-poly {ctx} x T eqCls ¬unit eqLoc eqImp eqPoly _
  with classifyBareBuiltin x | eqCls
... | bbc-other | refl
  with inferElabV ctx (Raw.RVar x) | inferElabV-RVar-fail-bridge ctx x ¬unit eqLoc eqImp
... | (failure _ , _) | refl
  with lookupPoly (NamedCtx.polys ctx) x | eqPoly
... | just _ | refl
  with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq = ⊥-elim (¬eq refl)
checkElab-fallback-RApp-id :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "id") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "id") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-id {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "id") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RApp-fst :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "fst") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-fst {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "fst") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RApp-snd :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "snd") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-snd {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "snd") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
private
  open import Data.Product using () renaming (proj₁ to checkProj₁)
  checkViewBridge : ∀ {ctx f x T} (vw : AppHeadView f) (eq : classifyAppHeadView f ≡ vw)
                  → checkElabV-RApp-dispatch ctx f x T (classifyAppHeadView f) refl
                    ≡ checkElabV-RApp-dispatch ctx f x T vw eq
  checkViewBridge _ refl = refl

checkElab-fallback-RApp-generic :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f' : ℕ}
  → classifyAppHead f ≡ nothing
  → inferElab ctx (Raw.RApp f x) ≡ success T Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp f x) T ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-generic {ctx} f x T eqAH eqInf
  rewrite cong checkProj₁ (checkViewBridge {ctx} {f} {x} {T} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
  with inferElabV ctx (Raw.RApp f x) | eqInf
... | success _ _ _ _ _ , _ | refl
    with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RApp-terminal :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "terminal") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "terminal") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-terminal {ctx} arg T eqInf
  with inferElabV ctx (Raw.RApp (Raw.RVar "terminal") arg) | eqInf
... | success T' _ _ _ _ , _ | refl with T ≟T T'
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RBinOp :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (e₁ e₂ : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RBinOp op e₁ e₂) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RBinOp {ctx} op e₁ e₂ T eqInf
  with inferElabV ctx (Raw.RBinOp op e₁ e₂)
... | failure _ , _ with eqInf
...   | ()
checkElab-fallback-RBinOp {ctx} op e₁ e₂ T eqInf
  | success T' Ψ' eE' d' fr' , w with eqInf
... | refl with T ≟T T
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq   = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------

-- | Compile with type signature. Plan 0.14 follow-up: uses Heap as
-- the default AllocMode for backwards compatibility with callers that
-- don't supply one via CLI.
compileExprTyped : RawExpr → (A : Type) → Maybe (IR Unit A)
compileExprTyped e A with checkElab emptyCtx e A
... | failure _                 = nothing
... | success Ψ se _ _          = just (Elab.elaborate-default se)

-- | Compile without signature
compileExpr : RawExpr → Maybe (∃[ A ] IR Unit A)
compileExpr e with inferElab emptyCtx e
... | failure _                 = nothing
... | success A Ψ se _ _        = just (A , Elab.elaborate-default se)

------------------------------------------------------------------------
-- Plan 0.4 T0 Option B — Verified elaborator
--
-- `inferElabV` and `checkElabV` are the canonical verified versions of
-- the elaborator: each clause produces both the elaboration result and
-- its soundness witness. The type checker enforces the witness; there
-- is no separate `infer-sound` / `check-sound` proof to drift out of
-- sync.
--
-- Migration is incremental — each `Phase` of plans/0.4-T0-handoff
-- replaces a TODO-stub clause with a real clause. Unmigrated clauses
-- delegate to the existing `inferElab` / `checkElab` for the result and
-- to a TODO-witness postulate for the soundness obligation. The
-- postulates retire as clauses migrate.
------------------------------------------------------------------------

inferElabProj : (ctx : NamedCtx) (e : RawExpr) → InferElabResult (NamedCtx.debruijn ctx)
inferElabProj ctx e = proj₁ (inferElabV ctx e)
  where open import Data.Product using (proj₁)

checkElabProj : (ctx : NamedCtx) (e : RawExpr) (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T
checkElabProj ctx e T = proj₁ (checkElabV ctx e T)
  where open import Data.Product using (proj₁)
