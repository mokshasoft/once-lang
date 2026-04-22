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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Once.Type
open Once.Type using (showQuantity; showType) public
open import Once.CCC.IR as IR
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
open import Once.Surface.Elaborate as Elab using (elaborate)

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

-- | Decidable functor and type equality (mutually recursive)
mutual
  -- | Decidable functor equality
  _≟F_ : (F G : Functor) → Dec (F ≡ G)
  K A ≟F K B with A ≟T B
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  Id ≟F Id = yes refl
  (F₁ ⊕ G₁) ≟F (F₂ ⊕ G₂) with F₁ ≟F F₂ | G₁ ≟F G₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (F₁ ⊗ G₁) ≟F (F₂ ⊗ G₂) with F₁ ≟F F₂ | G₁ ≟F G₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
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
  (A₁ Once.Type.* B₁) ≟T (A₂ Once.Type.* B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (A₁ Once.Type.+ B₁) ≟T (A₂ Once.Type.+ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
  (A₁ ⇒[ q₁ ] B₁) ≟T (A₂ ⇒[ q₂ ] B₂) with A₁ ≟T A₂ | q₁ ≟q q₂ | B₁ ≟T B₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q | _ = no λ { refl → ¬q refl }
  ... | _ | _ | no ¬r = no λ { refl → ¬r refl }
  (Eff A₁ B₁) ≟T (Eff A₂ B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ { refl → ¬p refl }
  ... | _ | no ¬q = no λ { refl → ¬q refl }
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
  Unit ≟T Eff _ _ = no λ ()
  Void ≟T Unit = no λ ()
  Void ≟T Int = no λ ()
  Void ≟T Float = no λ ()
  Void ≟T Str = no λ ()
  Void ≟T Buffer = no λ ()
  Void ≟T (_ Once.Type.* _) = no λ ()
  Void ≟T (_ Once.Type.+ _) = no λ ()
  Void ≟T (_ ⇒[ _ ] _) = no λ ()
  Void ≟T Eff _ _ = no λ ()
  Int ≟T Unit = no λ ()
  Int ≟T Void = no λ ()
  Int ≟T Float = no λ ()
  Int ≟T Str = no λ ()
  Int ≟T Buffer = no λ ()
  Int ≟T (_ Once.Type.* _) = no λ ()
  Int ≟T (_ Once.Type.+ _) = no λ ()
  Int ≟T (_ ⇒[ _ ] _) = no λ ()
  Int ≟T Eff _ _ = no λ ()
  Float ≟T Unit = no λ ()
  Float ≟T Void = no λ ()
  Float ≟T Int = no λ ()
  Float ≟T Str = no λ ()
  Float ≟T Buffer = no λ ()
  Float ≟T (_ Once.Type.* _) = no λ ()
  Float ≟T (_ Once.Type.+ _) = no λ ()
  Float ≟T (_ ⇒[ _ ] _) = no λ ()
  Float ≟T Eff _ _ = no λ ()
  Str ≟T Unit = no λ ()
  Str ≟T Void = no λ ()
  Str ≟T Int = no λ ()
  Str ≟T Float = no λ ()
  Str ≟T Buffer = no λ ()
  Str ≟T (_ Once.Type.* _) = no λ ()
  Str ≟T (_ Once.Type.+ _) = no λ ()
  Str ≟T (_ ⇒[ _ ] _) = no λ ()
  Str ≟T Eff _ _ = no λ ()
  Buffer ≟T Unit = no λ ()
  Buffer ≟T Void = no λ ()
  Buffer ≟T Int = no λ ()
  Buffer ≟T Float = no λ ()
  Buffer ≟T Str = no λ ()
  Buffer ≟T (_ Once.Type.* _) = no λ ()
  Buffer ≟T (_ Once.Type.+ _) = no λ ()
  Buffer ≟T (_ ⇒[ _ ] _) = no λ ()
  Buffer ≟T Eff _ _ = no λ ()
  (_ Once.Type.* _) ≟T Unit = no λ ()
  (_ Once.Type.* _) ≟T Void = no λ ()
  (_ Once.Type.* _) ≟T Int = no λ ()
  (_ Once.Type.* _) ≟T Float = no λ ()
  (_ Once.Type.* _) ≟T Str = no λ ()
  (_ Once.Type.* _) ≟T Buffer = no λ ()
  (_ Once.Type.* _) ≟T (_ Once.Type.+ _) = no λ ()
  (_ Once.Type.* _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.* _) ≟T Eff _ _ = no λ ()
  (_ Once.Type.+ _) ≟T Unit = no λ ()
  (_ Once.Type.+ _) ≟T Void = no λ ()
  (_ Once.Type.+ _) ≟T Int = no λ ()
  (_ Once.Type.+ _) ≟T Float = no λ ()
  (_ Once.Type.+ _) ≟T Str = no λ ()
  (_ Once.Type.+ _) ≟T Buffer = no λ ()
  (_ Once.Type.+ _) ≟T (_ Once.Type.* _) = no λ ()
  (_ Once.Type.+ _) ≟T (_ ⇒[ _ ] _) = no λ ()
  (_ Once.Type.+ _) ≟T Eff _ _ = no λ ()
  (_ ⇒[ _ ] _) ≟T Unit = no λ ()
  (_ ⇒[ _ ] _) ≟T Void = no λ ()
  (_ ⇒[ _ ] _) ≟T Int = no λ ()
  (_ ⇒[ _ ] _) ≟T Float = no λ ()
  (_ ⇒[ _ ] _) ≟T Str = no λ ()
  (_ ⇒[ _ ] _) ≟T Buffer = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.* _) = no λ ()
  (_ ⇒[ _ ] _) ≟T (_ Once.Type.+ _) = no λ ()
  (_ ⇒[ _ ] _) ≟T Eff _ _ = no λ ()
  Eff _ _ ≟T Unit = no λ ()
  Eff _ _ ≟T Void = no λ ()
  Eff _ _ ≟T Int = no λ ()
  Eff _ _ ≟T Float = no λ ()
  Eff _ _ ≟T Str = no λ ()
  Eff _ _ ≟T Buffer = no λ ()
  Eff _ _ ≟T (_ Once.Type.* _) = no λ ()
  Eff _ _ ≟T (_ Once.Type.+ _) = no λ ()
  Eff _ _ ≟T (_ ⇒[ _ ] _) = no λ ()
  -- TVar removed from Type; now in PolyType (see Once.Type)
  -- OCP-0003: μ-type and ν-type cases
  (μ-type F₁) ≟T (μ-type F₂) with F₁ ≟F F₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  (ν-type F₁) ≟T (ν-type F₂) with F₁ ≟F F₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  μ-type _ ≟T Unit = no λ ()
  μ-type _ ≟T Void = no λ ()
  μ-type _ ≟T Int = no λ ()
  μ-type _ ≟T Float = no λ ()
  μ-type _ ≟T Str = no λ ()
  μ-type _ ≟T Buffer = no λ ()
  μ-type _ ≟T (_ Once.Type.* _) = no λ ()
  μ-type _ ≟T (_ Once.Type.+ _) = no λ ()
  μ-type _ ≟T (_ ⇒[ _ ] _) = no λ ()
  μ-type _ ≟T Eff _ _ = no λ ()
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
  ν-type _ ≟T Eff _ _ = no λ ()
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
  Eff _ _ ≟T μ-type _ = no λ ()
  Eff _ _ ≟T ν-type _ = no λ ()
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
-- QTT Usage Helpers
------------------------------------------------------------------------

-- Import usage operations from Surface.Syntax
open Surface using (zeroUsage; singleUse; _+ᵘ_; _*ᵘ_) public

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Named Context with de Bruijn Correspondence
------------------------------------------------------------------------

-- | Imported primitives from other modules (e.g., "S.exit0" → Eff Unit Unit)
-- These are populated from qualified imports like "import M as S"
Imports : Set
Imports = List (String × Type)

-- | Empty imports
emptyImports : Imports
emptyImports = []

-- | Polymorphic-definition context (plan 0.6.2). Carries each
-- user-declared poly def's schema and body so they can be
-- specialised at call sites via schema instantiation. Structurally
-- `List (name, schema, body)`; kept separate from `imports` (which
-- is ground-typed) because lookup resolves differently.
PolyCtx : Set
PolyCtx = List (String × PolyType × RawExpr)

emptyPolyCtx : PolyCtx
emptyPolyCtx = []

-- | Lookup a polymorphic def by name.
lookupPoly : PolyCtx → String → Maybe (PolyType × RawExpr)
lookupPoly [] _ = nothing
lookupPoly ((n , schema , body) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just (schema , body)
... | no  _ = lookupPoly rest x

-- | Remove the named entry from a PolyCtx. Used during schema
-- instantiation to prevent direct cycles (a poly body specialising
-- to its own name's instantiation would loop); the recursive
-- `checkElab` call sees a `PolyCtx` without the name being
-- specialised, so that name's use sites inside the body fall
-- through to the non-poly lookup path.
-- Plan 0.6.2 Phase 4 (termination principlization).
removePoly : String → PolyCtx → PolyCtx
removePoly _ [] = []
removePoly x ((n , s , b) ∷ rest) with StrProp._≟_ n x
... | yes _ = rest
... | no  _ = (n , s , b) ∷ removePoly x rest

-- | When `x` is found in `polys`, `removePoly` strictly shrinks it.
-- Load-bearing for well-founded termination of the poly-splice recursion
-- in `resolveExpr`. Plan 0.6.2 Phase 4 (final).
removePoly-decreases :
  ∀ {r : PolyType × RawExpr} (x : String) (polys : PolyCtx)
  → lookupPoly polys x ≡ just r
  → length (removePoly x polys) < length polys
removePoly-decreases x [] ()
removePoly-decreases x ((n , s , b) ∷ rest) eq with StrProp._≟_ n x
... | yes _ = s≤s ≤-refl
... | no  _ = s≤s (removePoly-decreases x rest eq)

-- | A named context paired with its de Bruijn representation
-- Includes a fresh counter for generating unique type variables during instantiation
-- and imported primitives from other modules
record NamedCtx : Set where
  constructor mkCtx
  field
    size        : ℕ
    named       : Ctx
    debruijn    : SCtx size
    freshCounter : ℕ  -- For generating fresh type variables (α₀, α₁, α₂, ...)
    imports     : Imports  -- Imported primitives (qualified names → types)
    polys       : PolyCtx  -- User polymorphic definitions (plan 0.6.2)

-- | Empty context
emptyCtx : NamedCtx
emptyCtx = mkCtx 0 ∅ S∅ 0 emptyImports emptyPolyCtx

-- | Create context with imports
ctxWithImports : Imports → NamedCtx
ctxWithImports imps = mkCtx 0 ∅ S∅ 0 imps emptyPolyCtx

-- | Create context with imports and polymorphic defs. Plan 0.6.2.
ctxWithImportsAndPolys : Imports → PolyCtx → NamedCtx
ctxWithImportsAndPolys imps polys = mkCtx 0 ∅ S∅ 0 imps polys

-- | Create context with imports and self-reference for recursive definitions
-- The function's own name and type are added to the imports list so it can call itself.
-- This causes recursive calls to elaborate to `Prim "name"` which the C backend
-- handles as a function call.
ctxWithImportsAndSelf : Imports → String → Type → NamedCtx
ctxWithImportsAndSelf imps name ty =
  ctxWithImports ((name , ty) ∷ imps)

-- | Same as `ctxWithImportsAndSelf` but also carries a polymorphic
-- context. Plan 0.6.2 — used by `compileFun` to make poly defs
-- available to each ground function's body during typecheck.
ctxWithImportsAndSelfAndPolys : Imports → PolyCtx → String → Type → NamedCtx
ctxWithImportsAndSelfAndPolys imps polys name ty =
  ctxWithImportsAndPolys ((name , ty) ∷ imps) polys

-- | Extend context with a new binding (preserves fresh counter, imports, polys)
extendNamedCtx : NamedCtx → String → Type → NamedCtx
extendNamedCtx (mkCtx n Γ Δ fresh imps polys) x A =
  mkCtx (suc n) (extendCtx Γ x A) (Δ S, A) fresh imps polys

-- | Bump fresh counter (for generating new type variables)
bumpFresh : NamedCtx → NamedCtx
bumpFresh (mkCtx n Γ Δ fresh imps polys) = mkCtx n Γ Δ (suc fresh) imps polys

-- | Generate fresh type variable name
freshTVar : ℕ → String
freshTVar n = "α" ++ showℕ n
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

specId : (T : Type) → SExpr S∅ Surface.zeroUsage (T ⇒ T)
specId T = Surface.lam Many refl (Surface.var zero)

specFst : (A B : Type) → SExpr S∅ Surface.zeroUsage (A Once.Type.* B ⇒ A)
specFst A B = Surface.lam Many refl (Surface.fst' (Surface.var zero))

specSnd : (A B : Type) → SExpr S∅ Surface.zeroUsage (A Once.Type.* B ⇒ B)
specSnd A B = Surface.lam Many refl (Surface.snd' (Surface.var zero))

specInl : (A B : Type) → SExpr S∅ Surface.zeroUsage (A ⇒ (A Once.Type.+ B))
specInl A B = Surface.lam Many refl (Surface.inl' (Surface.var zero))

specInr : (A B : Type) → SExpr S∅ Surface.zeroUsage (B ⇒ (A Once.Type.+ B))
specInr A B = Surface.lam Many refl (Surface.inr' (Surface.var zero))

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
specTerminal A = Surface.lam Many refl Surface.unit

-- initial : Void → a
specInitial : (A : Type) → SExpr S∅ Surface.zeroUsage (Void ⇒ A)
specInitial A = Surface.lam Many refl (Surface.absurd (Surface.var zero))

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

-- arr : (a → b) → Eff a b
specArr : (A B : Type) → SExpr S∅ Surface.zeroUsage ((A ⇒ B) ⇒ Eff A B)
specArr A B = Surface.lam Many refl (Surface.arr' (Surface.var zero))


------------------------------------------------------------------------
-- Variable Lookup with Weakening and Instantiation
------------------------------------------------------------------------

-- | Look up a type in the imports list by name
lookupImport : Imports → String → Maybe Type
lookupImport [] _ = nothing
lookupImport ((n , ty) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just ty
... | no  _ = lookupImport rest x

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
    go (Raw.RApp f x) args = go f (x ∷ args)
    go other          args = mkSpine other args

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
lookupLocal : (ctx : NamedCtx) → String
            → Maybe (∃[ A ] ∃[ Ψ ] (SExpr (NamedCtx.debruijn ctx) Ψ A))
lookupLocal (mkCtx n Γ Δ _ _ _) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → Maybe (∃[ A ] ∃[ Ψ ] (SExpr Δ' Ψ A))
    go [] S∅                   = nothing
    go [] (_ S, _ ^ _)         = nothing
    go (_ ∷ _) S∅              = nothing
    go {suc m} (b ∷ Γ') (Δ' S, B ^ _) with Data.String._≟_ x (name b)
    ... | yes _ = just (B , _ , Surface.var zero)
    ... | no _  with go Γ' Δ'
    ...   | nothing        = nothing
    ...   | just (A , Ψ , se) = just (A , _ , weaken se)

-- | Find a local variable's de Bruijn position and declared quantity.
findLocalVarUsage : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx) × Quantity)
findLocalVarUsage (mkCtx n Γ Δ _ _ _) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → SCtx m → Maybe (Fin m × Quantity)
    go [] S∅ = nothing
    go [] (_ S, _ ^ _) = nothing
    go (_ ∷ _) S∅ = nothing
    go {suc m} (b ∷ Γ') (Δ' S, _ ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just (zero , q)
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just (i , q') = just (suc i , q')

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
         → SExpr Δ Ψ (A ⇒[ q ] B) → ℕ → ℕ → FunProjection Δ
  isEff  : (A B : Type) (Ψ : Surface.Usage n)
         → SExpr Δ Ψ (Eff A B) → ℕ → ℕ → FunProjection Δ
  notFun : TypeError → FunProjection Δ

asFun : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → FunProjection Δ
asFun (failure err)                                      = notFun err
asFun (success (A ⇒[ q ] B) Ψ se d f)                    = isFun A q B Ψ se d f
asFun (success (Eff A B) Ψ se d f)                       = isEff A B Ψ se d f
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
asInt (success (A ⇒[ q ] B) _ _ _ _)                     = notInt (TypeMismatch Int (A ⇒[ q ] B))
asInt (success (Eff A B) _ _ _ _)                        = notInt (TypeMismatch Int (Eff A B))
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

-- | Polymorphic-builtin identifier for the function position of an
-- `RApp`. The elaborator handles each polymorphic builtin specially
-- (separate type-checking rules, separate error paths). Hoisting the
-- dispatch into a classifier + `Maybe PolyBuiltinApp` makes the
-- elaborator's pattern coverage explicit and avoids the neutral-term
-- obstacle with literal-string patterns (analogous to the RVar "unit"
-- refactor).
data PolyBuiltinApp : Set where
  pba-id pba-fst pba-snd pba-terminal : PolyBuiltinApp  -- infer-mode successes
  pba-inl pba-inr pba-initial : PolyBuiltinApp          -- infer-mode rejections
  pba-arr : PolyBuiltinApp                              -- Eff lift, infer mode
  pba-pair-applied : PolyBuiltinApp                     -- `RApp (RVar "pair") _` head, check mode
  pba-compose-applied : PolyBuiltinApp                  -- `RApp (RVar "compose") _` head, check mode
  pba-curry : PolyBuiltinApp                            -- 1-arg `curry f`, check mode
  pba-apply : PolyBuiltinApp                            -- 1-arg `apply p`, infer / check mode

-- | Classify an application head. `just <pba>` iff the head is an
-- `RVar` bound to one of the seven polymorphic builtins; `nothing`
-- otherwise, in which case the generic application rule applies.
classifyAppHead : RawExpr → Maybe PolyBuiltinApp
classifyAppHead (Raw.RVar x) with StrProp._≟_ x "id"
... | yes _ = just pba-id
... | no  _ with StrProp._≟_ x "fst"
...   | yes _ = just pba-fst
...   | no  _ with StrProp._≟_ x "snd"
...     | yes _ = just pba-snd
...     | no  _ with StrProp._≟_ x "terminal"
...       | yes _ = just pba-terminal
...       | no  _ with StrProp._≟_ x "inl"
...         | yes _ = just pba-inl
...         | no  _ with StrProp._≟_ x "inr"
...           | yes _ = just pba-inr
...           | no  _ with StrProp._≟_ x "initial"
...             | yes _ = just pba-initial
...             | no  _ with StrProp._≟_ x "arr"
...               | yes _ = just pba-arr
...               | no  _ with StrProp._≟_ x "curry"
...                 | yes _ = just pba-curry
...                 | no  _ with StrProp._≟_ x "apply"
...                   | yes _ = just pba-apply
...                   | no  _ = nothing
-- Applied-form heads: `RApp (RVar "pair" | "compose") _`. Plan 0.6
-- Phase C.7 POC-2 / POC-3.
classifyAppHead (Raw.RApp (Raw.RVar x) _) with StrProp._≟_ x "pair"
... | yes _ = just pba-pair-applied
... | no  _ with StrProp._≟_ x "compose"
...   | yes _ = just pba-compose-applied
...   | no  _ = nothing
classifyAppHead (Raw.RApp _ _) = nothing
classifyAppHead _ = nothing

-- | View-type classification of an application head. Each constructor
-- fixes the head's concrete RawExpr shape via an index, so pattern-
-- matching on an `AppHeadView f` value makes `f`'s shape available
-- in the goal structurally — no `with`-abstraction interplay. This
-- is the "eliminate opaque `with`-helpers by refactoring the
-- definition" idiom (see `docs/formal/historical/lessons-learned.md`):
-- when a proof is fighting `rewrite` against an internal `with`-
-- dispatch, the fix is to refactor the function to return a datatype
-- carrying the proof, not to layer more proof tactics.
data AppHeadView : RawExpr → Set where
  ahv-id       : AppHeadView (Raw.RVar "id")
  ahv-fst      : AppHeadView (Raw.RVar "fst")
  ahv-snd      : AppHeadView (Raw.RVar "snd")
  ahv-terminal : AppHeadView (Raw.RVar "terminal")
  ahv-inl      : AppHeadView (Raw.RVar "inl")
  ahv-inr      : AppHeadView (Raw.RVar "inr")
  ahv-initial  : AppHeadView (Raw.RVar "initial")
  ahv-arr      : AppHeadView (Raw.RVar "arr")
  ahv-curry    : AppHeadView (Raw.RVar "curry")
  ahv-apply    : AppHeadView (Raw.RVar "apply")
  ahv-pair-applied    : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RVar "pair") f')
  ahv-compose-applied : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RVar "compose") f')
  ahv-other    : ∀ {f} → AppHeadView f

classifyAppHeadView : (f : RawExpr) → AppHeadView f
classifyAppHeadView (Raw.RVar x) with StrProp._≟_ x "id"
... | yes refl = ahv-id
... | no  _ with StrProp._≟_ x "fst"
...   | yes refl = ahv-fst
...   | no  _ with StrProp._≟_ x "snd"
...     | yes refl = ahv-snd
...     | no  _ with StrProp._≟_ x "terminal"
...       | yes refl = ahv-terminal
...       | no  _ with StrProp._≟_ x "inl"
...         | yes refl = ahv-inl
...         | no  _ with StrProp._≟_ x "inr"
...           | yes refl = ahv-inr
...           | no  _ with StrProp._≟_ x "initial"
...             | yes refl = ahv-initial
...             | no  _ with StrProp._≟_ x "arr"
...               | yes refl = ahv-arr
...               | no  _ with StrProp._≟_ x "curry"
...                 | yes refl = ahv-curry
...                 | no  _ with StrProp._≟_ x "apply"
...                   | yes refl = ahv-apply
...                   | no  _ = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RVar x) _) with StrProp._≟_ x "pair"
... | yes refl = ahv-pair-applied
... | no  _    with StrProp._≟_ x "compose"
...   | yes refl = ahv-compose-applied
...   | no  _    = ahv-other
classifyAppHeadView (Raw.RApp _ _)            = ahv-other
classifyAppHeadView (Raw.RQualified _ _)      = ahv-other
classifyAppHeadView (Raw.RLam _ _)            = ahv-other
classifyAppHeadView (Raw.RLet _ _ _)          = ahv-other
classifyAppHeadView (Raw.RPair _ _)           = ahv-other
classifyAppHeadView (Raw.RDestruct _ _ _ _ _) = ahv-other
classifyAppHeadView Raw.RUnit                 = ahv-other
classifyAppHeadView (Raw.RInt _)              = ahv-other
classifyAppHeadView (Raw.RStringLit _)        = ahv-other
classifyAppHeadView (Raw.RAnnot _ _)          = ahv-other
classifyAppHeadView (Raw.RBinOp _ _ _)        = ahv-other
classifyAppHeadView (Raw.RUnaryOp _ _)        = ahv-other

-- | Compat: `classifyAppHead f ≡ nothing` ⇔ `classifyAppHeadView f ≡
-- ahv-other`. Needed because existing downstream proofs (Judgment's
-- t-app premise, Soundness's sound-RApp-generic, etc.) use
-- `classifyAppHead`'s `Maybe`-return form, while the view enables
-- new proofs (`checkElab-fallback-RApp-generic` below).
classifyAppHead-nothing⇒view-other :
  ∀ {f} → classifyAppHead f ≡ nothing → classifyAppHeadView f ≡ ahv-other
-- Non-RVar heads: both classifyAppHead and classifyAppHeadView
-- reduce definitionally to their respective nothing / ahv-other.
-- Plan 0.6 Phase C.7 POC-2: the RApp case now has a nested match
-- on `RApp (RVar "pair") _`. Split: if head is `RVar "pair"`,
-- classifyAppHead returns `just pba-pair-applied` (so the premise
-- `≡ nothing` is impossible); otherwise uniform `refl`.
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RVar s) _} p with StrProp._≟_ s "pair"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RVar s) _} p | no _ with StrProp._≟_ s "compose"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RVar _) _} _ | no _ | no _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RApp _ _) _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RQualified _ _) _} _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RLam _ _) _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RLet _ _ _) _}     _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RPair _ _) _}      _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RDestruct _ _ _ _ _) _} _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp Raw.RUnit _}            _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RInt _) _}         _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RStringLit _) _}   _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RAnnot _ _) _}     _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RBinOp _ _ _) _}   _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RUnaryOp _ _) _}   _ = refl
classifyAppHead-nothing⇒view-other {Raw.RQualified _ _}     _ = refl
classifyAppHead-nothing⇒view-other {Raw.RLam _ _}           _ = refl
classifyAppHead-nothing⇒view-other {Raw.RLet _ _ _}         _ = refl
classifyAppHead-nothing⇒view-other {Raw.RPair _ _}          _ = refl
classifyAppHead-nothing⇒view-other {Raw.RDestruct _ _ _ _ _} _ = refl
classifyAppHead-nothing⇒view-other {Raw.RUnit}              _ = refl
classifyAppHead-nothing⇒view-other {Raw.RInt _}             _ = refl
classifyAppHead-nothing⇒view-other {Raw.RStringLit _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RAnnot _ _}         _ = refl
classifyAppHead-nothing⇒view-other {Raw.RBinOp _ _ _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RUnaryOp _ _}       _ = refl
-- RVar: both dispatches walk the same 7-string chain; show the
-- result alignment case-by-case.
classifyAppHead-nothing⇒view-other {Raw.RVar s} p with StrProp._≟_ s "id"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _
  with StrProp._≟_ s "fst"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _
  with StrProp._≟_ s "snd"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _
  with StrProp._≟_ s "terminal"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _
  with StrProp._≟_ s "inl"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "inr"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "initial"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "arr"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "curry"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "apply"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = refl

-- | Plan 0.6.2 Phase 3b: for `compose f g` at expected `A → C`,
-- when `inferElab g` fails, try to determine the intermediate
-- type `B` from `g`'s structural shape:
--   * `RVar poly_name` in `PolyCtx`: use schema instantiation.
--   * Bare builtin (fst/snd/id/terminal): use canonical schema.
--   * Anything else: `nothing` (compose can't proceed).
-- Subsequent `checkElab ctx g (A → B)` will handle specialisation.
composeArgB : NamedCtx → RawExpr → Type → Maybe Type
-- fst : (X * Y) → X, so B = X when A = X * Y.
composeArgB ctx (Raw.RVar "fst") (X Once.Type.* _) = just X
-- snd : (X * Y) → Y, so B = Y when A = X * Y.
composeArgB ctx (Raw.RVar "snd") (_ Once.Type.* Y) = just Y
-- id : X → X, so B = A.
composeArgB ctx (Raw.RVar "id") A = just A
-- terminal : X → Unit, so B = Unit.
composeArgB ctx (Raw.RVar "terminal") _ = just Unit
-- User poly name: look up schema, match domain, extract codomain.
composeArgB ctx (Raw.RVar name) A with lookupPoly (NamedCtx.polys ctx) name
... | just (schema , _) = schemaArrowCodomain schema A
... | nothing = nothing
-- Other shapes: compose can't proceed without inferElab success.
composeArgB _ _ _ = nothing

------------------------------------------------------------------------
-- Bare polymorphic-builtin classifier (plan 0.6 Phase C.7)
------------------------------------------------------------------------
-- Used by `checkElab-RVar` to dispatch specialised check-mode clauses
-- per builtin name. The view-constructor index exposes the concrete
-- string in each case, so Agda reductions proceed cleanly and proof
-- `with classifyBareBuiltin x` mirrors the elaborator's dispatch.

data BareBuiltinClass : String → Set where
  bbc-id       : BareBuiltinClass "id"
  bbc-fst      : BareBuiltinClass "fst"
  bbc-snd      : BareBuiltinClass "snd"
  bbc-terminal : BareBuiltinClass "terminal"
  bbc-initial  : BareBuiltinClass "initial"
  bbc-inl      : BareBuiltinClass "inl"
  bbc-inr      : BareBuiltinClass "inr"
  bbc-arr      : BareBuiltinClass "arr"
  bbc-other    : ∀ {x} → BareBuiltinClass x

classifyBareBuiltin : (x : String) → BareBuiltinClass x
classifyBareBuiltin x with StrProp._≟_ x "id"
... | yes refl = bbc-id
... | no  _ with StrProp._≟_ x "fst"
...   | yes refl = bbc-fst
...   | no  _ with StrProp._≟_ x "snd"
...     | yes refl = bbc-snd
...     | no  _ with StrProp._≟_ x "terminal"
...       | yes refl = bbc-terminal
...       | no  _ with StrProp._≟_ x "initial"
...         | yes refl = bbc-initial
...         | no  _ with StrProp._≟_ x "inl"
...           | yes refl = bbc-inl
...           | no  _ with StrProp._≟_ x "inr"
...             | yes refl = bbc-inr
...             | no  _ with StrProp._≟_ x "arr"
...               | yes refl = bbc-arr
...               | no  _ = bbc-other

------------------------------------------------------------------------
-- Bidirectional Inference (produces usage-indexed Expr)
------------------------------------------------------------------------

-- Plan 0.6.2 Phase 4: two-phase architecture. Phase 1 (this mutual
-- block) is purely structural on `RawExpr` — at user-polymorphic
-- references, it emits a `Surface.poly x T` placeholder rather than
-- recursing into the def's body. Phase 2 (`resolveExpr` below)
-- tree-walks the emitted Expr and splices bodies at `poly` nodes,
-- well-founded on `length polys`. No TERMINATING pragma needed.
mutual
  inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
  checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
  -- RVar dispatch helper (plan 0.6 Phase C.7 POC-1). Separates
  -- specialised bare-builtin handling from the generic lookup path.
  checkElab-RVar : (ctx : NamedCtx) → (x : String) → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
  -- Pair classifier helper (plan 0.6 Phase C.7 POC-2). Checks a
  -- 2-arg `pair f g` expression in check mode against the canonical
  -- `A ⇒[Many] (B * C)` shape.
  checkPair : (ctx : NamedCtx) → (pairHead arg : RawExpr) → (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T
  -- Compose / curry / apply classifier helpers (plan 0.6 Phase C.7
  -- POC-3).
  checkCompose : (ctx : NamedCtx) → (composeHead arg : RawExpr) → (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T
  checkCurry : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T
  checkApply : (ctx : NamedCtx) → (arg : RawExpr) → (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T

  -- ===== inferElab =====

  -- Literals
  inferElab ctx (Raw.RInt n) =
    success Int _ (Surface.int n) 0 (NamedCtx.freshCounter ctx)
  inferElab ctx (Raw.RStringLit s) =
    success Str _ (Surface.str s) 0 (NamedCtx.freshCounter ctx)
  inferElab ctx Raw.RUnit =
    success Unit _ Surface.unit 0 (NamedCtx.freshCounter ctx)

  -- Type annotation: check against the annotated type
  inferElab ctx (Raw.RAnnot e T) with checkElab ctx e T
  ... | success Ψ se d f = success T Ψ se d f
  ... | failure err     = failure err

  -- Variable lookup.
  --
  -- Order of precedence:
  --   (1) the `"unit"` builtin (monomorphic Unit);
  --   (2) local bindings in the typing context;
  --   (3) imported primitives (qualified-ish via bare name).
  --
  -- The `"unit"` check is written as a decidable equality (via
  -- `StrProp._≟_`) rather than a literal pattern match so downstream
  -- soundness proofs can case-split on it without hitting Agda's
  -- neutral-term obstacle on literal strings (analogous to the
  -- `decideLeq` refactor for `RLam`).
  inferElab ctx (Raw.RVar x) with StrProp._≟_ x "unit"
  ... | yes _ =
        success Unit _ Surface.unit 0 (NamedCtx.freshCounter ctx)
  ... | no  _ with lookupLocal ctx x
  ...   | just (A , Ψ , se) = success A Ψ se 0 (NamedCtx.freshCounter ctx)
  ...   | nothing with lookupImport (NamedCtx.imports ctx) x
  ...     | just ty = success ty _ (Surface.prim x) 0 (NamedCtx.freshCounter ctx)
  ...     | nothing = failure (UnboundVariable x)

  -- Qualified name: look up as "alias.name"
  inferElab ctx (Raw.RQualified name alias) with lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)
  ... | just ty = success ty _ (Surface.prim (alias ++ "." ++ name)) 0 (NamedCtx.freshCounter ctx)
  ... | nothing = failure (UnboundQualified name alias)

  -- Lambda without annotation: rejected in infer mode
  inferElab ctx (Raw.RLam _ _) =
    failure LambdaInInferMode

  -- Application.
  --
  -- The elaborator dispatches via `classifyAppHead f`: when `f` is
  -- one of the seven polymorphic builtins (`id`, `fst`, `snd`,
  -- `terminal`, `inl`, `inr`, `initial`), the specialised rule
  -- fires; otherwise the generic application rule applies.
  -- Collapsing the seven literal-pattern clauses into one `Maybe`
  -- dispatch keeps all soundness paths proof-tractable — no more
  -- neutral-term ambiguity between literal-pattern clauses and the
  -- generic-RApp clause.
  inferElab ctx (Raw.RApp f x) with classifyAppHeadView f
  -- id : A → A
  ... | ahv-id with inferElab ctx x
  ...   | failure err = failure err
  ...   | success T Ψ argE d f' =
          success T _ (Surface.app (weakenFromEmpty (specId T)) argE) (suc d) f'
  -- fst : (A * B) → A
  inferElab ctx (Raw.RApp f x) | ahv-fst with inferElab ctx x
  ... | failure err = failure err
  ... | success (A Once.Type.* B) Ψ argE d f' =
        success A _ (Surface.app (weakenFromEmpty (specFst A B)) argE) (suc d) f'
  ... | success _ _ _ _ _ = failure FstNeedsPair
  -- snd : (A * B) → B
  inferElab ctx (Raw.RApp f x) | ahv-snd with inferElab ctx x
  ... | failure err = failure err
  ... | success (A Once.Type.* B) Ψ argE d f' =
        success B _ (Surface.app (weakenFromEmpty (specSnd A B)) argE) (suc d) f'
  ... | success _ _ _ _ _ = failure SndNeedsPair
  -- terminal : A → Unit
  inferElab ctx (Raw.RApp f x) | ahv-terminal with inferElab ctx x
  ... | failure err = failure err
  ... | success A Ψ argE d f' =
        success Unit _ (Surface.app (weakenFromEmpty (specTerminal A)) argE) (suc d) f'
  -- arr : (A ⇒[Many] B) → Eff A B
  -- Lifts a Many-quantity pure function into the Eff monad. Linear
  -- (One-quantity) arrows are rejected — use explicit Surface.arr'
  -- via a type annotation when that's really wanted.
  inferElab ctx (Raw.RApp f x) | ahv-arr with inferElab ctx x
  ... | failure err = failure err
  ... | success (A Once.Type.⇒[ Once.Type.Many ] B) Ψ argE d f' =
        success (Once.Type.Eff A B) _
                (Surface.app (weakenFromEmpty (specArr A B)) argE) (suc d) f'
  ... | success _ _ _ _ _ = failure ArrNeedsFunction
  -- Partial / check-only builtins in infer mode: fail.
  inferElab ctx (Raw.RApp _ _) | ahv-inl =
    failure InlInInferMode
  inferElab ctx (Raw.RApp _ _) | ahv-inr =
    failure InrInInferMode
  inferElab ctx (Raw.RApp _ _) | ahv-initial =
    failure InitialInInferMode
  -- `pair f g` requires a check-mode expected type to determine
  -- A, B, C. Reject in infer mode (plan 0.6 Phase C.7 POC-2).
  inferElab ctx (Raw.RApp _ _) | ahv-pair-applied =
    failure (BuiltinTypeMismatch "pair")
  -- `compose f g`, `curry f` similarly require check-mode.
  inferElab ctx (Raw.RApp _ _) | ahv-compose-applied =
    failure (BuiltinTypeMismatch "compose")
  inferElab ctx (Raw.RApp _ _) | ahv-curry =
    failure (BuiltinTypeMismatch "curry")
  -- `apply p` is inferable when p has pair-of-function type.
  inferElab ctx (Raw.RApp _ x) | ahv-apply with inferElab ctx x
  ... | failure err = failure err
  ... | success ((A Once.Type.⇒[ Once.Type.Many ] B) Once.Type.* A') Ψ argE d f' with A ≟T A'
  ...   | yes refl =
          success B _ (Surface.app (weakenFromEmpty (specApply A B)) argE) (suc d) f'
  ...   | no  _ = failure (BuiltinTypeMismatch "apply")
  inferElab ctx (Raw.RApp _ _) | ahv-apply | success _ _ _ _ _ =
    failure (BuiltinTypeMismatch "apply")
  -- Generic application: infer f as function type, then x.
  inferElab ctx (Raw.RApp f x) | ahv-other with asFun (inferElab ctx f)
  ... | notFun err = failure err
  ... | isFun A q B Ψ₁ fE df ff with inferElab ctx x
  ...   | failure err = failure err
  ...   | success A' Ψ₂ xE dx fx with A ≟T A'
  ...     | yes refl = success B _ (Surface.app fE xE) (df ⊔ dx) fx
  ...     | no _ = failure (ApplicationTypeMismatch A A')
  inferElab ctx (Raw.RApp f x) | ahv-other | isEff A B Ψ₁ fE df ff with inferElab ctx x
  ...   | failure err = failure err
  ...   | success A' Ψ₂ xE dx fx with A ≟T A'
  ...     | yes refl = success (Eff Unit B) _ (Surface.effApp fE xE) (df ⊔ dx) fx
  ...     | no _ = failure (ApplicationTypeMismatch A A')

  -- Let binding: infer e₁, then e₂ under extended context.
  -- e₂'s usage has the shape (q ∷ᵘ Ψ) where q is the bound var's usage.
  inferElab ctx (Raw.RLet x e₁ e₂) with inferElab ctx e₁
  ... | failure err = failure err
  ... | success A Ψ₁ e₁E d₁ f₁ with inferElab (extendNamedCtx ctx x A) e₂
  ...   | failure err = failure err
  ...   | success B (q ∷ᵘ Ψ₂) e₂E d₂ f₂ =
        success B _ (Surface.let' e₁E e₂E) (d₁ ⊔ suc d₂) f₂

  -- Pair introduction
  inferElab ctx (Raw.RPair a b) with inferElab ctx a
  ... | failure err = failure err
  ... | success A Ψ₁ aE da fa with inferElab ctx b
  ...   | failure err = failure err
  ...   | success B Ψ₂ bE db fb =
        success (A Once.Type.* B) _ (Surface.pair aE bE) (da ⊔ db) fb

  -- Case (destruct)
  inferElab ctx (Raw.RDestruct scrut xL eL xR eR) with inferElab ctx scrut
  ... | failure err = failure err
  ... | success (A Once.Type.+ B) Ψs scrutE ds fs with inferElab (extendNamedCtx ctx xL A) eL
  ...   | failure err = failure err
  ...   | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL with inferElab (extendNamedCtx ctx xR B) eR
  ...     | failure err = failure err
  ...     | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR with C₁ ≟T C₂
  ...       | yes refl = success C₁ _ (Surface.case' scrutE eLE eRE)
                           (ds ⊔ suc dL ⊔ suc dR) fR
  ...       | no _ = failure CaseBranchMismatch
  inferElab ctx (Raw.RDestruct _ _ _ _ _) | success _ _ _ _ _ = failure CaseScrutineeNotSum

  -- Binary operators
  inferElab ctx (Raw.RBinOp op e₁ e₂) with asInt (inferElab ctx e₁)
  ... | notInt err = failure (BinOpLeftError err)
  ... | isInt Ψ₁ e₁E d₁ f₁ with asInt (inferElab ctx e₂)
  ...   | notInt err = failure (BinOpRightError err)
  ...   | isInt Ψ₂ e₂E d₂ f₂ =
        if Raw.isArithmeticOp op
          then success Int _ (mkArith op e₁E e₂E) (d₁ ⊔ d₂) f₂
          else success (Unit Once.Type.+ Unit) _ (mkCmp op e₁E e₂E) (d₁ ⊔ d₂) f₂
    where
      mkArith : ∀ {Δ : SCtx (NamedCtx.size ctx)} {Ψa Ψb : Surface.Usage (NamedCtx.size ctx)}
              → Raw.BinOp → SExpr Δ Ψa Int → SExpr Δ Ψb Int → SExpr Δ (Ψa +ᵘ Ψb) Int
      mkArith Raw.OpAdd = Surface.add
      mkArith Raw.OpSub = Surface.sub
      mkArith Raw.OpMul = Surface.mul
      mkArith Raw.OpDiv = Surface.div
      mkArith Raw.OpMod = Surface.mod'
      mkArith _         = Surface.add
      mkCmp : ∀ {Δ : SCtx (NamedCtx.size ctx)} {Ψa Ψb : Surface.Usage (NamedCtx.size ctx)}
            → Raw.BinOp → SExpr Δ Ψa Int → SExpr Δ Ψb Int → SExpr Δ (Ψa +ᵘ Ψb) (Unit Once.Type.+ Unit)
      mkCmp Raw.OpLt = Surface.lt
      mkCmp Raw.OpLe = Surface.le
      mkCmp Raw.OpGt = Surface.gt
      mkCmp Raw.OpGe = Surface.ge
      mkCmp Raw.OpEq = Surface.eq
      mkCmp Raw.OpNe = Surface.ne
      mkCmp _         = Surface.lt

  -- Unary negation
  inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) with inferElab ctx e
  ... | failure err = failure err
  ... | success Int Ψ eE d f = success Int _ (Surface.neg eE) d f
  ... | success _ _ _ _ _ = failure NegationNotInt

  -- ===== checkElab =====

  -- Lambda in check mode: destruct expected function type
  --
  -- The body's first-position usage `q'` must satisfy `q' ≤q q`; we
  -- need the Bool decision *with its proof* to construct `Surface.lam`.
  -- Returning the decision via a `Maybe`-wrapping helper (`decideLeq`,
  -- defined above) avoids the stdlib `inspect` idiom, whose internal
  -- `with`-helper name is opaque to external proofs.
  checkElab ctx (Raw.RLam x body) (A ⇒[ q ] B) with checkElab (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success (q' ∷ᵘ Ψ) bodyE d f with decideLeq q' q
  ...   | just eq =
        success _ (Surface.lam q eq bodyE) (suc d) f
  ...   | nothing = failure (UsageViolation x q q')
  checkElab ctx (Raw.RLam _ _) _ = failure LambdaRequiresFunctionType

  -- RApp in check mode: dispatch via `classifyAppHead` (same
  -- classifier used by inferElab). Three polymorphic-builtin app
  -- heads have specialised check-mode logic (inl, inr, initial); the
  -- other four (id, fst, snd, terminal) and the default `nothing`
  -- case fall through to the generic inferElab-then-match fallback.
  --
  -- Refactor rationale: with a concrete-string `Raw.RApp (Raw.RVar
  -- "inl") arg` pattern, `classifyAppHead f ≡ nothing` cannot teach
  -- Agda that `checkElab ctx (Raw.RApp f arg) T` reduces past the
  -- specialised clauses when `f` is abstract. Classifier dispatch
  -- lets `rewrite notPoly` unblock the reduction in downstream
  -- fallback proofs (see plan 0.3 G2 decision 2 resolution).
  -- Dispatch via `classifyAppHeadView`: each specialised case binds
  -- `f` concretely via the view-constructor's index, making the
  -- reduction visible to downstream proofs (no opaque with-helper
  -- over classifyAppHead's internal string-comparison chain).
  checkElab ctx (Raw.RApp f arg) T with classifyAppHeadView f
  ... | ahv-inl with T
  ...   | (A Once.Type.+ B) with checkElab ctx arg A
  ...     | failure err = failure err
  ...     | success Ψ argE d fr =
            success _ (Surface.app (weakenFromEmpty (specInl A B)) argE) (suc d) fr
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | Unit = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | Int = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | Str = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | Void = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | Float = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | Buffer = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | (_ Once.Type.* _) = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | (_ Once.Type.⇒[ _ ] _) = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | Eff _ _ = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | μ-type _ = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inl | ν-type _ = failure InlNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr with T
  ...   | (A Once.Type.+ B) with checkElab ctx arg B
  ...     | failure err = failure err
  ...     | success Ψ argE d fr =
            success _ (Surface.app (weakenFromEmpty (specInr A B)) argE) (suc d) fr
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | Unit = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | Int = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | Str = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | Void = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | Float = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | Buffer = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | (_ Once.Type.* _) = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | (_ Once.Type.⇒[ _ ] _) = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | Eff _ _ = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | μ-type _ = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-inr | ν-type _ = failure InrNeedsSumType
  checkElab ctx (Raw.RApp f arg) T | ahv-initial with checkElab ctx arg Void
  ...     | failure err = failure err
  ...     | success Ψ argE d fr =
            success _ (Surface.app (weakenFromEmpty (specInitial T)) argE) (suc d) fr
  -- ahv-id / ahv-fst / ahv-snd / ahv-terminal / ahv-other: fall through
  -- to the generic check-via-infer fallback. Each inlines the same
  -- body since Agda's `with` requires explicit coverage.
  checkElab ctx (Raw.RApp f arg) T | ahv-id with inferElab ctx (Raw.RApp f arg)
  ... | failure err = failure err
  ... | success T' Ψ eE d fr with T ≟T T'
  ...   | yes refl = success _ eE d fr
  ...   | no _ = failure (TypeMismatch T T')
  checkElab ctx (Raw.RApp f arg) T | ahv-fst with inferElab ctx (Raw.RApp f arg)
  ... | failure err = failure err
  ... | success T' Ψ eE d fr with T ≟T T'
  ...   | yes refl = success _ eE d fr
  ...   | no _ = failure (TypeMismatch T T')
  checkElab ctx (Raw.RApp f arg) T | ahv-snd with inferElab ctx (Raw.RApp f arg)
  ... | failure err = failure err
  ... | success T' Ψ eE d fr with T ≟T T'
  ...   | yes refl = success _ eE d fr
  ...   | no _ = failure (TypeMismatch T T')
  checkElab ctx (Raw.RApp f arg) T | ahv-terminal with inferElab ctx (Raw.RApp f arg)
  ... | failure err = failure err
  ... | success T' Ψ eE d fr with T ≟T T'
  ...   | yes refl = success _ eE d fr
  ...   | no _ = failure (TypeMismatch T T')
  -- arr in check mode: drive specialisation from the expected `Eff A
  -- B` so the argument is checked at `A ⇒[Many] B`. This is the path
  -- that lets `arr (\p -> p)` typecheck against an `Eff Int Int`
  -- expectation — inferElab on the bare lambda would fail with
  -- LambdaInInferMode, so we don't fall through to infer here.
  checkElab ctx (Raw.RApp f arg) T | ahv-arr with T
  ... | (Once.Type.Eff A B) with checkElab ctx arg (A Once.Type.⇒[ Once.Type.Many ] B)
  ...     | failure err = failure err
  ...     | success Ψ argE d fr =
            success _ (Surface.app (weakenFromEmpty (specArr A B)) argE) (suc d) fr
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | Unit         = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | Int          = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | Str          = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | Void         = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | Float        = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | Buffer       = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | (_ Once.Type.* _)      = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | (_ Once.Type.+ _)      = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | (_ Once.Type.⇒[ _ ] _) = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | μ-type _     = failure (TypeMismatch T T)
  checkElab ctx (Raw.RApp f arg) T | ahv-arr | ν-type _     = failure (TypeMismatch T T)
  -- `pair f g` check-mode dispatch (plan 0.6 Phase C.7 POC-2).
  -- The view index on `ahv-pair-applied` guarantees `f = Raw.RApp
  -- (Raw.RVar "pair") f_inner`; `checkPair` pattern-matches to
  -- extract `f_inner` and checks both sub-expressions against the
  -- expected `A ⇒[Many] (B * C)` shape.
  checkElab ctx (Raw.RApp f arg) T | ahv-pair-applied = checkPair ctx f arg T
  -- `compose f g` check-mode dispatch (plan 0.6 Phase C.7 POC-3).
  checkElab ctx (Raw.RApp f arg) T | ahv-compose-applied = checkCompose ctx f arg T
  -- `curry f` / `apply p` check-mode dispatch (plan 0.6 Phase C.7
  -- POC-3).
  checkElab ctx (Raw.RApp f arg) T | ahv-curry = checkCurry ctx arg T
  checkElab ctx (Raw.RApp f arg) T | ahv-apply = checkApply ctx arg T
  checkElab ctx (Raw.RApp f arg) T | ahv-other with inferElab ctx (Raw.RApp f arg)
  ... | failure err = failure err
  ... | success T' Ψ eE d fr with T ≟T T'
  ...   | yes refl = success _ eE d fr
  ...   | no _ = failure (TypeMismatch T T')

  -- Bare polymorphic builtins in check mode: the specialised
  -- `RVar "id"`/`RVar "fst"`/... clauses were REMOVED (G2 decision,
  -- plan 0.3). They created an impedance between the elaborator
  -- (which short-circuited to the polymorphic builtin) and the
  -- judgment (which routes bare `RVar x` through
  -- t-var-local/t-var-import/t-var-qualified). Now bare builtin
  -- names in check mode go through the generic fallback
  -- (inferElab-then-type-match), which consults local/import lookup.
  -- Users who want `check (id : A → A)` must have `id` in imports
  -- or a local binding. In applied form `id e`, the inferElab
  -- classifier-dispatch handles polymorphism (unchanged).

  -- Generic fallback: infer and match types.
  -- For `RVar x`, dispatches to `checkElab-RVar` to handle
  -- specialised bare-builtin clauses via a view-based dispatch
  -- (avoids clause-matching blocking on abstract `x` in proofs —
  -- plan 0.6 Phase C.7 POC-1).
  checkElab ctx (Raw.RVar x) T = checkElab-RVar ctx x T
  checkElab ctx e T with inferElab ctx e
  ... | failure err = failure err
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')

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
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.Many ] B) | bbc-id | failure _ with A ≟T B
  ... | yes refl = success _ (weakenFromEmpty (specId A)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "id")
  checkElab-RVar ctx _ _ | bbc-id | failure err = failure err
  -- fst : (A * B) → A
  checkElab-RVar ctx _ T | bbc-fst with inferElab ctx (Raw.RVar "fst")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.Many ] A') | bbc-fst | failure _ with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specFst A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "fst")
  checkElab-RVar ctx _ _ | bbc-fst | failure err = failure err
  -- snd : (A * B) → B
  checkElab-RVar ctx _ T | bbc-snd with inferElab ctx (Raw.RVar "snd")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.Many ] B') | bbc-snd | failure _ with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specSnd A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "snd")
  checkElab-RVar ctx _ _ | bbc-snd | failure err = failure err
  -- terminal : A → Unit
  checkElab-RVar ctx _ T | bbc-terminal with inferElab ctx (Raw.RVar "terminal")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.Many ] Unit) | bbc-terminal | failure _ =
    success _ (weakenFromEmpty (specTerminal A)) 0 (NamedCtx.freshCounter ctx)
  checkElab-RVar ctx _ _ | bbc-terminal | failure err = failure err
  -- initial : Void → A
  checkElab-RVar ctx _ T | bbc-initial with inferElab ctx (Raw.RVar "initial")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (Void Once.Type.⇒[ Once.Type.Many ] A) | bbc-initial | failure _ =
    success _ (weakenFromEmpty (specInitial A)) 0 (NamedCtx.freshCounter ctx)
  checkElab-RVar ctx _ _ | bbc-initial | failure err = failure err
  -- inl : A → (A + B)
  checkElab-RVar ctx _ T | bbc-inl with inferElab ctx (Raw.RVar "inl")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (A Once.Type.⇒[ Once.Type.Many ] (A' Once.Type.+ B)) | bbc-inl | failure _ with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specInl A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "inl")
  checkElab-RVar ctx _ _ | bbc-inl | failure err = failure err
  -- inr : B → (A + B)
  checkElab-RVar ctx _ T | bbc-inr with inferElab ctx (Raw.RVar "inr")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ (B Once.Type.⇒[ Once.Type.Many ] (A Once.Type.+ B')) | bbc-inr | failure _ with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specInr A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure (BuiltinTypeMismatch "inr")
  checkElab-RVar ctx _ _ | bbc-inr | failure err = failure err
  -- arr : (A → B) → Eff A B
  checkElab-RVar ctx _ T | bbc-arr with inferElab ctx (Raw.RVar "arr")
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure (TypeMismatch T T')
  checkElab-RVar ctx _ ((A Once.Type.⇒[ Once.Type.Many ] B) Once.Type.⇒[ Once.Type.Many ] Eff A' B') | bbc-arr | failure _ with A ≟T A' | B ≟T B'
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
            (A Once.Type.⇒[ Once.Type.Many ] (B Once.Type.* C))
    with checkElab ctx f_inner (A Once.Type.⇒[ Once.Type.Many ] B)
  ... | failure err = failure err
  ... | success Ψf fE df frf with checkElab ctx arg (A Once.Type.⇒[ Once.Type.Many ] C)
  ...   | failure err = failure err
  ...   | success Ψg gE dg frg =
          success _
            (Surface.app (Surface.app (weakenFromEmpty (specPair A B C)) fE) gE)
            (suc (df Data.Nat.⊔ dg)) frg
  -- Any other shape falls through to failure. Consistent with
  -- ahv-inl's per-shape exhaustive enumeration pattern.
  checkPair _ _ _ _ = failure (BuiltinTypeMismatch "pair")

  -- Plan 0.6 Phase C.7 POC-3 + 0.6.2 Phase 3b: bare `compose f g`
  -- check-mode. Expected `A ⇒[Many] C`. Primary path: infer g's type
  -- to determine B, then check f at `B ⇒[Many] C`. Fallback: if g
  -- is a polymorphic name (user def), derive B via
  -- `composePolyArgB` (schema-instantiation at domain A), then
  -- checkElab both sub-expressions at the resolved types.
  checkCompose ctx (Raw.RApp (Raw.RVar "compose") f_inner) arg
               (A Once.Type.⇒[ Once.Type.Many ] C)
    with inferElab ctx arg
  ... | failure _ with composeArgB ctx arg A
  ...   | nothing = failure (BuiltinTypeMismatch "compose")
  ...   | just B with checkElab ctx arg (A Once.Type.⇒[ Once.Type.Many ] B)
  ...     | failure err = failure err
  ...     | success Ψg gE dg frg with checkElab ctx f_inner (B Once.Type.⇒[ Once.Type.Many ] C)
  ...       | failure err = failure err
  ...       | success Ψf fE df frf =
              success _
                (Surface.app (Surface.app (weakenFromEmpty (specCompose A B C)) fE) gE)
                (suc (df Data.Nat.⊔ dg)) frf
  checkCompose ctx (Raw.RApp (Raw.RVar "compose") f_inner) arg
               (A Once.Type.⇒[ Once.Type.Many ] C)
    | success (A' Once.Type.⇒[ Once.Type.Many ] B) Ψg gE dg frg with A ≟T A'
  ...   | no _ = failure (BuiltinTypeMismatch "compose")
  ...   | yes refl with checkElab ctx f_inner (B Once.Type.⇒[ Once.Type.Many ] C)
  ...     | failure err = failure err
  ...     | success Ψf fE df frf =
            success _
              (Surface.app (Surface.app (weakenFromEmpty (specCompose A B C)) fE) gE)
              (suc (df Data.Nat.⊔ dg)) frf
  -- Non-arrow-Many inferred types for g: compose can't proceed.
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success Unit       _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success Int        _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success Str        _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success Void       _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success Float      _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success Buffer     _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success (_ Once.Type.* _)  _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success (_ Once.Type.+ _)  _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success (_ Once.Type.⇒[ Once.Type.One ] _)  _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success (_ Once.Type.⇒[ Once.Type.Zero ] _) _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success (Eff _ _)  _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success (μ-type _) _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ (_ Once.Type.⇒[ Once.Type.Many ] _) | success (ν-type _) _ _ _ _ = failure (BuiltinTypeMismatch "compose")
  checkCompose _ _ _ _ = failure (BuiltinTypeMismatch "compose")

  -- Plan 0.6 Phase C.7 POC-3: `curry f` check-mode.
  -- Expected `A ⇒[Many] (B ⇒[Many] C)`. Check f at `(A * B) ⇒[Many] C`.
  checkCurry ctx arg (A Once.Type.⇒[ Once.Type.Many ] (B Once.Type.⇒[ Once.Type.Many ] C))
    with checkElab ctx arg ((A Once.Type.* B) Once.Type.⇒[ Once.Type.Many ] C)
  ... | failure err = failure err
  ... | success Ψ argE d fr =
        success _ (Surface.app (weakenFromEmpty (specCurry A B C)) argE) (suc d) fr
  checkCurry _ _ _ = failure (BuiltinTypeMismatch "curry")

  -- Plan 0.6 Phase C.7 POC-3: `apply p` check-mode.
  -- Check mode falls through to infer (apply's infer mode succeeds
  -- when p has pair-of-function type). Matches result against T.
  checkApply ctx arg T with inferElab ctx (Raw.RApp (Raw.RVar "apply") arg)
  ... | failure err = failure err
  ... | success T' Ψ eE d fr with T ≟T T'
  ...   | yes refl = success _ eE d fr
  ...   | no _ = failure (TypeMismatch T T')

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
checkElab-fallback-RQualified name alias T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

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
checkElab-fallback-RAnnot e T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RPair: check-mode at `A * B` falls to generic fallback.
checkElab-fallback-RPair :
  ∀ {ctx : NamedCtx} (a b : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RPair a b) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RPair a b) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RPair a b T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RLet: no specialised check clause.
checkElab-fallback-RLet :
  ∀ {ctx : NamedCtx} (x : String) (e₁ e₂ : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RLet x e₁ e₂) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RLet x e₁ e₂) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RLet x e₁ e₂ T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

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
checkElab-fallback-RDestruct scrut xL eL xR eR T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RUnaryOp: no specialised check clause.
checkElab-fallback-RUnaryOp :
  ∀ {ctx : NamedCtx} (op : Raw.UnaryOp) (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RUnaryOp op e) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RUnaryOp op e) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RUnaryOp op e T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

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

checkElab-fallback-RVar-id :
  ∀ {ctx : NamedCtx} (T : Type)
  → lookupLocal ctx "id" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "id" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "id") (T Once.Type.⇒[ Once.Type.Many ] T)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-id {ctx} T localN importN
  rewrite localN | importN with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

checkElab-fallback-RVar-fst :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "fst" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "fst" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "fst") ((A Once.Type.* B) Once.Type.⇒[ Once.Type.Many ] A)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-fst {ctx} A B localN importN
  rewrite localN | importN with A ≟T A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

checkElab-fallback-RVar-snd :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "snd" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "snd" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "snd") ((A Once.Type.* B) Once.Type.⇒[ Once.Type.Many ] B)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-snd {ctx} A B localN importN
  rewrite localN | importN with B ≟T B
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

checkElab-fallback-RVar-terminal :
  ∀ {ctx : NamedCtx} (A : Type)
  → lookupLocal ctx "terminal" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "terminal" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "terminal") (A Once.Type.⇒[ Once.Type.Many ] Unit)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-terminal {ctx} A localN importN
  rewrite localN | importN = _ , _ , _ , refl

checkElab-fallback-RVar-initial :
  ∀ {ctx : NamedCtx} (A : Type)
  → lookupLocal ctx "initial" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "initial" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "initial") (Void Once.Type.⇒[ Once.Type.Many ] A)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-initial {ctx} A localN importN
  rewrite localN | importN = _ , _ , _ , refl

checkElab-fallback-RVar-inl :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "inl" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "inl" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "inl") (A Once.Type.⇒[ Once.Type.Many ] (A Once.Type.+ B))
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-inl {ctx} A B localN importN
  rewrite localN | importN with A ≟T A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

checkElab-fallback-RVar-inr :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "inr" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "inr" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "inr") (B Once.Type.⇒[ Once.Type.Many ] (A Once.Type.+ B))
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-inr {ctx} A B localN importN
  rewrite localN | importN with B ≟T B
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

checkElab-fallback-RVar-arr :
  ∀ {ctx : NamedCtx} (A B : Type)
  → lookupLocal ctx "arr" ≡ nothing
  → lookupImport (NamedCtx.imports ctx) "arr" ≡ nothing
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
      checkElab ctx (Raw.RVar "arr")
                   ((A Once.Type.⇒[ Once.Type.Many ] B) Once.Type.⇒[ Once.Type.Many ] Eff A B)
        ≡ success Surface.zeroUsage eE d f)))
checkElab-fallback-RVar-arr {ctx} A B localN importN
  rewrite localN | importN with A ≟T A | B ≟T B
... | yes refl | yes refl = _ , _ , _ , refl
... | no ¬eq | _ = ⊥-elim (¬eq refl)
... | _ | no ¬eq = ⊥-elim (¬eq refl)

-- Plan 0.6 Phase C.7 POC-2: applied `pair f g` at canonical
-- `A ⇒[Many] (B * C)` shape. Given check-mode elab successes for
-- both f and g, the specialised classifier dispatch
-- (`ahv-pair-applied`) emits the `app (app specPair fE) gE` Surface
-- IR. This helper threads the two sub-equations through the
-- pattern-matching reduction chain to close completeness.
checkElab-fallback-RApp-pair :
  ∀ {ctx : NamedCtx} (f g : RawExpr) (A B C : Type)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {eE_f : SExpr (NamedCtx.debruijn ctx) Ψ₁ (A Once.Type.⇒[ Once.Type.Many ] B)}
    {eE_g : SExpr (NamedCtx.debruijn ctx) Ψ₂ (A Once.Type.⇒[ Once.Type.Many ] C)}
    {d_f f_f d_g f_g : ℕ}
  → checkElab ctx f (A Once.Type.⇒[ Once.Type.Many ] B) ≡ success Ψ₁ eE_f d_f f_f
  → checkElab ctx g (A Once.Type.⇒[ Once.Type.Many ] C) ≡ success Ψ₂ eE_g d_g f_g
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ fr →
      checkElab ctx (Raw.RApp (Raw.RApp (Raw.RVar "pair") f) g)
                    (A Once.Type.⇒[ Once.Type.Many ] (B Once.Type.* C))
        ≡ success ((Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₁))
                    Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₂)) eE d fr)))
checkElab-fallback-RApp-pair {ctx} f g A B C eq_f eq_g
  rewrite eq_f | eq_g = _ , _ , _ , refl

-- Plan 0.6 Phase C.7 POC-3: applied `compose f g` at `A ⇒[Many] C`.
-- Takes the inferElab-success for g (fixes B) and checkElab-success
-- for f at `B ⇒[Many] C`.
checkElab-fallback-RApp-compose :
  ∀ {ctx : NamedCtx} (f g : RawExpr) (A B C : Type)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {eE_f : SExpr (NamedCtx.debruijn ctx) Ψ₁ (B Once.Type.⇒[ Once.Type.Many ] C)}
    {eE_g : SExpr (NamedCtx.debruijn ctx) Ψ₂ (A Once.Type.⇒[ Once.Type.Many ] B)}
    {d_f f_f d_g f_g : ℕ}
  → checkElab ctx f (B Once.Type.⇒[ Once.Type.Many ] C) ≡ success Ψ₁ eE_f d_f f_f
  → inferElab ctx g ≡ success (A Once.Type.⇒[ Once.Type.Many ] B) Ψ₂ eE_g d_g f_g
  → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ fr →
      checkElab ctx (Raw.RApp (Raw.RApp (Raw.RVar "compose") f) g)
                    (A Once.Type.⇒[ Once.Type.Many ] C)
        ≡ success ((Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₁))
                    Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ₂)) eE d fr)))
checkElab-fallback-RApp-compose {ctx} f g A B C eq_f eq_g
  rewrite eq_g with A ≟T A
... | yes refl rewrite eq_f = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.6 Phase C.7 POC-3: applied `curry f` at `A → B → C`.
checkElab-fallback-RApp-curry :
  ∀ {ctx : NamedCtx} (f : RawExpr) (A B C : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ ((A Once.Type.* B) Once.Type.⇒[ Once.Type.Many ] C)}
    {d fr : ℕ}
  → checkElab ctx f ((A Once.Type.* B) Once.Type.⇒[ Once.Type.Many ] C) ≡ success Ψ eE d fr
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "curry") f)
                    (A Once.Type.⇒[ Once.Type.Many ] (B Once.Type.⇒[ Once.Type.Many ] C))
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE' d' f')))
checkElab-fallback-RApp-curry {ctx} f A B C eq_f
  rewrite eq_f = _ , _ , _ , refl

-- Plan 0.6 Phase C.7 POC-3: applied `apply p` at result type B.
checkElab-fallback-RApp-apply :
  ∀ {ctx : NamedCtx} (p : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ ((A Once.Type.⇒[ Once.Type.Many ] B) Once.Type.* A)}
    {d fr : ℕ}
  → inferElab ctx p ≡ success ((A Once.Type.⇒[ Once.Type.Many ] B) Once.Type.* A) Ψ eE d fr
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "apply") p) B
        ≡ success (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE' d' f')))
checkElab-fallback-RApp-apply {ctx} p A B eq_p
  rewrite eq_p with A ≟T A
... | no ¬eq = ⊥-elim (¬eq refl)
... | yes refl with B ≟T B
...   | yes refl = _ , _ , _ , refl
...   | no ¬eq = ⊥-elim (¬eq refl)

-- Plan 0.6.2 Phase 4: polymorphic schema-instantiation path.
-- Premises:
--   * `x` is not a reserved builtin name (`classifyBareBuiltin x ≡
--     bbc-other`) — rules out the specialised bare-builtin paths.
--   * `x` is not in the user's local scope.
--   * `x` is not in the user's imports.
--   * `x` IS in the polymorphic context, resolving to `(schema, body)`.
--   * The body check-mode elab succeeds at expected `T` (with
--     `removePoly x` to prevent self-cycles) producing a closed SExpr.
-- Conclusion: the top-level `checkElab ctx (RVar x) T` succeeds.

-- ─── Phase 2: full tree-walk resolver (well-founded) ───────────────────
-- Walks an Expr tree, finding `Surface.poly x T` placeholders and
-- splicing in the elaborated body at type T. Recurses on the spliced
-- body with a smaller polys context to handle nested polys.
--
-- TERMINATION: lex on (length polys, Expr-structure) as direct arguments:
--   * Non-prim cases: Expr strictly decreases, `pAcc` unchanged.
--   * Prim-leaf-with-match: destructure `pAcc = acc rec`, recurse with
--     `rec (removePoly-decreases ...)` as the smaller Acc for the
--     shrunken polys. Agda's lex termination checker accepts this.
-- No TERMINATING pragma needed. Public `resolveExpr` wraps the WF
-- variant with `<-wellFounded (length polys)` — no caller changes.

-- Forward declarations: `resolveExprWF` and `resolvePolyCase` are
-- mutually recursive.
resolveExprWF : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
              → (polys : PolyCtx) → Acc _<_ (length polys)
              → Imports → ℕ
              → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolvePolyCase : ∀ {n} {Γ : Surface.Ctx n}
                → (polys : PolyCtx) → Acc _<_ (length polys)
                → Imports → ℕ → (x : String) (A : Type)
                → (look : Maybe (PolyType × RawExpr))
                → lookupPoly polys x ≡ look
                → Surface.Expr Γ Surface.zeroUsage A

resolveExprWF polys _ imps _ (Surface.var i) = Surface.var i
resolveExprWF polys pAcc imps fresh (Surface.lam q prf b) =
  Surface.lam q prf (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.app f a) =
  Surface.app (resolveExprWF polys pAcc imps fresh f) (resolveExprWF polys pAcc imps fresh a)
resolveExprWF polys pAcc imps fresh (Surface.effApp f a) =
  Surface.effApp (resolveExprWF polys pAcc imps fresh f) (resolveExprWF polys pAcc imps fresh a)
resolveExprWF polys pAcc imps fresh (Surface.pair a b) =
  Surface.pair (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.fst' p) = Surface.fst' (resolveExprWF polys pAcc imps fresh p)
resolveExprWF polys pAcc imps fresh (Surface.snd' p) = Surface.snd' (resolveExprWF polys pAcc imps fresh p)
resolveExprWF polys pAcc imps fresh (Surface.inl' e) = Surface.inl' (resolveExprWF polys pAcc imps fresh e)
resolveExprWF polys pAcc imps fresh (Surface.inr' e) = Surface.inr' (resolveExprWF polys pAcc imps fresh e)
resolveExprWF polys pAcc imps fresh (Surface.case' s l r) =
  Surface.case' (resolveExprWF polys pAcc imps fresh s)
                (resolveExprWF polys pAcc imps fresh l)
                (resolveExprWF polys pAcc imps fresh r)
resolveExprWF polys _ imps _ Surface.unit = Surface.unit
resolveExprWF polys pAcc imps fresh (Surface.absurd e) = Surface.absurd (resolveExprWF polys pAcc imps fresh e)
resolveExprWF polys pAcc imps fresh (Surface.let' e₁ e₂) =
  Surface.let' (resolveExprWF polys pAcc imps fresh e₁) (resolveExprWF polys pAcc imps fresh e₂)
resolveExprWF polys _ imps _ (Surface.int z) = Surface.int z
resolveExprWF polys _ imps _ (Surface.str s) = Surface.str s
resolveExprWF polys pAcc imps fresh (Surface.add a b) =
  Surface.add (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.sub a b) =
  Surface.sub (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.mul a b) =
  Surface.mul (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.div a b) =
  Surface.div (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.mod' a b) =
  Surface.mod' (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.neg e) = Surface.neg (resolveExprWF polys pAcc imps fresh e)
resolveExprWF polys pAcc imps fresh (Surface.lt a b) =
  Surface.lt (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.le a b) =
  Surface.le (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.gt a b) =
  Surface.gt (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.ge a b) =
  Surface.ge (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.eq a b) =
  Surface.eq (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.ne a b) =
  Surface.ne (resolveExprWF polys pAcc imps fresh a) (resolveExprWF polys pAcc imps fresh b)
resolveExprWF polys pAcc imps fresh (Surface.arr' e) = Surface.arr' (resolveExprWF polys pAcc imps fresh e)
-- Prim = external primitive. Pass through unchanged; resolver doesn't touch it.
resolveExprWF polys _ imps _ (Surface.prim s) = Surface.prim s
-- Poly = unresolved placeholder from Phase 1. Delegate to helper that
-- takes the lookup result + equation explicitly, so external proofs
-- about the prim case can `rewrite` the premise cleanly.
resolveExprWF {A = A} polys pAcc imps fresh (Surface.poly x _) =
  resolvePolyCase polys pAcc imps fresh x A (lookupPoly polys x) refl

resolvePolyCase polys _ imps _ x A nothing _ = Surface.poly x A
resolvePolyCase polys (acc rec) imps fresh x A (just (_ , body)) polyEq
    with checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body A
... | failure _ = Surface.poly x A
... | success Surface.[] eE _ _ =
       resolveExprWF (removePoly x polys)
                     (rec (removePoly-decreases x polys polyEq))
                     imps fresh (weakenFromEmpty eE)

-- Public entry. Computes `<-wellFounded` once; no callers need updating.
resolveExpr : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
            → (polys : PolyCtx) → Imports → ℕ
            → Surface.Expr Γ Ψ A → Surface.Expr Γ Ψ A
resolveExpr polys imps fresh e = resolveExprWF polys (<-wellFounded (length polys)) imps fresh e

-- ─── Resolver semantic-equivalence theorems ────────────────────────────
-- The resolver is a pure structural traversal: it commutes with every
-- non-poly Expr constructor by definitional equality, and is the
-- identity on `prim` leaves (external primitives are never polys).
-- Together these establish that `resolveExpr` is a "poly-leaf rewriter"
-- — it only touches `poly` positions, and leaves every other Expr
-- constructor structurally equal.
--
-- Below: full coverage for all 28 non-poly constructors, each `refl`.

-- Var is unaffected by resolution.
resolveExpr-var :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps : Imports) (fresh : ℕ) (i : _)
  → resolveExpr {Γ = Γ} polys imps fresh (Surface.var i) ≡ Surface.var i
resolveExpr-var _ _ _ _ = refl

-- Resolution commutes with lam.
resolveExpr-lam :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {q' A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (q : Quantity) (prf : (q' Once.Type.≤q q) ≡ true)
    (b : Surface.Expr (Γ Surface., A) (q' Surface.∷ Ψ) B)
  → resolveExpr polys imps fresh (Surface.lam q prf b)
      ≡ Surface.lam q prf (resolveExpr polys imps fresh b)
resolveExpr-lam _ _ _ _ _ _ = refl

-- Resolution commutes with app.
resolveExpr-app :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B q}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (f : Surface.Expr Γ Ψ₁ (A Once.Type.⇒[ q ] B))
    (a : Surface.Expr Γ Ψ₂ A)
  → resolveExpr polys imps fresh (Surface.app f a)
      ≡ Surface.app (resolveExpr polys imps fresh f) (resolveExpr polys imps fresh a)
resolveExpr-app _ _ _ _ _ = refl

-- Resolution commutes with pair.
resolveExpr-pair :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ A) (b : Surface.Expr Γ Ψ₂ B)
  → resolveExpr polys imps fresh (Surface.pair a b)
      ≡ Surface.pair (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-pair _ _ _ _ _ = refl

-- Resolution commutes with effApp.
resolveExpr-effApp :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (f : Surface.Expr Γ Ψ₁ (Once.Type.Eff A B)) (a : Surface.Expr Γ Ψ₂ A)
  → resolveExpr polys imps fresh (Surface.effApp f a)
      ≡ Surface.effApp (resolveExpr polys imps fresh f) (resolveExpr polys imps fresh a)
resolveExpr-effApp _ _ _ _ _ = refl

-- Resolution commutes with fst'.
resolveExpr-fst' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (p : Surface.Expr Γ Ψ (A Once.Type.* B))
  → resolveExpr polys imps fresh (Surface.fst' p)
      ≡ Surface.fst' (resolveExpr polys imps fresh p)
resolveExpr-fst' _ _ _ _ = refl

-- Resolution commutes with snd'.
resolveExpr-snd' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (p : Surface.Expr Γ Ψ (A Once.Type.* B))
  → resolveExpr polys imps fresh (Surface.snd' p)
      ≡ Surface.snd' (resolveExpr polys imps fresh p)
resolveExpr-snd' _ _ _ _ = refl

-- Resolution commutes with inl'.
resolveExpr-inl' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ A)
  → resolveExpr polys imps fresh (Surface.inl' {B = B} e)
      ≡ Surface.inl' (resolveExpr polys imps fresh e)
resolveExpr-inl' _ _ _ _ = refl

-- Resolution commutes with inr'.
resolveExpr-inr' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ B)
  → resolveExpr polys imps fresh (Surface.inr' {A = A} e)
      ≡ Surface.inr' (resolveExpr polys imps fresh e)
resolveExpr-inr' _ _ _ _ = refl

-- Resolution commutes with case'.
resolveExpr-case' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψs Ψₗ Ψᵣ : Surface.Usage n} {qℓ qr A B C}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (s : Surface.Expr Γ Ψs (A Once.Type.+ B))
    (l : Surface.Expr (Γ Surface., A) (qℓ Surface.∷ Ψₗ) C)
    (r : Surface.Expr (Γ Surface., B) (qr Surface.∷ Ψᵣ) C)
  → resolveExpr polys imps fresh (Surface.case' s l r)
      ≡ Surface.case' (resolveExpr polys imps fresh s)
                      (resolveExpr polys imps fresh l)
                      (resolveExpr polys imps fresh r)
resolveExpr-case' _ _ _ _ _ _ = refl

-- Unit is unaffected by resolution.
resolveExpr-unit :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
  → resolveExpr {Γ = Γ} polys imps fresh Surface.unit ≡ Surface.unit
resolveExpr-unit _ _ _ = refl

-- Resolution commutes with absurd.
resolveExpr-absurd :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ Once.Type.Void)
  → resolveExpr {A = A} polys imps fresh (Surface.absurd e)
      ≡ Surface.absurd (resolveExpr polys imps fresh e)
resolveExpr-absurd _ _ _ _ = refl

-- Resolution commutes with let'.
resolveExpr-let' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n} {q A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (e₁ : Surface.Expr Γ Ψ₁ A)
    (e₂ : Surface.Expr (Γ Surface., A) (q Surface.∷ Ψ₂) B)
  → resolveExpr polys imps fresh (Surface.let' e₁ e₂)
      ≡ Surface.let' (resolveExpr polys imps fresh e₁) (resolveExpr polys imps fresh e₂)
resolveExpr-let' _ _ _ _ _ = refl

-- Int / str literals are unaffected.
resolveExpr-int :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps : Imports) (fresh : ℕ) (z : Data.Integer.ℤ)
  → resolveExpr {Γ = Γ} polys imps fresh (Surface.int z) ≡ Surface.int z
resolveExpr-int _ _ _ _ = refl

resolveExpr-str :
  ∀ {n} {Γ : Surface.Ctx n} (polys : PolyCtx) (imps : Imports) (fresh : ℕ) (s : String)
  → resolveExpr {Γ = Γ} polys imps fresh (Surface.str s) ≡ Surface.str s
resolveExpr-str _ _ _ _ = refl

-- Resolution commutes with arithmetic (add / sub / mul / div / mod').
resolveExpr-add :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.add a b)
      ≡ Surface.add (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-add _ _ _ _ _ = refl

resolveExpr-sub :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.sub a b)
      ≡ Surface.sub (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-sub _ _ _ _ _ = refl

resolveExpr-mul :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.mul a b)
      ≡ Surface.mul (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-mul _ _ _ _ _ = refl

resolveExpr-div :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.div a b)
      ≡ Surface.div (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-div _ _ _ _ _ = refl

resolveExpr-mod' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.mod' a b)
      ≡ Surface.mod' (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-mod' _ _ _ _ _ = refl

-- Resolution commutes with neg.
resolveExpr-neg :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ Int)
  → resolveExpr polys imps fresh (Surface.neg e) ≡ Surface.neg (resolveExpr polys imps fresh e)
resolveExpr-neg _ _ _ _ = refl

-- Resolution commutes with comparison ops (lt / le / gt / ge / eq / ne).
resolveExpr-lt :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.lt a b)
      ≡ Surface.lt (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-lt _ _ _ _ _ = refl

resolveExpr-le :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.le a b)
      ≡ Surface.le (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-le _ _ _ _ _ = refl

resolveExpr-gt :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.gt a b)
      ≡ Surface.gt (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-gt _ _ _ _ _ = refl

resolveExpr-ge :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.ge a b)
      ≡ Surface.ge (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-ge _ _ _ _ _ = refl

resolveExpr-eq :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.eq a b)
      ≡ Surface.eq (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-eq _ _ _ _ _ = refl

resolveExpr-ne :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ₁ Ψ₂ : Surface.Usage n}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (a : Surface.Expr Γ Ψ₁ Int) (b : Surface.Expr Γ Ψ₂ Int)
  → resolveExpr polys imps fresh (Surface.ne a b)
      ≡ Surface.ne (resolveExpr polys imps fresh a) (resolveExpr polys imps fresh b)
resolveExpr-ne _ _ _ _ _ = refl

-- Resolution commutes with arr' (effect lifting).
resolveExpr-arr' :
  ∀ {n} {Γ : Surface.Ctx n} {Ψ : Surface.Usage n} {A B}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ)
    (e : Surface.Expr Γ Ψ (A Once.Type.⇒ B))
  → resolveExpr polys imps fresh (Surface.arr' e) ≡ Surface.arr' (resolveExpr polys imps fresh e)
resolveExpr-arr' _ _ _ _ = refl

-- Prim is always unaffected — it's for external primitives, not polys.
resolveExpr-prim :
  ∀ {n} {Γ : Surface.Ctx n} {A}
    (polys : PolyCtx) (imps : Imports) (fresh : ℕ) (s : String)
  → resolveExpr {Γ = Γ} polys imps fresh (Surface.prim {A = A} s)
      ≡ Surface.prim s
resolveExpr-prim _ _ _ _ = refl

-- ─── Gap 1 (positive direction, DEFERRED for a different reason): ────
-- The positive theorem — "at a matched poly, resolver splices the body"
-- — is intuitively trivial under Option A (no string decoding). The
-- proof does NOT require Acc-irrelevance anymore, but runs into a
-- different Agda limitation: the `resolvePolyCase` helper uses a nested
-- `with` on `checkElab ... body T` whose abstraction interacts with
-- `rewrite polyEq` in the outer proof, producing an "ill-typed with"
-- error. Resolvable with more careful proof engineering (e.g. explicit
-- `subst` chains, or inlining the case analysis via a view pattern).
-- Not chased here — the architectural wins of Option A are the primary
-- deliverable.

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
checkElab-fallback-RVar-poly {ctx} x T bbcOther x≢unit localN importN polyE _
  rewrite bbcOther
  with StrProp._≟_ x "unit"
... | yes eq = ⊥-elim (x≢unit eq)
... | no  _
      rewrite localN
            | importN
            | polyE
      = _ , _ , _ , refl

-- RApp (RVar "id") arg: no specialised check clause for "id" as app head
-- (only "inl"/"inr"/"initial" are specialised). Falls to fallback.
checkElab-fallback-RApp-id :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "id") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "id") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-id arg T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RApp (RVar "fst") arg: no specialised check clause.
checkElab-fallback-RApp-fst :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "fst") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-fst arg T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RApp (RVar "snd") arg: no specialised check clause.
checkElab-fallback-RApp-snd :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "snd") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-snd arg T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RApp f x with `classifyAppHead f ≡ nothing`: provable thanks to the
-- `AppHeadView` refactor. `classifyAppHead-nothing⇒view-other` converts
-- the premise to the view form (`classifyAppHeadView f ≡ ahv-other`),
-- which rewrites substitute cleanly — no opaque `with`-helper wall.
--
-- The rewrite is applied TWICE: `classifyAppHeadView f` appears in
-- both checkElab's outer dispatch AND inferElab's nested dispatch
-- (via the checkElab→inferElab call chain), and each `rewrite` pass
-- substitutes one layer's occurrence. After both rewrites, Agda
-- reduces through both with-abstractions; `rewrite eqInf` finishes
-- the inferElab leg, and `with T ≟T T` closes the goal.
checkElab-fallback-RApp-generic :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f' : ℕ}
  → classifyAppHead f ≡ nothing
  → inferElab ctx (Raw.RApp f x) ≡ success T Ψ eE d f'
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f'' →
      checkElab ctx (Raw.RApp f x) T ≡ success Ψ eE' d' f'')))
checkElab-fallback-RApp-generic f x T notPoly eqInf
  rewrite classifyAppHead-nothing⇒view-other {f} notPoly
        | classifyAppHead-nothing⇒view-other {f} notPoly
        | eqInf
  with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RApp (RVar "terminal") arg: no specialised check clause.
checkElab-fallback-RApp-terminal :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RApp (Raw.RVar "terminal") arg) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RApp (Raw.RVar "terminal") arg) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RApp-terminal arg T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

-- RBinOp: no specialised check clause.
checkElab-fallback-RBinOp :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (e₁ e₂ : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d f : ℕ}
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success T Ψ eE d f
  → ∃-syntax (λ eE' → ∃-syntax (λ d' → ∃-syntax (λ f' →
      checkElab ctx (Raw.RBinOp op e₁ e₂) T ≡ success Ψ eE' d' f')))
checkElab-fallback-RBinOp op e₁ e₂ T eqInf
  rewrite eqInf with T ≟T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------

-- | Compile with type signature
compileExprTyped : RawExpr → (A : Type) → Maybe (IR Unit A)
compileExprTyped e A with checkElab emptyCtx e A
... | failure _                 = nothing
... | success Ψ se _ _          = just (elaborate se)

-- | Compile without signature
compileExpr : RawExpr → Maybe (∃[ A ] IR Unit A)
compileExpr e with inferElab emptyCtx e
... | failure _                 = nothing
... | success A Ψ se _ _        = just (A , elaborate se)
