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
open import Data.Nat using (ℕ; zero; suc; _≤?_; _⊔_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Once.Type
open Once.Type using (showQuantity; showType) public
open import Once.CCC.IR as IR
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; name)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookupUsage; tailUsage)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open import Once.Surface.Thinning using (weaken)
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
weakenFromEmpty : ∀ {n} {Γ : SCtx n} {A : Type} → SExpr S∅ A → SExpr Γ A
weakenFromEmpty {Γ = S∅} e = e
weakenFromEmpty {Γ = Γ S, B ^ q} e = weaken {A = B} {q = q} (weakenFromEmpty {Γ = Γ} e)

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
-- Includes:
--   - Maximum nesting depth encountered (for verification limit tracking)
--   - Updated fresh counter (for polymorphic instantiation)
--   - Usage vector (for QTT - tracks how variables were used)
data InferElabResult {n : ℕ} (Δ : SCtx n) : Set where
  success : (A : Type) → SExpr Δ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : Surface.Usage n)  -- NEW: QTT usage tracking
          → InferElabResult Δ
  failure : String → InferElabResult Δ

-- | Result of type checking (verify against expected type)
-- The type is known, so we only return the expression, depth, fresh counter, and usage
data CheckElabResult {n : ℕ} (Δ : SCtx n) (A : Type) : Set where
  success : SExpr Δ A → (depth : ℕ) → (fresh : ℕ)
          → (usage : Surface.Usage n)  -- NEW: QTT usage tracking
          → CheckElabResult Δ A
  failure : String → CheckElabResult Δ A

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

-- | Empty context
emptyCtx : NamedCtx
emptyCtx = mkCtx 0 ∅ S∅ 0 emptyImports

-- | Create context with imports
ctxWithImports : Imports → NamedCtx
ctxWithImports imps = mkCtx 0 ∅ S∅ 0 imps

-- | Create context with imports and self-reference for recursive definitions
-- The function's own name and type are added to the imports list so it can call itself.
-- This causes recursive calls to elaborate to `Prim "name"` which the C backend
-- handles as a function call.
ctxWithImportsAndSelf : Imports → String → Type → NamedCtx
ctxWithImportsAndSelf imps name ty =
  ctxWithImports ((name , ty) ∷ imps)

-- | Extend context with a new binding (preserves fresh counter and imports)
extendNamedCtx : NamedCtx → String → Type → NamedCtx
extendNamedCtx (mkCtx n Γ Δ fresh imps) x A = mkCtx (suc n) (extendCtx Γ x A) (Δ S, A) fresh imps

-- | Bump fresh counter (for generating new type variables)
bumpFresh : NamedCtx → NamedCtx
bumpFresh (mkCtx n Γ Δ fresh imps) = mkCtx n Γ Δ (suc fresh) imps

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

specId : (T : Type) → SExpr S∅ (T ⇒ T)
specId T = Surface.lam Many (Surface.var zero)

specFst : (A B : Type) → SExpr S∅ (A Once.Type.* B ⇒ A)
specFst A B = Surface.lam Many (Surface.fst' (Surface.var zero))

specSnd : (A B : Type) → SExpr S∅ (A Once.Type.* B ⇒ B)
specSnd A B = Surface.lam Many (Surface.snd' (Surface.var zero))

specInl : (A B : Type) → SExpr S∅ (A ⇒ (A Once.Type.+ B))
specInl A B = Surface.lam Many (Surface.inl' (Surface.var zero))

specInr : (A B : Type) → SExpr S∅ (B ⇒ (A Once.Type.+ B))
specInr A B = Surface.lam Many (Surface.inr' (Surface.var zero))

specUnitGen : SExpr S∅ Unit
specUnitGen = Surface.unit

-- pair : (a → b) → (a → c) → a → (b × c)
specPair : (A B C : Type)
         → SExpr S∅ ((A ⇒ B) ⇒ (A ⇒ C) ⇒ A ⇒ (B Once.Type.* C))
specPair A B C =
  Surface.lam Many (Surface.lam Many (Surface.lam Many
    (Surface.pair
      (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero))
      (Surface.app (Surface.var (suc zero)) (Surface.var zero)))))

-- terminal : a → Unit
specTerminal : (A : Type) → SExpr S∅ (A ⇒ Unit)
specTerminal A = Surface.lam Many Surface.unit

-- initial : Void → a
specInitial : (A : Type) → SExpr S∅ (Void ⇒ A)
specInitial A = Surface.lam Many (Surface.absurd (Surface.var zero))

-- curry : ((a × b) → c) → a → b → c
specCurry : (A B C : Type)
          → SExpr S∅ ((A Once.Type.* B ⇒ C) ⇒ A ⇒ B ⇒ C)
specCurry A B C =
  Surface.lam Many (Surface.lam Many (Surface.lam Many
    (Surface.app (Surface.var (suc (suc zero)))
                 (Surface.pair (Surface.var (suc zero)) (Surface.var zero)))))

-- apply : ((a → b) × a) → b
specApply : (A B : Type)
          → SExpr S∅ (((A ⇒ B) Once.Type.* A) ⇒ B)
specApply A B =
  Surface.lam Many
    (Surface.app (Surface.fst' (Surface.var zero))
                 (Surface.snd' (Surface.var zero)))

-- compose : (b → c) → (a → b) → a → c
specCompose : (A B C : Type)
            → SExpr S∅ ((B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
specCompose A B C =
  Surface.lam Many (Surface.lam Many (Surface.lam Many
    (Surface.app (Surface.var (suc (suc zero)))
                 (Surface.app (Surface.var (suc zero)) (Surface.var zero)))))

-- arr : (a → b) → Eff a b
specArr : (A B : Type) → SExpr S∅ ((A ⇒ B) ⇒ Eff A B)
specArr A B = Surface.lam Many (Surface.arr' (Surface.var zero))


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
-- Returns just (i , type-at-i) if found in local bindings, nothing otherwise.
lookupLocal : (ctx : NamedCtx) → String
            → Maybe (∃[ A ] (SExpr (NamedCtx.debruijn ctx) A))
lookupLocal (mkCtx n Γ Δ _ _) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → Maybe (∃[ A ] (SExpr Δ' A))
    go [] S∅                  = nothing
    go [] (_ S, _ ^ _)        = nothing
    go (_ ∷ _) S∅             = nothing
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero)
    ... | no _  with go Γ' Δ'
    ...   | nothing             = nothing
    ...   | just (A , se)       = just (A , weaken {A = B} {q = q} se)

-- | Find a local variable's de Bruijn position and quantity by name.
-- Returns nothing if not in local bindings.
findLocalVarUsage : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx) × Quantity)
findLocalVarUsage (mkCtx n Γ Δ _ _) x = go Γ Δ
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

-- | Projection of an InferElabResult as a function-typed result.
-- Used to avoid combinatorial nested-with coverage when the caller needs
-- the inferred type to be a function type. Handles failure propagation
-- and exhaustive non-function-type cases in one place.
data FunProjection {n : ℕ} (Δ : SCtx n) : Set where
  isFun  : (A : Type) (q : Quantity) (B : Type)
         → SExpr Δ (A ⇒[ q ] B) → ℕ → ℕ → Surface.Usage n
         → FunProjection Δ
  notFun : String → FunProjection Δ

asFun : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → FunProjection Δ
asFun (failure err)                           = notFun err
asFun (success (A ⇒[ q ] B) se d f u)          = isFun A q B se d f u
asFun (success Unit _ _ _ _)                  = notFun "expected function type, got Unit"
asFun (success Void _ _ _ _)                  = notFun "expected function type, got Void"
asFun (success Int _ _ _ _)                   = notFun "expected function type, got Int"
asFun (success Float _ _ _ _)                 = notFun "expected function type, got Float"
asFun (success Str _ _ _ _)                   = notFun "expected function type, got Str"
asFun (success Buffer _ _ _ _)                = notFun "expected function type, got Buffer"
asFun (success (_ Once.Type.* _) _ _ _ _)     = notFun "expected function type, got product"
asFun (success (_ Once.Type.+ _) _ _ _ _)     = notFun "expected function type, got sum"
asFun (success (Eff _ _) _ _ _ _)             = notFun "expected function type, got Eff"
asFun (success (μ-type _) _ _ _ _)            = notFun "expected function type, got μ-type"
asFun (success (ν-type _) _ _ _ _)            = notFun "expected function type, got ν-type"

-- | Projection as an Int-typed result. Same pattern as asFun.
data IntProjection {n : ℕ} (Δ : SCtx n) : Set where
  isInt  : SExpr Δ Int → ℕ → ℕ → Surface.Usage n → IntProjection Δ
  notInt : String → IntProjection Δ

asInt : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → IntProjection Δ
asInt (failure err)                           = notInt err
asInt (success Int se d f u)                  = isInt se d f u
asInt (success Unit _ _ _ _)                  = notInt "expected Int, got Unit"
asInt (success Void _ _ _ _)                  = notInt "expected Int, got Void"
asInt (success Float _ _ _ _)                 = notInt "expected Int, got Float"
asInt (success Str _ _ _ _)                   = notInt "expected Int, got Str"
asInt (success Buffer _ _ _ _)                = notInt "expected Int, got Buffer"
asInt (success (_ Once.Type.* _) _ _ _ _)     = notInt "expected Int, got product"
asInt (success (_ Once.Type.+ _) _ _ _ _)     = notInt "expected Int, got sum"
asInt (success (_ ⇒[ _ ] _) _ _ _ _)          = notInt "expected Int, got function"
asInt (success (Eff _ _) _ _ _ _)             = notInt "expected Int, got Eff"
asInt (success (μ-type _) _ _ _ _)            = notInt "expected Int, got μ-type"
asInt (success (ν-type _) _ _ _ _)            = notInt "expected Int, got ν-type"

------------------------------------------------------------------------
-- New Bidirectional Inference/Checking (ground types throughout)
------------------------------------------------------------------------
--
-- These produce InferElabResult/CheckElabResult directly — no PolyExpr
-- intermediate, no InferSubst, no extraction. Polymorphic builtins are
-- specialized at their use site by inline pattern matching on the
-- application chain shape.
--
-- Current coverage: literals, unit, local variables, imports, type
-- annotations, let bindings (monomorphic), pair, case, binops, unary,
-- full applications of polymorphic builtins with all arguments provided,
-- lambdas in check mode, arbitrary applications in infer mode when the
-- function's type is a ground function type.

mutual
  inferNew : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
  checkNew : (ctx : NamedCtx) → RawExpr → (T : Type) → CheckElabResult (NamedCtx.debruijn ctx) T

  -- ===== inferNew =====

  -- Literals
  inferNew ctx (Raw.RInt n) =
    success Int (Surface.int n) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  inferNew ctx (Raw.RStringLit s) =
    success Str (Surface.str s) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  inferNew ctx Raw.RUnit =
    success Unit Surface.unit 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage

  -- Type annotation: check against the annotated type
  inferNew ctx (Raw.RAnnot e T) with checkNew ctx e T
  ... | success se d f u = success T se d f u
  ... | failure err = failure err

  -- The `unit` builtin is monomorphic: type is Unit.
  inferNew ctx (Raw.RVar "unit") =
    success Unit Surface.unit 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage

  -- Variable lookup (generic). Local first, then import, else fail.
  inferNew ctx (Raw.RVar x) with lookupLocal ctx x
  ... | just (A , se) with findLocalVarUsage ctx x
  ...   | just (i , q) = success A se 0 (NamedCtx.freshCounter ctx) (Surface.singleUse i q)
  ...   | nothing = success A se 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  inferNew ctx (Raw.RVar x) | nothing with lookupImport (NamedCtx.imports ctx) x
  ... | just ty = success ty (Surface.prim x) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  ... | nothing = failure ("Unbound or unspecialized variable: " ++ x ++
                           " (polymorphic builtins must appear applied or in check mode)")

  -- Qualified name: look up as "alias.name"
  inferNew ctx (Raw.RQualified name alias) with lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)
  ... | just ty = success ty (Surface.prim (alias ++ "." ++ name)) 0 (NamedCtx.freshCounter ctx) Surface.zeroUsage
  ... | nothing = failure ("Unbound qualified variable: " ++ name ++ "@" ++ alias)

  -- Lambda without annotation: rejected in infer mode
  inferNew ctx (Raw.RLam _ _) =
    failure "Lambda without type annotation not supported in inference mode."

  -- Polymorphic builtin applications (full arity).
  -- id : A → A
  inferNew ctx (Raw.RApp (Raw.RVar "id") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success T argE d f u =
        success T (Surface.app (weakenFromEmpty (specId T)) argE) (suc d) f u

  -- fst : (A * B) → A
  inferNew ctx (Raw.RApp (Raw.RVar "fst") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success (A Once.Type.* B) argE d f u =
        success A (Surface.app (weakenFromEmpty (specFst A B)) argE) (suc d) f u
  ... | success _ _ _ _ _ = failure "fst requires a pair argument"

  -- snd : (A * B) → B
  inferNew ctx (Raw.RApp (Raw.RVar "snd") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success (A Once.Type.* B) argE d f u =
        success B (Surface.app (weakenFromEmpty (specSnd A B)) argE) (suc d) f u
  ... | success _ _ _ _ _ = failure "snd requires a pair argument"

  -- terminal : A → Unit
  inferNew ctx (Raw.RApp (Raw.RVar "terminal") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success A argE d f u =
        success Unit (Surface.app (weakenFromEmpty (specTerminal A)) argE) (suc d) f u

  -- arr : (A → B) → Eff A B
  inferNew ctx (Raw.RApp (Raw.RVar "arr") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success (A ⇒[ Many ] B) argE d f u =
        success (Eff A B) (Surface.app (weakenFromEmpty (specArr A B)) argE) (suc d) f u
  ... | success _ _ _ _ _ = failure "arr requires a (A → B) pure-function argument"

  -- apply : ((A → B) * A) → B
  inferNew ctx (Raw.RApp (Raw.RVar "apply") arg) with inferNew ctx arg
  ... | failure err = failure err
  ... | success ((A ⇒[ Many ] B) Once.Type.* A') argE d f u with A ≟T A'
  ...   | yes refl = success B (Surface.app (weakenFromEmpty (specApply A B)) argE) (suc d) f u
  ...   | no _ = failure "apply: function domain must match second component"
  inferNew ctx (Raw.RApp (Raw.RVar "apply") _) | success _ _ _ _ _ = failure "apply requires ((A → B) * A)"

  -- compose : (B → C) → (A → B) → A → C  (arity 3)
  inferNew ctx (Raw.RApp (Raw.RApp (Raw.RApp (Raw.RVar "compose") f) g) x) with asFun (inferNew ctx f)
  ... | notFun err = failure ("compose/f: " ++ err)
  ... | isFun B qF C fE df ff uf with qF ≟q Many
  ...   | no _ = failure "compose: f must have Many-arrow function type"
  ...   | yes refl with asFun (inferNew ctx g)
  ...     | notFun err = failure ("compose/g: " ++ err)
  ...     | isFun A qG B' gE dg fg ug with qG ≟q Many | B ≟T B'
  ...       | no _ | _ = failure "compose: g must have Many-arrow function type"
  ...       | yes _ | no _ = failure "compose: g's codomain must match f's domain"
  ...       | yes refl | yes refl with inferNew ctx x
  ...         | failure err = failure err
  ...         | success A' xE dx fx ux with A ≟T A'
  ...           | yes refl = success C
                               (Surface.app (Surface.app
                                 (Surface.app (weakenFromEmpty (specCompose A B C)) fE)
                                 gE) xE)
                               (suc (df ⊔ dg ⊔ dx)) fx (uf +ᵘ ug +ᵘ ux)
  ...           | no _ = failure "compose: x's type must match g's domain"

  -- pair (fork) : (A → B) → (A → C) → A → (B * C)  (arity 3)
  inferNew ctx (Raw.RApp (Raw.RApp (Raw.RApp (Raw.RVar "pair") f) g) x) with asFun (inferNew ctx f)
  ... | notFun err = failure ("pair/f: " ++ err)
  ... | isFun A qF B fE df ff uf with qF ≟q Many
  ...   | no _ = failure "pair: f must have Many-arrow function type"
  ...   | yes refl with asFun (inferNew ctx g)
  ...     | notFun err = failure ("pair/g: " ++ err)
  ...     | isFun A' qG C gE dg fg ug with qG ≟q Many | A ≟T A'
  ...       | no _ | _ = failure "pair: g must have Many-arrow function type"
  ...       | yes _ | no _ = failure "pair: f and g must share the same domain"
  ...       | yes refl | yes refl with inferNew ctx x
  ...         | failure err = failure err
  ...         | success A'' xE dx fx ux with A ≟T A''
  ...           | yes refl = success (B Once.Type.* C)
                               (Surface.app (Surface.app
                                 (Surface.app (weakenFromEmpty (specPair A B C)) fE)
                                 gE) xE)
                               (suc (df ⊔ dg ⊔ dx)) fx (uf +ᵘ ug +ᵘ ux)
  ...           | no _ = failure "pair: x's type must match f/g domain"

  -- curry : ((A * B) → C) → A → B → C  (arity 3)
  inferNew ctx (Raw.RApp (Raw.RApp (Raw.RApp (Raw.RVar "curry") fn) a) b) with asFun (inferNew ctx fn)
  ... | notFun err = failure ("curry/fn: " ++ err)
  ... | isFun domT qF C fnE df ff uf with qF ≟q Many
  ...   | no _ = failure "curry: fn must have Many-arrow function type"
  ...   | yes refl with domT
  ...     | Unit        = failure "curry: fn's domain must be a product (A * B)"
  ...     | Void        = failure "curry: fn's domain must be a product (A * B)"
  ...     | Int         = failure "curry: fn's domain must be a product (A * B)"
  ...     | Float       = failure "curry: fn's domain must be a product (A * B)"
  ...     | Str         = failure "curry: fn's domain must be a product (A * B)"
  ...     | Buffer      = failure "curry: fn's domain must be a product (A * B)"
  ...     | (_ Once.Type.+ _) = failure "curry: fn's domain must be a product (A * B)"
  ...     | (_ ⇒[ _ ] _)       = failure "curry: fn's domain must be a product (A * B)"
  ...     | (Eff _ _)   = failure "curry: fn's domain must be a product (A * B)"
  ...     | (μ-type _)  = failure "curry: fn's domain must be a product (A * B)"
  ...     | (ν-type _)  = failure "curry: fn's domain must be a product (A * B)"
  ...     | (A Once.Type.* B) with inferNew ctx a
  ...       | failure err = failure err
  ...       | success A' aE da fa ua with A ≟T A'
  ...         | no _ = failure "curry: a's type must match the first component"
  ...         | yes refl with inferNew ctx b
  ...           | failure err = failure err
  ...           | success B' bE db fb ub with B ≟T B'
  ...             | yes refl = success C
                                 (Surface.app (Surface.app
                                   (Surface.app (weakenFromEmpty (specCurry A B C)) fnE)
                                   aE) bE)
                                 (suc (df ⊔ da ⊔ db)) fb (uf +ᵘ ua +ᵘ ub)
  ...             | no _ = failure "curry: b's type must match the second component"

  -- Partial or unsupported builtins in infer mode
  inferNew ctx (Raw.RApp (Raw.RVar "inl") _) =
    failure "inl requires check mode (needs target sum type)"
  inferNew ctx (Raw.RApp (Raw.RVar "inr") _) =
    failure "inr requires check mode (needs target sum type)"
  inferNew ctx (Raw.RApp (Raw.RVar "initial") _) =
    failure "initial requires check mode (needs target type)"

  -- Generic application: infer f, project as function type, then infer x.
  inferNew ctx (Raw.RApp f x) with asFun (inferNew ctx f)
  ... | notFun err = failure err
  ... | isFun A q B fE df ff uf with inferNew ctx x
  ...   | failure err = failure err
  ...   | success A' xE dx fx ux with A ≟T A'
  ...     | yes refl = success B (Surface.app fE xE) (df ⊔ dx) fx (uf +ᵘ ux)
  ...     | no _ = failure ("Application: argument type " ++ showType A' ++
                            " does not match function domain " ++ showType A)

  -- Let binding: infer e₁ monomorphically, then e₂ under extended context
  inferNew ctx (Raw.RLet x e₁ e₂) with inferNew ctx e₁
  ... | failure err = failure err
  ... | success A e₁E d₁ f₁ u₁ with inferNew (extendNamedCtx ctx x A) e₂
  ...   | failure err = failure err
  ...   | success B e₂E d₂ f₂ u₂ =
        success B (Surface.let' e₁E e₂E) (d₁ ⊔ suc d₂) f₂ (u₁ +ᵘ Surface.tailUsage u₂)

  -- Pair introduction
  inferNew ctx (Raw.RPair a b) with inferNew ctx a
  ... | failure err = failure err
  ... | success A aE da fa ua with inferNew ctx b
  ...   | failure err = failure err
  ...   | success B bE db fb ub =
        success (A Once.Type.* B) (Surface.pair aE bE) (da ⊔ db) fb (ua +ᵘ ub)

  -- Case (destruct)
  inferNew ctx (Raw.RDestruct scrut xL eL xR eR) with inferNew ctx scrut
  ... | failure err = failure err
  ... | success (A Once.Type.+ B) scrutE ds fs us with inferNew (extendNamedCtx ctx xL A) eL
  ...   | failure err = failure err
  ...   | success C₁ eLE dL fL uL with inferNew (extendNamedCtx ctx xR B) eR
  ...     | failure err = failure err
  ...     | success C₂ eRE dR fR uR with C₁ ≟T C₂
  ...       | yes refl = success C₁ (Surface.case' scrutE eLE eRE)
                           (ds ⊔ suc dL ⊔ suc dR) fR (us +ᵘ Surface.tailUsage uL +ᵘ Surface.tailUsage uR)
  ...       | no _ = failure "Case branches have different types"
  inferNew ctx (Raw.RDestruct _ _ _ _ _) | success _ _ _ _ _ = failure "Case requires a sum-typed scrutinee"

  -- Binary operators: both operands must be Int.
  inferNew ctx (Raw.RBinOp op e₁ e₂) with asInt (inferNew ctx e₁)
  ... | notInt err = failure ("binop left: " ++ err)
  ... | isInt e₁E d₁ f₁ u₁ with asInt (inferNew ctx e₂)
  ...   | notInt err = failure ("binop right: " ++ err)
  ...   | isInt e₂E d₂ f₂ u₂ =
        if Raw.isArithmeticOp op
          then success Int (mkArith op e₁E e₂E) (d₁ ⊔ d₂) f₂ (u₁ +ᵘ u₂)
          else success (Unit Once.Type.+ Unit) (mkCmp op e₁E e₂E) (d₁ ⊔ d₂) f₂ (u₁ +ᵘ u₂)
    where
      mkArith : Raw.BinOp → SExpr _ Int → SExpr _ Int → SExpr _ Int
      mkArith Raw.OpAdd = Surface.add
      mkArith Raw.OpSub = Surface.sub
      mkArith Raw.OpMul = Surface.mul
      mkArith Raw.OpDiv = Surface.div
      mkArith Raw.OpMod = Surface.mod'
      mkArith _ = Surface.add
      mkCmp : Raw.BinOp → SExpr _ Int → SExpr _ Int → SExpr _ (Unit Once.Type.+ Unit)
      mkCmp Raw.OpLt = Surface.lt
      mkCmp Raw.OpLe = Surface.le
      mkCmp Raw.OpGt = Surface.gt
      mkCmp Raw.OpGe = Surface.ge
      mkCmp Raw.OpEq = Surface.eq
      mkCmp Raw.OpNe = Surface.ne
      mkCmp _ = Surface.lt

  -- Unary
  inferNew ctx (Raw.RUnaryOp Raw.OpNeg e) with inferNew ctx e
  ... | failure err = failure err
  ... | success Int eE d f u = success Int (Surface.neg eE) d f u
  ... | success _ _ _ _ _ = failure "Negation requires Int operand"

  -- ===== checkNew =====

  -- Lambda in check mode: destruct function type from expected
  checkNew ctx (Raw.RLam x body) (A ⇒[ q ] B) with checkNew (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success bodyE d f u =
        let paramUsage = Surface.lookupUsage u zero
        in if paramUsage ≤q q
             then success (Surface.lam q bodyE) (suc d) f (Surface.tailUsage u)
             else failure ("Parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                          " but declared with quantity " ++ showQuantity q)
  checkNew ctx (Raw.RLam _ _) _ = failure "Lambda requires function type"

  -- inl in check mode: expected sum type
  checkNew ctx (Raw.RApp (Raw.RVar "inl") arg) (A Once.Type.+ B) with checkNew ctx arg A
  ... | failure err = failure err
  ... | success argE d f u =
        success (Surface.app (weakenFromEmpty (specInl A B)) argE) (suc d) f u
  checkNew ctx (Raw.RApp (Raw.RVar "inl") _) _ = failure "inl expects a sum type in check mode"

  -- inr in check mode
  checkNew ctx (Raw.RApp (Raw.RVar "inr") arg) (A Once.Type.+ B) with checkNew ctx arg B
  ... | failure err = failure err
  ... | success argE d f u =
        success (Surface.app (weakenFromEmpty (specInr A B)) argE) (suc d) f u
  checkNew ctx (Raw.RApp (Raw.RVar "inr") _) _ = failure "inr expects a sum type in check mode"

  -- initial in check mode: Void → A, so arg must have type Void, result T = A
  checkNew ctx (Raw.RApp (Raw.RVar "initial") arg) T with checkNew ctx arg Void
  ... | failure err = failure err
  ... | success argE d f u =
        success (Surface.app (weakenFromEmpty (specInitial T)) argE) (suc d) f u

  -- Generic fallback: infer and match types
  checkNew ctx e T with inferNew ctx e
  ... | failure err = failure err
  ... | success T' eE d f u with T ≟T T'
  ...   | yes refl = success eE d f u
  ...   | no _ = failure ("Type mismatch: expected " ++ showType T ++ " but got " ++ showType T')

-- | Experimental: new-architecture inference entry point (not yet default).
-- Enforces the depth ≤ 7 limit, same as inferElab.
newInferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
newInferElab ctx rawExpr = checkDepth (inferNew ctx rawExpr)
  where
    checkDepth : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
    checkDepth (failure err) = failure err
    checkDepth (success ty expr depth fresh usage) with depth ≤? 7
    ... | yes _ = success ty expr depth fresh usage
    ... | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                         "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                         "  Proven depth limit: 7\n" ++
                         "  Please refactor to reduce nesting of λ/case/let expressions.")

-- | Experimental: new-architecture checking entry point (not yet default).
newCheckElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
newCheckElab ctx expr ty = checkDepth (checkNew ctx expr ty)
  where
    checkDepth : CheckElabResult (NamedCtx.debruijn ctx) ty → CheckElabResult (NamedCtx.debruijn ctx) ty
    checkDepth (failure err) = failure err
    checkDepth (success expr' depth fresh usage) with depth ≤? 7
    ... | yes _ = success expr' depth fresh usage
    ... | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                         "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                         "  Proven depth limit: 7\n" ++
                         "  Please refactor to reduce nesting of λ/case/let expressions.")

------------------------------------------------------------------------
-- Depth-Checked Inference (Public Interface)
------------------------------------------------------------------------

-- | Type inference with depth limit enforcement
--
-- This is the public interface that enforces the depth ≤ 7 constraint.
-- Programs exceeding this limit are rejected with a clear error message.
--
-- RATIONALE: The exchange functions (used for context manipulation) are
-- proven correct only up to exchange₇. See docs/formal/full-verification-compiler-stack.md
--
-- Implementation uses two-phase approach:
-- 1. Polymorphic inference (builds PolyExpr with potential TVars)
-- 2. Extraction (converts to SExpr, fails if TVars remain)
--
-- This enables polymorphic builtins (id, fst, snd, etc.) to unify properly
-- during type inference before committing to ground types.
--
-- | Implementation now delegates to newInferElab (bidirectional, ground).
-- The old polymorphic-inference-then-extract path is retained only for the
-- deprecated compile paths while downstream stages are verified.
inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
inferElab = newInferElab

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------


-- | Implementation delegates to newCheckElab (bidirectional, ground).
checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
checkElab = newCheckElab

-- | Compile with type signature (PRIMARY INTERFACE - uses checking mode)
--
-- This is the recommended way to compile Once programs, as all top-level
-- declarations should have type signatures (Once philosophy: explicit > implicit).
--
-- Uses bidirectional checking mode for better error messages and polymorphism.
compileExprTyped : RawExpr → (A : Type) → Maybe (IR Unit A)
compileExprTyped e A with checkElab emptyCtx e A
... | failure _ = nothing
... | success se _ _ _ = just (elaborate se)

-- | Compile without type signature (FALLBACK - uses inference mode)
--
-- This is provided for compatibility, but users should prefer compileExprTyped
-- with explicit type signatures. Inference-only mode has limitations:
-- - Cannot handle all polymorphic cases
-- - Less helpful error messages
-- - May fail where checking succeeds
--
-- Once philosophy: Types guide, signatures required.
compileExpr : RawExpr → Maybe (∃[ A ] IR Unit A)
compileExpr e with inferElab emptyCtx e
... | failure _ = nothing
... | success A se _ _ _ = just (A , elaborate se)