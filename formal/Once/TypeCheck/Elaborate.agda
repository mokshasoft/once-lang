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
  failure : String → InferElabResult Δ

-- | Result of type checking (verify against expected type)
data CheckElabResult {n : ℕ} (Δ : SCtx n) (A : Type) : Set where
  success : (Ψ : Surface.Usage n) → SExpr Δ Ψ A
          → (depth : ℕ) → (fresh : ℕ)
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
lookupLocal (mkCtx n Γ Δ _ _) x = go Γ Δ
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

------------------------------------------------------------------------
-- Function-type and Int-type projections (for inference branching)
------------------------------------------------------------------------

data FunProjection {n : ℕ} (Δ : SCtx n) : Set where
  isFun  : (A : Type) (q : Quantity) (B : Type) (Ψ : Surface.Usage n)
         → SExpr Δ Ψ (A ⇒[ q ] B) → ℕ → ℕ → FunProjection Δ
  notFun : String → FunProjection Δ

asFun : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → FunProjection Δ
asFun (failure err)                                      = notFun err
asFun (success (A ⇒[ q ] B) Ψ se d f)                    = isFun A q B Ψ se d f
asFun (success Unit _ _ _ _)                             = notFun "expected function type, got Unit"
asFun (success Void _ _ _ _)                             = notFun "expected function type, got Void"
asFun (success Int _ _ _ _)                              = notFun "expected function type, got Int"
asFun (success Float _ _ _ _)                            = notFun "expected function type, got Float"
asFun (success Str _ _ _ _)                              = notFun "expected function type, got Str"
asFun (success Buffer _ _ _ _)                           = notFun "expected function type, got Buffer"
asFun (success (_ Once.Type.* _) _ _ _ _)                = notFun "expected function type, got product"
asFun (success (_ Once.Type.+ _) _ _ _ _)                = notFun "expected function type, got sum"
asFun (success (Eff _ _) _ _ _ _)                        = notFun "expected function type, got Eff"
asFun (success (μ-type _) _ _ _ _)                       = notFun "expected function type, got μ-type"
asFun (success (ν-type _) _ _ _ _)                       = notFun "expected function type, got ν-type"

data IntProjection {n : ℕ} (Δ : SCtx n) : Set where
  isInt  : (Ψ : Surface.Usage n) → SExpr Δ Ψ Int → ℕ → ℕ → IntProjection Δ
  notInt : String → IntProjection Δ

asInt : ∀ {n} {Δ : SCtx n} → InferElabResult Δ → IntProjection Δ
asInt (failure err)                                      = notInt err
asInt (success Int Ψ se d f)                             = isInt Ψ se d f
asInt (success Unit _ _ _ _)                             = notInt "expected Int, got Unit"
asInt (success Void _ _ _ _)                             = notInt "expected Int, got Void"
asInt (success Float _ _ _ _)                            = notInt "expected Int, got Float"
asInt (success Str _ _ _ _)                              = notInt "expected Int, got Str"
asInt (success Buffer _ _ _ _)                           = notInt "expected Int, got Buffer"
asInt (success (_ Once.Type.* _) _ _ _ _)                = notInt "expected Int, got product"
asInt (success (_ Once.Type.+ _) _ _ _ _)                = notInt "expected Int, got sum"
asInt (success (_ ⇒[ _ ] _) _ _ _ _)                     = notInt "expected Int, got function"
asInt (success (Eff _ _) _ _ _ _)                        = notInt "expected Int, got Eff"
asInt (success (μ-type _) _ _ _ _)                       = notInt "expected Int, got μ-type"
asInt (success (ν-type _) _ _ _ _)                       = notInt "expected Int, got ν-type"

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
decideLeq : (q' q : Quantity) → Maybe ((q' ≤q q) ≡ true)
decideLeq q' q with q' ≤q q
... | true  = just refl
... | false = nothing

------------------------------------------------------------------------
-- Bidirectional Inference (produces usage-indexed Expr)
------------------------------------------------------------------------

mutual
  inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
  checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A

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
  ...     | nothing = failure ("Unbound or unspecialized variable: " ++ x ++
                               " (polymorphic builtins must appear applied or in check mode)")

  -- Qualified name: look up as "alias.name"
  inferElab ctx (Raw.RQualified name alias) with lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)
  ... | just ty = success ty _ (Surface.prim (alias ++ "." ++ name)) 0 (NamedCtx.freshCounter ctx)
  ... | nothing = failure ("Unbound qualified variable: " ++ name ++ "@" ++ alias)

  -- Lambda without annotation: rejected in infer mode
  inferElab ctx (Raw.RLam _ _) =
    failure "Lambda without type annotation not supported in inference mode."

  -- Polymorphic builtin applications (fully applied):

  -- id : A → A
  inferElab ctx (Raw.RApp (Raw.RVar "id") arg) with inferElab ctx arg
  ... | failure err = failure err
  ... | success T Ψ argE d f =
        success T _ (Surface.app (weakenFromEmpty (specId T)) argE) (suc d) f

  -- fst : (A * B) → A
  inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) with inferElab ctx arg
  ... | failure err = failure err
  ... | success (A Once.Type.* B) Ψ argE d f =
        success A _ (Surface.app (weakenFromEmpty (specFst A B)) argE) (suc d) f
  ... | success _ _ _ _ _ = failure "fst requires a pair argument"

  -- snd : (A * B) → B
  inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) with inferElab ctx arg
  ... | failure err = failure err
  ... | success (A Once.Type.* B) Ψ argE d f =
        success B _ (Surface.app (weakenFromEmpty (specSnd A B)) argE) (suc d) f
  ... | success _ _ _ _ _ = failure "snd requires a pair argument"

  -- terminal : A → Unit
  inferElab ctx (Raw.RApp (Raw.RVar "terminal") arg) with inferElab ctx arg
  ... | failure err = failure err
  ... | success A Ψ argE d f =
        success Unit _ (Surface.app (weakenFromEmpty (specTerminal A)) argE) (suc d) f

  -- Partial / check-only builtins in infer mode: fail.
  inferElab ctx (Raw.RApp (Raw.RVar "inl") _) =
    failure "inl requires check mode (needs target sum type)"
  inferElab ctx (Raw.RApp (Raw.RVar "inr") _) =
    failure "inr requires check mode (needs target sum type)"
  inferElab ctx (Raw.RApp (Raw.RVar "initial") _) =
    failure "initial requires check mode (needs target type)"

  -- Generic application: infer f as function type, then x
  inferElab ctx (Raw.RApp f x) with asFun (inferElab ctx f)
  ... | notFun err = failure err
  ... | isFun A q B Ψ₁ fE df ff with inferElab ctx x
  ...   | failure err = failure err
  ...   | success A' Ψ₂ xE dx fx with A ≟T A'
  ...     | yes refl = success B _ (Surface.app fE xE) (df ⊔ dx) fx
  ...     | no _ = failure ("Application: argument type " ++ showType A' ++
                            " does not match function domain " ++ showType A)

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
  ...       | no _ = failure "Case branches have different types"
  inferElab ctx (Raw.RDestruct _ _ _ _ _) | success _ _ _ _ _ = failure "Case requires a sum-typed scrutinee"

  -- Binary operators
  inferElab ctx (Raw.RBinOp op e₁ e₂) with asInt (inferElab ctx e₁)
  ... | notInt err = failure ("binop left: " ++ err)
  ... | isInt Ψ₁ e₁E d₁ f₁ with asInt (inferElab ctx e₂)
  ...   | notInt err = failure ("binop right: " ++ err)
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
  ... | success _ _ _ _ _ = failure "Negation requires Int operand"

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
  ...   | nothing = failure ("Parameter '" ++ x ++ "' used with quantity " ++ showQuantity q' ++
                              " but declared with quantity " ++ showQuantity q)
  checkElab ctx (Raw.RLam _ _) _ = failure "Lambda requires function type"

  -- inl in check mode: expected sum type
  checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) (A Once.Type.+ B) with checkElab ctx arg A
  ... | failure err = failure err
  ... | success Ψ argE d f =
        success _ (Surface.app (weakenFromEmpty (specInl A B)) argE) (suc d) f
  checkElab ctx (Raw.RApp (Raw.RVar "inl") _) _ = failure "inl expects a sum type in check mode"

  -- inr in check mode
  checkElab ctx (Raw.RApp (Raw.RVar "inr") arg) (A Once.Type.+ B) with checkElab ctx arg B
  ... | failure err = failure err
  ... | success Ψ argE d f =
        success _ (Surface.app (weakenFromEmpty (specInr A B)) argE) (suc d) f
  checkElab ctx (Raw.RApp (Raw.RVar "inr") _) _ = failure "inr expects a sum type in check mode"

  -- initial in check mode: Void → A
  checkElab ctx (Raw.RApp (Raw.RVar "initial") arg) T with checkElab ctx arg Void
  ... | failure err = failure err
  ... | success Ψ argE d f =
        success _ (Surface.app (weakenFromEmpty (specInitial T)) argE) (suc d) f

  -- Bare polymorphic builtins in check mode: specialize against expected type.

  checkElab ctx (Raw.RVar "id") (A ⇒[ Many ] B) with A ≟T B
  ... | yes refl = success _ (weakenFromEmpty (specId A)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure "id: expected type A → A (domain must equal codomain)"

  checkElab ctx (Raw.RVar "fst") ((A Once.Type.* B) ⇒[ Many ] A') with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specFst A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure "fst: expected type (A * B) → A"

  checkElab ctx (Raw.RVar "snd") ((A Once.Type.* B) ⇒[ Many ] B') with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specSnd A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure "snd: expected type (A * B) → B"

  checkElab ctx (Raw.RVar "inl") (A ⇒[ Many ] (A' Once.Type.+ B)) with A ≟T A'
  ... | yes refl = success _ (weakenFromEmpty (specInl A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure "inl: expected type A → (A + B)"

  checkElab ctx (Raw.RVar "inr") (B ⇒[ Many ] (A Once.Type.+ B')) with B ≟T B'
  ... | yes refl = success _ (weakenFromEmpty (specInr A B)) 0 (NamedCtx.freshCounter ctx)
  ... | no _ = failure "inr: expected type B → (A + B)"

  checkElab ctx (Raw.RVar "terminal") (A ⇒[ Many ] Unit) =
    success _ (weakenFromEmpty (specTerminal A)) 0 (NamedCtx.freshCounter ctx)

  checkElab ctx (Raw.RVar "initial") (Void ⇒[ Many ] A) =
    success _ (weakenFromEmpty (specInitial A)) 0 (NamedCtx.freshCounter ctx)

  checkElab ctx (Raw.RVar "arr") ((A ⇒[ Many ] B) ⇒[ Many ] (Eff A' B')) with A ≟T A' | B ≟T B'
  ... | yes refl | yes refl = success _ (weakenFromEmpty (specArr A B)) 0 (NamedCtx.freshCounter ctx)
  ... | _ | _ = failure "arr: expected type (A → B) → Eff A B"

  checkElab ctx (Raw.RVar "apply") (((A ⇒[ Many ] B) Once.Type.* A') ⇒[ Many ] B') with A ≟T A' | B ≟T B'
  ... | yes refl | yes refl = success _ (weakenFromEmpty (specApply A B)) 0 (NamedCtx.freshCounter ctx)
  ... | _ | _ = failure "apply: expected type ((A → B) * A) → B"

  checkElab ctx (Raw.RVar "compose") ((B ⇒[ Many ] C) ⇒[ Many ] ((A ⇒[ Many ] B') ⇒[ Many ] (A' ⇒[ Many ] C'))) with B ≟T B' | A ≟T A' | C ≟T C'
  ... | yes refl | yes refl | yes refl = success _ (weakenFromEmpty (specCompose A B C)) 0 (NamedCtx.freshCounter ctx)
  ... | _ | _ | _ = failure "compose: expected type (B → C) → (A → B) → A → C"

  checkElab ctx (Raw.RVar "pair") ((A ⇒[ Many ] B) ⇒[ Many ] ((A' ⇒[ Many ] C) ⇒[ Many ] (A'' ⇒[ Many ] (B' Once.Type.* C')))) with A ≟T A' | A ≟T A'' | B ≟T B' | C ≟T C'
  ... | yes refl | yes refl | yes refl | yes refl = success _ (weakenFromEmpty (specPair A B C)) 0 (NamedCtx.freshCounter ctx)
  ... | _ | _ | _ | _ = failure "pair (fork): expected type (A → B) → (A → C) → A → (B * C)"

  checkElab ctx (Raw.RVar "curry") (((A Once.Type.* B) ⇒[ Many ] C) ⇒[ Many ] (A' ⇒[ Many ] (B' ⇒[ Many ] C'))) with A ≟T A' | B ≟T B' | C ≟T C'
  ... | yes refl | yes refl | yes refl = success _ (weakenFromEmpty (specCurry A B C)) 0 (NamedCtx.freshCounter ctx)
  ... | _ | _ | _ = failure "curry: expected type ((A * B) → C) → A → B → C"

  -- Generic fallback: infer and match types
  checkElab ctx e T with inferElab ctx e
  ... | failure err = failure err
  ... | success T' Ψ eE d f with T ≟T T'
  ...   | yes refl = success _ eE d f
  ...   | no _ = failure ("Type mismatch: expected " ++ showType T ++ " but got " ++ showType T')

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
