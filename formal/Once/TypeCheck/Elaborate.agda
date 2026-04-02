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
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; _⊔_)
open import Data.Nat as Nat
open import Data.Nat.Properties using (≤-refl; n<1+n; +-identityʳ; +-suc; +-comm)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin as Fin using (_↑ˡ_)
open import Data.Vec using (Vec; []; _∷_; tail) renaming (lookup to Vec-lookup)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym)
open import Induction.WellFounded using (Acc; acc; WfRec)
open import Data.Nat.Induction using (<-wellFounded)

open import Once.Type
open Once.Type using (showQuantity) public
open import Once.CCC.IR as IR
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; Binding; mkBinding; name; type)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using (lookup; lookupQuantity; lookupUsage; tailUsage; _≤ᵘ?_)
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open import Once.Surface.Thinning
  using (weaken; exchange; exchange₂; exchange₃; exchange₄; exchange₅; exchange₆; exchange₇; exchange₈)
open import Once.Surface.Elaborate as Elab using (elaborate; ⟦_⟧ᶜ)
open import Once.Postulates using (coerceQuantity)

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
weakenFromEmpty {Γ = Γ S, B ^ Many} e = weaken {A = B} {q = Many} (weakenFromEmpty {Γ = Γ} e)
-- For non-Many quantities, coerce (Step 2: infrastructure only, actual tracking in Step 3)
weakenFromEmpty {Γ = Γ S, B ^ q} e = coerceQuantity (weaken {A = B} {q = q} (weakenFromEmpty {Γ = Γ} e))

------------------------------------------------------------------------
-- Type Equality (Decidable with proof)
------------------------------------------------------------------------

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
(Fix F₁) ≟T (Fix F₂) with F₁ ≟T F₂
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
(TVar x) ≟T (TVar y) with Data.String._≟_ x y
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
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
Unit ≟T Fix _ = no λ ()
Unit ≟T TVar _ = no λ ()
Void ≟T Unit = no λ ()
Void ≟T Int = no λ ()
Void ≟T Float = no λ ()
Void ≟T Str = no λ ()
Void ≟T Buffer = no λ ()
Void ≟T (_ Once.Type.* _) = no λ ()
Void ≟T (_ Once.Type.+ _) = no λ ()
Void ≟T (_ ⇒[ _ ] _) = no λ ()
Void ≟T Eff _ _ = no λ ()
Void ≟T Fix _ = no λ ()
Void ≟T TVar _ = no λ ()
Int ≟T Unit = no λ ()
Int ≟T Void = no λ ()
Int ≟T Float = no λ ()
Int ≟T Str = no λ ()
Int ≟T Buffer = no λ ()
Int ≟T (_ Once.Type.* _) = no λ ()
Int ≟T (_ Once.Type.+ _) = no λ ()
Int ≟T (_ ⇒[ _ ] _) = no λ ()
Int ≟T Eff _ _ = no λ ()
Int ≟T Fix _ = no λ ()
Int ≟T TVar _ = no λ ()
Float ≟T Unit = no λ ()
Float ≟T Void = no λ ()
Float ≟T Int = no λ ()
Float ≟T Str = no λ ()
Float ≟T Buffer = no λ ()
Float ≟T (_ Once.Type.* _) = no λ ()
Float ≟T (_ Once.Type.+ _) = no λ ()
Float ≟T (_ ⇒[ _ ] _) = no λ ()
Float ≟T Eff _ _ = no λ ()
Float ≟T Fix _ = no λ ()
Float ≟T TVar _ = no λ ()
Str ≟T Unit = no λ ()
Str ≟T Void = no λ ()
Str ≟T Int = no λ ()
Str ≟T Float = no λ ()
Str ≟T Buffer = no λ ()
Str ≟T (_ Once.Type.* _) = no λ ()
Str ≟T (_ Once.Type.+ _) = no λ ()
Str ≟T (_ ⇒[ _ ] _) = no λ ()
Str ≟T Eff _ _ = no λ ()
Str ≟T Fix _ = no λ ()
Str ≟T TVar _ = no λ ()
Buffer ≟T Unit = no λ ()
Buffer ≟T Void = no λ ()
Buffer ≟T Int = no λ ()
Buffer ≟T Float = no λ ()
Buffer ≟T Str = no λ ()
Buffer ≟T (_ Once.Type.* _) = no λ ()
Buffer ≟T (_ Once.Type.+ _) = no λ ()
Buffer ≟T (_ ⇒[ _ ] _) = no λ ()
Buffer ≟T Eff _ _ = no λ ()
Buffer ≟T Fix _ = no λ ()
Buffer ≟T TVar _ = no λ ()
(_ Once.Type.* _) ≟T Unit = no λ ()
(_ Once.Type.* _) ≟T Void = no λ ()
(_ Once.Type.* _) ≟T Int = no λ ()
(_ Once.Type.* _) ≟T Float = no λ ()
(_ Once.Type.* _) ≟T Str = no λ ()
(_ Once.Type.* _) ≟T Buffer = no λ ()
(_ Once.Type.* _) ≟T (_ Once.Type.+ _) = no λ ()
(_ Once.Type.* _) ≟T (_ ⇒[ _ ] _) = no λ ()
(_ Once.Type.* _) ≟T Eff _ _ = no λ ()
(_ Once.Type.* _) ≟T Fix _ = no λ ()
(_ Once.Type.* _) ≟T TVar _ = no λ ()
(_ Once.Type.+ _) ≟T Unit = no λ ()
(_ Once.Type.+ _) ≟T Void = no λ ()
(_ Once.Type.+ _) ≟T Int = no λ ()
(_ Once.Type.+ _) ≟T Float = no λ ()
(_ Once.Type.+ _) ≟T Str = no λ ()
(_ Once.Type.+ _) ≟T Buffer = no λ ()
(_ Once.Type.+ _) ≟T (_ Once.Type.* _) = no λ ()
(_ Once.Type.+ _) ≟T (_ ⇒[ _ ] _) = no λ ()
(_ Once.Type.+ _) ≟T Eff _ _ = no λ ()
(_ Once.Type.+ _) ≟T Fix _ = no λ ()
(_ Once.Type.+ _) ≟T TVar _ = no λ ()
(_ ⇒[ _ ] _) ≟T Unit = no λ ()
(_ ⇒[ _ ] _) ≟T Void = no λ ()
(_ ⇒[ _ ] _) ≟T Int = no λ ()
(_ ⇒[ _ ] _) ≟T Float = no λ ()
(_ ⇒[ _ ] _) ≟T Str = no λ ()
(_ ⇒[ _ ] _) ≟T Buffer = no λ ()
(_ ⇒[ _ ] _) ≟T (_ Once.Type.* _) = no λ ()
(_ ⇒[ _ ] _) ≟T (_ Once.Type.+ _) = no λ ()
(_ ⇒[ _ ] _) ≟T Eff _ _ = no λ ()
(_ ⇒[ _ ] _) ≟T Fix _ = no λ ()
(_ ⇒[ _ ] _) ≟T TVar _ = no λ ()
Eff _ _ ≟T Unit = no λ ()
Eff _ _ ≟T Void = no λ ()
Eff _ _ ≟T Int = no λ ()
Eff _ _ ≟T Float = no λ ()
Eff _ _ ≟T Str = no λ ()
Eff _ _ ≟T Buffer = no λ ()
Eff _ _ ≟T (_ Once.Type.* _) = no λ ()
Eff _ _ ≟T (_ Once.Type.+ _) = no λ ()
Eff _ _ ≟T (_ ⇒[ _ ] _) = no λ ()
Eff _ _ ≟T Fix _ = no λ ()
Eff _ _ ≟T TVar _ = no λ ()
Fix _ ≟T Unit = no λ ()
Fix _ ≟T Void = no λ ()
Fix _ ≟T Int = no λ ()
Fix _ ≟T Float = no λ ()
Fix _ ≟T Str = no λ ()
Fix _ ≟T Buffer = no λ ()
Fix _ ≟T (_ Once.Type.* _) = no λ ()
Fix _ ≟T (_ Once.Type.+ _) = no λ ()
Fix _ ≟T (_ ⇒[ _ ] _) = no λ ()
Fix _ ≟T Eff _ _ = no λ ()
Fix _ ≟T TVar _ = no λ ()
TVar _ ≟T Unit = no λ ()
TVar _ ≟T Void = no λ ()
TVar _ ≟T Int = no λ ()
TVar _ ≟T Float = no λ ()
TVar _ ≟T Str = no λ ()
TVar _ ≟T Buffer = no λ ()
TVar _ ≟T (_ Once.Type.* _) = no λ ()
TVar _ ≟T (_ Once.Type.+ _) = no λ ()
TVar _ ≟T (_ ⇒[ _ ] _) = no λ ()
TVar _ ≟T Eff _ _ = no λ ()
TVar _ ≟T Fix _ = no λ ()

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
-- Helper: Find de Bruijn index of a variable by name
------------------------------------------------------------------------

-- | Find the de Bruijn index of a variable by name in the named context
-- Returns nothing if the variable is not found (it's a built-in)
findVarIndex : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx))
findVarIndex (mkCtx n Γ Δ fresh imps) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → Maybe (Fin m)
    go [] S∅ = nothing  -- Variable not found in context (must be built-in)
    go [] (_ S, _ ^ _) = nothing  -- Impossible: named empty but debruijn not
    go (_ ∷ _) S∅ = nothing  -- Impossible: named non-empty but debruijn empty
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just zero  -- Found at position 0
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just i  = just (suc i)  -- Found at position suc i

------------------------------------------------------------------------
-- Type Substitution and Instantiation
------------------------------------------------------------------------

-- | Substitution: mapping from type variable names to types
-- For now, we use a simple association list representation
Subst : Set
Subst = List (String × Type)

-- | Empty substitution
emptySubst : Subst
emptySubst = []

-- | Extend substitution with a new binding
extendSubst : Subst → String → Type → Subst
extendSubst σ x A = (x , A) ∷ σ

-- | Look up type variable in substitution
lookupSubst : Subst → String → Maybe Type
lookupSubst [] _ = nothing
lookupSubst ((x , A) ∷ σ) y with x Data.String.≟ y
... | yes _ = just A
... | no  _ = lookupSubst σ y

-- | Apply substitution to a type
applySubst : Subst → Type → Type
applySubst σ Unit = Unit
applySubst σ Void = Void
applySubst σ Int = Int
applySubst σ Float = Float
applySubst σ Str = Str
applySubst σ Buffer = Buffer
applySubst σ (A Once.Type.* B) = applySubst σ A Once.Type.* applySubst σ B
applySubst σ (A Once.Type.+ B) = applySubst σ A Once.Type.+ applySubst σ B
applySubst σ (A ⇒[ q ] B) = applySubst σ A ⇒[ q ] applySubst σ B
applySubst σ (Eff A B) = Eff (applySubst σ A) (applySubst σ B)
applySubst σ (Fix A) = Fix (applySubst σ A)
applySubst σ (TVar x) with lookupSubst σ x
... | just A = A
... | nothing = TVar x  -- Unbound type variable remains

-- | Instantiate a polymorphic type with fresh type variables
-- Collects all distinct TVar names and substitutes them with fresh variables
instantiate : Type → ℕ → Type × ℕ
instantiate ty counter = go ty counter emptySubst
  where
    go : Type → ℕ → Subst → Type × ℕ
    go Unit n σ = Unit , n
    go Void n σ = Void , n
    go Int n σ = Int , n
    go Float n σ = Float , n
    go Str n σ = Str , n
    go Buffer n σ = Buffer , n
    go (A Once.Type.* B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' Once.Type.* B') , n''
    go (A Once.Type.+ B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' Once.Type.+ B') , n''
    go (A ⇒[ q ] B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in (A' ⇒[ q ] B') , n''
    go (Eff A B) n σ =
      let (A' , n') = go A n σ
          (B' , n'') = go B n' σ
      in Eff A' B' , n''
    go (Fix A) n σ =
      let (A' , n') = go A n σ
      in Fix A' , n'
    go (TVar x) n σ with lookupSubst σ x
    ... | just A = A , n  -- Already instantiated
    ... | nothing =
        let fresh = TVar (freshTVar n)
            σ' = extendSubst σ x fresh
        in fresh , suc n

------------------------------------------------------------------------
-- Built-in Categorical Generators
------------------------------------------------------------------------

-- | Built-in categorical generators (implicitly imported)
--
-- These are the fundamental vocabulary of the categorical language:
-- identity, composition, products, coproducts, exponentials, etc.
--
-- They are available in all programs without explicit import.
--
-- Takes a fresh counter and returns instantiated type + expression + new counter
builtinType : String → ℕ → Maybe (∃[ A ] (Surface.Expr S∅ A × ℕ))
builtinType "id" n =
  let a = TVar (freshTVar n)
  in just (a ⇒ a , Surface.lam Many (Surface.var zero) , suc n)
builtinType "fst" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a Once.Type.* b) ⇒ a , Surface.lam Many (Surface.fst' (Surface.var zero)) , suc (suc n))
builtinType "snd" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a Once.Type.* b) ⇒ b , Surface.lam Many (Surface.snd' (Surface.var zero)) , suc (suc n))
builtinType "inl" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (a ⇒ (a Once.Type.+ b) , Surface.lam Many (Surface.inl' (Surface.var zero)) , suc (suc n))
builtinType "inr" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (b ⇒ (a Once.Type.+ b) , Surface.lam Many (Surface.inr' (Surface.var zero)) , suc (suc n))
builtinType "unit" n = just (Unit , Surface.unit , n)
-- pair (fork/⟨_,_⟩): (A -> B) -> (A -> C) -> A -> (B * C)
-- pair = λf. λg. λx. (f x, g x)
builtinType "pair" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((a ⇒ b) ⇒ (a ⇒ c) ⇒ a ⇒ (b Once.Type.* c) ,
          Surface.lam Many (Surface.lam Many (Surface.lam Many
            (Surface.pair
              (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero))
              (Surface.app (Surface.var (suc zero)) (Surface.var zero))))) ,
          suc (suc (suc n)))
-- terminal: α → Unit
-- terminal = λx. unit
builtinType "terminal" n =
  let a = TVar (freshTVar n)
  in just (a ⇒ Unit , Surface.lam Many Surface.unit , suc n)
-- initial: Void → α
-- initial = λx. absurd x
builtinType "initial" n =
  let a = TVar (freshTVar n)
  in just (Void ⇒ a , Surface.lam Many (Surface.absurd (Surface.var zero)) , suc n)
-- curry: ((α * β) → γ) → α → β → γ
-- curry = λf. λx. λy. f (x, y)
builtinType "curry" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just (((a Once.Type.* b) ⇒ c) ⇒ a ⇒ b ⇒ c ,
          Surface.lam Many (Surface.lam Many (Surface.lam Many
            (Surface.app (Surface.var (suc (suc zero)))
                        (Surface.pair (Surface.var (suc zero)) (Surface.var zero))))) ,
          suc (suc (suc n)))
-- apply: ((α → β) * α) → β
-- apply = λp. (fst p) (snd p)
builtinType "apply" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just (((a ⇒ b) Once.Type.* a) ⇒ b ,
          Surface.lam Many
            (Surface.app (Surface.fst' (Surface.var zero))
                        (Surface.snd' (Surface.var zero))) ,
          suc (suc n))
-- compose: (β → γ) → (α → β) → α → γ
-- compose = λf. λg. λx. f (g x)
builtinType "compose" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c ,
          Surface.lam Many (Surface.lam Many (Surface.lam Many
            (Surface.app (Surface.var (suc (suc zero)))
                        (Surface.app (Surface.var (suc zero)) (Surface.var zero))))) ,
          suc (suc (suc n)))
-- arr: (α → β) → Eff α β
-- arr = λf. arr' f (where arr' is the Surface constructor)
builtinType "arr" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
  in just ((a ⇒ b) ⇒ Eff a b ,
          Surface.lam Many (Surface.arr' (Surface.var zero)) ,
          suc (suc n))
-- fold: F → Fix F
-- fold = λx. roll' x (where roll' is the Surface constructor)
builtinType "fold" n =
  let f = TVar (freshTVar n)
  in just (f ⇒ Fix f ,
          Surface.lam Many (Surface.roll' (Surface.var zero)) ,
          suc n)
-- unfold: Fix F → F
-- unfold = λx. unroll' x (where unroll' is the Surface constructor)
builtinType "unfold" n =
  let f = TVar (freshTVar n)
  in just (Fix f ⇒ f ,
          Surface.lam Many (Surface.unroll' (Surface.var zero)) ,
          suc n)
-- case: (A → C) → (B → C) → (A + B) → C
-- case = λf. λg. λx. case' x (f a) (g b)
-- This is the copairing (coproduct eliminator) as a curried function.
-- In the body, f is at index 3, g at index 2, x at index 0 in the lambda context.
-- Inside case' branches, the bound variable is at index 0, so:
--   - left branch (context extended with a:A): f is at 3, a is at 0
--   - right branch (context extended with b:B): g is at 2, b is at 0
builtinType "case" n =
  let a = TVar (freshTVar n)
      b = TVar (freshTVar (suc n))
      c = TVar (freshTVar (suc (suc n)))
  in just ((a ⇒ c) ⇒ (b ⇒ c) ⇒ (a Once.Type.+ b) ⇒ c ,
          Surface.lam Many (Surface.lam Many (Surface.lam Many
            (Surface.case' (Surface.var zero)
              (Surface.app (Surface.var (suc (suc (suc zero)))) (Surface.var zero))
              (Surface.app (Surface.var (suc (suc zero))) (Surface.var zero))))) ,
          suc (suc (suc n)))
-- Note: pure is NOT a builtin - it's library code defined as:
--   pure : A → Eff Unit A
--   pure x = arr (λ_ → x)
-- Or equivalently: pure = arr ∘ curry terminal
builtinType _ _ = nothing

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
--
-- For built-in polymorphic functions, instantiates type variables with fresh names.
-- Returns the looked-up type/expr and the updated fresh counter.
--
lookupVar : (ctx : NamedCtx) → String
          → Maybe (∃[ A ] (SExpr (NamedCtx.debruijn ctx) A × ℕ))
lookupVar (mkCtx n Γ Δ fresh imps) x = go Γ Δ fresh
  where
    go : ∀ {m} → Ctx → (Δ' : SCtx m) → ℕ → Maybe (∃[ A ] (SExpr Δ' A × ℕ))
    go [] S∅ freshCtr with builtinType x freshCtr
    ... | just (instTy , se , freshCtr') = just (instTy , weakenFromEmpty se , freshCtr')
    ... | nothing with lookupImport imps x
    ...   | just ty = just (ty , Surface.prim x , freshCtr)  -- Imported primitive
    ...   | nothing = nothing
    go [] (_ S, _ ^ _) _ = nothing  -- impossible case: named context empty but debruijn not
    go (_ ∷ _) S∅ _ = nothing   -- impossible case: named context non-empty but debruijn empty
    go {suc m} (b ∷ Γ') (Δ' S, B ^ Many) freshCtr with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero , freshCtr)  -- Local var: no instantiation needed
    ... | no  _ with go Γ' Δ' freshCtr
    ...   | nothing = nothing
    ...   | just (A , se , freshCtr') = just (A , weaken se , freshCtr')
    go {suc m} (b ∷ Γ') (Δ' S, B ^ q) freshCtr with Data.String._≟_ x (name b)
    ... | yes _ = just (B , Surface.var zero , freshCtr)  -- Local var: no instantiation needed
    ... | no  _ with go Γ' Δ' freshCtr
    ...   | nothing = nothing
    ...   | just (A , se , freshCtr') = just (A , coerceQuantity (weaken {A = B} {q = q} se) , freshCtr')

------------------------------------------------------------------------
-- Bidirectional Type Checking: Inference and Checking Modes
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  -- | Type checking mode: verify expression has expected type
  -- This is the "checking" judgment: Γ ⊢ e ⇐ A
  checkElabImpl : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A

  -- Lambda with function type: check body against result type
  -- QTT: Validate parameter usage respects declared quantity, then drop from usage vector
  checkElabImpl ctx (Raw.RLam x body) (A ⇒[ q ] B) with checkElabImpl (extendNamedCtx ctx x A) body B
  ... | failure err = failure err
  ... | success bodyExpr depth fresh' usage' =
          -- Check parameter usage ≤ declared quantity
          let paramUsage = lookupUsage usage' zero
          in if paramUsage ≤q q
             then success (Surface.lam q bodyExpr) (suc depth) fresh' (tailUsage usage')
             else failure ("Parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                          " but declared with quantity " ++ showQuantity q)

  -- Lambda with non-function type: error
  checkElabImpl ctx (Raw.RLam _ _) ty =
    failure "Lambda requires function type"

  -- Default: fall back to inference and check equality
  checkElabImpl ctx expr expectedType with inferElabImpl ctx expr
  ... | failure err = failure err
  ... | success inferredType expr depth fresh' usage' with inferredType ≟T expectedType
  ...   | yes refl = success expr depth fresh' usage'
  ...   | no _     = failure "Type mismatch in checking mode"

  -- | Type inference mode: compute the type
  -- This is the "inference" judgment: Γ ⊢ e ⇒ A
  inferElabImpl : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)

  -- Variable: look up in context (depth 0 - no nesting)
  -- For local variables, mark as used with their declared quantity
  -- For built-ins, usage is zero (they have no free variables)
  inferElabImpl ctx (Raw.RVar x) with lookupVar ctx x
  ... | nothing = failure ("Unbound variable: " ++ x)
  ... | just (A , se , fresh') with findVarIndex ctx x
  ...   | just i  = -- Local variable: mark as used with declared quantity
                    let q = lookupQuantity (NamedCtx.debruijn ctx) i
                    in success A se 0 fresh' (singleUse i q)
  ...   | nothing = -- Built-in: no usage (weakened from empty context)
                    success A se 0 fresh' zeroUsage

  -- Qualified variable: name@alias (e.g., exit0@S)
  -- Look up using "alias.name" format to find imported functions
  inferElabImpl ctx (Raw.RQualified name alias) with lookupVar ctx (alias ++ "." ++ name)
  ... | nothing = failure ("Unbound qualified variable: " ++ name ++ "@" ++ alias)
  ... | just (A , se , fresh') = success A se 0 fresh' zeroUsage  -- Imported: no local usage

  -- Lambda: infer body with extended context, wrap in lam (depth = body depth + 1)
  -- QTT: Validate parameter usage respects Many (inferred lambdas are unrestricted),
  --      then drop parameter from usage vector
  inferElabImpl ctx (Raw.RLam x body) with inferElabImpl (extendNamedCtx ctx x (TVar "α")) body
  ... | failure err = failure err
  ... | success B bodyExpr bodyDepth fresh' usage' =
        -- Inferred lambdas default to Many quantity (unrestricted)
        let paramUsage = lookupUsage usage' zero
        in if paramUsage ≤q Many
           then success (TVar "α" ⇒ B) (Surface.lam Many bodyExpr) (suc bodyDepth) fresh' (tailUsage usage')
           else failure ("Lambda parameter '" ++ x ++ "' used with quantity " ++ showQuantity paramUsage ++
                        " but inferred lambdas default to " ++ showQuantity Many)

  -- Application: infer function, check it's a function type, infer arg, check types match
  -- (depth = max of function and argument depths, thread fresh counter through)
  -- QTT: Both function and argument contribute to usage, so combine with +ᵘ
  inferElabImpl ctx (Raw.RApp fun arg) = inferApp (inferElabImpl ctx fun)
    where
      inferApp : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferApp (failure err) = failure err
      -- Support all quantities (Zero/One/Many) for function arrows
      inferApp (success (A ⇒[ q ] B) funExpr funDepth funFresh usageFun) = inferArg (inferElabImpl (bumpFreshTo ctx funFresh) arg)
        where
          bumpFreshTo : NamedCtx → ℕ → NamedCtx
          bumpFreshTo (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps

          inferArg : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
          inferArg (failure err) = failure err
          inferArg (success A' argExpr argDepth argFresh usageArg) with A ≟T A'
          ... | yes refl = success B (Surface.app funExpr argExpr) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
          ... | no _ = failure "Type mismatch in application"
      inferApp (success Unit _ _ _ _) = failure "Expected function type in application"
      inferApp (success Void _ _ _ _) = failure "Expected function type in application"
      inferApp (success Int _ _ _ _) = failure "Expected function type in application"
      inferApp (success Float _ _ _ _) = failure "Expected function type in application"
      inferApp (success Str _ _ _ _) = failure "Expected function type in application"
      inferApp (success Buffer _ _ _ _) = failure "Expected function type in application"
      inferApp (success (_ Once.Type.* _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (_ Once.Type.+ _) _ _ _ _) = failure "Expected function type in application"
      -- Eff A B is applicable like A ⇒ B (effectful morphism application)
      inferApp (success (Eff A B) funExpr funDepth funFresh usageFun) = inferArgEff (inferElabImpl (bumpFreshToEff ctx funFresh) arg)
        where
          bumpFreshToEff : NamedCtx → ℕ → NamedCtx
          bumpFreshToEff (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps

          inferArgEff : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
          inferArgEff (failure err) = failure err
          inferArgEff (success A' argExpr argDepth argFresh usageArg) with A ≟T A'
          ... | yes refl = success B (Surface.effApp funExpr argExpr) (funDepth ⊔ argDepth) argFresh (usageFun +ᵘ usageArg)
          ... | no _ = failure "Type mismatch in effect application"
      inferApp (success (Fix _) _ _ _ _) = failure "Expected function type in application"
      inferApp (success (TVar _) _ _ _ _) = failure "Expected function type in application"

  -- Pair (depth = max of both elements, thread fresh counter)
  -- QTT: Both components contribute to usage, so combine with +ᵘ
  inferElabImpl ctx (Raw.RPair a b) with inferElabImpl ctx a
  ... | failure err = failure err
  ... | success A aExpr aDepth aFresh usage1 with inferElabImpl (bumpFresh' ctx aFresh) b
    where
      bumpFresh' : NamedCtx → ℕ → NamedCtx
      bumpFresh' (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps
  ...   | failure err = failure err
  ...   | success B bExpr bDepth bFresh usage2 =
        success (A Once.Type.* B) (Surface.pair aExpr bExpr) (aDepth ⊔ bDepth) bFresh (usage1 +ᵘ usage2)

  -- Unit (depth 0 - no nesting, preserve fresh counter)
  -- Unit doesn't use any variables, so usage is zero
  inferElabImpl ctx Raw.RUnit = success Unit Surface.unit 0 (NamedCtx.freshCounter ctx) zeroUsage

  -- Let binding (depth = max(e₁, e₂ + 1) since e₂ is under binder, thread fresh counter)
  -- QTT: Combine usage from binding and body (drop bound variable from body usage)
  inferElabImpl ctx (Raw.RLet x e₁ e₂) with inferElabImpl ctx e₁
  ... | failure err = failure err
  ... | success A e₁Expr e₁Depth e₁Fresh usage1 with inferElabImpl (extendNamedCtx' ctx x A e₁Fresh) e₂
    where
      extendNamedCtx' : NamedCtx → String → Type → ℕ → NamedCtx
      extendNamedCtx' (mkCtx n Γ Δ _ imps) y B fresh = mkCtx (suc n) (extendCtx Γ y B) (Δ S, B) fresh imps
  ...   | failure err = failure err
  ...   | success B e₂Expr e₂Depth e₂Fresh usage2 =
        success B (Surface.let' e₁Expr e₂Expr) (e₁Depth ⊔ suc e₂Depth) e₂Fresh (usage1 +ᵘ tailUsage usage2)

  -- Case analysis (depth = max(scrut, leftBranch + 1, rightBranch + 1) since branches are under binders)
  -- QTT: Combine usage from scrutinee and both branches (drop bound variables from branches)
  inferElabImpl ctx (Raw.RDestruct scrut xL eL xR eR) = inferCase (inferElabImpl ctx scrut)
    where
      extendCtx' : NamedCtx → String → Type → ℕ → NamedCtx
      extendCtx' (mkCtx n Γ Δ _ imps) y C fresh = mkCtx (suc n) (extendCtx Γ y C) (Δ S, C) fresh imps

      inferCase : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferCase (failure err) = failure err
      inferCase (success (A Once.Type.+ B) scrutExpr scrutDepth scrutFresh usageScr) = inferLeft (inferElabImpl (extendCtx' ctx xL A scrutFresh) eL)
        where
          inferLeft : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xL A))
                    → InferElabResult (NamedCtx.debruijn ctx)
          inferLeft (failure err) = failure err
          inferLeft (success C₁ eLExpr eLDepth eLFresh usageL) = inferRight (inferElabImpl (extendCtx' ctx xR B eLFresh) eR)
            where
              inferRight : InferElabResult (NamedCtx.debruijn (extendNamedCtx ctx xR B))
                         → InferElabResult (NamedCtx.debruijn ctx)
              inferRight (failure err) = failure err
              inferRight (success C₂ eRExpr eRDepth eRFresh usageR) with C₁ ≟T C₂
              ... | yes refl = success C₁ (Surface.case' scrutExpr eLExpr eRExpr)
                                       (scrutDepth ⊔ suc eLDepth ⊔ suc eRDepth) eRFresh
                                       (usageScr +ᵘ tailUsage usageL +ᵘ tailUsage usageR)
              ... | no _ = failure "Case branches have different types"
      inferCase (success Unit _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Void _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Int _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Float _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Str _ _ _ _) = failure "Expected sum type in case"
      inferCase (success Buffer _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (_ Once.Type.* _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (_ ⇒[ _ ] _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (Eff _ _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (Fix _) _ _ _ _) = failure "Expected sum type in case"
      inferCase (success (TVar _) _ _ _ _) = failure "Expected sum type in case"

  -- Integer literal: produce int n
  -- Depth 0 (no nesting), no usage (literals don't use variables)
  inferElabImpl ctx (Raw.RInt n) =
    success Int (Surface.int n) 0 (NamedCtx.freshCounter ctx) zeroUsage

  -- String literal: produce str s
  -- Depth 0 (no nesting), no usage (literals don't use variables)
  inferElabImpl ctx (Raw.RStringLit s) =
    success Str (Surface.str s) 0 (NamedCtx.freshCounter ctx) zeroUsage

  -- Type annotation: just elaborate the inner expression
  inferElabImpl ctx (Raw.RAnnot e _) = inferElabImpl ctx e

  -- Binary operators: infer both operands, check they're Int, produce operator
  -- QTT: Both operands contribute to usage
  inferElabImpl ctx (Raw.RBinOp op e₁ e₂) = inferOp (inferElabImpl ctx e₁)
    where
      bumpFresh' : NamedCtx → ℕ → NamedCtx
      bumpFresh' (mkCtx n Γ Δ _ imps) fresh = mkCtx n Γ Δ fresh imps

      -- Helper to build the result given the inferred operands
      inferOp : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferOp (failure err) = failure err
      inferOp (success Int e₁Expr e₁Depth e₁Fresh usage₁) = inferOp2 (inferElabImpl (bumpFresh' ctx e₁Fresh) e₂)
        where
          inferOp2 : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
          inferOp2 (failure err) = failure err
          inferOp2 (success Int e₂Expr e₂Depth e₂Fresh usage₂) =
            let depth = e₁Depth ⊔ e₂Depth
                usage = usage₁ +ᵘ usage₂
            in if Raw.isArithmeticOp op
               then success Int (mkArithOp op e₁Expr e₂Expr) depth e₂Fresh usage
               else success (Unit Once.Type.+ Unit) (mkCmpOp op e₁Expr e₂Expr) depth e₂Fresh usage
            where
              mkArithOp : Raw.BinOp → Surface.Expr _ Int → Surface.Expr _ Int → Surface.Expr _ Int
              mkArithOp Raw.OpAdd = Surface.add
              mkArithOp Raw.OpSub = Surface.sub
              mkArithOp Raw.OpMul = Surface.mul
              mkArithOp Raw.OpDiv = Surface.div
              mkArithOp Raw.OpMod = Surface.mod'
              mkArithOp _ = Surface.add  -- fallback (shouldn't happen)

              mkCmpOp : Raw.BinOp → Surface.Expr _ Int → Surface.Expr _ Int → Surface.Expr _ (Unit Once.Type.+ Unit)
              mkCmpOp Raw.OpLt = Surface.lt
              mkCmpOp Raw.OpLe = Surface.le
              mkCmpOp Raw.OpGt = Surface.gt
              mkCmpOp Raw.OpGe = Surface.ge
              mkCmpOp Raw.OpEq = Surface.eq
              mkCmpOp Raw.OpNe = Surface.ne
              mkCmpOp _ = Surface.lt  -- fallback (shouldn't happen)
          inferOp2 (success _ _ _ _ _) = failure "Binary operator requires Int operands"
      inferOp (success _ _ _ _ _) = failure "Binary operator requires Int operands"

  -- Unary operators: infer operand, check it's Int, produce negation
  inferElabImpl ctx (Raw.RUnaryOp Raw.OpNeg e) = inferNeg (inferElabImpl ctx e)
    where
      inferNeg : InferElabResult (NamedCtx.debruijn ctx) → InferElabResult (NamedCtx.debruijn ctx)
      inferNeg (failure err) = failure err
      inferNeg (success Int eExpr eDepth eFresh usage) =
        success Int (Surface.neg eExpr) eDepth eFresh usage
      inferNeg (success _ _ _ _ _) = failure "Negation requires Int operand"

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
inferElab : (ctx : NamedCtx) → RawExpr → InferElabResult (NamedCtx.debruijn ctx)
inferElab ctx rawExpr with inferElabImpl ctx rawExpr
... | failure err = failure err
... | success ty expr depth fresh usage with depth ≤? 7
...   | yes _ = success ty expr depth fresh usage
...   | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                       "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                       "  Proven depth limit: 7\n" ++
                       "  Please refactor to reduce nesting of λ/case/let expressions.")

------------------------------------------------------------------------
-- Top-level Compilation
------------------------------------------------------------------------

-- | Checking mode with depth limit (helper for top-level compilation)
checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
checkElab ctx expr ty with checkElabImpl ctx expr ty
... | failure err = failure err
... | success expr' depth fresh usage with depth ≤? 7
...   | yes _ = success expr' depth fresh usage
...   | no _ = failure ("Expression nesting depth exceeds verified limit.\n" ++
                       "  Depth encountered: " ++ showℕ depth ++ "\n" ++
                       "  Proven depth limit: 7\n" ++
                       "  Please refactor to reduce nesting of λ/case/let expressions.")

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