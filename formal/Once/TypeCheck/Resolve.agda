------------------------------------------------------------------------
-- Once.TypeCheck.Resolve
--
-- Scope resolution: converts named variables to de Bruijn indices.
-- Bridges between extrinsic typing (named contexts) and intrinsic
-- typing (de Bruijn indexed expressions).
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Resolve where

open import Data.String using (String; _≟_)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_; _⇒_; Eff; Fix; TVar; Quantity; Zero; One; Many; _≤q_)
open import Once.TypeCheck.Raw using (RawExpr; BinOp; UnaryOp; isComparisonOp)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; Binding; mkBinding; name; type)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.TypeCheck.Error using (TypeError; UnboundVariable)

-- Import intrinsically-typed surface syntax
open import Once.Surface.Syntax as Surface using () renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_)

------------------------------------------------------------------------
-- Resolution Context
------------------------------------------------------------------------

-- | Evidence that a named context corresponds to a de Bruijn context
--
-- CtxMatch Γ n Δ means:
-- - Γ is a named context (from TypeCheck.Context)
-- - n is the size (number of bindings)
-- - Δ is the corresponding de Bruijn context (from Surface.Syntax)
data CtxMatch : Ctx → (n : ℕ) → SCtx n → Set where
  match-empty : CtxMatch ∅ 0 S∅

  match-extend : ∀ {Γ n Δ x A q}
               → CtxMatch Γ n Δ
               → CtxMatch (mkBinding x A q ∷ Γ) (suc n) (Δ S, A)

------------------------------------------------------------------------
-- Index Lookup (Simplified)
------------------------------------------------------------------------

-- | Look up a variable name and return its index and type
lookupNamedIdx : String → Ctx → Maybe (ℕ × Type)
lookupNamedIdx x [] = nothing
lookupNamedIdx x (b ∷ Γ) with x ≟ name b
... | yes _ = just (0 , type b)
... | no  _ with lookupNamedIdx x Γ
...   | just (i , A) = just (suc i , A)
...   | nothing = nothing

-- | Convert ℕ index to Fin (if in bounds)
natToFin : (i : ℕ) → (n : ℕ) → Maybe (Fin n)
natToFin _ zero = nothing
natToFin zero (suc n) = just zero
natToFin (suc i) (suc n) with natToFin i n
... | just f  = just (suc f)
... | nothing = nothing

------------------------------------------------------------------------
-- Type Equality (Decidable)
------------------------------------------------------------------------

-- | Check if two types are equal
_≟T_ : Type → Type → Bool
Unit ≟T Unit = true
Void ≟T Void = true
Int ≟T Int = true
Float ≟T Float = true
Str ≟T Str = true
Buffer ≟T Buffer = true
(A₁ * B₁) ≟T (A₂ * B₂) = (A₁ ≟T A₂) ∧ (B₁ ≟T B₂)
(A₁ + B₁) ≟T (A₂ + B₂) = (A₁ ≟T A₂) ∧ (B₁ ≟T B₂)
(A₁ ⇒[ q₁ ] B₁) ≟T (A₂ ⇒[ q₂ ] B₂) = (q₁ ≤q q₂) ∧ (q₂ ≤q q₁) ∧ (A₁ ≟T A₂) ∧ (B₁ ≟T B₂)
(Eff A₁ B₁) ≟T (Eff A₂ B₂) = (A₁ ≟T A₂) ∧ (B₁ ≟T B₂)
(Fix F₁) ≟T (Fix F₂) = F₁ ≟T F₂
(TVar x) ≟T (TVar y) with x ≟ y
... | yes _ = true
... | no _  = false
_ ≟T _ = false

------------------------------------------------------------------------
-- Scope Resolution
------------------------------------------------------------------------

-- | Resolve a raw expression to an intrinsically-typed expression
--
-- Note: This is a simplified resolution that requires the type to be
-- already known (from inference). A full elaboration would combine
-- type inference with scope resolution.
--
-- The resolution converts named variables to de Bruijn indices
-- using the correspondence between named and indexed contexts.
--
-- Some cases are postulated because:
-- 1. Full proof requires showing context correspondence is preserved
-- 2. Surface.Syntax lacks some constructors (literals, binary ops)

{-# TERMINATING #-}
resolve : ∀ {n} (Γ : Ctx) (Δ : SCtx n)
        → CtxMatch Γ n Δ
        → (e : RawExpr)
        → (A : Type)
        → Maybe (SExpr Δ A)

-- Variable resolution
resolve {n} Γ Δ match (Raw.RVar x) A with lookupNamedIdx x Γ
... | nothing = nothing
... | just (i , A') with natToFin i n | A ≟T A'
...   | nothing | _ = nothing
...   | just fin | false = nothing
...   | just fin | true = postulate-var Γ Δ match x A fin
  where
  -- The actual construction requires proving lookup Δ fin ≡ A
  postulate postulate-var : ∀ {n} (Γ : Ctx) (Δ : SCtx n)
                          → CtxMatch Γ n Δ → String → (A : Type) → Fin n
                          → Maybe (SExpr Δ A)

-- Lambda resolution (only supports unrestricted/Many quantity for now)
resolve Γ Δ match (Raw.RLam x body) (A ⇒[ Many ] B) with resolve (extendCtx Γ x A) (Δ S, A) (match-extend match) body B
... | just se = just (Surface.lam se)
... | nothing = nothing
resolve _ _ _ (Raw.RLam _ _) _ = nothing

-- Application resolution
resolve Γ Δ match (Raw.RApp e₁ e₂) B = postulate-app Γ Δ match e₁ e₂ B
  where
  postulate postulate-app : ∀ {n} (Γ : Ctx) (Δ : SCtx n)
                          → CtxMatch Γ n Δ → RawExpr → RawExpr → Type
                          → Maybe (SExpr Δ B)

-- Pair resolution
resolve Γ Δ match (Raw.RPair e₁ e₂) (A * B) with resolve Γ Δ match e₁ A
... | nothing = nothing
... | just se₁ with resolve Γ Δ match e₂ B
...   | nothing = nothing
...   | just se₂ = just (Surface.pair se₁ se₂)
resolve _ _ _ (Raw.RPair _ _) _ = nothing

-- Unit resolution
resolve _ Δ _ Raw.RUnit Unit = just Surface.unit
resolve _ _ _ Raw.RUnit _ = nothing

-- Let binding
resolve Γ Δ match (Raw.RLet x e₁ e₂) B = postulate-let Γ Δ match x e₁ e₂ B
  where
  postulate postulate-let : ∀ {n} (Γ : Ctx) (Δ : SCtx n)
                          → CtxMatch Γ n Δ → String → RawExpr → RawExpr → Type
                          → Maybe (SExpr Δ B)

-- Case analysis
resolve Γ Δ match (Raw.RCase scrut xL eL xR eR) C = postulate-case Γ Δ match scrut xL eL xR eR C
  where
  postulate postulate-case : ∀ {n} (Γ : Ctx) (Δ : SCtx n)
                           → CtxMatch Γ n Δ → RawExpr → String → RawExpr → String → RawExpr → Type
                           → Maybe (SExpr Δ C)

-- Integer literals: Surface.Syntax lacks Int constructor
resolve _ _ _ (Raw.RInt _) _ = nothing

-- String literals: Surface.Syntax lacks String constructor
resolve _ _ _ (Raw.RStringLit _) _ = nothing

-- Type annotation: resolve the inner expression
resolve Γ Δ match (Raw.RAnnot e _) A = resolve Γ Δ match e A

-- Binary operators: Surface.Syntax lacks BinOp constructor
resolve _ _ _ (Raw.RBinOp _ _ _) _ = nothing

-- Unary operators: Surface.Syntax lacks UnaryOp constructor
resolve _ _ _ (Raw.RUnaryOp _ _) _ = nothing

------------------------------------------------------------------------
-- Resolution from Empty Context
------------------------------------------------------------------------

-- | Resolve a closed expression
resolveClosed : (e : RawExpr) → (A : Type) → Maybe (SExpr S∅ A)
resolveClosed e A = resolve ∅ S∅ match-empty e A

------------------------------------------------------------------------
-- Resolution Correctness
------------------------------------------------------------------------

-- | Resolution produces well-typed terms by construction
--
-- The SExpr type is intrinsically typed, so any term we construct
-- is guaranteed to be well-typed. The resolution either succeeds
-- with a well-typed term or fails with nothing.

resolve-well-typed : ∀ {n} {Γ : Ctx} {Δ : SCtx n} {match : CtxMatch Γ n Δ}
                     {e : RawExpr} {A : Type} {se : SExpr Δ A}
                   → resolve Γ Δ match e A ≡ just se
                   → SExpr Δ A
resolve-well-typed {se = se} _ = se

