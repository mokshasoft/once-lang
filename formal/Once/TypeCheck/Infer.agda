------------------------------------------------------------------------
-- Once.TypeCheck.Infer
--
-- Bidirectional type inference algorithm.
-- Infers types for raw expressions, producing typed evidence.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Infer where

open import Data.String using (String; _≟_)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒_; Eff; Fix; TVar)
open import Once.TypeCheck.Raw using (RawExpr; BinOp; UnaryOp; isComparisonOp)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; lookup; LookupResult; found; notFound; Quantity; Omega)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.TypeCheck.Error using (TypeError; UnboundVariable; TypeMismatch; NotAFunction;
                                         ArithNonInteger; CompareNonInteger)
open import Once.TypeCheck.Unify using (Subst; emptySubst; applySubst; composeSubst; unify; UnifyResult; unified; failed)

------------------------------------------------------------------------
-- Fresh Type Variables
------------------------------------------------------------------------

-- | Fresh variable counter
Fresh : Set
Fresh = ℕ

-- | Generate a fresh type variable
freshTVar : Fresh → Type × Fresh
freshTVar n = (TVar (Data.String.concat ("t" ∷ Data.Nat.Show.show n ∷ [])) , suc n)
  where
  import Data.Nat.Show
  import Data.String

------------------------------------------------------------------------
-- Generator Types
------------------------------------------------------------------------

-- | Built-in generator types (categorical combinators)
generatorType : String → Fresh → Maybe (Type × Fresh)
generatorType "id" f =
  let (α , f') = freshTVar f
  in just (α ⇒ α , f')

generatorType "fst" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
  in just ((α * β) ⇒ α , f₂)

generatorType "snd" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
  in just ((α * β) ⇒ β , f₂)

generatorType "pair" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
      (γ , f₃) = freshTVar f₂
  in just ((γ ⇒ α) ⇒ (γ ⇒ β) ⇒ γ ⇒ (α * β) , f₃)

generatorType "inl" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
  in just (α ⇒ (α + β) , f₂)

generatorType "inr" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
  in just (β ⇒ (α + β) , f₂)

generatorType "terminal" f =
  let (α , f') = freshTVar f
  in just (α ⇒ Unit , f')

generatorType "initial" f =
  let (α , f') = freshTVar f
  in just (Void ⇒ α , f')

generatorType "curry" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
      (γ , f₃) = freshTVar f₂
  in just (((α * β) ⇒ γ) ⇒ α ⇒ (β ⇒ γ) , f₃)

generatorType "apply" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
  in just (((α ⇒ β) * α) ⇒ β , f₂)

generatorType "pure" f =
  let (α , f') = freshTVar f
  in just (α ⇒ Eff Unit α , f')

generatorType "arr" f =
  let (α , f₁) = freshTVar f
      (β , f₂) = freshTVar f₁
  in just ((α ⇒ β) ⇒ Eff α β , f₂)

generatorType "fold" f =
  let (φ , f') = freshTVar f
  in just (φ ⇒ Fix φ , f')

generatorType "unfold" f =
  let (φ , f') = freshTVar f
  in just (Fix φ ⇒ φ , f')

generatorType _ _ = nothing

------------------------------------------------------------------------
-- Inference Result
------------------------------------------------------------------------

-- | Result of type inference
data InferResult : Set where
  success : Type → Subst → Fresh → InferResult
  failure : TypeError → InferResult

------------------------------------------------------------------------
-- Type Inference
------------------------------------------------------------------------

-- | Main type inference function
{-# TERMINATING #-}
infer : Ctx → RawExpr → Fresh → InferResult

-- Variable lookup
infer Γ (Raw.RVar x) f with lookup x Γ
... | found A _ _ = success A emptySubst f
... | notFound with generatorType x f
...   | just (T , f') = success T emptySubst f'
...   | nothing = failure (UnboundVariable x)

-- Application
infer Γ (Raw.RApp fun arg) f with infer Γ fun f
... | failure err = failure err
... | success funTy σ₁ f₁ with infer Γ arg f₁
...   | failure err = failure err
...   | success argTy σ₂ f₂ with freshTVar f₂
...     | (retTy , f₃) with unify (applySubst σ₂ funTy) (argTy ⇒ retTy)
...       | unified σ₃ = success (applySubst σ₃ retTy)
                                 (composeSubst σ₃ (composeSubst σ₂ σ₁)) f₃
...       | failed err = failure err

-- Lambda abstraction
infer Γ (Raw.RLam x body) f with freshTVar f
... | (argTy , f₁) with infer (extendCtx Γ x argTy) body f₁
...   | success bodyTy σ f₂ = success (applySubst σ argTy ⇒ bodyTy) σ f₂
...   | failure err = failure err

-- Let binding
infer Γ (Raw.RLet x e₁ e₂) f with infer Γ e₁ f
... | failure err = failure err
... | success ty₁ σ₁ f₁ with infer (extendCtx Γ x (applySubst σ₁ ty₁)) e₂ f₁
...   | success ty₂ σ₂ f₂ = success ty₂ (composeSubst σ₂ σ₁) f₂
...   | failure err = failure err

-- Pair introduction
infer Γ (Raw.RPair a b) f with infer Γ a f
... | failure err = failure err
... | success tyA σ₁ f₁ with infer Γ b f₁
...   | failure err = failure err
...   | success tyB σ₂ f₂ = success (applySubst σ₂ tyA * tyB) (composeSubst σ₂ σ₁) f₂

-- Case analysis
infer Γ (Raw.RCase scrut xL eL xR eR) f with infer Γ scrut f
... | failure err = failure err
... | success scrutTy σ₁ f₁ with freshTVar f₁
...   | (tyL , f₂) with freshTVar f₂
...     | (tyR , f₃) with unify scrutTy (tyL + tyR)
...       | failed err = failure err
...       | unified σ₂ with infer (extendCtx Γ xL (applySubst σ₂ tyL)) eL f₃
...         | failure err = failure err
...         | success tyBodyL σ₃ f₄ with infer (extendCtx Γ xR (applySubst σ₂ tyR)) eR f₄
...           | failure err = failure err
...           | success tyBodyR σ₄ f₅ with unify (applySubst σ₄ tyBodyL) tyBodyR
...             | failed err = failure err
...             | unified σ₅ = success (applySubst σ₅ tyBodyR)
                                       (composeSubst σ₅ (composeSubst σ₄
                                         (composeSubst σ₃ (composeSubst σ₂ σ₁))))
                                       f₅

-- Unit
infer Γ Raw.RUnit f = success Unit emptySubst f

-- Integer literal
infer Γ (Raw.RInt _) f = success Int emptySubst f

-- String literal
infer Γ (Raw.RStringLit _) f = success Str emptySubst f

-- Type annotation
infer Γ (Raw.RAnnot e T) f with infer Γ e f
... | failure err = failure err
... | success inferredTy σ f' with unify (applySubst σ T) inferredTy
...   | unified σ' = success (applySubst σ' inferredTy) (composeSubst σ' σ) f'
...   | failed err = failure err

-- Binary operators (OCP-0002)
infer Γ (Raw.RBinOp op a b) f with infer Γ a f
... | failure err = failure err
... | success tyA σ₁ f₁ with infer Γ b f₁
...   | failure err = failure err
...   | success tyB σ₂ f₂ with unify (applySubst σ₂ tyA) Int
...     | failed _ = failure (ArithNonInteger (applySubst σ₂ tyA))
...     | unified σ₃ with unify (applySubst σ₃ tyB) Int
...       | failed _ = failure (ArithNonInteger (applySubst σ₃ tyB))
...       | unified σ₄ =
            let finalSubst = composeSubst σ₄ (composeSubst σ₃ (composeSubst σ₂ σ₁))
                resultTy = if isComparisonOp op then (Unit + Unit) else Int
            in success resultTy finalSubst f₂

-- Unary operators (OCP-0002)
infer Γ (Raw.RUnaryOp Raw.OpNeg e) f with infer Γ e f
... | failure err = failure err
... | success tyE σ f' with unify tyE Int
...   | failed _ = failure (ArithNonInteger tyE)
...   | unified σ' = success Int (composeSubst σ' σ) f'

------------------------------------------------------------------------
-- Top-level Type Check
------------------------------------------------------------------------

-- | Check an expression against an expected type
check : Ctx → RawExpr → Type → Fresh → InferResult
check Γ e expected f with infer Γ e f
... | failure err = failure err
... | success inferred σ f' with unify (applySubst σ expected) inferred
...   | unified σ' = success (applySubst σ' inferred) (composeSubst σ' σ) f'
...   | failed err = failure err
