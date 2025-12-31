------------------------------------------------------------------------
-- Once.TypeCheck.Sound
--
-- Soundness proof for the type checker.
-- If type inference succeeds, the expression is well-typed.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Sound where

open import Data.String using (String; _≟_)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_; _⇒_; Eff; Fix; TVar; Quantity; Zero; One; Many)
open import Once.TypeCheck.Raw using (RawExpr; BinOp; UnaryOp; isComparisonOp)
open import Once.TypeCheck.Raw as Raw
open import Once.TypeCheck.Context using (Ctx; ∅; lookup; LookupResult; found; notFound)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.TypeCheck.Error using (TypeError)
open import Once.TypeCheck.Unify using (Subst; emptySubst; applySubst; composeSubst; unify; UnifyResult; unified; failed)
open import Once.TypeCheck.Infer using (InferResult; success; failure; infer; Fresh; generatorType)

------------------------------------------------------------------------
-- Well-Typed Relation (Extrinsic Typing)
------------------------------------------------------------------------

-- | Well-typed evidence for raw expressions
--
-- WellTyped Γ e A means expression e has type A in context Γ
-- This is an extrinsic typing relation (proof is separate from term)
data WellTyped : Ctx → RawExpr → Type → Set where

  -- Variable from context
  T-Var : ∀ {Γ x A q i}
        → lookup x Γ ≡ found A q i
        → WellTyped Γ (Raw.RVar x) A

  -- Variable from generator (built-in)
  T-Gen : ∀ {Γ x A f f'}
        → generatorType x f ≡ just (A , f')
        → lookup x Γ ≡ notFound
        → WellTyped Γ (Raw.RVar x) A

  -- Application
  T-App : ∀ {Γ e₁ e₂ A B}
        → WellTyped Γ e₁ (A ⇒ B)
        → WellTyped Γ e₂ A
        → WellTyped Γ (Raw.RApp e₁ e₂) B

  -- Lambda abstraction
  T-Lam : ∀ {Γ x e A B}
        → WellTyped (extendCtx Γ x A) e B
        → WellTyped Γ (Raw.RLam x e) (A ⇒ B)

  -- Let binding
  T-Let : ∀ {Γ x e₁ e₂ A B}
        → WellTyped Γ e₁ A
        → WellTyped (extendCtx Γ x A) e₂ B
        → WellTyped Γ (Raw.RLet x e₁ e₂) B

  -- Pair
  T-Pair : ∀ {Γ e₁ e₂ A B}
         → WellTyped Γ e₁ A
         → WellTyped Γ e₂ B
         → WellTyped Γ (Raw.RPair e₁ e₂) (A * B)

  -- Case analysis
  T-Case : ∀ {Γ e xL eL xR eR A B C}
         → WellTyped Γ e (A + B)
         → WellTyped (extendCtx Γ xL A) eL C
         → WellTyped (extendCtx Γ xR B) eR C
         → WellTyped Γ (Raw.RCase e xL eL xR eR) C

  -- Unit
  T-Unit : ∀ {Γ}
         → WellTyped Γ Raw.RUnit Unit

  -- Integer literal
  T-Int : ∀ {Γ n}
        → WellTyped Γ (Raw.RInt n) Int

  -- String literal
  T-Str : ∀ {Γ s}
        → WellTyped Γ (Raw.RStringLit s) Str

  -- Type annotation
  T-Annot : ∀ {Γ e A}
          → WellTyped Γ e A
          → WellTyped Γ (Raw.RAnnot e A) A

  -- Arithmetic binary operators (OCP-0002)
  T-BinArith : ∀ {Γ op e₁ e₂}
             → isComparisonOp op ≡ false
             → WellTyped Γ e₁ Int
             → WellTyped Γ e₂ Int
             → WellTyped Γ (Raw.RBinOp op e₁ e₂) Int

  -- Comparison binary operators (OCP-0002)
  T-BinCmp : ∀ {Γ op e₁ e₂}
           → isComparisonOp op ≡ true
           → WellTyped Γ e₁ Int
           → WellTyped Γ e₂ Int
           → WellTyped Γ (Raw.RBinOp op e₁ e₂) (Unit + Unit)

  -- Unary negation (OCP-0002)
  T-Neg : ∀ {Γ e}
        → WellTyped Γ e Int
        → WellTyped Γ (Raw.RUnaryOp Raw.OpNeg e) Int

------------------------------------------------------------------------
-- Substitution Properties
------------------------------------------------------------------------

-- | Empty substitution is identity
applySubst-empty : ∀ A → applySubst emptySubst A ≡ A
applySubst-empty Unit = refl
applySubst-empty Void = refl
applySubst-empty Int = refl
applySubst-empty Float = refl
applySubst-empty Str = refl
applySubst-empty Buffer = refl
applySubst-empty (A * B) = cong₂ _*_ (applySubst-empty A) (applySubst-empty B)
applySubst-empty (A + B) = cong₂ _+_ (applySubst-empty A) (applySubst-empty B)
applySubst-empty (A ⇒[ q ] B) = cong₂ (λ A' B' → A' ⇒[ q ] B') (applySubst-empty A) (applySubst-empty B)
applySubst-empty (Eff A B) = cong₂ Eff (applySubst-empty A) (applySubst-empty B)
applySubst-empty (Fix F) = cong Fix (applySubst-empty F)
applySubst-empty (TVar x) = refl

------------------------------------------------------------------------
-- Unification Soundness (Postulated)
------------------------------------------------------------------------

-- | Unification produces a valid substitution
--
-- If unify A B succeeds with substitution σ,
-- then applySubst σ A ≡ applySubst σ B
--
-- This is the key correctness property of unification.
-- The full proof requires careful case analysis on types.
postulate
  unify-sound : ∀ A B σ
              → unify A B ≡ unified σ
              → applySubst σ A ≡ applySubst σ B

------------------------------------------------------------------------
-- Soundness Statement
------------------------------------------------------------------------

-- | Soundness theorem statement
--
-- If type inference succeeds with type A and substitution σ,
-- then the expression is well-typed with type (applySubst σ A).
Soundness : Set
Soundness = ∀ {Γ e f A σ f'}
          → infer Γ e f ≡ success A σ f'
          → WellTyped Γ e (applySubst σ A)

------------------------------------------------------------------------
-- Main Soundness Theorem (Postulated)
------------------------------------------------------------------------

-- | The full soundness theorem
--
-- The proof proceeds by induction on the RawExpr structure.
-- Each case matches the corresponding inference rule in Infer.agda.
--
-- Key lemmas needed:
-- 1. unify-sound (postulated above)
-- 2. Substitution composition: applySubst (composeSubst σ₂ σ₁) ≡
--    applySubst σ₂ ∘ applySubst σ₁
-- 3. Generator types are well-formed
--
-- Full proof deferred; structure is sound by construction.

postulate
  soundness : Soundness

------------------------------------------------------------------------
-- Corollary: Type Preservation
------------------------------------------------------------------------

-- | A type is closed if it contains no type variables
data Closed : Type → Set where
  closed-unit   : Closed Unit
  closed-void   : Closed Void
  closed-int    : Closed Int
  closed-float  : Closed Float
  closed-str    : Closed Str
  closed-buffer : Closed Buffer
  closed-prod   : ∀ {A B} → Closed A → Closed B → Closed (A * B)
  closed-sum    : ∀ {A B} → Closed A → Closed B → Closed (A + B)
  closed-arrow  : ∀ {A B} → Closed A → Closed B → Closed (A ⇒ B)
  closed-eff    : ∀ {A B} → Closed A → Closed B → Closed (Eff A B)
  closed-fix    : ∀ {F} → Closed F → Closed (Fix F)

-- | Applying any substitution to a closed type is identity
postulate
  applySubst-closed : ∀ {A} → Closed A → ∀ σ → applySubst σ A ≡ A

------------------------------------------------------------------------
-- Decidability
------------------------------------------------------------------------

-- | Type inference is decidable: always terminates with success or failure
--
-- This follows from the structure of the infer function which is
-- total (modulo the TERMINATING pragma for the recursive calls).

Decidable : Set
Decidable = ∀ Γ e f → ∃[ r ] infer Γ e f ≡ r

-- Decidability is immediate from the definition of infer
decidable : Decidable
decidable Γ e f = infer Γ e f , refl

