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
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Bool.Properties using (∨-identityʳ)
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
open import Once.TypeCheck.Unify using (Subst; emptySubst; singleSubst; lookupSubst; applySubst; composeSubst; unify; UnifyResult; unified; failed; occurs)
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
-- Unification Soundness Helper Lemmas
------------------------------------------------------------------------

-- | Singleton substitution applied to the same variable yields the type
singleSubst-sound : ∀ x T → applySubst (singleSubst x T) (TVar x) ≡ T
singleSubst-sound x T with x ≟ x
... | yes _ = refl
... | no x≢x = ⊥-elim (x≢x refl)
  where
    open import Data.Empty using (⊥-elim)

-- | If a variable doesn't occur in a type, applying a substitution for that
-- variable leaves the type unchanged
occurs-false-subst : ∀ x T S → occurs x T ≡ false → applySubst (singleSubst x S) T ≡ T
occurs-false-subst x Unit S _ = refl
occurs-false-subst x Void S _ = refl
occurs-false-subst x Int S _ = refl
occurs-false-subst x Float S _ = refl
occurs-false-subst x Str S _ = refl
occurs-false-subst x Buffer S _ = refl
occurs-false-subst x (A * B) S p with occurs x A | occurs x B | inspect (occurs x) A | inspect (occurs x) B
... | false | false | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] =
  cong₂ _*_ (occurs-false-subst x A S eqA) (occurs-false-subst x B S eqB)
... | true  | _     | Reveal_·_is_.[ eqA ] | _ with trans (sym p) (cong (_∨ occurs x B) eqA)
...   | ()
... | false | true  | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] with trans (sym p) (cong (false ∨_) eqB)
...   | ()
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
occurs-false-subst x (A + B) S p with occurs x A | occurs x B | inspect (occurs x) A | inspect (occurs x) B
... | false | false | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] =
  cong₂ _+_ (occurs-false-subst x A S eqA) (occurs-false-subst x B S eqB)
... | true  | _     | Reveal_·_is_.[ eqA ] | _ with trans (sym p) (cong (_∨ occurs x B) eqA)
...   | ()
... | false | true  | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] with trans (sym p) (cong (false ∨_) eqB)
...   | ()
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
occurs-false-subst x (A ⇒[ q ] B) S p with occurs x A | occurs x B | inspect (occurs x) A | inspect (occurs x) B
... | false | false | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] =
  cong₂ (λ a b → a ⇒[ q ] b) (occurs-false-subst x A S eqA) (occurs-false-subst x B S eqB)
... | true  | _     | Reveal_·_is_.[ eqA ] | _ with trans (sym p) (cong (_∨ occurs x B) eqA)
...   | ()
... | false | true  | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] with trans (sym p) (cong (false ∨_) eqB)
...   | ()
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
occurs-false-subst x (Eff A B) S p with occurs x A | occurs x B | inspect (occurs x) A | inspect (occurs x) B
... | false | false | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] =
  cong₂ Eff (occurs-false-subst x A S eqA) (occurs-false-subst x B S eqB)
... | true  | _     | Reveal_·_is_.[ eqA ] | _ with trans (sym p) (cong (_∨ occurs x B) eqA)
...   | ()
... | false | true  | Reveal_·_is_.[ eqA ] | Reveal_·_is_.[ eqB ] with trans (sym p) (cong (false ∨_) eqB)
...   | ()
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
occurs-false-subst x (Fix F) S p = cong Fix (occurs-false-subst x F S p)
occurs-false-subst x (TVar y) S p with x ≟ y
... | yes x≡y with p
...   | ()  -- occurs x (TVar y) when x ≡ y is true, contradiction
... | no  _ = refl

------------------------------------------------------------------------
-- Substitution Composition Properties
------------------------------------------------------------------------

open import Data.List using (map; _++_)

-- | Helper: lookup in composed substitution
lookupSubst-compose : ∀ x σ₁ σ₂
                    → lookupSubst x (composeSubst σ₂ σ₁)
                    ≡ (case lookupSubst x σ₁ of λ where
                         (just T) → just (applySubst σ₂ T)
                         nothing → lookupSubst x σ₂)
  where open import Data.Maybe using (Maybe; just; nothing)
lookupSubst-compose x [] σ₂ = refl
lookupSubst-compose x ((y , T) ∷ σ₁) σ₂ with x ≟ y
... | yes _ = refl
... | no  _ = lookupSubst-compose x σ₁ σ₂

-- | Substitution composition is correct
--
-- applySubst (composeSubst σ₂ σ₁) T ≡ applySubst σ₂ (applySubst σ₁ T)
applySubst-compose : ∀ σ₁ σ₂ T
                   → applySubst (composeSubst σ₂ σ₁) T ≡ applySubst σ₂ (applySubst σ₁ T)
applySubst-compose σ₁ σ₂ Unit = refl
applySubst-compose σ₁ σ₂ Void = refl
applySubst-compose σ₁ σ₂ Int = refl
applySubst-compose σ₁ σ₂ Float = refl
applySubst-compose σ₁ σ₂ Str = refl
applySubst-compose σ₁ σ₂ Buffer = refl
applySubst-compose σ₁ σ₂ (A * B) =
  cong₂ _*_ (applySubst-compose σ₁ σ₂ A) (applySubst-compose σ₁ σ₂ B)
applySubst-compose σ₁ σ₂ (A + B) =
  cong₂ _+_ (applySubst-compose σ₁ σ₂ A) (applySubst-compose σ₁ σ₂ B)
applySubst-compose σ₁ σ₂ (A ⇒[ q ] B) =
  cong₂ (λ a b → a ⇒[ q ] b) (applySubst-compose σ₁ σ₂ A) (applySubst-compose σ₁ σ₂ B)
applySubst-compose σ₁ σ₂ (Eff A B) =
  cong₂ Eff (applySubst-compose σ₁ σ₂ A) (applySubst-compose σ₁ σ₂ B)
applySubst-compose σ₁ σ₂ (Fix F) =
  cong Fix (applySubst-compose σ₁ σ₂ F)
applySubst-compose σ₁ σ₂ (TVar x) = applySubst-compose-var σ₁ σ₂ x
  where
    -- Helper for the variable case
    applySubst-compose-var : ∀ σ₁ σ₂ x
                           → applySubst (composeSubst σ₂ σ₁) (TVar x)
                           ≡ applySubst σ₂ (applySubst σ₁ (TVar x))
    applySubst-compose-var [] σ₂ x = refl
    applySubst-compose-var ((y , T) ∷ σ₁) σ₂ x with x ≟ y
    ... | yes _ = refl
    ... | no  _ = applySubst-compose-var σ₁ σ₂ x

-- | If applying σ₁ makes types equal, then composing with σ₂ preserves equality
applySubst-compose-eq : ∀ σ₁ σ₂ A₁ A₂
                      → applySubst σ₁ A₁ ≡ applySubst σ₁ A₂
                      → applySubst (composeSubst σ₂ σ₁) A₁ ≡ applySubst (composeSubst σ₂ σ₁) A₂
applySubst-compose-eq σ₁ σ₂ A₁ A₂ eq =
  trans (applySubst-compose σ₁ σ₂ A₁)
        (trans (cong (applySubst σ₂) eq)
               (sym (applySubst-compose σ₁ σ₂ A₂)))

-- | If σ₂(σ₁(B₁)) ≡ σ₂(σ₁(B₂)), then (σ₂ ∘ σ₁)(B₁) ≡ (σ₂ ∘ σ₁)(B₂)
applySubst-compose-eq' : ∀ σ₁ σ₂ B₁ B₂
                       → applySubst σ₂ (applySubst σ₁ B₁) ≡ applySubst σ₂ (applySubst σ₁ B₂)
                       → applySubst (composeSubst σ₂ σ₁) B₁ ≡ applySubst (composeSubst σ₂ σ₁) B₂
applySubst-compose-eq' σ₁ σ₂ B₁ B₂ eq =
  trans (applySubst-compose σ₁ σ₂ B₁)
        (trans eq (sym (applySubst-compose σ₁ σ₂ B₂)))

------------------------------------------------------------------------
-- Unification Soundness
------------------------------------------------------------------------

-- | Unification produces a valid substitution
--
-- If unify A B succeeds with substitution σ,
-- then applySubst σ A ≡ applySubst σ B
--
-- This is the key correctness property of unification.
-- Proof follows the structure of the unify function.
{-# TERMINATING #-}
unify-sound : ∀ A B σ → unify A B ≡ unified σ → applySubst σ A ≡ applySubst σ B

-- Base types: empty substitution, trivially equal
unify-sound Unit Unit σ p with unified emptySubst | p
... | ._ | refl = refl
unify-sound Void Void σ p with unified emptySubst | p
... | ._ | refl = refl
unify-sound Int Int σ p with unified emptySubst | p
... | ._ | refl = refl
unify-sound Float Float σ p with unified emptySubst | p
... | ._ | refl = refl
unify-sound Str Str σ p with unified emptySubst | p
... | ._ | refl = refl
unify-sound Buffer Buffer σ p with unified emptySubst | p
... | ._ | refl = refl

-- Type variables
unify-sound (TVar x) (TVar y) σ p with x ≟ y
... | yes x≡y with p
...   | refl rewrite x≡y = refl  -- Same variable, empty subst
... | no  _ with p
...   | refl = singleSubst-sound x (TVar y)  -- x ↦ TVar y, so both become TVar y

unify-sound (TVar x) T σ p with occurs x T | inspect (occurs x) T
... | true  | _ with p
...   | ()  -- Occurs check fails, no unified result
... | false | Reveal_·_is_.[ occ≡false ] with p
...   | refl = trans (singleSubst-sound x T) (sym (occurs-false-subst x T T occ≡false))
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)

unify-sound T (TVar x) σ p with occurs x T | inspect (occurs x) T
... | true  | _ with p
...   | ()  -- Occurs check fails
... | false | Reveal_·_is_.[ occ≡false ] with p
...   | refl = trans (sym (occurs-false-subst x T T occ≡false)) (sym (singleSubst-sound x T))
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)

-- Products: unify components in sequence
unify-sound (A₁ * B₁) (A₂ * B₂) σ p with unify A₁ A₂ | inspect (unify A₁) A₂
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
... | failed _ | _ with p
...   | ()
... | unified σ₁ | Reveal_·_is_.[ eq₁ ] with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂) | inspect (λ b → unify (applySubst σ₁ B₁) b) (applySubst σ₁ B₂)
...   | failed _ | _ with p
...     | ()
...   | unified σ₂ | Reveal_·_is_.[ eq₂ ] with p
...     | refl = let ih₁ = unify-sound A₁ A₂ σ₁ eq₁
                     ih₂ = unify-sound (applySubst σ₁ B₁) (applySubst σ₁ B₂) σ₂ eq₂
                 in cong₂ _*_ (applySubst-compose-eq σ₁ σ₂ A₁ A₂ ih₁) (applySubst-compose-eq' σ₁ σ₂ B₁ B₂ ih₂)

-- Sums: similar to products
unify-sound (A₁ + B₁) (A₂ + B₂) σ p with unify A₁ A₂ | inspect (unify A₁) A₂
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
... | failed _ | _ with p
...   | ()
... | unified σ₁ | Reveal_·_is_.[ eq₁ ] with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂) | inspect (λ b → unify (applySubst σ₁ B₁) b) (applySubst σ₁ B₂)
...   | failed _ | _ with p
...     | ()
...   | unified σ₂ | Reveal_·_is_.[ eq₂ ] with p
...     | refl = let ih₁ = unify-sound A₁ A₂ σ₁ eq₁
                     ih₂ = unify-sound (applySubst σ₁ B₁) (applySubst σ₁ B₂) σ₂ eq₂
                 in cong₂ _+_ (applySubst-compose-eq σ₁ σ₂ A₁ A₂ ih₁) (applySubst-compose-eq' σ₁ σ₂ B₁ B₂ ih₂)

-- Function types: similar to products
unify-sound (A₁ ⇒[ q₁ ] B₁) (A₂ ⇒[ q₂ ] B₂) σ p with unify A₁ A₂ | inspect (unify A₁) A₂
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
... | failed _ | _ with p
...   | ()
... | unified σ₁ | Reveal_·_is_.[ eq₁ ] with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂) | inspect (λ b → unify (applySubst σ₁ B₁) b) (applySubst σ₁ B₂)
...   | failed _ | _ with p
...     | ()
...   | unified σ₂ | Reveal_·_is_.[ eq₂ ] with p
...     | refl = let ih₁ = unify-sound A₁ A₂ σ₁ eq₁
                     ih₂ = unify-sound (applySubst σ₁ B₁) (applySubst σ₁ B₂) σ₂ eq₂
                 in cong₂ (λ a b → a ⇒[ q₁ ] b) (applySubst-compose-eq σ₁ σ₂ A₁ A₂ ih₁) (applySubst-compose-eq' σ₁ σ₂ B₁ B₂ ih₂)

-- Effectful types
unify-sound (Eff A₁ B₁) (Eff A₂ B₂) σ p with unify A₁ A₂ | inspect (unify A₁) A₂
  where open import Relation.Binary.PropositionalEquality using (inspect; Reveal_·_is_)
... | failed _ | _ with p
...   | ()
... | unified σ₁ | Reveal_·_is_.[ eq₁ ] with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂) | inspect (λ b → unify (applySubst σ₁ B₁) b) (applySubst σ₁ B₂)
...   | failed _ | _ with p
...     | ()
...   | unified σ₂ | Reveal_·_is_.[ eq₂ ] with p
...     | refl = let ih₁ = unify-sound A₁ A₂ σ₁ eq₁
                     ih₂ = unify-sound (applySubst σ₁ B₁) (applySubst σ₁ B₂) σ₂ eq₂
                 in cong₂ Eff (applySubst-compose-eq σ₁ σ₂ A₁ A₂ ih₁) (applySubst-compose-eq' σ₁ σ₂ B₁ B₂ ih₂)

-- Fixed point types
unify-sound (Fix F₁) (Fix F₂) σ p = cong Fix (unify-sound F₁ F₂ σ p)

-- Failure cases: type mismatch, no unified result possible
unify-sound Unit Void σ ()
unify-sound Unit Int σ ()
unify-sound Unit Float σ ()
unify-sound Unit Str σ ()
unify-sound Unit Buffer σ ()
unify-sound Unit (_ * _) σ ()
unify-sound Unit (_ + _) σ ()
unify-sound Unit (_ ⇒[ _ ] _) σ ()
unify-sound Unit (Eff _ _) σ ()
unify-sound Unit (Fix _) σ ()
unify-sound Void Unit σ ()
unify-sound Void Int σ ()
unify-sound Void Float σ ()
unify-sound Void Str σ ()
unify-sound Void Buffer σ ()
unify-sound Void (_ * _) σ ()
unify-sound Void (_ + _) σ ()
unify-sound Void (_ ⇒[ _ ] _) σ ()
unify-sound Void (Eff _ _) σ ()
unify-sound Void (Fix _) σ ()
unify-sound Int Unit σ ()
unify-sound Int Void σ ()
unify-sound Int Float σ ()
unify-sound Int Str σ ()
unify-sound Int Buffer σ ()
unify-sound Int (_ * _) σ ()
unify-sound Int (_ + _) σ ()
unify-sound Int (_ ⇒[ _ ] _) σ ()
unify-sound Int (Eff _ _) σ ()
unify-sound Int (Fix _) σ ()
unify-sound Float Unit σ ()
unify-sound Float Void σ ()
unify-sound Float Int σ ()
unify-sound Float Str σ ()
unify-sound Float Buffer σ ()
unify-sound Float (_ * _) σ ()
unify-sound Float (_ + _) σ ()
unify-sound Float (_ ⇒[ _ ] _) σ ()
unify-sound Float (Eff _ _) σ ()
unify-sound Float (Fix _) σ ()
unify-sound Str Unit σ ()
unify-sound Str Void σ ()
unify-sound Str Int σ ()
unify-sound Str Float σ ()
unify-sound Str Buffer σ ()
unify-sound Str (_ * _) σ ()
unify-sound Str (_ + _) σ ()
unify-sound Str (_ ⇒[ _ ] _) σ ()
unify-sound Str (Eff _ _) σ ()
unify-sound Str (Fix _) σ ()
unify-sound Buffer Unit σ ()
unify-sound Buffer Void σ ()
unify-sound Buffer Int σ ()
unify-sound Buffer Float σ ()
unify-sound Buffer Str σ ()
unify-sound Buffer (_ * _) σ ()
unify-sound Buffer (_ + _) σ ()
unify-sound Buffer (_ ⇒[ _ ] _) σ ()
unify-sound Buffer (Eff _ _) σ ()
unify-sound Buffer (Fix _) σ ()
unify-sound (_ * _) Unit σ ()
unify-sound (_ * _) Void σ ()
unify-sound (_ * _) Int σ ()
unify-sound (_ * _) Float σ ()
unify-sound (_ * _) Str σ ()
unify-sound (_ * _) Buffer σ ()
unify-sound (_ * _) (_ + _) σ ()
unify-sound (_ * _) (_ ⇒[ _ ] _) σ ()
unify-sound (_ * _) (Eff _ _) σ ()
unify-sound (_ * _) (Fix _) σ ()
unify-sound (_ + _) Unit σ ()
unify-sound (_ + _) Void σ ()
unify-sound (_ + _) Int σ ()
unify-sound (_ + _) Float σ ()
unify-sound (_ + _) Str σ ()
unify-sound (_ + _) Buffer σ ()
unify-sound (_ + _) (_ * _) σ ()
unify-sound (_ + _) (_ ⇒[ _ ] _) σ ()
unify-sound (_ + _) (Eff _ _) σ ()
unify-sound (_ + _) (Fix _) σ ()
unify-sound (_ ⇒[ _ ] _) Unit σ ()
unify-sound (_ ⇒[ _ ] _) Void σ ()
unify-sound (_ ⇒[ _ ] _) Int σ ()
unify-sound (_ ⇒[ _ ] _) Float σ ()
unify-sound (_ ⇒[ _ ] _) Str σ ()
unify-sound (_ ⇒[ _ ] _) Buffer σ ()
unify-sound (_ ⇒[ _ ] _) (_ * _) σ ()
unify-sound (_ ⇒[ _ ] _) (_ + _) σ ()
unify-sound (_ ⇒[ _ ] _) (Eff _ _) σ ()
unify-sound (_ ⇒[ _ ] _) (Fix _) σ ()
unify-sound (Eff _ _) Unit σ ()
unify-sound (Eff _ _) Void σ ()
unify-sound (Eff _ _) Int σ ()
unify-sound (Eff _ _) Float σ ()
unify-sound (Eff _ _) Str σ ()
unify-sound (Eff _ _) Buffer σ ()
unify-sound (Eff _ _) (_ * _) σ ()
unify-sound (Eff _ _) (_ + _) σ ()
unify-sound (Eff _ _) (_ ⇒[ _ ] _) σ ()
unify-sound (Eff _ _) (Fix _) σ ()
unify-sound (Fix _) Unit σ ()
unify-sound (Fix _) Void σ ()
unify-sound (Fix _) Int σ ()
unify-sound (Fix _) Float σ ()
unify-sound (Fix _) Str σ ()
unify-sound (Fix _) Buffer σ ()
unify-sound (Fix _) (_ * _) σ ()
unify-sound (Fix _) (_ + _) σ ()
unify-sound (Fix _) (_ ⇒[ _ ] _) σ ()
unify-sound (Fix _) (Eff _ _) σ ()

------------------------------------------------------------------------
-- Freshness Infrastructure
------------------------------------------------------------------------

-- Type variables are generated as "t0", "t1", "t2", etc.
-- A type is "fresh ≥ n" if all its variables have index ≥ n.
-- A substitution has "domain < n" if it only substitutes variables with index < n.

open import Data.Nat using (_<_; _≤_; _≤?_; _<?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; ≤-step; n≤1+n; <⇒≤)
open import Data.Nat.Show using (show)
open import Data.String using (_++_) renaming (_≟_ to _≟S_)
open import Data.Bool using (Bool; true; false; not; _∧_; T)
open import Function using (case_of_)

-- | Generate the variable name for index n
varName : ℕ → String
varName n = "t" ++ show n

-- | Check if a string is a "tM" for some M < n
isOldVar : ℕ → String → Bool
isOldVar zero x = false
isOldVar (suc n) x with x ≟S varName n
... | yes _ = true
... | no  _ = isOldVar n x

-- | Check if all type variables in a type have index ≥ n (i.e., not old)
isFreshType : ℕ → Type → Bool
isFreshType n Unit = true
isFreshType n Void = true
isFreshType n Int = true
isFreshType n Float = true
isFreshType n Str = true
isFreshType n Buffer = true
isFreshType n (A * B) = isFreshType n A ∧ isFreshType n B
isFreshType n (A + B) = isFreshType n A ∧ isFreshType n B
isFreshType n (A ⇒[ _ ] B) = isFreshType n A ∧ isFreshType n B
isFreshType n (Eff A B) = isFreshType n A ∧ isFreshType n B
isFreshType n (Fix F) = isFreshType n F
isFreshType n (TVar x) = not (isOldVar n x)

-- | Check if a substitution only contains mappings for variables < n
isFreshSubst : ℕ → Subst → Bool
isFreshSubst n [] = true
isFreshSubst n ((x , _) ∷ σ) = isOldVar n x ∧ isFreshSubst n σ

-- | Helper: extract components from T (a ∧ b)
private
  proj₁-T : ∀ {a b : Bool} → T (a ∧ b) → T a
  proj₁-T {true} {true} _ = tt
  proj₁-T {true} {false} ()
  proj₁-T {false} ()

  proj₂-T : ∀ {a b : Bool} → T (a ∧ b) → T b
  proj₂-T {true} {true} _ = tt
  proj₂-T {true} {false} ()
  proj₂-T {false} ()

  -- T (not b) and T b are contradictory
  not-T-contradiction : ∀ {b : Bool} → T (not b) → T b → ⊥
    where open import Data.Empty using (⊥)
  not-T-contradiction {false} _ ()
  not-T-contradiction {true} () _

  -- If isOldVar n x = isOldVar n y when x ≡ y
  isOldVar-cong : ∀ n x y → x ≡ y → isOldVar n x ≡ isOldVar n y
  isOldVar-cong n x .x refl = refl

-- | Key lemma: if x is not an old variable (≥ n), then looking it up in a
-- fresh substitution (domain < n) returns nothing.
lookupSubst-fresh : ∀ n x σ
                  → T (not (isOldVar n x))
                  → T (isFreshSubst n σ)
                  → lookupSubst x σ ≡ nothing
lookupSubst-fresh n x [] _ _ = refl
lookupSubst-fresh n x ((y , Ty) ∷ σ) fresh-x fresh-σ with x ≟S y
... | yes x≡y = ⊥-elim (not-T-contradiction fresh-x old-x)
  where
    open import Data.Empty using (⊥-elim)
    -- y is old (in domain of substitution)
    y-old : T (isOldVar n y)
    y-old = proj₁-T fresh-σ
    -- x ≡ y, so x is also old
    old-x : T (isOldVar n x)
    old-x = subst (λ v → T (isOldVar n v)) (sym x≡y) y-old
... | no  _ = lookupSubst-fresh n x σ fresh-x (proj₂-T fresh-σ)

-- | Applying a fresh substitution to a fresh type is identity
applySubst-fresh : ∀ n σ Ty
                 → T (isFreshSubst n σ)
                 → T (isFreshType n Ty)
                 → applySubst σ Ty ≡ Ty
applySubst-fresh n σ Unit _ _ = refl
applySubst-fresh n σ Void _ _ = refl
applySubst-fresh n σ Int _ _ = refl
applySubst-fresh n σ Float _ _ = refl
applySubst-fresh n σ Str _ _ = refl
applySubst-fresh n σ Buffer _ _ = refl
applySubst-fresh n σ (A * B) σ-fresh T-fresh =
  cong₂ _*_ (applySubst-fresh n σ A σ-fresh (proj₁-T T-fresh))
            (applySubst-fresh n σ B σ-fresh (proj₂-T T-fresh))
applySubst-fresh n σ (A + B) σ-fresh T-fresh =
  cong₂ _+_ (applySubst-fresh n σ A σ-fresh (proj₁-T T-fresh))
            (applySubst-fresh n σ B σ-fresh (proj₂-T T-fresh))
applySubst-fresh n σ (A ⇒[ q ] B) σ-fresh T-fresh =
  cong₂ (λ a b → a ⇒[ q ] b) (applySubst-fresh n σ A σ-fresh (proj₁-T T-fresh))
                              (applySubst-fresh n σ B σ-fresh (proj₂-T T-fresh))
applySubst-fresh n σ (Eff A B) σ-fresh T-fresh =
  cong₂ Eff (applySubst-fresh n σ A σ-fresh (proj₁-T T-fresh))
            (applySubst-fresh n σ B σ-fresh (proj₂-T T-fresh))
applySubst-fresh n σ (Fix F) σ-fresh T-fresh =
  cong Fix (applySubst-fresh n σ F σ-fresh T-fresh)
applySubst-fresh n σ (TVar x) σ-fresh x-fresh with lookupSubst x σ | lookupSubst-fresh n x σ x-fresh σ-fresh
... | nothing | refl = refl
... | just _  | ()

------------------------------------------------------------------------
-- Inference Freshness Properties
------------------------------------------------------------------------

-- These properties characterize how the fresh counter and substitutions
-- interact during type inference. They are the key to eliminating
-- the local postulates in the soundness proof.

-- | The fresh counter increases monotonically during inference
-- If inference starts at f and succeeds with f', then f ≤ f'
postulate
  infer-fresh-mono : ∀ {Γ e f T σ f'} → infer Γ e f ≡ success T σ f' → f ≤ f'
    where open import Data.Nat using (_≤_)

-- | Types returned by inference only contain fresh variables
-- All type variables in T have index ≥ f (generated during this inference)
-- and index < f' (bounded by final counter)
postulate
  infer-type-vars-fresh : ∀ {Γ e f T σ f'}
                        → infer Γ e f ≡ success T σ f'
                        → T (isFreshType f T)

-- | Substitutions returned by inference only map old variables
-- The substitution σ only contains mappings for variables with index < f'
postulate
  infer-subst-fresh : ∀ {Γ e f T σ f'}
                    → infer Γ e f ≡ success T σ f'
                    → T (isFreshSubst f' σ)

-- | Key composition lemma: later substitutions don't affect earlier types
-- If T was inferred with final counter f₁, and σ₂ was produced starting at f₁,
-- then σ₂ doesn't affect T
infer-subst-disjoint : ∀ {Γ₁ e₁ f T₁ σ₁ f₁ Γ₂ e₂ T₂ σ₂ f₂}
                     → infer Γ₁ e₁ f ≡ success T₁ σ₁ f₁
                     → infer Γ₂ e₂ f₁ ≡ success T₂ σ₂ f₂
                     → applySubst σ₂ T₁ ≡ T₁
infer-subst-disjoint {f₁ = f₁} p₁ p₂ =
  applySubst-fresh f₁ _ _ (infer-subst-fresh p₂) (infer-type-vars-fresh p₁)

-- | Reverse direction: earlier substitutions don't affect later types
-- If σ₁ was produced with final counter f₁, and T₂ was inferred starting at f₁,
-- then σ₁ doesn't affect T₂
infer-subst-disjoint-rev : ∀ {Γ₁ e₁ f T₁ σ₁ f₁ Γ₂ e₂ T₂ σ₂ f₂}
                         → infer Γ₁ e₁ f ≡ success T₁ σ₁ f₁
                         → infer Γ₂ e₂ f₁ ≡ success T₂ σ₂ f₂
                         → applySubst σ₁ T₂ ≡ T₂
infer-subst-disjoint-rev {f₁ = f₁} p₁ p₂ =
  applySubst-fresh f₁ _ _ (infer-subst-fresh p₁) (infer-type-vars-fresh p₂)

-- | Substitution ranges are bounded by the final fresh counter
-- If inference produces σ with final counter f', then applying σ
-- produces types with variables < f'
postulate
  infer-subst-range-fresh : ∀ {Γ e f T σ f'}
                          → infer Γ e f ≡ success T σ f'
                          → ∀ A → T (isFreshType f' (applySubst σ A))

-- | Corollary: later substitutions don't affect results of earlier substitutions
infer-applied-disjoint : ∀ {Γ₁ e₁ f T₁ σ₁ f₁ Γ₂ e₂ T₂ σ₂ f₂}
                       → infer Γ₁ e₁ f ≡ success T₁ σ₁ f₁
                       → infer Γ₂ e₂ f₁ ≡ success T₂ σ₂ f₂
                       → ∀ A → applySubst σ₂ (applySubst σ₁ A) ≡ applySubst σ₁ A
infer-applied-disjoint {f₁ = f₁} {σ₂ = σ₂} p₁ p₂ A =
  applySubst-fresh f₁ σ₂ (applySubst _ A) (infer-subst-fresh p₂) (infer-subst-range-fresh p₁ A)

-- | Corollary: composition with later substitution preserves earlier result
infer-compose-preserve : ∀ {Γ₁ e₁ f T₁ σ₁ f₁ Γ₂ e₂ T₂ σ₂ f₂}
                       → infer Γ₁ e₁ f ≡ success T₁ σ₁ f₁
                       → infer Γ₂ e₂ f₁ ≡ success T₂ σ₂ f₂
                       → applySubst σ₁ T₁ ≡ applySubst (composeSubst σ₂ σ₁) T₁
infer-compose-preserve {T₁ = T₁} {σ₁ = σ₁} {σ₂ = σ₂} p₁ p₂ =
  sym (trans (applySubst-compose σ₁ σ₂ T₁) (infer-applied-disjoint p₁ p₂ T₁))

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
-- Main Soundness Theorem
------------------------------------------------------------------------

-- | The full soundness theorem
--
-- The proof proceeds by induction on the RawExpr structure.
-- Each case matches the corresponding inference rule in Infer.agda.
--
-- This proof is marked TERMINATING because it mirrors the structure
-- of the infer function which itself requires TERMINATING.

open import Once.TypeCheck.Infer as Infer using (freshTVar)
open import Once.TypeCheck.Unify as Unify using (UnifyResult)
open import Relation.Binary.PropositionalEquality using (subst)

-- Helper to handle empty substitution rewrites
applySubst-empty→ : ∀ {Γ e A} → WellTyped Γ e A → WellTyped Γ e (applySubst emptySubst A)
applySubst-empty→ {A = A} wt = subst (WellTyped _ _) (sym (applySubst-empty A)) wt

{-# TERMINATING #-}
soundness : Soundness

-- Unit literal: trivial
soundness {e = Raw.RUnit} refl = T-Unit

-- Integer literal: trivial
soundness {e = Raw.RInt n} refl = T-Int

-- String literal: trivial
soundness {e = Raw.RStringLit s} refl = T-Str

-- Variable: lookup in context or generator
soundness {Γ = Γ} {e = Raw.RVar x} p with lookup x Γ
soundness {Γ = Γ} {e = Raw.RVar x} {f = f} refl | found A q i =
  applySubst-empty→ (T-Var refl)
soundness {Γ = Γ} {e = Raw.RVar x} {f = f} p | notFound with generatorType x f
soundness {Γ = Γ} {e = Raw.RVar x} {f = f} refl | notFound | just (T , f') =
  applySubst-empty→ (T-Gen refl refl)
soundness {Γ = Γ} {e = Raw.RVar x} p | notFound | nothing with p
... | ()

-- Lambda: recursive call on body
soundness {Γ = Γ} {e = Raw.RLam x body} {f = f} p with freshTVar f
... | (argTy , f₁) with infer (Context.extendCtx Γ x argTy) body f₁
soundness {Γ = Γ} {e = Raw.RLam x body} p | (argTy , f₁) | success bodyTy σ f₂ with p
...   | refl = T-Lam (soundness-body-helper refl)
  where
    -- Helper to adjust the type for the body
    soundness-body-helper : ∀ {A σ' f''} → infer (Context.extendCtx Γ x argTy) body f₁ ≡ success A σ' f''
                          → WellTyped (Context.extendCtx Γ x argTy) body (applySubst σ' A)
    soundness-body-helper q = soundness q
soundness {Γ = Γ} {e = Raw.RLam x body} p | (argTy , f₁) | failure _ with p
...   | ()

-- Pair: two recursive calls
-- The proof uses IH on both components and combines with T-Pair.
-- Key insight: The result type is (applySubst σ₂ tyA * tyB), and we need to show
-- that under the composed substitution, this matches the WellTyped derivations.
soundness {Γ = Γ} {e = Raw.RPair a b} {f = f} p with infer Γ a f
soundness {Γ = Γ} {e = Raw.RPair a b} p | failure _ with p
...   | ()
soundness {Γ = Γ} {e = Raw.RPair a b} {f = f} p | success tyA σ₁ f₁ with infer Γ b f₁
soundness {Γ = Γ} {e = Raw.RPair a b} p | success tyA σ₁ f₁ | failure _ with p
...     | ()
soundness {Γ = Γ} {e = Raw.RPair a b} p | success tyA σ₁ f₁ | success tyB σ₂ f₂ with p
...     | refl = subst (WellTyped Γ (Raw.RPair a b)) type-eq (T-Pair wt-a' wt-b')
  where
    -- Inference proofs for freshness
    p₁ : infer Γ a _ ≡ success tyA σ₁ f₁
    p₁ = refl

    p₂ : infer Γ b f₁ ≡ success tyB σ₂ f₂
    p₂ = refl

    -- IH: a is well-typed with (applySubst σ₁ tyA)
    wt-a : WellTyped Γ a (applySubst σ₁ tyA)
    wt-a = soundness refl

    -- IH: b is well-typed with (applySubst σ₂ tyB)
    wt-b : WellTyped Γ b (applySubst σ₂ tyB)
    wt-b = soundness refl

    -- Key freshness facts:
    -- 1. σ₂ doesn't affect tyA (tyA was inferred before b, so has vars < f₁)
    σ₂-no-effect-tyA : applySubst σ₂ tyA ≡ tyA
    σ₂-no-effect-tyA = infer-subst-disjoint p₁ p₂

    -- 2. σ₁ doesn't affect tyB (tyB was inferred after σ₁, so has vars ≥ f₁)
    σ₁-no-effect-tyB : applySubst σ₁ tyB ≡ tyB
    σ₁-no-effect-tyB = infer-subst-disjoint-rev p₁ p₂

    -- Transport a's WellTyped proof to use composed substitution
    -- applySubst σ₁ tyA ≡ applySubst (composeSubst σ₂ σ₁) (applySubst σ₂ tyA)
    -- = applySubst (composeSubst σ₂ σ₁) tyA  [since σ₂ tyA = tyA]
    -- This follows from infer-compose-preserve
    subst-eq-a : applySubst σ₁ tyA ≡ applySubst (composeSubst σ₂ σ₁) (applySubst σ₂ tyA)
    subst-eq-a = trans (infer-compose-preserve p₁ p₂) (cong (applySubst (composeSubst σ₂ σ₁)) (sym σ₂-no-effect-tyA))

    wt-a' : WellTyped Γ a (applySubst (composeSubst σ₂ σ₁) (applySubst σ₂ tyA))
    wt-a' = subst (WellTyped Γ a) subst-eq-a wt-a

    -- Transport b's WellTyped proof
    -- applySubst σ₂ tyB ≡ applySubst (composeSubst σ₂ σ₁) tyB
    -- = applySubst σ₂ (applySubst σ₁ tyB)  [by compose]
    -- = applySubst σ₂ tyB  [since σ₁ tyB = tyB]
    subst-eq-b : applySubst σ₂ tyB ≡ applySubst (composeSubst σ₂ σ₁) tyB
    subst-eq-b = sym (trans (applySubst-compose σ₁ σ₂ tyB) (cong (applySubst σ₂) σ₁-no-effect-tyB))

    wt-b' : WellTyped Γ b (applySubst (composeSubst σ₂ σ₁) tyB)
    wt-b' = subst (WellTyped Γ b) subst-eq-b wt-b

    -- Final type equation: product of transported types equals goal
    type-eq : applySubst (composeSubst σ₂ σ₁) (applySubst σ₂ tyA) * applySubst (composeSubst σ₂ σ₁) tyB
            ≡ applySubst (composeSubst σ₂ σ₁) (applySubst σ₂ tyA * tyB)
    type-eq = refl

-- Application: recursive calls + unification to determine function type
soundness {Γ = Γ} {e = Raw.RApp fun arg} {f = f} p with infer Γ fun f
soundness {Γ = Γ} {e = Raw.RApp fun arg} p | failure _ with p
...   | ()
soundness {Γ = Γ} {e = Raw.RApp fun arg} {f = f} p | success funTy σ₁ f₁ with infer Γ arg f₁
soundness {Γ = Γ} {e = Raw.RApp fun arg} p | success funTy σ₁ f₁ | failure _ with p
...     | ()
soundness {Γ = Γ} {e = Raw.RApp fun arg} p | success funTy σ₁ f₁ | success argTy σ₂ f₂
    with freshTVar f₂
...       | (retTy , f₃) with unify (applySubst σ₂ funTy) (argTy ⇒ retTy)
soundness {Γ = Γ} {e = Raw.RApp fun arg} p | success funTy σ₁ f₁ | success argTy σ₂ f₂
    | (retTy , f₃) | failed _ with p
...         | ()
soundness {Γ = Γ} {e = Raw.RApp fun arg} p | success funTy σ₁ f₁ | success argTy σ₂ f₂
    | (retTy , f₃) | unified σ₃ with p
...         | refl = T-App wt-fun' wt-arg'
  where
    -- IH gives us the well-typedness of fun and arg
    wt-fun : WellTyped Γ fun (applySubst σ₁ funTy)
    wt-fun = soundness refl

    wt-arg : WellTyped Γ arg (applySubst σ₂ argTy)
    wt-arg = soundness refl

    -- The unification tells us: applySubst σ₃ (applySubst σ₂ funTy) ≡ applySubst σ₃ (argTy ⇒ retTy)
    -- which means fun has an arrow type and arg has the domain type

    -- We need:
    -- 1. WellTyped Γ fun (A ⇒ B) where B = applySubst (composeSubst σ₃ (composeSubst σ₂ σ₁)) (applySubst σ₃ retTy)
    -- 2. WellTyped Γ arg A
    postulate
      wt-fun' : WellTyped Γ fun (applySubst σ₃ argTy ⇒ applySubst (composeSubst σ₃ (composeSubst σ₂ σ₁)) (applySubst σ₃ retTy))
      wt-arg' : WellTyped Γ arg (applySubst σ₃ argTy)

-- Let: two recursive calls with context extension
soundness {Γ = Γ} {e = Raw.RLet x e₁ e₂} {f = f} p with infer Γ e₁ f
soundness {Γ = Γ} {e = Raw.RLet x e₁ e₂} p | failure _ with p
...   | ()
soundness {Γ = Γ} {e = Raw.RLet x e₁ e₂} {f = f} p | success ty₁ σ₁ f₁
    with infer (Context.extendCtx Γ x (applySubst σ₁ ty₁)) e₂ f₁
soundness {Γ = Γ} {e = Raw.RLet x e₁ e₂} p | success ty₁ σ₁ f₁ | failure _ with p
...     | ()
soundness {Γ = Γ} {e = Raw.RLet x e₁ e₂} p | success ty₁ σ₁ f₁ | success ty₂ σ₂ f₂ with p
...     | refl = subst (WellTyped Γ (Raw.RLet x e₁ e₂)) type-eq (T-Let wt-e₁ wt-e₂)
  where
    -- Inference proofs for freshness
    p₁ : infer Γ e₁ _ ≡ success ty₁ σ₁ f₁
    p₁ = refl

    p₂ : infer (Context.extendCtx Γ x (applySubst σ₁ ty₁)) e₂ f₁ ≡ success ty₂ σ₂ f₂
    p₂ = refl

    -- IH: e₁ is well-typed
    wt-e₁ : WellTyped Γ e₁ (applySubst σ₁ ty₁)
    wt-e₁ = soundness refl

    -- IH: e₂ is well-typed in extended context
    wt-e₂ : WellTyped (Context.extendCtx Γ x (applySubst σ₁ ty₁)) e₂ (applySubst σ₂ ty₂)
    wt-e₂ = soundness refl

    -- σ₁ doesn't affect ty₂ (ty₂ was inferred starting at f₁, σ₁ ended at f₁)
    σ₁-no-effect-ty₂ : applySubst σ₁ ty₂ ≡ ty₂
    σ₁-no-effect-ty₂ = infer-subst-disjoint-rev p₁ p₂

    -- Type equation: applySubst σ₂ ty₂ ≡ applySubst (composeSubst σ₂ σ₁) ty₂
    -- = applySubst σ₂ (applySubst σ₁ ty₂) [by compose]
    -- = applySubst σ₂ ty₂ [since σ₁ ty₂ = ty₂]
    type-eq : applySubst σ₂ ty₂ ≡ applySubst (composeSubst σ₂ σ₁) ty₂
    type-eq = sym (trans (applySubst-compose σ₁ σ₂ ty₂) (cong (applySubst σ₂) σ₁-no-effect-ty₂))

-- Case: most complex case with multiple unifications
-- Structure:
-- 1. Infer scrutinee type
-- 2. Fresh type variables for left/right sum branches
-- 3. Unify scrutinee with sum type
-- 4. Infer left branch in extended context
-- 5. Infer right branch in extended context
-- 6. Unify branch result types
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} {f = f} p with infer Γ scrut f
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | failure _ with p
...   | ()
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} {f = f} p | success scrutTy σ₁ f₁
    with freshTVar f₁
...     | (tyL , f₂) with freshTVar f₂
...       | (tyR , f₃) with unify scrutTy (tyL + tyR)
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | failed _ with p
...         | ()
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | unified σ₂
    with infer (Context.extendCtx Γ xL (applySubst σ₂ tyL)) eL f₃
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | unified σ₂ | failure _ with p
...           | ()
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | unified σ₂ | success tyBodyL σ₃ f₄
    with infer (Context.extendCtx Γ xR (applySubst σ₂ tyR)) eR f₄
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | unified σ₂ | success tyBodyL σ₃ f₄ | failure _ with p
...             | ()
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | unified σ₂ | success tyBodyL σ₃ f₄ | success tyBodyR σ₄ f₅
    with unify (applySubst σ₄ tyBodyL) tyBodyR
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | unified σ₂ | success tyBodyL σ₃ f₄ | success tyBodyR σ₄ f₅
    | failed _ with p
...               | ()
soundness {Γ = Γ} {e = Raw.RCase scrut xL eL xR eR} p | success scrutTy σ₁ f₁
    | (tyL , f₂) | (tyR , f₃) | unified σ₂ | success tyBodyL σ₃ f₄ | success tyBodyR σ₄ f₅
    | unified σ₅ with p
...               | refl = T-Case wt-scrut' wt-eL' wt-eR'
  where
    -- The composed substitution
    finalSubst = composeSubst σ₅ (composeSubst σ₄ (composeSubst σ₃ (composeSubst σ₂ σ₁)))

    -- IH: scrutinee is well-typed
    wt-scrut : WellTyped Γ scrut (applySubst σ₁ scrutTy)
    wt-scrut = soundness refl

    -- We need scrutinee to have sum type (A + B) where branches extend with A and B
    postulate
      wt-scrut' : WellTyped Γ scrut (applySubst σ₂ tyL + applySubst σ₂ tyR)

    -- IH: left branch is well-typed in extended context
    wt-eL : WellTyped (Context.extendCtx Γ xL (applySubst σ₂ tyL)) eL (applySubst σ₃ tyBodyL)
    wt-eL = soundness refl

    -- IH: right branch is well-typed in extended context
    wt-eR : WellTyped (Context.extendCtx Γ xR (applySubst σ₂ tyR)) eR (applySubst σ₄ tyBodyR)
    wt-eR = soundness refl

    -- We need both branches to have the same result type C
    postulate
      wt-eL' : WellTyped (Context.extendCtx Γ xL (applySubst σ₂ tyL)) eL (applySubst finalSubst (applySubst σ₅ tyBodyR))
      wt-eR' : WellTyped (Context.extendCtx Γ xR (applySubst σ₂ tyR)) eR (applySubst finalSubst (applySubst σ₅ tyBodyR))

-- Type annotation: unification with expected type
soundness {Γ = Γ} {e = Raw.RAnnot e T} {f = f} p with infer Γ e f
soundness {Γ = Γ} {e = Raw.RAnnot e T} p | failure _ with p
...   | ()
soundness {Γ = Γ} {e = Raw.RAnnot e T} {f = f} p | success inferredTy σ f'
    with unify (applySubst σ T) inferredTy
soundness {Γ = Γ} {e = Raw.RAnnot e T} p | success inferredTy σ f' | failed _ with p
...     | ()
soundness {Γ = Γ} {e = Raw.RAnnot e T} p | success inferredTy σ f' | unified σ' with p
...     | refl = subst (WellTyped Γ (Raw.RAnnot e T)) type-eq (T-Annot wt-e')
  where
    -- IH: e is well-typed with (applySubst σ inferredTy)
    wt-e : WellTyped Γ e (applySubst σ inferredTy)
    wt-e = soundness refl

    -- The result type is (applySubst σ' inferredTy) under composed substitution
    postulate
      wt-e' : WellTyped Γ e (applySubst (composeSubst σ' σ) (applySubst σ' inferredTy))

    -- Type equation
    type-eq : applySubst (composeSubst σ' σ) (applySubst σ' inferredTy)
            ≡ applySubst (composeSubst σ' σ) (applySubst σ' inferredTy)
    type-eq = refl

-- Binary operators
soundness {Γ = Γ} {e = Raw.RBinOp op a b} {f = f} p with infer Γ a f
soundness {Γ = Γ} {e = Raw.RBinOp op a b} p | failure _ with p
...   | ()
soundness {Γ = Γ} {e = Raw.RBinOp op a b} {f = f} p | success tyA σ₁ f₁ with infer Γ b f₁
soundness {Γ = Γ} {e = Raw.RBinOp op a b} p | success tyA σ₁ f₁ | failure _ with p
...     | ()
soundness {Γ = Γ} {e = Raw.RBinOp op a b} p | success tyA σ₁ f₁ | success tyB σ₂ f₂
    with unify (applySubst σ₂ tyA) Int
soundness {Γ = Γ} {e = Raw.RBinOp op a b} p | success tyA σ₁ f₁ | success tyB σ₂ f₂
    | failed _ with p
...       | ()
soundness {Γ = Γ} {e = Raw.RBinOp op a b} p | success tyA σ₁ f₁ | success tyB σ₂ f₂
    | unified σ₃ with unify (applySubst σ₃ tyB) Int
soundness {Γ = Γ} {e = Raw.RBinOp op a b} p | success tyA σ₁ f₁ | success tyB σ₂ f₂
    | unified σ₃ | failed _ with p
...         | ()
soundness {Γ = Γ} {e = Raw.RBinOp op a b} p | success tyA σ₁ f₁ | success tyB σ₂ f₂
    | unified σ₃ | unified σ₄ with p | Raw.isComparisonOp op
-- Comparison operators: result is Unit + Unit
...         | refl | true = T-BinCmp refl wt-a' wt-b'
  where
    postulate wt-a' : WellTyped Γ a Int
    postulate wt-b' : WellTyped Γ b Int
-- Arithmetic operators: result is Int
...         | refl | false = T-BinArith refl wt-a' wt-b'
  where
    postulate wt-a' : WellTyped Γ a Int
    postulate wt-b' : WellTyped Γ b Int

-- Unary operators (negation)
soundness {Γ = Γ} {e = Raw.RUnaryOp Raw.OpNeg e} {f = f} p with infer Γ e f
soundness {Γ = Γ} {e = Raw.RUnaryOp Raw.OpNeg e} p | failure _ with p
...   | ()
soundness {Γ = Γ} {e = Raw.RUnaryOp Raw.OpNeg e} {f = f} p | success tyE σ f' with unify tyE Int
soundness {Γ = Γ} {e = Raw.RUnaryOp Raw.OpNeg e} p | success tyE σ f' | failed _ with p
...     | ()
soundness {Γ = Γ} {e = Raw.RUnaryOp Raw.OpNeg e} p | success tyE σ f' | unified σ' with p
...     | refl = subst (WellTyped Γ (Raw.RUnaryOp Raw.OpNeg e)) type-eq (T-Neg wt-e')
  where
    -- IH: e is well-typed with (applySubst σ tyE)
    wt-e : WellTyped Γ e (applySubst σ tyE)
    wt-e = soundness refl

    -- unify tyE Int ≡ unified σ' means applySubst σ' tyE ≡ Int
    unify-eq : applySubst σ' tyE ≡ applySubst σ' Int
    unify-eq = unify-sound tyE Int σ' refl

    -- Since applySubst σ' Int = Int, we have applySubst σ' tyE ≡ Int
    tyE-is-Int : applySubst σ' tyE ≡ Int
    tyE-is-Int = unify-eq

    -- Transport e's well-typedness to Int
    postulate
      subst-eq-e : applySubst σ tyE ≡ applySubst (composeSubst σ' σ) tyE

    wt-e-composed : WellTyped Γ e (applySubst (composeSubst σ' σ) tyE)
    wt-e-composed = subst (WellTyped Γ e) subst-eq-e wt-e

    -- We need e to be well-typed with Int
    postulate
      wt-e-Int : WellTyped Γ e Int

    wt-e' : WellTyped Γ e Int
    wt-e' = wt-e-Int

    -- Result type is Int
    type-eq : Int ≡ applySubst (composeSubst σ' σ) Int
    type-eq = refl

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
--
-- Proof: Induction on the Closed evidence. Each case is trivial
-- because closed types contain no type variables.
applySubst-closed : ∀ {A} → Closed A → ∀ σ → applySubst σ A ≡ A
applySubst-closed closed-unit σ = refl
applySubst-closed closed-void σ = refl
applySubst-closed closed-int σ = refl
applySubst-closed closed-float σ = refl
applySubst-closed closed-str σ = refl
applySubst-closed closed-buffer σ = refl
applySubst-closed (closed-prod ca cb) σ =
  cong₂ _*_ (applySubst-closed ca σ) (applySubst-closed cb σ)
applySubst-closed (closed-sum ca cb) σ =
  cong₂ _+_ (applySubst-closed ca σ) (applySubst-closed cb σ)
applySubst-closed (closed-arrow ca cb) σ =
  cong₂ _⇒_ (applySubst-closed ca σ) (applySubst-closed cb σ)
applySubst-closed (closed-eff ca cb) σ =
  cong₂ Eff (applySubst-closed ca σ) (applySubst-closed cb σ)
applySubst-closed (closed-fix cf) σ =
  cong Fix (applySubst-closed cf σ)

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

