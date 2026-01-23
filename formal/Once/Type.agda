------------------------------------------------------------------------
-- Once.Type
--
-- Definition of types in the Once language.
-- These are the objects of a Cartesian Closed Category.
------------------------------------------------------------------------

module Once.Type where

open import Level using (Level)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟S_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Quantitative Type Theory: Usage Grades
------------------------------------------------------------------------

-- | Usage quantities (grades) for QTT
--
-- These track how many times a variable is used:
-- - Zero: Erased (compile-time only, zero runtime cost)
-- - One:  Linear (used exactly once, enforce resource safety)
-- - Many: Unrestricted (used 0+ times)
--
data Quantity : Set where
  Zero  : Quantity  -- 0: Erased
  One   : Quantity  -- 1: Linear
  Many  : Quantity  -- ω: Unrestricted

-- | Quantity addition (usage combination)
--
-- When two branches both use a variable, we add their usage:
-- - 0 + q = q (erased doesn't contribute)
-- - 1 + 0 = 1 (linear, other branch erased)
-- - 1 + 1 = ω (both branches use → unrestricted needed)
-- - ω + _ = ω (unrestricted propagates)
--
_+q_ : Quantity → Quantity → Quantity
Zero  +q q     = q
One   +q Zero  = One
One   +q One   = Many
One   +q Many  = Many
Many  +q _     = Many

infixl 60 _+q_

-- | Quantity multiplication (usage scaling)
--
-- When a variable is used inside a context with quantity q:
-- - 0 * _ = 0 (erased context → variable erased)
-- - 1 * q = q (linear context → preserve variable usage)
-- - ω * q = ω (unrestricted context → variable unrestricted)
--
_*q_ : Quantity → Quantity → Quantity
Zero  *q _     = Zero
_     *q Zero  = Zero
One   *q q     = q
q     *q One   = q
Many  *q Many  = Many

infixl 70 _*q_

-- | Decidable equality for quantities
_≟q_ : (q₁ q₂ : Quantity) → Dec (q₁ ≡ q₂)
Zero  ≟q Zero  = yes refl
Zero  ≟q One   = no (λ ())
Zero  ≟q Many  = no (λ ())
One   ≟q Zero  = no (λ ())
One   ≟q One   = yes refl
One   ≟q Many  = no (λ ())
Many  ≟q Zero  = no (λ ())
Many  ≟q One   = no (λ ())
Many  ≟q Many  = yes refl

-- | Subusaging order (q₁ ≤ q₂ means q₁ can be used where q₂ is expected)
--
-- - 0 ≤ q for all q (can always erase)
-- - 1 ≤ ω (linear can be used as unrestricted)
-- - q ≤ q (reflexive)
--
_≤q_ : Quantity → Quantity → Bool
Zero  ≤q _     = true
One   ≤q One   = true
One   ≤q Many  = true
Many  ≤q Many  = true
_     ≤q _     = false

-- | Show function for Quantity (for error messages)
showQuantity : Quantity → String
showQuantity Zero = "0"
showQuantity One  = "1"
showQuantity Many = "ω"

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | Types in Once
--
-- These correspond to objects in a Cartesian Closed Category:
-- - Unit is the terminal object (1)
-- - Void is the initial object (0)
-- - _*_ is the categorical product (×)
-- - _+_ is the categorical coproduct (+)
-- - _⇒_ is the exponential object (function space, pure)
-- - Eff is the effectful morphism (D032: arrow-based effects)
-- - Fix is the fixed point (for recursive types)
--
-- Additional base types for practical programming:
-- - Int is machine integers
-- - Float is IEEE 754 double-precision floats
-- - Str is UTF-8 strings
-- - Buffer is raw byte buffers
-- - TVar is a type variable (for polymorphism)
--
data Type : Set where
  -- Categorical structure
  Unit   : Type                    -- Terminal object
  Void   : Type                    -- Initial object
  _*_    : Type → Type → Type      -- Product
  _+_    : Type → Type → Type      -- Coproduct (sum)
  _⇒[_]_ : Type → Quantity → Type → Type  -- Graded function arrow (QTT)
  Eff    : Type → Type → Type      -- Effectful morphism (D032)
  Fix    : Type → Type             -- Fixed point: Fix F ≅ F (Fix F)
  -- Base types for practical programming
  Int    : Type                    -- Machine integers
  Float  : Type                    -- IEEE 754 double-precision floats
  Str    : Type                    -- UTF-8 strings
  Buffer : Type                    -- Raw byte buffers
  TVar   : String → Type           -- Type variable (polymorphism)

infixr 30 _⇒[_]_
infixr 40 _+_
infixr 50 _*_

-- | Smart constructors for common quantity patterns
_⊸_ : Type → Type → Type  -- Linear function (quantity = 1)
A ⊸ B = A ⇒[ One ] B

_⇒_ : Type → Type → Type  -- Unrestricted function (quantity = ω)
A ⇒ B = A ⇒[ Many ] B

_⇒₀_ : Type → Type → Type  -- Erased function (quantity = 0)
A ⇒₀ B = A ⇒[ Zero ] B

infixr 30 _⊸_
infixr 30 _⇒_
infixr 30 _⇒₀_

-- | IO type alias (D032)
-- IO A is sugar for Eff Unit A (effectful computation producing A)
IO : Type → Type
IO A = Eff Unit A

------------------------------------------------------------------------
-- Decidable equality for Type
------------------------------------------------------------------------

_≟T_ : (A B : Type) → Dec (A ≡ B)
Unit ≟T Unit = yes refl
Void ≟T Void = yes refl
Int ≟T Int = yes refl
Float ≟T Float = yes refl
Str ≟T Str = yes refl
Buffer ≟T Buffer = yes refl
(A₁ * B₁) ≟T (A₂ * B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬q = no λ { refl → ¬q refl }
(A₁ + B₁) ≟T (A₂ + B₂) with A₁ ≟T A₂ | B₁ ≟T B₂
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
(TVar x) ≟T (TVar y) with x ≟S y
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
-- All other combinations are unequal
Unit ≟T Void = no λ ()
Unit ≟T Int = no λ ()
Unit ≟T Float = no λ ()
Unit ≟T Str = no λ ()
Unit ≟T Buffer = no λ ()
Unit ≟T (_ * _) = no λ ()
Unit ≟T (_ + _) = no λ ()
Unit ≟T (_ ⇒[ _ ] _) = no λ ()
Unit ≟T Eff _ _ = no λ ()
Unit ≟T Fix _ = no λ ()
Unit ≟T TVar _ = no λ ()
Void ≟T Unit = no λ ()
Void ≟T Int = no λ ()
Void ≟T Float = no λ ()
Void ≟T Str = no λ ()
Void ≟T Buffer = no λ ()
Void ≟T (_ * _) = no λ ()
Void ≟T (_ + _) = no λ ()
Void ≟T (_ ⇒[ _ ] _) = no λ ()
Void ≟T Eff _ _ = no λ ()
Void ≟T Fix _ = no λ ()
Void ≟T TVar _ = no λ ()
Int ≟T Unit = no λ ()
Int ≟T Void = no λ ()
Int ≟T Float = no λ ()
Int ≟T Str = no λ ()
Int ≟T Buffer = no λ ()
Int ≟T (_ * _) = no λ ()
Int ≟T (_ + _) = no λ ()
Int ≟T (_ ⇒[ _ ] _) = no λ ()
Int ≟T Eff _ _ = no λ ()
Int ≟T Fix _ = no λ ()
Int ≟T TVar _ = no λ ()
Float ≟T Unit = no λ ()
Float ≟T Void = no λ ()
Float ≟T Int = no λ ()
Float ≟T Str = no λ ()
Float ≟T Buffer = no λ ()
Float ≟T (_ * _) = no λ ()
Float ≟T (_ + _) = no λ ()
Float ≟T (_ ⇒[ _ ] _) = no λ ()
Float ≟T Eff _ _ = no λ ()
Float ≟T Fix _ = no λ ()
Float ≟T TVar _ = no λ ()
Str ≟T Unit = no λ ()
Str ≟T Void = no λ ()
Str ≟T Int = no λ ()
Str ≟T Float = no λ ()
Str ≟T Buffer = no λ ()
Str ≟T (_ * _) = no λ ()
Str ≟T (_ + _) = no λ ()
Str ≟T (_ ⇒[ _ ] _) = no λ ()
Str ≟T Eff _ _ = no λ ()
Str ≟T Fix _ = no λ ()
Str ≟T TVar _ = no λ ()
Buffer ≟T Unit = no λ ()
Buffer ≟T Void = no λ ()
Buffer ≟T Int = no λ ()
Buffer ≟T Float = no λ ()
Buffer ≟T Str = no λ ()
Buffer ≟T (_ * _) = no λ ()
Buffer ≟T (_ + _) = no λ ()
Buffer ≟T (_ ⇒[ _ ] _) = no λ ()
Buffer ≟T Eff _ _ = no λ ()
Buffer ≟T Fix _ = no λ ()
Buffer ≟T TVar _ = no λ ()
(_ * _) ≟T Unit = no λ ()
(_ * _) ≟T Void = no λ ()
(_ * _) ≟T Int = no λ ()
(_ * _) ≟T Float = no λ ()
(_ * _) ≟T Str = no λ ()
(_ * _) ≟T Buffer = no λ ()
(_ * _) ≟T (_ + _) = no λ ()
(_ * _) ≟T (_ ⇒[ _ ] _) = no λ ()
(_ * _) ≟T Eff _ _ = no λ ()
(_ * _) ≟T Fix _ = no λ ()
(_ * _) ≟T TVar _ = no λ ()
(_ + _) ≟T Unit = no λ ()
(_ + _) ≟T Void = no λ ()
(_ + _) ≟T Int = no λ ()
(_ + _) ≟T Float = no λ ()
(_ + _) ≟T Str = no λ ()
(_ + _) ≟T Buffer = no λ ()
(_ + _) ≟T (_ * _) = no λ ()
(_ + _) ≟T (_ ⇒[ _ ] _) = no λ ()
(_ + _) ≟T Eff _ _ = no λ ()
(_ + _) ≟T Fix _ = no λ ()
(_ + _) ≟T TVar _ = no λ ()
(_ ⇒[ _ ] _) ≟T Unit = no λ ()
(_ ⇒[ _ ] _) ≟T Void = no λ ()
(_ ⇒[ _ ] _) ≟T Int = no λ ()
(_ ⇒[ _ ] _) ≟T Float = no λ ()
(_ ⇒[ _ ] _) ≟T Str = no λ ()
(_ ⇒[ _ ] _) ≟T Buffer = no λ ()
(_ ⇒[ _ ] _) ≟T (_ * _) = no λ ()
(_ ⇒[ _ ] _) ≟T (_ + _) = no λ ()
(_ ⇒[ _ ] _) ≟T Eff _ _ = no λ ()
(_ ⇒[ _ ] _) ≟T Fix _ = no λ ()
(_ ⇒[ _ ] _) ≟T TVar _ = no λ ()
Eff _ _ ≟T Unit = no λ ()
Eff _ _ ≟T Void = no λ ()
Eff _ _ ≟T Int = no λ ()
Eff _ _ ≟T Float = no λ ()
Eff _ _ ≟T Str = no λ ()
Eff _ _ ≟T Buffer = no λ ()
Eff _ _ ≟T (_ * _) = no λ ()
Eff _ _ ≟T (_ + _) = no λ ()
Eff _ _ ≟T (_ ⇒[ _ ] _) = no λ ()
Eff _ _ ≟T Fix _ = no λ ()
Eff _ _ ≟T TVar _ = no λ ()
Fix _ ≟T Unit = no λ ()
Fix _ ≟T Void = no λ ()
Fix _ ≟T Int = no λ ()
Fix _ ≟T Float = no λ ()
Fix _ ≟T Str = no λ ()
Fix _ ≟T Buffer = no λ ()
Fix _ ≟T (_ * _) = no λ ()
Fix _ ≟T (_ + _) = no λ ()
Fix _ ≟T (_ ⇒[ _ ] _) = no λ ()
Fix _ ≟T Eff _ _ = no λ ()
Fix _ ≟T TVar _ = no λ ()
TVar _ ≟T Unit = no λ ()
TVar _ ≟T Void = no λ ()
TVar _ ≟T Int = no λ ()
TVar _ ≟T Float = no λ ()
TVar _ ≟T Str = no λ ()
TVar _ ≟T Buffer = no λ ()
TVar _ ≟T (_ * _) = no λ ()
TVar _ ≟T (_ + _) = no λ ()
TVar _ ≟T (_ ⇒[ _ ] _) = no λ ()
TVar _ ≟T Eff _ _ = no λ ()
TVar _ ≟T Fix _ = no λ ()
