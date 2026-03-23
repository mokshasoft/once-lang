-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Type
--
-- Definition of types in the Once language.
-- These are the objects of a Cartesian Closed Category.
------------------------------------------------------------------------

module Once.Type where

open import Level using (Level)
open import Data.String using (String)
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
-- Types and Functors (Mutually Recursive)
------------------------------------------------------------------------
--
-- Types correspond to objects in a Cartesian Closed Category:
-- - Unit is the terminal object (1)
-- - Void is the initial object (0)
-- - _*_ is the categorical product (×)
-- - _+_ is the categorical coproduct (+)
-- - _⇒_ is the exponential object (function space, pure)
-- - Eff is the effectful morphism (D032: arrow-based effects)
-- - Fix is the fixed point (for recursive types)
--
-- Functors are polynomial type expressions with an explicit recursive
-- position, used by the structured recursion scheme IR constructors.
--
-- Additional base types for practical programming:
-- - Int is machine integers
-- - Float is IEEE 754 double-precision floats
-- - Str is UTF-8 strings
-- - Buffer is raw byte buffers
-- - TVar is a type variable (for polymorphism)
--

mutual
  -- | Functor codes (strictly positive type expressions)
  --
  -- K A    - Constant type (no recursion)
  -- Id     - Recursive position
  -- F ⊕ G  - Sum (coproduct)
  -- F ⊗ G  - Product
  --
  data Functor : Set where
    K    : Type → Functor           -- Constant
    Id   : Functor                  -- Recursive position
    _⊕_  : Functor → Functor → Functor  -- Sum
    _⊗_  : Functor → Functor → Functor  -- Product

  data Type : Set where
    -- Categorical structure
    Unit   : Type                    -- Terminal object
    Void   : Type                    -- Initial object
    _*_    : Type → Type → Type      -- Product
    _+_    : Type → Type → Type      -- Coproduct (sum)
    _⇒[_]_ : Type → Quantity → Type → Type  -- Graded function arrow (QTT)
    Eff    : Type → Type → Type      -- Effectful morphism (D032)
    -- Fix removed by OCP-0003: use μ-type/ν-type instead
    -- Polynomial functor fixed points (OCP-0003: total/productive)
    μ-type : Functor → Type          -- Initial algebra (inductive, total)
    ν-type : Functor → Type          -- Final coalgebra (coinductive, productive)
    -- Guarded functor values (OCP-0003: productive corecursion)
    -- GuardedT F A represents F-shaped values where recursive positions
    -- are "guarded" - each observation produces one F-layer before recursion.
    -- Used by Ana to enforce productivity at the type level.
    GuardedT : Functor → Type → Type
    -- Base types for practical programming
    Int    : Type                    -- Machine integers
    Float  : Type                    -- IEEE 754 double-precision floats
    Str    : Type                    -- UTF-8 strings
    Buffer : Type                    -- Raw byte buffers
    TVar   : String → Type           -- Type variable (polymorphism)

infixr 40 _⊕_
infixr 50 _⊗_

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
-- Type-Level Functor Interpretation
--
-- Interprets a Functor code as a Type → Type function.
-- Used by IR constructors for recursion schemes.
------------------------------------------------------------------------

-- | Interpret functor code at a carrier Type
--
-- ⟦ K A ⟧T X = A         (constant, ignores X)
-- ⟦ Id ⟧T X = X          (recursive position)
-- ⟦ F ⊕ G ⟧T X = ⟦ F ⟧T X + ⟦ G ⟧T X
-- ⟦ F ⊗ G ⟧T X = ⟦ F ⟧T X * ⟦ G ⟧T X
--
⟦_⟧T : Functor → Type → Type
⟦ K A ⟧T X = A
⟦ Id ⟧T X = X
⟦ F ⊕ G ⟧T X = ⟦ F ⟧T X + ⟦ G ⟧T X
⟦ F ⊗ G ⟧T X = ⟦ F ⟧T X * ⟦ G ⟧T X

------------------------------------------------------------------------
-- Common Functor Patterns
------------------------------------------------------------------------

-- | Natural numbers: Nat = μ (K Unit ⊕ Id)
NatF : Functor
NatF = K Unit ⊕ Id

-- | List A = μ (K Unit ⊕ K A ⊗ Id)
ListF : Type → Functor
ListF A = K Unit ⊕ (K A ⊗ Id)

-- | Binary tree: Tree A = μ (K A ⊕ Id ⊗ Id)
TreeF : Type → Functor
TreeF A = K A ⊕ (Id ⊗ Id)

------------------------------------------------------------------------
-- Primitive Type Evidence
------------------------------------------------------------------------

-- | Evidence that a type is a primitive (non-compound) type.
-- Used by backends to dispatch on primitive types.
data IsPrimitive : Type → Set where
  is-unit   : IsPrimitive Unit
  is-int    : IsPrimitive Int
  is-float  : IsPrimitive Float
  is-str    : IsPrimitive Str
  is-buffer : IsPrimitive Buffer