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
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

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

-- | Quantity maximum (per-branch upper bound)
--
-- Used for case analysis: exactly one branch runs, so the effective usage
-- at each position is the maximum over branches in the QTT lattice.
--
-- Lattice order: Zero ≤ One ≤ Many
--
-- - Zero ⊔q q = q
-- - q ⊔q Zero = q
-- - One ⊔q One = One
-- - One ⊔q Many = Many
-- - Many ⊔q _ = Many
--
_⊔q_ : Quantity → Quantity → Quantity
Zero ⊔q q    = q
One  ⊔q Zero = One
One  ⊔q One  = One
One  ⊔q Many = Many
Many ⊔q _    = Many

infixl 55 _⊔q_

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
--
-- Note: Type variables (TVar) are now in PolyType, not Type.
-- This separation enables clean decidable equality on Type and
-- simpler pattern matching in optimization functions.
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
    -- GuardedT removed: productivity follows from IR totality (see IR/Totality.agda)
    -- Base types for practical programming
    Int    : Type                    -- Machine integers
    Float  : Type                    -- IEEE 754 double-precision floats
    Str    : Type                    -- UTF-8 strings
    Buffer : Type                    -- Raw byte buffers
    -- TVar moved to PolyType (see below)

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

-- Note: IO sugar removed for clarity in error messages.
-- The parser desugars "IO A" to "Eff Unit A" at parse time.
-- Use Eff Unit A directly in Agda code.

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

------------------------------------------------------------------------
-- Type Pretty Printing
------------------------------------------------------------------------

-- | Convert types and functors to human-readable strings
-- Used for error messages
mutual
  showType : Type → String
  showType Unit = "Unit"
  showType Void = "Void"
  showType (A * B) = "(" ++ showType A ++ " * " ++ showType B ++ ")"
  showType (A + B) = "(" ++ showType A ++ " + " ++ showType B ++ ")"
  showType (A ⇒[ q ] B) = "(" ++ showType A ++ " " ++ showQuantity q ++ "→ " ++ showType B ++ ")"
  showType (Eff A B) = "Eff " ++ showType A ++ " " ++ showType B
  showType (μ-type F) = "μ " ++ showFunctor F
  showType (ν-type F) = "ν " ++ showFunctor F
  showType Int = "Int"
  showType Float = "Float"
  showType Str = "String"
  showType Buffer = "Buffer"

  showFunctor : Functor → String
  showFunctor (K A) = "(K " ++ showType A ++ ")"
  showFunctor Id = "Id"
  showFunctor (F ⊕ G) = "(" ++ showFunctor F ++ " ⊕ " ++ showFunctor G ++ ")"
  showFunctor (F ⊗ G) = "(" ++ showFunctor F ++ " ⊗ " ++ showFunctor G ++ ")"

------------------------------------------------------------------------
-- PolyType: Parser-boundary staging area for type variables
--
-- Ground `Type` carries no type variables — that invariant is
-- load-bearing for clean `_≟T_`, clean IR pattern-matching, and the
-- optimizer's postulate-free status (plan 0.2.5 rationale).
-- `PolyType` is a *separate* data type that mirrors `Type` plus a
-- `PTVar` constructor, used strictly at the parser/signature boundary
-- for user-declared polymorphic signatures like `swap : a * b → b * a`.
--
-- Data flow (plan 0.6 Phase B/C):
--
--   parser returns PolyType in DTypeSig / DPrimitive
--        ↓
--   extractFunctions projects PolyType → Type if Ground
--        ↓ (else: package TVars for Phase C monomorphization)
--   SExpr / IR / optimizer / semantics all see ground Type only
--
-- Nothing downstream of `extractFunctions` ever receives a `PTVar`.
-- The April-17 split's invariant is preserved.
------------------------------------------------------------------------

mutual
  data PolyFunctor : Set where
    PK   : PolyType → PolyFunctor
    PId  : PolyFunctor
    _P⊕_ : PolyFunctor → PolyFunctor → PolyFunctor
    _P⊗_ : PolyFunctor → PolyFunctor → PolyFunctor

  data PolyType : Set where
    -- Categorical structure
    PUnit   : PolyType
    PVoid   : PolyType
    _P*_    : PolyType → PolyType → PolyType
    _P+_    : PolyType → PolyType → PolyType
    _P⇒[_]_ : PolyType → Quantity → PolyType → PolyType
    PEff    : PolyType → PolyType → PolyType
    -- Polynomial functor fixed points
    Pμ-type : PolyFunctor → PolyType
    Pν-type : PolyFunctor → PolyType
    -- Base types
    PInt    : PolyType
    PFloat  : PolyType
    PStr    : PolyType
    PBuffer : PolyType
    -- Type variable (the whole reason this type exists)
    PTVar   : String → PolyType

infixr 40 _P⊕_
infixr 50 _P⊗_
infixr 30 _P⇒[_]_
infixr 40 _P+_
infixr 50 _P*_

------------------------------------------------------------------------
-- Ground predicate: this PolyType contains no TVars
--
-- `Ground A` is a proof that every subterm of `A` is a non-TVar
-- constructor. It's the precondition for the total projection
-- `extractGround : PolyType → Type` (Lambek-style: Ground is an
-- iso-class predicate; `extractGround` is its witness).
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

mutual
  GroundF : PolyFunctor → Set
  GroundF (PK A)   = Ground A
  GroundF PId      = ⊤
  GroundF (F P⊕ G) = GroundF F × GroundF G
  GroundF (F P⊗ G) = GroundF F × GroundF G

  Ground : PolyType → Set
  Ground PUnit           = ⊤
  Ground PVoid           = ⊤
  Ground (A P* B)        = Ground A × Ground B
  Ground (A P+ B)        = Ground A × Ground B
  Ground (A P⇒[ _ ] B)   = Ground A × Ground B
  Ground (PEff A B)      = Ground A × Ground B
  Ground (Pμ-type F)     = GroundF F
  Ground (Pν-type F)     = GroundF F
  Ground PInt            = ⊤
  Ground PFloat          = ⊤
  Ground PStr            = ⊤
  Ground PBuffer         = ⊤
  Ground (PTVar _)       = ⊥     -- the only non-Ground case

------------------------------------------------------------------------
-- Total projection PolyType → Type given Ground witness
------------------------------------------------------------------------

mutual
  extractGroundF : (F : PolyFunctor) → GroundF F → Functor
  extractGroundF (PK A) g          = K (extractGround A g)
  extractGroundF PId _             = Id
  extractGroundF (F P⊕ G) (gF , gG) = extractGroundF F gF ⊕ extractGroundF G gG
  extractGroundF (F P⊗ G) (gF , gG) = extractGroundF F gF ⊗ extractGroundF G gG

  extractGround : (A : PolyType) → Ground A → Type
  extractGround PUnit            _        = Unit
  extractGround PVoid            _        = Void
  extractGround (A P* B)         (gA , gB) = extractGround A gA * extractGround B gB
  extractGround (A P+ B)         (gA , gB) = extractGround A gA + extractGround B gB
  extractGround (A P⇒[ q ] B)    (gA , gB) = extractGround A gA ⇒[ q ] extractGround B gB
  extractGround (PEff A B)       (gA , gB) = Eff (extractGround A gA) (extractGround B gB)
  extractGround (Pμ-type F)      g        = μ-type (extractGroundF F g)
  extractGround (Pν-type F)      g        = ν-type (extractGroundF F g)
  extractGround PInt             _        = Int
  extractGround PFloat           _        = Float
  extractGround PStr             _        = Str
  extractGround PBuffer          _        = Buffer
  -- PTVar case is unreachable (its Ground = ⊥)

------------------------------------------------------------------------
-- Embedding Type → PolyType (always Ground by construction)
--
-- Lets existing ground `Type` values flow through the PolyType layer
-- when needed (e.g. alias expansion where the RHS was parsed as
-- Type already).
------------------------------------------------------------------------

mutual
  embedFunctor : Functor → PolyFunctor
  embedFunctor (K A)   = PK (embed A)
  embedFunctor Id      = PId
  embedFunctor (F ⊕ G) = embedFunctor F P⊕ embedFunctor G
  embedFunctor (F ⊗ G) = embedFunctor F P⊗ embedFunctor G

  embed : Type → PolyType
  embed Unit           = PUnit
  embed Void           = PVoid
  embed (A * B)        = embed A P* embed B
  embed (A + B)        = embed A P+ embed B
  embed (A ⇒[ q ] B)   = embed A P⇒[ q ] embed B
  embed (Eff A B)      = PEff (embed A) (embed B)
  embed (μ-type F)     = Pμ-type (embedFunctor F)
  embed (ν-type F)     = Pν-type (embedFunctor F)
  embed Int            = PInt
  embed Float          = PFloat
  embed Str            = PStr
  embed Buffer         = PBuffer

------------------------------------------------------------------------
-- Decidable Ground check
--
-- `isGround` lets callers ask "can this PolyType be projected to
-- Type?" without a dependent-type handstand. Returns the Ground
-- witness on success so `extractGround` can be called directly.
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)

mutual
  isGroundF : (F : PolyFunctor) → (GroundF F) ⊎ ⊤
  isGroundF (PK A) with isGround A
  ... | inj₁ gA = inj₁ gA
  ... | inj₂ _  = inj₂ tt
  isGroundF PId = inj₁ tt
  isGroundF (F P⊕ G) with isGroundF F | isGroundF G
  ... | inj₁ gF | inj₁ gG = inj₁ (gF , gG)
  ... | _       | _       = inj₂ tt
  isGroundF (F P⊗ G) with isGroundF F | isGroundF G
  ... | inj₁ gF | inj₁ gG = inj₁ (gF , gG)
  ... | _       | _       = inj₂ tt

  isGround : (A : PolyType) → (Ground A) ⊎ ⊤
  isGround PUnit        = inj₁ tt
  isGround PVoid        = inj₁ tt
  isGround (A P* B) with isGround A | isGround B
  ... | inj₁ gA | inj₁ gB = inj₁ (gA , gB)
  ... | _       | _       = inj₂ tt
  isGround (A P+ B) with isGround A | isGround B
  ... | inj₁ gA | inj₁ gB = inj₁ (gA , gB)
  ... | _       | _       = inj₂ tt
  isGround (A P⇒[ _ ] B) with isGround A | isGround B
  ... | inj₁ gA | inj₁ gB = inj₁ (gA , gB)
  ... | _       | _       = inj₂ tt
  isGround (PEff A B) with isGround A | isGround B
  ... | inj₁ gA | inj₁ gB = inj₁ (gA , gB)
  ... | _       | _       = inj₂ tt
  isGround (Pμ-type F) with isGroundF F
  ... | inj₁ g = inj₁ g
  ... | inj₂ _ = inj₂ tt
  isGround (Pν-type F) with isGroundF F
  ... | inj₁ g = inj₁ g
  ... | inj₂ _ = inj₂ tt
  isGround PInt         = inj₁ tt
  isGround PFloat       = inj₁ tt
  isGround PStr         = inj₁ tt
  isGround PBuffer      = inj₁ tt
  isGround (PTVar _)    = inj₂ tt

------------------------------------------------------------------------
-- PolyType Pretty Printing
------------------------------------------------------------------------

mutual
  showPolyType : PolyType → String
  showPolyType PUnit            = "Unit"
  showPolyType PVoid            = "Void"
  showPolyType (A P* B)         = "(" ++ showPolyType A ++ " * " ++ showPolyType B ++ ")"
  showPolyType (A P+ B)         = "(" ++ showPolyType A ++ " + " ++ showPolyType B ++ ")"
  showPolyType (A P⇒[ q ] B)    = "(" ++ showPolyType A ++ " " ++ showQuantity q ++ "→ " ++ showPolyType B ++ ")"
  showPolyType (PEff A B)       = "Eff " ++ showPolyType A ++ " " ++ showPolyType B
  showPolyType (Pμ-type F)      = "μ " ++ showPolyFunctor F
  showPolyType (Pν-type F)      = "ν " ++ showPolyFunctor F
  showPolyType PInt             = "Int"
  showPolyType PFloat           = "Float"
  showPolyType PStr             = "String"
  showPolyType PBuffer          = "Buffer"
  showPolyType (PTVar x)        = x

  showPolyFunctor : PolyFunctor → String
  showPolyFunctor (PK A)        = "(K " ++ showPolyType A ++ ")"
  showPolyFunctor PId           = "Id"
  showPolyFunctor (F P⊕ G)      = "(" ++ showPolyFunctor F ++ " ⊕ " ++ showPolyFunctor G ++ ")"
  showPolyFunctor (F P⊗ G)      = "(" ++ showPolyFunctor F ++ " ⊗ " ++ showPolyFunctor G ++ ")"

