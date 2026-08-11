-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
-- Note: `Zero *q _ = Zero` keeps the first arg's case-tree branch as
-- a single clause, preserving `Zero *q q ≡ Zero` for any `q` (and
-- avoiding fully-enumerated reduction loss). The reverse direction
-- `_ *q Zero ≡ Zero` is NOT preserved here — switching that to a
-- catch-all would re-introduce overlap. Downstream proofs needing
-- the right-zero-absorb law should reduce by case-splitting `q`.
_*q_ : Quantity → Quantity → Quantity
Zero  *q _     = Zero
One   *q Zero  = Zero
One   *q One   = One
One   *q Many  = Many
Many  *q Zero  = Zero
Many  *q One   = Many
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
-- Note: `Zero ≤q _ = true` keeps the first arg's case-tree branch
-- as a single clause, preserving the definitional equality
-- `Zero ≤q q ≡ true` for any `q`. Switching to fully-enumerated
-- `Zero ≤q Zero/One/Many = true` would lose this reduction and
-- break downstream proofs that pattern-match on this judgment.
_≤q_ : Quantity → Quantity → Bool
Zero  ≤q _     = true
One   ≤q Zero  = false
One   ≤q One   = true
One   ≤q Many  = true
Many  ≤q Zero  = false
Many  ≤q One   = false
Many  ≤q Many  = true

-- | Show function for Quantity (for error messages)
showQuantity : Quantity → String
showQuantity Zero = "0"
showQuantity One  = "1"
showQuantity Many = "ω"

------------------------------------------------------------------------
-- Plan 0.5.1: Arrow Kinds — Orthogonal Quantity × Purity
------------------------------------------------------------------------
--
-- An arrow type `A ⇒ B` in Once carries two independent annotations:
--
--   * Quantity (from QTT): tracks how many times the arrow's input
--     is consumed. Zero / One / Many.
--   * Purity (from D032): tracks whether the arrow's execution has
--     observable side effects. pure / eff.
--
-- These are **categorically independent** annotations on the same
-- exponential object. No structural law couples them; all four
-- combinations are coherent morphism types.
--
-- `ArrowKind` packages both annotations into a single record. This
-- replaces the earlier design where `Eff A B` was a distinct Type
-- constructor and `A ⇒[q] B` carried only the quantity — that design
-- had redundant type-level tagging (Eff duplicated the information
-- the kind could carry) and foreclosed linear effects by omission.
--
-- See plan 0.5.1 for the full refactor design.

data Purity : Set where
  pure : Purity   -- No observable side effects
  eff  : Purity   -- Effectful (D032: arrow-based effects)

-- | Show function for Purity
showPurity : Purity → String
showPurity pure = "pure"
showPurity eff  = "eff"

record ArrowKind : Set where
  constructor mk-kind
  field
    quantity : Quantity
    purity   : Purity

open ArrowKind public

-- | Show function for ArrowKind
showArrowKind : ArrowKind → String
showArrowKind (mk-kind q p) = showQuantity q ++ "," ++ showPurity p

-- | Common ArrowKind values (conveniences)
pureK : Quantity → ArrowKind
pureK q = mk-kind q pure

effK : ArrowKind
effK = mk-kind Many eff

-- | Purity join (Plan 0.36 Phase 1): the 2-point lattice `pure ≤ eff`.
-- Composition of morphisms takes the join of their grades — `pure` is the
-- unit (a pure factor adds no effect), `eff` absorbs. This is D032's
-- single-category "uniform composition": one composition, the grade is a
-- tracked property, not a separate structure.
_⊔p_ : Purity → Purity → Purity
pure ⊔p p = p
eff  ⊔p _ = eff

infixr 5 _⊔p_

-- | Decidable equality on Purity (plan 0.5.1)
_≟p_ : (p₁ p₂ : Purity) → Dec (p₁ ≡ p₂)
pure ≟p pure = yes refl
pure ≟p eff  = no (λ ())
eff  ≟p pure = no (λ ())
eff  ≟p eff  = yes refl

-- | Decidable equality on ArrowKind (plan 0.5.1)
≟k-aux : ∀ {q₁ q₂ p₁ p₂}
       → Dec (q₁ ≡ q₂) → Dec (p₁ ≡ p₂)
       → Dec (mk-kind q₁ p₁ ≡ mk-kind q₂ p₂)
≟k-aux (yes refl) (yes refl) = yes refl
≟k-aux (yes refl) (no ¬p)    = no λ { refl → ¬p refl }
≟k-aux (no ¬q)    (yes _)    = no λ { refl → ¬q refl }
≟k-aux (no ¬q)    (no _)     = no λ { refl → ¬q refl }

_≟k_ : (k₁ k₂ : ArrowKind) → Dec (k₁ ≡ k₂)
mk-kind q₁ p₁ ≟k mk-kind q₂ p₂ = ≟k-aux (q₁ ≟q q₂) (p₁ ≟p p₂)

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
    -- Kinded function arrow: single exponential with ArrowKind carrying
    -- both quantity (QTT) and purity (D032) as orthogonal annotations.
    -- Plan 0.5.1 unified `_⇒[_]_` (was Quantity-parameterized) and
    -- `Eff` (was a distinct constructor) under this single type former.
    _⇒[_]_ : Type → ArrowKind → Type → Type
    -- Polynomial functor fixed points (OCP-0003: total/productive)
    μ-type : Functor → Type          -- Initial algebra (inductive, total)
    ν-type : Functor → Type          -- Final coalgebra (coinductive, productive)
    -- Base types for practical programming
    Int    : Type                    -- Machine integers
    Float  : Type                    -- IEEE 754 double-precision floats
    Str    : Type                    -- UTF-8 strings
    Buffer : Type                    -- Raw byte buffers

infixr 40 _⊕_
infixr 50 _⊗_

infixr 30 _⇒[_]_
infixr 40 _+_
infixr 50 _*_

-- | Smart constructors for common quantity patterns
_⊸_ : Type → Type → Type  -- Linear function (quantity = 1)
A ⊸ B = A ⇒[ mk-kind One pure ] B

_⇒_ : Type → Type → Type  -- Unrestricted function (quantity = ω)
A ⇒ B = A ⇒[ mk-kind Many pure ] B

_⇒₀_ : Type → Type → Type  -- Erased function (quantity = 0)
A ⇒₀ B = A ⇒[ mk-kind Zero pure ] B

infixr 30 _⊸_
infixr 30 _⇒_
infixr 30 _⇒₀_

-- | Is this type the terminal `Unit`? A LOW-level decision (so SD's
-- `arrow-info` and the elaborator's `ext-resolved-info` can BOTH dispatch on
-- the same `Dec`, without SD importing the elaborator). The codomain-is-Unit
-- check is what `EffectShape`'s `Emits`/`Halts` coherence needs; sharing the
-- one decision keeps the masquerade a single case-split rather than an
-- 11-constructor enumeration. ([[feedback_with_clauses_painful]] — the
-- constructor-pattern analogue: dispatch on a reducible decision, not a
-- scrutinee opaque to the proof's variables.)
isUnit? : (T : Type) → Dec (T ≡ Unit)
isUnit? Unit          = yes refl
isUnit? Void          = no (λ ())
isUnit? (_ * _)       = no (λ ())
isUnit? (_ + _)       = no (λ ())
isUnit? (_ ⇒[ _ ] _)  = no (λ ())
isUnit? (μ-type _)    = no (λ ())
isUnit? (ν-type _)    = no (λ ())
isUnit? Int           = no (λ ())
isUnit? Float         = no (λ ())
isUnit? Str           = no (λ ())
isUnit? Buffer        = no (λ ())

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
-- FitsInReg (Plan 0.2.4.5)
--
-- A type satisfies `FitsInReg A` iff a value of type A fits in a
-- single machine register (one word). After Plan 0.2.4.5 the legacy
-- `IsPrimitive` predicate has been retired in favour of FitsInReg
-- everywhere; Unit is erased throughout the IR semantics rather than
-- carrying a register slot.
--
-- Excluded from FitsInReg (deliberately):
--   - Unit: erased entirely; carries no information; not register-
--           tracked.
--   - Str, Buffer: 16-byte fat (data-ptr + len); structurally
--           compound 2-slot records, not register-fittable.
--
-- Used to gate the `InReg : Reg → ValueLocation` constructor (Plan
-- 0.2.4.5 D4): only `FitsInReg`-typed values may be register-
-- resident. Compounds always live at `AtStack` / `AtDynamic`.
------------------------------------------------------------------------

data FitsInReg : Type → Set where
  fits-int   : FitsInReg Int
  fits-float : FitsInReg Float

-- | Decider for `FitsInReg` (Plan 0.26). The single point in the
-- codebase that pattern-matches on `Type` constructors for the
-- "register-resident" classification — downstream consumers (CCC's
-- per-class SigOp dispatch in `SMCore`/`IRTraceCorrect`) import
-- `FitsInReg` + `fits-in-reg?` and never name primitive type
-- constructors themselves.
fits-in-reg? : (B : Type) → Maybe (FitsInReg B)
fits-in-reg? Int   = just fits-int
fits-in-reg? Float = just fits-float
fits-in-reg? _     = nothing

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
  showType (A ⇒[ mk-kind q pure ] B) = "(" ++ showType A ++ " " ++ showQuantity q ++ "→ " ++ showType B ++ ")"
  showType (A ⇒[ mk-kind _ eff ] B)  = "Eff " ++ showType A ++ " " ++ showType B
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
-- optimizer's fully-proved status (plan 0.2.5 rationale).
-- `PolyType` is a *separate* data type that mirrors `Type` plus a
-- `PTVar` constructor, used strictly at the parser/signature boundary
-- for user-declared polymorphic signatures like `swap : a * b → b * a`.
--
-- Data flow (plan 0.6 Phase B/C):
--
--   parser returns PolyType in DTypeSig / DSignature
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
  extractGround (A P⇒[ q ] B)    (gA , gB) = extractGround A gA ⇒[ mk-kind q pure ] extractGround B gB
  extractGround (PEff A B)       (gA , gB) = extractGround A gA ⇒[ mk-kind Many eff ] extractGround B gB
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
  embed (A ⇒[ mk-kind q pure ] B) = embed A P⇒[ q ] embed B
  embed (A ⇒[ mk-kind _ eff ] B)  = PEff (embed A) (embed B)
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

-- Helper: combine two Ground witnesses (no with-block).
both-ground : ∀ {X Y : Set} → X ⊎ ⊤ → Y ⊎ ⊤ → (X × Y) ⊎ ⊤
both-ground (inj₁ x) (inj₁ y) = inj₁ (x , y)
both-ground (inj₁ _) (inj₂ _) = inj₂ tt
both-ground (inj₂ _) (inj₁ _) = inj₂ tt
both-ground (inj₂ _) (inj₂ _) = inj₂ tt

mutual
  isGroundF : (F : PolyFunctor) → (GroundF F) ⊎ ⊤
  isGroundF (PK A)    = isGround A          -- GroundF (PK A) = Ground A
  isGroundF PId       = inj₁ tt
  isGroundF (F P⊕ G)  = both-ground (isGroundF F) (isGroundF G)
  isGroundF (F P⊗ G)  = both-ground (isGroundF F) (isGroundF G)

  isGround : (A : PolyType) → (Ground A) ⊎ ⊤
  isGround PUnit          = inj₁ tt
  isGround PVoid          = inj₁ tt
  isGround (A P* B)       = both-ground (isGround A) (isGround B)
  isGround (A P+ B)       = both-ground (isGround A) (isGround B)
  isGround (A P⇒[ _ ] B)  = both-ground (isGround A) (isGround B)
  isGround (PEff A B)     = both-ground (isGround A) (isGround B)
  isGround (Pμ-type F)    = isGroundF F     -- Ground (Pμ-type F) = GroundF F
  isGround (Pν-type F)    = isGroundF F     -- Ground (Pν-type F) = GroundF F
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

------------------------------------------------------------------------
-- Bool-valued Type / Functor equality
------------------------------------------------------------------------
-- Used by `instantiate` for the TVar-consistency check. Decidable
-- equality lives in `Once.TypeCheck.Elaborate._≟T_` (richer form,
-- returns Dec with refl evidence); this simpler Bool version avoids
-- the upward dependency from Type → Elaborate. Plan 0.6.2 Phase 1.

open Data.Bool using (_∧_)

quantityEqBool : Quantity → Quantity → Bool
quantityEqBool Zero Zero = true
quantityEqBool Zero One  = false
quantityEqBool Zero Many = false
quantityEqBool One  Zero = false
quantityEqBool One  One  = true
quantityEqBool One  Many = false
quantityEqBool Many Zero = false
quantityEqBool Many One  = false
quantityEqBool Many Many = true

purityEqBool : Purity → Purity → Bool
purityEqBool pure pure = true
purityEqBool pure eff  = false
purityEqBool eff  pure = false
purityEqBool eff  eff  = true

mutual
  typeEqBool : Type → Type → Bool
  typeEqBool Unit Unit = true
  typeEqBool Unit Void = false
  typeEqBool Unit (_ * _) = false
  typeEqBool Unit (_ + _) = false
  typeEqBool Unit (_ ⇒[ _ ] _) = false
  typeEqBool Unit (μ-type _) = false
  typeEqBool Unit (ν-type _) = false
  typeEqBool Unit Int = false
  typeEqBool Unit Float = false
  typeEqBool Unit Str = false
  typeEqBool Unit Buffer = false
  typeEqBool Void Unit = false
  typeEqBool Void Void = true
  typeEqBool Void (_ * _) = false
  typeEqBool Void (_ + _) = false
  typeEqBool Void (_ ⇒[ _ ] _) = false
  typeEqBool Void (μ-type _) = false
  typeEqBool Void (ν-type _) = false
  typeEqBool Void Int = false
  typeEqBool Void Float = false
  typeEqBool Void Str = false
  typeEqBool Void Buffer = false
  typeEqBool (_ * _) Unit = false
  typeEqBool (_ * _) Void = false
  typeEqBool (a * b) (a' * b') = typeEqBool a a' ∧ typeEqBool b b'
  typeEqBool (_ * _) (_ + _) = false
  typeEqBool (_ * _) (_ ⇒[ _ ] _) = false
  typeEqBool (_ * _) (μ-type _) = false
  typeEqBool (_ * _) (ν-type _) = false
  typeEqBool (_ * _) Int = false
  typeEqBool (_ * _) Float = false
  typeEqBool (_ * _) Str = false
  typeEqBool (_ * _) Buffer = false
  typeEqBool (_ + _) Unit = false
  typeEqBool (_ + _) Void = false
  typeEqBool (_ + _) (_ * _) = false
  typeEqBool (a + b) (a' + b') = typeEqBool a a' ∧ typeEqBool b b'
  typeEqBool (_ + _) (_ ⇒[ _ ] _) = false
  typeEqBool (_ + _) (μ-type _) = false
  typeEqBool (_ + _) (ν-type _) = false
  typeEqBool (_ + _) Int = false
  typeEqBool (_ + _) Float = false
  typeEqBool (_ + _) Str = false
  typeEqBool (_ + _) Buffer = false
  typeEqBool (_ ⇒[ _ ] _) Unit = false
  typeEqBool (_ ⇒[ _ ] _) Void = false
  typeEqBool (_ ⇒[ _ ] _) (_ * _) = false
  typeEqBool (_ ⇒[ _ ] _) (_ + _) = false
  typeEqBool (a ⇒[ mk-kind q p ] b) (a' ⇒[ mk-kind q' p' ] b') =
    quantityEqBool q q' ∧ purityEqBool p p' ∧ typeEqBool a a' ∧ typeEqBool b b'
  typeEqBool (_ ⇒[ _ ] _) (μ-type _) = false
  typeEqBool (_ ⇒[ _ ] _) (ν-type _) = false
  typeEqBool (_ ⇒[ _ ] _) Int = false
  typeEqBool (_ ⇒[ _ ] _) Float = false
  typeEqBool (_ ⇒[ _ ] _) Str = false
  typeEqBool (_ ⇒[ _ ] _) Buffer = false
  typeEqBool (μ-type _) Unit = false
  typeEqBool (μ-type _) Void = false
  typeEqBool (μ-type _) (_ * _) = false
  typeEqBool (μ-type _) (_ + _) = false
  typeEqBool (μ-type _) (_ ⇒[ _ ] _) = false
  typeEqBool (μ-type f) (μ-type f') = functorEqBool f f'
  typeEqBool (μ-type _) (ν-type _) = false
  typeEqBool (μ-type _) Int = false
  typeEqBool (μ-type _) Float = false
  typeEqBool (μ-type _) Str = false
  typeEqBool (μ-type _) Buffer = false
  typeEqBool (ν-type _) Unit = false
  typeEqBool (ν-type _) Void = false
  typeEqBool (ν-type _) (_ * _) = false
  typeEqBool (ν-type _) (_ + _) = false
  typeEqBool (ν-type _) (_ ⇒[ _ ] _) = false
  typeEqBool (ν-type _) (μ-type _) = false
  typeEqBool (ν-type f) (ν-type f') = functorEqBool f f'
  typeEqBool (ν-type _) Int = false
  typeEqBool (ν-type _) Float = false
  typeEqBool (ν-type _) Str = false
  typeEqBool (ν-type _) Buffer = false
  typeEqBool Int Unit = false
  typeEqBool Int Void = false
  typeEqBool Int (_ * _) = false
  typeEqBool Int (_ + _) = false
  typeEqBool Int (_ ⇒[ _ ] _) = false
  typeEqBool Int (μ-type _) = false
  typeEqBool Int (ν-type _) = false
  typeEqBool Int Int = true
  typeEqBool Int Float = false
  typeEqBool Int Str = false
  typeEqBool Int Buffer = false
  typeEqBool Float Unit = false
  typeEqBool Float Void = false
  typeEqBool Float (_ * _) = false
  typeEqBool Float (_ + _) = false
  typeEqBool Float (_ ⇒[ _ ] _) = false
  typeEqBool Float (μ-type _) = false
  typeEqBool Float (ν-type _) = false
  typeEqBool Float Int = false
  typeEqBool Float Float = true
  typeEqBool Float Str = false
  typeEqBool Float Buffer = false
  typeEqBool Str Unit = false
  typeEqBool Str Void = false
  typeEqBool Str (_ * _) = false
  typeEqBool Str (_ + _) = false
  typeEqBool Str (_ ⇒[ _ ] _) = false
  typeEqBool Str (μ-type _) = false
  typeEqBool Str (ν-type _) = false
  typeEqBool Str Int = false
  typeEqBool Str Float = false
  typeEqBool Str Str = true
  typeEqBool Str Buffer = false
  typeEqBool Buffer Unit = false
  typeEqBool Buffer Void = false
  typeEqBool Buffer (_ * _) = false
  typeEqBool Buffer (_ + _) = false
  typeEqBool Buffer (_ ⇒[ _ ] _) = false
  typeEqBool Buffer (μ-type _) = false
  typeEqBool Buffer (ν-type _) = false
  typeEqBool Buffer Int = false
  typeEqBool Buffer Float = false
  typeEqBool Buffer Str = false
  typeEqBool Buffer Buffer = true

  functorEqBool : Functor → Functor → Bool
  functorEqBool (K a) (K a') = typeEqBool a a'
  functorEqBool (K _) Id = false
  functorEqBool (K _) (_ ⊕ _) = false
  functorEqBool (K _) (_ ⊗ _) = false
  functorEqBool Id (K _) = false
  functorEqBool Id Id = true
  functorEqBool Id (_ ⊕ _) = false
  functorEqBool Id (_ ⊗ _) = false
  functorEqBool (_ ⊕ _) (K _) = false
  functorEqBool (_ ⊕ _) Id = false
  functorEqBool (f ⊕ g) (f' ⊕ g') = functorEqBool f f' ∧ functorEqBool g g'
  functorEqBool (_ ⊕ _) (_ ⊗ _) = false
  functorEqBool (_ ⊗ _) (K _) = false
  functorEqBool (_ ⊗ _) Id = false
  functorEqBool (_ ⊗ _) (_ ⊕ _) = false
  functorEqBool (f ⊗ g) (f' ⊗ g') = functorEqBool f f' ∧ functorEqBool g g'

------------------------------------------------------------------------
-- PolyType ↔ Type structural instantiation
------------------------------------------------------------------------
-- Plan 0.6.2 Phase 1 (load-bearing POC for Option C of D044's
-- follow-up). Given a PolyType schema with `PTVar` type variables
-- and a candidate ground Type, produces a TVar → Type substitution
-- that makes the schema match the ground type, or `nothing` if the
-- shapes don't line up or a TVar is bound to two distinct types.
--
-- D007-compatible: structural template matching, not unification.
-- No meta-variables. Total function.

open import Data.List using (List; []; _∷_)
open import Data.Product using () renaming (_,_ to _,,_)

Subst : Set
Subst = List (String ×' Type)
  where
    _×'_ = _×_    -- bring product into scope under a local alias
    open Data.Product using (_×_; _,_)

lookupSubst : String → Subst → Maybe Type
lookupSubst _ [] = nothing
lookupSubst x ((y , t) ∷ rest) with Data.String._≟_ x y
  where open import Data.String
... | yes _ = just t
... | no _  = lookupSubst x rest

-- | Extend substitution with `(x, t)`; returns `nothing` if `x` was
-- already bound to a different type.
extendSubst : String → Type → Subst → Maybe Subst
extendSubst x t s with lookupSubst x s
... | just t' = if typeEqBool t t' then just s else nothing
    where open Data.Bool using (if_then_else_)
... | nothing = just ((x , t) ∷ s)

-- Maybe-handling helpers (no-with form).

maybe-bind : ∀ {A B : Set} → (A → Maybe B) → Maybe A → Maybe B
maybe-bind _ nothing  = nothing
maybe-bind f (just a) = f a

maybe-pair : ∀ {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
maybe-pair f (just a) (just b) = just (f a b)
maybe-pair _ (just _) nothing  = nothing
maybe-pair _ nothing  (just _) = nothing
maybe-pair _ nothing  nothing  = nothing

if-true-maybe : ∀ {A : Set} → Bool → Maybe A → Maybe A
if-true-maybe true  m = m
if-true-maybe false _ = nothing

-- | Instantiate a `PolyType` schema against a candidate ground `Type`.
-- The top-level wrapper runs the accumulator form with an empty
-- initial substitution.
mutual
  instantiate : PolyType → Type → Maybe Subst
  instantiate p t = instantiateAcc p t []

  instantiateAcc : PolyType → Type → Subst → Maybe Subst
  instantiateAcc (PTVar x)       t               s = extendSubst x t s
  instantiateAcc PUnit           Unit            s = just s
  instantiateAcc PVoid           Void            s = just s
  instantiateAcc PInt            Int             s = just s
  instantiateAcc PFloat          Float           s = just s
  instantiateAcc PStr            Str             s = just s
  instantiateAcc PBuffer         Buffer          s = just s
  instantiateAcc (A P* B)        (a * b)         s =
    maybe-bind (instantiateAcc B b) (instantiateAcc A a s)
  instantiateAcc (A P+ B)        (a + b)         s =
    maybe-bind (instantiateAcc B b) (instantiateAcc A a s)
  instantiateAcc (A P⇒[ q ] B)   (a ⇒[ mk-kind q' pure ] b)   s =
    if-true-maybe (quantityEqBool q q')
      (maybe-bind (instantiateAcc B b) (instantiateAcc A a s))
  instantiateAcc (PEff A B)      (a ⇒[ mk-kind _ eff ] b)     s =
    maybe-bind (instantiateAcc B b) (instantiateAcc A a s)
  instantiateAcc (Pμ-type F)     (μ-type f)      s = instantiateFunctor F f s
  instantiateAcc (Pν-type F)     (ν-type f)      s = instantiateFunctor F f s
  -- Shape mismatch on each PolyType constructor (no catch-all).
  instantiateAcc PUnit           Void            _ = nothing
  instantiateAcc PUnit           (_ * _)         _ = nothing
  instantiateAcc PUnit           (_ + _)         _ = nothing
  instantiateAcc PUnit           (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PUnit           (μ-type _)      _ = nothing
  instantiateAcc PUnit           (ν-type _)      _ = nothing
  instantiateAcc PUnit           Int             _ = nothing
  instantiateAcc PUnit           Float           _ = nothing
  instantiateAcc PUnit           Str             _ = nothing
  instantiateAcc PUnit           Buffer          _ = nothing
  instantiateAcc PVoid           Unit            _ = nothing
  instantiateAcc PVoid           (_ * _)         _ = nothing
  instantiateAcc PVoid           (_ + _)         _ = nothing
  instantiateAcc PVoid           (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PVoid           (μ-type _)      _ = nothing
  instantiateAcc PVoid           (ν-type _)      _ = nothing
  instantiateAcc PVoid           Int             _ = nothing
  instantiateAcc PVoid           Float           _ = nothing
  instantiateAcc PVoid           Str             _ = nothing
  instantiateAcc PVoid           Buffer          _ = nothing
  instantiateAcc (_ P* _)        Unit            _ = nothing
  instantiateAcc (_ P* _)        Void            _ = nothing
  instantiateAcc (_ P* _)        (_ + _)         _ = nothing
  instantiateAcc (_ P* _)        (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (_ P* _)        (μ-type _)      _ = nothing
  instantiateAcc (_ P* _)        (ν-type _)      _ = nothing
  instantiateAcc (_ P* _)        Int             _ = nothing
  instantiateAcc (_ P* _)        Float           _ = nothing
  instantiateAcc (_ P* _)        Str             _ = nothing
  instantiateAcc (_ P* _)        Buffer          _ = nothing
  instantiateAcc (_ P+ _)        Unit            _ = nothing
  instantiateAcc (_ P+ _)        Void            _ = nothing
  instantiateAcc (_ P+ _)        (_ * _)         _ = nothing
  instantiateAcc (_ P+ _)        (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (_ P+ _)        (μ-type _)      _ = nothing
  instantiateAcc (_ P+ _)        (ν-type _)      _ = nothing
  instantiateAcc (_ P+ _)        Int             _ = nothing
  instantiateAcc (_ P+ _)        Float           _ = nothing
  instantiateAcc (_ P+ _)        Str             _ = nothing
  instantiateAcc (_ P+ _)        Buffer          _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Unit            _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Void            _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (_ * _)         _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (_ + _)         _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (_ ⇒[ mk-kind _ eff ] _) _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (μ-type _)      _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   (ν-type _)      _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Int             _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Float           _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Str             _ = nothing
  instantiateAcc (_ P⇒[ _ ] _)   Buffer          _ = nothing
  instantiateAcc (PEff _ _)      Unit            _ = nothing
  instantiateAcc (PEff _ _)      Void            _ = nothing
  instantiateAcc (PEff _ _)      (_ * _)         _ = nothing
  instantiateAcc (PEff _ _)      (_ + _)         _ = nothing
  instantiateAcc (PEff _ _)      (_ ⇒[ mk-kind _ pure ] _) _ = nothing
  instantiateAcc (PEff _ _)      (μ-type _)      _ = nothing
  instantiateAcc (PEff _ _)      (ν-type _)      _ = nothing
  instantiateAcc (PEff _ _)      Int             _ = nothing
  instantiateAcc (PEff _ _)      Float           _ = nothing
  instantiateAcc (PEff _ _)      Str             _ = nothing
  instantiateAcc (PEff _ _)      Buffer          _ = nothing
  instantiateAcc (Pμ-type _)     Unit            _ = nothing
  instantiateAcc (Pμ-type _)     Void            _ = nothing
  instantiateAcc (Pμ-type _)     (_ * _)         _ = nothing
  instantiateAcc (Pμ-type _)     (_ + _)         _ = nothing
  instantiateAcc (Pμ-type _)     (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (Pμ-type _)     (ν-type _)      _ = nothing
  instantiateAcc (Pμ-type _)     Int             _ = nothing
  instantiateAcc (Pμ-type _)     Float           _ = nothing
  instantiateAcc (Pμ-type _)     Str             _ = nothing
  instantiateAcc (Pμ-type _)     Buffer          _ = nothing
  instantiateAcc (Pν-type _)     Unit            _ = nothing
  instantiateAcc (Pν-type _)     Void            _ = nothing
  instantiateAcc (Pν-type _)     (_ * _)         _ = nothing
  instantiateAcc (Pν-type _)     (_ + _)         _ = nothing
  instantiateAcc (Pν-type _)     (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc (Pν-type _)     (μ-type _)      _ = nothing
  instantiateAcc (Pν-type _)     Int             _ = nothing
  instantiateAcc (Pν-type _)     Float           _ = nothing
  instantiateAcc (Pν-type _)     Str             _ = nothing
  instantiateAcc (Pν-type _)     Buffer          _ = nothing
  instantiateAcc PInt            Unit            _ = nothing
  instantiateAcc PInt            Void            _ = nothing
  instantiateAcc PInt            (_ * _)         _ = nothing
  instantiateAcc PInt            (_ + _)         _ = nothing
  instantiateAcc PInt            (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PInt            (μ-type _)      _ = nothing
  instantiateAcc PInt            (ν-type _)      _ = nothing
  instantiateAcc PInt            Float           _ = nothing
  instantiateAcc PInt            Str             _ = nothing
  instantiateAcc PInt            Buffer          _ = nothing
  instantiateAcc PFloat          Unit            _ = nothing
  instantiateAcc PFloat          Void            _ = nothing
  instantiateAcc PFloat          (_ * _)         _ = nothing
  instantiateAcc PFloat          (_ + _)         _ = nothing
  instantiateAcc PFloat          (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PFloat          (μ-type _)      _ = nothing
  instantiateAcc PFloat          (ν-type _)      _ = nothing
  instantiateAcc PFloat          Int             _ = nothing
  instantiateAcc PFloat          Str             _ = nothing
  instantiateAcc PFloat          Buffer          _ = nothing
  instantiateAcc PStr            Unit            _ = nothing
  instantiateAcc PStr            Void            _ = nothing
  instantiateAcc PStr            (_ * _)         _ = nothing
  instantiateAcc PStr            (_ + _)         _ = nothing
  instantiateAcc PStr            (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PStr            (μ-type _)      _ = nothing
  instantiateAcc PStr            (ν-type _)      _ = nothing
  instantiateAcc PStr            Int             _ = nothing
  instantiateAcc PStr            Float           _ = nothing
  instantiateAcc PStr            Buffer          _ = nothing
  instantiateAcc PBuffer         Unit            _ = nothing
  instantiateAcc PBuffer         Void            _ = nothing
  instantiateAcc PBuffer         (_ * _)         _ = nothing
  instantiateAcc PBuffer         (_ + _)         _ = nothing
  instantiateAcc PBuffer         (_ ⇒[ _ ] _)    _ = nothing
  instantiateAcc PBuffer         (μ-type _)      _ = nothing
  instantiateAcc PBuffer         (ν-type _)      _ = nothing
  instantiateAcc PBuffer         Int             _ = nothing
  instantiateAcc PBuffer         Float           _ = nothing
  instantiateAcc PBuffer         Str             _ = nothing

  instantiateFunctor : PolyFunctor → Functor → Subst → Maybe Subst
  instantiateFunctor (PK A)    (K a)   s = instantiateAcc A a s
  instantiateFunctor PId       Id      s = just s
  instantiateFunctor (F P⊕ G) (f ⊕ g) s =
    maybe-bind (instantiateFunctor G g) (instantiateFunctor F f s)
  instantiateFunctor (F P⊗ G) (f ⊗ g) s =
    maybe-bind (instantiateFunctor G g) (instantiateFunctor F f s)
  instantiateFunctor (PK _)    Id      _ = nothing
  instantiateFunctor (PK _)    (_ ⊕ _) _ = nothing
  instantiateFunctor (PK _)    (_ ⊗ _) _ = nothing
  instantiateFunctor PId       (K _)   _ = nothing
  instantiateFunctor PId       (_ ⊕ _) _ = nothing
  instantiateFunctor PId       (_ ⊗ _) _ = nothing
  instantiateFunctor (_ P⊕ _)  (K _)   _ = nothing
  instantiateFunctor (_ P⊕ _)  Id      _ = nothing
  instantiateFunctor (_ P⊕ _)  (_ ⊗ _) _ = nothing
  instantiateFunctor (_ P⊗ _)  (K _)   _ = nothing
  instantiateFunctor (_ P⊗ _)  Id      _ = nothing
  instantiateFunctor (_ P⊗ _)  (_ ⊕ _) _ = nothing

-- | Apply a substitution to a PolyType, producing a ground Type.
-- Returns `nothing` if the PolyType contains a `PTVar` not covered
-- by the substitution (shouldn't happen after a successful
-- `instantiate`, but we return Maybe for safety rather than assuming).
mutual
  applySubst : Subst → PolyType → Maybe Type
  applySubst s (PTVar x)       = lookupSubst x s
  applySubst _ PUnit           = just Unit
  applySubst _ PVoid           = just Void
  applySubst _ PInt            = just Int
  applySubst _ PFloat          = just Float
  applySubst _ PStr            = just Str
  applySubst _ PBuffer         = just Buffer
  applySubst s (A P* B)        = maybe-pair _*_ (applySubst s A) (applySubst s B)
  applySubst s (A P+ B)        = maybe-pair _+_ (applySubst s A) (applySubst s B)
  applySubst s (A P⇒[ q ] B)   =
    maybe-pair (λ a b → a ⇒[ mk-kind q pure ] b) (applySubst s A) (applySubst s B)
  applySubst s (PEff A B)      =
    maybe-pair (λ a b → a ⇒[ mk-kind Many eff ] b) (applySubst s A) (applySubst s B)
  applySubst s (Pμ-type F)     = maybe-bind (λ f → just (μ-type f)) (applySubstFunctor s F)
  applySubst s (Pν-type F)     = maybe-bind (λ f → just (ν-type f)) (applySubstFunctor s F)

  applySubstFunctor : Subst → PolyFunctor → Maybe Functor
  applySubstFunctor s (PK A)   = maybe-bind (λ a → just (K a)) (applySubst s A)
  applySubstFunctor _ PId      = just Id
  applySubstFunctor s (F P⊕ G) =
    maybe-pair _⊕_ (applySubstFunctor s F) (applySubstFunctor s G)
  applySubstFunctor s (F P⊗ G) =
    maybe-pair _⊗_ (applySubstFunctor s F) (applySubstFunctor s G)

-- | For a polymorphic arrow schema `A ⇒[q] B` and a known ground
-- domain `Adom`, compute the ground codomain by matching `A`
-- against `Adom` (yielding a substitution) and applying it to `B`.
-- Plan 0.6.2 Phase 3b: the load-bearing primitive for classifier
-- helpers (e.g. `checkCompose`) that know one side of a poly
-- sub-expression's arrow type and need the other.
--
-- Returns `nothing` if the schema isn't an arrow, if the domain
-- doesn't match, or if the codomain still contains free TVars
-- after substitution (shouldn't happen with well-formed schemas).
schemaArrowCodomain : PolyType → Type → Maybe Type
schemaArrowCodomain (A P⇒[ _ ] B) domain =
  maybe-bind (λ subst → applySubst subst B) (instantiate A domain)
-- Schema is not an arrow → no codomain.
schemaArrowCodomain (PTVar _)    _ = nothing
schemaArrowCodomain PUnit        _ = nothing
schemaArrowCodomain PVoid        _ = nothing
schemaArrowCodomain (_ P* _)     _ = nothing
schemaArrowCodomain (_ P+ _)     _ = nothing
schemaArrowCodomain (PEff _ _)   _ = nothing
schemaArrowCodomain (Pμ-type _)  _ = nothing
schemaArrowCodomain (Pν-type _)  _ = nothing
schemaArrowCodomain PInt         _ = nothing
schemaArrowCodomain PFloat       _ = nothing
schemaArrowCodomain PStr         _ = nothing
schemaArrowCodomain PBuffer      _ = nothing

