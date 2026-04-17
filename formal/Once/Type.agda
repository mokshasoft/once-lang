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

------------------------------------------------------------------------
-- Polymorphic Types (for Type Inference)
------------------------------------------------------------------------
--
-- PolyType mirrors Type but includes TVar for type variables.
-- This separation enables:
-- 1. Clean decidable equality on Type (no TVar cases)
-- 2. Simpler pattern matching in optimization functions
-- 3. Clear phase separation: PolyType during inference, Type after
--
-- PolyFunctor is the polymorphic version of Functor.
--

mutual
  -- | Polymorphic functor codes
  data PolyFunctor : Set where
    PK   : PolyType → PolyFunctor
    PId  : PolyFunctor
    _P⊕_ : PolyFunctor → PolyFunctor → PolyFunctor
    _P⊗_ : PolyFunctor → PolyFunctor → PolyFunctor

  -- | Polymorphic types (includes type variables)
  data PolyType : Set where
    -- Categorical structure (mirrors Type)
    PUnit   : PolyType
    PVoid   : PolyType
    _P*_    : PolyType → PolyType → PolyType
    _P+_    : PolyType → PolyType → PolyType
    _P⇒[_]_ : PolyType → Quantity → PolyType → PolyType
    PEff    : PolyType → PolyType → PolyType
    Pμ-type : PolyFunctor → PolyType
    Pν-type : PolyFunctor → PolyType
    -- Base types
    PInt    : PolyType
    PFloat  : PolyType
    PStr    : PolyType
    PBuffer : PolyType
    -- Type variables (the key addition)
    TVar    : String → PolyType

infixr 40 _P⊕_
infixr 50 _P⊗_
infixr 30 _P⇒[_]_
infixr 40 _P+_
infixr 50 _P*_

------------------------------------------------------------------------
-- Type/PolyType Embedding and Extraction
------------------------------------------------------------------------

-- | Embed a ground Type into PolyType
--
-- Every Type is trivially a PolyType (no TVars).
--
mutual
  embedFunctor : Functor → PolyFunctor
  embedFunctor (K A) = PK (embed A)
  embedFunctor Id = PId
  embedFunctor (F ⊕ G) = embedFunctor F P⊕ embedFunctor G
  embedFunctor (F ⊗ G) = embedFunctor F P⊗ embedFunctor G

  embed : Type → PolyType
  embed Unit = PUnit
  embed Void = PVoid
  embed (A * B) = embed A P* embed B
  embed (A + B) = embed A P+ embed B
  embed (A ⇒[ q ] B) = embed A P⇒[ q ] embed B
  embed (Eff A B) = PEff (embed A) (embed B)
  embed (μ-type F) = Pμ-type (embedFunctor F)
  embed (ν-type F) = Pν-type (embedFunctor F)
  embed Int = PInt
  embed Float = PFloat
  embed Str = PStr
  embed Buffer = PBuffer

-- | Extract a ground Type from PolyType
--
-- Fails (returns nothing) if any TVar remains unresolved.
--
mutual
  extractFunctor : PolyFunctor → Maybe Functor
  extractFunctor (PK A) with extract A
  ... | just A' = just (K A')
  ... | nothing = nothing
  extractFunctor PId = just Id
  extractFunctor (F P⊕ G) with extractFunctor F | extractFunctor G
  ... | just F' | just G' = just (F' ⊕ G')
  ... | _ | _ = nothing
  extractFunctor (F P⊗ G) with extractFunctor F | extractFunctor G
  ... | just F' | just G' = just (F' ⊗ G')
  ... | _ | _ = nothing

  extract : PolyType → Maybe Type
  extract PUnit = just Unit
  extract PVoid = just Void
  extract (A P* B) with extract A | extract B
  ... | just A' | just B' = just (A' * B')
  ... | _ | _ = nothing
  extract (A P+ B) with extract A | extract B
  ... | just A' | just B' = just (A' + B')
  ... | _ | _ = nothing
  extract (A P⇒[ q ] B) with extract A | extract B
  ... | just A' | just B' = just (A' ⇒[ q ] B')
  ... | _ | _ = nothing
  extract (PEff A B) with extract A | extract B
  ... | just A' | just B' = just (Eff A' B')
  ... | _ | _ = nothing
  extract (Pμ-type F) with extractFunctor F
  ... | just F' = just (μ-type F')
  ... | nothing = nothing
  extract (Pν-type F) with extractFunctor F
  ... | just F' = just (ν-type F')
  ... | nothing = nothing
  extract PInt = just Int
  extract PFloat = just Float
  extract PStr = just Str
  extract PBuffer = just Buffer
  extract (TVar _) = nothing  -- Unresolved type variable

------------------------------------------------------------------------
-- Embed-Extract Roundtrip Lemmas
------------------------------------------------------------------------

mutual
  -- | Extracting an embedded functor gives back the original
  extractFunctor-embedFunctor : (F : Functor) → extractFunctor (embedFunctor F) ≡ just F
  extractFunctor-embedFunctor (K A) rewrite extract-embed A = refl
  extractFunctor-embedFunctor Id = refl
  extractFunctor-embedFunctor (F ⊕ G)
    rewrite extractFunctor-embedFunctor F | extractFunctor-embedFunctor G = refl
  extractFunctor-embedFunctor (F ⊗ G)
    rewrite extractFunctor-embedFunctor F | extractFunctor-embedFunctor G = refl

  -- | Extracting an embedded type gives back the original
  extract-embed : (A : Type) → extract (embed A) ≡ just A
  extract-embed Unit = refl
  extract-embed Void = refl
  extract-embed (A * B) rewrite extract-embed A | extract-embed B = refl
  extract-embed (A + B) rewrite extract-embed A | extract-embed B = refl
  extract-embed (A ⇒[ q ] B) rewrite extract-embed A | extract-embed B = refl
  extract-embed (Eff A B) rewrite extract-embed A | extract-embed B = refl
  extract-embed (μ-type F) rewrite extractFunctor-embedFunctor F = refl
  extract-embed (ν-type F) rewrite extractFunctor-embedFunctor F = refl
  extract-embed Int = refl
  extract-embed Float = refl
  extract-embed Str = refl
  extract-embed Buffer = refl

------------------------------------------------------------------------
-- Extract Inversion Lemmas
------------------------------------------------------------------------
--
-- If extract succeeds on a compound type, it must succeed on subparts.
-- These lemmas are used to prove impossible cases in extractExprProof.
--

open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)

-- | Inversion for function types
extract-fun-inv : ∀ {A B q T} → extract (A P⇒[ q ] B) ≡ just T
                → ∃[ A' ] ∃[ B' ] (extract A ≡ just A' × extract B ≡ just B')
extract-fun-inv {A} {B} pf with extract A | extract B | pf
... | just A' | just B' | _ = A' , B' , refl , refl

-- | Inversion for effect types
extract-eff-inv : ∀ {A B T} → extract (PEff A B) ≡ just T
                → ∃[ A' ] ∃[ B' ] (extract A ≡ just A' × extract B ≡ just B')
extract-eff-inv {A} {B} pf with extract A | extract B | pf
... | just A' | just B' | _ = A' , B' , refl , refl

-- | Inversion for product types
extract-prod-inv : ∀ {A B T} → extract (A P* B) ≡ just T
                 → ∃[ A' ] ∃[ B' ] (extract A ≡ just A' × extract B ≡ just B')
extract-prod-inv {A} {B} pf with extract A | extract B | pf
... | just A' | just B' | _ = A' , B' , refl , refl

-- | Inversion for sum types
extract-sum-inv : ∀ {A B T} → extract (A P+ B) ≡ just T
                → ∃[ A' ] ∃[ B' ] (extract A ≡ just A' × extract B ≡ just B')
extract-sum-inv {A} {B} pf with extract A | extract B | pf
... | just A' | just B' | _ = A' , B' , refl , refl

------------------------------------------------------------------------
-- Ground Predicate and Total Extraction
------------------------------------------------------------------------
--
-- A PolyType is Ground if it contains no TVars.
-- Given a Ground proof, extraction is total (no Maybe needed).
--

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

mutual
  -- | Ground predicate for PolyFunctor (no TVars)
  GroundFunctor : PolyFunctor → Set
  GroundFunctor (PK A) = Ground A
  GroundFunctor PId = ⊤
  GroundFunctor (F P⊕ G) = GroundFunctor F × GroundFunctor G
  GroundFunctor (F P⊗ G) = GroundFunctor F × GroundFunctor G

  -- | Ground predicate for PolyType (no TVars)
  Ground : PolyType → Set
  Ground PUnit = ⊤
  Ground PVoid = ⊤
  Ground (A P* B) = Ground A × Ground B
  Ground (A P+ B) = Ground A × Ground B
  Ground (A P⇒[ q ] B) = Ground A × Ground B
  Ground (PEff A B) = Ground A × Ground B
  Ground (Pμ-type F) = GroundFunctor F
  Ground (Pν-type F) = GroundFunctor F
  Ground PInt = ⊤
  Ground PFloat = ⊤
  Ground PStr = ⊤
  Ground PBuffer = ⊤
  Ground (TVar _) = ⊥

mutual
  -- | Total extraction for ground functors
  extractGroundFunctor : (F : PolyFunctor) → GroundFunctor F → Functor
  extractGroundFunctor (PK A) g = K (extractGround A g)
  extractGroundFunctor PId _ = Id
  extractGroundFunctor (F P⊕ G) (gf , gg) = extractGroundFunctor F gf ⊕ extractGroundFunctor G gg
  extractGroundFunctor (F P⊗ G) (gf , gg) = extractGroundFunctor F gf ⊗ extractGroundFunctor G gg

  -- | Total extraction for ground types (no Maybe!)
  extractGround : (A : PolyType) → Ground A → Type
  extractGround PUnit _ = Unit
  extractGround PVoid _ = Void
  extractGround (A P* B) (ga , gb) = extractGround A ga * extractGround B gb
  extractGround (A P+ B) (ga , gb) = extractGround A ga + extractGround B gb
  extractGround (A P⇒[ q ] B) (ga , gb) = extractGround A ga ⇒[ q ] extractGround B gb
  extractGround (PEff A B) (ga , gb) = Eff (extractGround A ga) (extractGround B gb)
  extractGround (Pμ-type F) g = μ-type (extractGroundFunctor F g)
  extractGround (Pν-type F) g = ν-type (extractGroundFunctor F g)
  extractGround PInt _ = Int
  extractGround PFloat _ = Float
  extractGround PStr _ = Str
  extractGround PBuffer _ = Buffer
  extractGround (TVar _) ()  -- Impossible: Ground (TVar _) = ⊥

-- | Consistency: extractGround agrees with extract
--
-- If A is ground, then extract A = just (extractGround A g)
--
mutual
  extractGround-consistent-functor : (F : PolyFunctor) (g : GroundFunctor F)
                                   → extractFunctor F ≡ just (extractGroundFunctor F g)
  extractGround-consistent-functor (PK A) g
    rewrite extractGround-consistent A g = refl
  extractGround-consistent-functor PId _ = refl
  extractGround-consistent-functor (F P⊕ G) (gf , gg)
    rewrite extractGround-consistent-functor F gf
          | extractGround-consistent-functor G gg = refl
  extractGround-consistent-functor (F P⊗ G) (gf , gg)
    rewrite extractGround-consistent-functor F gf
          | extractGround-consistent-functor G gg = refl

  extractGround-consistent : (A : PolyType) (g : Ground A)
                           → extract A ≡ just (extractGround A g)
  extractGround-consistent PUnit _ = refl
  extractGround-consistent PVoid _ = refl
  extractGround-consistent (A P* B) (ga , gb)
    rewrite extractGround-consistent A ga | extractGround-consistent B gb = refl
  extractGround-consistent (A P+ B) (ga , gb)
    rewrite extractGround-consistent A ga | extractGround-consistent B gb = refl
  extractGround-consistent (A P⇒[ q ] B) (ga , gb)
    rewrite extractGround-consistent A ga | extractGround-consistent B gb = refl
  extractGround-consistent (PEff A B) (ga , gb)
    rewrite extractGround-consistent A ga | extractGround-consistent B gb = refl
  extractGround-consistent (Pμ-type F) g
    rewrite extractGround-consistent-functor F g = refl
  extractGround-consistent (Pν-type F) g
    rewrite extractGround-consistent-functor F g = refl
  extractGround-consistent PInt _ = refl
  extractGround-consistent PFloat _ = refl
  extractGround-consistent PStr _ = refl
  extractGround-consistent PBuffer _ = refl
  extractGround-consistent (TVar _) ()

------------------------------------------------------------------------
-- Substitution Infrastructure
------------------------------------------------------------------------
--
-- A substitution maps TVar names to ground Types.
-- Applying a complete substitution produces a ground PolyType.
--

open import Data.String using (String)

-- | Type substitution: maps TVar names to ground Types
Subst : Set
Subst = String → Maybe Type

-- | Empty substitution (maps nothing)
emptySubst : Subst
emptySubst _ = nothing

-- | Extend substitution with a new mapping
extendSubst : String → Type → Subst → Subst
extendSubst x T σ y with x Data.String.≟ y
... | yes _ = just T
... | no _  = σ y
  where open import Relation.Nullary using (yes; no)

mutual
  -- | Apply substitution to PolyFunctor
  applySubstFunctor : Subst → PolyFunctor → PolyFunctor
  applySubstFunctor σ (PK A) = PK (applySubstType σ A)
  applySubstFunctor σ PId = PId
  applySubstFunctor σ (F P⊕ G) = applySubstFunctor σ F P⊕ applySubstFunctor σ G
  applySubstFunctor σ (F P⊗ G) = applySubstFunctor σ F P⊗ applySubstFunctor σ G

  -- | Apply substitution to PolyType
  --
  -- TVars are replaced by their mapped Type (embedded back to PolyType).
  -- Unmapped TVars remain as TVars.
  --
  applySubstType : Subst → PolyType → PolyType
  applySubstType σ PUnit = PUnit
  applySubstType σ PVoid = PVoid
  applySubstType σ (A P* B) = applySubstType σ A P* applySubstType σ B
  applySubstType σ (A P+ B) = applySubstType σ A P+ applySubstType σ B
  applySubstType σ (A P⇒[ q ] B) = applySubstType σ A P⇒[ q ] applySubstType σ B
  applySubstType σ (PEff A B) = PEff (applySubstType σ A) (applySubstType σ B)
  applySubstType σ (Pμ-type F) = Pμ-type (applySubstFunctor σ F)
  applySubstType σ (Pν-type F) = Pν-type (applySubstFunctor σ F)
  applySubstType σ PInt = PInt
  applySubstType σ PFloat = PFloat
  applySubstType σ PStr = PStr
  applySubstType σ PBuffer = PBuffer
  applySubstType σ (TVar x) with σ x
  ... | just T  = embed T
  ... | nothing = TVar x

mutual
  -- | Complete predicate for functors: all TVars are mapped by σ
  CompleteFunctor : Subst → PolyFunctor → Set
  CompleteFunctor σ (PK A) = Complete σ A
  CompleteFunctor σ PId = ⊤
  CompleteFunctor σ (F P⊕ G) = CompleteFunctor σ F × CompleteFunctor σ G
  CompleteFunctor σ (F P⊗ G) = CompleteFunctor σ F × CompleteFunctor σ G

  -- | Complete predicate for types: all TVars are mapped by σ
  Complete : Subst → PolyType → Set
  Complete σ PUnit = ⊤
  Complete σ PVoid = ⊤
  Complete σ (A P* B) = Complete σ A × Complete σ B
  Complete σ (A P+ B) = Complete σ A × Complete σ B
  Complete σ (A P⇒[ q ] B) = Complete σ A × Complete σ B
  Complete σ (PEff A B) = Complete σ A × Complete σ B
  Complete σ (Pμ-type F) = CompleteFunctor σ F
  Complete σ (Pν-type F) = CompleteFunctor σ F
  Complete σ PInt = ⊤
  Complete σ PFloat = ⊤
  Complete σ PStr = ⊤
  Complete σ PBuffer = ⊤
  Complete σ (TVar x) = ∃[ T ] (σ x ≡ just T)

-- | Key lemma: applying a complete substitution produces a ground type
--
-- This is the bridge between substitution and extraction.
--
mutual
  complete→ground-functor : (σ : Subst) (F : PolyFunctor)
                          → CompleteFunctor σ F
                          → GroundFunctor (applySubstFunctor σ F)
  complete→ground-functor σ (PK A) c = complete→ground σ A c
  complete→ground-functor σ PId _ = tt
  complete→ground-functor σ (F P⊕ G) (cf , cg) =
    complete→ground-functor σ F cf , complete→ground-functor σ G cg
  complete→ground-functor σ (F P⊗ G) (cf , cg) =
    complete→ground-functor σ F cf , complete→ground-functor σ G cg

  complete→ground : (σ : Subst) (A : PolyType)
                  → Complete σ A
                  → Ground (applySubstType σ A)
  complete→ground σ PUnit _ = tt
  complete→ground σ PVoid _ = tt
  complete→ground σ (A P* B) (ca , cb) =
    complete→ground σ A ca , complete→ground σ B cb
  complete→ground σ (A P+ B) (ca , cb) =
    complete→ground σ A ca , complete→ground σ B cb
  complete→ground σ (A P⇒[ q ] B) (ca , cb) =
    complete→ground σ A ca , complete→ground σ B cb
  complete→ground σ (PEff A B) (ca , cb) =
    complete→ground σ A ca , complete→ground σ B cb
  complete→ground σ (Pμ-type F) c = complete→ground-functor σ F c
  complete→ground σ (Pν-type F) c = complete→ground-functor σ F c
  complete→ground σ PInt _ = tt
  complete→ground σ PFloat _ = tt
  complete→ground σ PStr _ = tt
  complete→ground σ PBuffer _ = tt
  complete→ground σ (TVar x) (T , pf) with σ x | pf
  ... | just T' | refl = embed-ground T'
    where
      -- Embedded types are always ground (they have no TVars)
      embed-ground : (T : Type) → Ground (embed T)
      embed-ground Unit = tt
      embed-ground Void = tt
      embed-ground (A * B) = embed-ground A , embed-ground B
      embed-ground (A + B) = embed-ground A , embed-ground B
      embed-ground (A ⇒[ q ] B) = embed-ground A , embed-ground B
      embed-ground (Eff A B) = embed-ground A , embed-ground B
      embed-ground (μ-type F) = embed-ground-functor F
        where
          embed-ground-functor : (F : Functor) → GroundFunctor (embedFunctor F)
          embed-ground-functor (K A) = embed-ground A
          embed-ground-functor Id = tt
          embed-ground-functor (F ⊕ G) = embed-ground-functor F , embed-ground-functor G
          embed-ground-functor (F ⊗ G) = embed-ground-functor F , embed-ground-functor G
      embed-ground (ν-type F) = embed-ground-functor F
        where
          embed-ground-functor : (F : Functor) → GroundFunctor (embedFunctor F)
          embed-ground-functor (K A) = embed-ground A
          embed-ground-functor Id = tt
          embed-ground-functor (F ⊕ G) = embed-ground-functor F , embed-ground-functor G
          embed-ground-functor (F ⊗ G) = embed-ground-functor F , embed-ground-functor G
      embed-ground Int = tt
      embed-ground Float = tt
      embed-ground Str = tt
      embed-ground Buffer = tt

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
-- PolyType Pretty Printing
------------------------------------------------------------------------

-- | Convert polymorphic types and functors to human-readable strings
-- Used for error messages during type inference
mutual
  showPolyType : PolyType → String
  showPolyType PUnit = "Unit"
  showPolyType PVoid = "Void"
  showPolyType (A P* B) = "(" ++ showPolyType A ++ " * " ++ showPolyType B ++ ")"
  showPolyType (A P+ B) = "(" ++ showPolyType A ++ " + " ++ showPolyType B ++ ")"
  showPolyType (A P⇒[ q ] B) = "(" ++ showPolyType A ++ " " ++ showQuantity q ++ "→ " ++ showPolyType B ++ ")"
  showPolyType (PEff A B) = "Eff " ++ showPolyType A ++ " " ++ showPolyType B
  showPolyType (Pμ-type F) = "μ " ++ showPolyFunctor F
  showPolyType (Pν-type F) = "ν " ++ showPolyFunctor F
  showPolyType PInt = "Int"
  showPolyType PFloat = "Float"
  showPolyType PStr = "String"
  showPolyType PBuffer = "Buffer"
  showPolyType (TVar x) = x

  showPolyFunctor : PolyFunctor → String
  showPolyFunctor (PK A) = "(K " ++ showPolyType A ++ ")"
  showPolyFunctor PId = "Id"
  showPolyFunctor (F P⊕ G) = "(" ++ showPolyFunctor F ++ " ⊕ " ++ showPolyFunctor G ++ ")"
  showPolyFunctor (F P⊗ G) = "(" ++ showPolyFunctor F ++ " ⊗ " ++ showPolyFunctor G ++ ")"