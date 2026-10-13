-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type — the implementation's operations on types.
--
-- The types themselves are the Spec's (`Once.Spec.Type`, `.Grade`, `.Poly`).
-- This module holds what the compiler needs beyond them: decidable equality,
-- Boolean equality, the groundness decider, printing for error messages, the
-- register-resident classification and a few example functors.
------------------------------------------------------------------------

module Once.Type where


open import Relation.Binary.Definitions using (DecidableEquality)

open import Data.Nat using (ℕ)
import Data.Nat
import Data.Nat.Show
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Once.Spec.Type.Grade
  using (Quantity; Zero; One; Many; Purity; pure; act; eff⁺; eff; ArrowKind; mk-kind)
open import Once.Spec.Type
  using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid; TKind; k-base; k-any;
         Functor; K; Id; _⊕_; _⊗_)
open import Once.Spec.Type.Poly
  using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff;
         Pμ-type; Pν-type; PInt; PFloat; PTVar; Ground; GroundF)


-- | Show function for Quantity (for error messages)
showQuantity : Quantity → String
showQuantity Zero = "0"
showQuantity One  = "1"
showQuantity Many = "ω"


-- | Show function for Purity
showPurity : Purity → String
showPurity pure = "pure"
showPurity eff  = "eff"
showPurity eff⁺ = "eff⁺"
showPurity act  = "act"


-- | Show function for ArrowKind
showArrowKind : ArrowKind → String
showArrowKind (mk-kind q p) = showQuantity q ++ "," ++ showPurity p


-- The deciders on quantities, purities and kinds are `Once.Spec.Type.DecEq`'s.

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
{-# CATCHALL #-}
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
  showType (A ⇒[ mk-kind _ eff⁺ ] B) = "Eff⁺ " ++ showType A ++ " " ++ showType B
  showType (A ⇒[ mk-kind _ act ] B) = "Act " ++ showType A ++ " " ++ showType B
  showType (μ-type F) = "μ " ++ showFunctor F
  showType (ν-type F pure) = "ν " ++ showFunctor F
  showType (ν-type F eff)  = "ν (Eff " ++ showFunctor F ++ ")"
  showType (ν-type F eff⁺) = "ν (Eff⁺ " ++ showFunctor F ++ ")"
  showType (ν-type F act) = "ν (Act " ++ showFunctor F ++ ")"
  showType Int = "Int"
  showType Float = "Float"
  showType (rigid k-base i) = "'b" ++ Data.Nat.Show.show i
  showType (rigid k-any i)  = "'a" ++ Data.Nat.Show.show i

  showFunctor : Functor → String
  showFunctor (K A) = "(K " ++ showType A ++ ")"
  showFunctor Id = "Id"
  showFunctor (F ⊕ G) = "(" ++ showFunctor F ++ " ⊕ " ++ showFunctor G ++ ")"
  showFunctor (F ⊗ G) = "(" ++ showFunctor F ++ " ⊗ " ++ showFunctor G ++ ")"


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
  isGround (Pν-type F _)  = isGroundF F     -- Ground (Pν-type F) = GroundF F
  isGround PInt         = inj₁ tt
  isGround PFloat       = inj₁ tt
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
  showPolyType (Pν-type F pure) = "ν " ++ showPolyFunctor F
  showPolyType (Pν-type F eff)  = "ν (Eff " ++ showPolyFunctor F ++ ")"
  showPolyType (Pν-type F eff⁺) = "ν (Eff⁺ " ++ showPolyFunctor F ++ ")"
  showPolyType (Pν-type F act) = "ν (Act " ++ showPolyFunctor F ++ ")"
  showPolyType PInt             = "Int"
  showPolyType PFloat           = "Float"
  showPolyType (PTVar x)        = x

  showPolyFunctor : PolyFunctor → String
  showPolyFunctor (PK A)        = "(K " ++ showPolyType A ++ ")"
  showPolyFunctor PId           = "Id"
  showPolyFunctor (F P⊕ G)      = "(" ++ showPolyFunctor F ++ " ⊕ " ++ showPolyFunctor G ++ ")"
  showPolyFunctor (F P⊗ G)      = "(" ++ showPolyFunctor F ++ " ⊗ " ++ showPolyFunctor G ++ ")"


------------------------------------------------------------------------
-- Bool-valued Purity equality (the oracle's unifier, `TypeCheck.Principal`).
-- Decidable equality is `_≟p_` above.


purityEqBool : Purity → Purity → Bool
purityEqBool pure pure = true
purityEqBool eff  eff  = true
purityEqBool eff⁺ eff⁺ = true
purityEqBool act  act  = true
{-# CATCHALL #-}
purityEqBool _    _    = false
