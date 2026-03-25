------------------------------------------------------------------------
-- Once.CCC.IR.Guarded
--
-- DEPRECATED: This module is no longer used.
--
-- OCP-0003: GuardedT was removed from the IR because productivity
-- follows directly from IR totality (see IR/Totality.agda).
-- All IR morphisms terminate, so coalgebras are automatically "guarded"
-- in the sense that they produce F-layers in finite time.
--
-- The module is kept for historical reference but is not imported
-- by any other module.
--
-- Original documentation:
-- Guarded types for productive corecursion (anamorphisms).
-- The Guarded type encodes the guardedness condition.
------------------------------------------------------------------------

module Once.CCC.IR.Guarded where

open import Level using (Level; _⊔_; 0ℓ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_)

------------------------------------------------------------------------
-- Guarded Functor Values (Universe Polymorphic)
--
-- A value of type Guarded F A represents an F-shaped structure where:
-- - Constant positions contain values of the constant type
-- - Recursive positions (Id) contain A values, BUT are "guarded"
--   by appearing inside a constructor (GRec wraps them)
--
-- The GRec constructor explicitly marks where recursion occurs,
-- making the guardedness visible in the type structure.
------------------------------------------------------------------------

-- | Guarded values for a polynomial functor
--
-- This captures the guardedness condition for productive corecursion:
-- - GConst: Constant values pass through unchanged
-- - GRec: Marks a guarded recursive position (the "guard")
-- - GProd: Products of guarded values
-- - GInl/GInr: Coproduct injections of guarded values
--
-- Universe polymorphic to work with any type interpretation.
--
data Guarded {ℓ : Level} (Sem : Type → Set ℓ) : Functor → Set ℓ → Set (suc ℓ) where
  -- Constant: the recursive position doesn't occur
  GConst : ∀ {A B} → Sem A → Guarded Sem (K A) B

  -- Recursive position: A value is guarded by appearing here
  GRec : ∀ {A} → A → Guarded Sem Id A

  -- Product: both components must be guarded
  GProd : ∀ {F G A} → Guarded Sem F A → Guarded Sem G A → Guarded Sem (F ⊗ G) A

  -- Coproduct: inject into left with guarded value
  GInl : ∀ {F G A} → Guarded Sem F A → Guarded Sem (F ⊕ G) A

  -- Coproduct: inject into right with guarded value
  GInr : ∀ {F G A} → Guarded Sem G A → Guarded Sem (F ⊕ G) A

------------------------------------------------------------------------
-- Functor Interpretation (at Set level)
--
-- We need to interpret Functor codes as Set → Set functions for unguard.
-- Parameterized by a type interpretation function.
------------------------------------------------------------------------

-- | Interpret functor code at a carrier type (Set-level)
--
-- ⟦ K A ⟧F X = Sem A       (constant, uses type interpretation)
-- ⟦ Id ⟧F X = X            (recursive position)
-- ⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X ⊎ ⟦ G ⟧F X
-- ⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X × ⟦ G ⟧F X
--
⟦_⟧F : ∀ {ℓ} → (Type → Set ℓ) → Functor → Set ℓ → Set ℓ
⟦ Sem ⟧F (K A) X = Sem A
⟦ Sem ⟧F Id X = X
⟦ Sem ⟧F (F ⊕ G) X = ⟦ Sem ⟧F F X ⊎ ⟦ Sem ⟧F G X
⟦ Sem ⟧F (F ⊗ G) X = ⟦ Sem ⟧F F X × ⟦ Sem ⟧F G X

------------------------------------------------------------------------
-- Unguarding
--
-- Extract the underlying functor value from a guarded value.
-- This is used by ana to build the actual coinductive structure.
------------------------------------------------------------------------

-- | Extract unguarded functor value
--
-- The guardedness is "consumed" by this operation - we've verified
-- that the value was guarded, now we can use it.
--
-- The type interpretation Sem is passed explicitly for clarity.
--
unguard : ∀ {ℓ} (Sem : Type → Set ℓ) → ∀ F {A} → Guarded Sem F A → ⟦ Sem ⟧F F A
unguard Sem (K A) (GConst x) = x
unguard Sem Id (GRec a) = a
unguard Sem (F ⊗ G) (GProd gf gg) = (unguard Sem F gf , unguard Sem G gg)
unguard Sem (F ⊕ G) (GInl gf) = inj₁ (unguard Sem F gf)
unguard Sem (F ⊕ G) (GInr gg) = inj₂ (unguard Sem G gg)

------------------------------------------------------------------------
-- Guarding (Lifting into Guarded)
--
-- These smart constructors help build guarded values.
-- Parameterized by type interpretation Sem.
------------------------------------------------------------------------

-- | Lift a constant value to Guarded
guardConst : ∀ {ℓ} {Sem : Type → Set ℓ} {A B} → Sem A → Guarded Sem (K A) B
guardConst = GConst

-- | Guard a recursive value
guardRec : ∀ {ℓ} {Sem : Type → Set ℓ} {A} → A → Guarded Sem Id A
guardRec = GRec

-- | Combine guarded values into a product
guardPair : ∀ {ℓ} {Sem : Type → Set ℓ} {F G A} → Guarded Sem F A → Guarded Sem G A → Guarded Sem (F ⊗ G) A
guardPair = GProd

-- | Inject guarded value into left of coproduct
guardInl : ∀ {ℓ} {Sem : Type → Set ℓ} {F G A} → Guarded Sem F A → Guarded Sem (F ⊕ G) A
guardInl = GInl

-- | Inject guarded value into right of coproduct
guardInr : ∀ {ℓ} {Sem : Type → Set ℓ} {F G A} → Guarded Sem G A → Guarded Sem (F ⊕ G) A
guardInr = GInr

------------------------------------------------------------------------
-- Functorial Map for Guarded
--
-- We can map over the A values inside Guarded F A.
-- This is useful for composing coalgebras.
------------------------------------------------------------------------

-- | Map a function over guarded values
gmapA : ∀ {ℓ} {Sem : Type → Set ℓ} {F A B} → (A → B) → Guarded Sem F A → Guarded Sem F B
gmapA {F = K A} f (GConst x) = GConst x
gmapA {F = Id} f (GRec a) = GRec (f a)
gmapA {F = F ⊗ G} f (GProd gf gg) = GProd (gmapA f gf) (gmapA f gg)
gmapA {F = F ⊕ G} f (GInl gf) = GInl (gmapA f gf)
gmapA {F = F ⊕ G} f (GInr gg) = GInr (gmapA f gg)

------------------------------------------------------------------------
-- Standard Guarded Patterns
--
-- Helpers for common use cases.
-- These require a type interpretation that maps Unit to ⊤.
------------------------------------------------------------------------

-- | Unit (for K Unit) - requires Sem Unit = ⊤
gunit : ∀ {ℓ} {Sem : Type → Set ℓ} {A} → Sem Once.Type.Unit → Guarded Sem (K Once.Type.Unit) A
gunit u = GConst u

-- | Build guarded natural number successor: n → Guarded NatF Nat
gsuc : ∀ {ℓ} {Sem : Type → Set ℓ} {A} → A → Guarded Sem (Once.Type.K Once.Type.Unit ⊕ Id) A
gsuc n = GInr (GRec n)

-- | Build guarded list cons: (a, xs) → Guarded (ListF A) (List A)
gcons : ∀ {ℓ} {Sem : Type → Set ℓ} {A B} → Sem A → B → Guarded Sem (Once.Type.K Once.Type.Unit ⊕ (Once.Type.K A ⊗ Id)) B
gcons a xs = GInr (GProd (GConst a) (GRec xs))

-- | Build guarded list nil
gnil : ∀ {ℓ} {Sem : Type → Set ℓ} {A B} → Sem Once.Type.Unit → Guarded Sem (Once.Type.K Once.Type.Unit ⊕ (Once.Type.K A ⊗ Id)) B
gnil u = GInl (GConst u)

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
--
-- Guarded Sem F A represents "guarded" F-shaped structures:
-- - Every recursive occurrence is wrapped in GRec
-- - unguard extracts the underlying ⟦ Sem ⟧F F A value
-- - Used by Ana to ensure productive corecursion
--
-- The guardedness guarantee:
-- - If you have Guarded Sem F A, you can produce ⟦ Sem ⟧F F A
-- - The F structure is already built (the "observation")
-- - Only the A values need further computation
--
-- This is exactly what productivity requires: each step of unfolding
-- produces at least one constructor before any recursive calls.
------------------------------------------------------------------------
