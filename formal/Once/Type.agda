------------------------------------------------------------------------
-- Once.Type
--
-- Definition of types in the Once language.
-- These are the objects of a Cartesian Closed Category.
------------------------------------------------------------------------

module Once.Type where

open import Level using (Level)

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
data Type : Set where
  Unit  : Type                    -- Terminal object
  Void  : Type                    -- Initial object
  _*_   : Type → Type → Type      -- Product
  _+_   : Type → Type → Type      -- Coproduct (sum)
  _⇒_   : Type → Type → Type      -- Exponential (function, pure)
  Eff   : Type → Type → Type      -- Effectful morphism (D032)
  Fix   : Type → Type             -- Fixed point: Fix F ≅ F (Fix F)

infixr 30 _⇒_
infixr 40 _+_
infixr 50 _*_

-- | IO type alias (D032)
-- IO A is sugar for Eff Unit A (effectful computation producing A)
IO : Type → Type
IO A = Eff Unit A
