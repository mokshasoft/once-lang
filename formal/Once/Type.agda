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
-- - _⇒_ is the exponential object (function space)
--
data Type : Set where
  Unit  : Type                    -- Terminal object
  Void  : Type                    -- Initial object
  _*_   : Type → Type → Type      -- Product
  _+_   : Type → Type → Type      -- Coproduct (sum)
  _⇒_   : Type → Type → Type      -- Exponential (function)

infixr 30 _⇒_
infixr 40 _+_
infixr 50 _*_
