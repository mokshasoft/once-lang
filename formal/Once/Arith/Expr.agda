------------------------------------------------------------------------
-- Once.Arith.Expr
--
-- Shared arithmetic expression type.
-- Defined at top-level, used by Surface.Elaborate and domain compilers.
--
-- Part of OCP-0003: Pluggable domain compiler architecture.
--
-- This is NOT the Arith compiler - just the expression type.
-- Different compilers can handle different subsets of ArithExpr.
------------------------------------------------------------------------

module Once.Arith.Expr where

open import Once.Type
open import Data.Nat using (ℕ)
open import Data.String using (String)

------------------------------------------------------------------------
-- Arithmetic Expressions
------------------------------------------------------------------------

-- | ArithExpr A B represents an arithmetic operation from A to B.
--
-- This is a shared type - compilers process what they can handle
-- and pass the rest through.
--
data ArithExpr : Type → Type → Set where
  -- Literals (Unit → T, ignores input)
  lit-int   : ℕ → ArithExpr Unit Int
  lit-str   : String → ArithExpr Unit Str

  -- Binary arithmetic (Int × Int → Int)
  arith-add : ArithExpr (Int * Int) Int
  arith-sub : ArithExpr (Int * Int) Int
  arith-mul : ArithExpr (Int * Int) Int
  arith-div : ArithExpr (Int * Int) Int
  arith-mod : ArithExpr (Int * Int) Int

  -- Unary arithmetic (Int → Int)
  arith-neg : ArithExpr Int Int

  -- Comparisons (Int × Int → Bool, where Bool = Unit + Unit)
  arith-lt  : ArithExpr (Int * Int) (Unit + Unit)
  arith-le  : ArithExpr (Int * Int) (Unit + Unit)
  arith-gt  : ArithExpr (Int * Int) (Unit + Unit)
  arith-ge  : ArithExpr (Int * Int) (Unit + Unit)
  arith-eq  : ArithExpr (Int * Int) (Unit + Unit)
  arith-ne  : ArithExpr (Int * Int) (Unit + Unit)

  -- Extensible: other domains can add more
  -- (or we can extend this datatype later)
  -- Examples that might be added:
  --   math-sin  : ArithExpr Float Float
  --   math-cos  : ArithExpr Float Float
  --   math-sqrt : ArithExpr Float Float

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Get a human-readable name for an ArithExpr (for debugging/emission)
arith-name : ∀ {A B} → ArithExpr A B → String
arith-name (lit-int n) = "lit.int"
arith-name (lit-str s) = "lit.str"
arith-name arith-add = "arith.add"
arith-name arith-sub = "arith.sub"
arith-name arith-mul = "arith.mul"
arith-name arith-div = "arith.div"
arith-name arith-mod = "arith.mod"
arith-name arith-neg = "arith.neg"
arith-name arith-lt  = "arith.lt"
arith-name arith-le  = "arith.le"
arith-name arith-gt  = "arith.gt"
arith-name arith-ge  = "arith.ge"
arith-name arith-eq  = "arith.eq"
arith-name arith-ne  = "arith.ne"
