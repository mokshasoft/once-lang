------------------------------------------------------------------------
-- Once.Arith.ExprSemantics
--
-- Semantics for ArithExpr (the shared arithmetic expression type).
-- Parameterized by MachineInterface (for ⟦_⟧ and word operations).
--
-- Part of OCP-0003: Pluggable domain compiler architecture.
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.Arith.ExprSemantics (MI : MachineInterface) where

open import Data.Bool using (Bool; true; false; not)

open import Once.Type
open import Once.Arith.Expr
open import Once.SemanticBaseMachine MI

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Evaluation of ArithExpr
------------------------------------------------------------------------

private
  -- Convert Bool to Unit + Unit (true = inj₁, false = inj₂)
  bool-to-sum : Bool → ⟦ Unit + Unit ⟧
  bool-to-sum true  = inj₁ tt
  bool-to-sum false = inj₂ tt

  -- Convert word comparison result (ℕ: 0 or 1) to sum
  word-to-sum : ⟦ Int ⟧ → ⟦ Unit + Unit ⟧
  word-to-sum w = bool-to-sum (word-to-bool w)

  swap : ∀ {A B : Set} → A × B → B × A
  swap (a , b) = (b , a)

  -- a ≤ b ≡ ¬(b < a)
  le-sem : ⟦ Int * Int ⟧ → ⟦ Unit + Unit ⟧
  le-sem (a , b) = bool-to-sum (not (word-to-bool (int-lt (b , a))))

  -- a ≥ b ≡ ¬(a < b)
  ge-sem : ⟦ Int * Int ⟧ → ⟦ Unit + Unit ⟧
  ge-sem (a , b) = bool-to-sum (not (word-to-bool (int-lt (a , b))))

  -- a ≠ b ≡ ¬(a = b)
  ne-sem : ⟦ Int * Int ⟧ → ⟦ Unit + Unit ⟧
  ne-sem p = bool-to-sum (not (word-to-bool (int-eq p)))

-- | Evaluate an arithmetic expression
--
-- This provides the semantics for ArithExpr in terms of machine words.
--
evalArith : ∀ {A B} → ArithExpr A B → ⟦ A ⟧ → ⟦ B ⟧

-- Literals: ⟦ Int ⟧ = ℕ, so lit-int n just returns n directly
evalArith (lit-int n) _ = n
evalArith (lit-str s) _ = s

-- Binary arithmetic
evalArith arith-add p = int-add p
evalArith arith-sub p = int-sub p
evalArith arith-mul p = int-mul p
evalArith arith-div p = int-div p
evalArith arith-mod p = int-mod p

-- Unary arithmetic
evalArith arith-neg n = int-neg n

-- Comparisons (return Unit + Unit, i.e., Bool)
evalArith arith-lt p = word-to-sum (int-lt p)
evalArith arith-le p = le-sem p
evalArith arith-gt p = word-to-sum (int-lt (swap p))
evalArith arith-ge p = ge-sem p
evalArith arith-eq p = word-to-sum (int-eq p)
evalArith arith-ne p = ne-sem p
