-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Raw — the elaborator's decisions on written terms.
--
-- The terms are the Spec's (`Once.Spec.Surface.Syntax`). This module classes
-- the binary operators and defines and decides `ClosedLiftShape`, the side
-- condition of the closed-expression lift.
------------------------------------------------------------------------

module Once.TypeCheck.Raw where

open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Once.Spec.Surface.Syntax
  using (Expr; BinOp; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat;
         RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)

------------------------------------------------------------------------
-- The operators' classes
------------------------------------------------------------------------

isComparisonOp : BinOp → Bool
isComparisonOp OpLt  = true
isComparisonOp OpLe  = true
isComparisonOp OpGt  = true
isComparisonOp OpGe  = true
isComparisonOp OpEq  = true
isComparisonOp OpNe  = true
isComparisonOp OpAdd = false
isComparisonOp OpSub = false
isComparisonOp OpMul = false
isComparisonOp OpDiv = false
isComparisonOp OpMod = false

-- The operators defined on `Float`. `%` is not: `fmod` is a different
-- function from the integer remainder, and is not given a meaning.
isFloatArithmeticOp : BinOp → Bool
isFloatArithmeticOp OpAdd = true
isFloatArithmeticOp OpSub = true
isFloatArithmeticOp OpMul = true
isFloatArithmeticOp OpDiv = true
isFloatArithmeticOp OpMod = false
isFloatArithmeticOp OpLt  = false
isFloatArithmeticOp OpLe  = false
isFloatArithmeticOp OpGt  = false
isFloatArithmeticOp OpGe  = false
isFloatArithmeticOp OpEq  = false
isFloatArithmeticOp OpNe  = false

isArithmeticOp : BinOp → Bool
isArithmeticOp OpAdd = true
isArithmeticOp OpSub = true
isArithmeticOp OpMul = true
isArithmeticOp OpDiv = true
isArithmeticOp OpMod = true
isArithmeticOp OpLt  = false
isArithmeticOp OpLe  = false
isArithmeticOp OpGt  = false
isArithmeticOp OpGe  = false
isArithmeticOp OpEq  = false
isArithmeticOp OpNe  = false

------------------------------------------------------------------------
-- The forms without a checking rule of their own
------------------------------------------------------------------------

-- A closed expression of one of these forms may be checked against a type by
-- inferring its type and converting (the subsumption rule of a bidirectional
-- system applies only to forms that are not introductions). Leaving `RLam`
-- out matters: otherwise a lambda would have two checking derivations with
-- different meanings. The other introduction forms have their own rules.
data ClosedLiftShape : Expr → Set where
  cls-var    : ∀ {x}         → ClosedLiftShape (RVar x)
  cls-qual   : ∀ {n a}       → ClosedLiftShape (RQualified n a)
  cls-res    : ∀ {cn}        → ClosedLiftShape (RResolved cn)
  cls-let    : ∀ {x e₁ e₂}   → ClosedLiftShape (RLet x e₁ e₂)
  cls-destr  : ∀ {s x eL y eR} → ClosedLiftShape (RDestruct s x eL y eR)
  cls-unit   :                 ClosedLiftShape RUnit
  cls-annot  : ∀ {e T}       → ClosedLiftShape (RAnnot e T)
  cls-binop  : ∀ {op a b}    → ClosedLiftShape (RBinOp op a b)


-- | Decides it. The elaborator calls this on the expression it is checking, so
-- the rule's side condition is discharged by the elaborator itself.
closedLiftShape? : ∀ (e : Expr) → Maybe (ClosedLiftShape e)
closedLiftShape? (RVar _)              = just cls-var
closedLiftShape? (RQualified _ _)      = just cls-qual
closedLiftShape? (RResolved _)         = just cls-res
closedLiftShape? (RLet _ _ _)          = just cls-let
closedLiftShape? (RDestruct _ _ _ _ _) = just cls-destr
closedLiftShape? RUnit                 = just cls-unit
closedLiftShape? (RAnnot _ _)          = just cls-annot
closedLiftShape? (RBinOp _ _ _)        = just cls-binop
closedLiftShape? (RApp _ _)            = nothing
closedLiftShape? (RLam _ _)            = nothing
closedLiftShape? (RPair _ _)           = nothing
closedLiftShape? (RInt _)              = nothing
closedLiftShape? (RFloat _ _ _)      = nothing
closedLiftShape? (RNeg _)        = nothing

-- | …and agrees with the witness, which is what makes the elaborator's
-- dispatch reduce in the completeness proof.
closedLiftShape?-just : ∀ {e : Expr} (c : ClosedLiftShape e)
                      → closedLiftShape? e ≡ just c
closedLiftShape?-just cls-var   = refl
closedLiftShape?-just cls-qual  = refl
closedLiftShape?-just cls-res   = refl
closedLiftShape?-just cls-let   = refl
closedLiftShape?-just cls-destr = refl
closedLiftShape?-just cls-unit  = refl
closedLiftShape?-just cls-annot = refl
closedLiftShape?-just cls-binop = refl
