-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Raw — the elaborator's decisions on written terms.
--
-- The terms are the Spec's (`Once.Lang.Syntax`). This module decides
-- `ClosedLiftShape`, the side condition of the closed-expression lift.
------------------------------------------------------------------------

module Once.TypeCheck.Raw where

open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Lang.Syntax
  using ( RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt
        ; RFloat; RAnnot; RBinOp; RUnaryOp; RAna
        ; ClosedLiftShape; cls-var; cls-qual; cls-res; cls-let; cls-destr; cls-unit
        ; cls-annot; cls-binop )

-- | Decides it. The elaborator calls this on the expression it is checking, so
-- the rule's side condition is discharged by the elaborator itself.
closedLiftShape? : ∀ (e : RawExpr) → Maybe (ClosedLiftShape e)
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
closedLiftShape? (RFloat _ _ _ _)      = nothing
closedLiftShape? (RUnaryOp _ _)        = nothing
closedLiftShape? (RAna _ _)            = nothing

-- | …and agrees with the witness, which is what makes the elaborator's
-- dispatch reduce in the completeness proof.
closedLiftShape?-just : ∀ {e : RawExpr} (c : ClosedLiftShape e)
                      → closedLiftShape? e ≡ just c
closedLiftShape?-just cls-var   = refl
closedLiftShape?-just cls-qual  = refl
closedLiftShape?-just cls-res   = refl
closedLiftShape?-just cls-let   = refl
closedLiftShape?-just cls-destr = refl
closedLiftShape?-just cls-unit  = refl
closedLiftShape?-just cls-annot = refl
closedLiftShape?-just cls-binop = refl
