-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Syntax — the program GRAMMAR (OCP-0006, spec).
--
-- SPEC (trust boundary): what a program IS, at the two stages a reader cares
-- about — `Once.TypeCheck.Raw` (`RawExpr`, the parsed concrete syntax the
-- programmer writes) and `Once.Surface.Syntax` (`Expr`, the intrinsically-typed
-- term grammar the denotation interprets). Both are re-exported.
------------------------------------------------------------------------

module Once.Spec.Syntax where

-- P5: `RawExpr` ONLY — what you may WRITE. The elaborated `Surface.Expr`
-- family is elaborator OUTPUT (implementation), not spec.
-- EXPLICIT re-export: the WRITTEN grammar, and the two operator predicates the
-- arithmetic/comparison rules name. The `closedLiftShape?` DECIDER is
-- implementation and stays out (D134: the spec names properties).
open import Once.TypeCheck.Raw public
  using ( RawExpr ; RVar ; RQualified ; RResolved ; RApp ; RLam ; RLet
        ; RPair ; RDestruct ; RUnit ; RInt ; RFloat ; RStringLit ; RAnnot
        ; RBinOp ; RUnaryOp ; RAna
        ; RawType ; RTVar ; RTUnit ; RTVoid ; RTInt ; RTFloat ; RTBuffer
        ; RTStr ; RTProduct ; RTSum ; RTArrow ; RTEff ; RTFix
        ; BinOp ; OpAdd ; OpSub ; OpMul ; OpDiv ; OpMod
        ; OpLt ; OpLe ; OpGt ; OpGe ; OpEq ; OpNe
        ; UnaryOp ; OpNeg
        ; isArithmeticOp ; isFloatArithmeticOp ; isComparisonOp
        ; ClosedLiftShape ; cls-var ; cls-qual ; cls-res ; cls-let
        ; cls-destr ; cls-unit ; cls-str ; cls-annot ; cls-binop
        )
