-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Admissible — WHICH PROGRAMS A TARGET OWES AN ANSWER FOR
-- (plan 0.74, D115/D116).
--
-- SPEC. `Once.Spec.Meaning` re-exports it, for the reason D114 gives for the
-- observable: a statement that decides what counts as correct belongs in the
-- reviewed spec, not in a module the spec merely reaches through.
--
-- `Typed` is TARGET-FREE — parsing and typing do not depend on the target.
-- This is the other half: whether a typed program can be EXPRESSED at a given
-- target. An `Int` literal must fit that target's signed range; a literal that
-- does not is a compile error (D115).
--
-- WHY IT IS IN THE SPEC AND NOT MERELY IMPLEMENTED. Without it, a compiler
-- that rejects EVERY program satisfies soundness vacuously — only completeness
-- rules that out, and completeness is stated against the meaning. So the
-- meaning has to say which programs a target owes an answer for. The
-- `Admissible` premise is exactly what makes rejecting an out-of-range literal
-- legal WITHOUT making "reject everything" legal.
--
-- WHY A PREDICATE AND NOT A PARTIAL `⟦_⟧ˢ`. An ill-typed program does not get
-- a `nothing` meaning either — it is excluded by `Typed`, and `⟦_⟧ˢ` is TOTAL
-- behind that gate. "Does 1001 fit in 8 bits" is the same kind of question:
-- static, decidable, and about EXPRESSIBILITY rather than about what the
-- program computes. Making `⟦_⟧ˢ` `Maybe`-valued would stack an admissibility
-- monad on the trace monad `T` and force every structural clause to thread it.
--
-- FLOATS PLACE NO CONDITION HERE. They always lower, rounding when the target
-- cannot hold them exactly (D116) — so the gate is `Int`-ONLY. That asymmetry
-- is D054 one level down: IEEE's promise INCLUDES rounding, while `Int`'s
-- promise is modular ARITHMETIC and a literal is not arithmetic.
--
-- STATED OVER THE SOURCE, NOT OVER `moduleToIR`. D057 moved the meaning off
-- the elaborator and it stays off: this walks the parsed module's own syntax.
-- The backend walks the IR instead, and that the two agree is a PROOF
-- obligation (plan 0.74 J4), not something faked by sharing a traversal. What
-- IS shared is the per-literal decision, `Once.Word.Width.inRange?` — one
-- procedure, two callers.
------------------------------------------------------------------------

module Once.Denotation.Admissible where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; all?)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec)

open import Once.Target.Arch using (Arch; arch-int-bits)
import Once.Word as OnceWord
open import Once.TypeCheck.Raw using
  ( RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct
  ; RUnit; RInt; RFloat; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna )
open import Once.Parser.Module.Core using
  ( Module; mkModule; decls; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias
  ; DImport )

------------------------------------------------------------------------
-- The literals a program contains
--
-- ENUMERATED, with no catch-all. A catch-all would silently return `[]` for a
-- constructor added later, and the gate would pass a program whose literal it
-- never looked at — the exact shape of hole D114 found in the observable.
------------------------------------------------------------------------

rawIntLits : RawExpr → List ℤ
rawIntLits (RInt n)             = n ∷ []
rawIntLits (RApp f x)           = rawIntLits f ++ rawIntLits x
rawIntLits (RLam _ b)           = rawIntLits b
rawIntLits (RLet _ e b)         = rawIntLits e ++ rawIntLits b
rawIntLits (RPair a b)          = rawIntLits a ++ rawIntLits b
rawIntLits (RDestruct s _ l _ r) = rawIntLits s ++ rawIntLits l ++ rawIntLits r
rawIntLits (RAnnot e _)         = rawIntLits e
rawIntLits (RBinOp _ a b)       = rawIntLits a ++ rawIntLits b
rawIntLits (RUnaryOp _ e)       = rawIntLits e
rawIntLits (RAna _ e)           = rawIntLits e
-- leaves that carry no `Int` literal
rawIntLits (RVar _)             = []
rawIntLits (RQualified _ _)     = []
rawIntLits (RResolved _)        = []
rawIntLits RUnit                = []
-- a FLOAT literal is not checked here: it always lowers, rounding if the
-- target cannot hold it exactly (D116).
rawIntLits (RFloat _ _ _)       = []
rawIntLits (RStringLit _)       = []

declIntLits : Decl → List ℤ
declIntLits (DFunDef _ _ body) = rawIntLits body
declIntLits (DTypeSig _ _)     = []
declIntLits (DSignature _ _ _ _) = []
declIntLits (DTypeAlias _ _ _) = []
declIntLits (DImport _)        = []

moduleIntLits : Module → List ℤ
moduleIntLits (mkModule ds) = go ds
  where
    go : List Decl → List ℤ
    go []       = []
    go (d ∷ ds) = declIntLits d ++ go ds

------------------------------------------------------------------------
-- Admissibility
------------------------------------------------------------------------

-- | Every `Int` literal in the module fits this target's signed range.
AdmissibleM : Arch → Module → Set
AdmissibleM arch m =
  All (OnceWord.Width.InRange (arch-int-bits arch)) (moduleIntLits m)

-- | …and it is DECIDABLE, which is what lets the backend dispatch on the very
-- same decision rather than a second implementation of it.
admissibleM? : ∀ arch m → Dec (AdmissibleM arch m)
admissibleM? arch m =
  all? (OnceWord.Width.inRange? (arch-int-bits arch)) (moduleIntLits m)
