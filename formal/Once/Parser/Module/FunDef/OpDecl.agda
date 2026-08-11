-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.FunDef.OpDecl
--
-- Operator-form declaration: `(op)` followed by either a type
-- signature (`: Type`) or a function definition.
------------------------------------------------------------------------

module Once.Parser.Module.FunDef.OpDecl where

open import Once.Parser.Module.Core
open import Once.Parser.Module.OpName
open import Once.Parser.Module.FunDef.Def
open import Once.Parser.Module.DeclTail using (colonHead; colDrop1; colDrop1-≤)
open import Once.Parser.PolyType using (parsePolyTypeB; ParsePolyAtB)
open import Data.Bool using (Bool; true; false)
open import Data.Nat.Properties using (<-≤-trans)

-- | After parsing an operator name, decide: type sig or fun def.
-- Weak shrink: residual ≤ input. The TColon case produces a type
-- signature; every other token delegates to `parseFunDefB`, which
-- bundles the (possibly-empty) parameter list and body parse. Routed through
-- the `colonHead` classifier (instead of matching `TColon ∷ rest` directly).
toda-sig : (name : String) (toks : List Token) → ParsePolyAtB (colDrop1 toks) → ParseAtB≤ {Decl} toks
toda-sig name toks nothing                   = nothing
toda-sig name toks (just (ty , rest' , bnd)) =
  just (DTypeSig name ty , rest' , <⇒≤ (<-≤-trans bnd (colDrop1-≤ toks)))

toda-fun : (name : String) (toks : List Token) → ParseAtB {Decl} toks → ParseAtB≤ {Decl} toks
toda-fun name toks nothing                  = nothing
toda-fun name toks (just (d , rest' , bnd)) = just (d , rest' , <⇒≤ bnd)

toda-go : (name : String) (toks : List Token) → Bool → ParseAtB≤ {Decl} toks
toda-go name toks true  = toda-sig name toks (parsePolyTypeB (colDrop1 toks))
toda-go name toks false = toda-fun name toks (parseFunDefB name toks)

tryOpDeclAfterB : String → (toks : List Token) → ParseAtB≤ {Decl} toks
tryOpDeclAfterB name toks = toda-go name toks (colonHead toks)

tryOpDeclAfter : String → List Token → Maybe (Decl × List Token)
tryOpDeclAfter name toks with tryOpDeclAfterB name toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Try to parse an operator-name declaration (type sig or fun def).
-- Strictly shrinks (consumes at least `(op)`).
tryOpDeclB : (toks : List Token) → ParseAtB {Decl} toks
tryOpDeclB toks with parseOperatorNameB toks
... | nothing = nothing
... | just (name , rest , bnd) with tryOpDeclAfterB name rest
...   | just (d , rest' , bnd') = just (d , rest' , ≤-<-trans bnd' bnd)
...   | nothing = nothing

tryOpDecl : List Token → Maybe (Decl × List Token)
tryOpDecl toks with tryOpDeclB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
