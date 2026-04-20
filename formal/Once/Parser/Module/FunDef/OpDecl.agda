-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
open import Once.Parser.PolyType using (parsePolyTypeB)

-- | After parsing an operator name, decide: type sig or fun def.
-- Weak shrink: residual ≤ input. The TColon case produces a type
-- signature; every other token delegates to `parseFunDefB`, which
-- bundles the (possibly-empty) parameter list and body parse.
tryOpDeclAfterB : String → (toks : List Token) → ParseAtB≤ {Decl} toks
tryOpDeclAfterB name (TColon ∷ rest) with parsePolyTypeB rest
... | just (ty , rest' , bnd) =
      just (DTypeSig name ty , rest' , <⇒≤ (<-trans bnd (s≤s ≤-refl)))
... | nothing = nothing
tryOpDeclAfterB name toks with parseFunDefB name toks
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing

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
