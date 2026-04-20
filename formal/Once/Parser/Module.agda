-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module
--
-- Module-level parser: declarations, imports, type aliases.
-- Produces a Module record containing all declarations.
--
-- The body of this module is split across `Once.Parser.Module.*`
-- submodules to keep the generated GHC (MAlonzo) case-trees for each
-- source file small enough to compile in bounded memory. This file
-- re-exports all the pieces and contains only the top-level driver
-- (`parseDeclB` / `parseDeclsWF` / `parseModule`) that glues them
-- together.
------------------------------------------------------------------------

module Once.Parser.Module where

open import Once.Parser.Module.Core public
open import Once.Parser.Module.Import public
open import Once.Parser.Module.Alloc public
open import Once.Parser.Module.OpName public
open import Once.Parser.Module.FunDef public
open import Once.Parser.Module.DeclTail public

-- | Bounded parse of a single declaration. On success the residual is
-- strictly shorter than the input, which gives us the measure to do
-- well-founded recursion in `parseDeclsWF` below.
parseDeclB : (toks : List Token) → ParseAtB {Decl} toks
parseDeclB [] = nothing
parseDeclB (TWord w ∷ rest) with w ≟ "import"
... | yes _ with parseImportB rest
...   | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
...   | nothing = nothing
parseDeclB (TWord w ∷ rest) | no _ with w ≟ "type"
... | yes _ with parseTypeAliasB rest
...   | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
...   | nothing = nothing
parseDeclB (TWord w ∷ rest) | no _ | no _ with w ≟ "primitive"
... | yes _ with parsePrimitiveB rest
...   | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
...   | nothing = nothing
parseDeclB (TWord w ∷ TColon ∷ rest) | no _ | no _ | no _ with parseTypeB rest
... | nothing = nothing
... | just (ty , TEquals ∷ _ , _) = nothing
... | just (ty , rest' , bnd) =
      just (DTypeSig w ty , rest' ,
            <-trans (<-trans bnd (s≤s ≤-refl)) (s≤s ≤-refl))
parseDeclB (TWord w ∷ rest) | no _ | no _ | no _
  with parseFunDefB w rest
... | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseDeclB (TLParen ∷ rest) = tryOpDeclB (TLParen ∷ rest)
parseDeclB _ = nothing

parseDecl : Parser Decl
parseDecl toks with parseDeclB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

------------------------------------------------------------------------
-- Module Parser
------------------------------------------------------------------------

-- | Length bound for `skipNewlines`: the emitted residual is ≤ the
-- input. This is proved structurally: each step either passes through
-- unchanged (equal length) or drops a `TNewline` (strictly smaller).
skipNewlines-≤ : (toks : List Token) →
                 ∀ {ns rest} → skipNewlines toks ≡ just (ns , rest) →
                 length rest ≤ length toks
skipNewlines-≤ [] refl = ≤-refl
skipNewlines-≤ (TNewline ∷ rest) eq with skipNewlines rest | skipNewlines-≤ rest
... | just (_ , _) | rec with eq
...   | refl = ≤-trans (rec refl) (n≤1+n _)
skipNewlines-≤ (TNewline ∷ rest) eq | nothing | _ with eq
...   | refl = n≤1+n _
skipNewlines-≤ (TWord _ ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLParen ∷ rest) refl = ≤-refl
skipNewlines-≤ (TRParen ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLBrace ∷ rest) refl = ≤-refl
skipNewlines-≤ (TRBrace ∷ rest) refl = ≤-refl
skipNewlines-≤ (TColon ∷ rest) refl = ≤-refl
skipNewlines-≤ (TEquals ∷ rest) refl = ≤-refl
skipNewlines-≤ (TArrow ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLambda ∷ rest) refl = ≤-refl
skipNewlines-≤ (TComma ∷ rest) refl = ≤-refl
skipNewlines-≤ (TSemicolon ∷ rest) refl = ≤-refl
skipNewlines-≤ (TAt ∷ rest) refl = ≤-refl
skipNewlines-≤ (TPipe ∷ rest) refl = ≤-refl
skipNewlines-≤ (TDot ∷ rest) refl = ≤-refl
skipNewlines-≤ (TPlus ∷ rest) refl = ≤-refl
skipNewlines-≤ (TMinus ∷ rest) refl = ≤-refl
skipNewlines-≤ (TStar ∷ rest) refl = ≤-refl
skipNewlines-≤ (TSlash ∷ rest) refl = ≤-refl
skipNewlines-≤ (TPercent ∷ rest) refl = ≤-refl
skipNewlines-≤ (TAmpersand ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLt ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLe ∷ rest) refl = ≤-refl
skipNewlines-≤ (TGt ∷ rest) refl = ≤-refl
skipNewlines-≤ (TGe ∷ rest) refl = ≤-refl
skipNewlines-≤ (TEqEq ∷ rest) refl = ≤-refl
skipNewlines-≤ (TNeq ∷ rest) refl = ≤-refl
skipNewlines-≤ (TCaret1 ∷ rest) refl = ≤-refl
skipNewlines-≤ (TCaret0 ∷ rest) refl = ≤-refl
skipNewlines-≤ (TCaretW ∷ rest) refl = ≤-refl
skipNewlines-≤ (TInt _ ∷ rest) refl = ≤-refl
skipNewlines-≤ (TString _ ∷ rest) refl = ≤-refl
skipNewlines-≤ (TEOF ∷ rest) refl = ≤-refl

-- | Well-founded parse of a list of declarations. Always succeeds,
-- returning `[]` plus the unchanged input when no declaration parses.
-- Each recursive call is on a strictly shorter residual, proved via
-- `parseDeclB`'s Σ-bound composed with `skipNewlines-≤`.
parseDeclsWF : (toks : List Token) → Acc _<_ (length toks) →
               Σ[ ds ∈ List Decl ] Σ[ rest ∈ List Token ]
                 length rest ≤ length toks
parseDeclsWF toks (acc rec) with skipNewlines toks in skipEq
... | nothing = [] , toks , ≤-refl
... | just (_ , toks') with parseDeclB toks' | skipNewlines-≤ toks skipEq
...   | nothing | skipBnd = [] , toks' , skipBnd
...   | just (d , rest , declBnd) | skipBnd
        with parseDeclsWF rest (rec (<-≤-trans declBnd skipBnd))
...     | (ds , rest' , restBnd) =
          d ∷ ds , rest' , ≤-trans restBnd (≤-trans (<⇒≤ declBnd) skipBnd)

-- | Parse all declarations (separated by newlines).
-- Termination: via well-founded recursion on token length. Each
-- successful `parseDecl` strictly shrinks the residual (`parseDeclB`'s
-- Σ-bound), while `skipNewlines` is weakly shrinking (≤). No
-- TERMINATING pragma is needed.
parseDecls : Parser (List Decl)
parseDecls toks with parseDeclsWF toks (<-wellFounded (length toks))
... | (ds , rest , _) = just (ds , rest)

-- | Parse a complete module
parseModule : Parser Module
parseModule toks with parseDecls toks
... | just (ds , rest) = just (mkModule ds , rest)
... | nothing = just (mkModule [] , toks)
