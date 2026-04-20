-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.DeclTail
--
-- Declarations whose leading identifier has been consumed (or will be
-- consumed locally): type aliases and primitive declarations.
------------------------------------------------------------------------

module Once.Parser.Module.DeclTail where

open import Data.List using (reverse)

open import Once.Parser.Module.Core

-- | Parameter-scanning helper inside parseTypeAlias. Consumes `=`
-- plus a type, so the residual is strictly shorter. Recursion shrinks
-- by one token when scanning a `TWord` parameter.
goTypeAliasB : String → (toks : List Token) → List String →
               ParseAtB {Decl} toks
goTypeAliasB name (TEquals ∷ rest') params with parseTypeB rest'
... | just (ty , rest'' , bnd) =
      just (DTypeAlias name (reverse params) ty , rest'' ,
            <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
goTypeAliasB name (TWord p ∷ rest') params with goTypeAliasB name rest' (p ∷ params)
... | just (d , rest'' , bnd) = just (d , rest'' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
goTypeAliasB _ _ _ = nothing

parseTypeAliasB : (toks : List Token) → ParseAtB {Decl} toks
parseTypeAliasB toks with anyWordB toks
... | nothing = nothing
... | just (name , rest , bnd) with goTypeAliasB name rest []
...   | just (d , rest' , bnd') = just (d , rest' , <-trans bnd' bnd)
...   | nothing = nothing

parseTypeAlias : Parser Decl
parseTypeAlias toks with parseTypeAliasB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

parsePrimitiveB : (toks : List Token) → ParseAtB {Decl} toks
parsePrimitiveB toks with anyWordB toks
... | nothing = nothing
... | just (name , TColon ∷ rest , bnd) with parseTypeB rest
...   | just (ty , rest' , bnd') =
        just (DPrimitive name ty , rest' ,
              <-trans (<-trans bnd' (s≤s ≤-refl)) bnd)
...   | nothing = nothing
parsePrimitiveB toks | just (_ , _ , _) = nothing

parsePrimitive : Parser Decl
parsePrimitive toks with parsePrimitiveB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
