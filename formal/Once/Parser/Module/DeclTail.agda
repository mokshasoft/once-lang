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
open import Once.Parser.PolyType using (parsePolyTypeB)

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

-- | Map a shape word to its `SigEffect`. Only `halts`/`emits` are
-- recognised; anything else is not a shape (the `!` is left in place,
-- so the decl parser reports the stray token). Plan 0.38 M0.2.
shapeWord : String → Maybe SigEffect
shapeWord w with w ≟ "halts"
... | yes _ = just halts
... | no _ with w ≟ "emits"
...   | yes _ = just emits
...   | no _  = nothing

-- | Optional trailing `! <shape>` EffectShape annotation. Consumes the
-- two tokens `TBang ∷ TWord <shape>` when `<shape>` is a recognised
-- shape word; otherwise consumes nothing. The remainder is never longer
-- than the input.
parseEffAnnot : (toks : List Token) →
                Maybe SigEffect ×
                Σ[ rest ∈ List Token ] (length rest ≤ length toks)
parseEffAnnot (TBang ∷ TWord w ∷ rest) with shapeWord w
... | just se = just se , rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
... | nothing = nothing , TBang ∷ TWord w ∷ rest , ≤-refl
parseEffAnnot toks = nothing , toks , ≤-refl

parseSignatureB : (toks : List Token) → ParseAtB {Decl} toks
parseSignatureB toks with anyWordB toks
... | nothing = nothing
... | just (name , TColon ∷ rest , bnd) with parsePolyTypeB rest
...   | just (ty , rest' , bnd') with parseEffAnnot rest'
...     | (meff , rest'' , bndE) =
          just (DSignature name nothing ty meff , rest'' ,
                ≤-<-trans bndE (<-trans (<-trans bnd' (s≤s ≤-refl)) bnd))
parseSignatureB toks | just (_ , TColon ∷ rest , bnd) | nothing = nothing
parseSignatureB toks | just (_ , _ , _) = nothing

parseSignature : Parser Decl
parseSignature toks with parseSignatureB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
