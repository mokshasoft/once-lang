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
open import Once.Parser.Module.Resolve public
open import Once.Parser.PolyType using (parsePolyTypeB)

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
parseDeclB (TWord w ∷ rest) | no _ | no _ with w ≟ "signature"
... | yes _ with parseSignatureB rest
...   | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
...   | nothing = nothing
parseDeclB (TWord w ∷ TColon ∷ rest) | no _ | no _ | no _ with parsePolyTypeB rest
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
skipNewlines-≤ (TBang ∷ rest) refl = ≤-refl
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
-- De-`with`'d via parameterized helpers (`pdwf-sk`/`pdwf-dc`): the `skipNewlines`
-- and `parseDeclB` results are ARGUMENTS, with their equations available, so the
-- verified decls-loop bridge (`Once.Adequacy.FrontEndBridge`) can case those
-- parameters WITHOUT the ill-typed-with-abstraction clash against an internal
-- `with skipNewlines`. Behaviour-identical to the old `with` form.
pdwf-dc : (toks : List Token) → (∀ {y} → y < length toks → Acc _<_ y) →
          (toks' : List Token) → length toks' ≤ length toks →
          ParseAtB {Decl} toks' →
          Σ[ ds ∈ List Decl ] Σ[ rest ∈ List Token ] length rest ≤ length toks
-- `pdwf-sk` takes the residual-bound as a FUNCTION of the (matched) `sk`, NOT
-- an equation `skipNewlines toks ≡ sk`. So `parseDeclsWF` passes `skipNewlines-≤
-- toks` (no self-referential `refl`), and BOTH bridge directions can reduce
-- `parseDeclsWF` under a `skipNewlines toks ≡ …` hypothesis without the
-- ill-typed-with-abstraction clash.
pdwf-sk : (toks : List Token) → (∀ {y} → y < length toks → Acc _<_ y) →
          (sk : Maybe (List Token × List Token)) →
          (∀ {nl toks'} → sk ≡ just (nl , toks') → length toks' ≤ length toks) →
          Σ[ ds ∈ List Decl ] Σ[ rest ∈ List Token ] length rest ≤ length toks
parseDeclsWF : (toks : List Token) → Acc _<_ (length toks) →
               Σ[ ds ∈ List Decl ] Σ[ rest ∈ List Token ]
                 length rest ≤ length toks

parseDeclsWF toks (acc rec) = pdwf-sk toks rec (skipNewlines toks) (skipNewlines-≤ toks)

pdwf-sk toks rec nothing             bnd = [] , toks , ≤-refl
pdwf-sk toks rec (just (nl , toks')) bnd =
  pdwf-dc toks rec toks' (bnd refl) (parseDeclB toks')

pdwf-dc toks rec toks' skipBnd nothing = [] , toks' , skipBnd
pdwf-dc toks rec toks' skipBnd (just (d , rest , declBnd)) =
  let r = parseDeclsWF rest (rec (<-≤-trans declBnd skipBnd))
  in d ∷ proj₁ r , proj₁ (proj₂ r) ,
     ≤-trans (proj₂ (proj₂ r)) (≤-trans (<⇒≤ declBnd) skipBnd)

-- | Parse all declarations (separated by newlines).
-- Termination: via well-founded recursion on token length. Each
-- successful `parseDecl` strictly shrinks the residual (`parseDeclB`'s
-- Σ-bound), while `skipNewlines` is weakly shrinking (≤). No
-- TERMINATING pragma is needed.
-- Projection-based (NO `with`) so `parseDecls toks` reduces definitionally to
-- `just (proj … parseDeclsWF …)` — the verified front-end's decls-loop bridge
-- (`Once.Adequacy.FrontEndBridge`) needs this to relate `parseDecls` to its
-- relation `ParsesDecls` without `with`-opacity.
parseDecls : Parser (List Decl)
parseDecls toks =
  just (proj₁ r , proj₁ (proj₂ r))
  where r = parseDeclsWF toks (<-wellFounded (length toks))

-- | Parse a complete module. Clause-based dispatch (NO `with`) on the
-- `parseDecls` result, so the verified front-end bridge can reduce
-- `parseModule` under a `parseDecls toks ≡ just (ds, rest)` hypothesis.
parseModule-pd : Maybe (List Decl × List Token) → List Token → Maybe (Module × List Token)
parseModule-pd (just (ds , rest)) _    = just (mkModule ds , rest)
parseModule-pd nothing            toks = just (mkModule [] , toks)

parseModule : Parser Module
parseModule toks = parseModule-pd (parseDecls toks) toks
