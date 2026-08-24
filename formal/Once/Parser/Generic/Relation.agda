-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.Relation
--
-- The type-grammar parsing relation, parameterised over a `TyAlg` (AST builders)
-- + an extra-atom hook. One structure for both ground `Type` (extra = none) and
-- `PolyType` (extra = lowercase TVar). Tails use Bool/enum CLASSIFIER premises
-- (`isStar`/`isPlus`/`arrowDir`) + `drop1`/`drop2` bodies, so the parser routes
-- (no per-token enumeration) and the bridge proofs reduce. `Mu` reads a functor
-- SUM (the polynomial-functor fixpoint denotation; see Plan 0.7 Phase 2).
------------------------------------------------------------------------

module Once.Parser.Generic.Relation where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <-≤-trans; <⇒≤; m≤n⇒m≤1+n; n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Quantity; Zero; One; Many)
open import Once.Parser.Token

------------------------------------------------------------------------
-- Head classifiers + drops.
------------------------------------------------------------------------

isStar : List Token → Bool
isStar (TStar ∷ _) = true
isStar _           = false

isPlus : List Token → Bool
isPlus (TPlus ∷ _) = true
isPlus _           = false

data ArrowDir : Set where
  adG : Quantity → ArrowDir   -- grade + arrow (consume 2)
  adA : ArrowDir              -- plain arrow (consume 1)
  adR : ArrowDir              -- grade without arrow: reject
  adD : ArrowDir              -- done (no arrow tail)

arrowDir : List Token → ArrowDir
arrowDir (TCaret1 ∷ TArrow ∷ _) = adG One
arrowDir (TCaret0 ∷ TArrow ∷ _) = adG Zero
arrowDir (TCaretW ∷ TArrow ∷ _) = adG Many
arrowDir (TArrow ∷ _)           = adA
arrowDir (TCaret1 ∷ _)          = adR
arrowDir (TCaret0 ∷ _)          = adR
arrowDir (TCaretW ∷ _)          = adR
arrowDir _                      = adD

drop1 : List Token → List Token
drop1 []       = []
drop1 (_ ∷ xs) = xs

drop1-≤ : (xs : List Token) → length (drop1 xs) ≤ length xs
drop1-≤ []       = ≤-refl
drop1-≤ (_ ∷ xs) = m≤n⇒m≤1+n ≤-refl

drop2 : List Token → List Token
drop2 (_ ∷ _ ∷ xs) = xs
drop2 xs           = xs

drop2-≤ : (xs : List Token) → length (drop2 xs) ≤ length xs
drop2-≤ (_ ∷ _ ∷ xs) = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
drop2-≤ []           = ≤-refl
drop2-≤ (_ ∷ [])     = ≤-refl

------------------------------------------------------------------------
-- The algebra.
------------------------------------------------------------------------

record TyAlg : Set₁ where
  field
    R RF : Set
    aUnit aVoid aInt aFloat aBuffer aStr : R
    aProd aSum aEff : R → R → R
    aArrow : Quantity → R → R → R
    aMu : RF → R
    fK : R → RF
    fId : RF
    fSum fProd : RF → RF → RF
    Extra : List Token → R → List Token → Set
    extraShrink : ∀ {toks a rest} → Extra toks a rest → length rest < length toks
    -- executable extra-atom parser (tried first; only hits on extra atoms)
    extraP : (toks : List Token) → Maybe (Σ[ a ∈ R ] Σ[ rest ∈ List Token ] Extra toks a rest)
    extraComplete : ∀ {toks a rest} (ex : Extra toks a rest) → extraP toks ≡ just (a , rest , ex)
    extraMiss-Unit   : (rest : List Token) → extraP (TWord "Unit"   ∷ rest) ≡ nothing
    extraMiss-Void   : (rest : List Token) → extraP (TWord "Void"   ∷ rest) ≡ nothing
    extraMiss-Int    : (rest : List Token) → extraP (TWord "Int"    ∷ rest) ≡ nothing
    extraMiss-Float  : (rest : List Token) → extraP (TWord "Float"  ∷ rest) ≡ nothing
    extraMiss-Buffer : (rest : List Token) → extraP (TWord "Buffer" ∷ rest) ≡ nothing
    extraMiss-String : (rest : List Token) → extraP (TWord "String" ∷ rest) ≡ nothing
    extraMiss-Eff    : (rest : List Token) → extraP (TWord "Eff"    ∷ rest) ≡ nothing
    extraMiss-IO     : (rest : List Token) → extraP (TWord "IO"     ∷ rest) ≡ nothing
    extraMiss-Mu     : (rest : List Token) → extraP (TWord "Mu"     ∷ rest) ≡ nothing
    extraMiss-LParen : (rest : List Token) → extraP (TLParen ∷ rest) ≡ nothing

-- Strict-decrease lemmas for the classifier-routed tails (enumeration, ONCE).
isStar-< : (toks : List Token) → isStar toks ≡ true → length (drop1 toks) < length toks
isStar-< (TStar ∷ rest) eq = s≤s ≤-refl
isStar-< [] ()
isStar-< (TWord _ ∷ _) ()
isStar-< (TInt _ _ ∷ _) ()
isStar-< (TString _ ∷ _) ()
isStar-< (TLParen ∷ _) ()
isStar-< (TRParen ∷ _) ()
isStar-< (TLBrace ∷ _) ()
isStar-< (TRBrace ∷ _) ()
isStar-< (TColon ∷ _) ()
isStar-< (TEquals ∷ _) ()
isStar-< (TArrow ∷ _) ()
isStar-< (TCaret1 ∷ _) ()
isStar-< (TCaret0 ∷ _) ()
isStar-< (TCaretW ∷ _) ()
isStar-< (TLambda ∷ _) ()
isStar-< (TComma ∷ _) ()
isStar-< (TSemicolon ∷ _) ()
isStar-< (TAt ∷ _) ()
isStar-< (TPipe ∷ _) ()
isStar-< (TDot ∷ _) ()
isStar-< (TPlus ∷ _) ()
isStar-< (TMinus ∷ _) ()
isStar-< (TSlash ∷ _) ()
isStar-< (TPercent ∷ _) ()
isStar-< (TAmpersand ∷ _) ()
isStar-< (TLt ∷ _) ()
isStar-< (TLe ∷ _) ()
isStar-< (TGt ∷ _) ()
isStar-< (TGe ∷ _) ()
isStar-< (TEqEq ∷ _) ()
isStar-< (TNeq ∷ _) ()
isStar-< (TBang ∷ _) ()
isStar-< (TNewline ∷ _) ()
isStar-< (TEOF ∷ _) ()

isPlus-< : (toks : List Token) → isPlus toks ≡ true → length (drop1 toks) < length toks
isPlus-< (TPlus ∷ rest) eq = s≤s ≤-refl
isPlus-< [] ()
isPlus-< (TWord _ ∷ _) ()
isPlus-< (TInt _ _ ∷ _) ()
isPlus-< (TString _ ∷ _) ()
isPlus-< (TLParen ∷ _) ()
isPlus-< (TRParen ∷ _) ()
isPlus-< (TLBrace ∷ _) ()
isPlus-< (TRBrace ∷ _) ()
isPlus-< (TColon ∷ _) ()
isPlus-< (TEquals ∷ _) ()
isPlus-< (TArrow ∷ _) ()
isPlus-< (TCaret1 ∷ _) ()
isPlus-< (TCaret0 ∷ _) ()
isPlus-< (TCaretW ∷ _) ()
isPlus-< (TLambda ∷ _) ()
isPlus-< (TComma ∷ _) ()
isPlus-< (TSemicolon ∷ _) ()
isPlus-< (TAt ∷ _) ()
isPlus-< (TPipe ∷ _) ()
isPlus-< (TDot ∷ _) ()
isPlus-< (TMinus ∷ _) ()
isPlus-< (TStar ∷ _) ()
isPlus-< (TSlash ∷ _) ()
isPlus-< (TPercent ∷ _) ()
isPlus-< (TAmpersand ∷ _) ()
isPlus-< (TLt ∷ _) ()
isPlus-< (TLe ∷ _) ()
isPlus-< (TGt ∷ _) ()
isPlus-< (TGe ∷ _) ()
isPlus-< (TEqEq ∷ _) ()
isPlus-< (TNeq ∷ _) ()
isPlus-< (TBang ∷ _) ()
isPlus-< (TNewline ∷ _) ()
isPlus-< (TEOF ∷ _) ()

arrowDir-A-< : (toks : List Token) → arrowDir toks ≡ adA → length (drop1 toks) < length toks
arrowDir-A-< (TArrow ∷ rest) eq = s≤s ≤-refl
arrowDir-A-< [] ()
arrowDir-A-< (TWord _ ∷ _) ()
arrowDir-A-< (TInt _ _ ∷ _) ()
arrowDir-A-< (TString _ ∷ _) ()
arrowDir-A-< (TLParen ∷ _) ()
arrowDir-A-< (TRParen ∷ _) ()
arrowDir-A-< (TLBrace ∷ _) ()
arrowDir-A-< (TRBrace ∷ _) ()
arrowDir-A-< (TColon ∷ _) ()
arrowDir-A-< (TEquals ∷ _) ()
arrowDir-A-< (TLambda ∷ _) ()
arrowDir-A-< (TComma ∷ _) ()
arrowDir-A-< (TSemicolon ∷ _) ()
arrowDir-A-< (TAt ∷ _) ()
arrowDir-A-< (TPipe ∷ _) ()
arrowDir-A-< (TDot ∷ _) ()
arrowDir-A-< (TPlus ∷ _) ()
arrowDir-A-< (TMinus ∷ _) ()
arrowDir-A-< (TStar ∷ _) ()
arrowDir-A-< (TSlash ∷ _) ()
arrowDir-A-< (TPercent ∷ _) ()
arrowDir-A-< (TAmpersand ∷ _) ()
arrowDir-A-< (TLt ∷ _) ()
arrowDir-A-< (TLe ∷ _) ()
arrowDir-A-< (TGt ∷ _) ()
arrowDir-A-< (TGe ∷ _) ()
arrowDir-A-< (TEqEq ∷ _) ()
arrowDir-A-< (TNeq ∷ _) ()
arrowDir-A-< (TBang ∷ _) ()
arrowDir-A-< (TNewline ∷ _) ()
arrowDir-A-< (TEOF ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TArrow ∷ _) ()
arrowDir-A-< (TCaret1 ∷ []) ()
arrowDir-A-< (TCaret1 ∷ TWord _ ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TInt _ _ ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TString _ ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TLParen ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TRParen ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TLBrace ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TRBrace ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TColon ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TEquals ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TCaret1 ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TCaret0 ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TCaretW ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TLambda ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TComma ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TSemicolon ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TAt ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TPipe ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TDot ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TPlus ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TMinus ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TStar ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TSlash ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TPercent ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TAmpersand ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TLt ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TLe ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TGt ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TGe ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TEqEq ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TNeq ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TBang ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TNewline ∷ _) ()
arrowDir-A-< (TCaret1 ∷ TEOF ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TArrow ∷ _) ()
arrowDir-A-< (TCaret0 ∷ []) ()
arrowDir-A-< (TCaret0 ∷ TWord _ ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TInt _ _ ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TString _ ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TLParen ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TRParen ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TLBrace ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TRBrace ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TColon ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TEquals ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TCaret1 ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TCaret0 ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TCaretW ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TLambda ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TComma ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TSemicolon ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TAt ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TPipe ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TDot ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TPlus ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TMinus ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TStar ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TSlash ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TPercent ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TAmpersand ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TLt ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TLe ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TGt ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TGe ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TEqEq ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TNeq ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TBang ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TNewline ∷ _) ()
arrowDir-A-< (TCaret0 ∷ TEOF ∷ _) ()
arrowDir-A-< (TCaretW ∷ TArrow ∷ _) ()
arrowDir-A-< (TCaretW ∷ []) ()
arrowDir-A-< (TCaretW ∷ TWord _ ∷ _) ()
arrowDir-A-< (TCaretW ∷ TInt _ _ ∷ _) ()
arrowDir-A-< (TCaretW ∷ TString _ ∷ _) ()
arrowDir-A-< (TCaretW ∷ TLParen ∷ _) ()
arrowDir-A-< (TCaretW ∷ TRParen ∷ _) ()
arrowDir-A-< (TCaretW ∷ TLBrace ∷ _) ()
arrowDir-A-< (TCaretW ∷ TRBrace ∷ _) ()
arrowDir-A-< (TCaretW ∷ TColon ∷ _) ()
arrowDir-A-< (TCaretW ∷ TEquals ∷ _) ()
arrowDir-A-< (TCaretW ∷ TCaret1 ∷ _) ()
arrowDir-A-< (TCaretW ∷ TCaret0 ∷ _) ()
arrowDir-A-< (TCaretW ∷ TCaretW ∷ _) ()
arrowDir-A-< (TCaretW ∷ TLambda ∷ _) ()
arrowDir-A-< (TCaretW ∷ TComma ∷ _) ()
arrowDir-A-< (TCaretW ∷ TSemicolon ∷ _) ()
arrowDir-A-< (TCaretW ∷ TAt ∷ _) ()
arrowDir-A-< (TCaretW ∷ TPipe ∷ _) ()
arrowDir-A-< (TCaretW ∷ TDot ∷ _) ()
arrowDir-A-< (TCaretW ∷ TPlus ∷ _) ()
arrowDir-A-< (TCaretW ∷ TMinus ∷ _) ()
arrowDir-A-< (TCaretW ∷ TStar ∷ _) ()
arrowDir-A-< (TCaretW ∷ TSlash ∷ _) ()
arrowDir-A-< (TCaretW ∷ TPercent ∷ _) ()
arrowDir-A-< (TCaretW ∷ TAmpersand ∷ _) ()
arrowDir-A-< (TCaretW ∷ TLt ∷ _) ()
arrowDir-A-< (TCaretW ∷ TLe ∷ _) ()
arrowDir-A-< (TCaretW ∷ TGt ∷ _) ()
arrowDir-A-< (TCaretW ∷ TGe ∷ _) ()
arrowDir-A-< (TCaretW ∷ TEqEq ∷ _) ()
arrowDir-A-< (TCaretW ∷ TNeq ∷ _) ()
arrowDir-A-< (TCaretW ∷ TBang ∷ _) ()
arrowDir-A-< (TCaretW ∷ TNewline ∷ _) ()
arrowDir-A-< (TCaretW ∷ TEOF ∷ _) ()

arrowDir-G-< : (toks : List Token) {q : Quantity} → arrowDir toks ≡ adG q → length (drop2 toks) < length toks
arrowDir-G-< (TCaret1 ∷ TArrow ∷ rest) eq = s≤s (n≤1+n _)
arrowDir-G-< (TCaret0 ∷ TArrow ∷ rest) eq = s≤s (n≤1+n _)
arrowDir-G-< (TCaretW ∷ TArrow ∷ rest) eq = s≤s (n≤1+n _)
arrowDir-G-< [] ()
arrowDir-G-< (TArrow ∷ _) ()
arrowDir-G-< (TWord _ ∷ _) ()
arrowDir-G-< (TInt _ _ ∷ _) ()
arrowDir-G-< (TString _ ∷ _) ()
arrowDir-G-< (TLParen ∷ _) ()
arrowDir-G-< (TRParen ∷ _) ()
arrowDir-G-< (TLBrace ∷ _) ()
arrowDir-G-< (TRBrace ∷ _) ()
arrowDir-G-< (TColon ∷ _) ()
arrowDir-G-< (TEquals ∷ _) ()
arrowDir-G-< (TLambda ∷ _) ()
arrowDir-G-< (TComma ∷ _) ()
arrowDir-G-< (TSemicolon ∷ _) ()
arrowDir-G-< (TAt ∷ _) ()
arrowDir-G-< (TPipe ∷ _) ()
arrowDir-G-< (TDot ∷ _) ()
arrowDir-G-< (TPlus ∷ _) ()
arrowDir-G-< (TMinus ∷ _) ()
arrowDir-G-< (TStar ∷ _) ()
arrowDir-G-< (TSlash ∷ _) ()
arrowDir-G-< (TPercent ∷ _) ()
arrowDir-G-< (TAmpersand ∷ _) ()
arrowDir-G-< (TLt ∷ _) ()
arrowDir-G-< (TLe ∷ _) ()
arrowDir-G-< (TGt ∷ _) ()
arrowDir-G-< (TGe ∷ _) ()
arrowDir-G-< (TEqEq ∷ _) ()
arrowDir-G-< (TNeq ∷ _) ()
arrowDir-G-< (TBang ∷ _) ()
arrowDir-G-< (TNewline ∷ _) ()
arrowDir-G-< (TEOF ∷ _) ()
arrowDir-G-< (TCaret1 ∷ []) ()
arrowDir-G-< (TCaret1 ∷ TWord _ ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TInt _ _ ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TString _ ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TLParen ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TRParen ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TLBrace ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TRBrace ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TColon ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TEquals ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TCaret1 ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TCaret0 ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TCaretW ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TLambda ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TComma ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TSemicolon ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TAt ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TPipe ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TDot ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TPlus ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TMinus ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TStar ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TSlash ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TPercent ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TAmpersand ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TLt ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TLe ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TGt ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TGe ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TEqEq ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TNeq ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TBang ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TNewline ∷ _) ()
arrowDir-G-< (TCaret1 ∷ TEOF ∷ _) ()
arrowDir-G-< (TCaret0 ∷ []) ()
arrowDir-G-< (TCaret0 ∷ TWord _ ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TInt _ _ ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TString _ ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TLParen ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TRParen ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TLBrace ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TRBrace ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TColon ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TEquals ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TCaret1 ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TCaret0 ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TCaretW ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TLambda ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TComma ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TSemicolon ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TAt ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TPipe ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TDot ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TPlus ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TMinus ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TStar ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TSlash ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TPercent ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TAmpersand ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TLt ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TLe ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TGt ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TGe ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TEqEq ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TNeq ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TBang ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TNewline ∷ _) ()
arrowDir-G-< (TCaret0 ∷ TEOF ∷ _) ()
arrowDir-G-< (TCaretW ∷ []) ()
arrowDir-G-< (TCaretW ∷ TWord _ ∷ _) ()
arrowDir-G-< (TCaretW ∷ TInt _ _ ∷ _) ()
arrowDir-G-< (TCaretW ∷ TString _ ∷ _) ()
arrowDir-G-< (TCaretW ∷ TLParen ∷ _) ()
arrowDir-G-< (TCaretW ∷ TRParen ∷ _) ()
arrowDir-G-< (TCaretW ∷ TLBrace ∷ _) ()
arrowDir-G-< (TCaretW ∷ TRBrace ∷ _) ()
arrowDir-G-< (TCaretW ∷ TColon ∷ _) ()
arrowDir-G-< (TCaretW ∷ TEquals ∷ _) ()
arrowDir-G-< (TCaretW ∷ TCaret1 ∷ _) ()
arrowDir-G-< (TCaretW ∷ TCaret0 ∷ _) ()
arrowDir-G-< (TCaretW ∷ TCaretW ∷ _) ()
arrowDir-G-< (TCaretW ∷ TLambda ∷ _) ()
arrowDir-G-< (TCaretW ∷ TComma ∷ _) ()
arrowDir-G-< (TCaretW ∷ TSemicolon ∷ _) ()
arrowDir-G-< (TCaretW ∷ TAt ∷ _) ()
arrowDir-G-< (TCaretW ∷ TPipe ∷ _) ()
arrowDir-G-< (TCaretW ∷ TDot ∷ _) ()
arrowDir-G-< (TCaretW ∷ TPlus ∷ _) ()
arrowDir-G-< (TCaretW ∷ TMinus ∷ _) ()
arrowDir-G-< (TCaretW ∷ TStar ∷ _) ()
arrowDir-G-< (TCaretW ∷ TSlash ∷ _) ()
arrowDir-G-< (TCaretW ∷ TPercent ∷ _) ()
arrowDir-G-< (TCaretW ∷ TAmpersand ∷ _) ()
arrowDir-G-< (TCaretW ∷ TLt ∷ _) ()
arrowDir-G-< (TCaretW ∷ TLe ∷ _) ()
arrowDir-G-< (TCaretW ∷ TGt ∷ _) ()
arrowDir-G-< (TCaretW ∷ TGe ∷ _) ()
arrowDir-G-< (TCaretW ∷ TEqEq ∷ _) ()
arrowDir-G-< (TCaretW ∷ TNeq ∷ _) ()
arrowDir-G-< (TCaretW ∷ TBang ∷ _) ()
arrowDir-G-< (TCaretW ∷ TNewline ∷ _) ()
arrowDir-G-< (TCaretW ∷ TEOF ∷ _) ()

module Gen (alg : TyAlg) where
  open TyAlg alg

  mutual
    data ParsesAtomG : List Token → R → List Token → Set where
      pa-unit   : ∀ rest → ParsesAtomG (TWord "Unit"   ∷ rest) aUnit   rest
      pa-void   : ∀ rest → ParsesAtomG (TWord "Void"   ∷ rest) aVoid   rest
      pa-int    : ∀ rest → ParsesAtomG (TWord "Int"    ∷ rest) aInt    rest
      pa-float  : ∀ rest → ParsesAtomG (TWord "Float"  ∷ rest) aFloat  rest
      pa-buffer : ∀ rest → ParsesAtomG (TWord "Buffer" ∷ rest) aBuffer rest
      pa-string : ∀ rest → ParsesAtomG (TWord "String" ∷ rest) aStr    rest
      pa-eff : ∀ {toks1 toks2 rest} {A B : R}
             → ParsesAtomG toks1 A toks2 → ParsesAtomG toks2 B rest
             → ParsesAtomG (TWord "Eff" ∷ toks1) (aEff A B) rest
      pa-io : ∀ {toks1 rest} {A : R}
            → ParsesAtomG toks1 A rest → ParsesAtomG (TWord "IO" ∷ toks1) (aEff aUnit A) rest
      pa-mu : ∀ {toks rest} {F : RF}
            → ParsesFuncSumG toks F rest → ParsesAtomG (TWord "Mu" ∷ toks) (aMu F) rest
      pa-extra : ∀ {toks a rest} → Extra toks a rest → ParsesAtomG toks a rest
      pa-paren : ∀ {toks rest1 rest2} {T : R}
               → ParsesTypeG toks T rest1 → rest1 ≡ TRParen ∷ rest2
               → ParsesAtomG (TLParen ∷ toks) T rest2

    data ParsesProdG : List Token → R → List Token → Set where
      pp-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesAtomG toks A toks1 → ParsesProdTailG A toks1 T rest → ParsesProdG toks T rest

    data ParsesProdTailG : R → List Token → R → List Token → Set where
      ppt-done : ∀ {l toks} → isStar toks ≡ false → ParsesProdTailG l toks l toks
      ppt-star : ∀ {l toks toks2 rest} {B T : R} → isStar toks ≡ true
               → ParsesAtomG (drop1 toks) B toks2 → ParsesProdTailG (aProd l B) toks2 T rest
               → ParsesProdTailG l toks T rest

    data ParsesSumG : List Token → R → List Token → Set where
      ps-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesProdG toks A toks1 → ParsesSumTailG A toks1 T rest → ParsesSumG toks T rest

    data ParsesSumTailG : R → List Token → R → List Token → Set where
      pst-done : ∀ {l toks} → isPlus toks ≡ false → ParsesSumTailG l toks l toks
      pst-plus : ∀ {l toks toks2 rest} {B T : R} → isPlus toks ≡ true
               → ParsesProdG (drop1 toks) B toks2 → ParsesSumTailG (aSum l B) toks2 T rest
               → ParsesSumTailG l toks T rest

    data ParsesTypeG : List Token → R → List Token → Set where
      pt-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesSumG toks A toks1 → ParsesArrowTailG A toks1 T rest → ParsesTypeG toks T rest

    data ParsesArrowTailG : R → List Token → R → List Token → Set where
      pat-done : ∀ {l toks} → arrowDir toks ≡ adD → ParsesArrowTailG l toks l toks
      pat-arrow-g : ∀ {l toks rest} {B : R} {q : Quantity} → arrowDir toks ≡ adG q
                  → ParsesTypeG (drop2 toks) B rest → ParsesArrowTailG l toks (aArrow q l B) rest
      pat-arrow : ∀ {l toks rest} {B : R} → arrowDir toks ≡ adA
                → ParsesTypeG (drop1 toks) B rest → ParsesArrowTailG l toks (aArrow Many l B) rest

    data ParsesFuncAtomG : List Token → RF → List Token → Set where
      pfa-id : ∀ rest → ParsesFuncAtomG (TWord "Id" ∷ rest) fId rest
      pfa-k  : ∀ {toks rest} {A : R}
             → ParsesAtomG toks A rest → ParsesFuncAtomG (TWord "K" ∷ toks) (fK A) rest
      pfa-paren : ∀ {toks rest1 rest2} {F : RF}
                → ParsesFuncSumG toks F rest1 → rest1 ≡ TRParen ∷ rest2
                → ParsesFuncAtomG (TLParen ∷ toks) F rest2

    data ParsesFuncProdG : List Token → RF → List Token → Set where
      pfp-mk : ∀ {toks toks1 rest} {A F : RF}
             → ParsesFuncAtomG toks A toks1 → ParsesFuncProdTailG A toks1 F rest → ParsesFuncProdG toks F rest

    data ParsesFuncProdTailG : RF → List Token → RF → List Token → Set where
      pfpt-done : ∀ {l toks} → isStar toks ≡ false → ParsesFuncProdTailG l toks l toks
      pfpt-star : ∀ {l toks toks2 rest} {B F : RF} → isStar toks ≡ true
                → ParsesFuncAtomG (drop1 toks) B toks2 → ParsesFuncProdTailG (fProd l B) toks2 F rest
                → ParsesFuncProdTailG l toks F rest

    data ParsesFuncSumG : List Token → RF → List Token → Set where
      pfs-mk : ∀ {toks toks1 rest} {A F : RF}
             → ParsesFuncProdG toks A toks1 → ParsesFuncSumTailG A toks1 F rest → ParsesFuncSumG toks F rest

    data ParsesFuncSumTailG : RF → List Token → RF → List Token → Set where
      pfst-done : ∀ {l toks} → isPlus toks ≡ false → ParsesFuncSumTailG l toks l toks
      pfst-plus : ∀ {l toks toks2 rest} {B F : RF} → isPlus toks ≡ true
                → ParsesFuncProdG (drop1 toks) B toks2 → ParsesFuncSumTailG (fSum l B) toks2 F rest
                → ParsesFuncSumTailG l toks F rest

  ------------------------------------------------------------------------
  -- Shrinks.
  ------------------------------------------------------------------------
  mutual
    atomShrink : ∀ {toks T rest} → ParsesAtomG toks T rest → length rest < length toks
    atomShrink (pa-unit rest)   = s≤s ≤-refl
    atomShrink (pa-void rest)   = s≤s ≤-refl
    atomShrink (pa-int rest)    = s≤s ≤-refl
    atomShrink (pa-float rest)  = s≤s ≤-refl
    atomShrink (pa-buffer rest) = s≤s ≤-refl
    atomShrink (pa-string rest) = s≤s ≤-refl
    atomShrink (pa-eff dA dB) = <-trans (atomShrink dB) (<-trans (atomShrink dA) (s≤s ≤-refl))
    atomShrink (pa-io dA) = <-trans (atomShrink dA) (s≤s ≤-refl)
    atomShrink (pa-mu dF) = <-trans (funcSumShrink dF) (s≤s ≤-refl)
    atomShrink (pa-extra ex) = extraShrink ex
    atomShrink (pa-paren dT refl) = <-trans (s≤s ≤-refl) (<-trans (typeShrink dT) (s≤s ≤-refl))

    prodShrink : ∀ {toks T rest} → ParsesProdG toks T rest → length rest < length toks
    prodShrink (pp-mk dA dT) = ≤-<-trans (prodTailShrink dT) (atomShrink dA)

    prodTailShrink : ∀ {l toks T rest} → ParsesProdTailG l toks T rest → length rest ≤ length toks
    prodTailShrink (ppt-done _) = ≤-refl
    prodTailShrink {toks = toks} (ppt-star _ dB dT) =
      <⇒≤ (≤-<-trans (prodTailShrink dT) (<-≤-trans (atomShrink dB) (drop1-≤ toks)))

    sumShrink : ∀ {toks T rest} → ParsesSumG toks T rest → length rest < length toks
    sumShrink (ps-mk dA dT) = ≤-<-trans (sumTailShrink dT) (prodShrink dA)

    sumTailShrink : ∀ {l toks T rest} → ParsesSumTailG l toks T rest → length rest ≤ length toks
    sumTailShrink (pst-done _) = ≤-refl
    sumTailShrink {toks = toks} (pst-plus _ dB dT) =
      <⇒≤ (≤-<-trans (sumTailShrink dT) (<-≤-trans (prodShrink dB) (drop1-≤ toks)))

    arrowTailShrink : ∀ {l toks T rest} → ParsesArrowTailG l toks T rest → length rest ≤ length toks
    arrowTailShrink (pat-done _) = ≤-refl
    arrowTailShrink {toks = toks} (pat-arrow-g _ dT) = <⇒≤ (<-≤-trans (typeShrink dT) (drop2-≤ toks))
    arrowTailShrink {toks = toks} (pat-arrow _ dT) = <⇒≤ (<-≤-trans (typeShrink dT) (drop1-≤ toks))

    typeShrink : ∀ {toks T rest} → ParsesTypeG toks T rest → length rest < length toks
    typeShrink (pt-mk dS dA) = ≤-<-trans (arrowTailShrink dA) (sumShrink dS)

    funcAtomShrink : ∀ {toks F rest} → ParsesFuncAtomG toks F rest → length rest < length toks
    funcAtomShrink (pfa-id rest) = s≤s ≤-refl
    funcAtomShrink (pfa-k dA) = <-trans (atomShrink dA) (s≤s ≤-refl)
    funcAtomShrink (pfa-paren dF refl) = <-trans (s≤s ≤-refl) (<-trans (funcSumShrink dF) (s≤s ≤-refl))

    funcProdShrink : ∀ {toks F rest} → ParsesFuncProdG toks F rest → length rest < length toks
    funcProdShrink (pfp-mk dA dT) = ≤-<-trans (funcProdTailShrink dT) (funcAtomShrink dA)

    funcProdTailShrink : ∀ {l toks F rest} → ParsesFuncProdTailG l toks F rest → length rest ≤ length toks
    funcProdTailShrink (pfpt-done _) = ≤-refl
    funcProdTailShrink {toks = toks} (pfpt-star _ dB dT) =
      <⇒≤ (≤-<-trans (funcProdTailShrink dT) (<-≤-trans (funcAtomShrink dB) (drop1-≤ toks)))

    funcSumShrink : ∀ {toks F rest} → ParsesFuncSumG toks F rest → length rest < length toks
    funcSumShrink (pfs-mk dA dT) = ≤-<-trans (funcSumTailShrink dT) (funcProdShrink dA)

    funcSumTailShrink : ∀ {l toks F rest} → ParsesFuncSumTailG l toks F rest → length rest ≤ length toks
    funcSumTailShrink (pfst-done _) = ≤-refl
    funcSumTailShrink {toks = toks} (pfst-plus _ dB dT) =
      <⇒≤ (≤-<-trans (funcSumTailShrink dT) (<-≤-trans (funcProdShrink dB) (drop1-≤ toks)))
