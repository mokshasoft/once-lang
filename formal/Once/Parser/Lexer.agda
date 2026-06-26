-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Lexer
--
-- Tokenizer for the Once language.
-- Converts a string (List Char) into a list of tokens.
--
-- Termination note. `tokenize` is defined by well-founded recursion on
-- the length of its input list (via `<-wellFounded` from the standard
-- library). Helpers that can consume multiple characters at once
-- (`skipLine`, `skipBlock`, `collectString`, `collectDigits`,
-- `collectIdent`) return their result paired with a length-bound
-- witness so that the main recursion can produce a fresh Acc witness
-- for each recursive call.
------------------------------------------------------------------------

module Once.Parser.Lexer where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂; Σ-syntax)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Char using (Char; isAlpha; isDigit; isSpace; isLower)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n; n≤1+n; <-trans; m≤n⇒m≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Integer using (ℤ; +_)
open import Data.String using (String; fromList; toList)
open import Agda.Builtin.Char using (primCharEquality; primCharToNat)

-- | Convert Char to ℕ (character code)
toNat : Char → ℕ
toNat = primCharToNat

open import Once.Parser.Token

------------------------------------------------------------------------
-- Character Classification
------------------------------------------------------------------------

-- | Is this character an identifier start? [a-zA-Z_]
isIdentStart : Char → Bool
isIdentStart c = isAlpha c ∨ (toNat c ≡ᵇ toNat '_')

-- | Is this character an identifier continuation? [a-zA-Z0-9_'+*!?]
isIdentContinue : Char → Bool
isIdentContinue c =
  isAlpha c ∨ isDigit c ∨
  (toNat c ≡ᵇ toNat '_') ∨
  (toNat c ≡ᵇ toNat '\'') ∨
  (toNat c ≡ᵇ toNat '+') ∨
  (toNat c ≡ᵇ toNat '*') ∨
  (toNat c ≡ᵇ toNat '!') ∨
  (toNat c ≡ᵇ toNat '?')

-- | Character equality
_==c_ : Char → Char → Bool
c₁ ==c c₂ = primCharEquality c₁ c₂

------------------------------------------------------------------------
-- Bounded-consumption helpers.
--
-- Each helper returns its result paired with a proof that the remaining
-- input has length bounded by the input. This makes the well-founded
-- recursion in `tokenize-WF` definable without needing separate
-- length-bound lemmas on functions whose reduction behaviour is
-- obstructed by literal-character patterns.
------------------------------------------------------------------------

-- Bounded result: a payload `P` paired with a remainder whose length is
-- bounded above by `n`.
Bounded : Set → ℕ → Set
Bounded P n = Σ[ p ∈ P ] Σ[ rest ∈ List Char ] (length rest ≤ n)

BoundedStrict : Set → ℕ → Set
BoundedStrict P n = Σ[ p ∈ P ] Σ[ rest ∈ List Char ] (length rest < n)

-- | Collect identifier continuation characters.
collectIdentB : (cs : List Char) → Bounded (List Char) (length cs)
collectIdentB [] = [] , [] , z≤n
collectIdentB (c ∷ cs) with isDigit c | isIdentContinue c
... | _ | true = let (ident , rest , bnd) = collectIdentB cs
                 in  c ∷ ident , rest , m≤n⇒m≤1+n bnd
... | _ | false = [] , c ∷ cs , ≤-refl

-- | Plain un-wrapped version for readability where the bound isn't
-- needed (e.g. at the top-level caller once we've extracted fields).
collectIdent : List Char → List Char × List Char
collectIdent cs =
  let (id , rest , _) = collectIdentB cs
  in id , rest

-- | Collect digits.
collectDigitsB : (cs : List Char) → Bounded (List Char) (length cs)
collectDigitsB [] = [] , [] , z≤n
collectDigitsB (c ∷ cs) with isDigit c
... | true = let (digs , rest , bnd) = collectDigitsB cs
             in  c ∷ digs , rest , m≤n⇒m≤1+n bnd
... | false = [] , c ∷ cs , ≤-refl

collectDigits : List Char → List Char × List Char
collectDigits cs =
  let (ds , rest , _) = collectDigitsB cs
  in ds , rest

-- | Convert digit chars to natural number.
digitsToNat : List Char → ℕ
digitsToNat = go 0
  where
  charToDigit : Char → ℕ
  charToDigit c = toNat c Data.Nat.∸ toNat '0'

  go : ℕ → List Char → ℕ
  go a [] = a
  go a (c ∷ cs) = go (a Data.Nat.* 10 Data.Nat.+ charToDigit c) cs

-- | Collect string literal contents (after the opening `"`).
-- On success, the remainder is strictly shorter than the input.
-- On failure (unterminated string), returns `nothing`.
collectStringB : (cs : List Char) →
                 Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ]
                          length rest < length cs)
collectStringB [] = nothing
collectStringB ('"' ∷ cs) = just ([] , cs , s≤s ≤-refl)
collectStringB ('\\' ∷ 'n' ∷ cs) with collectStringB cs
... | just (s , rest , bnd) =
        just ('\n' ∷ s , rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n bnd))
... | nothing = nothing
collectStringB ('\\' ∷ 't' ∷ cs) with collectStringB cs
... | just (s , rest , bnd) =
        just ('\t' ∷ s , rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n bnd))
... | nothing = nothing
collectStringB ('\\' ∷ 'r' ∷ cs) with collectStringB cs
... | just (s , rest , bnd) =
        just ('\r' ∷ s , rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n bnd))
... | nothing = nothing
collectStringB ('\\' ∷ '\\' ∷ cs) with collectStringB cs
... | just (s , rest , bnd) =
        just ('\\' ∷ s , rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n bnd))
... | nothing = nothing
collectStringB ('\\' ∷ '"' ∷ cs) with collectStringB cs
... | just (s , rest , bnd) =
        just ('"' ∷ s , rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n bnd))
... | nothing = nothing
collectStringB (c ∷ cs) with collectStringB cs
... | just (s , rest , bnd) = just (c ∷ s , rest , m≤n⇒m≤1+n bnd)
... | nothing = nothing

collectString : List Char → Maybe (List Char × List Char)
collectString cs with collectStringB cs
... | just (s , rest , _) = just (s , rest)
... | nothing = nothing

-- | Skip to end of line (for line comments).
-- Always returns a list of length ≤ the input.
skipLineB : (cs : List Char) → Σ[ rest ∈ List Char ] (length rest ≤ length cs)
skipLineB [] = [] , z≤n
skipLineB ('\n' ∷ cs) = '\n' ∷ cs , ≤-refl
skipLineB (c ∷ cs) with c ==c '\n'
... | true  = c ∷ cs , ≤-refl
... | false = let (rest , bnd) = skipLineB cs
              in  rest , m≤n⇒m≤1+n bnd

skipLine : List Char → List Char
skipLine cs = proj₁ (skipLineB cs)

skipLine-length : ∀ cs → length (skipLine cs) ≤ length cs
skipLine-length cs = proj₂ (skipLineB cs)

-- | Skip block comment (handles nesting). We use well-founded
-- recursion on `length cs` so the definition can dispatch via
-- boolean equality tests without tripping Agda's structural
-- termination checker.
skipBlockB-WF : ℕ → (cs : List Char) → Acc _<_ (length cs) →
                Σ[ rest ∈ List Char ] (length rest ≤ length cs)
skipBlockB-WF zero    cs       _         = cs , ≤-refl
skipBlockB-WF (suc _) []       _         = [] , z≤n
skipBlockB-WF (suc n) (c ∷ []) (acc rec) =
  let (rest , bnd) = skipBlockB-WF (suc n) [] (rec (s≤s z≤n))
  in  rest , m≤n⇒m≤1+n bnd
skipBlockB-WF (suc n) (c₁ ∷ c₂ ∷ cs) (acc rec)
  with c₁ ==c '{' ∧ c₂ ==c '-' | c₁ ==c '-' ∧ c₂ ==c '}'
... | true  | _     =
        let (rest , bnd) =
              skipBlockB-WF (suc (suc n)) cs
                (rec (s≤s (n≤1+n _)))
        in  rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n bnd)
... | false | true  =
        let (rest , bnd) =
              skipBlockB-WF n cs
                (rec (s≤s (n≤1+n _)))
        in  rest , m≤n⇒m≤1+n (m≤n⇒m≤1+n bnd)
... | false | false =
        let (rest , bnd) =
              skipBlockB-WF (suc n) (c₂ ∷ cs)
                (rec (s≤s ≤-refl))
        in  rest , m≤n⇒m≤1+n bnd

skipBlockB : ℕ → (cs : List Char) →
             Σ[ rest ∈ List Char ] (length rest ≤ length cs)
skipBlockB n cs = skipBlockB-WF n cs (<-wellFounded (length cs))

skipBlock : ℕ → List Char → List Char
skipBlock n cs = proj₁ (skipBlockB n cs)

skipBlock-length : ∀ n cs → length (skipBlock n cs) ≤ length cs
skipBlock-length n cs = proj₂ (skipBlockB n cs)

------------------------------------------------------------------------
-- Main Tokenizer (well-founded on the input length)
------------------------------------------------------------------------

-- | Tokenize worker: receives an Acc witness on `length cs` to
-- justify termination. The two `with`-clauses (string literal, and the
-- digit/ident/skip general head) are de-`with`'d into parameterized helpers
-- `tok-str`/`tok-gen` so the verified lexer bridge (`Once.Adequacy.LexerBridge`)
-- can case those result PARAMETERS without an internal-`with` clash.
tok-str : (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
          Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ] length rest < length cs) →
          List Token
tok-gen : (c : Char) (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
          Bool → Bool → List Token
tokenize-WF : (cs : List Char) → Acc _<_ (length cs) → List Token
tokenize-WF [] _ = TEOF ∷ []

-- Line comments
tokenize-WF ('-' ∷ '-' ∷ cs) (acc rec) =
  let (rest , bnd) = skipLineB cs
  in  tokenize-WF rest (rec (s≤s (m≤n⇒m≤1+n bnd)))

-- Block comments
tokenize-WF ('{' ∷ '-' ∷ cs) (acc rec) =
  let (rest , bnd) = skipBlockB 1 cs
  in  tokenize-WF rest (rec (s≤s (m≤n⇒m≤1+n bnd)))

-- Whitespace (non-newline)
tokenize-WF (' '  ∷ cs) (acc rec) = tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('\t' ∷ cs) (acc rec) = tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('\r' ∷ cs) (acc rec) = tokenize-WF cs (rec (s≤s ≤-refl))

-- Newlines: only significant if the next line starts at column 0.
tokenize-WF ('\n' ∷ ' ' ∷ cs) (acc rec) =
  tokenize-WF (' ' ∷ cs) (rec (s≤s ≤-refl))
tokenize-WF ('\n' ∷ '\t' ∷ cs) (acc rec) =
  tokenize-WF ('\t' ∷ cs) (rec (s≤s ≤-refl))
tokenize-WF ('\n' ∷ cs) (acc rec) =
  TNewline ∷ tokenize-WF cs (rec (s≤s ≤-refl))

-- QTT grade annotations on argument types: A^1, A^0, A^w.
tokenize-WF ('^' ∷ '1' ∷ cs) (acc rec) =
  TCaret1 ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))
tokenize-WF ('^' ∷ '0' ∷ cs) (acc rec) =
  TCaret0 ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))
tokenize-WF ('^' ∷ 'w' ∷ cs) (acc rec) =
  TCaretW ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))

-- Two-character operators (max munch)
tokenize-WF ('-' ∷ '>' ∷ cs) (acc rec) =
  TArrow ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))
tokenize-WF ('<' ∷ '=' ∷ cs) (acc rec) =
  TLe ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))
tokenize-WF ('>' ∷ '=' ∷ cs) (acc rec) =
  TGe ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))
tokenize-WF ('=' ∷ '=' ∷ cs) (acc rec) =
  TEqEq ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))
tokenize-WF ('!' ∷ '=' ∷ cs) (acc rec) =
  TNeq ∷ tokenize-WF cs (rec (s≤s (m≤n⇒m≤1+n ≤-refl)))

-- EffectShape delimiter `!` (standalone, not `!=`). Plan 0.38 M0.2.
-- Must come AFTER the `!=`/TNeq clause (max-munch) and is a single char.
tokenize-WF ('!' ∷ cs) (acc rec) = TBang ∷ tokenize-WF cs (rec (s≤s ≤-refl))

-- Single-character punctuation
tokenize-WF ('(' ∷ cs) (acc rec) = TLParen    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF (')' ∷ cs) (acc rec) = TRParen    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('{' ∷ cs) (acc rec) = TLBrace    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('}' ∷ cs) (acc rec) = TRBrace    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF (':' ∷ cs) (acc rec) = TColon     ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('=' ∷ cs) (acc rec) = TEquals    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('\\' ∷ cs) (acc rec) = TLambda   ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF (',' ∷ cs) (acc rec) = TComma     ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF (';' ∷ cs) (acc rec) = TSemicolon ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('@' ∷ cs) (acc rec) = TAt        ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('|' ∷ cs) (acc rec) = TPipe      ∷ tokenize-WF cs (rec (s≤s ≤-refl))

-- Operators
tokenize-WF ('+' ∷ cs) (acc rec) = TPlus      ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('-' ∷ cs) (acc rec) = TMinus     ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('*' ∷ cs) (acc rec) = TStar      ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('/' ∷ cs) (acc rec) = TSlash     ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('%' ∷ cs) (acc rec) = TPercent   ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('&' ∷ cs) (acc rec) = TAmpersand ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('<' ∷ cs) (acc rec) = TLt        ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('>' ∷ cs) (acc rec) = TGt        ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tokenize-WF ('.' ∷ cs) (acc rec) = TDot       ∷ tokenize-WF cs (rec (s≤s ≤-refl))

-- String literals / integer / identifier / fallthrough — de-`with`'d.
tokenize-WF ('"' ∷ cs) (acc rec) = tok-str cs rec (collectStringB cs)
tokenize-WF (c ∷ cs)   (acc rec) = tok-gen c cs rec (isDigit c) (isIdentStart c)

tok-str cs rec (just (s , rest , bnd)) =
  TString (fromList s) ∷ tokenize-WF rest (rec (m≤n⇒m≤1+n bnd))
tok-str cs rec nothing = []  -- error: unterminated string
tok-gen c cs rec true  _     =
  let (digits , rest , bnd) = collectDigitsB cs
  in  TInt (+ digitsToNat (c ∷ digits)) ∷ tokenize-WF rest (rec (s≤s bnd))
tok-gen c cs rec false true  =
  let (ident , rest , bnd) = collectIdentB cs
  in  TWord (fromList (c ∷ ident)) ∷ tokenize-WF rest (rec (s≤s bnd))
tok-gen c cs rec false false = tokenize-WF cs (rec (s≤s ≤-refl))

-- | Tokenize a list of characters into tokens.
tokenize : List Char → List Token
tokenize cs = tokenize-WF cs (<-wellFounded (length cs))

------------------------------------------------------------------------
-- Entry Point
------------------------------------------------------------------------

-- | Tokenize a string
tokenizeString : String → List Token
tokenizeString s = tokenize (toList s)
