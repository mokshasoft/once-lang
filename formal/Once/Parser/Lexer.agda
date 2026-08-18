-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Char using (Char; isAlpha; isDigit; isSpace; isLower) renaming (_≟_ to _≟c_)
open import Relation.Nullary using (does)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n; n≤1+n; <-trans; m≤n⇒m≤1+n; <⇒≤)
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

-- | Collect a FRACTION: a '.' followed by AT LEAST ONE digit (plan 0.71).
--
-- `nothing` when the input does not start one, and the digit requirement is
-- what keeps the two readings of a dot disjoint: `x.f` is a qualified name and
-- `1.` is not a literal, so neither steals from the other. Same
-- `Maybe`-returning shape as `collectStringB`, so the caller dispatches on a
-- value instead of a `with`.
collectFracB : (cs : List Char) →
               Maybe (Σ[ f ∈ List Char ] Σ[ rest ∈ List Char ]
                        length rest < length cs)
collectFracB ('.' ∷ c ∷ cs) with isDigit c
... | true  = let (digs , rest , bnd) = collectDigitsB cs
              in  just (c ∷ digs , rest , s≤s (m≤n⇒m≤1+n bnd))
... | false = nothing
collectFracB _ = nothing

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

-- | Classifiers for the MULTI-CHAR head dispatch. `tokenize-WF` routes the
-- multi-char heads (`\n`/`-`/`<`/`>`/`=`/`!`/`{`/`^`) through these + the helpers
-- below, INSTEAD of clause-order pattern matching. Behaviour is identical, but
-- the second-char decision becomes a PARAMETER, so the verified lexer bridge
-- (`Once.Adequacy.LexerBridge`) can reduce `tokenize-WF` under it without the
-- catch-all-over-`Char` clash (a variable tail no longer leaves the function
-- stuck). See [[feedback_de_with_parameterize_equation]].
data Dash3  : Set where d-comment d-arrow d-minus : Dash3
data Caret4 : Set where c-1 c-0 c-w c-gen : Caret4

-- Defined via DECIDABLE char equality (`does (c ≟c X)`) — NOT literal pattern
-- matching — so a proof can reduce them under `with c ≟c X` (the `no`/`yes`
-- decision makes `does …` compute, and `yes refl` refines the char). See the
-- LexerBridge doc.
nlIndent : List Char → Bool
nlIndent (c ∷ _) = does (c ≟c ' ') ∨ does (c ≟c '\t')
nlIndent []      = false
isEqHead : List Char → Bool
isEqHead (c ∷ _) = does (c ≟c '=')
isEqHead []      = false
isDashHead : List Char → Bool
isDashHead (c ∷ _) = does (c ≟c '-')
isDashHead []      = false
dashClass : List Char → Dash3
dashClass (c ∷ _) = if does (c ≟c '-') then d-comment else (if does (c ≟c '>') then d-arrow else d-minus)
dashClass []      = d-minus
caretClass : List Char → Caret4
caretClass (c ∷ _) = if does (c ≟c '1') then c-1 else (if does (c ≟c '0') then c-0 else (if does (c ≟c 'w') then c-w else c-gen))
caretClass []      = c-gen

-- | Drop the first char (uniform tail). Lets the multi-char helpers recurse on
-- `drop1 cs` instead of pattern-matching `cs ≡ '=' ∷ rest` — so the helpers
-- REDUCE under a known classifier (e.g. `tok-op2 cs rec _ _ true`) even when the
-- tail is a variable. Behaviour-preserving (a known classifier ⇒ the head is the
-- consumed char, so `drop1 cs ≡ rest`); the old `cs`-pattern catch-alls were
-- already flagged unreachable.
drop1 : List Char → List Char
drop1 []       = []
drop1 (_ ∷ cs) = cs

drop1-≤ : (cs : List Char) → length (drop1 cs) ≤ length cs
drop1-≤ []       = z≤n
drop1-≤ (_ ∷ cs) = n≤1+n _

-- | Head classifier: maps the first char to its dispatch kind. Routing
-- `tokenize-WF`'s head through this (instead of 27 positional literal clauses)
-- lets the bridge proofs step `tokenize-WF (c ∷ cs)` for a VARIABLE `c` via
-- `with headK c in eq` — Agda cannot reduce a positional catch-all under a peeled
-- literal, but it reduces `tok-head c cs rec (headK c)` once `headK c` is known.
data HeadK : Set where
  hkWS hkNL hkCaret hkDash hkLBrace hkLt hkGt hkEq hkBang
    hkLParen hkRParen hkRBrace hkColon hkLambda hkComma hkSemi hkAt hkPipe
    hkPlus hkStar hkSlash hkPct hkAmp hkDot hkStr hkGen : HeadK

headK : Char → HeadK
headK c =
  if does (c ≟c ' ') ∨ does (c ≟c '\t') ∨ does (c ≟c '\r') then hkWS
  else if does (c ≟c '\n') then hkNL
  else if does (c ≟c '^') then hkCaret
  else if does (c ≟c '-') then hkDash
  else if does (c ≟c '{') then hkLBrace
  else if does (c ≟c '<') then hkLt
  else if does (c ≟c '>') then hkGt
  else if does (c ≟c '=') then hkEq
  else if does (c ≟c '!') then hkBang
  else if does (c ≟c '(') then hkLParen
  else if does (c ≟c ')') then hkRParen
  else if does (c ≟c '}') then hkRBrace
  else if does (c ≟c ':') then hkColon
  else if does (c ≟c '\\') then hkLambda
  else if does (c ≟c ',') then hkComma
  else if does (c ≟c ';') then hkSemi
  else if does (c ≟c '@') then hkAt
  else if does (c ≟c '|') then hkPipe
  else if does (c ≟c '+') then hkPlus
  else if does (c ≟c '*') then hkStar
  else if does (c ≟c '/') then hkSlash
  else if does (c ≟c '%') then hkPct
  else if does (c ≟c '&') then hkAmp
  else if does (c ≟c '.') then hkDot
  else if does (c ≟c '"') then hkStr
  else hkGen

-- | Tokenize worker. The head is dispatched via `headK` + `tok-head`; the
-- multi-char heads delegate to `tok-nl`/`tok-op2`/`tok-minus`/`tok-lbrace`/
-- `tok-caret`; the string/general clauses to `tok-str`/`tok-gen`.
tok-str : (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
          Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ] length rest < length cs) →
          List Token
tok-gen : (c : Char) (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
          Bool → Bool → List Token
-- Plan 0.71: the numeric branch, split off so the fraction is dispatched on a
-- VALUE (`collectFracB rest`) rather than a `with` — the same shape `tok-str`
-- uses, and what keeps the clause reducible for the soundness proof.
tok-num : (c : Char) (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
          (digits rest : List Char) → length rest ≤ length cs →
          Maybe (Σ[ f ∈ List Char ] Σ[ r ∈ List Char ] length r < length rest) →
          List Token
tok-nl  : (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Bool → List Token
tok-op2 : (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
          Token → Token → Bool → List Token
tok-lbrace : (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Bool → List Token
tok-minus  : (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Dash3 → List Token
tok-caret  : (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Caret4 → List Token
tok-head   : (c : Char) (cs : List Char) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → HeadK → List Token
tokenize-WF : (cs : List Char) → Acc _<_ (length cs) → List Token

tokenize-WF [] _ = TEOF ∷ []
tokenize-WF (c ∷ cs) (acc rec) = tok-head c cs rec (headK c)

tok-head c cs rec hkWS     = tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkNL     = tok-nl cs rec (nlIndent cs)
tok-head c cs rec hkCaret  = tok-caret cs rec (caretClass cs)
tok-head c cs rec hkDash   = tok-minus cs rec (dashClass cs)
tok-head c cs rec hkLBrace = tok-lbrace cs rec (isDashHead cs)
tok-head c cs rec hkLt     = tok-op2 cs rec TLe TLt (isEqHead cs)
tok-head c cs rec hkGt     = tok-op2 cs rec TGe TGt (isEqHead cs)
tok-head c cs rec hkEq     = tok-op2 cs rec TEqEq TEquals (isEqHead cs)
tok-head c cs rec hkBang   = tok-op2 cs rec TNeq TBang (isEqHead cs)
tok-head c cs rec hkLParen = TLParen    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkRParen = TRParen    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkRBrace = TRBrace    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkColon  = TColon     ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkLambda = TLambda    ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkComma  = TComma     ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkSemi   = TSemicolon ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkAt     = TAt        ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkPipe   = TPipe      ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkPlus   = TPlus      ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkStar   = TStar      ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkSlash  = TSlash     ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkPct    = TPercent   ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkAmp    = TAmpersand ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkDot    = TDot       ∷ tokenize-WF cs (rec (s≤s ≤-refl))
tok-head c cs rec hkStr    = tok-str cs rec (collectStringB cs)
tok-head c cs rec hkGen    = tok-gen c cs rec (isDigit c) (isIdentStart c)

tok-str cs rec (just (s , rest , bnd)) =
  TString (fromList s) ∷ tokenize-WF rest (rec (m≤n⇒m≤1+n bnd))
tok-str cs rec nothing = []  -- error: unterminated string
tok-gen c cs rec true  _     =
  let (digits , rest , bnd) = collectDigitsB cs
  in  tok-num c cs rec digits rest bnd (collectFracB rest)
tok-gen c cs rec false true  =
  let (ident , rest , bnd) = collectIdentB cs
  in  TWord (fromList (c ∷ ident)) ∷ tokenize-WF rest (rec (s≤s bnd))
tok-gen c cs rec false false = tokenize-WF cs (rec (s≤s ≤-refl))

-- A FLOAT when a fraction follows, an INT when it does not. The bound composes:
-- the fraction's remainder is strictly shorter than the integer part's
-- remainder, which is already bounded by the input — so the recursion decreases
-- for the same reason it did before, one step further along.
tok-num c cs rec digits rest bnd (just (frac , rest' , fbnd)) =
  TFloat (digitsToNat (c ∷ digits)) (digitsToNat frac) (length frac)
    ∷ tokenize-WF rest' (rec (s≤s (≤-trans (<⇒≤ fbnd) bnd)))
tok-num c cs rec digits rest bnd nothing =
  TInt (+ digitsToNat (c ∷ digits)) ∷ tokenize-WF rest (rec (s≤s bnd))

-- `\n`: indented continuation (next char ' '/'\t') ⇒ insignificant (skip);
-- else a significant `TNewline`. Both recurse on the tail `cs`.
tok-nl cs rec true  = tokenize-WF cs (rec (n<1+n _))
tok-nl cs rec false = TNewline ∷ tokenize-WF cs (rec (n<1+n _))

-- 2-char `…=` operators: `t2` if next is `=` (recurse past it via drop1), else `t1`.
tok-op2 cs rec t2 t1 true  = t2 ∷ tokenize-WF (drop1 cs) (rec (s≤s (drop1-≤ cs)))
tok-op2 cs rec t2 t1 false = t1 ∷ tokenize-WF cs (rec (n<1+n _))

-- `{`: block comment `{-` (skip via skipBlockB ∘ drop1) else `TLBrace`.
tok-lbrace cs rec true  = tokenize-WF (proj₁ (skipBlockB 1 (drop1 cs))) (rec (s≤s (≤-trans (proj₂ (skipBlockB 1 (drop1 cs))) (drop1-≤ cs))))
tok-lbrace cs rec false = TLBrace ∷ tokenize-WF cs (rec (n<1+n _))

-- `-`: line comment `--` (skipLineB ∘ drop1), arrow `->` (drop1), else `TMinus`.
tok-minus cs rec d-comment = tokenize-WF (proj₁ (skipLineB (drop1 cs))) (rec (s≤s (≤-trans (proj₂ (skipLineB (drop1 cs))) (drop1-≤ cs))))
tok-minus cs rec d-arrow   = TArrow ∷ tokenize-WF (drop1 cs) (rec (s≤s (drop1-≤ cs)))
tok-minus cs rec d-minus   = TMinus ∷ tokenize-WF cs (rec (n<1+n _))

-- `^`: grade caret `^1`/`^0`/`^w` (drop1), else fall to the general head.
tok-caret cs rec c-1 = TCaret1 ∷ tokenize-WF (drop1 cs) (rec (s≤s (drop1-≤ cs)))
tok-caret cs rec c-0 = TCaret0 ∷ tokenize-WF (drop1 cs) (rec (s≤s (drop1-≤ cs)))
tok-caret cs rec c-w = TCaretW ∷ tokenize-WF (drop1 cs) (rec (s≤s (drop1-≤ cs)))
tok-caret cs rec c-gen = tok-gen '^' cs rec (isDigit '^') (isIdentStart '^')

-- | Tokenize a list of characters into tokens.
tokenize : List Char → List Token
tokenize cs = tokenize-WF cs (<-wellFounded (length cs))

------------------------------------------------------------------------
-- Entry Point
------------------------------------------------------------------------

-- | Tokenize a string
tokenizeString : String → List Token
tokenizeString s = tokenize (toList s)
