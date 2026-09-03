-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Lexing — the lexer RELATION, and nothing else (Plan 0.84).
--
-- `LexesChars`/`Lexes` say WHAT IT MEANS for a text to lex to a token stream.
-- They are part of the statement of `correct` (via `ParsesText`), so they are
-- inside the `Once.Spec` re-export closure and a reviewer must read them.
--
-- The bridge to the executable lexer — `lexer-sound`/`lexer-complete` and the
-- determinism chain — is EVIDENCE that `tokenizeString` meets this relation,
-- not part of what is claimed. It stays in `Once.Adequacy.LexerBridge`, which
-- imports this module.
--
-- The relation is stated against the lexer's own classifiers (`headK`,
-- `dashClass`, …) and collectors (`collectDigitsB`, …). That is a genuine
-- weakness — a spec phrased with the implementation's helpers — recorded
-- against plan 0.59, NOT laundered by leaving it on the proof side.
------------------------------------------------------------------------

module Once.Spec.Lexing where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; _<_)
open import Data.List using (List; []; _∷_; length)
open import Data.Char using (Char; isDigit)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Parser.Lexer
  using (adv; headK; isIdentStart;
         collectStringB; collectDigitsB; collectFracB; collectIdentB;
         skipLineB; skipBlockB; digitsToNat; drop1;
         nlIndent; isEqHead; isDashHead; dashClass; caretClass;
         d-comment; d-arrow; d-minus; c-1; c-0; c-w; c-gen;
         hkWS; hkNL; hkCaret; hkDash; hkLBrace; hkLt; hkGt; hkEq; hkBang;
         hkLParen; hkRParen; hkRBrace; hkColon; hkLambda; hkComma; hkSemi; hkAt;
         hkPipe; hkPlus; hkStar; hkSlash; hkPct; hkAmp; hkDot; hkStr; hkGen)

------------------------------------------------------------------------
-- The relation.
------------------------------------------------------------------------

-- PLAN 0.74 (positions): INDEXED BY THE SOURCE OFFSET of `cs`'s first
-- character, because the token stream now carries positions and the relation
-- has to say which ones.
--
-- Erasing the offsets instead — relating a position-free token stream — was
-- the cheaper option and it does NOT compose: the parser consumes the real
-- stream and copies a float's offset into `RFloat`, so the parse RESULT
-- depends on positions. A bridge that only pinned the erased stream would
-- leave a gap exactly where `parseStrict-sound` needs it.
--
-- Every premise advances the offset by `adv`, the same function the worker
-- uses — so the relation cannot disagree with the lexer about how far a
-- clause moved.
data LexesChars : ℕ → List Char → List Token → Set where
  lex-eof : ∀ {off} → LexesChars off [] (TEOF ∷ [])
  lex-ws  : ∀ {off c cs ts} → headK c ≡ hkWS → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) ts
  -- newline (indent continuation vs significant TNewline)
  lex-nl-ind : ∀ {off c cs ts} → headK c ≡ hkNL → nlIndent cs ≡ true  → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) ts
  lex-nl     : ∀ {off c cs ts} → headK c ≡ hkNL → nlIndent cs ≡ false → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TNewline ∷ ts)
  -- grade carets
  lex-caret1    : ∀ {off c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-1   → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TCaret1 ∷ ts)
  lex-caret0    : ∀ {off c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-0   → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TCaret0 ∷ ts)
  lex-caretw    : ∀ {off c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-w   → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TCaretW ∷ ts)
  lex-caret-gen : ∀ {off c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-gen → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) ts
  -- dash head: line comment / arrow / minus
  lex-lcomment-ind : ∀ {off c cs ts} → headK c ≡ hkDash → dashClass cs ≡ d-comment → LexesChars (adv cs (proj₁ (skipLineB (drop1 cs))) off) (proj₁ (skipLineB (drop1 cs))) ts → LexesChars off (c ∷ cs) ts
  lex-arrow-ind    : ∀ {off c cs ts} → headK c ≡ hkDash → dashClass cs ≡ d-arrow   → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TArrow ∷ ts)
  lex-minus        : ∀ {off c cs ts} → headK c ≡ hkDash → dashClass cs ≡ d-minus   → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TMinus ∷ ts)
  -- brace head: block comment / lbrace
  lex-bcomment-ind : ∀ {off c cs ts} → headK c ≡ hkLBrace → isDashHead cs ≡ true  → LexesChars (adv cs (proj₁ (skipBlockB 1 (drop1 cs))) off) (proj₁ (skipBlockB 1 (drop1 cs))) ts → LexesChars off (c ∷ cs) ts
  lex-lbrace       : ∀ {off c cs ts} → headK c ≡ hkLBrace → isDashHead cs ≡ false → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TLBrace ∷ ts)
  -- `…=` operators
  lex-le-ind   : ∀ {off c cs ts} → headK c ≡ hkLt   → isEqHead cs ≡ true  → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TLe ∷ ts)
  lex-lt       : ∀ {off c cs ts} → headK c ≡ hkLt   → isEqHead cs ≡ false → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TLt ∷ ts)
  lex-ge-ind   : ∀ {off c cs ts} → headK c ≡ hkGt   → isEqHead cs ≡ true  → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TGe ∷ ts)
  lex-gt       : ∀ {off c cs ts} → headK c ≡ hkGt   → isEqHead cs ≡ false → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TGt ∷ ts)
  lex-eqeq-ind : ∀ {off c cs ts} → headK c ≡ hkEq   → isEqHead cs ≡ true  → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TEqEq ∷ ts)
  lex-equals   : ∀ {off c cs ts} → headK c ≡ hkEq   → isEqHead cs ≡ false → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TEquals ∷ ts)
  lex-neq-ind  : ∀ {off c cs ts} → headK c ≡ hkBang → isEqHead cs ≡ true  → LexesChars (adv cs (drop1 cs) off) (drop1 cs) ts → LexesChars off (c ∷ cs) (TNeq ∷ ts)
  lex-bang     : ∀ {off c cs ts} → headK c ≡ hkBang → isEqHead cs ≡ false → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TBang ∷ ts)
  -- single-char punctuation / operators
  lex-lparen : ∀ {off c cs ts} → headK c ≡ hkLParen → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TLParen ∷ ts)
  lex-rparen : ∀ {off c cs ts} → headK c ≡ hkRParen → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TRParen ∷ ts)
  lex-rbrace : ∀ {off c cs ts} → headK c ≡ hkRBrace → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TRBrace ∷ ts)
  lex-colon  : ∀ {off c cs ts} → headK c ≡ hkColon  → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TColon ∷ ts)
  lex-lambda : ∀ {off c cs ts} → headK c ≡ hkLambda → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TLambda ∷ ts)
  lex-comma  : ∀ {off c cs ts} → headK c ≡ hkComma  → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TComma ∷ ts)
  lex-semi   : ∀ {off c cs ts} → headK c ≡ hkSemi   → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TSemicolon ∷ ts)
  lex-at     : ∀ {off c cs ts} → headK c ≡ hkAt     → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TAt ∷ ts)
  lex-pipe   : ∀ {off c cs ts} → headK c ≡ hkPipe   → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TPipe ∷ ts)
  lex-plus   : ∀ {off c cs ts} → headK c ≡ hkPlus   → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TPlus ∷ ts)
  lex-star   : ∀ {off c cs ts} → headK c ≡ hkStar   → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TStar ∷ ts)
  lex-slash  : ∀ {off c cs ts} → headK c ≡ hkSlash  → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TSlash ∷ ts)
  lex-pct    : ∀ {off c cs ts} → headK c ≡ hkPct    → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TPercent ∷ ts)
  lex-amp    : ∀ {off c cs ts} → headK c ≡ hkAmp    → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TAmpersand ∷ ts)
  lex-dot    : ∀ {off c cs ts} → headK c ≡ hkDot    → LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) (TDot ∷ ts)
  -- string literals
  lex-string : ∀ {off c cs ts} → headK c ≡ hkStr → (s rest : List Char) (bnd : length rest < length cs) →
    collectStringB cs ≡ just (s , rest , bnd) → LexesChars (adv cs rest off) rest ts →
    LexesChars off (c ∷ cs) (TString (fromList s) ∷ ts)
  lex-string-err : ∀ {off c cs} → headK c ≡ hkStr → collectStringB cs ≡ nothing → LexesChars off (c ∷ cs) []
  -- general head: digit / identifier / skip
  -- PLAN 0.71: the numeric head splits on whether a FRACTION follows the
  -- integer part. Both rules stay under `headK c ≡ hkGen` and `isDigit c ≡
  -- true` — the float path adds no head class, so the other 25 classifier
  -- cases are untouched. `collectFracB` decides between them, and each rule
  -- carries its own outcome as a premise, so neither can fire where the other
  -- should (the same shape `lex-caret*`/`lex-nl*` use).
  lex-digit : ∀ {off c cs ts} → headK c ≡ hkGen → isDigit c ≡ true →
    collectFracB (proj₁ (proj₂ (collectDigitsB cs))) ≡ nothing →
    LexesChars (adv cs (proj₁ (proj₂ (collectDigitsB cs))) off) (proj₁ (proj₂ (collectDigitsB cs))) ts →
    LexesChars off (c ∷ cs) (TInt (+ digitsToNat (c ∷ proj₁ (collectDigitsB cs))) off ∷ ts)
  lex-float : ∀ {off c cs ts f r bnd} → headK c ≡ hkGen → isDigit c ≡ true →
    collectFracB (proj₁ (proj₂ (collectDigitsB cs))) ≡ just (f , r , bnd) →
    LexesChars (adv cs r off) r ts →
    LexesChars off (c ∷ cs)
      (TFloat (digitsToNat (c ∷ proj₁ (collectDigitsB cs))) (digitsToNat f) (length f) off ∷ ts)
  lex-ident : ∀ {off c cs ts} → headK c ≡ hkGen → isDigit c ≡ false → isIdentStart c ≡ true →
    LexesChars (adv cs (proj₁ (proj₂ (collectIdentB cs))) off) (proj₁ (proj₂ (collectIdentB cs))) ts →
    LexesChars off (c ∷ cs) (TWord (fromList (c ∷ proj₁ (collectIdentB cs))) ∷ ts)
  lex-skip : ∀ {off c cs ts} → headK c ≡ hkGen → isDigit c ≡ false → isIdentStart c ≡ false →
    LexesChars (adv cs cs off) cs ts → LexesChars off (c ∷ cs) ts

-- The whole text starts at offset 0, which is where the threading bottoms out
-- and why nothing above this line has to know about absolute positions.
Lexes : String → List Token → Set
Lexes text toks = LexesChars 0 (toList text) toks
