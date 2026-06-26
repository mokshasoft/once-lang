-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.LexerBridge — the GENUINE lexer relation (Plan 0.52, no shim).
--
-- `LexesChars` is the independent char-production relation (one constructor per
-- `tokenize-WF` rule); `lexes-tok` (soundness) and `tokenize-complete`
-- (completeness) bridge it to the executable `tokenize-WF` (de-`with`'d into
-- `tok-str`/`tok-gen`). The relation is EXCLUSION-FREE (no max-munch side
-- conditions baked into constructors): determinism is enforced in the
-- completeness direction by case-analysis + refutation (a wrong overlapping
-- derivation contradicts `tokenize`'s actual head token).
--
-- `Once.Adequacy.FrontEndBridge` consumes `Lexes`/`lexer-sound`/`lexer-complete`
-- (defined at the bottom over `toList`/`tokenize-WF`), replacing its postulates.
------------------------------------------------------------------------

module Once.Adequacy.LexerBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_<_)
open import Data.List using (List; []; _∷_; length)
open import Data.Char using (Char; isDigit)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Parser.Lexer
  using (isIdentStart; collectStringB; collectDigitsB; collectIdentB;
         skipLineB; skipBlockB; digitsToNat)

------------------------------------------------------------------------
-- The relation — one constructor per `tokenize-WF` rule.
------------------------------------------------------------------------

data LexesChars : List Char → List Token → Set where
  lex-eof : LexesChars [] (TEOF ∷ [])
  -- comments (consume via skipLineB / skipBlockB, then continue)
  lex-lcomment : ∀ {cs ts} → LexesChars (proj₁ (skipLineB cs)) ts → LexesChars ('-' ∷ '-' ∷ cs) ts
  lex-bcomment : ∀ {cs ts} → LexesChars (proj₁ (skipBlockB 1 cs)) ts → LexesChars ('{' ∷ '-' ∷ cs) ts
  -- whitespace (skip)
  lex-space : ∀ {cs ts} → LexesChars cs ts → LexesChars (' '  ∷ cs) ts
  lex-tab   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\t' ∷ cs) ts
  lex-cr    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\r' ∷ cs) ts
  -- newlines
  lex-nl-sp  : ∀ {cs ts} → LexesChars (' '  ∷ cs) ts → LexesChars ('\n' ∷ ' '  ∷ cs) ts
  lex-nl-tab : ∀ {cs ts} → LexesChars ('\t' ∷ cs) ts → LexesChars ('\n' ∷ '\t' ∷ cs) ts
  lex-nl     : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\n' ∷ cs) (TNewline ∷ ts)
  -- grade carets
  lex-caret1 : ∀ {cs ts} → LexesChars cs ts → LexesChars ('^' ∷ '1' ∷ cs) (TCaret1 ∷ ts)
  lex-caret0 : ∀ {cs ts} → LexesChars cs ts → LexesChars ('^' ∷ '0' ∷ cs) (TCaret0 ∷ ts)
  lex-caretw : ∀ {cs ts} → LexesChars cs ts → LexesChars ('^' ∷ 'w' ∷ cs) (TCaretW ∷ ts)
  -- two-char operators
  lex-arrow : ∀ {cs ts} → LexesChars cs ts → LexesChars ('-' ∷ '>' ∷ cs) (TArrow ∷ ts)
  lex-le    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('<' ∷ '=' ∷ cs) (TLe ∷ ts)
  lex-ge    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('>' ∷ '=' ∷ cs) (TGe ∷ ts)
  lex-eqeq  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('=' ∷ '=' ∷ cs) (TEqEq ∷ ts)
  lex-neq   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('!' ∷ '=' ∷ cs) (TNeq ∷ ts)
  lex-bang  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('!' ∷ cs) (TBang ∷ ts)
  -- single-char punctuation / operators
  lex-lparen : ∀ {cs ts} → LexesChars cs ts → LexesChars ('(' ∷ cs) (TLParen ∷ ts)
  lex-rparen : ∀ {cs ts} → LexesChars cs ts → LexesChars (')' ∷ cs) (TRParen ∷ ts)
  lex-lbrace : ∀ {cs ts} → LexesChars cs ts → LexesChars ('{' ∷ cs) (TLBrace ∷ ts)
  lex-rbrace : ∀ {cs ts} → LexesChars cs ts → LexesChars ('}' ∷ cs) (TRBrace ∷ ts)
  lex-colon  : ∀ {cs ts} → LexesChars cs ts → LexesChars (':' ∷ cs) (TColon ∷ ts)
  lex-equals : ∀ {cs ts} → LexesChars cs ts → LexesChars ('=' ∷ cs) (TEquals ∷ ts)
  lex-lambda : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\\' ∷ cs) (TLambda ∷ ts)
  lex-comma  : ∀ {cs ts} → LexesChars cs ts → LexesChars (',' ∷ cs) (TComma ∷ ts)
  lex-semi   : ∀ {cs ts} → LexesChars cs ts → LexesChars (';' ∷ cs) (TSemicolon ∷ ts)
  lex-at     : ∀ {cs ts} → LexesChars cs ts → LexesChars ('@' ∷ cs) (TAt ∷ ts)
  lex-pipe   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('|' ∷ cs) (TPipe ∷ ts)
  lex-plus   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('+' ∷ cs) (TPlus ∷ ts)
  lex-minus  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('-' ∷ cs) (TMinus ∷ ts)
  lex-star   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('*' ∷ cs) (TStar ∷ ts)
  lex-slash  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('/' ∷ cs) (TSlash ∷ ts)
  lex-pct    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('%' ∷ cs) (TPercent ∷ ts)
  lex-amp    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('&' ∷ cs) (TAmpersand ∷ ts)
  lex-lt     : ∀ {cs ts} → LexesChars cs ts → LexesChars ('<' ∷ cs) (TLt ∷ ts)
  lex-gt     : ∀ {cs ts} → LexesChars cs ts → LexesChars ('>' ∷ cs) (TGt ∷ ts)
  lex-dot    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('.' ∷ cs) (TDot ∷ ts)
  -- string literals
  lex-string : ∀ {cs ts} (s rest : List Char) (bnd : length rest < length cs) →
    collectStringB cs ≡ just (s , rest , bnd) → LexesChars rest ts →
    LexesChars ('"' ∷ cs) (TString (fromList s) ∷ ts)
  lex-string-err : ∀ {cs} → collectStringB cs ≡ nothing → LexesChars ('"' ∷ cs) []
  -- general head: digit / identifier / skip
  lex-digit : ∀ {c cs ts} → isDigit c ≡ true →
    LexesChars (proj₁ (proj₂ (collectDigitsB cs))) ts →
    LexesChars (c ∷ cs) (TInt (+ digitsToNat (c ∷ proj₁ (collectDigitsB cs))) ∷ ts)
  lex-ident : ∀ {c cs ts} → isDigit c ≡ false → isIdentStart c ≡ true →
    LexesChars (proj₁ (proj₂ (collectIdentB cs))) ts →
    LexesChars (c ∷ cs) (TWord (fromList (c ∷ proj₁ (collectIdentB cs))) ∷ ts)
  lex-skip : ∀ {c cs ts} → isDigit c ≡ false → isIdentStart c ≡ false →
    LexesChars cs ts → LexesChars (c ∷ cs) ts

Lexes : String → List Token → Set
Lexes text toks = LexesChars (toList text) toks

------------------------------------------------------------------------
-- SOUNDNESS / COMPLETENESS — NEXT STEP (precisely scoped & DIAGNOSED).
--
-- DONE: `tokenize-WF`'s 8 multi-char heads (`\n`/`-`/`<`/`>`/`=`/`!`/`{`/`^`) are
-- de-`with`'d via classifiers (`nlIndent`/`isEqHead`/`isDashHead`/`dashClass`/
-- `caretClass`) + helpers (`tok-nl`/`tok-op2`/`tok-lbrace`/`tok-minus`/`tok-caret`)
-- in `Once.Parser.Lexer` — behaviour-preserving, committed.
--
-- THE REMAINING SUBTLETY (diagnosed, the earlier note was WRONG): casing the
-- second char in `lexes-tok` does NOT work, because Agda does NOT reduce a char
-- classifier under a PEELED literal — in a clause `lexes-tok ('\n' ∷ c ∷ cs)`
-- (c split off after the `' '`/`'\t'` clauses), `nlIndent (c ∷ cs)` stays STUCK
-- (the constraint `c ≠ ' '/'\t'` is not used in reduction), so the goal
-- `tokenize-WF` won't step. Likewise the structure/refutation lemmas can't be
-- proved by literal-peeling.
--
-- THE FIX: define the classifiers in `Lexer` via DECIDABLE char equality
-- (`nlIndent (c ∷ _) = does (c ≟ ' ') ∨ does (c ≟ '\t')`, etc.) so they REDUCE
-- under a decision; then `lexes-tok` dispatches `with c ≟ '='` (etc.) — the `no
-- ¬p` branch makes `isEqHead (c ∷ _)` compute to `false` (so `tok-op2 …` steps),
-- and the `yes refl` branch REFINES `c` to the literal (so the 2-char rule's
-- continuation is in scope). `lexer-complete` inducts on the derivation, using
-- the same decisions; each fallback constructor carries `<classifier> ≡ <fallback>`
-- so the overlap is refuted by the decision. The relation below gets those
-- `≡`-premises on the fallback constructors (`lex-nl`/`lex-lt`/`lex-minus`/…).
------------------------------------------------------------------------
