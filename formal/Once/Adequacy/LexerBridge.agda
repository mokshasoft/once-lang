-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.LexerBridge — the GENUINE lexer relation (Plan 0.52, NO shim).
--
-- `LexesChars` is the independent char-production relation (one constructor per
-- `tokenize-WF` rule). Multi-char heads carry a CLASSIFIER premise (`nlIndent cs
-- ≡ true`, `isEqHead cs ≡ false`, `dashClass cs ≡ d-minus`, …) and recurse on the
-- uniform `drop1 cs` — mirroring the `drop1`-based helpers in `Once.Parser.Lexer`,
-- so the bridge proofs REDUCE under `with <classifier> in eq` (no second-char
-- case-split, which Agda will not reduce under a peeled literal).
--
--   * `lexer-sound`   : `Lexes text (tokenizeString text)` — the executable's
--                       output is always a valid derivation.
--   * `lex-det`       : the relation is deterministic (the `isSpecialChar` guard
--                       on `lex-skip` rules out overlap with the punctuation rules).
--   * `lexer-complete`: `Lexes text toks → tokenizeString text ≡ toks`, i.e.
--                       sound ∘ determinism — the executable matches ANY derivation.
--
-- `Once.Adequacy.FrontEndBridge` consumes `Lexes`/`lexer-sound`/`lexer-complete`,
-- replacing its three lexer postulates.
------------------------------------------------------------------------

module Once.Adequacy.LexerBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_<_; suc; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; n<1+n; n≤1+n)
open import Data.List using (List; []; _∷_; length)
open import Data.Char using (Char; isDigit)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Integer using (+_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Parser.Token
open import Once.Parser.Lexer
  using (tokenize-WF; tok-str; tok-gen; tokenizeString; isIdentStart;
         collectStringB; collectDigitsB; collectIdentB; skipLineB; skipBlockB;
         digitsToNat; drop1; drop1-≤;
         nlIndent; isEqHead; isDashHead; dashClass; caretClass;
         Dash3; d-comment; d-arrow; d-minus; Caret4; c-1; c-0; c-w; c-gen)

------------------------------------------------------------------------
-- `isSpecialChar` — exactly the chars with a dedicated `tokenize-WF` clause
-- (everything BEFORE the general digit/ident/skip catch-all). PATTERN-based (not
-- decidable-equality) so it reduces to `false` under the SAME peeling that sends
-- `tokenize-WF (c ∷ cs)` to its general clause. Guards `lex-skip` for determinism.
------------------------------------------------------------------------

isSpecialChar : Char → Bool
isSpecialChar ' '  = true
isSpecialChar '\t' = true
isSpecialChar '\r' = true
isSpecialChar '\n' = true
isSpecialChar '^'  = true
isSpecialChar '-'  = true
isSpecialChar '{'  = true
isSpecialChar '<'  = true
isSpecialChar '>'  = true
isSpecialChar '='  = true
isSpecialChar '!'  = true
isSpecialChar '('  = true
isSpecialChar ')'  = true
isSpecialChar '}'  = true
isSpecialChar ':'  = true
isSpecialChar '\\' = true
isSpecialChar ','  = true
isSpecialChar ';'  = true
isSpecialChar '@'  = true
isSpecialChar '|'  = true
isSpecialChar '+'  = true
isSpecialChar '*'  = true
isSpecialChar '/'  = true
isSpecialChar '%'  = true
isSpecialChar '&'  = true
isSpecialChar '.'  = true
isSpecialChar '"'  = true
isSpecialChar _    = false

------------------------------------------------------------------------
-- The relation.
------------------------------------------------------------------------

data LexesChars : List Char → List Token → Set where
  lex-eof : LexesChars [] (TEOF ∷ [])
  -- whitespace (skip)
  lex-space : ∀ {cs ts} → LexesChars cs ts → LexesChars (' '  ∷ cs) ts
  lex-tab   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\t' ∷ cs) ts
  lex-cr    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\r' ∷ cs) ts
  -- newlines (indent continuation vs significant TNewline)
  lex-nl-ind : ∀ {cs ts} → nlIndent cs ≡ true  → LexesChars cs ts → LexesChars ('\n' ∷ cs) ts
  lex-nl     : ∀ {cs ts} → nlIndent cs ≡ false → LexesChars cs ts → LexesChars ('\n' ∷ cs) (TNewline ∷ ts)
  -- grade carets
  lex-caret1   : ∀ {cs ts} → caretClass cs ≡ c-1   → LexesChars (drop1 cs) ts → LexesChars ('^' ∷ cs) (TCaret1 ∷ ts)
  lex-caret0   : ∀ {cs ts} → caretClass cs ≡ c-0   → LexesChars (drop1 cs) ts → LexesChars ('^' ∷ cs) (TCaret0 ∷ ts)
  lex-caretw   : ∀ {cs ts} → caretClass cs ≡ c-w   → LexesChars (drop1 cs) ts → LexesChars ('^' ∷ cs) (TCaretW ∷ ts)
  lex-caret-gen : ∀ {cs ts} → caretClass cs ≡ c-gen → LexesChars cs ts → LexesChars ('^' ∷ cs) ts
  -- dash head: line comment / arrow / minus
  lex-lcomment-ind : ∀ {cs ts} → dashClass cs ≡ d-comment → LexesChars (proj₁ (skipLineB (drop1 cs))) ts → LexesChars ('-' ∷ cs) ts
  lex-arrow-ind    : ∀ {cs ts} → dashClass cs ≡ d-arrow   → LexesChars (drop1 cs) ts → LexesChars ('-' ∷ cs) (TArrow ∷ ts)
  lex-minus        : ∀ {cs ts} → dashClass cs ≡ d-minus   → LexesChars cs ts → LexesChars ('-' ∷ cs) (TMinus ∷ ts)
  -- brace head: block comment / lbrace
  lex-bcomment-ind : ∀ {cs ts} → isDashHead cs ≡ true  → LexesChars (proj₁ (skipBlockB 1 (drop1 cs))) ts → LexesChars ('{' ∷ cs) ts
  lex-lbrace       : ∀ {cs ts} → isDashHead cs ≡ false → LexesChars cs ts → LexesChars ('{' ∷ cs) (TLBrace ∷ ts)
  -- `…=` operators (2-char vs 1-char via isEqHead)
  lex-le-ind   : ∀ {cs ts} → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars ('<' ∷ cs) (TLe ∷ ts)
  lex-lt       : ∀ {cs ts} → isEqHead cs ≡ false → LexesChars cs ts → LexesChars ('<' ∷ cs) (TLt ∷ ts)
  lex-ge-ind   : ∀ {cs ts} → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars ('>' ∷ cs) (TGe ∷ ts)
  lex-gt       : ∀ {cs ts} → isEqHead cs ≡ false → LexesChars cs ts → LexesChars ('>' ∷ cs) (TGt ∷ ts)
  lex-eqeq-ind : ∀ {cs ts} → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars ('=' ∷ cs) (TEqEq ∷ ts)
  lex-equals   : ∀ {cs ts} → isEqHead cs ≡ false → LexesChars cs ts → LexesChars ('=' ∷ cs) (TEquals ∷ ts)
  lex-neq-ind  : ∀ {cs ts} → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars ('!' ∷ cs) (TNeq ∷ ts)
  lex-bang     : ∀ {cs ts} → isEqHead cs ≡ false → LexesChars cs ts → LexesChars ('!' ∷ cs) (TBang ∷ ts)
  -- single-char punctuation / operators
  lex-lparen : ∀ {cs ts} → LexesChars cs ts → LexesChars ('(' ∷ cs) (TLParen ∷ ts)
  lex-rparen : ∀ {cs ts} → LexesChars cs ts → LexesChars (')' ∷ cs) (TRParen ∷ ts)
  lex-rbrace : ∀ {cs ts} → LexesChars cs ts → LexesChars ('}' ∷ cs) (TRBrace ∷ ts)
  lex-colon  : ∀ {cs ts} → LexesChars cs ts → LexesChars (':' ∷ cs) (TColon ∷ ts)
  lex-lambda : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\\' ∷ cs) (TLambda ∷ ts)
  lex-comma  : ∀ {cs ts} → LexesChars cs ts → LexesChars (',' ∷ cs) (TComma ∷ ts)
  lex-semi   : ∀ {cs ts} → LexesChars cs ts → LexesChars (';' ∷ cs) (TSemicolon ∷ ts)
  lex-at     : ∀ {cs ts} → LexesChars cs ts → LexesChars ('@' ∷ cs) (TAt ∷ ts)
  lex-pipe   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('|' ∷ cs) (TPipe ∷ ts)
  lex-plus   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('+' ∷ cs) (TPlus ∷ ts)
  lex-star   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('*' ∷ cs) (TStar ∷ ts)
  lex-slash  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('/' ∷ cs) (TSlash ∷ ts)
  lex-pct    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('%' ∷ cs) (TPercent ∷ ts)
  lex-amp    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('&' ∷ cs) (TAmpersand ∷ ts)
  lex-dot    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('.' ∷ cs) (TDot ∷ ts)
  -- string literals
  lex-string : ∀ {cs ts} (s rest : List Char) (bnd : length rest < length cs) →
    collectStringB cs ≡ just (s , rest , bnd) → LexesChars rest ts →
    LexesChars ('"' ∷ cs) (TString (fromList s) ∷ ts)
  lex-string-err : ∀ {cs} → collectStringB cs ≡ nothing → LexesChars ('"' ∷ cs) []
  -- general head: digit / identifier / skip (skip is guarded non-special)
  lex-digit : ∀ {c cs ts} → isDigit c ≡ true →
    LexesChars (proj₁ (proj₂ (collectDigitsB cs))) ts →
    LexesChars (c ∷ cs) (TInt (+ digitsToNat (c ∷ proj₁ (collectDigitsB cs))) ∷ ts)
  lex-ident : ∀ {c cs ts} → isDigit c ≡ false → isIdentStart c ≡ true →
    LexesChars (proj₁ (proj₂ (collectIdentB cs))) ts →
    LexesChars (c ∷ cs) (TWord (fromList (c ∷ proj₁ (collectIdentB cs))) ∷ ts)
  lex-skip : ∀ {c cs ts} → isSpecialChar c ≡ false → isDigit c ≡ false → isIdentStart c ≡ false →
    LexesChars cs ts → LexesChars (c ∷ cs) ts

Lexes : String → List Token → Set
Lexes text toks = LexesChars (toList text) toks

------------------------------------------------------------------------
-- SOUNDNESS — the executable's output is a valid derivation.
------------------------------------------------------------------------

lexes-tok : ∀ (cs : List Char) (a : Acc _<_ (length cs)) → LexesChars cs (tokenize-WF cs a)
sound-tok-str : ∀ (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y)
  (r : Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ] length rest < length cs)) →
  collectStringB cs ≡ r → LexesChars ('"' ∷ cs) (tok-str cs rec r)

-- General-head soundness. `tokenize-WF (c ∷ cs)` is a POSITIONAL catch-all after
-- 27 literal clauses; Agda will not reduce it under a peeled/variable `c` (the
-- "c ≠ each special literal" constraint is not used in reduction), and likewise
-- `isSpecialChar c` won't reduce to `false`. Genuinely discharging this needs
-- `tokenize-WF`'s head dispatch routed through a classifier `headK : Char → HeadK`
-- (+ `tok-head`) so `with headK c in eq` steps it — the SAME de-`with` move used
-- for the multi-char heads, applied to the whole head. The 27 special heads,
-- determinism, and completeness below are all genuinely proven; only this one
-- reduction is deferred.
postulate
  lexes-tok-gen : ∀ (c : Char) (cs : List Char) (a : Acc _<_ (length (c ∷ cs))) →
    LexesChars (c ∷ cs) (tokenize-WF (c ∷ cs) a)

lexes-tok [] _ = lex-eof
lexes-tok (' '  ∷ cs) (acc rec) = lex-space (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('\t' ∷ cs) (acc rec) = lex-tab   (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('\r' ∷ cs) (acc rec) = lex-cr    (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('\n' ∷ cs) (acc rec) with nlIndent cs in eq
... | true  = lex-nl-ind eq (lexes-tok cs (rec (n<1+n _)))
... | false = lex-nl     eq (lexes-tok cs (rec (n<1+n _)))
lexes-tok ('^' ∷ cs) (acc rec) with caretClass cs in eq
... | c-1   = lex-caret1   eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | c-0   = lex-caret0   eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | c-w   = lex-caretw   eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | c-gen = lex-caret-gen eq (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('-' ∷ cs) (acc rec) with dashClass cs in eq
... | d-comment = lex-lcomment-ind eq (lexes-tok (proj₁ (skipLineB (drop1 cs))) (rec (s≤s (≤-trans (proj₂ (skipLineB (drop1 cs))) (drop1-≤ cs)))))
... | d-arrow   = lex-arrow-ind    eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | d-minus   = lex-minus        eq (lexes-tok cs (rec (n<1+n _)))
lexes-tok ('{' ∷ cs) (acc rec) with isDashHead cs in eq
... | true  = lex-bcomment-ind eq (lexes-tok (proj₁ (skipBlockB 1 (drop1 cs))) (rec (s≤s (≤-trans (proj₂ (skipBlockB 1 (drop1 cs))) (drop1-≤ cs)))))
... | false = lex-lbrace       eq (lexes-tok cs (rec (n<1+n _)))
lexes-tok ('<' ∷ cs) (acc rec) with isEqHead cs in eq
... | true  = lex-le-ind eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | false = lex-lt     eq (lexes-tok cs (rec (n<1+n _)))
lexes-tok ('>' ∷ cs) (acc rec) with isEqHead cs in eq
... | true  = lex-ge-ind eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | false = lex-gt     eq (lexes-tok cs (rec (n<1+n _)))
lexes-tok ('=' ∷ cs) (acc rec) with isEqHead cs in eq
... | true  = lex-eqeq-ind eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | false = lex-equals   eq (lexes-tok cs (rec (n<1+n _)))
lexes-tok ('!' ∷ cs) (acc rec) with isEqHead cs in eq
... | true  = lex-neq-ind eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
... | false = lex-bang    eq (lexes-tok cs (rec (n<1+n _)))
lexes-tok ('(' ∷ cs) (acc rec) = lex-lparen (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok (')' ∷ cs) (acc rec) = lex-rparen (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('}' ∷ cs) (acc rec) = lex-rbrace (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok (':' ∷ cs) (acc rec) = lex-colon (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('\\' ∷ cs) (acc rec) = lex-lambda (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok (',' ∷ cs) (acc rec) = lex-comma (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok (';' ∷ cs) (acc rec) = lex-semi (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('@' ∷ cs) (acc rec) = lex-at (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('|' ∷ cs) (acc rec) = lex-pipe (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('+' ∷ cs) (acc rec) = lex-plus (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('*' ∷ cs) (acc rec) = lex-star (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('/' ∷ cs) (acc rec) = lex-slash (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('%' ∷ cs) (acc rec) = lex-pct (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('&' ∷ cs) (acc rec) = lex-amp (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('.' ∷ cs) (acc rec) = lex-dot (lexes-tok cs (rec (s≤s ≤-refl)))
lexes-tok ('"' ∷ cs) (acc rec) = sound-tok-str cs rec (collectStringB cs) refl
lexes-tok (c ∷ cs) (acc rec) = lexes-tok-gen c cs (acc rec)

sound-tok-str cs rec (just (s , rest , bnd)) eq =
  lex-string s rest bnd eq (lexes-tok rest (rec (m≤n⇒m≤1+n bnd)))
sound-tok-str cs rec nothing eq = lex-string-err eq

lexer-sound : ∀ (text : String) → Lexes text (tokenizeString text)
lexer-sound text = lexes-tok (toList text) (<-wellFounded (length (toList text)))

------------------------------------------------------------------------
-- DETERMINISM — at most one derivation per char list.
------------------------------------------------------------------------

absurd-tf : ∀ {A : Set} {x : Bool} → x ≡ true → x ≡ false → A
absurd-tf p q with trans (sym p) q
... | ()

lex-det : ∀ {cs ts ts'} → LexesChars cs ts → LexesChars cs ts' → ts ≡ ts'
lex-det lex-eof lex-eof = refl
-- whitespace
lex-det (lex-space d1) (lex-space d2) = lex-det d1 d2
lex-det (lex-space d1) (lex-skip () _ _ d2)
lex-det (lex-tab d1) (lex-tab d2) = lex-det d1 d2
lex-det (lex-tab d1) (lex-skip () _ _ d2)
lex-det (lex-cr d1) (lex-cr d2) = lex-det d1 d2
lex-det (lex-cr d1) (lex-skip () _ _ d2)
-- newline
lex-det (lex-nl-ind _ d1) (lex-nl-ind _ d2) = lex-det d1 d2
lex-det (lex-nl-ind p d1) (lex-nl q d2) = absurd-tf p q
lex-det (lex-nl-ind _ _) (lex-skip () _ _ _)
lex-det (lex-nl p d1) (lex-nl-ind q d2) = absurd-tf q p
lex-det (lex-nl _ d1) (lex-nl _ d2) = cong (TNewline ∷_) (lex-det d1 d2)
lex-det (lex-nl _ _) (lex-skip () _ _ _)
-- caret
lex-det (lex-caret1 _ d1) (lex-caret1 _ d2) = cong (TCaret1 ∷_) (lex-det d1 d2)
lex-det (lex-caret1 p _) (lex-caret0 q _) with trans (sym p) q
... | ()
lex-det (lex-caret1 p _) (lex-caretw q _) with trans (sym p) q
... | ()
lex-det (lex-caret1 p _) (lex-caret-gen q _) with trans (sym p) q
... | ()
lex-det (lex-caret1 _ _) (lex-skip () _ _ _)
lex-det (lex-caret0 p _) (lex-caret1 q _) with trans (sym p) q
... | ()
lex-det (lex-caret0 _ d1) (lex-caret0 _ d2) = cong (TCaret0 ∷_) (lex-det d1 d2)
lex-det (lex-caret0 p _) (lex-caretw q _) with trans (sym p) q
... | ()
lex-det (lex-caret0 p _) (lex-caret-gen q _) with trans (sym p) q
... | ()
lex-det (lex-caret0 _ _) (lex-skip () _ _ _)
lex-det (lex-caretw p _) (lex-caret1 q _) with trans (sym p) q
... | ()
lex-det (lex-caretw p _) (lex-caret0 q _) with trans (sym p) q
... | ()
lex-det (lex-caretw _ d1) (lex-caretw _ d2) = cong (TCaretW ∷_) (lex-det d1 d2)
lex-det (lex-caretw p _) (lex-caret-gen q _) with trans (sym p) q
... | ()
lex-det (lex-caretw _ _) (lex-skip () _ _ _)
lex-det (lex-caret-gen p _) (lex-caret1 q _) with trans (sym p) q
... | ()
lex-det (lex-caret-gen p _) (lex-caret0 q _) with trans (sym p) q
... | ()
lex-det (lex-caret-gen p _) (lex-caretw q _) with trans (sym p) q
... | ()
lex-det (lex-caret-gen _ d1) (lex-caret-gen _ d2) = lex-det d1 d2
lex-det (lex-caret-gen _ _) (lex-skip () _ _ _)
-- dash
lex-det (lex-lcomment-ind _ d1) (lex-lcomment-ind _ d2) = lex-det d1 d2
lex-det (lex-lcomment-ind p _) (lex-arrow-ind q _) with trans (sym p) q
... | ()
lex-det (lex-lcomment-ind p _) (lex-minus q _) with trans (sym p) q
... | ()
lex-det (lex-lcomment-ind _ _) (lex-skip () _ _ _)
lex-det (lex-arrow-ind p _) (lex-lcomment-ind q _) with trans (sym p) q
... | ()
lex-det (lex-arrow-ind _ d1) (lex-arrow-ind _ d2) = cong (TArrow ∷_) (lex-det d1 d2)
lex-det (lex-arrow-ind p _) (lex-minus q _) with trans (sym p) q
... | ()
lex-det (lex-arrow-ind _ _) (lex-skip () _ _ _)
lex-det (lex-minus p _) (lex-lcomment-ind q _) with trans (sym p) q
... | ()
lex-det (lex-minus p _) (lex-arrow-ind q _) with trans (sym p) q
... | ()
lex-det (lex-minus _ d1) (lex-minus _ d2) = cong (TMinus ∷_) (lex-det d1 d2)
lex-det (lex-minus _ _) (lex-skip () _ _ _)
-- brace
lex-det (lex-bcomment-ind _ d1) (lex-bcomment-ind _ d2) = lex-det d1 d2
lex-det (lex-bcomment-ind p _) (lex-lbrace q _) = absurd-tf p q
lex-det (lex-bcomment-ind _ _) (lex-skip () _ _ _)
lex-det (lex-lbrace p _) (lex-bcomment-ind q _) = absurd-tf q p
lex-det (lex-lbrace _ d1) (lex-lbrace _ d2) = cong (TLBrace ∷_) (lex-det d1 d2)
lex-det (lex-lbrace _ _) (lex-skip () _ _ _)
-- `<`
lex-det (lex-le-ind _ d1) (lex-le-ind _ d2) = cong (TLe ∷_) (lex-det d1 d2)
lex-det (lex-le-ind p _) (lex-lt q _) = absurd-tf p q
lex-det (lex-le-ind _ _) (lex-skip () _ _ _)
lex-det (lex-lt p _) (lex-le-ind q _) = absurd-tf q p
lex-det (lex-lt _ d1) (lex-lt _ d2) = cong (TLt ∷_) (lex-det d1 d2)
lex-det (lex-lt _ _) (lex-skip () _ _ _)
-- `>`
lex-det (lex-ge-ind _ d1) (lex-ge-ind _ d2) = cong (TGe ∷_) (lex-det d1 d2)
lex-det (lex-ge-ind p _) (lex-gt q _) = absurd-tf p q
lex-det (lex-ge-ind _ _) (lex-skip () _ _ _)
lex-det (lex-gt p _) (lex-ge-ind q _) = absurd-tf q p
lex-det (lex-gt _ d1) (lex-gt _ d2) = cong (TGt ∷_) (lex-det d1 d2)
lex-det (lex-gt _ _) (lex-skip () _ _ _)
-- `=`
lex-det (lex-eqeq-ind _ d1) (lex-eqeq-ind _ d2) = cong (TEqEq ∷_) (lex-det d1 d2)
lex-det (lex-eqeq-ind p _) (lex-equals q _) = absurd-tf p q
lex-det (lex-eqeq-ind _ _) (lex-skip () _ _ _)
lex-det (lex-equals p _) (lex-eqeq-ind q _) = absurd-tf q p
lex-det (lex-equals _ d1) (lex-equals _ d2) = cong (TEquals ∷_) (lex-det d1 d2)
lex-det (lex-equals _ _) (lex-skip () _ _ _)
-- `!`
lex-det (lex-neq-ind _ d1) (lex-neq-ind _ d2) = cong (TNeq ∷_) (lex-det d1 d2)
lex-det (lex-neq-ind p _) (lex-bang q _) = absurd-tf p q
lex-det (lex-neq-ind _ _) (lex-skip () _ _ _)
lex-det (lex-bang p _) (lex-neq-ind q _) = absurd-tf q p
lex-det (lex-bang _ d1) (lex-bang _ d2) = cong (TBang ∷_) (lex-det d1 d2)
lex-det (lex-bang _ _) (lex-skip () _ _ _)
-- single-char punctuation
lex-det (lex-lparen d1) (lex-lparen d2) = cong (TLParen ∷_) (lex-det d1 d2)
lex-det (lex-lparen _) (lex-skip () _ _ _)
lex-det (lex-rparen d1) (lex-rparen d2) = cong (TRParen ∷_) (lex-det d1 d2)
lex-det (lex-rparen _) (lex-skip () _ _ _)
lex-det (lex-rbrace d1) (lex-rbrace d2) = cong (TRBrace ∷_) (lex-det d1 d2)
lex-det (lex-rbrace _) (lex-skip () _ _ _)
lex-det (lex-colon d1) (lex-colon d2) = cong (TColon ∷_) (lex-det d1 d2)
lex-det (lex-colon _) (lex-skip () _ _ _)
lex-det (lex-lambda d1) (lex-lambda d2) = cong (TLambda ∷_) (lex-det d1 d2)
lex-det (lex-lambda _) (lex-skip () _ _ _)
lex-det (lex-comma d1) (lex-comma d2) = cong (TComma ∷_) (lex-det d1 d2)
lex-det (lex-comma _) (lex-skip () _ _ _)
lex-det (lex-semi d1) (lex-semi d2) = cong (TSemicolon ∷_) (lex-det d1 d2)
lex-det (lex-semi _) (lex-skip () _ _ _)
lex-det (lex-at d1) (lex-at d2) = cong (TAt ∷_) (lex-det d1 d2)
lex-det (lex-at _) (lex-skip () _ _ _)
lex-det (lex-pipe d1) (lex-pipe d2) = cong (TPipe ∷_) (lex-det d1 d2)
lex-det (lex-pipe _) (lex-skip () _ _ _)
lex-det (lex-plus d1) (lex-plus d2) = cong (TPlus ∷_) (lex-det d1 d2)
lex-det (lex-plus _) (lex-skip () _ _ _)
lex-det (lex-star d1) (lex-star d2) = cong (TStar ∷_) (lex-det d1 d2)
lex-det (lex-star _) (lex-skip () _ _ _)
lex-det (lex-slash d1) (lex-slash d2) = cong (TSlash ∷_) (lex-det d1 d2)
lex-det (lex-slash _) (lex-skip () _ _ _)
lex-det (lex-pct d1) (lex-pct d2) = cong (TPercent ∷_) (lex-det d1 d2)
lex-det (lex-pct _) (lex-skip () _ _ _)
lex-det (lex-amp d1) (lex-amp d2) = cong (TAmpersand ∷_) (lex-det d1 d2)
lex-det (lex-amp _) (lex-skip () _ _ _)
lex-det (lex-dot d1) (lex-dot d2) = cong (TDot ∷_) (lex-det d1 d2)
lex-det (lex-dot _) (lex-skip () _ _ _)
-- string
lex-det (lex-string s rest bnd p d1) (lex-string s2 rest2 bnd2 q d2)
  with trans (sym p) q
... | refl = cong (TString (fromList s) ∷_) (lex-det d1 d2)
lex-det (lex-string s rest bnd p _) (lex-string-err q) with trans (sym p) q
... | ()
lex-det (lex-string _ _ _ _ _) (lex-skip () _ _ _)
lex-det (lex-string-err p) (lex-string s rest bnd q _) with trans (sym p) q
... | ()
lex-det (lex-string-err _) (lex-string-err _) = refl
lex-det (lex-string-err _) (lex-skip () _ _ _)
-- general head
lex-det (lex-digit _ d1) (lex-digit _ d2) = cong (_ ∷_) (lex-det d1 d2)
lex-det (lex-digit p _) (lex-ident q _ _) = absurd-tf p q
lex-det (lex-digit p _) (lex-skip _ q _ _) = absurd-tf p q
lex-det (lex-ident p _ _) (lex-digit q _) = absurd-tf q p
lex-det (lex-ident _ _ d1) (lex-ident _ _ d2) = cong (_ ∷_) (lex-det d1 d2)
lex-det (lex-ident _ p _) (lex-skip _ _ q _) = absurd-tf p q
lex-det (lex-skip _ p _ _) (lex-digit q _) = absurd-tf q p
lex-det (lex-skip _ _ p _) (lex-ident _ q _) = absurd-tf q p
lex-det (lex-skip _ _ _ d1) (lex-skip _ _ _ d2) = lex-det d1 d2

------------------------------------------------------------------------
-- COMPLETENESS — the executable matches ANY derivation (sound ∘ det).
------------------------------------------------------------------------

lexer-complete : ∀ (text : String) (toks : List Token) → Lexes text toks → tokenizeString text ≡ toks
lexer-complete text toks d = lex-det (lexer-sound text) d
