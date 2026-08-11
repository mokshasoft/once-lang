-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.LexerBridge — the GENUINE lexer relation (Plan 0.52, NO shim,
-- NO postulate).
--
-- `LexesChars` is the independent char-production relation: one constructor per
-- `tokenize-WF` rule, each carrying a `headK c ≡ hkX` premise (the head
-- classifier from `Once.Parser.Lexer`) plus, for the multi-char heads, the
-- secondary classifier (`nlIndent cs ≡ true`, `isEqHead cs ≡ false`, …) and a
-- `drop1 cs` continuation. Both directions then REDUCE `tokenize-WF (c ∷ cs)` for
-- a VARIABLE head: soundness dispatches `with headK c in eq`; completeness
-- `rewrite`s the `headK c ≡ hkX` premise. (Agda will not reduce a positional
-- catch-all under a peeled literal — routing the head through `headK`/`tok-head`
-- is what makes this provable.)
--
--   * `lexer-sound`    : `Lexes text (tokenizeString text)`.
--   * `lexer-complete` : `Lexes text toks → tokenizeString text ≡ toks`.
--
-- `Once.Adequacy.FrontEndBridge` consumes `Lexes`/`lexer-sound`/`lexer-complete`.
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Parser.Token
open import Once.Parser.Lexer
  using (tokenize-WF; tok-str; tok-gen; tok-nl; tok-op2; tok-lbrace; tok-minus;
         tok-caret; tok-head; tokenizeString; isIdentStart;
         collectStringB; collectDigitsB; collectIdentB; skipLineB; skipBlockB;
         digitsToNat; drop1; drop1-≤;
         nlIndent; isEqHead; isDashHead; dashClass; caretClass;
         Dash3; d-comment; d-arrow; d-minus; Caret4; c-1; c-0; c-w; c-gen;
         HeadK; hkWS; hkNL; hkCaret; hkDash; hkLBrace; hkLt; hkGt; hkEq; hkBang;
         hkLParen; hkRParen; hkRBrace; hkColon; hkLambda; hkComma; hkSemi; hkAt;
         hkPipe; hkPlus; hkStar; hkSlash; hkPct; hkAmp; hkDot; hkStr; hkGen; headK)

------------------------------------------------------------------------
-- The relation.
------------------------------------------------------------------------

data LexesChars : List Char → List Token → Set where
  lex-eof : LexesChars [] (TEOF ∷ [])
  lex-ws  : ∀ {c cs ts} → headK c ≡ hkWS → LexesChars cs ts → LexesChars (c ∷ cs) ts
  -- newline (indent continuation vs significant TNewline)
  lex-nl-ind : ∀ {c cs ts} → headK c ≡ hkNL → nlIndent cs ≡ true  → LexesChars cs ts → LexesChars (c ∷ cs) ts
  lex-nl     : ∀ {c cs ts} → headK c ≡ hkNL → nlIndent cs ≡ false → LexesChars cs ts → LexesChars (c ∷ cs) (TNewline ∷ ts)
  -- grade carets
  lex-caret1    : ∀ {c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-1   → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TCaret1 ∷ ts)
  lex-caret0    : ∀ {c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-0   → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TCaret0 ∷ ts)
  lex-caretw    : ∀ {c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-w   → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TCaretW ∷ ts)
  lex-caret-gen : ∀ {c cs ts} → headK c ≡ hkCaret → caretClass cs ≡ c-gen → LexesChars cs ts → LexesChars (c ∷ cs) ts
  -- dash head: line comment / arrow / minus
  lex-lcomment-ind : ∀ {c cs ts} → headK c ≡ hkDash → dashClass cs ≡ d-comment → LexesChars (proj₁ (skipLineB (drop1 cs))) ts → LexesChars (c ∷ cs) ts
  lex-arrow-ind    : ∀ {c cs ts} → headK c ≡ hkDash → dashClass cs ≡ d-arrow   → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TArrow ∷ ts)
  lex-minus        : ∀ {c cs ts} → headK c ≡ hkDash → dashClass cs ≡ d-minus   → LexesChars cs ts → LexesChars (c ∷ cs) (TMinus ∷ ts)
  -- brace head: block comment / lbrace
  lex-bcomment-ind : ∀ {c cs ts} → headK c ≡ hkLBrace → isDashHead cs ≡ true  → LexesChars (proj₁ (skipBlockB 1 (drop1 cs))) ts → LexesChars (c ∷ cs) ts
  lex-lbrace       : ∀ {c cs ts} → headK c ≡ hkLBrace → isDashHead cs ≡ false → LexesChars cs ts → LexesChars (c ∷ cs) (TLBrace ∷ ts)
  -- `…=` operators
  lex-le-ind   : ∀ {c cs ts} → headK c ≡ hkLt   → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TLe ∷ ts)
  lex-lt       : ∀ {c cs ts} → headK c ≡ hkLt   → isEqHead cs ≡ false → LexesChars cs ts → LexesChars (c ∷ cs) (TLt ∷ ts)
  lex-ge-ind   : ∀ {c cs ts} → headK c ≡ hkGt   → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TGe ∷ ts)
  lex-gt       : ∀ {c cs ts} → headK c ≡ hkGt   → isEqHead cs ≡ false → LexesChars cs ts → LexesChars (c ∷ cs) (TGt ∷ ts)
  lex-eqeq-ind : ∀ {c cs ts} → headK c ≡ hkEq   → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TEqEq ∷ ts)
  lex-equals   : ∀ {c cs ts} → headK c ≡ hkEq   → isEqHead cs ≡ false → LexesChars cs ts → LexesChars (c ∷ cs) (TEquals ∷ ts)
  lex-neq-ind  : ∀ {c cs ts} → headK c ≡ hkBang → isEqHead cs ≡ true  → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TNeq ∷ ts)
  lex-bang     : ∀ {c cs ts} → headK c ≡ hkBang → isEqHead cs ≡ false → LexesChars cs ts → LexesChars (c ∷ cs) (TBang ∷ ts)
  -- single-char punctuation / operators
  lex-lparen : ∀ {c cs ts} → headK c ≡ hkLParen → LexesChars cs ts → LexesChars (c ∷ cs) (TLParen ∷ ts)
  lex-rparen : ∀ {c cs ts} → headK c ≡ hkRParen → LexesChars cs ts → LexesChars (c ∷ cs) (TRParen ∷ ts)
  lex-rbrace : ∀ {c cs ts} → headK c ≡ hkRBrace → LexesChars cs ts → LexesChars (c ∷ cs) (TRBrace ∷ ts)
  lex-colon  : ∀ {c cs ts} → headK c ≡ hkColon  → LexesChars cs ts → LexesChars (c ∷ cs) (TColon ∷ ts)
  lex-lambda : ∀ {c cs ts} → headK c ≡ hkLambda → LexesChars cs ts → LexesChars (c ∷ cs) (TLambda ∷ ts)
  lex-comma  : ∀ {c cs ts} → headK c ≡ hkComma  → LexesChars cs ts → LexesChars (c ∷ cs) (TComma ∷ ts)
  lex-semi   : ∀ {c cs ts} → headK c ≡ hkSemi   → LexesChars cs ts → LexesChars (c ∷ cs) (TSemicolon ∷ ts)
  lex-at     : ∀ {c cs ts} → headK c ≡ hkAt     → LexesChars cs ts → LexesChars (c ∷ cs) (TAt ∷ ts)
  lex-pipe   : ∀ {c cs ts} → headK c ≡ hkPipe   → LexesChars cs ts → LexesChars (c ∷ cs) (TPipe ∷ ts)
  lex-plus   : ∀ {c cs ts} → headK c ≡ hkPlus   → LexesChars cs ts → LexesChars (c ∷ cs) (TPlus ∷ ts)
  lex-star   : ∀ {c cs ts} → headK c ≡ hkStar   → LexesChars cs ts → LexesChars (c ∷ cs) (TStar ∷ ts)
  lex-slash  : ∀ {c cs ts} → headK c ≡ hkSlash  → LexesChars cs ts → LexesChars (c ∷ cs) (TSlash ∷ ts)
  lex-pct    : ∀ {c cs ts} → headK c ≡ hkPct    → LexesChars cs ts → LexesChars (c ∷ cs) (TPercent ∷ ts)
  lex-amp    : ∀ {c cs ts} → headK c ≡ hkAmp    → LexesChars cs ts → LexesChars (c ∷ cs) (TAmpersand ∷ ts)
  lex-dot    : ∀ {c cs ts} → headK c ≡ hkDot    → LexesChars cs ts → LexesChars (c ∷ cs) (TDot ∷ ts)
  -- string literals
  lex-string : ∀ {c cs ts} → headK c ≡ hkStr → (s rest : List Char) (bnd : length rest < length cs) →
    collectStringB cs ≡ just (s , rest , bnd) → LexesChars rest ts →
    LexesChars (c ∷ cs) (TString (fromList s) ∷ ts)
  lex-string-err : ∀ {c cs} → headK c ≡ hkStr → collectStringB cs ≡ nothing → LexesChars (c ∷ cs) []
  -- general head: digit / identifier / skip
  lex-digit : ∀ {c cs ts} → headK c ≡ hkGen → isDigit c ≡ true →
    LexesChars (proj₁ (proj₂ (collectDigitsB cs))) ts →
    LexesChars (c ∷ cs) (TInt (+ digitsToNat (c ∷ proj₁ (collectDigitsB cs))) ∷ ts)
  lex-ident : ∀ {c cs ts} → headK c ≡ hkGen → isDigit c ≡ false → isIdentStart c ≡ true →
    LexesChars (proj₁ (proj₂ (collectIdentB cs))) ts →
    LexesChars (c ∷ cs) (TWord (fromList (c ∷ proj₁ (collectIdentB cs))) ∷ ts)
  lex-skip : ∀ {c cs ts} → headK c ≡ hkGen → isDigit c ≡ false → isIdentStart c ≡ false →
    LexesChars cs ts → LexesChars (c ∷ cs) ts

Lexes : String → List Token → Set
Lexes text toks = LexesChars (toList text) toks

------------------------------------------------------------------------
-- SOUNDNESS — the executable's output is a valid derivation.
------------------------------------------------------------------------

lexes-tok : ∀ (cs : List Char) (a : Acc _<_ (length cs)) → LexesChars cs (tokenize-WF cs a)
sound-nl : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkNL → (b : Bool) → nlIndent cs ≡ b → LexesChars (c ∷ cs) (tok-nl cs rec b)
sound-caret : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkCaret → (k : Caret4) → caretClass cs ≡ k → LexesChars (c ∷ cs) (tok-caret cs rec k)
sound-dash : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkDash → (k : Dash3) → dashClass cs ≡ k → LexesChars (c ∷ cs) (tok-minus cs rec k)
sound-lbrace : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkLBrace → (b : Bool) → isDashHead cs ≡ b → LexesChars (c ∷ cs) (tok-lbrace cs rec b)
sound-lt : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkLt → (b : Bool) → isEqHead cs ≡ b → LexesChars (c ∷ cs) (tok-op2 cs rec TLe TLt b)
sound-gt : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkGt → (b : Bool) → isEqHead cs ≡ b → LexesChars (c ∷ cs) (tok-op2 cs rec TGe TGt b)
sound-eq : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkEq → (b : Bool) → isEqHead cs ≡ b → LexesChars (c ∷ cs) (tok-op2 cs rec TEqEq TEquals b)
sound-bang : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkBang → (b : Bool) → isEqHead cs ≡ b → LexesChars (c ∷ cs) (tok-op2 cs rec TNeq TBang b)
sound-str : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) → headK c ≡ hkStr →
  (r : Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ] length rest < length cs)) →
  collectStringB cs ≡ r → LexesChars (c ∷ cs) (tok-str cs rec r)
sound-gen : ∀ {c} (cs : List Char) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) → headK c ≡ hkGen →
  (d i : Bool) → isDigit c ≡ d → isIdentStart c ≡ i → LexesChars (c ∷ cs) (tok-gen c cs rec d i)

lexes-tok [] _ = lex-eof
lexes-tok (c ∷ cs) (acc rec) with headK c in eq
... | hkWS     = lex-ws eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkNL     = sound-nl cs rec eq (nlIndent cs) refl
... | hkCaret  = sound-caret cs rec eq (caretClass cs) refl
... | hkDash   = sound-dash cs rec eq (dashClass cs) refl
... | hkLBrace = sound-lbrace cs rec eq (isDashHead cs) refl
... | hkLt     = sound-lt cs rec eq (isEqHead cs) refl
... | hkGt     = sound-gt cs rec eq (isEqHead cs) refl
... | hkEq     = sound-eq cs rec eq (isEqHead cs) refl
... | hkBang   = sound-bang cs rec eq (isEqHead cs) refl
... | hkLParen = lex-lparen eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkRParen = lex-rparen eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkRBrace = lex-rbrace eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkColon  = lex-colon eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkLambda = lex-lambda eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkComma  = lex-comma eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkSemi   = lex-semi eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkAt     = lex-at eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkPipe   = lex-pipe eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkPlus   = lex-plus eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkStar   = lex-star eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkSlash  = lex-slash eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkPct    = lex-pct eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkAmp    = lex-amp eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkDot    = lex-dot eq (lexes-tok cs (rec (s≤s ≤-refl)))
... | hkStr    = sound-str cs rec eq (collectStringB cs) refl
... | hkGen    = sound-gen cs rec eq (isDigit c) (isIdentStart c) refl refl

sound-nl cs rec eqh true  eq = lex-nl-ind eqh eq (lexes-tok cs (rec (n<1+n _)))
sound-nl cs rec eqh false eq = lex-nl eqh eq (lexes-tok cs (rec (n<1+n _)))

sound-caret cs rec eqh c-1   eq = lex-caret1 eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-caret cs rec eqh c-0   eq = lex-caret0 eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-caret cs rec eqh c-w   eq = lex-caretw eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-caret cs rec eqh c-gen eq = lex-caret-gen eqh eq (lexes-tok cs (rec (s≤s ≤-refl)))

sound-dash cs rec eqh d-comment eq = lex-lcomment-ind eqh eq (lexes-tok (proj₁ (skipLineB (drop1 cs))) (rec (s≤s (≤-trans (proj₂ (skipLineB (drop1 cs))) (drop1-≤ cs)))))
sound-dash cs rec eqh d-arrow   eq = lex-arrow-ind eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-dash cs rec eqh d-minus   eq = lex-minus eqh eq (lexes-tok cs (rec (n<1+n _)))

sound-lbrace cs rec eqh true  eq = lex-bcomment-ind eqh eq (lexes-tok (proj₁ (skipBlockB 1 (drop1 cs))) (rec (s≤s (≤-trans (proj₂ (skipBlockB 1 (drop1 cs))) (drop1-≤ cs)))))
sound-lbrace cs rec eqh false eq = lex-lbrace eqh eq (lexes-tok cs (rec (n<1+n _)))

sound-lt cs rec eqh true  eq = lex-le-ind eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-lt cs rec eqh false eq = lex-lt eqh eq (lexes-tok cs (rec (n<1+n _)))
sound-gt cs rec eqh true  eq = lex-ge-ind eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-gt cs rec eqh false eq = lex-gt eqh eq (lexes-tok cs (rec (n<1+n _)))
sound-eq cs rec eqh true  eq = lex-eqeq-ind eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-eq cs rec eqh false eq = lex-equals eqh eq (lexes-tok cs (rec (n<1+n _)))
sound-bang cs rec eqh true  eq = lex-neq-ind eqh eq (lexes-tok (drop1 cs) (rec (s≤s (drop1-≤ cs))))
sound-bang cs rec eqh false eq = lex-bang eqh eq (lexes-tok cs (rec (n<1+n _)))

sound-str cs rec eqh (just (s , rest , bnd)) eq =
  lex-string eqh s rest bnd eq (lexes-tok rest (rec (m≤n⇒m≤1+n bnd)))
sound-str cs rec eqh nothing eq = lex-string-err eqh eq

sound-gen cs rec eqh true  i eqd eqi = lex-digit eqh eqd (lexes-tok _ (rec (s≤s (proj₂ (proj₂ (collectDigitsB cs))))))
sound-gen cs rec eqh false true  eqd eqi = lex-ident eqh eqd eqi (lexes-tok _ (rec (s≤s (proj₂ (proj₂ (collectIdentB cs))))))
sound-gen cs rec eqh false false eqd eqi = lex-skip eqh eqd eqi (lexes-tok cs (rec (s≤s ≤-refl)))

lexer-sound : ∀ (text : String) → Lexes text (tokenizeString text)
lexer-sound text = lexes-tok (toList text) (<-wellFounded (length (toList text)))

------------------------------------------------------------------------
-- COMPLETENESS — the executable matches ANY derivation. Induction on the
-- derivation, threading the Acc; `rewrite` the `headK c ≡ hkX` premise steps
-- `tokenize-WF (c ∷ cs)` even for a variable head.
------------------------------------------------------------------------

tok-complete : ∀ {cs ts} (a : Acc _<_ (length cs)) → LexesChars cs ts → tokenize-WF cs a ≡ ts
tok-complete _ lex-eof = refl
tok-complete (acc rec) (lex-ws eqh d) rewrite eqh = tok-complete (rec (s≤s ≤-refl)) d
tok-complete (acc rec) (lex-nl-ind eqh eq d) rewrite eqh | eq = tok-complete (rec (n<1+n _)) d
tok-complete (acc rec) (lex-nl eqh eq d) rewrite eqh | eq = cong (TNewline ∷_) (tok-complete (rec (n<1+n _)) d)
tok-complete (acc rec) (lex-caret1 {cs = cs} eqh eq d) rewrite eqh | eq = cong (TCaret1 ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-caret0 {cs = cs} eqh eq d) rewrite eqh | eq = cong (TCaret0 ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-caretw {cs = cs} eqh eq d) rewrite eqh | eq = cong (TCaretW ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-caret-gen eqh eq d) rewrite eqh | eq = tok-complete (rec (s≤s ≤-refl)) d
tok-complete (acc rec) (lex-lcomment-ind {cs = cs} eqh eq d) rewrite eqh | eq = tok-complete (rec (s≤s (≤-trans (proj₂ (skipLineB (drop1 cs))) (drop1-≤ cs)))) d
tok-complete (acc rec) (lex-arrow-ind {cs = cs} eqh eq d) rewrite eqh | eq = cong (TArrow ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-minus eqh eq d) rewrite eqh | eq = cong (TMinus ∷_) (tok-complete (rec (n<1+n _)) d)
tok-complete (acc rec) (lex-bcomment-ind {cs = cs} eqh eq d) rewrite eqh | eq = tok-complete (rec (s≤s (≤-trans (proj₂ (skipBlockB 1 (drop1 cs))) (drop1-≤ cs)))) d
tok-complete (acc rec) (lex-lbrace eqh eq d) rewrite eqh | eq = cong (TLBrace ∷_) (tok-complete (rec (n<1+n _)) d)
tok-complete (acc rec) (lex-le-ind {cs = cs} eqh eq d) rewrite eqh | eq = cong (TLe ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-lt eqh eq d) rewrite eqh | eq = cong (TLt ∷_) (tok-complete (rec (n<1+n _)) d)
tok-complete (acc rec) (lex-ge-ind {cs = cs} eqh eq d) rewrite eqh | eq = cong (TGe ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-gt eqh eq d) rewrite eqh | eq = cong (TGt ∷_) (tok-complete (rec (n<1+n _)) d)
tok-complete (acc rec) (lex-eqeq-ind {cs = cs} eqh eq d) rewrite eqh | eq = cong (TEqEq ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-equals eqh eq d) rewrite eqh | eq = cong (TEquals ∷_) (tok-complete (rec (n<1+n _)) d)
tok-complete (acc rec) (lex-neq-ind {cs = cs} eqh eq d) rewrite eqh | eq = cong (TNeq ∷_) (tok-complete (rec (s≤s (drop1-≤ cs))) d)
tok-complete (acc rec) (lex-bang eqh eq d) rewrite eqh | eq = cong (TBang ∷_) (tok-complete (rec (n<1+n _)) d)
tok-complete (acc rec) (lex-lparen eqh d) rewrite eqh = cong (TLParen ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-rparen eqh d) rewrite eqh = cong (TRParen ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-rbrace eqh d) rewrite eqh = cong (TRBrace ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-colon eqh d) rewrite eqh = cong (TColon ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-lambda eqh d) rewrite eqh = cong (TLambda ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-comma eqh d) rewrite eqh = cong (TComma ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-semi eqh d) rewrite eqh = cong (TSemicolon ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-at eqh d) rewrite eqh = cong (TAt ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-pipe eqh d) rewrite eqh = cong (TPipe ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-plus eqh d) rewrite eqh = cong (TPlus ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-star eqh d) rewrite eqh = cong (TStar ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-slash eqh d) rewrite eqh = cong (TSlash ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-pct eqh d) rewrite eqh = cong (TPercent ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-amp eqh d) rewrite eqh = cong (TAmpersand ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-dot eqh d) rewrite eqh = cong (TDot ∷_) (tok-complete (rec (s≤s ≤-refl)) d)
tok-complete (acc rec) (lex-string eqh s rest bnd eq d) rewrite eqh | eq = cong (TString (fromList s) ∷_) (tok-complete (rec (m≤n⇒m≤1+n bnd)) d)
tok-complete (acc rec) (lex-string-err eqh eq) rewrite eqh | eq = refl
tok-complete (acc rec) (lex-digit {cs = cs} eqh eq d) rewrite eqh | eq = cong (_ ∷_) (tok-complete (rec (s≤s (proj₂ (proj₂ (collectDigitsB cs))))) d)
tok-complete (acc rec) (lex-ident {cs = cs} eqh eqd eqi d) rewrite eqh | eqd | eqi = cong (_ ∷_) (tok-complete (rec (s≤s (proj₂ (proj₂ (collectIdentB cs))))) d)
tok-complete (acc rec) (lex-skip eqh eqd eqi d) rewrite eqh | eqd | eqi = tok-complete (rec (s≤s ≤-refl)) d

lexer-complete : ∀ (text : String) (toks : List Token) → Lexes text toks → tokenizeString text ≡ toks
lexer-complete text toks d = tok-complete (<-wellFounded (length (toList text))) d
