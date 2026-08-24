-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.LexerBridge — the GENUINE lexer relation (Plan 0.52).
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
open import Data.Nat using (ℕ; _<_; suc; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; n<1+n; n≤1+n; <⇒≤)
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
  using (adv; tokenize-WF; tok-str; tok-gen; tok-num; tok-nl; tok-op2; tok-lbrace; tok-minus;
         tok-caret; tok-head; tokenizeString; isIdentStart;
         collectStringB; collectDigitsB; collectFracB; collectIdentB; skipLineB; skipBlockB;
         digitsToNat; drop1; drop1-≤;
         nlIndent; isEqHead; isDashHead; dashClass; caretClass;
         Dash3; d-comment; d-arrow; d-minus; Caret4; c-1; c-0; c-w; c-gen;
         HeadK; hkWS; hkNL; hkCaret; hkDash; hkLBrace; hkLt; hkGt; hkEq; hkBang;
         hkLParen; hkRParen; hkRBrace; hkColon; hkLambda; hkComma; hkSemi; hkAt;
         hkPipe; hkPlus; hkStar; hkSlash; hkPct; hkAmp; hkDot; hkStr; hkGen; headK)

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

------------------------------------------------------------------------
-- SOUNDNESS — the executable's output is a valid derivation.
------------------------------------------------------------------------

lexes-tok : ∀ (cs : List Char) (off : ℕ) (a : Acc _<_ (length cs)) → LexesChars off cs (tokenize-WF cs off a)
sound-nl : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkNL → (b : Bool) → nlIndent cs ≡ b → LexesChars off (c ∷ cs) (tok-nl cs off rec b)
sound-caret : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkCaret → (k : Caret4) → caretClass cs ≡ k → LexesChars off (c ∷ cs) (tok-caret cs off rec k)
sound-dash : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkDash → (k : Dash3) → dashClass cs ≡ k → LexesChars off (c ∷ cs) (tok-minus cs off rec k)
sound-lbrace : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkLBrace → (b : Bool) → isDashHead cs ≡ b → LexesChars off (c ∷ cs) (tok-lbrace cs off rec b)
sound-lt : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkLt → (b : Bool) → isEqHead cs ≡ b → LexesChars off (c ∷ cs) (tok-op2 cs off rec TLe TLt b)
sound-gt : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkGt → (b : Bool) → isEqHead cs ≡ b → LexesChars off (c ∷ cs) (tok-op2 cs off rec TGe TGt b)
sound-eq : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkEq → (b : Bool) → isEqHead cs ≡ b → LexesChars off (c ∷ cs) (tok-op2 cs off rec TEqEq TEquals b)
sound-bang : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
  headK c ≡ hkBang → (b : Bool) → isEqHead cs ≡ b → LexesChars off (c ∷ cs) (tok-op2 cs off rec TNeq TBang b)
sound-str : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) → headK c ≡ hkStr →
  (r : Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ] length rest < length cs)) →
  collectStringB cs ≡ r → LexesChars off (c ∷ cs) (tok-str cs off rec r)
sound-num : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) →
            headK c ≡ hkGen → isDigit c ≡ true →
            (i : Bool)
            (m : Maybe (Σ[ f ∈ List Char ] Σ[ r ∈ List Char ]
                          length r < length (proj₁ (proj₂ (collectDigitsB cs))))) →
            collectFracB (proj₁ (proj₂ (collectDigitsB cs))) ≡ m →
            LexesChars off (c ∷ cs) (tok-gen c cs off rec true i)
sound-gen : ∀ {c} (cs : List Char) (off : ℕ) (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) → headK c ≡ hkGen →
  (d i : Bool) → isDigit c ≡ d → isIdentStart c ≡ i → LexesChars off (c ∷ cs) (tok-gen c cs off rec d i)

lexes-tok [] off _ = lex-eof
lexes-tok (c ∷ cs) off (acc rec) with headK c in eq
... | hkWS     = lex-ws eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkNL     = sound-nl cs off rec eq (nlIndent cs) refl
... | hkCaret  = sound-caret cs off rec eq (caretClass cs) refl
... | hkDash   = sound-dash cs off rec eq (dashClass cs) refl
... | hkLBrace = sound-lbrace cs off rec eq (isDashHead cs) refl
... | hkLt     = sound-lt cs off rec eq (isEqHead cs) refl
... | hkGt     = sound-gt cs off rec eq (isEqHead cs) refl
... | hkEq     = sound-eq cs off rec eq (isEqHead cs) refl
... | hkBang   = sound-bang cs off rec eq (isEqHead cs) refl
... | hkLParen = lex-lparen eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkRParen = lex-rparen eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkRBrace = lex-rbrace eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkColon  = lex-colon eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkLambda = lex-lambda eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkComma  = lex-comma eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkSemi   = lex-semi eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkAt     = lex-at eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkPipe   = lex-pipe eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkPlus   = lex-plus eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkStar   = lex-star eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkSlash  = lex-slash eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkPct    = lex-pct eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkAmp    = lex-amp eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkDot    = lex-dot eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))
... | hkStr    = sound-str cs off rec eq (collectStringB cs) refl
... | hkGen    = sound-gen cs off rec eq (isDigit c) (isIdentStart c) refl refl

sound-nl cs off rec eqh true  eq = lex-nl-ind eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))
sound-nl cs off rec eqh false eq = lex-nl eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))

sound-caret cs off rec eqh c-1   eq = lex-caret1 eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-caret cs off rec eqh c-0   eq = lex-caret0 eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-caret cs off rec eqh c-w   eq = lex-caretw eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-caret cs off rec eqh c-gen eq = lex-caret-gen eqh eq (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))

sound-dash cs off rec eqh d-comment eq = lex-lcomment-ind eqh eq (lexes-tok (proj₁ (skipLineB (drop1 cs))) (adv cs (proj₁ (skipLineB (drop1 cs))) off) (rec (s≤s (≤-trans (proj₂ (skipLineB (drop1 cs))) (drop1-≤ cs)))))
sound-dash cs off rec eqh d-arrow   eq = lex-arrow-ind eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-dash cs off rec eqh d-minus   eq = lex-minus eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))

sound-lbrace cs off rec eqh true  eq = lex-bcomment-ind eqh eq (lexes-tok (proj₁ (skipBlockB 1 (drop1 cs))) (adv cs (proj₁ (skipBlockB 1 (drop1 cs))) off) (rec (s≤s (≤-trans (proj₂ (skipBlockB 1 (drop1 cs))) (drop1-≤ cs)))))
sound-lbrace cs off rec eqh false eq = lex-lbrace eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))

sound-lt cs off rec eqh true  eq = lex-le-ind eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-lt cs off rec eqh false eq = lex-lt eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))
sound-gt cs off rec eqh true  eq = lex-ge-ind eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-gt cs off rec eqh false eq = lex-gt eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))
sound-eq cs off rec eqh true  eq = lex-eqeq-ind eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-eq cs off rec eqh false eq = lex-equals eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))
sound-bang cs off rec eqh true  eq = lex-neq-ind eqh eq (lexes-tok (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs))))
sound-bang cs off rec eqh false eq = lex-bang eqh eq (lexes-tok cs (adv cs cs off) (rec (n<1+n _)))

sound-str cs off rec eqh (just (s , rest , bnd)) eq =
  lex-string eqh s rest bnd eq (lexes-tok rest (adv cs rest off) (rec (m≤n⇒m≤1+n bnd)))
sound-str cs off rec eqh nothing eq = lex-string-err eqh eq

-- PLAN 0.71: the digit branch dispatches on `collectFracB`'s OUTCOME, taken as
-- an argument with its defining equation (`sound-num`), so the goal reduces on
-- the same value the tokenizer branched on. Passing the equation is what lets
-- the rule's premise be discharged by `refl` at each site — the alternative,
-- a `with` here, would abstract the goal away from `tok-num`'s clause.
sound-gen cs off rec eqh true  i eqd eqi =
  sound-num cs off rec eqh eqd i (collectFracB (proj₁ (proj₂ (collectDigitsB cs)))) refl
sound-gen cs off rec eqh false true  eqd eqi = lex-ident eqh eqd eqi (lexes-tok (proj₁ (proj₂ (collectIdentB cs))) (adv cs (proj₁ (proj₂ (collectIdentB cs))) off) (rec (s≤s (proj₂ (proj₂ (collectIdentB cs))))))
sound-gen cs off rec eqh false false eqd eqi = lex-skip eqh eqd eqi (lexes-tok cs (adv cs cs off) (rec (s≤s ≤-refl)))

sound-num cs off rec eqh eqd i nothing eqf
  rewrite eqf = lex-digit eqh eqd eqf (lexes-tok (proj₁ (proj₂ (collectDigitsB cs))) (adv cs (proj₁ (proj₂ (collectDigitsB cs))) off) (rec (s≤s (proj₂ (proj₂ (collectDigitsB cs))))))
sound-num cs off rec eqh eqd i (just (f , r , fbnd)) eqf
  rewrite eqf = lex-float eqh eqd eqf
                  (lexes-tok r (adv cs r off) (rec (s≤s (≤-trans (<⇒≤ fbnd) (proj₂ (proj₂ (collectDigitsB cs)))))))

lexer-sound : ∀ (text : String) → Lexes text (tokenizeString text)
lexer-sound text = lexes-tok (toList text) 0 (<-wellFounded (length (toList text)))

------------------------------------------------------------------------
-- COMPLETENESS — the executable matches ANY derivation. Induction on the
-- derivation, threading the Acc; `rewrite` the `headK c ≡ hkX` premise steps
-- `tokenize-WF (c ∷ cs)` even for a variable head.
------------------------------------------------------------------------

tok-complete : ∀ {cs ts off} (a : Acc _<_ (length cs)) → LexesChars off cs ts → tokenize-WF cs off a ≡ ts
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
tok-complete (acc rec) (lex-digit {cs = cs} eqh eq eqf d) rewrite eqh | eq | eqf = cong (_ ∷_) (tok-complete (rec (s≤s (proj₂ (proj₂ (collectDigitsB cs))))) d)
tok-complete (acc rec) (lex-float {cs = cs} {bnd = fbnd} eqh eq eqf d) rewrite eqh | eq | eqf =
  cong (_ ∷_) (tok-complete (rec (s≤s (≤-trans (<⇒≤ fbnd) (proj₂ (proj₂ (collectDigitsB cs)))))) d)
tok-complete (acc rec) (lex-ident {cs = cs} eqh eqd eqi d) rewrite eqh | eqd | eqi = cong (_ ∷_) (tok-complete (rec (s≤s (proj₂ (proj₂ (collectIdentB cs))))) d)
tok-complete (acc rec) (lex-skip eqh eqd eqi d) rewrite eqh | eqd | eqi = tok-complete (rec (s≤s ≤-refl)) d

lexer-complete : ∀ (text : String) (toks : List Token) → Lexes text toks → tokenizeString text ≡ toks
lexer-complete text toks d = tok-complete (<-wellFounded (length (toList text))) d
