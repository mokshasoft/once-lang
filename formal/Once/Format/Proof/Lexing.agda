-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Lexing — what the layout writes lexes as its tokens
-- (plan 0.124 step 4.3).
--
-- A list of lexemes is well formed (`WS`) when each is (a printable token, a
-- line comment) and each pair of neighbours is one the layout writes: two
-- tokens only when they are not `apart`, a comment after a blank or at the
-- start of a line and before its line end, indentation only after a line end.
-- Its text then lexes (the Spec's `LexesChars`) as `run false`: the tokens,
-- with a `TNewline` for each line end not followed by an indented line, and
-- `TEOF`.
--
-- Generated (the cases per token) by `scripts/gen-format-lexing.py`: edit the
-- generator, not this file.
------------------------------------------------------------------------

module Once.Format.Proof.Lexing where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; isDigit)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; replicate; concatMap; length)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _^_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.String.Properties using (primStringToListInjective)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing
open import Once.Format.Spell using (spell; decimal; fixed)
open import Once.Format.Doc using (Lexeme; lt; lsp; lnl; lind; lcm; chars; apart; continues; number; dashes;
  greater; equals)
open import Once.Format.Proof.Digits using (decimal-val; decimal-digits; decimal-nonempty; fixed-val;
  fixed-length; fixed-digits; fixed-nonempty; decimal-head)

------------------------------------------------------------------------
-- Printable tokens, line comments
------------------------------------------------------------------------

data Sym : Token → Set where
  s-lparen : Sym TLParen
  s-rparen : Sym TRParen
  s-lbrace : Sym TLBrace
  s-rbrace : Sym TRBrace
  s-colon : Sym TColon
  s-equals : Sym TEquals
  s-arrow : Sym TArrow
  s-caret1 : Sym TCaret1
  s-caret0 : Sym TCaret0
  s-caretw : Sym TCaretW
  s-lambda : Sym TLambda
  s-comma : Sym TComma
  s-semicolon : Sym TSemicolon
  s-at : Sym TAt
  s-pipe : Sym TPipe
  s-dot : Sym TDot
  s-plus : Sym TPlus
  s-minus : Sym TMinus
  s-star : Sym TStar
  s-slash : Sym TSlash
  s-percent : Sym TPercent
  s-ampersand : Sym TAmpersand
  s-lt : Sym TLt
  s-le : Sym TLe
  s-gt : Sym TGt
  s-ge : Sym TGe
  s-eqeq : Sym TEqEq
  s-neq : Sym TNeq
  s-bang : Sym TBang

-- A token that lexes back from its spelling: a word that is an identifier, a
-- non-negative integer, a float whose fraction fits its digits, a symbol.
data Printable : Token → Set where
  p-word  : ∀ {s c i} → toList s ≡ c ∷ i → ¬ Special c → isDigit c ≡ false → isIdentStart c ≡ true
          → All (λ x → isIdentContinue x ≡ true) i → Printable (TWord s)
  p-int   : ∀ {n} → Printable (TInt (+ n))
  p-float : ∀ {i f l} → f < 10 ^ suc l → Printable (TFloat i f (suc l))
  p-sym   : ∀ {t} → Sym t → Printable t

-- `--` and the rest of the line.
data LineComment : List Char → Set where
  lc : ∀ {b} → All (λ x → x ≢ '\n') b → LineComment ('-' ∷ '-' ∷ b)

------------------------------------------------------------------------
-- What may follow a token
------------------------------------------------------------------------

-- The first character, if any, is not one of `p`.
data Stop (p : Char → Bool) : List Char → Set where
  stop-end : Stop p []
  stop     : ∀ {c cs} → p c ≡ false → Stop p (c ∷ cs)

Follows : Token → List Char → Set
Follows (TWord _) cs = Stop isIdentContinue cs
Follows (TInt _) cs = Stop isDigit cs × ¬ Next cs '.'
Follows (TFloat _ _ _) cs = Stop isDigit cs
Follows (TString _) cs = ⊤
Follows TLParen cs = ⊤
Follows TRParen cs = ⊤
Follows TLBrace cs = ¬ Next cs '-'
Follows TRBrace cs = ⊤
Follows TColon cs = ⊤
Follows TEquals cs = ¬ Next cs '='
Follows TArrow cs = ⊤
Follows TCaret1 cs = ⊤
Follows TCaret0 cs = ⊤
Follows TCaretW cs = ⊤
Follows TLambda cs = ⊤
Follows TComma cs = ⊤
Follows TSemicolon cs = ⊤
Follows TAt cs = ⊤
Follows TPipe cs = ⊤
Follows TDot cs = ⊤
Follows TPlus cs = ⊤
Follows TMinus cs = ¬ Next cs '-' × ¬ Next cs '>'
Follows TStar cs = ⊤
Follows TSlash cs = ⊤
Follows TPercent cs = ⊤
Follows TAmpersand cs = ⊤
Follows TLt cs = ¬ Next cs '='
Follows TLe cs = ⊤
Follows TGt cs = ¬ Next cs '='
Follows TGe cs = ⊤
Follows TEqEq cs = ⊤
Follows TNeq cs = ⊤
Follows TBang cs = ¬ Next cs '='
Follows TNewline cs = ⊤
Follows TEOF cs = ⊤

private
  fromList∘toList : ∀ s → fromList (toList s) ≡ s
  fromList∘toList s = primStringToListInjective _ _ (toList∘fromList (toList s))

  identRest : ∀ {i cs} → All (λ x → isIdentContinue x ≡ true) i → Stop isIdentContinue cs → IdentRest (i ++ cs) i cs
  identRest []       stop-end = id-end
  identRest []       (stop q) = id-stop q
  identRest (p ∷ ps) s        = id-more p (identRest ps s)

  digitsRest : ∀ {ds cs} → All (λ x → isDigit x ≡ true) ds → Stop isDigit cs → Digits (ds ++ cs) ds cs
  digitsRest []       stop-end = dg-end
  digitsRest []       (stop q) = dg-stop q
  digitsRest (p ∷ ps) s        = dg-more p (digitsRest ps s)

  lineRest : ∀ {b cs} → All (λ x → x ≢ '\n') b → LineRest (b ++ '\n' ∷ cs) ('\n' ∷ cs)
  lineRest []       = lr-nl
  lineRest (p ∷ ps) = lr-char p (lineRest ps)

  -- A character of one kind is not one of another.
  nx : ∀ {c d cs} (f : Char → Bool) → f c ≡ true → f d ≡ false → ¬ Next (c ∷ cs) d
  nx f fc fd next with () ← trans (sym fc) fd

  lex-int′ : ∀ {xs cs ts} → All (λ x → isDigit x ≡ true) xs → xs ≢ [] → Stop isDigit cs → ¬ Next cs '.'
           → LexesChars cs ts → LexesChars (xs ++ cs) (TInt (+ digitsToNat xs) ∷ ts)
  lex-int′ []       ne _ _  _ with () ← ne refl
  lex-int′ (p ∷ ps) _  s nd l = lex-int p (digitsRest ps s) nofrac l
    where
      nofrac : ¬ (Data.Product.∃ λ f → Data.Product.∃ λ r′ → Fraction _ f r′)
      nofrac (_ , _ , fraction _ _) = nd next

  lex-float′ : ∀ {xs fs cs ts} → All (λ x → isDigit x ≡ true) xs → xs ≢ [] → All (λ x → isDigit x ≡ true) fs
             → fs ≢ [] → Stop isDigit cs → LexesChars cs ts
             → LexesChars (xs ++ '.' ∷ fs ++ cs) (TFloat (digitsToNat xs) (digitsToNat fs) (length fs) ∷ ts)
  lex-float′ []       ne _        _   _ _ with () ← ne refl
  lex-float′ (_ ∷ _)  _  []       ne  _ _ with () ← ne refl
  lex-float′ (p ∷ ps) _  (q ∷ qs) _   s l = lex-float p (digitsRest ps (stop refl)) (fraction q (digitsRest qs s)) l

  nonempty : ∀ {A : Set} {xs : List A} {y ys} → xs ≡ y ∷ ys → xs ≢ []
  nonempty refl ()

-- | A printable token, then what may follow it.
lex-token : ∀ {t cs ts} → Printable t → Follows t cs → LexesChars cs ts → LexesChars (chars (lt t) ++ cs) (t ∷ ts)
lex-token {TWord s} {cs} {ts} (p-word {c = c} {i} eq ¬s ¬d st ps) f l =
  subst (λ xs → LexesChars (xs ++ cs) (TWord s ∷ ts)) (sym eq)
    (subst (λ x → LexesChars (c ∷ i ++ cs) (TWord x ∷ ts)) (trans (cong fromList (sym eq)) (fromList∘toList s))
      (lex-ident ¬s ¬d st (identRest ps f) l))
lex-token {TInt (+ n)} {cs} {ts} p-int (f , nd) l =
  subst (λ xs → LexesChars (xs ++ cs) (TInt (+ n) ∷ ts)) (sym (toList∘fromList (decimal n)))
    (subst (λ v → LexesChars (decimal n ++ cs) (TInt (+ v) ∷ ts)) (decimal-val n)
      (lex-int′ (decimal-digits n) (nonempty (proj₂ (proj₂ (decimal-nonempty n)))) f nd l))
lex-token {TFloat i f (suc k)} {cs} {ts} (p-float f<) fo l =
  subst (λ xs → LexesChars (xs ++ cs) (TFloat i f (suc k) ∷ ts)) (sym (toList∘fromList (decimal i ++ '.' ∷ fixed (suc k) f)))
    (subst (λ xs → LexesChars xs (TFloat i f (suc k) ∷ ts)) (sym (++-assoc (decimal i) ('.' ∷ fixed (suc k) f) cs))
      (subst (λ v → LexesChars (decimal i ++ '.' ∷ fixed (suc k) f ++ cs) (TFloat v f (suc k) ∷ ts)) (decimal-val i)
        (subst (λ v → LexesChars (decimal i ++ '.' ∷ fixed (suc k) f ++ cs) (TFloat (digitsToNat (decimal i)) v (suc k) ∷ ts))
          (fixed-val (suc k) f f<)
          (subst (λ v → LexesChars (decimal i ++ '.' ∷ fixed (suc k) f ++ cs)
                          (TFloat (digitsToNat (decimal i)) (digitsToNat (fixed (suc k) f)) v ∷ ts))
            (fixed-length (suc k) f)
            (lex-float′ (decimal-digits i) (nonempty (proj₂ (proj₂ (decimal-nonempty i))))
              (fixed-digits (suc k) f) (nonempty (proj₂ (proj₂ (fixed-nonempty k f)))) fo l)))))
lex-token (p-sym s-lparen) f l = lex-lparen l
lex-token (p-sym s-rparen) f l = lex-rparen l
lex-token (p-sym s-lbrace) f l = lex-lbrace f l
lex-token (p-sym s-rbrace) f l = lex-rbrace l
lex-token (p-sym s-colon) f l = lex-colon l
lex-token (p-sym s-equals) f l = lex-equal f l
lex-token (p-sym s-arrow) f l = lex-arrow l
lex-token (p-sym s-caret1) f l = lex-caret1 l
lex-token (p-sym s-caret0) f l = lex-caret0 l
lex-token (p-sym s-caretw) f l = lex-caretw l
lex-token (p-sym s-lambda) f l = lex-lambda l
lex-token (p-sym s-comma) f l = lex-comma l
lex-token (p-sym s-semicolon) f l = lex-semi l
lex-token (p-sym s-at) f l = lex-at l
lex-token (p-sym s-pipe) f l = lex-pipe l
lex-token (p-sym s-dot) f l = lex-dot l
lex-token (p-sym s-plus) f l = lex-plus l
lex-token (p-sym s-minus) f l = lex-minus (proj₁ f) (proj₂ f) l
lex-token (p-sym s-star) f l = lex-star l
lex-token (p-sym s-slash) f l = lex-slash l
lex-token (p-sym s-percent) f l = lex-pct l
lex-token (p-sym s-ampersand) f l = lex-amp l
lex-token (p-sym s-lt) f l = lex-lt f l
lex-token (p-sym s-le) f l = lex-le l
lex-token (p-sym s-gt) f l = lex-gt f l
lex-token (p-sym s-ge) f l = lex-ge l
lex-token (p-sym s-eqeq) f l = lex-eqeq l
lex-token (p-sym s-neq) f l = lex-neq l
lex-token (p-sym s-bang) f l = lex-bang f l

------------------------------------------------------------------------
-- What follows a token, in the layout
------------------------------------------------------------------------

-- | A blank may follow any token.
follows-sp : ∀ u {cs} → Follows u (' ' ∷ cs)
follows-sp (TWord _) = stop refl
follows-sp (TInt _) = stop refl , (λ ())
follows-sp (TFloat _ _ _) = stop refl
follows-sp (TString _) = tt
follows-sp TLParen = tt
follows-sp TRParen = tt
follows-sp TLBrace = λ ()
follows-sp TRBrace = tt
follows-sp TColon = tt
follows-sp TEquals = λ ()
follows-sp TArrow = tt
follows-sp TCaret1 = tt
follows-sp TCaret0 = tt
follows-sp TCaretW = tt
follows-sp TLambda = tt
follows-sp TComma = tt
follows-sp TSemicolon = tt
follows-sp TAt = tt
follows-sp TPipe = tt
follows-sp TDot = tt
follows-sp TPlus = tt
follows-sp TMinus = (λ ()) , (λ ())
follows-sp TStar = tt
follows-sp TSlash = tt
follows-sp TPercent = tt
follows-sp TAmpersand = tt
follows-sp TLt = λ ()
follows-sp TLe = tt
follows-sp TGt = λ ()
follows-sp TGe = tt
follows-sp TEqEq = tt
follows-sp TNeq = tt
follows-sp TBang = λ ()
follows-sp TNewline = tt
follows-sp TEOF = tt

-- | A line end may follow any token.
follows-nl : ∀ u {cs} → Follows u ('\n' ∷ cs)
follows-nl (TWord _) = stop refl
follows-nl (TInt _) = stop refl , (λ ())
follows-nl (TFloat _ _ _) = stop refl
follows-nl (TString _) = tt
follows-nl TLParen = tt
follows-nl TRParen = tt
follows-nl TLBrace = λ ()
follows-nl TRBrace = tt
follows-nl TColon = tt
follows-nl TEquals = λ ()
follows-nl TArrow = tt
follows-nl TCaret1 = tt
follows-nl TCaret0 = tt
follows-nl TCaretW = tt
follows-nl TLambda = tt
follows-nl TComma = tt
follows-nl TSemicolon = tt
follows-nl TAt = tt
follows-nl TPipe = tt
follows-nl TDot = tt
follows-nl TPlus = tt
follows-nl TMinus = (λ ()) , (λ ())
follows-nl TStar = tt
follows-nl TSlash = tt
follows-nl TPercent = tt
follows-nl TAmpersand = tt
follows-nl TLt = λ ()
follows-nl TLe = tt
follows-nl TGt = λ ()
follows-nl TGe = tt
follows-nl TEqEq = tt
follows-nl TNeq = tt
follows-nl TBang = λ ()
follows-nl TNewline = tt
follows-nl TEOF = tt

-- | Any token may end the text.
follows-end : ∀ u → Follows u []
follows-end (TWord _) = stop-end
follows-end (TInt _) = stop-end , λ ()
follows-end (TFloat _ _ _) = stop-end
follows-end (TString _) = tt
follows-end TLParen = tt
follows-end TRParen = tt
follows-end TLBrace = λ ()
follows-end TRBrace = tt
follows-end TColon = tt
follows-end TEquals = λ ()
follows-end TArrow = tt
follows-end TCaret1 = tt
follows-end TCaret0 = tt
follows-end TCaretW = tt
follows-end TLambda = tt
follows-end TComma = tt
follows-end TSemicolon = tt
follows-end TAt = tt
follows-end TPipe = tt
follows-end TDot = tt
follows-end TPlus = tt
follows-end TMinus = (λ ()) , (λ ())
follows-end TStar = tt
follows-end TSlash = tt
follows-end TPercent = tt
follows-end TAmpersand = tt
follows-end TLt = λ ()
follows-end TLe = tt
follows-end TGt = λ ()
follows-end TGe = tt
follows-end TEqEq = tt
follows-end TNeq = tt
follows-end TBang = λ ()
follows-end TNewline = tt
follows-end TEOF = tt

private
  headNext : ∀ {xs ys c cs d} (f : Char → Bool) → xs ≡ c ∷ cs → f c ≡ true → f d ≡ false → ¬ Next (xs ++ ys) d
  headNext f refl fc fd = nx f fc fd

  -- The first character of a word, an integer, a float.
  wordNext : ∀ {s c i cs d} → toList s ≡ c ∷ i → isIdentStart c ≡ true → isIdentStart d ≡ false
           → ¬ Next (toList s ++ cs) d
  wordNext eq st sd = headNext isIdentStart eq st sd

  intNext : ∀ n {cs d} → isDigit d ≡ false → ¬ Next (toList (fromList (decimal n)) ++ cs) d
  intNext n dd with decimal-head n
  ... | c , _ , eq , p = headNext isDigit (trans (toList∘fromList (decimal n)) eq) p dd

  floatNext : ∀ i f l {cs d} → isDigit d ≡ false → ¬ Next (toList (fromList (decimal i ++ '.' ∷ fixed l f)) ++ cs) d
  floatNext i f l dd with decimal-head i
  ... | c , _ , eq , p =
    headNext isDigit (trans (toList∘fromList (decimal i ++ '.' ∷ fixed l f)) (cong (_++ '.' ∷ fixed l f) eq)) p dd


ft-word : ∀ t {cs} → continues t ≡ false → Printable t → Stop isIdentContinue (chars (lt t) ++ cs)
ft-word (TWord s) () _
ft-word (TInt (+ n)) () _
ft-word (TFloat i f l) () _
ft-word (TString _) h (p-sym ())
ft-word TLParen h _ = stop refl
ft-word TRParen h _ = stop refl
ft-word TLBrace h _ = stop refl
ft-word TRBrace h _ = stop refl
ft-word TColon h _ = stop refl
ft-word TEquals h _ = stop refl
ft-word TArrow h _ = stop refl
ft-word TCaret1 h _ = stop refl
ft-word TCaret0 h _ = stop refl
ft-word TCaretW h _ = stop refl
ft-word TLambda h _ = stop refl
ft-word TComma h _ = stop refl
ft-word TSemicolon h _ = stop refl
ft-word TAt h _ = stop refl
ft-word TPipe h _ = stop refl
ft-word TDot h _ = stop refl
ft-word TPlus () _
ft-word TMinus h _ = stop refl
ft-word TStar () _
ft-word TSlash h _ = stop refl
ft-word TPercent h _ = stop refl
ft-word TAmpersand h _ = stop refl
ft-word TLt h _ = stop refl
ft-word TLe h _ = stop refl
ft-word TGt h _ = stop refl
ft-word TGe h _ = stop refl
ft-word TEqEq h _ = stop refl
ft-word TNeq () _
ft-word TBang () _
ft-word TNewline h (p-sym ())
ft-word TEOF h (p-sym ())

ft-num : ∀ t {cs} → number t ≡ false → Printable t → Stop isDigit (chars (lt t) ++ cs) × ¬ Next (chars (lt t) ++ cs) '.'
ft-num (TWord s) () _
ft-num (TInt (+ n)) () _
ft-num (TFloat i f l) () _
ft-num (TString _) h (p-sym ())
ft-num TLParen h _ = stop refl , (λ ())
ft-num TRParen h _ = stop refl , (λ ())
ft-num TLBrace h _ = stop refl , (λ ())
ft-num TRBrace h _ = stop refl , (λ ())
ft-num TColon h _ = stop refl , (λ ())
ft-num TEquals h _ = stop refl , (λ ())
ft-num TArrow h _ = stop refl , (λ ())
ft-num TCaret1 h _ = stop refl , (λ ())
ft-num TCaret0 h _ = stop refl , (λ ())
ft-num TCaretW h _ = stop refl , (λ ())
ft-num TLambda h _ = stop refl , (λ ())
ft-num TComma h _ = stop refl , (λ ())
ft-num TSemicolon h _ = stop refl , (λ ())
ft-num TAt h _ = stop refl , (λ ())
ft-num TPipe h _ = stop refl , (λ ())
ft-num TDot () _
ft-num TPlus () _
ft-num TMinus h _ = stop refl , (λ ())
ft-num TStar () _
ft-num TSlash h _ = stop refl , (λ ())
ft-num TPercent h _ = stop refl , (λ ())
ft-num TAmpersand h _ = stop refl , (λ ())
ft-num TLt h _ = stop refl , (λ ())
ft-num TLe h _ = stop refl , (λ ())
ft-num TGt h _ = stop refl , (λ ())
ft-num TGe h _ = stop refl , (λ ())
ft-num TEqEq h _ = stop refl , (λ ())
ft-num TNeq () _
ft-num TBang () _
ft-num TNewline h (p-sym ())
ft-num TEOF h (p-sym ())

ft-minus : ∀ t {cs} → (dashes t ∨ greater t) ≡ false → Printable t → ¬ Next (chars (lt t) ++ cs) '-' × ¬ Next (chars (lt t) ++ cs) '>'
ft-minus (TWord s) h (p-word eq ¬s ¬d st ps) = wordNext {s = s} eq st refl , wordNext {s = s} eq st refl
ft-minus (TInt (+ n)) h p-int = intNext n refl , intNext n refl
ft-minus (TFloat i f l) h (p-float _) = floatNext i f l refl , floatNext i f l refl
ft-minus (TString _) h (p-sym ())
ft-minus TLParen h _ = (λ ()) , (λ ())
ft-minus TRParen h _ = (λ ()) , (λ ())
ft-minus TLBrace h _ = (λ ()) , (λ ())
ft-minus TRBrace h _ = (λ ()) , (λ ())
ft-minus TColon h _ = (λ ()) , (λ ())
ft-minus TEquals h _ = (λ ()) , (λ ())
ft-minus TArrow () _
ft-minus TCaret1 h _ = (λ ()) , (λ ())
ft-minus TCaret0 h _ = (λ ()) , (λ ())
ft-minus TCaretW h _ = (λ ()) , (λ ())
ft-minus TLambda h _ = (λ ()) , (λ ())
ft-minus TComma h _ = (λ ()) , (λ ())
ft-minus TSemicolon h _ = (λ ()) , (λ ())
ft-minus TAt h _ = (λ ()) , (λ ())
ft-minus TPipe h _ = (λ ()) , (λ ())
ft-minus TDot h _ = (λ ()) , (λ ())
ft-minus TPlus h _ = (λ ()) , (λ ())
ft-minus TMinus () _
ft-minus TStar h _ = (λ ()) , (λ ())
ft-minus TSlash h _ = (λ ()) , (λ ())
ft-minus TPercent h _ = (λ ()) , (λ ())
ft-minus TAmpersand h _ = (λ ()) , (λ ())
ft-minus TLt h _ = (λ ()) , (λ ())
ft-minus TLe h _ = (λ ()) , (λ ())
ft-minus TGt () _
ft-minus TGe () _
ft-minus TEqEq h _ = (λ ()) , (λ ())
ft-minus TNeq h _ = (λ ()) , (λ ())
ft-minus TBang h _ = (λ ()) , (λ ())
ft-minus TNewline h (p-sym ())
ft-minus TEOF h (p-sym ())

ft-eq : ∀ t {cs} → equals t ≡ false → Printable t → ¬ Next (chars (lt t) ++ cs) '='
ft-eq (TWord s) h (p-word eq ¬s ¬d st ps) = wordNext {s = s} eq st refl
ft-eq (TInt (+ n)) h p-int = intNext n refl
ft-eq (TFloat i f l) h (p-float _) = floatNext i f l refl
ft-eq (TString _) h (p-sym ())
ft-eq TLParen h _ = (λ ())
ft-eq TRParen h _ = (λ ())
ft-eq TLBrace h _ = (λ ())
ft-eq TRBrace h _ = (λ ())
ft-eq TColon h _ = (λ ())
ft-eq TEquals () _
ft-eq TArrow h _ = (λ ())
ft-eq TCaret1 h _ = (λ ())
ft-eq TCaret0 h _ = (λ ())
ft-eq TCaretW h _ = (λ ())
ft-eq TLambda h _ = (λ ())
ft-eq TComma h _ = (λ ())
ft-eq TSemicolon h _ = (λ ())
ft-eq TAt h _ = (λ ())
ft-eq TPipe h _ = (λ ())
ft-eq TDot h _ = (λ ())
ft-eq TPlus h _ = (λ ())
ft-eq TMinus h _ = (λ ())
ft-eq TStar h _ = (λ ())
ft-eq TSlash h _ = (λ ())
ft-eq TPercent h _ = (λ ())
ft-eq TAmpersand h _ = (λ ())
ft-eq TLt h _ = (λ ())
ft-eq TLe h _ = (λ ())
ft-eq TGt h _ = (λ ())
ft-eq TGe h _ = (λ ())
ft-eq TEqEq () _
ft-eq TNeq h _ = (λ ())
ft-eq TBang h _ = (λ ())
ft-eq TNewline h (p-sym ())
ft-eq TEOF h (p-sym ())

ft-brace : ∀ t {cs} → dashes t ≡ false → Printable t → ¬ Next (chars (lt t) ++ cs) '-'
ft-brace (TWord s) h (p-word eq ¬s ¬d st ps) = wordNext {s = s} eq st refl
ft-brace (TInt (+ n)) h p-int = intNext n refl
ft-brace (TFloat i f l) h (p-float _) = floatNext i f l refl
ft-brace (TString _) h (p-sym ())
ft-brace TLParen h _ = (λ ())
ft-brace TRParen h _ = (λ ())
ft-brace TLBrace h _ = (λ ())
ft-brace TRBrace h _ = (λ ())
ft-brace TColon h _ = (λ ())
ft-brace TEquals h _ = (λ ())
ft-brace TArrow () _
ft-brace TCaret1 h _ = (λ ())
ft-brace TCaret0 h _ = (λ ())
ft-brace TCaretW h _ = (λ ())
ft-brace TLambda h _ = (λ ())
ft-brace TComma h _ = (λ ())
ft-brace TSemicolon h _ = (λ ())
ft-brace TAt h _ = (λ ())
ft-brace TPipe h _ = (λ ())
ft-brace TDot h _ = (λ ())
ft-brace TPlus h _ = (λ ())
ft-brace TMinus () _
ft-brace TStar h _ = (λ ())
ft-brace TSlash h _ = (λ ())
ft-brace TPercent h _ = (λ ())
ft-brace TAmpersand h _ = (λ ())
ft-brace TLt h _ = (λ ())
ft-brace TLe h _ = (λ ())
ft-brace TGt h _ = (λ ())
ft-brace TGe h _ = (λ ())
ft-brace TEqEq h _ = (λ ())
ft-brace TNeq h _ = (λ ())
ft-brace TBang h _ = (λ ())
ft-brace TNewline h (p-sym ())
ft-brace TEOF h (p-sym ())

-- | A token may follow a token it is not `apart` from.
follows-tok : ∀ u t {cs} → apart u t ≡ false → Printable t → Follows u (chars (lt t) ++ cs)
follows-tok (TWord _) t h p = ft-word t h p
follows-tok (TInt _) t h p = ft-num t h p
follows-tok (TFloat _ _ _) t h p = proj₁ (ft-num t h p)
follows-tok (TString _) t h p = tt
follows-tok TLParen t h p = tt
follows-tok TRParen t h p = tt
follows-tok TLBrace t h p = ft-brace t h p
follows-tok TRBrace t h p = tt
follows-tok TColon t h p = tt
follows-tok TEquals t h p = ft-eq t h p
follows-tok TArrow t h p = tt
follows-tok TCaret1 t h p = tt
follows-tok TCaret0 t h p = tt
follows-tok TCaretW t h p = tt
follows-tok TLambda t h p = tt
follows-tok TComma t h p = tt
follows-tok TSemicolon t h p = tt
follows-tok TAt t h p = tt
follows-tok TPipe t h p = tt
follows-tok TDot t h p = tt
follows-tok TPlus t h p = tt
follows-tok TMinus t h p = ft-minus t h p
follows-tok TStar t h p = tt
follows-tok TSlash t h p = tt
follows-tok TPercent t h p = tt
follows-tok TAmpersand t h p = tt
follows-tok TLt t h p = ft-eq t h p
follows-tok TLe t h p = tt
follows-tok TGt t h p = ft-eq t h p
follows-tok TGe t h p = tt
follows-tok TEqEq t h p = tt
follows-tok TNeq t h p = tt
follows-tok TBang t h p = ft-eq t h p
follows-tok TNewline t h p = tt
follows-tok TEOF t h p = tt

------------------------------------------------------------------------
-- Well-formed lexemes, and the tokens they lex as
------------------------------------------------------------------------

Valid : Lexeme → Set
Valid (lt t)   = Printable t
Valid lsp      = ⊤
Valid lnl      = ⊤
Valid (lind _) = ⊤
Valid (lcm c)  = LineComment c

-- The neighbours the layout writes.
data Adj : Lexeme → Lexeme → Set where
  tok-tok : ∀ {u t} → apart u t ≡ false → Adj (lt u) (lt t)
  tok-sp  : ∀ {u} → Adj (lt u) lsp
  tok-nl  : ∀ {u} → Adj (lt u) lnl
  sp-tok  : ∀ {t} → Adj lsp (lt t)
  sp-sp   : Adj lsp lsp
  sp-cm   : ∀ {c} → Adj lsp (lcm c)
  sp-nl   : Adj lsp lnl
  nl-nl   : Adj lnl lnl
  nl-ind  : ∀ {i} → Adj lnl (lind i)
  ind-tok : ∀ {i t} → Adj (lind i) (lt t)
  ind-cm  : ∀ {i c} → Adj (lind i) (lcm c)
  cm-nl   : ∀ {c} → Adj (lcm c) lnl

-- What may end the text (a comment is followed by its line end).
data Last : Lexeme → Set where
  last-tok : ∀ {t} → Last (lt t)
  last-sp  : Last lsp
  last-nl  : Last lnl
  last-ind : ∀ {i} → Last (lind i)

data WS : List Lexeme → Set where
  ws-[] : WS []
  ws-1  : ∀ {x} → Valid x → Last x → WS (x ∷ [])
  ws-∷  : ∀ {x y ys} → Valid x → Adj x y → WS (y ∷ ys) → WS (x ∷ y ∷ ys)

-- | The tokens: a line end is a `TNewline` unless an indented line follows
-- (`p`: a line end waits for what follows it).
nl? : Bool → List Token → List Token
nl? true  ts = TNewline ∷ ts
nl? false ts = ts

run : Bool → List Lexeme → List Token
run p []                  = nl? p (TEOF ∷ [])
run p (lt t ∷ xs)         = nl? p (t ∷ run false xs)
run p (lsp ∷ xs)          = run false xs
run p (lnl ∷ xs)          = nl? p (run true xs)
run p (lind zero ∷ xs)    = run p xs
run p (lind (suc _) ∷ xs) = run false xs
run p (lcm _ ∷ xs)        = nl? p (run false xs)

private
  spaces : ∀ n {cs ts} → LexesChars cs ts → LexesChars (replicate n ' ' ++ cs) ts
  spaces zero    l = l
  spaces (suc n) l = lex-space (spaces n l)

  ind-run : ∀ n xs → run false (lind n ∷ xs) ≡ run false xs
  ind-run zero    xs = refl
  ind-run (suc n) xs = refl

  -- What starts a line is not a blank.
  tok-blank : ∀ t {cs} → Printable t → ¬ Next (chars (lt t) ++ cs) ' ' × ¬ Next (chars (lt t) ++ cs) '\t'
  tok-blank (TWord s) (p-word eq ¬s ¬d st ps) = wordNext {s = s} eq st refl , wordNext {s = s} eq st refl
  tok-blank (TInt (+ n)) p-int = intNext n refl , intNext n refl
  tok-blank (TFloat i f l) (p-float _) = floatNext i f l refl , floatNext i f l refl
  tok-blank (TString _) (p-sym ())
  tok-blank TLParen _ = (λ ()) , (λ ())
  tok-blank TRParen _ = (λ ()) , (λ ())
  tok-blank TLBrace _ = (λ ()) , (λ ())
  tok-blank TRBrace _ = (λ ()) , (λ ())
  tok-blank TColon _ = (λ ()) , (λ ())
  tok-blank TEquals _ = (λ ()) , (λ ())
  tok-blank TArrow _ = (λ ()) , (λ ())
  tok-blank TCaret1 _ = (λ ()) , (λ ())
  tok-blank TCaret0 _ = (λ ()) , (λ ())
  tok-blank TCaretW _ = (λ ()) , (λ ())
  tok-blank TLambda _ = (λ ()) , (λ ())
  tok-blank TComma _ = (λ ()) , (λ ())
  tok-blank TSemicolon _ = (λ ()) , (λ ())
  tok-blank TAt _ = (λ ()) , (λ ())
  tok-blank TPipe _ = (λ ()) , (λ ())
  tok-blank TDot _ = (λ ()) , (λ ())
  tok-blank TPlus _ = (λ ()) , (λ ())
  tok-blank TMinus _ = (λ ()) , (λ ())
  tok-blank TStar _ = (λ ()) , (λ ())
  tok-blank TSlash _ = (λ ()) , (λ ())
  tok-blank TPercent _ = (λ ()) , (λ ())
  tok-blank TAmpersand _ = (λ ()) , (λ ())
  tok-blank TLt _ = (λ ()) , (λ ())
  tok-blank TLe _ = (λ ()) , (λ ())
  tok-blank TGt _ = (λ ()) , (λ ())
  tok-blank TGe _ = (λ ()) , (λ ())
  tok-blank TEqEq _ = (λ ()) , (λ ())
  tok-blank TNeq _ = (λ ()) , (λ ())
  tok-blank TBang _ = (λ ()) , (λ ())
  tok-blank TNewline (p-sym ())
  tok-blank TEOF (p-sym ())

-- | Well-formed lexemes lex as their tokens.
lexes : ∀ xs → WS xs → LexesChars (concatMap chars xs) (run false xs)
lexes []               ws-[]                 = lex-eof
lexes (lt t ∷ [])      (ws-1 v _)            = lex-token v (follows-end t) lex-eof
lexes (lsp ∷ [])       (ws-1 _ _)            = lex-space lex-eof
lexes (lnl ∷ [])       (ws-1 _ _)            = lex-nl (λ ()) (λ ()) lex-eof
lexes (lind n ∷ [])    (ws-1 _ _)            = subst (LexesChars _) (sym (ind-run n [])) (spaces n lex-eof)
lexes (lcm _ ∷ [])     (ws-1 _ ())
lexes (lt t ∷ y ∷ ys)  (ws-∷ v a w)          = lex-token v (after a w) (lexes (y ∷ ys) w)
  where
    after : ∀ {y ys} → Adj (lt t) y → WS (y ∷ ys) → Follows t (concatMap chars (y ∷ ys))
    after (tok-tok h) (ws-1 p _)   = follows-tok t _ h p
    after (tok-tok h) (ws-∷ p _ _) = follows-tok t _ h p
    after tok-sp      _            = follows-sp t
    after tok-nl      _            = follows-nl t
lexes (lsp ∷ y ∷ ys)   (ws-∷ _ _ w)          = lex-space (lexes (y ∷ ys) w)
lexes (lind n ∷ y ∷ ys) (ws-∷ _ _ w)         = subst (LexesChars _) (sym (ind-run n (y ∷ ys))) (spaces n (lexes (y ∷ ys) w))
lexes (lcm _ ∷ lnl ∷ ys) (ws-∷ (lc b) cm-nl w) = lex-comment (lineRest b) (lexes (lnl ∷ ys) w)
lexes (lnl ∷ lnl ∷ ys) (ws-∷ _ nl-nl w)      = lex-nl (λ ()) (λ ()) (lexes (lnl ∷ ys) w)
lexes (lnl ∷ lind (suc n) ∷ ys) (ws-∷ _ nl-ind w) = lex-nl-cont next (inj₁ refl) (lexes (lind (suc n) ∷ ys) w)
lexes (lnl ∷ lind zero ∷ []) (ws-∷ _ nl-ind (ws-1 _ _)) = lex-nl (λ ()) (λ ()) lex-eof
lexes (lnl ∷ lind zero ∷ lt t ∷ zs) (ws-∷ _ nl-ind (ws-∷ _ ind-tok w)) =
  lex-nl (proj₁ (tok-blank t (valid w))) (proj₂ (tok-blank t (valid w))) (lexes (lt t ∷ zs) w)
  where
    valid : ∀ {x xs} → WS (x ∷ xs) → Valid x
    valid (ws-1 v _)   = v
    valid (ws-∷ v _ _) = v
lexes (lnl ∷ lind zero ∷ lcm c ∷ zs) (ws-∷ _ nl-ind (ws-∷ _ ind-cm w)) with w
... | ws-∷ (lc b) cm-nl w′ = lex-nl (λ ()) (λ ()) (lexes (lcm c ∷ zs) w)
