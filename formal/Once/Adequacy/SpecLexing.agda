-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecLexing — the tokenizer lexes as the Spec says.
--
-- `Once.Spec.Surface.Lexing` says which token stream a text is, on its own
-- terms. The compiler's tokenizer (`Once.Parser.Lexer`) is already proved
-- against its own relation (`Once.Parser.Relation.Lexing`, `Once.Adequacy.LexerBridge`);
-- here the two relations meet: every derivation of the one gives a derivation
-- of the other, the tokens agreeing once the source offsets the compiler's
-- literal tokens carry (for diagnostics) are forgotten.
--
--   * `spec-lexes`          : `Lexes text (map forget (tokenizeString text))`, when the tokens reach `TEOF`;
--   * `spec-lexes-complete` : `Lexes text ts → map forget (tokenizeString text) ≡ ts`;
--   * `spec-lexes-unique`   : a text is one token stream.
------------------------------------------------------------------------

module Once.Adequacy.SpecLexing where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; isDigit)
open import Data.Integer using (+_)
import Data.Char as Ch
open import Data.Char.Properties using (_==_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; Dec; yes; no; does)
open import Relation.Nullary.Decidable using (isYes)

open import Once.Spec.Surface.Lexing
import Once.Parser.Token as P
import Once.Parser.Relation.Lexing as L
open import Once.Parser.Lexer
  using (HeadK; hkWS; hkNL; hkCaret; hkDash; hkLBrace; hkLt; hkGt; hkEq; hkBang;
         hkLParen; hkRParen; hkRBrace; hkColon; hkLambda; hkComma; hkSemi; hkAt;
         hkPipe; hkPlus; hkStar; hkSlash; hkPct; hkAmp; hkDot; hkStr; hkGen; headK;
         Dash3; d-comment; d-arrow; d-minus; Caret4; c-1; c-0; c-w; c-gen;
         nlIndent; isEqHead; isDashHead; dashClass; caretClass; drop1; adv;
         collectDigitsB; collectIdentB; collectFracB; frac-dot; frac-digit;
         collectStringB; str-char; str-cons; str-esc; str-esc′; escChar;
         skipLineB; skip-nl; skipBlockB; skipBlockB-WF; tokenizeString)
open import Once.Adequacy.LexerBridge using (lexer-sound; lexer-complete)

------------------------------------------------------------------------
-- Tokens: the compiler's, with the literals' source offsets forgotten
------------------------------------------------------------------------

forget : P.Token → Token
forget (P.TWord s)         = TWord s
forget (P.TInt i _)        = TInt i
forget (P.TFloat a f n _)  = TFloat a f n
forget (P.TString s)       = TString s
forget P.TLParen = TLParen
forget P.TRParen = TRParen
forget P.TLBrace = TLBrace
forget P.TRBrace = TRBrace
forget P.TColon = TColon
forget P.TEquals = TEquals
forget P.TArrow = TArrow
forget P.TCaret1 = TCaret1
forget P.TCaret0 = TCaret0
forget P.TCaretW = TCaretW
forget P.TLambda = TLambda
forget P.TComma = TComma
forget P.TSemicolon = TSemicolon
forget P.TAt = TAt
forget P.TPipe = TPipe
forget P.TDot = TDot
forget P.TPlus = TPlus
forget P.TMinus = TMinus
forget P.TStar = TStar
forget P.TSlash = TSlash
forget P.TPercent = TPercent
forget P.TAmpersand = TAmpersand
forget P.TLt = TLt
forget P.TLe = TLe
forget P.TGt = TGt
forget P.TGe = TGe
forget P.TEqEq = TEqEq
forget P.TNeq = TNeq
forget P.TBang = TBang
forget P.TNewline = TNewline
forget P.TEOF = TEOF

------------------------------------------------------------------------
-- Small facts
------------------------------------------------------------------------

private
  t≢f : true ≢ false
  t≢f ()

  nothing≢just : ∀ {A : Set} {x : A} → nothing ≢ just x
  nothing≢just ()

  next-inv : ∀ {c t x} → Next (c ∷ t) x → c ≡ x
  next-inv next = refl

  isYes-no : ∀ {A : Set} (d : Dec A) → ¬ A → isYes d ≡ false
  isYes-no (yes a) n = ⊥-elim (n a)
  isYes-no (no _)  n = refl

  isYes-yes : ∀ {A : Set} (d : Dec A) → A → isYes d ≡ true
  isYes-yes (yes _) a = refl
  isYes-yes (no n)  a = ⊥-elim (n a)

  ==-refl : ∀ c → (c == c) ≡ true
  ==-refl c = isYes-yes (c Ch.≟ c) refl

  ∧-yes′ : ∀ {c₁ c₂ x y : Char} (d₁ : Dec (c₁ ≡ x)) (d₂ : Dec (c₂ ≡ y)) → isYes d₁ ∧ isYes d₂ ≡ true → c₁ ≡ x × c₂ ≡ y
  ∧-yes′ (yes p) (yes q) _ = p , q
  ∧-yes′ (yes _) (no _) ()
  ∧-yes′ (no _)  _      ()

  ∧-yes : ∀ {c₁ c₂ x y} → (c₁ == x) ∧ (c₂ == y) ≡ true → c₁ ≡ x × c₂ ≡ y
  ∧-yes {c₁} {c₂} {x} {y} e = ∧-yes′ (c₁ Ch.≟ x) (c₂ Ch.≟ y) e

  ∧-no : ∀ {c₁ c₂ x y} → (c₁ == x) ∧ (c₂ == y) ≡ false → ¬ (c₁ ≡ x × c₂ ≡ y)
  ∧-no {c₁} {c₂} e (refl , refl) = t≢f (trans (sym (cong₂ _∧_ (==-refl c₁) (==-refl c₂))) e)

------------------------------------------------------------------------
-- The head character: `headK` read back as the character it saw
------------------------------------------------------------------------

data HeadView : Char → HeadK → Set where
  hv-space : HeadView ' ' hkWS
  hv-tab : HeadView '\t' hkWS
  hv-cr : HeadView '\r' hkWS
  hv-nl : HeadView '\n' hkNL
  hv-caret : HeadView '^' hkCaret
  hv-dash : HeadView '-' hkDash
  hv-lbrace : HeadView '{' hkLBrace
  hv-lt : HeadView '<' hkLt
  hv-gt : HeadView '>' hkGt
  hv-eq : HeadView '=' hkEq
  hv-bang : HeadView '!' hkBang
  hv-lparen : HeadView '(' hkLParen
  hv-rparen : HeadView ')' hkRParen
  hv-rbrace : HeadView '}' hkRBrace
  hv-colon : HeadView ':' hkColon
  hv-lambda : HeadView '\\' hkLambda
  hv-comma : HeadView ',' hkComma
  hv-semi : HeadView ';' hkSemi
  hv-at : HeadView '@' hkAt
  hv-pipe : HeadView '|' hkPipe
  hv-plus : HeadView '+' hkPlus
  hv-star : HeadView '*' hkStar
  hv-slash : HeadView '/' hkSlash
  hv-pct : HeadView '%' hkPct
  hv-amp : HeadView '&' hkAmp
  hv-dot : HeadView '.' hkDot
  hv-quote : HeadView '"' hkStr
  hv-gen : ∀ {c} → ¬ Special c → HeadView c hkGen

-- `headK` is a chain of tests, one character each.
private
  pick : Char → List (Char × HeadK) → HeadK
  pick c []             = hkGen
  pick c ((x , k) ∷ t) = if does (c Ch.≟ x) then k else pick c t

table′ : List (Char × HeadK)
table′ =
  ('\n' , hkNL)
  ∷ ('^' , hkCaret)
  ∷ ('-' , hkDash)
  ∷ ('{' , hkLBrace)
  ∷ ('<' , hkLt)
  ∷ ('>' , hkGt)
  ∷ ('=' , hkEq)
  ∷ ('!' , hkBang)
  ∷ ('(' , hkLParen)
  ∷ (')' , hkRParen)
  ∷ ('}' , hkRBrace)
  ∷ (':' , hkColon)
  ∷ ('\\' , hkLambda)
  ∷ (',' , hkComma)
  ∷ (';' , hkSemi)
  ∷ ('@' , hkAt)
  ∷ ('|' , hkPipe)
  ∷ ('+' , hkPlus)
  ∷ ('*' , hkStar)
  ∷ ('/' , hkSlash)
  ∷ ('%' , hkPct)
  ∷ ('&' , hkAmp)
  ∷ ('.' , hkDot)
  ∷ ('"' , hkStr) ∷ []

table : List (Char × HeadK)
table = (' ' , hkWS) ∷ ('\t' , hkWS) ∷ ('\r' , hkWS) ∷ table′

private
  ∨-if : ∀ a b d (x y : HeadK) → (if a ∨ b ∨ d then x else y) ≡ (if a then x else if b then x else if d then x else y)
  ∨-if true  _     _     x y = refl
  ∨-if false true  _     x y = refl
  ∨-if false false true  x y = refl
  ∨-if false false false x y = refl

  headK≡pick : ∀ c → headK c ≡ pick c table
  headK≡pick c = ∨-if (does (c Ch.≟ ' ')) (does (c Ch.≟ '\t')) (does (c Ch.≟ '\r')) hkWS (pick c table′)

data PickView (c : Char) : List (Char × HeadK) → HeadK → Set where
  pv-here  : ∀ {k t} → PickView c ((c , k) ∷ t) k
  pv-there : ∀ {x k t r} → c ≢ x → PickView c t r → PickView c ((x , k) ∷ t) r
  pv-none  : PickView c [] hkGen

private
  pv-step : ∀ c x k t {r} (d : Dec (c ≡ x)) → PickView c t r → PickView c ((x , k) ∷ t) (if does d then k else r)
  pv-step c x k t (yes refl) v = pv-here
  pv-step c x k t (no ne)    v = pv-there ne v

  pick-view : ∀ c t → PickView c t (pick c t)
  pick-view c []             = pv-none
  pick-view c ((x , k) ∷ t) = pv-step c x k t (c Ch.≟ x) (pick-view c t)

not-special : ∀ {c} → c ≢ ' ' → c ≢ '\t' → c ≢ '\r' → c ≢ '\n' → c ≢ '^' → c ≢ '-' → c ≢ '{' → c ≢ '<' → c ≢ '>' → c ≢ '=' → c ≢ '!' → c ≢ '(' → c ≢ ')' → c ≢ '}' → c ≢ ':' → c ≢ '\\' → c ≢ ',' → c ≢ ';' → c ≢ '@' → c ≢ '|' → c ≢ '+' → c ≢ '*' → c ≢ '/' → c ≢ '%' → c ≢ '&' → c ≢ '.' → c ≢ '"' → ¬ Special c
not-special n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-space = n refl
not-special _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-tab = n refl
not-special _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-cr = n refl
not-special _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-nl = n refl
not-special _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-caret = n refl
not-special _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-dash = n refl
not-special _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-lbrace = n refl
not-special _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-lt = n refl
not-special _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-gt = n refl
not-special _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-eq = n refl
not-special _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-bang = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-lparen = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp-rparen = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ _ sp-rbrace = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ sp-colon = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ sp-backslash = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ sp-comma = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ sp-semi = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ sp-at = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ sp-pipe = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ _ sp-plus = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ sp-star = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ sp-slash = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ _ sp-pct = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ _ sp-amp = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ sp-dot = n refl
not-special _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n sp-quote = n refl

toHead : ∀ {c k} → PickView c table k → HeadView c k
toHead (pv-here) = hv-space
toHead (pv-there _ (pv-here)) = hv-tab
toHead (pv-there _ (pv-there _ (pv-here))) = hv-cr
toHead (pv-there _ (pv-there _ (pv-there _ (pv-here)))) = hv-nl
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))) = hv-caret
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))) = hv-dash
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))) = hv-lbrace
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))) = hv-lt
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))) = hv-gt
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))) = hv-eq
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))) = hv-bang
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))) = hv-lparen
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))) = hv-rparen
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))))) = hv-rbrace
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))))) = hv-colon
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))))))) = hv-lambda
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))))))) = hv-comma
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))))))))) = hv-semi
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))))))))) = hv-at
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))))))))))) = hv-pipe
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))))))))))) = hv-plus
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))))))))))))) = hv-star
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))))))))))))) = hv-slash
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))))))))))))))) = hv-pct
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))))))))))))))) = hv-amp
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here)))))))))))))))))))))))))) = hv-dot
toHead (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-there _ (pv-here))))))))))))))))))))))))))) = hv-quote
toHead (pv-there n0 (pv-there n1 (pv-there n2 (pv-there n3 (pv-there n4 (pv-there n5 (pv-there n6 (pv-there n7 (pv-there n8 (pv-there n9 (pv-there n10 (pv-there n11 (pv-there n12 (pv-there n13 (pv-there n14 (pv-there n15 (pv-there n16 (pv-there n17 (pv-there n18 (pv-there n19 (pv-there n20 (pv-there n21 (pv-there n22 (pv-there n23 (pv-there n24 (pv-there n25 (pv-there n26 (pv-none)))))))))))))))))))))))))))) =
  hv-gen (not-special n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26)

head-view : ∀ c → HeadView c (headK c)
head-view c = toHead (subst (PickView c table) (sym (headK≡pick c)) (pick-view c table))

hview : ∀ {c k} → headK c ≡ k → HeadView c k
hview {c} e = subst (HeadView c) e (head-view c)

dns : ∀ {c} → Special c → isDigit c ≡ true → ⊥
dns sp-space ()
dns sp-tab ()
dns sp-cr ()
dns sp-nl ()
dns sp-caret ()
dns sp-dash ()
dns sp-lbrace ()
dns sp-lt ()
dns sp-gt ()
dns sp-eq ()
dns sp-bang ()
dns sp-lparen ()
dns sp-rparen ()
dns sp-rbrace ()
dns sp-colon ()
dns sp-backslash ()
dns sp-comma ()
dns sp-semi ()
dns sp-at ()
dns sp-pipe ()
dns sp-plus ()
dns sp-star ()
dns sp-slash ()
dns sp-pct ()
dns sp-amp ()
dns sp-dot ()
dns sp-quote ()

hv-gen-eq : ∀ {c k} → HeadView c k → ¬ Special c → k ≡ hkGen
hv-gen-eq hv-space ns = ⊥-elim (ns sp-space)
hv-gen-eq hv-tab ns = ⊥-elim (ns sp-tab)
hv-gen-eq hv-cr ns = ⊥-elim (ns sp-cr)
hv-gen-eq hv-nl ns = ⊥-elim (ns sp-nl)
hv-gen-eq hv-caret ns = ⊥-elim (ns sp-caret)
hv-gen-eq hv-dash ns = ⊥-elim (ns sp-dash)
hv-gen-eq hv-lbrace ns = ⊥-elim (ns sp-lbrace)
hv-gen-eq hv-lt ns = ⊥-elim (ns sp-lt)
hv-gen-eq hv-gt ns = ⊥-elim (ns sp-gt)
hv-gen-eq hv-eq ns = ⊥-elim (ns sp-eq)
hv-gen-eq hv-bang ns = ⊥-elim (ns sp-bang)
hv-gen-eq hv-lparen ns = ⊥-elim (ns sp-lparen)
hv-gen-eq hv-rparen ns = ⊥-elim (ns sp-rparen)
hv-gen-eq hv-rbrace ns = ⊥-elim (ns sp-rbrace)
hv-gen-eq hv-colon ns = ⊥-elim (ns sp-colon)
hv-gen-eq hv-lambda ns = ⊥-elim (ns sp-backslash)
hv-gen-eq hv-comma ns = ⊥-elim (ns sp-comma)
hv-gen-eq hv-semi ns = ⊥-elim (ns sp-semi)
hv-gen-eq hv-at ns = ⊥-elim (ns sp-at)
hv-gen-eq hv-pipe ns = ⊥-elim (ns sp-pipe)
hv-gen-eq hv-plus ns = ⊥-elim (ns sp-plus)
hv-gen-eq hv-star ns = ⊥-elim (ns sp-star)
hv-gen-eq hv-slash ns = ⊥-elim (ns sp-slash)
hv-gen-eq hv-pct ns = ⊥-elim (ns sp-pct)
hv-gen-eq hv-amp ns = ⊥-elim (ns sp-amp)
hv-gen-eq hv-dot ns = ⊥-elim (ns sp-dot)
hv-gen-eq hv-quote ns = ⊥-elim (ns sp-quote)
hv-gen-eq (hv-gen _) _ = refl

gen-head : ∀ {c} → ¬ Special c → headK c ≡ hkGen
gen-head {c} ns = hv-gen-eq (head-view c) ns

------------------------------------------------------------------------
-- The second character: the compiler's classifiers read back
------------------------------------------------------------------------

data NLView (cs : List Char) : Bool → Set where
  nl-ind : ∀ {c} → Next cs c → c ≡ ' ' ⊎ c ≡ '\t' → NLView cs true
  nl-not : ¬ Next cs ' ' → ¬ Next cs '\t' → NLView cs false

private
  nl-step : ∀ c t (d₁ : Dec (c ≡ ' ')) (d₂ : Dec (c ≡ '\t')) → NLView (c ∷ t) (does d₁ ∨ does d₂)
  nl-step c t (yes p) d₂      = nl-ind next (inj₁ p)
  nl-step c t (no n₁) (yes p) = nl-ind next (inj₂ p)
  nl-step c t (no n₁) (no n₂) = nl-not (λ x → n₁ (next-inv x)) (λ x → n₂ (next-inv x))

nl-view : ∀ cs → NLView cs (nlIndent cs)
nl-view []      = nl-not (λ ()) (λ ())
nl-view (c ∷ t) = nl-step c t (c Ch.≟ ' ') (c Ch.≟ '\t')

nl-true : ∀ {cs b c} → NLView cs b → Next cs c → c ≡ ' ' ⊎ c ≡ '\t' → b ≡ true
nl-true (nl-ind _ _) _  _           = refl
nl-true (nl-not a _) nx (inj₁ refl) = ⊥-elim (a nx)
nl-true (nl-not _ t) nx (inj₂ refl) = ⊥-elim (t nx)

nl-false : ∀ {cs b} → NLView cs b → ¬ Next cs ' ' → ¬ Next cs '\t' → b ≡ false
nl-false (nl-ind nx (inj₁ refl)) a _ = ⊥-elim (a nx)
nl-false (nl-ind nx (inj₂ refl)) _ t = ⊥-elim (t nx)
nl-false (nl-not _ _)            _ _ = refl

data CaretView : List Char → Caret4 → Set where
  cv-1   : ∀ {t} → CaretView ('1' ∷ t) c-1
  cv-0   : ∀ {t} → CaretView ('0' ∷ t) c-0
  cv-w   : ∀ {t} → CaretView ('w' ∷ t) c-w
  cv-gen : ∀ {cs} → ¬ Next cs '1' → ¬ Next cs '0' → ¬ Next cs 'w' → CaretView cs c-gen

private
  cv-step : ∀ c t (d₁ : Dec (c ≡ '1')) (d₀ : Dec (c ≡ '0')) (dw : Dec (c ≡ 'w'))
          → CaretView (c ∷ t) (if does d₁ then c-1 else (if does d₀ then c-0 else (if does dw then c-w else c-gen)))
  cv-step c t (yes refl) _          _          = cv-1
  cv-step c t (no _)     (yes refl) _          = cv-0
  cv-step c t (no _)     (no _)     (yes refl) = cv-w
  cv-step c t (no n₁)    (no n₀)    (no nw)    =
    cv-gen (λ x → n₁ (next-inv x)) (λ x → n₀ (next-inv x)) (λ x → nw (next-inv x))

caret-view : ∀ cs → CaretView cs (caretClass cs)
caret-view []      = cv-gen (λ ()) (λ ()) (λ ())
caret-view (c ∷ t) = cv-step c t (c Ch.≟ '1') (c Ch.≟ '0') (c Ch.≟ 'w')

cview : ∀ {cs k} → caretClass cs ≡ k → CaretView cs k
cview {cs} e = subst (CaretView cs) e (caret-view cs)

data DashView : List Char → Dash3 → Set where
  dv-comment : ∀ {t} → DashView ('-' ∷ t) d-comment
  dv-arrow   : ∀ {t} → DashView ('>' ∷ t) d-arrow
  dv-minus   : ∀ {cs} → ¬ Next cs '-' → ¬ Next cs '>' → DashView cs d-minus

private
  dv-step : ∀ c t (d₁ : Dec (c ≡ '-')) (d₂ : Dec (c ≡ '>'))
          → DashView (c ∷ t) (if does d₁ then d-comment else (if does d₂ then d-arrow else d-minus))
  dv-step c t (yes refl) _          = dv-comment
  dv-step c t (no _)     (yes refl) = dv-arrow
  dv-step c t (no n₁)    (no n₂)    = dv-minus (λ x → n₁ (next-inv x)) (λ x → n₂ (next-inv x))

dash-view : ∀ cs → DashView cs (dashClass cs)
dash-view []      = dv-minus (λ ()) (λ ())
dash-view (c ∷ t) = dv-step c t (c Ch.≟ '-') (c Ch.≟ '>')

dview : ∀ {cs k} → dashClass cs ≡ k → DashView cs k
dview {cs} e = subst (DashView cs) e (dash-view cs)

dash-minus : ∀ {cs k} → DashView cs k → ¬ Next cs '-' → ¬ Next cs '>' → k ≡ d-minus
dash-minus dv-comment a _ = ⊥-elim (a next)
dash-minus dv-arrow   _ b = ⊥-elim (b next)
dash-minus (dv-minus _ _) _ _ = refl

-- Whether the next character is `x`.
data HeadIs (x : Char) : List Char → Bool → Set where
  hi-yes : ∀ {t} → HeadIs x (x ∷ t) true
  hi-no  : ∀ {cs} → ¬ Next cs x → HeadIs x cs false

private
  hi-step : ∀ x c t (d : Dec (c ≡ x)) → HeadIs x (c ∷ t) (does d)
  hi-step x c t (yes refl) = hi-yes
  hi-step x c t (no n)     = hi-no (λ e → n (next-inv e))

eq-view : ∀ cs → HeadIs '=' cs (isEqHead cs)
eq-view []      = hi-no (λ ())
eq-view (c ∷ t) = hi-step '=' c t (c Ch.≟ '=')

eqview : ∀ {cs b} → isEqHead cs ≡ b → HeadIs '=' cs b
eqview {cs} e = subst (HeadIs '=' cs) e (eq-view cs)

dhead-view : ∀ cs → HeadIs '-' cs (isDashHead cs)
dhead-view []      = hi-no (λ ())
dhead-view (c ∷ t) = hi-step '-' c t (c Ch.≟ '-')

dheadview : ∀ {cs b} → isDashHead cs ≡ b → HeadIs '-' cs b
dheadview {cs} e = subst (HeadIs '-' cs) e (dhead-view cs)

head-false : ∀ {x cs b} → HeadIs x cs b → ¬ Next cs x → b ≡ false
head-false hi-yes     n = ⊥-elim (n next)
head-false (hi-no _)  n = refl

------------------------------------------------------------------------
-- The pieces of a token: each scanner meets its Spec relation
------------------------------------------------------------------------

-- Digits.
digits-sound : ∀ cs → Digits cs (proj₁ (collectDigitsB cs)) (proj₁ (proj₂ (collectDigitsB cs)))
private
  dg-step : ∀ c cs b → isDigit c ≡ b → Digits (c ∷ cs) (proj₁ (collectDigitsB (c ∷ cs))) (proj₁ (proj₂ (collectDigitsB (c ∷ cs))))
  dg-step c cs true  e rewrite e = dg-more e (digits-sound cs)
  dg-step c cs false e rewrite e = dg-stop e
digits-sound []       = dg-end
digits-sound (c ∷ cs) = dg-step c cs (isDigit c) refl

digits-det : ∀ {cs ds r ds′ r′} → Digits cs ds r → Digits cs ds′ r′ → ds ≡ ds′ × r ≡ r′
digits-det dg-end        dg-end         = refl , refl
digits-det (dg-stop _)   (dg-stop _)    = refl , refl
digits-det (dg-more _ a) (dg-more _ b)  = cong (_ ∷_) (proj₁ (digits-det a b)) , proj₂ (digits-det a b)
digits-det (dg-stop e)   (dg-more e′ _) = ⊥-elim (t≢f (trans (sym e′) e))
digits-det (dg-more e _) (dg-stop e′)   = ⊥-elim (t≢f (trans (sym e) e′))

digits-eq : ∀ {cs ds r} → Digits cs ds r → proj₁ (collectDigitsB cs) ≡ ds × proj₁ (proj₂ (collectDigitsB cs)) ≡ r
digits-eq {cs} d = digits-det (digits-sound cs) d

-- Identifier characters.
ident-sound : ∀ cs → IdentRest cs (proj₁ (collectIdentB cs)) (proj₁ (proj₂ (collectIdentB cs)))
private
  id-step : ∀ c cs b → isIdentContinue c ≡ b → IdentRest (c ∷ cs) (proj₁ (collectIdentB (c ∷ cs))) (proj₁ (proj₂ (collectIdentB (c ∷ cs))))
  id-step c cs true  e rewrite e = id-more e (ident-sound cs)
  id-step c cs false e rewrite e = id-stop e
ident-sound []       = id-end
ident-sound (c ∷ cs) = id-step c cs (isIdentContinue c) refl

ident-det : ∀ {cs i r i′ r′} → IdentRest cs i r → IdentRest cs i′ r′ → i ≡ i′ × r ≡ r′
ident-det id-end        id-end         = refl , refl
ident-det (id-stop _)   (id-stop _)    = refl , refl
ident-det (id-more _ a) (id-more _ b)  = cong (_ ∷_) (proj₁ (ident-det a b)) , proj₂ (ident-det a b)
ident-det (id-stop e)   (id-more e′ _) = ⊥-elim (t≢f (trans (sym e′) e))
ident-det (id-more e _) (id-stop e′)   = ⊥-elim (t≢f (trans (sym e) e′))

ident-eq : ∀ {cs i r} → IdentRest cs i r → proj₁ (collectIdentB cs) ≡ i × proj₁ (proj₂ (collectIdentB cs)) ≡ r
ident-eq {cs} d = ident-det (ident-sound cs) d

-- A fraction.
private
  fs-digit : ∀ {c cs f r′ b} (x : Bool) → isDigit c ≡ x → frac-digit x c cs ≡ just (f , r′ , b) → Fraction ('.' ∷ c ∷ cs) f r′
  fs-digit {cs = cs} true ed refl = fraction ed (digits-sound cs)
  fs-digit false ed ()

  fs-dot : ∀ p cs (d : Dec (p ≡ '.')) {f r′ b} → frac-dot (isYes d) cs ≡ just (f , r′ , b) → Fraction (p ∷ cs) f r′
  fs-dot p []       (yes refl) ()
  fs-dot p (c ∷ cs) (yes refl) e = fs-digit (isDigit c) refl e
  fs-dot p cs       (no _)     ()

frac-sound : ∀ r {f r′ b} → collectFracB r ≡ just (f , r′ , b) → Fraction r f r′
frac-sound []       ()
frac-sound (p ∷ cs) e = fs-dot p cs (p Ch.≟ '.') e

private
  fj : ∀ {d cs ds r} → isDigit d ≡ true → proj₁ (collectDigitsB cs) ≡ ds → proj₁ (proj₂ (collectDigitsB cs)) ≡ r
     → Σ[ b ∈ length r < length ('.' ∷ d ∷ cs) ] collectFracB ('.' ∷ d ∷ cs) ≡ just (d ∷ ds , r , b)
  fj ed refl refl rewrite ed = _ , refl

frac-just : ∀ {r f r′} → Fraction r f r′ → Σ[ b ∈ length r′ < length r ] collectFracB r ≡ just (f , r′ , b)
frac-just (fraction ed ds) = fj ed (proj₁ (digits-eq ds)) (proj₂ (digits-eq ds))

frac-none : ∀ {r f r′} → collectFracB r ≡ nothing → ¬ Fraction r f r′
frac-none e fr = nothing≢just (trans (sym e) (proj₂ (frac-just fr)))

private
  fn : ∀ r → ¬ (∃[ f ] ∃[ r′ ] Fraction r f r′) → (m : Maybe (Σ[ f ∈ List Char ] Σ[ rest ∈ List Char ] length rest < length r))
     → collectFracB r ≡ m → collectFracB r ≡ nothing
  fn r n (just (f , r′ , b)) e = ⊥-elim (n (f , r′ , frac-sound r e))
  fn r n nothing             e = e

frac-nothing : ∀ {r} → ¬ (∃[ f ] ∃[ r′ ] Fraction r f r′) → collectFracB r ≡ nothing
frac-nothing {r} n = fn r n (collectFracB r) refl

-- A string literal's body.
data EscView (e : Char) : Maybe Char → Set where
  ev-yes : ∀ {x} → Escape e x → EscView e (just x)
  ev-no  : (∀ x → ¬ Escape e x) → e ≢ '"' → e ≢ '\\' → EscView e nothing

private
  no-escape : ∀ {e x} → e ≢ 'n' → e ≢ 't' → e ≢ 'r' → e ≢ '\\' → e ≢ '"' → ¬ Escape e x
  no-escape n _ _ _ _ esc-n  = n refl
  no-escape _ t _ _ _ esc-t  = t refl
  no-escape _ _ r _ _ esc-r  = r refl
  no-escape _ _ _ b _ esc-bs = b refl
  no-escape _ _ _ _ q esc-q  = q refl

  ev-step : ∀ e (dn : Dec (e ≡ 'n')) (dt : Dec (e ≡ 't')) (dr : Dec (e ≡ 'r')) (db : Dec (e ≡ '\\')) (dq : Dec (e ≡ '"'))
          → EscView e (if isYes dn then just '\n' else if isYes dt then just '\t' else if isYes dr then just '\r'
                       else if isYes db then just '\\' else if isYes dq then just '"' else nothing)
  ev-step e (yes refl) _ _ _ _ = ev-yes esc-n
  ev-step e (no _) (yes refl) _ _ _ = ev-yes esc-t
  ev-step e (no _) (no _) (yes refl) _ _ = ev-yes esc-r
  ev-step e (no _) (no _) (no _) (yes refl) _ = ev-yes esc-bs
  ev-step e (no _) (no _) (no _) (no _) (yes refl) = ev-yes esc-q
  ev-step e (no nn) (no nt) (no nr) (no nb) (no nq) = ev-no (λ x → no-escape nn nt nr nb nq) nq nb

esc-view : ∀ e → EscView e (escChar e)
esc-view e = ev-step e (e Ch.≟ 'n') (e Ch.≟ 't') (e Ch.≟ 'r') (e Ch.≟ '\\') (e Ch.≟ '"')

escChar-sound : ∀ {e x} → Escape e x → escChar e ≡ just x
escChar-sound esc-n  = refl
escChar-sound esc-t  = refl
escChar-sound esc-r  = refl
escChar-sound esc-bs = refl
escChar-sound esc-q  = refl

private
  en : ∀ {e} → (∀ x → ¬ Escape e x) → (m : Maybe Char) → EscView e m → m ≡ nothing
  en n _ (ev-yes esc)  = ⊥-elim (n _ esc)
  en n _ (ev-no _ _ _) = refl

esc-nothing : ∀ {e} → (∀ x → ¬ Escape e x) → escChar e ≡ nothing
esc-nothing {e} n = en n (escChar e) (esc-view e)

private
  Scan : ℕ → Set
  Scan n = Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ] length rest < n)

  cons-inv : ∀ {n} (p : List Char) (m : Scan n) {s r b} → str-cons p m ≡ just (s , r , b)
           → Σ[ s′ ∈ List Char ] Σ[ b′ ∈ length r < n ] (m ≡ just (s′ , r , b′) × s ≡ p ++ s′)
  cons-inv p (just (s′ , r , b′)) refl = s′ , b′ , refl , refl
  cons-inv p nothing ()

  cons-just : ∀ {n} {p : List Char} {m : Scan n} {s r b} → m ≡ just (s , r , b)
            → Σ[ b′ ∈ length r < suc n ] str-cons p m ≡ just (p ++ s , r , b′)
  cons-just refl = _ , refl

string-sound : ∀ cs {s r b} → collectStringB cs ≡ just (s , r , b) → StringBody cs s r
private
  ss-plain : ∀ {c} cs {s r} → c ≢ '"' → c ≢ '\\'
           → Σ[ s′ ∈ List Char ] Σ[ b′ ∈ length r < length cs ] (collectStringB cs ≡ just (s′ , r , b′) × s ≡ c ∷ s′)
           → StringBody (c ∷ cs) s r
  ss-plain cs nq nk (s′ , b′ , e , refl) = sb-char nq (λ p → nk (proj₁ p)) (string-sound cs e)

  esc-yes₂ : ∀ {e x} cs {s r} → Escape e x
           → Σ[ s′ ∈ List Char ] Σ[ b′ ∈ length r < length cs ] (collectStringB cs ≡ just (s′ , r , b′) × s ≡ x ∷ s′)
           → StringBody ('\\' ∷ e ∷ cs) s r
  esc-yes₂ cs esc (s′ , b′ , e , refl) = sb-esc esc (string-sound cs e)

  esc-yes₁ : ∀ {e x} cs {s r} → Escape e x
           → Σ[ s′ ∈ List Char ] Σ[ b′ ∈ length r < suc (length cs) ]
               (str-cons (x ∷ []) (collectStringB cs) ≡ just (s′ , r , b′) × s ≡ s′)
           → StringBody ('\\' ∷ e ∷ cs) s r
  esc-yes₁ cs esc (s′ , b′ , e , refl) = esc-yes₂ cs esc (cons-inv _ (collectStringB cs) e)

  esc-no₂ : ∀ {e} cs {s r} → (∀ x → ¬ Escape e x) → e ≢ '"' → e ≢ '\\'
          → Σ[ s′ ∈ List Char ] Σ[ b′ ∈ length r < length cs ] (collectStringB cs ≡ just (s′ , r , b′) × s ≡ e ∷ s′)
          → StringBody (e ∷ cs) s r
  esc-no₂ cs ne nq nb (s′ , b′ , e , refl) = sb-char nq (λ p → nb (proj₁ p)) (string-sound cs e)

  esc-no₁ : ∀ {e} cs {s r} → (∀ x → ¬ Escape e x) → e ≢ '"' → e ≢ '\\'
          → Σ[ s′ ∈ List Char ] Σ[ b′ ∈ length r < suc (length cs) ]
              (str-cons (e ∷ []) (collectStringB cs) ≡ just (s′ , r , b′) × s ≡ '\\' ∷ s′)
          → StringBody ('\\' ∷ e ∷ cs) s r
  esc-no₁ cs ne nq nb (s′ , b′ , e , refl) =
    sb-char (λ ()) (λ { (_ , e′ , x , nx , esc) → ne x (subst (λ z → Escape z x) (sym (next-inv nx)) esc) })
      (esc-no₂ cs ne nq nb (cons-inv _ (collectStringB cs) e))

  ss-esc′ : ∀ e cs (m : Maybe Char) → EscView e m → ∀ {s r b} → str-esc′ m e cs ≡ just (s , r , b) → StringBody ('\\' ∷ e ∷ cs) s r
  ss-esc′ e cs (just x) (ev-yes esc)     eq = esc-yes₁ cs esc (cons-inv [] _ eq)
  ss-esc′ e cs nothing  (ev-no ne nq nb) eq = esc-no₁ cs ne nq nb (cons-inv _ _ eq)

  ss-esc : ∀ cs {s r b} → str-esc cs ≡ just (s , r , b) → StringBody ('\\' ∷ cs) s r
  ss-esc []       ()
  ss-esc (e ∷ cs) eq = ss-esc′ e cs (escChar e) (esc-view e) eq

  ss-char : ∀ c cs (q : Dec (c ≡ '"')) (k : Dec (c ≡ '\\')) {s r b}
          → str-char (isYes q) (isYes k) c cs ≡ just (s , r , b) → StringBody (c ∷ cs) s r
  ss-char c cs (yes refl) k        refl = sb-close
  ss-char c cs (no nq)    (yes refl) e  = ss-esc cs e
  ss-char c cs (no nq)    (no nk)    e  = ss-plain cs nq nk (cons-inv _ (collectStringB cs) e)

string-sound []       ()
string-sound (c ∷ cs) e = ss-char c cs (c Ch.≟ '"') (c Ch.≟ '\\') e

string-complete : ∀ {cs s r} → StringBody cs s r → Σ[ b ∈ length r < length cs ] collectStringB cs ≡ just (s , r , b)
private
  sc-esc : ∀ {e x} cs {s r} → escChar e ≡ just x → Σ[ b ∈ length r < length cs ] collectStringB cs ≡ just (s , r , b)
         → Σ[ b ∈ length r < suc (suc (length cs)) ] str-esc′ (escChar e) e cs ≡ just (x ∷ s , r , b)
  sc-esc cs ee (b , ih) rewrite ee = cons-just (proj₂ (cons-just {p = _ ∷ []} ih))

  sc-char : ∀ c {cs s r} (d : Dec (c ≡ '\\')) → c ≢ '"' → ¬ (c ≡ '\\' × ∃[ e ] ∃[ x ] (Next cs e × Escape e x))
          → StringBody cs s r → Σ[ b ∈ length r < suc (length cs) ] collectStringB (c ∷ cs) ≡ just (c ∷ s , r , b)
  sc-char c (no nk) nq nesc body
    rewrite isYes-no (c Ch.≟ '"') nq | isYes-no (c Ch.≟ '\\') nk = cons-just (proj₂ (string-complete body))
  sc-char c (yes refl) nq nesc sb-close = ⊥-elim (nesc (refl , '"' , '"' , next , esc-q))
  sc-char c (yes refl) nq nesc (sb-esc _ _) = ⊥-elim (nesc (refl , '\\' , '\\' , next , esc-bs))
  sc-char c (yes refl) nq nesc (sb-char {c = e} {cs = t} _ _ body′)
    rewrite esc-nothing {e} (λ x esc → nesc (refl , e , x , next , esc)) =
      cons-just (proj₂ (cons-just {p = e ∷ []} (proj₂ (string-complete body′))))

string-complete sb-close = _ , refl
string-complete (sb-esc {e = e} {cs = cs} esc body) = sc-esc {e = e} cs (escChar-sound esc) (string-complete body)
string-complete (sb-char {c = c} nq nesc body) = sc-char c (c Ch.≟ '\\') nq nesc body

string-none : ∀ {cs s r} → collectStringB cs ≡ nothing → ¬ StringBody cs s r
string-none e body = nothing≢just (trans (sym e) (proj₂ (string-complete body)))

private
  sn : ∀ cs → ¬ (∃[ s ] ∃[ r ] StringBody cs s r) → (m : Scan (length cs)) → collectStringB cs ≡ m → collectStringB cs ≡ nothing
  sn cs n (just (s , r , b)) e = ⊥-elim (n (s , r , string-sound cs e))
  sn cs n nothing            e = e

string-nothing : ∀ {cs} → ¬ (∃[ s ] ∃[ r ] StringBody cs s r) → collectStringB cs ≡ nothing
string-nothing {cs} n = sn cs n (collectStringB cs) refl

-- A line comment.
line-sound : ∀ cs → LineRest cs (proj₁ (skipLineB cs))
private
  ls-step : ∀ c cs (d : Dec (c ≡ '\n')) → LineRest (c ∷ cs) (proj₁ (skip-nl (isYes d) c cs))
  ls-step c cs (yes refl) = lr-nl
  ls-step c cs (no n)     = lr-char n (line-sound cs)
line-sound []       = lr-end
line-sound (c ∷ cs) = ls-step c cs (c Ch.≟ '\n')

line-det : ∀ {cs r r′} → LineRest cs r → LineRest cs r′ → r ≡ r′
line-det lr-end        lr-end        = refl
line-det lr-nl         lr-nl         = refl
line-det (lr-char _ a) (lr-char _ b) = line-det a b
line-det lr-nl         (lr-char n _) = ⊥-elim (n refl)
line-det (lr-char n _) lr-nl         = ⊥-elim (n refl)

line-eq : ∀ {cs r} → LineRest cs r → proj₁ (skipLineB cs) ≡ r
line-eq {cs} lr = line-det (line-sound cs) lr

-- A nested comment.
block-sound : ∀ n cs (a : Acc _<_ (length cs)) → BlockRest n cs (proj₁ (skipBlockB-WF n cs a))
private
  open-case : ∀ {n c₁ c₂ cs r} → c₁ ≡ '{' × c₂ ≡ '-' → BlockRest (suc (suc n)) cs r → BlockRest (suc n) (c₁ ∷ c₂ ∷ cs) r
  open-case (refl , refl) b = br-open b

  close-case : ∀ {n c₁ c₂ cs r} → c₁ ≡ '-' × c₂ ≡ '}' → BlockRest n cs r → BlockRest (suc n) (c₁ ∷ c₂ ∷ cs) r
  close-case (refl , refl) b = br-close b

  bs-step : ∀ n c₁ c₂ cs (rec : ∀ {y} → y < length (c₁ ∷ c₂ ∷ cs) → Acc _<_ y)
          → (b₁ : Bool) → (c₁ == '{') ∧ (c₂ == '-') ≡ b₁ → (b₂ : Bool) → (c₁ == '-') ∧ (c₂ == '}') ≡ b₂
          → BlockRest (suc n) (c₁ ∷ c₂ ∷ cs) (proj₁ (skipBlockB-WF (suc n) (c₁ ∷ c₂ ∷ cs) (acc rec)))
  bs-step n c₁ c₂ cs rec true  e₁ b₂ e₂ rewrite e₁ = open-case (∧-yes e₁) (block-sound (suc (suc n)) cs (rec _))
  bs-step n c₁ c₂ cs rec false e₁ true e₂ rewrite e₁ | e₂ = close-case (∧-yes e₂) (block-sound n cs (rec _))
  bs-step n c₁ c₂ cs rec false e₁ false e₂ rewrite e₁ | e₂ =
    br-char (∧-no e₁) (∧-no e₂) (block-sound (suc n) (c₂ ∷ cs) (rec _))

block-sound zero    cs              a         = br-done
block-sound (suc n) []              a         = br-end
block-sound (suc n) (c ∷ [])        (acc rec) = br-last
block-sound (suc n) (c₁ ∷ c₂ ∷ cs) (acc rec) =
  bs-step n c₁ c₂ cs rec _ refl _ refl

block-det : ∀ {n cs r r′} → BlockRest n cs r → BlockRest n cs r′ → r ≡ r′
block-det br-done        br-done        = refl
block-det br-end         br-end         = refl
block-det br-last        br-last        = refl
block-det (br-open a)    (br-open b)    = block-det a b
block-det (br-close a)   (br-close b)   = block-det a b
block-det (br-char _ _ a) (br-char _ _ b) = block-det a b
block-det (br-open _)    (br-char p _ _) = ⊥-elim (p (refl , refl))
block-det (br-char p _ _) (br-open _)    = ⊥-elim (p (refl , refl))
block-det (br-close _)   (br-char _ q _) = ⊥-elim (q (refl , refl))
block-det (br-char _ q _) (br-close _)   = ⊥-elim (q (refl , refl))

block-eq : ∀ {n cs r} → BlockRest n cs r → proj₁ (skipBlockB n cs) ≡ r
block-eq {n} {cs} b = block-det (block-sound n cs (<-wellFounded (length cs))) b

------------------------------------------------------------------------
-- The compiler's relation gives the Spec's
------------------------------------------------------------------------

private
  n-ws : ∀ {c cs ts} → HeadView c hkWS → LexesChars cs ts → LexesChars (c ∷ cs) ts
  n-ws hv-space d = lex-space d
  n-ws hv-tab   d = lex-tab d
  n-ws hv-cr    d = lex-cr d

  n-nl-ind : ∀ {c cs ts} → HeadView c hkNL → NLView cs true → LexesChars cs ts → LexesChars (c ∷ cs) ts
  n-nl-ind hv-nl (nl-ind nx o) d = lex-nl-cont nx o d

  n-nl : ∀ {c cs ts} → HeadView c hkNL → NLView cs false → LexesChars cs ts → LexesChars (c ∷ cs) (TNewline ∷ ts)
  n-nl hv-nl (nl-not a b) d = lex-nl a b d

  n-caret1 : ∀ {c cs ts} → HeadView c hkCaret → CaretView cs c-1 → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TCaret1 ∷ ts)
  n-caret1 hv-caret cv-1 d = lex-caret1 d
  n-caret0 : ∀ {c cs ts} → HeadView c hkCaret → CaretView cs c-0 → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TCaret0 ∷ ts)
  n-caret0 hv-caret cv-0 d = lex-caret0 d
  n-caretw : ∀ {c cs ts} → HeadView c hkCaret → CaretView cs c-w → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TCaretW ∷ ts)
  n-caretw hv-caret cv-w d = lex-caretw d

  n-comment : ∀ {c cs ts} → HeadView c hkDash → DashView cs d-comment → LexesChars (proj₁ (skipLineB (drop1 cs))) ts → LexesChars (c ∷ cs) ts
  n-comment hv-dash (dv-comment {t}) d = lex-comment (line-sound t) d
  n-arrow : ∀ {c cs ts} → HeadView c hkDash → DashView cs d-arrow → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TArrow ∷ ts)
  n-arrow hv-dash dv-arrow d = lex-arrow d
  n-minus : ∀ {c cs ts} → HeadView c hkDash → DashView cs d-minus → LexesChars cs ts → LexesChars (c ∷ cs) (TMinus ∷ ts)
  n-minus hv-dash (dv-minus a b) d = lex-minus a b d

  n-block : ∀ {c cs ts} → HeadView c hkLBrace → HeadIs '-' cs true → LexesChars (proj₁ (skipBlockB 1 (drop1 cs))) ts → LexesChars (c ∷ cs) ts
  n-block hv-lbrace (hi-yes {t}) d = lex-block (block-sound 1 t _) d
  n-lbrace : ∀ {c cs ts} → HeadView c hkLBrace → HeadIs '-' cs false → LexesChars cs ts → LexesChars (c ∷ cs) (TLBrace ∷ ts)
  n-lbrace hv-lbrace (hi-no n) d = lex-lbrace n d

  n-le : ∀ {c cs ts} → HeadView c hkLt → HeadIs '=' cs true → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TLe ∷ ts)
  n-le hv-lt hi-yes d = lex-le d
  n-lt : ∀ {c cs ts} → HeadView c hkLt → HeadIs '=' cs false → LexesChars cs ts → LexesChars (c ∷ cs) (TLt ∷ ts)
  n-lt hv-lt (hi-no n) d = lex-lt n d
  n-ge : ∀ {c cs ts} → HeadView c hkGt → HeadIs '=' cs true → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TGe ∷ ts)
  n-ge hv-gt hi-yes d = lex-ge d
  n-gt : ∀ {c cs ts} → HeadView c hkGt → HeadIs '=' cs false → LexesChars cs ts → LexesChars (c ∷ cs) (TGt ∷ ts)
  n-gt hv-gt (hi-no n) d = lex-gt n d
  n-eqeq : ∀ {c cs ts} → HeadView c hkEq → HeadIs '=' cs true → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TEqEq ∷ ts)
  n-eqeq hv-eq hi-yes d = lex-eqeq d
  n-equal : ∀ {c cs ts} → HeadView c hkEq → HeadIs '=' cs false → LexesChars cs ts → LexesChars (c ∷ cs) (TEquals ∷ ts)
  n-equal hv-eq (hi-no n) d = lex-equal n d
  n-neq : ∀ {c cs ts} → HeadView c hkBang → HeadIs '=' cs true → LexesChars (drop1 cs) ts → LexesChars (c ∷ cs) (TNeq ∷ ts)
  n-neq hv-bang hi-yes d = lex-neq d
  n-bang : ∀ {c cs ts} → HeadView c hkBang → HeadIs '=' cs false → LexesChars cs ts → LexesChars (c ∷ cs) (TBang ∷ ts)
  n-bang hv-bang (hi-no n) d = lex-bang n d

  n-lparen : ∀ {c cs ts} → HeadView c hkLParen → LexesChars cs ts → LexesChars (c ∷ cs) (TLParen ∷ ts)
  n-lparen hv-lparen d = lex-lparen d
  n-rparen : ∀ {c cs ts} → HeadView c hkRParen → LexesChars cs ts → LexesChars (c ∷ cs) (TRParen ∷ ts)
  n-rparen hv-rparen d = lex-rparen d
  n-rbrace : ∀ {c cs ts} → HeadView c hkRBrace → LexesChars cs ts → LexesChars (c ∷ cs) (TRBrace ∷ ts)
  n-rbrace hv-rbrace d = lex-rbrace d
  n-colon : ∀ {c cs ts} → HeadView c hkColon → LexesChars cs ts → LexesChars (c ∷ cs) (TColon ∷ ts)
  n-colon hv-colon d = lex-colon d
  n-lambda : ∀ {c cs ts} → HeadView c hkLambda → LexesChars cs ts → LexesChars (c ∷ cs) (TLambda ∷ ts)
  n-lambda hv-lambda d = lex-lambda d
  n-comma : ∀ {c cs ts} → HeadView c hkComma → LexesChars cs ts → LexesChars (c ∷ cs) (TComma ∷ ts)
  n-comma hv-comma d = lex-comma d
  n-semi : ∀ {c cs ts} → HeadView c hkSemi → LexesChars cs ts → LexesChars (c ∷ cs) (TSemicolon ∷ ts)
  n-semi hv-semi d = lex-semi d
  n-at : ∀ {c cs ts} → HeadView c hkAt → LexesChars cs ts → LexesChars (c ∷ cs) (TAt ∷ ts)
  n-at hv-at d = lex-at d
  n-pipe : ∀ {c cs ts} → HeadView c hkPipe → LexesChars cs ts → LexesChars (c ∷ cs) (TPipe ∷ ts)
  n-pipe hv-pipe d = lex-pipe d
  n-plus : ∀ {c cs ts} → HeadView c hkPlus → LexesChars cs ts → LexesChars (c ∷ cs) (TPlus ∷ ts)
  n-plus hv-plus d = lex-plus d
  n-star : ∀ {c cs ts} → HeadView c hkStar → LexesChars cs ts → LexesChars (c ∷ cs) (TStar ∷ ts)
  n-star hv-star d = lex-star d
  n-slash : ∀ {c cs ts} → HeadView c hkSlash → LexesChars cs ts → LexesChars (c ∷ cs) (TSlash ∷ ts)
  n-slash hv-slash d = lex-slash d
  n-pct : ∀ {c cs ts} → HeadView c hkPct → LexesChars cs ts → LexesChars (c ∷ cs) (TPercent ∷ ts)
  n-pct hv-pct d = lex-pct d
  n-amp : ∀ {c cs ts} → HeadView c hkAmp → LexesChars cs ts → LexesChars (c ∷ cs) (TAmpersand ∷ ts)
  n-amp hv-amp d = lex-amp d
  n-dot : ∀ {c cs ts} → HeadView c hkDot → LexesChars cs ts → LexesChars (c ∷ cs) (TDot ∷ ts)
  n-dot hv-dot d = lex-dot d

  n-string : ∀ {c cs s r ts} → HeadView c hkStr → StringBody cs s r → LexesChars r ts → LexesChars (c ∷ cs) (TString (fromList s) ∷ ts)
  n-string hv-quote body d = lex-string body d

  n-ident : ∀ {c cs i r ts} → HeadView c hkGen → isDigit c ≡ false → isIdentStart c ≡ true → IdentRest cs i r
          → LexesChars r ts → LexesChars (c ∷ cs) (TWord (fromList (c ∷ i)) ∷ ts)
  n-ident (hv-gen ns) e i ir d = lex-ident ns e i ir d

-- | The tokens reach `TEOF`: the lexer read the text to its end (D343).
isEOF : Token → Bool
isEOF TEOF = true
{-# CATCHALL #-}
isEOF _    = false

ended : List Token → Bool
ended []       = false
ended (t ∷ ts) = isEOF t ∨ ended ts

toNew : ∀ {off cs ts} → L.LexesChars off cs ts → ended (map forget ts) ≡ true → LexesChars cs (map forget ts)
toNew L.lex-eof _ = lex-eof
toNew (L.lex-ws eqh d) e = n-ws (hview eqh) (toNew d e)
toNew (L.lex-nl-ind {cs = cs} eqh eq d) e = n-nl-ind (hview eqh) (subst (NLView cs) eq (nl-view cs)) (toNew d e)
toNew (L.lex-nl {cs = cs} eqh eq d) e = n-nl (hview eqh) (subst (NLView cs) eq (nl-view cs)) (toNew d e)
toNew (L.lex-caret1 eqh eq d) e = n-caret1 (hview eqh) (cview eq) (toNew d e)
toNew (L.lex-caret0 eqh eq d) e = n-caret0 (hview eqh) (cview eq) (toNew d e)
toNew (L.lex-caretw eqh eq d) e = n-caretw (hview eqh) (cview eq) (toNew d e)
toNew (L.lex-caret-err eqh eq) ()
toNew (L.lex-lcomment-ind eqh eq d) e = n-comment (hview eqh) (dview eq) (toNew d e)
toNew (L.lex-arrow-ind eqh eq d) e = n-arrow (hview eqh) (dview eq) (toNew d e)
toNew (L.lex-minus eqh eq d) e = n-minus (hview eqh) (dview eq) (toNew d e)
toNew (L.lex-bcomment-ind eqh eq d) e = n-block (hview eqh) (dheadview eq) (toNew d e)
toNew (L.lex-lbrace eqh eq d) e = n-lbrace (hview eqh) (dheadview eq) (toNew d e)
toNew (L.lex-le-ind eqh eq d) e = n-le (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-lt eqh eq d) e = n-lt (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-ge-ind eqh eq d) e = n-ge (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-gt eqh eq d) e = n-gt (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-eqeq-ind eqh eq d) e = n-eqeq (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-equals eqh eq d) e = n-equal (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-neq-ind eqh eq d) e = n-neq (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-bang eqh eq d) e = n-bang (hview eqh) (eqview eq) (toNew d e)
toNew (L.lex-lparen eqh d) e = n-lparen (hview eqh) (toNew d e)
toNew (L.lex-rparen eqh d) e = n-rparen (hview eqh) (toNew d e)
toNew (L.lex-rbrace eqh d) e = n-rbrace (hview eqh) (toNew d e)
toNew (L.lex-colon eqh d) e = n-colon (hview eqh) (toNew d e)
toNew (L.lex-lambda eqh d) e = n-lambda (hview eqh) (toNew d e)
toNew (L.lex-comma eqh d) e = n-comma (hview eqh) (toNew d e)
toNew (L.lex-semi eqh d) e = n-semi (hview eqh) (toNew d e)
toNew (L.lex-at eqh d) e = n-at (hview eqh) (toNew d e)
toNew (L.lex-pipe eqh d) e = n-pipe (hview eqh) (toNew d e)
toNew (L.lex-plus eqh d) e = n-plus (hview eqh) (toNew d e)
toNew (L.lex-star eqh d) e = n-star (hview eqh) (toNew d e)
toNew (L.lex-slash eqh d) e = n-slash (hview eqh) (toNew d e)
toNew (L.lex-pct eqh d) e = n-pct (hview eqh) (toNew d e)
toNew (L.lex-amp eqh d) e = n-amp (hview eqh) (toNew d e)
toNew (L.lex-dot eqh d) e = n-dot (hview eqh) (toNew d e)
toNew (L.lex-string {cs = cs} eqh s rest bnd eq d) e = n-string (hview eqh) (string-sound cs eq) (toNew d e)
toNew (L.lex-string-err eqh eq) ()
toNew (L.lex-digit {cs = cs} eqh eqd eqf d) e =
  lex-int eqd (digits-sound cs) (λ (f , r′ , fr) → frac-none eqf fr) (toNew d e)
toNew (L.lex-float {cs = cs} eqh eqd eqf d) e = lex-float eqd (digits-sound cs) (frac-sound _ eqf) (toNew d e)
toNew (L.lex-ident {cs = cs} eqh eqd eqi d) e = n-ident (hview eqh) eqd eqi (ident-sound cs) (toNew d e)
toNew (L.lex-char-err eqh eqd eqi) ()

------------------------------------------------------------------------
-- The Spec's relation gives the compiler's, at every offset
------------------------------------------------------------------------

Old : ℕ → List Char → List Token → Set
Old off cs ts′ = Σ[ ts ∈ List P.Token ] (L.LexesChars off cs ts × map forget ts ≡ ts′)

private
  o-skip : ∀ {off off′ cs cs′ ts′} → (∀ {ts} → L.LexesChars off′ cs′ ts → L.LexesChars off cs ts) → Old off′ cs′ ts′ → Old off cs ts′
  o-skip f (ts , d , e) = ts , f d , e

  o-cons : ∀ {off off′ cs cs′ ts′} (t : P.Token) → (∀ {ts} → L.LexesChars off′ cs′ ts → L.LexesChars off cs (t ∷ ts))
         → Old off′ cs′ ts′ → Old off cs (forget t ∷ ts′)
  o-cons t f (ts , d , e) = t ∷ ts , f d , cong (forget t ∷_) e

  o-at : ∀ {r r′ ts′} → r′ ≡ r → (∀ off → Old off r ts′) → ∀ off → Old off r′ ts′
  o-at refl f = f

  int-old : ∀ {c cs ds r ts′} off → headK c ≡ hkGen → isDigit c ≡ true
          → proj₁ (collectDigitsB cs) ≡ ds → proj₁ (proj₂ (collectDigitsB cs)) ≡ r → ¬ (∃[ f ] ∃[ r′ ] Fraction r f r′)
          → (∀ off → Old off r ts′) → Old off (c ∷ cs) (TInt (+ digitsToNat (c ∷ ds)) ∷ ts′)
  int-old off eh e refl refl nf ih = o-cons (P.TInt _ off) (L.lex-digit eh e (frac-nothing nf)) (ih _)

  float-old : ∀ {c cs ds r f r′ ts′} off → headK c ≡ hkGen → isDigit c ≡ true
            → proj₁ (collectDigitsB cs) ≡ ds → proj₁ (proj₂ (collectDigitsB cs)) ≡ r → Fraction r f r′
            → (∀ off → Old off r′ ts′) → Old off (c ∷ cs) (TFloat (digitsToNat (c ∷ ds)) (digitsToNat f) (length f) ∷ ts′)
  float-old off eh e refl refl fr ih =
    o-cons (P.TFloat _ _ _ off) (L.lex-float {bnd = proj₁ (frac-just fr)} eh e (proj₂ (frac-just fr))) (ih _)

  ident-old : ∀ {c cs i r ts′} off → headK c ≡ hkGen → isDigit c ≡ false → isIdentStart c ≡ true
            → proj₁ (collectIdentB cs) ≡ i → proj₁ (proj₂ (collectIdentB cs)) ≡ r
            → (∀ off → Old off r ts′) → Old off (c ∷ cs) (TWord (fromList (c ∷ i)) ∷ ts′)
  ident-old off eh e i refl refl ih = o-cons (P.TWord _) (L.lex-ident eh e i) (ih _)

toOld : ∀ {cs ts′} → LexesChars cs ts′ → ∀ off → Old off cs ts′
toOld lex-eof off = P.TEOF ∷ [] , L.lex-eof , refl
toOld (lex-space d) off = o-skip (L.lex-ws refl) (toOld d _)
toOld (lex-tab d) off = o-skip (L.lex-ws refl) (toOld d _)
toOld (lex-cr d) off = o-skip (L.lex-ws refl) (toOld d _)
toOld (lex-nl-cont {cs = cs} nx o d) off = o-skip (L.lex-nl-ind refl (nl-true (nl-view cs) nx o)) (toOld d _)
toOld (lex-nl {cs = cs} a b d) off = o-cons P.TNewline (L.lex-nl refl (nl-false (nl-view cs) a b)) (toOld d _)
toOld (lex-caret1 d) off = o-cons P.TCaret1 (L.lex-caret1 refl refl) (toOld d _)
toOld (lex-caret0 d) off = o-cons P.TCaret0 (L.lex-caret0 refl refl) (toOld d _)
toOld (lex-caretw d) off = o-cons P.TCaretW (L.lex-caretw refl refl) (toOld d _)
toOld (lex-comment lr d) off = o-skip (L.lex-lcomment-ind refl refl) (o-at (line-eq lr) (toOld d) _)
toOld (lex-arrow d) off = o-cons P.TArrow (L.lex-arrow-ind refl refl) (toOld d _)
toOld (lex-minus {cs = cs} a b d) off = o-cons P.TMinus (L.lex-minus refl (dash-minus (dash-view cs) a b)) (toOld d _)
toOld (lex-block br d) off = o-skip (L.lex-bcomment-ind refl refl) (o-at (block-eq br) (toOld d) _)
toOld (lex-lbrace {cs = cs} n d) off = o-cons P.TLBrace (L.lex-lbrace refl (head-false (dhead-view cs) n)) (toOld d _)
toOld (lex-le d) off = o-cons P.TLe (L.lex-le-ind refl refl) (toOld d _)
toOld (lex-lt {cs = cs} n d) off = o-cons P.TLt (L.lex-lt refl (head-false (eq-view cs) n)) (toOld d _)
toOld (lex-ge d) off = o-cons P.TGe (L.lex-ge-ind refl refl) (toOld d _)
toOld (lex-gt {cs = cs} n d) off = o-cons P.TGt (L.lex-gt refl (head-false (eq-view cs) n)) (toOld d _)
toOld (lex-eqeq d) off = o-cons P.TEqEq (L.lex-eqeq-ind refl refl) (toOld d _)
toOld (lex-equal {cs = cs} n d) off = o-cons P.TEquals (L.lex-equals refl (head-false (eq-view cs) n)) (toOld d _)
toOld (lex-neq d) off = o-cons P.TNeq (L.lex-neq-ind refl refl) (toOld d _)
toOld (lex-bang {cs = cs} n d) off = o-cons P.TBang (L.lex-bang refl (head-false (eq-view cs) n)) (toOld d _)
toOld (lex-lparen d) off = o-cons P.TLParen (L.lex-lparen refl) (toOld d _)
toOld (lex-rparen d) off = o-cons P.TRParen (L.lex-rparen refl) (toOld d _)
toOld (lex-rbrace d) off = o-cons P.TRBrace (L.lex-rbrace refl) (toOld d _)
toOld (lex-colon d) off = o-cons P.TColon (L.lex-colon refl) (toOld d _)
toOld (lex-lambda d) off = o-cons P.TLambda (L.lex-lambda refl) (toOld d _)
toOld (lex-comma d) off = o-cons P.TComma (L.lex-comma refl) (toOld d _)
toOld (lex-semi d) off = o-cons P.TSemicolon (L.lex-semi refl) (toOld d _)
toOld (lex-at d) off = o-cons P.TAt (L.lex-at refl) (toOld d _)
toOld (lex-pipe d) off = o-cons P.TPipe (L.lex-pipe refl) (toOld d _)
toOld (lex-plus d) off = o-cons P.TPlus (L.lex-plus refl) (toOld d _)
toOld (lex-star d) off = o-cons P.TStar (L.lex-star refl) (toOld d _)
toOld (lex-slash d) off = o-cons P.TSlash (L.lex-slash refl) (toOld d _)
toOld (lex-pct d) off = o-cons P.TPercent (L.lex-pct refl) (toOld d _)
toOld (lex-amp d) off = o-cons P.TAmpersand (L.lex-amp refl) (toOld d _)
toOld (lex-dot d) off = o-cons P.TDot (L.lex-dot refl) (toOld d _)
toOld (lex-string {s = s} {r = r} body d) off =
  o-cons (P.TString (fromList s)) (L.lex-string refl s r (proj₁ (string-complete body)) (proj₂ (string-complete body))) (toOld d _)
toOld (lex-int {c = c} e dg nf d) off = int-old off (gen-head {c} (λ sp → dns sp e)) e (proj₁ (digits-eq dg)) (proj₂ (digits-eq dg)) nf (toOld d)
toOld (lex-float {c = c} e dg fr d) off = float-old off (gen-head {c} (λ sp → dns sp e)) e (proj₁ (digits-eq dg)) (proj₂ (digits-eq dg)) fr (toOld d)
toOld (lex-ident ns e i ir d) off = ident-old off (gen-head ns) e i (proj₁ (ident-eq ir)) (proj₂ (ident-eq ir)) (toOld d)

------------------------------------------------------------------------
-- The tokenizer lexes as the Spec says
------------------------------------------------------------------------

spec-lexes : ∀ text → ended (map forget (tokenizeString text)) ≡ true → Lexes text (map forget (tokenizeString text))
spec-lexes text = toNew (lexer-sound text)

spec-lexes-complete : ∀ text ts → Lexes text ts → map forget (tokenizeString text) ≡ ts
spec-lexes-complete text ts d =
  trans (cong (map forget) (lexer-complete text (proj₁ (toOld d 0)) (proj₁ (proj₂ (toOld d 0))))) (proj₂ (proj₂ (toOld d 0)))

spec-lexes-unique : ∀ {text ts ts′} → Lexes text ts → Lexes text ts′ → ts ≡ ts′
spec-lexes-unique {text} {ts} {ts′} d d′ = trans (sym (spec-lexes-complete text ts d)) (spec-lexes-complete text ts′ d′)
