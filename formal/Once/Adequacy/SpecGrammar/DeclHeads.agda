-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.DeclHeads — the compiler's declaration- and
-- module-level classifiers (`wordHead`, `dotHead`, `colonHead`, `eqHead`,
-- `taEqHead`, `sepClass`, `opTokClass`, `allTrailing`, `skipNewlines`)
-- read as the Spec's lookaheads. Generated case splits on the head token.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.DeclHeads where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Once.Spec.Surface.Lexing using (Token)
open Token
open import Once.Spec.Surface.Grammar
  using (Starts; starts; StartsWord; starts-word; OpChar; oc-dot; oc-plus; oc-minus; oc-star; oc-slash; oc-pct;
         oc-lt; oc-gt; oc-pipe; oc-amp; oc-at; Trailing; trail-end; trail-nl; trail-eof; SkipNewlines; skip-nl; skip-done)
import Once.Parser.Token as P
open import Once.Parser.Core using (skipNewlines)
open import Once.Parser.Module.Core using (wordHead)
open import Once.Parser.Module.Import using (dotHead)
open import Once.Parser.Module.DeclTail using (colonHead; taEqHead)
open import Once.Parser.Module.FunDef.Body using (eqHead)
open import Once.Parser.Module.FunDef.Params using (SepK; skEq; skWord; skStop; sepClass)
open import Once.Parser.Module.OpName using (OpTok; otClose; otChar; otNone; opTokClass)
open import Once.Parser using (allTrailing)
open import Once.Parser.Module using (parseDeclB)
open import Once.Adequacy.SpecGrammar.Tokens using (forget)

private
  F : List P.Token → List Token
  F = map forget

-- Whether a list starts with a word.
data WordView : List P.Token → Bool → Set where
  wv-word : ∀ {s t} → WordView (P.TWord s ∷ t) true
  wv-not  : ∀ {toks} → ¬ StartsWord (F toks) → WordView toks false

word-view : ∀ toks → WordView toks (wordHead toks)
word-view [] = wv-not (λ ())
word-view (P.TWord _ ∷ _) = wv-word
word-view ((P.TInt _ _) ∷ _) = wv-not (λ ())
word-view ((P.TFloat _ _ _ _) ∷ _) = wv-not (λ ())
word-view ((P.TString _) ∷ _) = wv-not (λ ())
word-view (P.TLParen ∷ _) = wv-not (λ ())
word-view (P.TRParen ∷ _) = wv-not (λ ())
word-view (P.TLBrace ∷ _) = wv-not (λ ())
word-view (P.TRBrace ∷ _) = wv-not (λ ())
word-view (P.TColon ∷ _) = wv-not (λ ())
word-view (P.TEquals ∷ _) = wv-not (λ ())
word-view (P.TArrow ∷ _) = wv-not (λ ())
word-view (P.TCaret1 ∷ _) = wv-not (λ ())
word-view (P.TCaret0 ∷ _) = wv-not (λ ())
word-view (P.TCaretW ∷ _) = wv-not (λ ())
word-view (P.TLambda ∷ _) = wv-not (λ ())
word-view (P.TComma ∷ _) = wv-not (λ ())
word-view (P.TSemicolon ∷ _) = wv-not (λ ())
word-view (P.TAt ∷ _) = wv-not (λ ())
word-view (P.TPipe ∷ _) = wv-not (λ ())
word-view (P.TDot ∷ _) = wv-not (λ ())
word-view (P.TPlus ∷ _) = wv-not (λ ())
word-view (P.TMinus ∷ _) = wv-not (λ ())
word-view (P.TStar ∷ _) = wv-not (λ ())
word-view (P.TSlash ∷ _) = wv-not (λ ())
word-view (P.TPercent ∷ _) = wv-not (λ ())
word-view (P.TAmpersand ∷ _) = wv-not (λ ())
word-view (P.TLt ∷ _) = wv-not (λ ())
word-view (P.TLe ∷ _) = wv-not (λ ())
word-view (P.TGt ∷ _) = wv-not (λ ())
word-view (P.TGe ∷ _) = wv-not (λ ())
word-view (P.TEqEq ∷ _) = wv-not (λ ())
word-view (P.TNeq ∷ _) = wv-not (λ ())
word-view (P.TBang ∷ _) = wv-not (λ ())
word-view (P.TNewline ∷ _) = wv-not (λ ())
word-view (P.TEOF ∷ _) = wv-not (λ ())

data DotView : List P.Token → Bool → Set where
  dot-yes : ∀ {t} → DotView (P.TDot ∷ t) true
  dot-no  : ∀ {toks} → ¬ Starts (F toks) TDot → DotView toks false

dot-view : ∀ toks → DotView toks (dotHead toks)
dot-view [] = dot-no (λ ())
dot-view ((P.TWord _) ∷ _) = dot-no (λ ())
dot-view ((P.TInt _ _) ∷ _) = dot-no (λ ())
dot-view ((P.TFloat _ _ _ _) ∷ _) = dot-no (λ ())
dot-view ((P.TString _) ∷ _) = dot-no (λ ())
dot-view (P.TLParen ∷ _) = dot-no (λ ())
dot-view (P.TRParen ∷ _) = dot-no (λ ())
dot-view (P.TLBrace ∷ _) = dot-no (λ ())
dot-view (P.TRBrace ∷ _) = dot-no (λ ())
dot-view (P.TColon ∷ _) = dot-no (λ ())
dot-view (P.TEquals ∷ _) = dot-no (λ ())
dot-view (P.TArrow ∷ _) = dot-no (λ ())
dot-view (P.TCaret1 ∷ _) = dot-no (λ ())
dot-view (P.TCaret0 ∷ _) = dot-no (λ ())
dot-view (P.TCaretW ∷ _) = dot-no (λ ())
dot-view (P.TLambda ∷ _) = dot-no (λ ())
dot-view (P.TComma ∷ _) = dot-no (λ ())
dot-view (P.TSemicolon ∷ _) = dot-no (λ ())
dot-view (P.TAt ∷ _) = dot-no (λ ())
dot-view (P.TPipe ∷ _) = dot-no (λ ())
dot-view (P.TDot ∷ _) = dot-yes
dot-view (P.TPlus ∷ _) = dot-no (λ ())
dot-view (P.TMinus ∷ _) = dot-no (λ ())
dot-view (P.TStar ∷ _) = dot-no (λ ())
dot-view (P.TSlash ∷ _) = dot-no (λ ())
dot-view (P.TPercent ∷ _) = dot-no (λ ())
dot-view (P.TAmpersand ∷ _) = dot-no (λ ())
dot-view (P.TLt ∷ _) = dot-no (λ ())
dot-view (P.TLe ∷ _) = dot-no (λ ())
dot-view (P.TGt ∷ _) = dot-no (λ ())
dot-view (P.TGe ∷ _) = dot-no (λ ())
dot-view (P.TEqEq ∷ _) = dot-no (λ ())
dot-view (P.TNeq ∷ _) = dot-no (λ ())
dot-view (P.TBang ∷ _) = dot-no (λ ())
dot-view (P.TNewline ∷ _) = dot-no (λ ())
dot-view (P.TEOF ∷ _) = dot-no (λ ())

data ColonView : List P.Token → Bool → Set where
  colon-yes : ∀ {t} → ColonView (P.TColon ∷ t) true
  colon-no  : ∀ {toks} → ¬ Starts (F toks) TColon → ColonView toks false

colon-view : ∀ toks → ColonView toks (colonHead toks)
colon-view [] = colon-no (λ ())
colon-view ((P.TWord _) ∷ _) = colon-no (λ ())
colon-view ((P.TInt _ _) ∷ _) = colon-no (λ ())
colon-view ((P.TFloat _ _ _ _) ∷ _) = colon-no (λ ())
colon-view ((P.TString _) ∷ _) = colon-no (λ ())
colon-view (P.TLParen ∷ _) = colon-no (λ ())
colon-view (P.TRParen ∷ _) = colon-no (λ ())
colon-view (P.TLBrace ∷ _) = colon-no (λ ())
colon-view (P.TRBrace ∷ _) = colon-no (λ ())
colon-view (P.TColon ∷ _) = colon-yes
colon-view (P.TEquals ∷ _) = colon-no (λ ())
colon-view (P.TArrow ∷ _) = colon-no (λ ())
colon-view (P.TCaret1 ∷ _) = colon-no (λ ())
colon-view (P.TCaret0 ∷ _) = colon-no (λ ())
colon-view (P.TCaretW ∷ _) = colon-no (λ ())
colon-view (P.TLambda ∷ _) = colon-no (λ ())
colon-view (P.TComma ∷ _) = colon-no (λ ())
colon-view (P.TSemicolon ∷ _) = colon-no (λ ())
colon-view (P.TAt ∷ _) = colon-no (λ ())
colon-view (P.TPipe ∷ _) = colon-no (λ ())
colon-view (P.TDot ∷ _) = colon-no (λ ())
colon-view (P.TPlus ∷ _) = colon-no (λ ())
colon-view (P.TMinus ∷ _) = colon-no (λ ())
colon-view (P.TStar ∷ _) = colon-no (λ ())
colon-view (P.TSlash ∷ _) = colon-no (λ ())
colon-view (P.TPercent ∷ _) = colon-no (λ ())
colon-view (P.TAmpersand ∷ _) = colon-no (λ ())
colon-view (P.TLt ∷ _) = colon-no (λ ())
colon-view (P.TLe ∷ _) = colon-no (λ ())
colon-view (P.TGt ∷ _) = colon-no (λ ())
colon-view (P.TGe ∷ _) = colon-no (λ ())
colon-view (P.TEqEq ∷ _) = colon-no (λ ())
colon-view (P.TNeq ∷ _) = colon-no (λ ())
colon-view (P.TBang ∷ _) = colon-no (λ ())
colon-view (P.TNewline ∷ _) = colon-no (λ ())
colon-view (P.TEOF ∷ _) = colon-no (λ ())

data EqView : List P.Token → Bool → Set where
  eq-yes : ∀ {t} → EqView (P.TEquals ∷ t) true
  eq-no  : ∀ {toks} → ¬ Starts (F toks) TEquals → EqView toks false

eq-view : ∀ toks → EqView toks (eqHead toks)
eq-view [] = eq-no (λ ())
eq-view ((P.TWord _) ∷ _) = eq-no (λ ())
eq-view ((P.TInt _ _) ∷ _) = eq-no (λ ())
eq-view ((P.TFloat _ _ _ _) ∷ _) = eq-no (λ ())
eq-view ((P.TString _) ∷ _) = eq-no (λ ())
eq-view (P.TLParen ∷ _) = eq-no (λ ())
eq-view (P.TRParen ∷ _) = eq-no (λ ())
eq-view (P.TLBrace ∷ _) = eq-no (λ ())
eq-view (P.TRBrace ∷ _) = eq-no (λ ())
eq-view (P.TColon ∷ _) = eq-no (λ ())
eq-view (P.TEquals ∷ _) = eq-yes
eq-view (P.TArrow ∷ _) = eq-no (λ ())
eq-view (P.TCaret1 ∷ _) = eq-no (λ ())
eq-view (P.TCaret0 ∷ _) = eq-no (λ ())
eq-view (P.TCaretW ∷ _) = eq-no (λ ())
eq-view (P.TLambda ∷ _) = eq-no (λ ())
eq-view (P.TComma ∷ _) = eq-no (λ ())
eq-view (P.TSemicolon ∷ _) = eq-no (λ ())
eq-view (P.TAt ∷ _) = eq-no (λ ())
eq-view (P.TPipe ∷ _) = eq-no (λ ())
eq-view (P.TDot ∷ _) = eq-no (λ ())
eq-view (P.TPlus ∷ _) = eq-no (λ ())
eq-view (P.TMinus ∷ _) = eq-no (λ ())
eq-view (P.TStar ∷ _) = eq-no (λ ())
eq-view (P.TSlash ∷ _) = eq-no (λ ())
eq-view (P.TPercent ∷ _) = eq-no (λ ())
eq-view (P.TAmpersand ∷ _) = eq-no (λ ())
eq-view (P.TLt ∷ _) = eq-no (λ ())
eq-view (P.TLe ∷ _) = eq-no (λ ())
eq-view (P.TGt ∷ _) = eq-no (λ ())
eq-view (P.TGe ∷ _) = eq-no (λ ())
eq-view (P.TEqEq ∷ _) = eq-no (λ ())
eq-view (P.TNeq ∷ _) = eq-no (λ ())
eq-view (P.TBang ∷ _) = eq-no (λ ())
eq-view (P.TNewline ∷ _) = eq-no (λ ())
eq-view (P.TEOF ∷ _) = eq-no (λ ())

data TaEqView : List P.Token → Bool → Set where
  taEq-yes : ∀ {t} → TaEqView (P.TEquals ∷ t) true
  taEq-no  : ∀ {toks} → ¬ Starts (F toks) TEquals → TaEqView toks false

taEq-view : ∀ toks → TaEqView toks (taEqHead toks)
taEq-view [] = taEq-no (λ ())
taEq-view ((P.TWord _) ∷ _) = taEq-no (λ ())
taEq-view ((P.TInt _ _) ∷ _) = taEq-no (λ ())
taEq-view ((P.TFloat _ _ _ _) ∷ _) = taEq-no (λ ())
taEq-view ((P.TString _) ∷ _) = taEq-no (λ ())
taEq-view (P.TLParen ∷ _) = taEq-no (λ ())
taEq-view (P.TRParen ∷ _) = taEq-no (λ ())
taEq-view (P.TLBrace ∷ _) = taEq-no (λ ())
taEq-view (P.TRBrace ∷ _) = taEq-no (λ ())
taEq-view (P.TColon ∷ _) = taEq-no (λ ())
taEq-view (P.TEquals ∷ _) = taEq-yes
taEq-view (P.TArrow ∷ _) = taEq-no (λ ())
taEq-view (P.TCaret1 ∷ _) = taEq-no (λ ())
taEq-view (P.TCaret0 ∷ _) = taEq-no (λ ())
taEq-view (P.TCaretW ∷ _) = taEq-no (λ ())
taEq-view (P.TLambda ∷ _) = taEq-no (λ ())
taEq-view (P.TComma ∷ _) = taEq-no (λ ())
taEq-view (P.TSemicolon ∷ _) = taEq-no (λ ())
taEq-view (P.TAt ∷ _) = taEq-no (λ ())
taEq-view (P.TPipe ∷ _) = taEq-no (λ ())
taEq-view (P.TDot ∷ _) = taEq-no (λ ())
taEq-view (P.TPlus ∷ _) = taEq-no (λ ())
taEq-view (P.TMinus ∷ _) = taEq-no (λ ())
taEq-view (P.TStar ∷ _) = taEq-no (λ ())
taEq-view (P.TSlash ∷ _) = taEq-no (λ ())
taEq-view (P.TPercent ∷ _) = taEq-no (λ ())
taEq-view (P.TAmpersand ∷ _) = taEq-no (λ ())
taEq-view (P.TLt ∷ _) = taEq-no (λ ())
taEq-view (P.TLe ∷ _) = taEq-no (λ ())
taEq-view (P.TGt ∷ _) = taEq-no (λ ())
taEq-view (P.TGe ∷ _) = taEq-no (λ ())
taEq-view (P.TEqEq ∷ _) = taEq-no (λ ())
taEq-view (P.TNeq ∷ _) = taEq-no (λ ())
taEq-view (P.TBang ∷ _) = taEq-no (λ ())
taEq-view (P.TNewline ∷ _) = taEq-no (λ ())
taEq-view (P.TEOF ∷ _) = taEq-no (λ ())

data SepView : List P.Token → SepK → Set where
  sv-eq   : ∀ {t} → SepView (P.TEquals ∷ t) skEq
  sv-word : ∀ {s t} → SepView (P.TWord s ∷ t) skWord
  sv-stop : ∀ {toks} → ¬ Starts (F toks) TEquals → ¬ StartsWord (F toks) → SepView toks skStop

sep-view : ∀ toks → SepView toks (sepClass toks)
sep-view [] = sv-stop (λ ()) (λ ())
sep-view (P.TWord _ ∷ _) = sv-word
sep-view ((P.TInt _ _) ∷ _) = sv-stop (λ ()) (λ ())
sep-view ((P.TFloat _ _ _ _) ∷ _) = sv-stop (λ ()) (λ ())
sep-view ((P.TString _) ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TLParen ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TRParen ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TLBrace ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TRBrace ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TColon ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TEquals ∷ _) = sv-eq
sep-view (P.TArrow ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TCaret1 ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TCaret0 ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TCaretW ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TLambda ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TComma ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TSemicolon ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TAt ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TPipe ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TDot ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TPlus ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TMinus ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TStar ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TSlash ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TPercent ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TAmpersand ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TLt ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TLe ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TGt ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TGe ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TEqEq ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TNeq ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TBang ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TNewline ∷ _) = sv-stop (λ ()) (λ ())
sep-view (P.TEOF ∷ _) = sv-stop (λ ()) (λ ())

data OpTokView : P.Token → OpTok → Set where
  otv-close : OpTokView P.TRParen otClose
  otv-char  : ∀ {t ch} → OpChar (forget t) ch → OpTokView t (otChar ch)
  otv-none  : ∀ {t} → (forget t ≡ TRParen → Data.Empty.⊥) → (∀ {ch} → ¬ OpChar (forget t) ch) → OpTokView t otNone

optok-view : ∀ t → OpTokView t (opTokClass t)
optok-view (P.TWord _) = otv-none (λ ()) (λ ())
optok-view (P.TInt _ _) = otv-none (λ ()) (λ ())
optok-view (P.TFloat _ _ _ _) = otv-none (λ ()) (λ ())
optok-view (P.TString _) = otv-none (λ ()) (λ ())
optok-view P.TLParen = otv-none (λ ()) (λ ())
optok-view P.TRParen = otv-close
optok-view P.TLBrace = otv-none (λ ()) (λ ())
optok-view P.TRBrace = otv-none (λ ()) (λ ())
optok-view P.TColon = otv-none (λ ()) (λ ())
optok-view P.TEquals = otv-none (λ ()) (λ ())
optok-view P.TArrow = otv-none (λ ()) (λ ())
optok-view P.TCaret1 = otv-none (λ ()) (λ ())
optok-view P.TCaret0 = otv-none (λ ()) (λ ())
optok-view P.TCaretW = otv-none (λ ()) (λ ())
optok-view P.TLambda = otv-none (λ ()) (λ ())
optok-view P.TComma = otv-none (λ ()) (λ ())
optok-view P.TSemicolon = otv-none (λ ()) (λ ())
optok-view P.TAt = otv-char oc-at
optok-view P.TPipe = otv-char oc-pipe
optok-view P.TDot = otv-char oc-dot
optok-view P.TPlus = otv-char oc-plus
optok-view P.TMinus = otv-char oc-minus
optok-view P.TStar = otv-char oc-star
optok-view P.TSlash = otv-char oc-slash
optok-view P.TPercent = otv-char oc-pct
optok-view P.TAmpersand = otv-char oc-amp
optok-view P.TLt = otv-char oc-lt
optok-view P.TLe = otv-none (λ ()) (λ ())
optok-view P.TGt = otv-char oc-gt
optok-view P.TGe = otv-none (λ ()) (λ ())
optok-view P.TEqEq = otv-none (λ ()) (λ ())
optok-view P.TNeq = otv-none (λ ()) (λ ())
optok-view P.TBang = otv-none (λ ()) (λ ())
optok-view P.TNewline = otv-none (λ ()) (λ ())
optok-view P.TEOF = otv-none (λ ()) (λ ())

trail→ : ∀ toks → allTrailing toks ≡ true → Trailing (F toks)
trail→ [] _ = trail-end
trail→ ((P.TWord _) ∷ _) ()
trail→ ((P.TInt _ _) ∷ _) ()
trail→ ((P.TFloat _ _ _ _) ∷ _) ()
trail→ ((P.TString _) ∷ _) ()
trail→ (P.TLParen ∷ _) ()
trail→ (P.TRParen ∷ _) ()
trail→ (P.TLBrace ∷ _) ()
trail→ (P.TRBrace ∷ _) ()
trail→ (P.TColon ∷ _) ()
trail→ (P.TEquals ∷ _) ()
trail→ (P.TArrow ∷ _) ()
trail→ (P.TCaret1 ∷ _) ()
trail→ (P.TCaret0 ∷ _) ()
trail→ (P.TCaretW ∷ _) ()
trail→ (P.TLambda ∷ _) ()
trail→ (P.TComma ∷ _) ()
trail→ (P.TSemicolon ∷ _) ()
trail→ (P.TAt ∷ _) ()
trail→ (P.TPipe ∷ _) ()
trail→ (P.TDot ∷ _) ()
trail→ (P.TPlus ∷ _) ()
trail→ (P.TMinus ∷ _) ()
trail→ (P.TStar ∷ _) ()
trail→ (P.TSlash ∷ _) ()
trail→ (P.TPercent ∷ _) ()
trail→ (P.TAmpersand ∷ _) ()
trail→ (P.TLt ∷ _) ()
trail→ (P.TLe ∷ _) ()
trail→ (P.TGt ∷ _) ()
trail→ (P.TGe ∷ _) ()
trail→ (P.TEqEq ∷ _) ()
trail→ (P.TNeq ∷ _) ()
trail→ (P.TBang ∷ _) ()
trail→ (P.TNewline ∷ t) e = trail-nl (trail→ t e)
trail→ (P.TEOF ∷ t) e = trail-eof (trail→ t e)

trail← : ∀ toks → Trailing (F toks) → allTrailing toks ≡ true
trail← [] _ = refl
trail← ((P.TWord _) ∷ _) ()
trail← ((P.TInt _ _) ∷ _) ()
trail← ((P.TFloat _ _ _ _) ∷ _) ()
trail← ((P.TString _) ∷ _) ()
trail← (P.TLParen ∷ _) ()
trail← (P.TRParen ∷ _) ()
trail← (P.TLBrace ∷ _) ()
trail← (P.TRBrace ∷ _) ()
trail← (P.TColon ∷ _) ()
trail← (P.TEquals ∷ _) ()
trail← (P.TArrow ∷ _) ()
trail← (P.TCaret1 ∷ _) ()
trail← (P.TCaret0 ∷ _) ()
trail← (P.TCaretW ∷ _) ()
trail← (P.TLambda ∷ _) ()
trail← (P.TComma ∷ _) ()
trail← (P.TSemicolon ∷ _) ()
trail← (P.TAt ∷ _) ()
trail← (P.TPipe ∷ _) ()
trail← (P.TDot ∷ _) ()
trail← (P.TPlus ∷ _) ()
trail← (P.TMinus ∷ _) ()
trail← (P.TStar ∷ _) ()
trail← (P.TSlash ∷ _) ()
trail← (P.TPercent ∷ _) ()
trail← (P.TAmpersand ∷ _) ()
trail← (P.TLt ∷ _) ()
trail← (P.TLe ∷ _) ()
trail← (P.TGt ∷ _) ()
trail← (P.TGe ∷ _) ()
trail← (P.TEqEq ∷ _) ()
trail← (P.TNeq ∷ _) ()
trail← (P.TBang ∷ _) ()
trail← (P.TNewline ∷ t) (trail-nl d) = trail← t d
trail← (P.TEOF ∷ t) (trail-eof d) = trail← t d

decl-trail : ∀ toks → Trailing (F toks) → ¬ Starts (F toks) TNewline → parseDeclB toks ≡ nothing
decl-trail [] _ _ = refl
decl-trail ((P.TWord _) ∷ _) () _
decl-trail ((P.TInt _ _) ∷ _) () _
decl-trail ((P.TFloat _ _ _ _) ∷ _) () _
decl-trail ((P.TString _) ∷ _) () _
decl-trail (P.TLParen ∷ _) () _
decl-trail (P.TRParen ∷ _) () _
decl-trail (P.TLBrace ∷ _) () _
decl-trail (P.TRBrace ∷ _) () _
decl-trail (P.TColon ∷ _) () _
decl-trail (P.TEquals ∷ _) () _
decl-trail (P.TArrow ∷ _) () _
decl-trail (P.TCaret1 ∷ _) () _
decl-trail (P.TCaret0 ∷ _) () _
decl-trail (P.TCaretW ∷ _) () _
decl-trail (P.TLambda ∷ _) () _
decl-trail (P.TComma ∷ _) () _
decl-trail (P.TSemicolon ∷ _) () _
decl-trail (P.TAt ∷ _) () _
decl-trail (P.TPipe ∷ _) () _
decl-trail (P.TDot ∷ _) () _
decl-trail (P.TPlus ∷ _) () _
decl-trail (P.TMinus ∷ _) () _
decl-trail (P.TStar ∷ _) () _
decl-trail (P.TSlash ∷ _) () _
decl-trail (P.TPercent ∷ _) () _
decl-trail (P.TAmpersand ∷ _) () _
decl-trail (P.TLt ∷ _) () _
decl-trail (P.TLe ∷ _) () _
decl-trail (P.TGt ∷ _) () _
decl-trail (P.TGe ∷ _) () _
decl-trail (P.TEqEq ∷ _) () _
decl-trail (P.TNeq ∷ _) () _
decl-trail (P.TBang ∷ _) () _
decl-trail (P.TNewline ∷ _) _ n = ⊥-elim (n starts)
decl-trail (P.TEOF ∷ _) _ _ = refl

data SkipView : List P.Token → Set where
  sk-nil  : SkipView []
  sk-nl   : ∀ {t} → SkipView (P.TNewline ∷ t)
  sk-stop : ∀ {toks} → ¬ Starts (F toks) TNewline → skipNewlines toks ≡ just ([] , toks) → SkipView toks

skip-view : ∀ toks → SkipView toks
skip-view [] = sk-nil
skip-view ((P.TWord _) ∷ _) = sk-stop (λ ()) refl
skip-view ((P.TInt _ _) ∷ _) = sk-stop (λ ()) refl
skip-view ((P.TFloat _ _ _ _) ∷ _) = sk-stop (λ ()) refl
skip-view ((P.TString _) ∷ _) = sk-stop (λ ()) refl
skip-view (P.TLParen ∷ _) = sk-stop (λ ()) refl
skip-view (P.TRParen ∷ _) = sk-stop (λ ()) refl
skip-view (P.TLBrace ∷ _) = sk-stop (λ ()) refl
skip-view (P.TRBrace ∷ _) = sk-stop (λ ()) refl
skip-view (P.TColon ∷ _) = sk-stop (λ ()) refl
skip-view (P.TEquals ∷ _) = sk-stop (λ ()) refl
skip-view (P.TArrow ∷ _) = sk-stop (λ ()) refl
skip-view (P.TCaret1 ∷ _) = sk-stop (λ ()) refl
skip-view (P.TCaret0 ∷ _) = sk-stop (λ ()) refl
skip-view (P.TCaretW ∷ _) = sk-stop (λ ()) refl
skip-view (P.TLambda ∷ _) = sk-stop (λ ()) refl
skip-view (P.TComma ∷ _) = sk-stop (λ ()) refl
skip-view (P.TSemicolon ∷ _) = sk-stop (λ ()) refl
skip-view (P.TAt ∷ _) = sk-stop (λ ()) refl
skip-view (P.TPipe ∷ _) = sk-stop (λ ()) refl
skip-view (P.TDot ∷ _) = sk-stop (λ ()) refl
skip-view (P.TPlus ∷ _) = sk-stop (λ ()) refl
skip-view (P.TMinus ∷ _) = sk-stop (λ ()) refl
skip-view (P.TStar ∷ _) = sk-stop (λ ()) refl
skip-view (P.TSlash ∷ _) = sk-stop (λ ()) refl
skip-view (P.TPercent ∷ _) = sk-stop (λ ()) refl
skip-view (P.TAmpersand ∷ _) = sk-stop (λ ()) refl
skip-view (P.TLt ∷ _) = sk-stop (λ ()) refl
skip-view (P.TLe ∷ _) = sk-stop (λ ()) refl
skip-view (P.TGt ∷ _) = sk-stop (λ ()) refl
skip-view (P.TGe ∷ _) = sk-stop (λ ()) refl
skip-view (P.TEqEq ∷ _) = sk-stop (λ ()) refl
skip-view (P.TNeq ∷ _) = sk-stop (λ ()) refl
skip-view (P.TBang ∷ _) = sk-stop (λ ()) refl
skip-view (P.TNewline ∷ _) = sk-nl
skip-view (P.TEOF ∷ _) = sk-stop (λ ()) refl
