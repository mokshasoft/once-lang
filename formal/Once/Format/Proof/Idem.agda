-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Idem — formatting twice is formatting once, for a text
-- without comments (plan 0.124 step 4.5).
--
-- The formatter's output of such a text holds no comment: the printer
-- without trivia writes none (`Canon.Bare`), the layout of a document without
-- one writes no comment lexeme, and no two of its characters start one (`--`
-- or `{-`: `NoPair`), so the lexer finds none in it (`noc-WF`). Then the
-- output is formatted as the text is (`Canon.format-quiet`), and the
-- formatter's second pass returns it unchanged (`idempotent`).
--
-- Generated in part (the cases per token) by `scripts/gen-format-idem.py`:
-- edit the generator, not this file.
------------------------------------------------------------------------

module Once.Format.Proof.Idem where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char; isDigit)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; replicate; reverse; concatMap; length)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TString; TLParen; TRParen; TLBrace; TRBrace;
  TColon; TEquals; TArrow; TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon; TAt; TPipe; TDot; TPlus; TMinus;
  TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang; TNewline; TEOF; Next; next;
  isIdentStart; isIdentContinue)
open import Once.Spec.Surface.Syntax using (Module; mkModule)
open import Once.Parser using (parseStrict)
import Once.Parser.Lexer as PL
open import Once.Format using (formatSource; formatParsed)
open import Once.Format.Spell using (spell; decimal; fixed)
open import Once.Format.Doc
open import Once.Format.Lex using (Item; tok; comment; cont; lexItems; items-WF; it-head; it-str; it-gen; it-num; it-nl;
  it-op2; it-lbrace; it-minus; it-caret)
open import Once.Format.Print using (format; pmodule; pdecls)
open import Once.Format.Proof.Digits using (decimal-digits; fixed-digits)
open import Once.Format.Proof.Lexing using (Printable; p-word; p-int; p-float; p-sym; Valid; Adj; tok-tok; tok-sp; tok-nl;
  WS; ws-[]; ws-1; ws-∷; ft-minus; ft-brace)
open import Once.Format.Proof.Module using (module-ws)
import Once.Format.Proof.Module
import Once.Format.Proof.Printable
import Data.Nat.Induction
import Once.Adequacy.SpecGrammar.Decl
import Once.Adequacy.FrontEndBridge
open import Once.Format.Proof.Decl using (decl-ok)
open import Once.Format.Proof.Canon using (NoComment; nc-tok; nc-cont; format-quiet; NoNotes; nn-empty; nn-tk; nn-sp;
  nn-line; nn-newline; nn-blank; nn-<>; nn-nest; nn-group)
import Once.Format.Proof.Canon as Canon
open import Once.Format.Proof.LexOK using (DigitBound)
open import Once.Format.Proof.WF using (parsed-wf)
open import Once.Format.Proof.RoundTrip using (roundtrip)
open import Once.Adequacy.SpecLexing using (hview; HeadView; hv-dash; hv-lbrace; dview; DashView; dv-comment; dv-arrow;
  dv-minus; dheadview; HeadIs; hi-yes; hi-no; ident-sound; digits-sound; frac-sound; string-sound)

------------------------------------------------------------------------
-- No comment starts in a text
------------------------------------------------------------------------

-- `--` and `{-` start a comment.
data Bad : Char → Char → Set where
  bad-dd : Bad '-' '-'
  bad-bd : Bad '{' '-'

data NoPair : List Char → Set where
  np-[] : NoPair []
  np-1  : ∀ {c} → NoPair (c ∷ [])
  np-∷  : ∀ {c d cs} → ¬ Bad c d → NoPair (d ∷ cs) → NoPair (c ∷ d ∷ cs)

private
  np-tail : ∀ {c cs} → NoPair (c ∷ cs) → NoPair cs
  np-tail np-1       = np-[]
  np-tail (np-∷ _ p) = p

  np-drop : ∀ xs {ys} → NoPair (xs ++ ys) → NoPair ys
  np-drop []       p = p
  np-drop (x ∷ xs) p = np-drop xs (np-tail p)

  -- Characters that start nothing dangerous.
  Safe : Char → Set
  Safe c = c ≢ '-' × c ≢ '{'

  DF : List Char → Set
  DF = All Safe

  safe-bad : ∀ {c d} → Safe c → ¬ Bad c d
  safe-bad (n , _) bad-dd = n refl
  safe-bad (_ , n) bad-bd = n refl

  df-np : ∀ xs {ys} → DF xs → NoPair ys → NoPair (xs ++ ys)
  df-np []           _        p = p
  df-np (x ∷ [])     (s ∷ []) np-[]        = np-1
  df-np (x ∷ [])     (s ∷ []) p@np-1       = np-∷ (safe-bad s) p
  df-np (x ∷ [])     (s ∷ []) p@(np-∷ _ _) = np-∷ (safe-bad s) p
  df-np (x ∷ y ∷ xs) (s ∷ ss) p = np-∷ (safe-bad s) (df-np (y ∷ xs) ss p)

  -- A character of one kind is safe.
  kind-safe : ∀ {c} (f : Char → Bool) → f c ≡ true → f '-' ≡ false → f '{' ≡ false → Safe c
  kind-safe {c} f fc fd fb = (λ { refl → t≢f (trans (sym fc) fd) }) , (λ { refl → t≢f (trans (sym fc) fb) })
    where
      t≢f : true ≡ false → ⊥
      t≢f ()

  digits-df : ∀ {xs} → All (λ x → isDigit x ≡ true) xs → DF xs
  digits-df []       = []
  digits-df (p ∷ ps) = kind-safe isDigit p refl refl ∷ digits-df ps

  cont-df : ∀ {xs} → All (λ x → isIdentContinue x ≡ true) xs → DF xs
  cont-df []       = []
  cont-df (p ∷ ps) = kind-safe isIdentContinue p refl refl ∷ cont-df ps

  minus-np : ∀ {ys} → ¬ Next ys '-' → NoPair ys → NoPair ('-' ∷ ys)
  minus-np {[]}    n p = np-1
  minus-np {_ ∷ _} n p = np-∷ (λ { bad-dd → n next }) p

  brace-np : ∀ {ys} → ¬ Next ys '-' → NoPair ys → NoPair ('{' ∷ ys)
  brace-np {[]}    n p = np-1
  brace-np {_ ∷ _} n p = np-∷ (λ { bad-bd → n next }) p

  arrow-np : ∀ {ys} → NoPair ys → NoPair ('-' ∷ '>' ∷ ys)
  arrow-np p = np-∷ (λ ()) (df-np ('>' ∷ []) (((λ ()) , (λ ())) ∷ []) p)

  replicate-df : ∀ n → DF (replicate n ' ')
  replicate-df zero    = []
  replicate-df (suc n) = ((λ ()) , (λ ())) ∷ replicate-df n

  -- What follows a lexeme may not continue `-` or `{` into a comment.
  After : Lexeme → List Char → Set
  After (lt TMinus)  ys = ¬ Next ys '-'
  After (lt TLBrace) ys = ¬ Next ys '-'
  {-# CATCHALL #-}
  After _            ys = ⊤

  NotLcm : Lexeme → Set
  NotLcm (lcm _) = ⊥
  {-# CATCHALL #-}
  NotLcm _       = ⊤

-- | A lexeme, then a text with no comment start.
lexeme-np : ∀ x ys → Valid x → NotLcm x → After x ys → NoPair ys → NoPair (chars x ++ ys)
lexeme-np lsp ys _ _ _ p = df-np (' ' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np lnl ys _ _ _ p = df-np ('\n' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lind i) ys _ _ _ p = df-np (replicate i ' ') (replicate-df i) p
lexeme-np (lcm c) ys _ () _ p
lexeme-np (lt (TWord s)) ys (p-word {c = c} {i} eq ¬s ¬d ist ps) _ _ p =
  subst (λ xs → NoPair (xs ++ ys)) (sym eq) (df-np (c ∷ i) (kind-safe isIdentStart ist refl refl ∷ cont-df ps) p)
lexeme-np (lt (TInt .(+ n))) ys (p-int {n}) _ _ p =
  subst (λ xs → NoPair (xs ++ ys)) (sym (toList∘fromList (decimal n))) (df-np (decimal n) (digits-df (decimal-digits n)) p)
lexeme-np (lt (TFloat i f .(suc l))) ys (p-float {l = l} _) _ _ p =
  subst (λ xs → NoPair (xs ++ ys)) (sym (toList∘fromList (decimal i ++ '.' ∷ fixed (suc l) f)))
    (df-np (decimal i ++ '.' ∷ fixed (suc l) f)
      (AllP.++⁺ (digits-df (decimal-digits i)) (((λ ()) , (λ ())) ∷ digits-df (fixed-digits (suc l) f))) p)
lexeme-np (lt (TString _)) ys (p-sym ()) _ _ p
lexeme-np (lt TNewline) ys (p-sym ()) _ _ p
lexeme-np (lt TEOF) ys (p-sym ()) _ _ p
lexeme-np (lt TLParen) ys _ _ _ p = df-np ('(' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TRParen) ys _ _ _ p = df-np (')' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TLBrace) ys _ _ a p = brace-np a p
lexeme-np (lt TRBrace) ys _ _ _ p = df-np ('}' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TColon) ys _ _ _ p = df-np (':' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TEquals) ys _ _ _ p = df-np ('=' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TArrow) ys _ _ a p = arrow-np p
lexeme-np (lt TCaret1) ys _ _ _ p = df-np ('^' ∷ '1' ∷ []) (((λ ()) , (λ ())) ∷ ((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TCaret0) ys _ _ _ p = df-np ('^' ∷ '0' ∷ []) (((λ ()) , (λ ())) ∷ ((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TCaretW) ys _ _ _ p = df-np ('^' ∷ 'w' ∷ []) (((λ ()) , (λ ())) ∷ ((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TLambda) ys _ _ _ p = df-np ('\\' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TComma) ys _ _ _ p = df-np (',' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TSemicolon) ys _ _ _ p = df-np (';' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TAt) ys _ _ _ p = df-np ('@' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TPipe) ys _ _ _ p = df-np ('|' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TDot) ys _ _ _ p = df-np ('.' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TPlus) ys _ _ _ p = df-np ('+' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TMinus) ys _ _ a p = minus-np a p
lexeme-np (lt TStar) ys _ _ _ p = df-np ('*' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TSlash) ys _ _ _ p = df-np ('/' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TPercent) ys _ _ _ p = df-np ('%' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TAmpersand) ys _ _ _ p = df-np ('&' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TLt) ys _ _ _ p = df-np ('<' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TLe) ys _ _ _ p = df-np ('<' ∷ '=' ∷ []) (((λ ()) , (λ ())) ∷ ((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TGt) ys _ _ _ p = df-np ('>' ∷ []) (((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TGe) ys _ _ _ p = df-np ('>' ∷ '=' ∷ []) (((λ ()) , (λ ())) ∷ ((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TEqEq) ys _ _ _ p = df-np ('=' ∷ '=' ∷ []) (((λ ()) , (λ ())) ∷ ((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TNeq) ys _ _ _ p = df-np ('!' ∷ '=' ∷ []) (((λ ()) , (λ ())) ∷ ((λ ()) , (λ ())) ∷ []) p
lexeme-np (lt TBang) ys _ _ _ p = df-np ('!' ∷ []) (((λ ()) , (λ ())) ∷ []) p

private
  -- What follows a token after it, in the layout.
  after : ∀ {x y} ys → Adj x y → Valid y → After x (chars y ++ ys)
  after {lt TMinus}  ys (tok-tok {t = t} h) v = proj₁ (ft-minus t h v)
  after {lt TLBrace} ys (tok-tok {t = t} h) v = ft-brace t h v
  after {lt TMinus}  ys tok-sp _ = λ ()
  after {lt TLBrace} ys tok-sp _ = λ ()
  after {lt TMinus}  ys tok-nl _ = λ ()
  after {lt TLBrace} ys tok-nl _ = λ ()
  after {lt (TWord _)} ys (tok-tok _) _ = tt
  after {lt (TWord _)} ys tok-sp _ = tt
  after {lt (TWord _)} ys tok-nl _ = tt
  after {lt (TInt _)} ys (tok-tok _) _ = tt
  after {lt (TInt _)} ys tok-sp _ = tt
  after {lt (TInt _)} ys tok-nl _ = tt
  after {lt (TFloat _ _ _)} ys (tok-tok _) _ = tt
  after {lt (TFloat _ _ _)} ys tok-sp _ = tt
  after {lt (TFloat _ _ _)} ys tok-nl _ = tt
  after {lt (TString _)} ys (tok-tok _) _ = tt
  after {lt (TString _)} ys tok-sp _ = tt
  after {lt (TString _)} ys tok-nl _ = tt
  after {lt TLParen} ys (tok-tok _) _ = tt
  after {lt TLParen} ys tok-sp _ = tt
  after {lt TLParen} ys tok-nl _ = tt
  after {lt TRParen} ys (tok-tok _) _ = tt
  after {lt TRParen} ys tok-sp _ = tt
  after {lt TRParen} ys tok-nl _ = tt
  after {lt TRBrace} ys (tok-tok _) _ = tt
  after {lt TRBrace} ys tok-sp _ = tt
  after {lt TRBrace} ys tok-nl _ = tt
  after {lt TColon} ys (tok-tok _) _ = tt
  after {lt TColon} ys tok-sp _ = tt
  after {lt TColon} ys tok-nl _ = tt
  after {lt TEquals} ys (tok-tok _) _ = tt
  after {lt TEquals} ys tok-sp _ = tt
  after {lt TEquals} ys tok-nl _ = tt
  after {lt TArrow} ys (tok-tok _) _ = tt
  after {lt TArrow} ys tok-sp _ = tt
  after {lt TArrow} ys tok-nl _ = tt
  after {lt TCaret1} ys (tok-tok _) _ = tt
  after {lt TCaret1} ys tok-sp _ = tt
  after {lt TCaret1} ys tok-nl _ = tt
  after {lt TCaret0} ys (tok-tok _) _ = tt
  after {lt TCaret0} ys tok-sp _ = tt
  after {lt TCaret0} ys tok-nl _ = tt
  after {lt TCaretW} ys (tok-tok _) _ = tt
  after {lt TCaretW} ys tok-sp _ = tt
  after {lt TCaretW} ys tok-nl _ = tt
  after {lt TLambda} ys (tok-tok _) _ = tt
  after {lt TLambda} ys tok-sp _ = tt
  after {lt TLambda} ys tok-nl _ = tt
  after {lt TComma} ys (tok-tok _) _ = tt
  after {lt TComma} ys tok-sp _ = tt
  after {lt TComma} ys tok-nl _ = tt
  after {lt TSemicolon} ys (tok-tok _) _ = tt
  after {lt TSemicolon} ys tok-sp _ = tt
  after {lt TSemicolon} ys tok-nl _ = tt
  after {lt TAt} ys (tok-tok _) _ = tt
  after {lt TAt} ys tok-sp _ = tt
  after {lt TAt} ys tok-nl _ = tt
  after {lt TPipe} ys (tok-tok _) _ = tt
  after {lt TPipe} ys tok-sp _ = tt
  after {lt TPipe} ys tok-nl _ = tt
  after {lt TDot} ys (tok-tok _) _ = tt
  after {lt TDot} ys tok-sp _ = tt
  after {lt TDot} ys tok-nl _ = tt
  after {lt TPlus} ys (tok-tok _) _ = tt
  after {lt TPlus} ys tok-sp _ = tt
  after {lt TPlus} ys tok-nl _ = tt
  after {lt TStar} ys (tok-tok _) _ = tt
  after {lt TStar} ys tok-sp _ = tt
  after {lt TStar} ys tok-nl _ = tt
  after {lt TSlash} ys (tok-tok _) _ = tt
  after {lt TSlash} ys tok-sp _ = tt
  after {lt TSlash} ys tok-nl _ = tt
  after {lt TPercent} ys (tok-tok _) _ = tt
  after {lt TPercent} ys tok-sp _ = tt
  after {lt TPercent} ys tok-nl _ = tt
  after {lt TAmpersand} ys (tok-tok _) _ = tt
  after {lt TAmpersand} ys tok-sp _ = tt
  after {lt TAmpersand} ys tok-nl _ = tt
  after {lt TLt} ys (tok-tok _) _ = tt
  after {lt TLt} ys tok-sp _ = tt
  after {lt TLt} ys tok-nl _ = tt
  after {lt TLe} ys (tok-tok _) _ = tt
  after {lt TLe} ys tok-sp _ = tt
  after {lt TLe} ys tok-nl _ = tt
  after {lt TGt} ys (tok-tok _) _ = tt
  after {lt TGt} ys tok-sp _ = tt
  after {lt TGt} ys tok-nl _ = tt
  after {lt TGe} ys (tok-tok _) _ = tt
  after {lt TGe} ys tok-sp _ = tt
  after {lt TGe} ys tok-nl _ = tt
  after {lt TEqEq} ys (tok-tok _) _ = tt
  after {lt TEqEq} ys tok-sp _ = tt
  after {lt TEqEq} ys tok-nl _ = tt
  after {lt TNeq} ys (tok-tok _) _ = tt
  after {lt TNeq} ys tok-sp _ = tt
  after {lt TNeq} ys tok-nl _ = tt
  after {lt TBang} ys (tok-tok _) _ = tt
  after {lt TBang} ys tok-sp _ = tt
  after {lt TBang} ys tok-nl _ = tt
  after {lt TNewline} ys (tok-tok _) _ = tt
  after {lt TNewline} ys tok-sp _ = tt
  after {lt TNewline} ys tok-nl _ = tt
  after {lt TEOF} ys (tok-tok _) _ = tt
  after {lt TEOF} ys tok-sp _ = tt
  after {lt TEOF} ys tok-nl _ = tt
  after {lsp} ys _ _ = tt
  after {lnl} ys _ _ = tt
  after {(lind _)} ys _ _ = tt
  after {lcm _} ys _ _ = tt

  head-valid : ∀ {y ys} → WS (y ∷ ys) → Valid y
  head-valid (ws-1 v _)   = v
  head-valid (ws-∷ v _ _) = v

-- | Well-formed lexemes without comments hold no comment start.
np-ws : ∀ xs → WS xs → All NotLcm xs → NoPair (concatMap chars xs)
np-ws []           ws-[]         []        = np-[]
np-ws (x ∷ [])     (ws-1 v _)    (n ∷ [])  = lexeme-np x [] v n (last-after x) np-[]
  where
    last-after : ∀ x → After x []
    last-after (lt TMinus) = λ ()
    last-after (lt TLBrace) = λ ()
    last-after (lt (TWord _)) = tt
    last-after (lt (TInt _)) = tt
    last-after (lt (TFloat _ _ _)) = tt
    last-after (lt (TString _)) = tt
    last-after (lt TLParen) = tt
    last-after (lt TRParen) = tt
    last-after (lt TRBrace) = tt
    last-after (lt TColon) = tt
    last-after (lt TEquals) = tt
    last-after (lt TArrow) = tt
    last-after (lt TCaret1) = tt
    last-after (lt TCaret0) = tt
    last-after (lt TCaretW) = tt
    last-after (lt TLambda) = tt
    last-after (lt TComma) = tt
    last-after (lt TSemicolon) = tt
    last-after (lt TAt) = tt
    last-after (lt TPipe) = tt
    last-after (lt TDot) = tt
    last-after (lt TPlus) = tt
    last-after (lt TStar) = tt
    last-after (lt TSlash) = tt
    last-after (lt TPercent) = tt
    last-after (lt TAmpersand) = tt
    last-after (lt TLt) = tt
    last-after (lt TLe) = tt
    last-after (lt TGt) = tt
    last-after (lt TGe) = tt
    last-after (lt TEqEq) = tt
    last-after (lt TNeq) = tt
    last-after (lt TBang) = tt
    last-after (lt TNewline) = tt
    last-after (lt TEOF) = tt
    last-after lsp = tt
    last-after lnl = tt
    last-after (lind _) = tt
    last-after (lcm _) = tt
np-ws (x ∷ y ∷ ys) (ws-∷ v a w) (n ∷ ns) =
  lexeme-np x (concatMap chars (y ∷ ys)) v n (after (concatMap chars ys) a (head-valid w)) (np-ws (y ∷ ys) w ns)


------------------------------------------------------------------------
-- The layout of a document without comments writes none
------------------------------------------------------------------------

private
  Clean : St → Set
  Clean σ = All NotLcm (St.out σ) × St.ends σ ≡ []

  put-clean : ∀ x n σ → NotLcm x → Clean σ → Clean (put x n σ)
  put-clean x n (st o c (just i) e) nx (a , e≡) = nx ∷ tt ∷ a , e≡
  put-clean x n (st o c nothing e)  nx (a , e≡) = nx ∷ a , e≡

  space-clean : ∀ σ → Clean σ → Clean (space σ)
  space-clean (st o c (just i) e) cl = cl
  space-clean (st o c nothing e)  cl = put-clean lsp 1 (st o c nothing e) tt cl

  apart-clean : ∀ t u o c e b → Clean (st (lt u ∷ o) c nothing e)
              → Clean (if b then put (lt t) (Data.String.length (spell t)) (space (st (lt u ∷ o) c nothing e))
                       else put (lt t) (Data.String.length (spell t)) (st (lt u ∷ o) c nothing e))
  apart-clean t u o c e true  cl =
    put-clean (lt t) (Data.String.length (spell t)) (space (st (lt u ∷ o) c nothing e)) tt (space-clean (st (lt u ∷ o) c nothing e) cl)
  apart-clean t u o c e false cl = put-clean (lt t) (Data.String.length (spell t)) (st (lt u ∷ o) c nothing e) tt cl

  token-clean : ∀ t σ → Clean σ → Clean (token t σ)
  token-clean t σ@(st [] c p e) cl = put-clean (lt t) (Data.String.length (spell t)) σ tt cl
  token-clean t (st (lt u ∷ o) c nothing e) cl = apart-clean t u o c e (apart u t) cl
  token-clean t σ@(st (lt u ∷ o) c (just i) e) cl = put-clean (lt t) (Data.String.length (spell t)) σ tt cl
  token-clean t σ@(st (lsp ∷ o) c p e) cl = put-clean (lt t) (Data.String.length (spell t)) σ tt cl
  token-clean t σ@(st (lnl ∷ o) c p e) cl = put-clean (lt t) (Data.String.length (spell t)) σ tt cl
  token-clean t σ@(st (lind j ∷ o) c p e) cl = put-clean (lt t) (Data.String.length (spell t)) σ tt cl
  token-clean t (st (lcm x ∷ o) c p e) (() ∷ _ , _)

  trim-clean : ∀ o → All NotLcm o → All NotLcm (trim o)
  trim-clean []          a       = a
  trim-clean (lsp ∷ o)   (_ ∷ a) = trim-clean o a
  trim-clean (lt _ ∷ o)  a       = a
  trim-clean (lnl ∷ o)   a       = a
  trim-clean (lind _ ∷ o) a      = a
  trim-clean (lcm _ ∷ o) a       = a

  brk-clean : ∀ i σ → Clean σ → Clean (brk i σ)
  brk-clean i (st o c (just _) .[]) (a , refl) = a , refl
  brk-clean i (st o c nothing .[])  (a , refl) = tt ∷ trim-clean o a , refl

  blank-clean : ∀ i σ → Clean σ → Clean (blankLine i σ)
  blank-clean i (st o c (just j) .[]) (a , refl) = fresh o a
    where
      fresh : ∀ o → All NotLcm o → Clean (blankLine i (st o c (just j) []))
      fresh []      a = [] , refl
      fresh (x ∷ o) a = tt ∷ a , refl
  blank-clean i (st o c nothing .[])  (a , refl) = tt ∷ tt ∷ trim-clean o a , refl

layout-clean : ∀ d i f σ → NoNotes d → Clean σ → Clean (layout i f d σ)
layout-clean empty i f σ nn-empty cl = cl
layout-clean (tk t) i f σ nn-tk cl = token-clean t σ cl
layout-clean sp i f σ nn-sp cl = space-clean σ cl
layout-clean line i true  σ nn-line cl = space-clean σ cl
layout-clean line i false σ nn-line cl = brk-clean i σ cl
layout-clean newline i f σ nn-newline cl = brk-clean i σ cl
layout-clean blank zero    f σ nn-blank cl = blank-clean zero σ cl
layout-clean blank (suc i) f σ nn-blank cl = brk-clean (suc i) σ cl
layout-clean (a <> b) i f σ (nn-<> na nb) cl = layout-clean b i f _ nb (layout-clean a i f σ na cl)
layout-clean (nest n d) i f σ (nn-nest nd) cl = layout-clean d (i + n) f σ nd cl
  where open import Data.Nat using (_+_)
layout-clean (group d) i true  σ (nn-group nd) cl = layout-clean d i true σ nd cl
layout-clean (group d) i false σ (nn-group nd) cl = layout-clean d i _ σ nd cl

private
  allRev : ∀ {A : Set} {P : A → Set} {acc xs} → All P acc → All P xs → All P (Data.List.reverseAcc acc xs)
  allRev pa []       = pa
  allRev pa (p ∷ ps) = allRev (p ∷ pa) ps

-- | …and so its lexemes hold no comment.
lexemes-clean : ∀ d → NoNotes d → All NotLcm (lexemes d)
lexemes-clean d nd =
  allRev [] (proj₁ (brk-clean 0 (layout 0 false d (st [] 0 (just 0) [])) (layout-clean d 0 false (st [] 0 (just 0) []) nd ([] , refl))))

------------------------------------------------------------------------
-- The lexer finds no comment where none starts
------------------------------------------------------------------------

private
  digits-np : ∀ {cs ds r} → Data.Product.Σ _ (λ _ → Once.Spec.Surface.Lexing.Digits cs ds r) → NoPair cs → NoPair r
  digits-np (_ , Once.Spec.Surface.Lexing.dg-end) p = p
  digits-np (_ , Once.Spec.Surface.Lexing.dg-stop _) p = p
  digits-np (_ , Once.Spec.Surface.Lexing.dg-more _ d) p = digits-np (tt , d) (np-tail p)

  ident-np : ∀ {cs i r} → Once.Spec.Surface.Lexing.IdentRest cs i r → NoPair cs → NoPair r
  ident-np Once.Spec.Surface.Lexing.id-end p = p
  ident-np (Once.Spec.Surface.Lexing.id-stop _) p = p
  ident-np (Once.Spec.Surface.Lexing.id-more _ d) p = ident-np d (np-tail p)

  frac-np : ∀ {r f r′} → Once.Spec.Surface.Lexing.Fraction r f r′ → NoPair r → NoPair r′
  frac-np (Once.Spec.Surface.Lexing.fraction _ d) p = digits-np (tt , d) (np-tail (np-tail p))

  string-np : ∀ {cs s r} → Once.Spec.Surface.Lexing.StringBody cs s r → NoPair cs → NoPair r
  string-np Once.Spec.Surface.Lexing.sb-close p = np-tail p
  string-np (Once.Spec.Surface.Lexing.sb-esc _ d) p = string-np d (np-tail (np-tail p))
  string-np (Once.Spec.Surface.Lexing.sb-char _ _ d) p = string-np d (np-tail p)

  drop1-np : ∀ cs → NoPair cs → NoPair (PL.drop1 cs)
  drop1-np []       p = p
  drop1-np (_ ∷ cs) p = np-tail p

Rec : List Char → Set
Rec cs = ∀ {y} → y < suc (length cs) → Acc _<_ y

mutual
  -- | Without a comment start, the comment-keeping lexer finds no comment.
  noc-WF : ∀ cs off (a : Acc _<_ (length cs)) → NoPair cs → All NoComment (items-WF cs off a)
  noc-WF []       off _         _  = nc-tok ∷ []
  noc-WF (c ∷ cs) off (acc rec) np = noc-head c cs off rec (PL.headK c) (hview refl) np

  noc-head : ∀ c cs off (rec : Rec cs) k → HeadView c k → NoPair (c ∷ cs) → All NoComment (it-head c cs off rec k)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-space np = noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-tab np = noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-cr np = noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-nl np = noc-nl cs off rec (PL.nlIndent cs) (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-caret np = noc-caret cs off rec (PL.caretClass cs) (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-dash np = noc-minus cs off rec (PL.dashClass cs) (dview refl) np
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-lbrace np = noc-lbrace cs off rec (PL.isDashHead cs) (dheadview refl) np
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-lt np = noc-op2 cs off rec _ _ (PL.isEqHead cs) (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-gt np = noc-op2 cs off rec _ _ (PL.isEqHead cs) (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-eq np = noc-op2 cs off rec _ _ (PL.isEqHead cs) (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-bang np = noc-op2 cs off rec _ _ (PL.isEqHead cs) (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-lparen np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-rparen np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-rbrace np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-colon np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-lambda np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-comma np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-semi np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-at np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-pipe np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-plus np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-star np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-slash np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-pct np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-amp np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-dot np = nc-tok ∷ noc-WF cs _ _ (np-tail np)
  noc-head c cs off rec _ Once.Adequacy.SpecLexing.hv-quote np = noc-str cs off rec (PL.collectStringB cs) refl (np-tail np)
  noc-head c cs off rec _ (Once.Adequacy.SpecLexing.hv-gen _) np = noc-gen c cs off rec (isDigit c) (isIdentStart c) np

  noc-nl : ∀ cs off (rec : Rec cs) b → NoPair cs → All NoComment (it-nl cs off rec b)
  noc-nl cs off rec true  np = nc-cont ∷ noc-WF cs _ _ np
  noc-nl cs off rec false np = nc-tok ∷ noc-WF cs _ _ np

  noc-op2 : ∀ cs off (rec : Rec cs) t2 t1 b → NoPair cs → All NoComment (it-op2 cs off rec t2 t1 b)
  noc-op2 cs off rec t2 t1 true  np = nc-tok ∷ noc-WF (PL.drop1 cs) _ _ (drop1-np cs np)
  noc-op2 cs off rec t2 t1 false np = nc-tok ∷ noc-WF cs _ _ np

  noc-caret : ∀ cs off (rec : Rec cs) k → NoPair cs → All NoComment (it-caret cs off rec k)
  noc-caret cs off rec PL.c-1   np = nc-tok ∷ noc-WF (PL.drop1 cs) _ _ (drop1-np cs np)
  noc-caret cs off rec PL.c-0   np = nc-tok ∷ noc-WF (PL.drop1 cs) _ _ (drop1-np cs np)
  noc-caret cs off rec PL.c-w   np = nc-tok ∷ noc-WF (PL.drop1 cs) _ _ (drop1-np cs np)
  noc-caret cs off rec PL.c-gen np = noc-WF cs _ _ np

  noc-minus : ∀ cs off (rec : Rec cs) d → DashView cs d → NoPair ('-' ∷ cs) → All NoComment (it-minus cs off rec d)
  noc-minus .('-' ∷ _) off rec _ dv-comment (np-∷ ¬b _) = ⊥-elim (¬b bad-dd)
  noc-minus .('>' ∷ _) off rec _ dv-arrow   np = nc-tok ∷ noc-WF _ _ _ (np-tail (np-tail np))
  noc-minus cs off rec _ (dv-minus _ _) np = nc-tok ∷ noc-WF cs _ _ (np-tail np)

  noc-lbrace : ∀ cs off (rec : Rec cs) b → HeadIs '-' cs b → NoPair ('{' ∷ cs) → All NoComment (it-lbrace cs off rec b)
  noc-lbrace .('-' ∷ _) off rec _ hi-yes (np-∷ ¬b _) = ⊥-elim (¬b bad-bd)
  noc-lbrace cs off rec _ (hi-no _) np = nc-tok ∷ noc-WF cs _ _ (np-tail np)

  noc-str : ∀ cs off (rec : Rec cs) m → PL.collectStringB cs ≡ m → NoPair cs → All NoComment (it-str cs off rec m)
  noc-str cs off rec (just (s , rest , bnd)) eq np = nc-tok ∷ noc-WF rest _ _ (string-np (string-sound cs eq) np)
  noc-str cs off rec nothing eq np = []

  noc-gen : ∀ c cs off (rec : Rec cs) b₁ b₂ → NoPair (c ∷ cs) → All NoComment (it-gen c cs off rec b₁ b₂)
  noc-gen c cs off rec true _ np =
    noc-num c cs off rec _ _ _ (PL.collectFracB (proj₁ (proj₂ (PL.collectDigitsB cs)))) refl
      (digits-np (tt , digits-sound cs) (np-tail np))
  noc-gen c cs off rec false true np = nc-tok ∷ noc-WF _ _ _ (ident-np (ident-sound cs) (np-tail np))
  noc-gen c cs off rec false false np = noc-WF cs _ _ (np-tail np)

  noc-num : ∀ c cs off (rec : Rec cs) ds rest (bnd : length rest Data.Nat.≤ length cs) m → PL.collectFracB rest ≡ m → NoPair rest
          → All NoComment (it-num c cs off rec ds rest bnd m)
  noc-num c cs off rec ds rest bnd (just (f , rest′ , fb)) eq np = nc-tok ∷ noc-WF rest′ _ _ (frac-np (frac-sound rest eq) np)
  noc-num c cs off rec ds rest bnd nothing eq np = nc-tok ∷ noc-WF rest _ _ np

------------------------------------------------------------------------
-- Formatting twice
------------------------------------------------------------------------

private
  oks : ∀ {ds} → All Once.Format.Proof.Printable.PD ds → All Once.Format.Proof.Module.DeclOK ds
  oks []       = []
  oks (p ∷ ps) = decl-ok _ p ∷ oks ps

  -- The formatter's output of a module without trivia holds no comment.
  out-quiet : ∀ ds → All Once.Format.Proof.Printable.PD ds
            → All NoComment (lexItems (toList (format (mkModule ds) [])))
  out-quiet ds pds =
    subst (λ cs → All NoComment (items-WF cs 0 (Data.Nat.Induction.<-wellFounded (length cs))))
      (sym (toList∘fromList (concatMap chars (lexemes D))))
      (noc-WF _ 0 _ (np-ws (lexemes D) (module-ws ds [] (oks pds)) (lexemes-clean D (Canon.Bare.pdecls-nn nothing ds 0))))
    where
      D = proj₁ (pmodule (mkModule ds) [] 0)

-- | For a text without comments, formatting twice is formatting once.
idempotent : DigitBound → ∀ text m → parseStrict text ≡ inj₂ m → All NoComment (lexItems (toList text))
           → formatSource text ≡ inj₂ (format m (lexItems (toList text)))
             × formatSource (format m (lexItems (toList text))) ≡ inj₂ (format m (lexItems (toList text)))
idempotent bound text (mkModule ds) eq nc with parsed-wf bound {text} {mkModule ds}
                                          (Once.Adequacy.SpecGrammar.Decl.parses→ {text} (Once.Adequacy.FrontEndBridge.parseStrict-sound text _ eq))
... | wfs , pds =
  cong (formatParsed text) eq ,
  trans (cong (formatParsed out) ps)
    (cong inj₂ (trans (format-quiet (mkModule ds) _ (subst (λ o → All NoComment (lexItems (toList o))) (sym q₁) (out-quiet ds pds)))
                      (sym q₁)))
  where
    out = format (mkModule ds) (lexItems (toList text))
    q₁ : out ≡ format (mkModule ds) []
    q₁ = format-quiet (mkModule ds) _ nc
    ps : parseStrict out ≡ inj₂ (mkModule ds)
    ps = proj₂ (proj₂ (roundtrip bound text (mkModule ds) eq))
