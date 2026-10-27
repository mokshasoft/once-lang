-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Written — the comments a layout writes hold the
-- document's comment words, in order (plan 0.124 step 4.5).
--
-- The words written so far, then those of the end-of-line comments waiting
-- for the line's end, are the words of what the layout has read (`layout-CW`):
-- a comment ends its line after the comments already waiting on it, so none
-- overtakes another. A text's words (`cwords`, a comment's text without its
-- trailing blanks) read from a formatted text are its document's
-- (`render-words`).
------------------------------------------------------------------------

module Once.Format.Proof.Written where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse; concatMap; map; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse; reverse-++; reverse-involutive)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; fromList; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Postulates using (toList∘fromList)
import Once.Format.Doc as D
open import Once.Format.Doc using (Doc; Lexeme; lt; lsp; lnl; lind; lcm; St; st; put; space; token; trim; brk;
  blankLine; paragraph; fill; layout; lexemes; render; chars; joined; dashed; lineComment; apart; column; fits; flatWidth;
  empty; tk; sp; cmt; para; line; newline; blank; eol; _<>_; nest; group)
open import Once.Format.Comment using (blankish)
open import Once.Format.Spell using (spell)
import Data.String as Str
open import Once.Format.Print using (trimEnd; dropLead)
open import Once.Format.Lex using (Item; tok; comment; cont; lexItems)
open import Once.Format.Proof.Items using (EItem; etok; ecomment; econt; erase; items-complete)
open import Once.Format.Proof.ItemsLex using (itemsL; items-ws)
open import Once.Format.Proof.Lexing using (WS)
open import Once.Format.Proof.Words

------------------------------------------------------------------------
-- The words of a text
------------------------------------------------------------------------

-- | A comment's words: its text without trailing blanks.
cw : String → List (List Char)
cw c = Mn (trimEnd c)

-- | The words of a text's comments, in order.
cwords : List Item → List (List Char)
cwords []              = []
cwords (tok _ ∷ is)     = cwords is
cwords (comment c ∷ is) = cw c ++ cwords is
cwords (cont ∷ is)      = cwords is

cwordsE : List EItem → List (List Char)
cwordsE []               = []
cwordsE (etok _ ∷ is)     = cwordsE is
cwordsE (ecomment c ∷ is) = cw c ++ cwordsE is
cwordsE (econt ∷ is)      = cwordsE is

cwords-erase : ∀ is → cwords is ≡ cwordsE (map erase is)
cwords-erase []              = refl
cwords-erase (tok _ ∷ is)     = cwords-erase is
cwords-erase (comment c ∷ is) = cong (cw c ++_) (cwords-erase is)
cwords-erase (cont ∷ is)      = cwords-erase is

------------------------------------------------------------------------
-- A written comment's words
------------------------------------------------------------------------

private
  dropLead-split : ∀ zs → ∃[ pre ] (zs ≡ pre ++ dropLead zs × All (λ c → blankish c ≡ true) pre)
  dropLead-split []       = [] , refl , []
  dropLead-split (c ∷ cs) =
    ifcase {P = λ z → ∃[ pre ] (c ∷ cs ≡ pre ++ z × All (λ c → blankish c ≡ true) pre)} (blankish c)
      (λ e → let (pre , eq , bs) = dropLead-split cs in c ∷ pre , cong (c ∷_) eq , e ∷ bs)
      (λ _ → [] , refl , [])

  all-rev : ∀ {P : Char → Set} xs → All P xs → All P (reverse xs)
  all-rev []       []       = []
  all-rev (x ∷ xs) (p ∷ ps) = subst (All _) (sym (unfold-reverse x xs)) (all-++ (all-rev xs ps) (p ∷ []))
    where
      all-++ : ∀ {P : Char → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
      all-++ []       qs = qs
      all-++ (p ∷ ps) qs = p ∷ all-++ ps qs

  dw-blanks : ∀ a bs w → All (λ c → blankish c ≡ true) bs → dw (a ++ bs) w ≡ dw a w
  dw-blanks a []       w []       = cong (λ z → dw z w) (++-identityʳ a)
  dw-blanks a (b ∷ bs) w (p ∷ ps) = trans (dw-split a bs w (∨-true (blankish b) p)) (trans (cong (dw a w ++_) (gaps bs ps)) (++-identityʳ _))
    where
      gaps : ∀ bs → All (λ c → blankish c ≡ true) bs → dw bs [] ≡ []
      gaps []       []       = refl
      gaps (b ∷ bs) (p ∷ ps) = trans (dw-gap bs (∨-true (blankish b) p)) (gaps bs ps)

  -- (blanks never start with `--`)
  no-dash : ∀ {r} → All (λ c → blankish c ≡ true) ('-' ∷ r) → ⊥
  no-dash (() ∷ _)

  -- the chars kept, `--` first
  keep-dd : ∀ D bs r → D ++ bs ≡ '-' ∷ '-' ∷ r → All (λ c → blankish c ≡ true) bs → ∃[ s ] D ≡ '-' ∷ '-' ∷ s
  keep-dd (x ∷ y ∷ s) bs r refl _ = s , refl
  keep-dd (x ∷ [])    bs r refl q = ⊥-elim (no-dash q)
  keep-dd []          bs r refl q = ⊥-elim (no-dash q)

-- | A line comment written by the layout: its words, trailing blanks or not.
Mn-dd : ∀ r → cw (fromList ('-' ∷ '-' ∷ r)) ≡ dashWords ('-' ∷ '-' ∷ r)
Mn-dd r with dropLead-split (reverse ('-' ∷ '-' ∷ r))
... | pre , eq , bs = trans (cong (λ z → dashWords (unblock z)) tl) (trans (cong (λ z → dashWords (unblock z)) dd) (sym whole))
  where
    D = dropLead (reverse ('-' ∷ '-' ∷ r))
    tl : toList (trimEnd (fromList ('-' ∷ '-' ∷ r))) ≡ reverse D
    tl = trans (toList∘fromList _) (cong (λ z → reverse (dropLead (reverse z))) (toList∘fromList ('-' ∷ '-' ∷ r)))
    -- the text is what is kept, then the blanks dropped
    split : '-' ∷ '-' ∷ r ≡ reverse D ++ reverse pre
    split = trans (sym (reverse-involutive _)) (trans (cong reverse eq) (reverse-++ pre D))
    kd = keep-dd (reverse D) (reverse pre) r (sym split) (all-rev pre bs)
    dd : reverse D ≡ '-' ∷ '-' ∷ Data.Product.proj₁ kd
    dd = Data.Product.proj₂ kd
    whole : dashWords ('-' ∷ '-' ∷ r) ≡ dashWords ('-' ∷ '-' ∷ Data.Product.proj₁ kd)
    whole = trans (cong dashWords split) (trans (dw-blanks (reverse D) (reverse pre) [] (all-rev pre bs)) (cong dashWords dd))

------------------------------------------------------------------------
-- The layout
------------------------------------------------------------------------

-- | The words of a lexeme.
lw : Lexeme → List (List Char)
lw (lt _)   = []
lw lsp      = []
lw lnl      = []
lw (lind _) = []
lw (lcm c)  = cw (fromList c)

-- | The words written (`out` is last first).
CWo : List Lexeme → List (List Char)
CWo o = concatMap lw (reverse o)

-- | The words written, then those waiting at the line's end.
CW : St → List (List Char)
CW σ = CWo (St.out σ) ++ concatMap DW (St.ends σ)

CWo-cons : ∀ x o → CWo (x ∷ o) ≡ CWo o ++ lw x
CWo-cons x o = trans (cong (concatMap lw) (unfold-reverse x o))
  (trans (cm-++ lw (reverse o) (x ∷ [])) (cong (CWo o ++_) (++-identityʳ (lw x))))

private
  CWo-0 : ∀ x o → lw x ≡ [] → CWo (x ∷ o) ≡ CWo o
  CWo-0 x o e = trans (CWo-cons x o) (trans (cong (CWo o ++_) e) (++-identityʳ (CWo o)))

  put-CW : ∀ x n σ → lw x ≡ [] → CW (put x n σ) ≡ CW σ
  put-CW x n (st o c (just i) e) z = cong (_++ concatMap DW e) (trans (CWo-0 x (lind i ∷ o) z) (CWo-0 (lind i) o refl))
  put-CW x n (st o c nothing e)  z = cong (_++ concatMap DW e) (CWo-0 x o z)

  space-CW : ∀ σ → CW (space σ) ≡ CW σ
  space-CW (st o c (just i) e) = refl
  space-CW (st o c nothing e)  = put-CW lsp 1 (st o c nothing e) refl

  token-CW : ∀ t σ → CW (token t σ) ≡ CW σ
  token-CW t (st [] c p e)                = put-CW (lt t) (Str.length (spell t)) (st [] c p e) refl
  token-CW t (st (lt u ∷ o) c nothing e)  =
    ifcase {P = λ z → CW z ≡ CW (st (lt u ∷ o) c nothing e)} (apart u t)
      (λ _ → trans (put-CW (lt t) (Str.length (spell t)) (space (st (lt u ∷ o) c nothing e)) refl) (space-CW (st (lt u ∷ o) c nothing e)))
      (λ _ → put-CW (lt t) (Str.length (spell t)) (st (lt u ∷ o) c nothing e) refl)
  token-CW t (st (lt u ∷ o) c (just j) e) = put-CW (lt t) (Str.length (spell t)) (st (lt u ∷ o) c (just j) e) refl
  token-CW t (st (lsp ∷ o) c p e)         = put-CW (lt t) (Str.length (spell t)) (st (lsp ∷ o) c p e) refl
  token-CW t (st (lnl ∷ o) c p e)         = put-CW (lt t) (Str.length (spell t)) (st (lnl ∷ o) c p e) refl
  token-CW t (st (lind j ∷ o) c p e)      = put-CW (lt t) (Str.length (spell t)) (st (lind j ∷ o) c p e) refl
  token-CW t (st (lcm x ∷ o) c p e)       = put-CW (lt t) (Str.length (spell t)) (st (lcm x ∷ o) c p e) refl

  trim-CWo : ∀ o → CWo (trim o) ≡ CWo o
  trim-CWo []           = refl
  trim-CWo (lsp ∷ o)    = trans (trim-CWo o) (sym (CWo-0 lsp o refl))
  trim-CWo (lt t ∷ o)   = refl
  trim-CWo (lnl ∷ o)    = refl
  trim-CWo (lind i ∷ o) = refl
  trim-CWo (lcm c ∷ o)  = refl

  -- the end-of-line comments, joined
  lw-joined : ∀ x xs → lw (lcm (joined (x ∷ xs))) ≡ concatMap DW (x ∷ xs)
  lw-joined x []       = trans (Mn-dd (D.oneLine (D.body (toList x)))) (joined-DW (x ∷ []))
  lw-joined x (y ∷ ys) = trans (Mn-dd (D.oneLine (D.body (toList x)) ++ ' ' ∷ joined (y ∷ ys))) (joined-DW (x ∷ y ∷ ys))

  ends-line : ∀ o x xs → CWo (lcm (joined (x ∷ xs)) ∷ o) ≡ CWo o ++ concatMap DW (x ∷ xs)
  ends-line o x xs = trans (CWo-cons _ o) (cong (CWo o ++_) (lw-joined x xs))

brk-CW : ∀ i σ → CW (brk i σ) ≡ CW σ
brk-CW i (st o c (just j) [])       = refl
brk-CW i (st o c (just j) (x ∷ xs)) =
  trans (++-identityʳ _) (trans (CWo-0 lnl (lcm (joined (x ∷ xs)) ∷ lind j ∷ o) refl) (trans (ends-line (lind j ∷ o) x xs) (cong (_++ _) (CWo-0 (lind j) o refl))))
brk-CW i (st o c nothing [])        = cong (_++ []) (trans (CWo-0 lnl (trim o) refl) (trim-CWo o))
brk-CW i (st o c nothing (x ∷ xs))  =
  trans (++-identityʳ _) (trans (CWo-0 lnl (lcm (joined (x ∷ xs)) ∷ lsp ∷ trim o) refl) (trans (ends-line (lsp ∷ trim o) x xs)
    (cong (_++ _) (trans (CWo-0 lsp (trim o) refl) (trim-CWo o)))))

brk-ends : ∀ i σ → St.ends (brk i σ) ≡ []
brk-ends i (st o c (just j) [])      = refl
brk-ends i (st o c (just j) (_ ∷ _)) = refl
brk-ends i (st o c nothing [])       = refl
brk-ends i (st o c nothing (_ ∷ _))  = refl

private
  snoc-CW : ∀ o c p e s → CW (st o c p (e ++ s ∷ [])) ≡ CW (st o c p e) ++ DW s
  snoc-CW o c p e s = trans (cong (CWo o ++_) (trans (cm-++ DW e (s ∷ [])) (cong (concatMap DW e ++_) (++-identityʳ (DW s)))))
                        (sym (++-assoc (CWo o) (concatMap DW e) (DW s)))

  comment-CW : ∀ i c σ → CW (D.comment i c σ) ≡ CW σ ++ DW c
  comment-CW i x (st o c p e) = trans (brk-CW i (st o c p (e ++ x ∷ []))) (snoc-CW o c p e x)

  blankLine-CW : ∀ i σ → CW (blankLine i σ) ≡ CW σ
  blankLine-CW i (st o c (just j) (x ∷ xs))      = trans (cong (_++ []) (CWo-0 lnl (lnl ∷ lcm (joined (x ∷ xs)) ∷ lind j ∷ o) refl)) (brk-CW i (st o c (just j) (x ∷ xs)))
  blankLine-CW i (st o c nothing [])             = trans (cong (_++ []) (CWo-0 lnl (lnl ∷ trim o) refl)) (brk-CW i (st o c nothing []))
  blankLine-CW i (st o c nothing (x ∷ xs))       = trans (cong (_++ []) (CWo-0 lnl (lnl ∷ lcm (joined (x ∷ xs)) ∷ lsp ∷ trim o) refl)) (brk-CW i (st o c nothing (x ∷ xs)))
  blankLine-CW i (st [] c (just j) [])      = refl
  blankLine-CW i (st (x ∷ o) c (just j) []) = cong (_++ []) (CWo-0 lnl (x ∷ o) refl)

  paragraph-CW : ∀ i ls σ → CW (paragraph i ls σ) ≡ CW σ ++ concatMap (λ l → concatMap DW l) ls
  paragraph-CW i []       σ = sym (++-identityʳ (CW σ))
  paragraph-CW i (l ∷ ls) σ =
    trans (paragraph-CW i ls (D.comment i (fromList (dashed l)) σ))
      (trans (cong (_++ concatMap (λ l → concatMap DW l) ls)
               (trans (comment-CW i (fromList (dashed l)) σ)
                 (cong (CW σ ++_) (trans (cong dashWords (toList∘fromList (dashed l))) (dashed-DW l)))))
        (++-assoc (CW σ) (concatMap DW l) _))

-- | What the layout writes, and what waits at the line's end, holds the
-- document's comment words after those before.
layout-CW : ∀ i f d σ → CW (layout i f d σ) ≡ CW σ ++ DocC d
layout-CW i f empty      σ = sym (++-identityʳ (CW σ))
layout-CW i f (tk t)     σ = trans (token-CW t σ) (sym (++-identityʳ (CW σ)))
layout-CW i f sp         σ = trans (space-CW σ) (sym (++-identityʳ (CW σ)))
layout-CW i f (cmt c)    σ = comment-CW i c σ
layout-CW i f (para ws)  σ =
  trans (paragraph-CW i (fill i (column σ + 2) [] ws) σ)
    (cong (CW σ ++_) (trans (sym (cm-cm DW (λ l → l) (fill i (column σ + 2) [] ws)))
                       (cong (concatMap DW) (fill-words i (column σ + 2) [] ws))))
  where open Data.Nat using (_+_)
layout-CW i true  line   σ = trans (space-CW σ) (sym (++-identityʳ (CW σ)))
layout-CW i false line   σ = trans (brk-CW i σ) (sym (++-identityʳ (CW σ)))
layout-CW i f newline    σ = trans (brk-CW i σ) (sym (++-identityʳ (CW σ)))
layout-CW zero    f blank σ = trans (blankLine-CW zero σ) (sym (++-identityʳ (CW σ)))
layout-CW (suc i) f blank σ = trans (brk-CW (suc i) σ) (sym (++-identityʳ (CW σ)))
layout-CW i f (eol s)    (st o c p e) = snoc-CW o c p e s
layout-CW i f (a <> b)   σ =
  trans (layout-CW i f b (layout i f a σ)) (trans (cong (_++ DocC b) (layout-CW i f a σ)) (++-assoc (CW σ) (DocC a) (DocC b)))
layout-CW i f (nest n d) σ = layout-CW (i Data.Nat.+ n) f d σ
layout-CW i true  (group d) σ = layout-CW i true d σ
layout-CW i false (group d) σ = layout-CW i (fits (column σ) (flatWidth d)) d σ

-- | The lexemes of a document hold its comment words.
lexemes-CW : ∀ d → concatMap lw (lexemes d) ≡ DocC d
lexemes-CW d =
  trans (sym (++-identityʳ _))
    (trans (cong (λ e → CWo (St.out L) ++ concatMap DW e) (sym (brk-ends 0 (layout 0 false d σ₀))))
      (trans (brk-CW 0 (layout 0 false d σ₀)) (layout-CW 0 false d σ₀)))
  where
    σ₀ = st [] 0 (just 0) []
    L = brk 0 (layout 0 false d σ₀)

------------------------------------------------------------------------
-- Read back
------------------------------------------------------------------------

private
  itemsL-words : ∀ p xs → cwordsE (itemsL p xs) ≡ concatMap lw xs
  itemsL-words true  []                  = refl
  itemsL-words false []                  = refl
  itemsL-words true  (lt t ∷ xs)         = itemsL-words false xs
  itemsL-words false (lt t ∷ xs)         = itemsL-words false xs
  itemsL-words true  (lsp ∷ xs)          = itemsL-words false xs
  itemsL-words false (lsp ∷ xs)          = itemsL-words false xs
  itemsL-words true  (lnl ∷ xs)          = itemsL-words true xs
  itemsL-words false (lnl ∷ xs)          = itemsL-words true xs
  itemsL-words true  (lind zero ∷ xs)    = itemsL-words true xs
  itemsL-words false (lind zero ∷ xs)    = itemsL-words false xs
  itemsL-words true  (lind (suc _) ∷ xs) = itemsL-words false xs
  itemsL-words false (lind (suc _) ∷ xs) = itemsL-words false xs
  itemsL-words true  (lcm c ∷ xs)        = cong (cw (fromList c) ++_) (itemsL-words false xs)
  itemsL-words false (lcm c ∷ xs)        = cong (cw (fromList c) ++_) (itemsL-words false xs)

-- | A formatted text's comment words are its document's.
render-words : ∀ d → WS (lexemes d) → cwords (lexItems (toList (render d))) ≡ DocC d
render-words d ws
  rewrite toList∘fromList (concatMap chars (lexemes d))
        | cwords-erase (lexItems (concatMap chars (lexemes d)))
        | items-complete {off = 0} (<-wellFounded (length (concatMap chars (lexemes d)))) (items-ws (lexemes d) ws)
  = trans (itemsL-words false (lexemes d)) (lexemes-CW d)
