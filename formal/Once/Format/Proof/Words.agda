-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Words — the words of a comment, and what the formatter
-- does to them (plan 0.124 step 4.5).
--
-- A comment's words (`dashWords`): its text split at blanks and line ends,
-- each word without the dashes it starts with, empty ones dropped; a block
-- comment's text without `{-` and `-}` (`Mn`). The formatter rewrites a
-- comment's spelling (a block comment as line comments, a paragraph filled
-- to the width, end-of-line comments joined, `--` given a blank after it) but
-- never its words: each rendering step keeps them (`commentRun-words`,
-- `eolText-words`, `lineComment-words`, `joined-words`).
------------------------------------------------------------------------

module Once.Format.Proof.Words where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char)
import Data.Char as Ch
open import Data.List using (List; []; _∷_; _++_; reverse; concatMap; map; replicate; _∷ʳ_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; unfold-reverse; reverse-involutive; reverse-++)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; fromList; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)
import Relation.Nullary

open import Once.Postulates using (toList∘fromList)
open import Once.Format.Comment using (is; blankish; words; wordsGo; emitW; dropBlanks; strip; linesGo; linesOf;
  inside; isBlock; asLine; dropEmpty; trimLines; atLeastOne; commentLines; CLine; prose; verbatim; afterBlank;
  afterDashes; allDash; listItem; dashLine; classifyChars; classify; lineDoc; commentLinesDoc; commentRun;
  eolAfter; eolChars; eolText)
open import Once.Format.Doc using (oneLine; body; lineComment; joined; dashed; fill; width)
import Data.String as Str
open import Data.Nat using (_+_; _≤ᵇ_)

------------------------------------------------------------------------
-- Words
------------------------------------------------------------------------

-- | A blank or a line end: words end at one.
gapC : Char → Bool
gapC c = blankish c ∨ is c '\n'

-- | Dashes at the start dropped.
undash : List Char → List Char
undash []       = []
undash (c ∷ cs) = if is c '-' then undash cs else c ∷ cs

-- A word, unless empty.
keep : List Char → List (List Char) → List (List Char)
keep []       r = r
keep (x ∷ xs) r = (x ∷ xs) ∷ r

-- A word read (last character first), before the words after it.
emitD : List Char → List (List Char) → List (List Char)
emitD w r = keep (undash (reverse w)) r

dw : List Char → List Char → List (List Char)
dw []       w = emitD w []
dw (c ∷ cs) w = if gapC c then emitD w (dw cs []) else dw cs (c ∷ w)

-- | The words of a text.
dashWords : List Char → List (List Char)
dashWords cs = dw cs []

-- | The words of a string.
DW : String → List (List Char)
DW s = dashWords (toList s)

-- | The words of a note (a comment's text): a block comment's inside.
unblock : List Char → List Char
unblock cs = if isBlock cs then inside cs else cs

Mn : String → List (List Char)
Mn s = dashWords (unblock (toList s))

------------------------------------------------------------------------
-- Lemmas on words
------------------------------------------------------------------------

-- | A case on a boolean.
ifcase : ∀ {A : Set} {P : A → Set} (b : Bool) {x y : A} → (b ≡ true → P x) → (b ≡ false → P y)
       → P (if b then x else y)
ifcase true  t f = t refl
ifcase false t f = f refl

-- | A case on a boolean argument.
bcase : ∀ {P : Bool → Set} (b : Bool) → (b ≡ true → P true) → (b ≡ false → P false) → P b
bcase true  t f = t refl
bcase false t f = f refl

if-t : ∀ {A : Set} {b : Bool} {x y : A} → b ≡ true → (if b then x else y) ≡ x
if-t refl = refl

if-f : ∀ {A : Set} {b : Bool} {x y : A} → b ≡ false → (if b then x else y) ≡ y
if-f refl = refl

∨-true : ∀ a {b} → a ≡ true → a ∨ b ≡ true
∨-true .true refl = refl

∨-true′ : ∀ a {b} → b ≡ true → a ∨ b ≡ true
∨-true′ true  _    = refl
∨-true′ false refl = refl

private
  keep-++ : ∀ w r s → keep w r ++ s ≡ keep w (r ++ s)
  keep-++ []       r s = refl
  keep-++ (x ∷ xs) r s = refl

emitD-++ : ∀ w r s → emitD w r ++ s ≡ emitD w (r ++ s)
emitD-++ w = keep-++ (undash (reverse w))

-- | Words split at a gap.
dw-split : ∀ a {b} c w → gapC b ≡ true → dw (a ++ b ∷ c) w ≡ dw a w ++ dw c []
dw-split [] {b} c w g = trans (if-t g) (sym (emitD-++ w [] (dw c [])))
dw-split (x ∷ a) c w g =
  ifcase {P = λ z → z ≡ (if gapC x then emitD w (dw a []) else dw a (x ∷ w)) ++ dw c []} (gapC x)
    (λ e → trans (cong (emitD w) (dw-split a c [] g))
                   (trans (sym (emitD-++ w (dw a []) (dw c []))) (cong (_++ dw c []) (sym (if-t e)))))
    (λ e → trans (dw-split a c (x ∷ w) g) (cong (_++ dw c []) (sym (if-f e))))

-- | A gap at the end changes nothing.
dw-snoc : ∀ a {b} w → gapC b ≡ true → dw (a ++ b ∷ []) w ≡ dw a w
dw-snoc a w g = trans (dw-split a [] w g) (++-identityʳ (dw a w))

-- | Nor one at the start.
dw-gap : ∀ {b} cs → gapC b ≡ true → dw (b ∷ cs) [] ≡ dw cs []
dw-gap cs g = if-t g

private
  undash-dash : ∀ v → undash ('-' ∷ v) ≡ undash v
  undash-dash v = refl

  emitD-dash : ∀ w r → emitD (w ++ '-' ∷ []) r ≡ emitD w r
  emitD-dash w r = cong (λ z → keep (undash z) r) (reverse-++ w ('-' ∷ []))

  dw-dashacc : ∀ cs w → dw cs (w ++ '-' ∷ []) ≡ dw cs w
  dw-dashacc []       w = emitD-dash w []
  dw-dashacc (c ∷ cs) w =
    ifcase {P = λ z → z ≡ (if gapC c then emitD w (dw cs []) else dw cs (c ∷ w))} (gapC c)
      (λ e → trans (emitD-dash w (dw cs [])) (sym (if-t e)))
      (λ e → trans (dw-dashacc cs (c ∷ w)) (sym (if-f e)))

-- | A dash at the start of the text changes nothing.
dashWords-dash : ∀ cs → dashWords ('-' ∷ cs) ≡ dashWords cs
dashWords-dash cs = dw-dashacc cs []

-- | `-- ` at the start changes nothing.
dashWords-dd : ∀ cs → dashWords ('-' ∷ '-' ∷ ' ' ∷ cs) ≡ dashWords cs
dashWords-dd cs = trans (dashWords-dash ('-' ∷ ' ' ∷ cs)) (dashWords-dash (' ' ∷ cs))

-- | Nor `--`, whatever follows.
dashWords-d2 : ∀ cs → dashWords ('-' ∷ '-' ∷ cs) ≡ dashWords cs
dashWords-d2 cs = trans (dashWords-dash ('-' ∷ cs)) (dashWords-dash cs)

private
  dw-[] : dashWords [] ≡ []
  dw-[] = refl

-- | Line ends as blanks.
dw-oneLine : ∀ cs w → dw (oneLine cs) w ≡ dw cs w
dw-oneLine []       w = refl
dw-oneLine (c ∷ cs) w = go (is c '\n') refl
  where
    go : ∀ b → is c '\n' ≡ b → dw ((if b then ' ' else c) ∷ oneLine cs) w ≡ dw (c ∷ cs) w
    go true  e = trans (cong (emitD w) (dw-oneLine cs [])) (sym (if-t (∨-true′ (blankish c) e)))
    go false _ = cong₂ (λ x y → if gapC c then emitD w x else y) (dw-oneLine cs []) (dw-oneLine cs (c ∷ w))

-- | A character test that holds is an equation.
is-eq : ∀ c d → is c d ≡ true → c ≡ d
is-eq c d = dec-true (c Ch.≟ d)
  where
    dec-true : ∀ {P : Set} (q : Relation.Nullary.Dec P) → does q ≡ true → P
    dec-true (Relation.Nullary.yes p) _ = p
    dec-true (Relation.Nullary.no _) ()

∧-l : ∀ a {b} → a ∧ b ≡ true → a ≡ true
∧-l true _ = refl

∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
∧-r true e = e

------------------------------------------------------------------------
-- Lists of words
------------------------------------------------------------------------

module _ {A B : Set} where
  cm-++ : ∀ (f : A → List B) xs ys → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
  cm-++ f []       ys = refl
  cm-++ f (x ∷ xs) ys = trans (cong (f x ++_) (cm-++ f xs ys)) (sym (++-assoc (f x) _ _))

  cm-cong : ∀ {f g : A → List B} → (∀ x → f x ≡ g x) → ∀ xs → concatMap f xs ≡ concatMap g xs
  cm-cong h []       = refl
  cm-cong h (x ∷ xs) = cong₂ _++_ (h x) (cm-cong h xs)

module _ {A B C : Set} where
  cm-map : ∀ (f : B → List C) (g : A → B) xs → concatMap f (map g xs) ≡ concatMap (λ x → f (g x)) xs
  cm-map f g []       = refl
  cm-map f g (x ∷ xs) = cong (f (g x) ++_) (cm-map f g xs)

  cm-cm : ∀ (f : B → List C) (g : A → List B) xs → concatMap f (concatMap g xs) ≡ concatMap (λ x → concatMap f (g x)) xs
  cm-cm f g []       = refl
  cm-cm f g (x ∷ xs) = trans (cm-++ f (g x) (concatMap g xs)) (cong (concatMap f (g x) ++_) (cm-cm f g xs))

------------------------------------------------------------------------
-- What the comment renderer does keeps the words
------------------------------------------------------------------------

private
  emitW-DW : ∀ w r → concatMap DW (emitW w r) ≡ dashWords (reverse w) ++ concatMap DW r
  emitW-DW []       r = refl
  emitW-DW (x ∷ xs) r = cong (_++ concatMap DW r) (cong dashWords (toList∘fromList (reverse (x ∷ xs))))

  rev-snoc : ∀ (w : List Char) c cs → reverse (c ∷ w) ++ cs ≡ reverse w ++ c ∷ cs
  rev-snoc w c cs = trans (cong (_++ cs) (unfold-reverse c w)) (++-assoc (reverse w) (c ∷ []) cs)

  wordsGo-DW : ∀ cs w → concatMap DW (wordsGo cs w) ≡ dashWords (reverse w ++ cs)
  wordsGo-DW []       w = trans (emitW-DW w []) (trans (++-identityʳ _) (cong dashWords (sym (++-identityʳ (reverse w)))))
  wordsGo-DW (c ∷ cs) w =
    ifcase {P = λ z → concatMap DW z ≡ dashWords (reverse w ++ c ∷ cs)} (blankish c)
      (λ e → trans (emitW-DW w (wordsGo cs [])) (trans (cong (dashWords (reverse w) ++_) (wordsGo-DW cs []))
               (sym (dw-split (reverse w) cs [] (∨-true (blankish c) e)))))
      (λ e → trans (wordsGo-DW cs (c ∷ w)) (cong dashWords (rev-snoc w c cs)))

-- | Filling a text's words keeps them.
words-DW : ∀ cs → concatMap DW (words cs) ≡ dashWords cs
words-DW cs = wordsGo-DW cs []

private
  linesGo-DW : ∀ cs l → concatMap dashWords (linesGo cs l) ≡ dashWords (reverse l ++ cs)
  linesGo-DW []       l = trans (++-identityʳ _) (cong dashWords (sym (++-identityʳ (reverse l))))
  linesGo-DW (c ∷ cs) l =
    ifcase {P = λ z → concatMap dashWords z ≡ dashWords (reverse l ++ c ∷ cs)} (is c '\n')
      (λ e → trans (cong (dashWords (reverse l) ++_) (linesGo-DW cs []))
               (sym (dw-split (reverse l) cs [] (∨-true′ (blankish c) e))))
      (λ e → trans (linesGo-DW cs (c ∷ l)) (cong dashWords (rev-snoc l c cs)))

  dropBlanks-DW : ∀ cs → dashWords (dropBlanks cs) ≡ dashWords cs
  dropBlanks-DW []       = refl
  dropBlanks-DW (c ∷ cs) =
    ifcase {P = λ z → dashWords z ≡ dashWords (c ∷ cs)} (blankish c)
      (λ e → trans (dropBlanks-DW cs) (sym (dw-gap cs (∨-true (blankish c) e))))
      (λ _ → refl)

  rev-dropBlanks : ∀ xs → dashWords (reverse (dropBlanks xs)) ≡ dashWords (reverse xs)
  rev-dropBlanks []       = refl
  rev-dropBlanks (x ∷ xs) =
    ifcase {P = λ z → dashWords (reverse z) ≡ dashWords (reverse (x ∷ xs))} (blankish x)
      (λ e → trans (rev-dropBlanks xs)
               (sym (trans (cong dashWords (unfold-reverse x xs)) (dw-snoc (reverse xs) [] (∨-true (blankish x) e)))))
      (λ _ → refl)

-- | Blanks at both ends are no words.
strip-DW : ∀ cs → dashWords (strip cs) ≡ dashWords cs
strip-DW cs = trans (rev-dropBlanks (reverse (dropBlanks cs)))
  (trans (cong dashWords (reverse-involutive (dropBlanks cs))) (dropBlanks-DW cs))

private
  dropEmpty-DW : ∀ ls → concatMap dashWords (dropEmpty ls) ≡ concatMap dashWords ls
  dropEmpty-DW []             = refl
  dropEmpty-DW ([] ∷ ls)      = dropEmpty-DW ls
  dropEmpty-DW ((x ∷ xs) ∷ ls) = refl

  rev-dropEmpty : ∀ ls → concatMap dashWords (reverse (dropEmpty ls)) ≡ concatMap dashWords (reverse ls)
  rev-dropEmpty []              = refl
  rev-dropEmpty ([] ∷ ls)       =
    trans (rev-dropEmpty ls) (sym (trans (cong (concatMap dashWords) (unfold-reverse [] ls))
      (trans (cm-++ dashWords (reverse ls) ([] ∷ [])) (++-identityʳ _))))
  rev-dropEmpty ((x ∷ xs) ∷ ls) = refl

  trimLines-DW : ∀ ls → concatMap dashWords (trimLines ls) ≡ concatMap dashWords ls
  trimLines-DW ls = trans (rev-dropEmpty (reverse (dropEmpty ls)))
    (trans (cong (concatMap dashWords) (reverse-involutive (dropEmpty ls))) (dropEmpty-DW ls))

  asLine-DW : ∀ l → DW (asLine l) ≡ dashWords l
  asLine-DW []       = refl
  asLine-DW (x ∷ xs) = trans (cong dashWords (toList∘fromList ('-' ∷ '-' ∷ ' ' ∷ x ∷ xs))) (dashWords-dd (x ∷ xs))

  atLeastOne-DW : ∀ ls → concatMap DW (atLeastOne ls) ≡ concatMap DW ls
  atLeastOne-DW []      = refl
  atLeastOne-DW (_ ∷ _) = refl

-- | A comment's lines hold its words.
commentLines-DW : ∀ s → concatMap DW (commentLines s) ≡ Mn s
commentLines-DW s =
  ifcase {P = λ z → concatMap DW z ≡ Mn s} (isBlock (toList s))
    (λ e → trans (atLeastOne-DW (map (λ l → asLine (strip l)) (trimLines (linesOf (inside (toList s))))))
      (trans (cm-map DW (λ l → asLine (strip l)) (trimLines (linesOf (inside (toList s)))))
      (trans (cm-cong (λ l → trans (asLine-DW (strip l)) (strip-DW l)) (trimLines (linesOf (inside (toList s)))))
      (trans (trimLines-DW (linesOf (inside (toList s))))
      (trans (linesGo-DW (inside (toList s)) []) (cong dashWords (sym (if-t e))))))))
    (λ e → trans (++-identityʳ (DW s)) (cong dashWords (sym (if-f e))))

------------------------------------------------------------------------
-- The words a document's comments hold
------------------------------------------------------------------------

open import Once.Format.Doc using (Doc; empty; tk; sp; cmt; para; line; newline; blank; eol; _<>_; nest; group)

DocC : Doc → List (List Char)
DocC empty      = []
DocC (tk _)     = []
DocC sp         = []
DocC (cmt c)    = DW c
DocC (para ws)  = concatMap DW ws
DocC line       = []
DocC newline    = []
DocC blank      = []
DocC (eol s)    = DW s
DocC (a <> b)   = DocC a ++ DocC b
DocC (nest _ d) = DocC d
DocC (group d)  = DocC d

private
  afterBlank-DW : ∀ s c cs → toList s ≡ '-' ∷ '-' ∷ c ∷ cs → gapC c ≡ true
                → DocC (lineDoc (afterBlank s cs)) ≡ dashWords cs
  afterBlank-DW s c []       eq g = refl
  afterBlank-DW s c (d ∷ ds) eq g =
    ifcase {P = λ z → DocC (lineDoc z) ≡ dashWords (d ∷ ds)} (is d ' ')
      (λ _ → whole)
      (λ _ → ifcase {P = λ z → DocC (lineDoc z) ≡ dashWords (d ∷ ds)} (listItem (d ∷ ds))
               (λ _ → whole) (λ _ → words-DW (d ∷ ds)))
    where
      whole : DW s ≡ dashWords (d ∷ ds)
      whole = trans (cong dashWords eq) (trans (dashWords-d2 (c ∷ d ∷ ds)) (dw-gap {b = c} (d ∷ ds) g))

  afterDashes-DW : ∀ s body → toList s ≡ '-' ∷ '-' ∷ body → DocC (lineDoc (afterDashes s body)) ≡ dashWords body
  afterDashes-DW s []       eq = refl
  afterDashes-DW s (c ∷ cs) eq =
    ifcase {P = λ z → DocC (lineDoc z) ≡ dashWords (c ∷ cs)} (is c ' ')
      (λ e → trans (afterBlank-DW s c cs eq (∨-true (blankish c) (∨-true (is c ' ') e))) (sym (dw-gap cs (∨-true (blankish c) (∨-true (is c ' ') e)))))
      (λ _ → words-DW (c ∷ cs))

  classifyChars-DW : ∀ s cs → toList s ≡ cs → DocC (lineDoc (classifyChars s cs)) ≡ dashWords cs
  classifyChars-DW s []            eq = cong dashWords eq
  classifyChars-DW s (c ∷ [])      eq = cong dashWords eq
  classifyChars-DW s (c ∷ d ∷ body) eq =
    bcase {P = λ z → DocC (lineDoc (dashLine z s body)) ≡ dashWords (c ∷ d ∷ body)} (is c '-' ∧ is d '-')
      (λ e → dash2 (is-eq c '-' (∧-l (is c '-') e)) (is-eq d '-' (∧-r (is c '-') e)))
      (λ _ → cong dashWords eq)
    where
      dash2 : c ≡ '-' → d ≡ '-' → DocC (lineDoc (dashLine true s body)) ≡ dashWords (c ∷ d ∷ body)
      dash2 refl refl =
        ifcase {P = λ z → DocC (lineDoc z) ≡ dashWords ('-' ∷ '-' ∷ body)} (allDash body)
          (λ _ → cong dashWords eq)
          (λ _ → trans (afterDashes-DW s body eq) (sym (dashWords-d2 body)))

-- | A comment line, as the renderer reads it, holds its words.
classify-DW : ∀ s → DocC (lineDoc (classify s)) ≡ DW s
classify-DW s = classifyChars-DW s (toList s) refl

commentLinesDoc-DW : ∀ ls → DocC (commentLinesDoc ls) ≡ concatMap DW ls
commentLinesDoc-DW []       = refl
commentLinesDoc-DW (l ∷ ls) = cong₂ _++_ (classify-DW l) (commentLinesDoc-DW ls)

-- | A run of comments, rendered, holds their words.
commentRun-DW : ∀ cs → DocC (commentRun cs) ≡ concatMap Mn cs
commentRun-DW cs = trans (commentLinesDoc-DW (concatMap commentLines cs))
  (trans (cm-cm DW commentLines cs) (cm-cong commentLines-DW cs))

private
  nl2sp : ∀ cs → concatMap (λ c → if is c '\n' then ' ' ∷ [] else c ∷ []) cs ≡ oneLine cs
  nl2sp []       = refl
  nl2sp (c ∷ cs) =
    ifcase {P = λ z → z ++ concatMap (λ c → if is c '\n' then ' ' ∷ [] else c ∷ []) cs
                      ≡ (if is c '\n' then ' ' else c) ∷ oneLine cs} (is c '\n')
      (λ e → trans (cong (' ' ∷_) (nl2sp cs)) (cong (_∷ oneLine cs) (sym (if-t e))))
      (λ e → trans (cong (c ∷_) (nl2sp cs)) (cong (_∷ oneLine cs) (sym (if-f e))))

  eolChars-DW : ∀ s cs → toList s ≡ cs → DW (eolChars s cs) ≡ dashWords cs
  eolChars-DW s []           eq = cong dashWords eq
  eolChars-DW s (c ∷ [])     eq = cong dashWords eq
  eolChars-DW s (c ∷ d ∷ cs) eq =
    ifcase {P = λ z → DW z ≡ dashWords (c ∷ d ∷ cs)} (is c '-' ∧ is d '-')
      (λ e → after (is-eq c '-' (∧-l (is c '-') e)) (is-eq d '-' (∧-r (is c '-') e)))
      (λ _ → cong dashWords eq)
    where
      after : c ≡ '-' → d ≡ '-' → DW (eolAfter s cs) ≡ dashWords (c ∷ d ∷ cs)
      after refl refl = go cs refl
        where
          go : ∀ xs → xs ≡ cs → DW (eolAfter s xs) ≡ dashWords ('-' ∷ '-' ∷ cs)
          go []       refl = cong dashWords eq
          go (x ∷ xs) refl =
            ifcase {P = λ z → DW z ≡ dashWords ('-' ∷ '-' ∷ x ∷ xs)} (is x ' ' ∨ is x '-')
              (λ _ → cong dashWords eq)
              (λ _ → trans (cong dashWords (toList∘fromList ('-' ∷ '-' ∷ ' ' ∷ x ∷ xs))) (trans (dashWords-dd (x ∷ xs)) (sym (dashWords-d2 (x ∷ xs)))))

private
  nl : List Char → List Char
  nl = concatMap (λ c → if is c '\n' then ' ' ∷ [] else c ∷ [])

-- | An end-of-line comment, rendered, holds its words.
eolText-DW : ∀ s → DW (eolText s) ≡ Mn s
eolText-DW s =
  ifcase {P = λ z → DW z ≡ Mn s} (isBlock (toList s))
    (λ e → trans (asLine-DW (strip (nl (inside (toList s))))) (trans (strip-DW (nl (inside (toList s)))) (trans (cong dashWords (nl2sp (inside (toList s))))
             (trans (dw-oneLine (inside (toList s)) []) (cong dashWords (sym (if-t e)))))))
    (λ e → trans (eolChars-DW s (toList s) refl) (cong dashWords (sym (if-f e))))

------------------------------------------------------------------------
-- What the layout writes keeps the words
------------------------------------------------------------------------

-- | A comment written as a line comment.
lineComment-DW : ∀ cs → dashWords (lineComment cs) ≡ dashWords cs
lineComment-DW cs = trans (dashWords-d2 (oneLine (body cs))) (trans (dw-oneLine (body cs) []) (body-DW cs))
  where
    body-DW : ∀ cs → dashWords (body cs) ≡ dashWords cs
    body-DW []           = refl
    body-DW (c ∷ [])     = refl
    body-DW (c ∷ d ∷ cs) =
      ifcase {P = λ z → dashWords z ≡ dashWords (c ∷ d ∷ cs)} (is c '-' ∧ is d '-')
        (λ e → dd (is-eq c '-' (∧-l (is c '-') e)) (is-eq d '-' (∧-r (is c '-') e)))
        (λ _ → refl)
      where
        dd : c ≡ '-' → d ≡ '-' → dashWords cs ≡ dashWords (c ∷ d ∷ cs)
        dd refl refl = sym (dashWords-d2 cs)

-- | The end-of-line comments of a line, joined.
joined-DW : ∀ e → dashWords (joined e) ≡ concatMap DW e
joined-DW []               = refl
joined-DW (x ∷ [])         = trans (lineComment-DW (toList x)) (sym (++-identityʳ (DW x)))
joined-DW (x ∷ xs@(_ ∷ _)) =
  trans (dw-split (lineComment (toList x)) {b = ' '} (joined xs) [] refl)
    (cong₂ _++_ (lineComment-DW (toList x)) (joined-DW xs))

-- | A paragraph's line.
dashed-DW : ∀ l → dashWords (dashed l) ≡ concatMap DW l
dashed-DW l = trans (dashWords-d2 (concatMap (λ w → ' ' ∷ toList w) l)) (go l)
  where
    go : ∀ l → dashWords (concatMap (λ w → ' ' ∷ toList w) l) ≡ concatMap DW l
    go []           = refl
    go (w ∷ [])     = trans (cong dashWords (++-identityʳ (toList w))) (sym (++-identityʳ (DW w)))
    go (w ∷ v ∷ vs) = trans (dw-split (toList w) {b = ' '} (toList v ++ concatMap (λ w → ' ' ∷ toList w) vs) [] refl)
                        (cong (DW w ++_) (go (v ∷ vs)))

-- | Filling keeps the words, in order.
fill-words : ∀ i c cur ws → concatMap (λ l → l) (fill i c cur ws) ≡ reverse cur ++ ws
fill-words i c []          []       = refl
fill-words i c (x ∷ xs)    []       = refl
fill-words i c []          (w ∷ ws) = fill-words i _ (w ∷ []) ws
fill-words i c cur@(x ∷ xs) (w ∷ ws) =
  ifcase {P = λ z → concatMap (λ l → l) z ≡ reverse cur ++ w ∷ ws} ((c + 1 + Str.length w) ≤ᵇ width)
    (λ _ → trans (fill-words i _ (w ∷ cur) ws) (rev-snoc′ cur w ws))
    (λ _ → cong (reverse cur ++_) (fill-words i _ (w ∷ []) ws))
  where
    rev-snoc′ : ∀ (cur : List String) w ws → reverse (w ∷ cur) ++ ws ≡ reverse cur ++ w ∷ ws
    rev-snoc′ cur w ws = trans (cong (_++ ws) (unfold-reverse w cur)) (++-assoc (reverse cur) (w ∷ []) ws)
