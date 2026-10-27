-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Rerender — a formatted comment, read back, is
-- formatted as itself (plan 0.124 step 4.5).
--
-- The layout writes a comment as line comments (`Comment.commentRun`): a
-- prose line filled to the width (`Doc.fill`), the rest as written. Read
-- back, each such line is one comment, and formatting it gives it again
-- (`RL`): a filled line still fits, so it fills as one line; its words are
-- its words; a line kept as written is kept again. So a run of comments,
-- formatted twice, is formatted once (`rendered-fix`). The comments that end
-- one line, joined (`Doc.joined`), are read back as one comment that ends
-- the line as they did (`eol-fix`).
------------------------------------------------------------------------

module Once.Format.Proof.Rerender where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_; T)
open import Data.Char using (Char)
import Data.Char as Ch
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; reverse; foldl; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ; reverse-involutive; reverse-++; unfold-reverse;
  concatMap-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Nat.Properties using (+-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; ∃₂)
open import Data.String using (String; toList; fromList) renaming (_++_ to _++ˢ_)
import Data.String as Str
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does; yes; no)
open import Relation.Nullary.Decidable using (dec-false; dec-true)
open import Agda.Builtin.String.Properties using (primStringToListInjective)

open import Once.Postulates using (toList∘fromList)
open import Once.Format.Doc using (lineComment; oneLine; body; joined; dashed; fill; width)
open import Once.Format.Comment using (is; allDash; listItem; blankish; emitW; wordsGo; words; CLine; prose;
  verbatim; classify; classifyChars; afterDashes; afterBlank; commentLines)
open import Once.Format.Print using (trimEnd; dropLead)

------------------------------------------------------------------------
-- Characters and words
------------------------------------------------------------------------

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = primStringToListInjective _ _ (toList∘fromList (toList s))

NoNl : List Char → Set
NoNl = All (_≢ '\n')

-- A character inside a word: not a blank, not a line end.
InWord : Char → Set
InWord c = blankish c ≡ false × c ≢ '\n'

-- | A word: some characters, none a blank or a line end.
Word : String → Set
Word w = ∃₂ λ (x : Char) (xs : List Char) → toList w ≡ x ∷ xs × All InWord (x ∷ xs)

all-rev : ∀ {P : Char → Set} {xs} → All P xs → All P (reverse xs)
all-rev []                  = []
all-rev {P} {x ∷ xs} (p ∷ ps) = subst (All P) (sym (unfold-reverse x xs)) (AllP.++⁺ (all-rev ps) (p ∷ []))

private
  rev-nonempty : ∀ x xs → ∃₂ λ (y : Char) (ys : List Char) → reverse (x ∷ xs) ≡ y ∷ ys
  rev-nonempty x xs with reverse xs | unfold-reverse x xs
  ... | []     | e = x , [] , e
  ... | y ∷ ys | e = y , ys ++ x ∷ [] , e

  emit-word : ∀ w acc → All InWord w → All Word acc → All Word (emitW w acc)
  emit-word []       acc _  as = as
  emit-word (x ∷ xs) acc iw as with rev-nonempty x xs
  ... | y , ys , e =
    (y , ys , trans (toList∘fromList _) e , subst (All InWord) e (all-rev iw)) ∷ as

  go-word : ∀ cs w → NoNl cs → All InWord w → All Word (wordsGo cs w)
  go-word []       w _        iw = emit-word w [] iw []
  go-word (c ∷ cs) w (n ∷ ns) iw with blankish c in e
  ... | true  = emit-word w _ iw (go-word cs [] ns [])
  ... | false = go-word cs (c ∷ w) ns ((e , n) ∷ iw)

-- | The words of a text with no line end are words.
words-word : ∀ cs → NoNl cs → All Word (words cs)
words-word cs ns = go-word cs [] ns []

-- The characters of words, a blank before each.
spaced : List String → List Char
spaced ws = concatMap (λ w → ' ' ∷ toList w) ws

private
  revOnto : List Char → List Char → List Char
  revOnto []       acc = acc
  revOnto (c ∷ cs) acc = revOnto cs (c ∷ acc)

  revOnto-rev : ∀ cs acc → revOnto cs acc ≡ reverse cs ++ acc
  revOnto-rev []       acc = refl
  revOnto-rev (c ∷ cs) acc =
    trans (revOnto-rev cs (c ∷ acc))
      (trans (sym (++-assoc (reverse cs) (c ∷ []) acc)) (cong (_++ acc) (sym (unfold-reverse c cs))))

  go-chars : ∀ cs rest acc → All InWord cs → wordsGo (cs ++ rest) acc ≡ wordsGo rest (revOnto cs acc)
  go-chars []       rest acc _               = refl
  go-chars (c ∷ cs) rest acc ((e , _) ∷ iw) rewrite e = go-chars cs rest (c ∷ acc) iw

  -- after a word: its characters (last first), then a blank or the end
  emit-next : ∀ ws y ys → wordsGo (spaced ws) (y ∷ ys) ≡ fromList (reverse (y ∷ ys)) ∷ wordsGo (spaced ws) []
  emit-next []       y ys = refl
  emit-next (v ∷ vs) y ys = refl

  -- a word read, then the words after a blank
  go-word-then : ∀ w ws → Word w → wordsGo (toList w ++ spaced ws) [] ≡ w ∷ wordsGo (spaced ws) []
  go-word-then w ws (x , xs , e , iw) =
    trans (cong (λ cs → wordsGo (cs ++ spaced ws) []) e)
      (trans (go-chars (x ∷ xs) (spaced ws) [] iw)
        (trans (cong (wordsGo (spaced ws)) (trans (revOnto-rev (x ∷ xs) []) (++-identityʳ _)))
          (next (rev-nonempty x xs))))
    where
      next : (∃₂ λ (y : Char) (ys : List Char) → reverse (x ∷ xs) ≡ y ∷ ys) → wordsGo (spaced ws) (reverse (x ∷ xs)) ≡ w ∷ wordsGo (spaced ws) []
      next (y , ys , q) rewrite q =
        trans (emit-next ws y ys)
          (cong (_∷ wordsGo (spaced ws) [])
            (trans (cong fromList (trans (cong reverse (sym q)) (reverse-involutive (x ∷ xs))))
                   (trans (cong fromList (sym e)) (fromList∘toList w))))

-- | Words written with a blank between are read back as themselves.
words-spaced : ∀ w ws → All Word (w ∷ ws) → words (toList w ++ spaced ws) ≡ w ∷ ws
words-spaced w []       (aw ∷ []) = go-word-then w [] aw
words-spaced w (v ∷ vs) (aw ∷ avs) = trans (go-word-then w (v ∷ vs) aw) (cong (w ∷_) (words-spaced v vs avs))

------------------------------------------------------------------------
-- Line comments
------------------------------------------------------------------------

-- | A decision on characters, read off an inequality.
≟-false : ∀ {c d} → c ≢ d → does (c Ch.≟ d) ≡ false
≟-false {c} {d} n = dec-false (c Ch.≟ d) n

oneLine-id : ∀ cs → NoNl cs → oneLine cs ≡ cs
oneLine-id []       []       = refl
oneLine-id (c ∷ cs) (n ∷ ns) = cong₂ _∷_ (cong (λ b → if b then ' ' else c) (≟-false n)) (oneLine-id cs ns)

-- | A line comment with no line end is written as it is.
lineComment-id : ∀ b → NoNl b → lineComment ('-' ∷ '-' ∷ b) ≡ '-' ∷ '-' ∷ b
lineComment-id b ns = cong (λ x → '-' ∷ '-' ∷ x) (oneLine-id b ns)

private
  word-nonl : ∀ {w} → Word w → NoNl (toList w)
  word-nonl (x , xs , e , iw) = subst NoNl (sym e) (Data.List.Relation.Unary.All.map proj₂ iw)

spaced-nonl : ∀ ws → All Word ws → NoNl (spaced ws)
spaced-nonl []       []         = []
spaced-nonl (w ∷ ws) (aw ∷ aws) = (λ ()) ∷ AllP.++⁺ (word-nonl {w} aw) (spaced-nonl ws aws)

-- | No blank ends it.
NoTrail : List Char → Set
NoTrail cs = ∃₂ λ (ys : List Char) (y : Char) → cs ≡ ys ++ y ∷ [] × blankish y ≡ false

dropLead-keep : ∀ y rs → blankish y ≡ false → dropLead (y ∷ rs) ≡ y ∷ rs
dropLead-keep y rs nb = cong (λ b → if b then dropLead rs else y ∷ rs) nb

trimEnd-id : ∀ cs → NoTrail cs → trimEnd (fromList cs) ≡ fromList cs
trimEnd-id cs (ys , y , refl , nb)
  rewrite toList∘fromList (ys ++ y ∷ []) | reverse-++ ys (y ∷ []) | dropLead-keep y (reverse ys) nb =
  cong fromList (trans (unfold-reverse y (reverse ys)) (cong (_++ y ∷ []) (reverse-involutive ys)))

-- | A comment line, as the walker reads it back: `--` first, no line end
-- in it, no blank at its end.
LineC : String → Set
LineC s = ∃[ b ] (toList s ≡ '-' ∷ '-' ∷ b × NoNl b × NoTrail ('-' ∷ '-' ∷ b))

------------------------------------------------------------------------
-- Small facts about decisions and lists
------------------------------------------------------------------------

open import Data.Char.Properties using (toℕ-injective)
open import Data.Nat.Properties using (≡ᵇ⇒≡)

-- | A decision on characters that holds is an equality.
is-true : ∀ c d → is c d ≡ true → c ≡ d
is-true c d e = toℕ-injective c d (≡ᵇ⇒≡ (Ch.toℕ c) (Ch.toℕ d) (subst T (sym e) tt))

is-false : ∀ c d → is c d ≡ false → c ≢ d
is-false c d e refl = subst T e (subst T (sym (dec-true (c Ch.≟ c) refl)) tt)

if-true : ∀ {A : Set} b {x y : A} → T b → (if b then x else y) ≡ x
if-true true  _ = refl

if-false : ∀ {A : Set} b {x y : A} → b ≡ false → (if b then x else y) ≡ y
if-false false _ = refl

∨-false-l : ∀ a b → a ∨ b ≡ false → a ≡ false
∨-false-l false b e = refl

all-revA : ∀ {A : Set} {P : A → Set} {xs} → All P xs → All P (reverse xs)
all-revA []                  = []
all-revA {A} {P} {x ∷ xs} (p ∷ ps) = subst (All P) (sym (unfold-reverse x xs)) (AllP.++⁺ (all-revA ps) (p ∷ []))

-- The last character of some characters a property holds of.
notrail : ∀ x xs → All InWord (x ∷ xs) → NoTrail (x ∷ xs)
notrail x []       ((nb , _) ∷ [])  = [] , x , refl , nb
notrail x (y ∷ ys) (_ ∷ iw) with notrail y ys iw
... | zs , z , e , nb = x ∷ zs , z , cong (x ∷_) e , nb

notrail-++ : ∀ xs ys → NoTrail ys → NoTrail (xs ++ ys)
notrail-++ xs ys (zs , z , e , nb) = xs ++ zs , z , trans (cong (xs ++_) e) (sym (++-assoc xs zs (z ∷ []))) , nb

------------------------------------------------------------------------
-- What a line comment is
------------------------------------------------------------------------

-- The three kinds a comment line is read as: kept, `--` alone, prose.
data Kind (s : String) : CLine → Set where
  k-kept  : Kind s (verbatim s)
  k-empty : Kind s (verbatim "--")
  k-prose : ∀ {ws} → All Word ws → Kind s (prose ws)

private
  kind-if : ∀ {s} b {x} → Kind s x → Kind s (if b then verbatim s else x)
  kind-if true  _ = k-kept
  kind-if false k = k

  kind-if2 : ∀ {s} b {x y} → Kind s x → Kind s y → Kind s (if b then x else y)
  kind-if2 true  kx _  = kx
  kind-if2 false _  ky = ky

  kind-prose : ∀ {s} cs → NoNl cs → Kind s (prose (words cs))
  kind-prose cs nn = k-prose (words-word cs nn)

  kind-blank : ∀ {s} cs → NoNl cs → Kind s (afterBlank s cs)
  kind-blank []       _  = k-empty
  kind-blank (d ∷ ds) nn = kind-if (is d ' ') (kind-if (listItem (d ∷ ds)) (kind-prose (d ∷ ds) nn))

  kind-dashes : ∀ {s} cs → NoNl cs → Kind s (afterDashes s cs)
  kind-dashes []       _              = k-prose []
  kind-dashes (c ∷ cs) nn@(_ ∷ nn′) = kind-if2 (is c ' ') (kind-blank cs nn′) (kind-prose (c ∷ cs) nn)

-- | A comment line is kept, `--` alone, or prose of words.
kind : ∀ s → LineC s → Kind s (classify s)
kind s (b , e , nn , _) = subst (λ cs → Kind s (classifyChars s cs)) (sym e) (kind-if (allDash b) (kind-dashes b nn))

------------------------------------------------------------------------
-- Filling a paragraph
------------------------------------------------------------------------

-- Each word after the first fits, from column `c`.
Fits : ℕ → List String → Set
Fits c []       = ⊤
Fits c (w ∷ ws) = T ((c + 1 + Str.length w) ≤ᵇ width) × Fits (c + 1 + Str.length w) ws

-- The column after words, from `c`.
pos : ℕ → List String → ℕ
pos c []       = c
pos c (w ∷ ws) = pos (c + 1 + Str.length w) ws

-- | A line of a paragraph at indentation `i`: empty, or a first word and
-- words that fit after it.
LineOK : ℕ → List String → Set
LineOK i l = l ≡ [] ⊎ ∃₂ λ (w : String) (ws : List String) → l ≡ w ∷ ws × Fits ((i + 2) + 1 + Str.length w) ws

private
  fill-done : ∀ i c x cur ws → Fits c ws → fill i c (x ∷ cur) ws ≡ (reverse (x ∷ cur) ++ ws) ∷ []
  fill-done i c x cur []       _        = cong (_∷ []) (sym (++-identityʳ _))
  fill-done i c x cur (w ∷ ws) (t , f) =
    trans (if-true ((c + 1 + Str.length w) ≤ᵇ width) t)
      (trans (fill-done i (c + 1 + Str.length w) w (x ∷ cur) ws f)
        (cong (_∷ []) (trans (cong (_++ ws) (unfold-reverse w (x ∷ cur))) (++-assoc (reverse (x ∷ cur)) (w ∷ []) ws))))

  fits-snoc : ∀ c rest w → Fits c rest → T ((pos c rest + 1 + Str.length w) ≤ᵇ width) → Fits c (rest ++ w ∷ [])
  fits-snoc c []         w _       t = t , tt
  fits-snoc c (v ∷ vs)   w (t′ , f) t = t′ , fits-snoc (c + 1 + Str.length v) vs w f t

  pos-snoc : ∀ c rest w → pos c (rest ++ w ∷ []) ≡ pos c rest + 1 + Str.length w
  pos-snoc c []       w = refl
  pos-snoc c (v ∷ vs) w = pos-snoc (c + 1 + Str.length v) vs w

  -- the line being filled: its first word, the words that fit after it, the column after them
  Cur : ℕ → ℕ → List String → Set
  Cur i c cur = ∃₂ λ (w₀ : String) (rest : List String) → reverse cur ≡ w₀ ∷ rest
                  × Fits ((i + 2) + 1 + Str.length w₀) rest × c ≡ pos ((i + 2) + 1 + Str.length w₀) rest

  fill-go : ∀ i c x cur ws → Cur i c (x ∷ cur) → All (LineOK i) (fill i c (x ∷ cur) ws)
  fill-go i c x cur [] (w₀ , rest , e , f , _) = inj₂ (w₀ , rest , e , f) ∷ []
  fill-go i c x cur (w ∷ ws) (w₀ , rest , er , f , ec) = branch ((c + 1 + Str.length w) ≤ᵇ width) refl
    where
      branch : ∀ b → ((c + 1 + Str.length w) ≤ᵇ width) ≡ b
             → All (LineOK i) (if b then fill i (c + 1 + Str.length w) (w ∷ x ∷ cur) ws
                                else reverse (x ∷ cur) ∷ fill i (i + 3 + Str.length w) (w ∷ []) ws)
      branch true e =
        fill-go i (c + 1 + Str.length w) w (x ∷ cur) ws
          (w₀ , rest ++ w ∷ [] ,
           trans (unfold-reverse w (x ∷ cur)) (cong (_++ w ∷ []) er) ,
           fits-snoc _ rest w f (subst (λ n → T ((n + 1 + Str.length w) ≤ᵇ width)) ec (subst T (sym e) tt)) ,
           trans (cong (λ n → n + 1 + Str.length w) ec) (sym (pos-snoc _ rest w)))
      branch false e =
        inj₂ (w₀ , rest , er , f) ∷
        fill-go i (i + 3 + Str.length w) w [] ws (w , [] , refl , tt , cong (_+ Str.length w) (sym (+-assoc i 2 1)))

-- | The lines of a paragraph are lines.
fill-lines : ∀ i ws → All (LineOK i) (fill i (i + 2) [] ws)
fill-lines i []       = inj₁ refl ∷ []
fill-lines i (w ∷ ws) = fill-go i ((i + 2) + 1 + Str.length w) w [] ws (w , [] , refl , tt , refl)

-- | A line of a paragraph, filled again, is that line.
fill-line : ∀ i l → LineOK i l → fill i (i + 2) [] l ≡ l ∷ []
fill-line i .[]       (inj₁ refl)               = refl
fill-line i .(w ∷ ws) (inj₂ (w , ws , refl , f)) = fill-done i ((i + 2) + 1 + Str.length w) w [] ws f

-- | A paragraph's lines are made of its words.
fill-words : ∀ {P : String → Set} i c cur ws → All P cur → All P ws → All (All P) (fill i c cur ws)
fill-words i c []          []       _  _          = [] ∷ []
fill-words i c (x ∷ cur)   []       pc _          = all-revA pc ∷ []
fill-words i c []          (w ∷ ws) _  (pw ∷ pws) = fill-words i (c + 1 + Str.length w) (w ∷ []) ws (pw ∷ []) pws
fill-words {P} i c (x ∷ cur) (w ∷ ws) pc (pw ∷ pws) = branch ((c + 1 + Str.length w) ≤ᵇ width)
  where
    branch : ∀ b → All (All P) (if b then fill i (c + 1 + Str.length w) (w ∷ x ∷ cur) ws
                                else reverse (x ∷ cur) ∷ fill i (i + 3 + Str.length w) (w ∷ []) ws)
    branch true  = fill-words i _ (w ∷ x ∷ cur) ws (pw ∷ pc) pws
    branch false = all-revA pc ∷ fill-words i _ (w ∷ []) ws (pw ∷ []) pws

------------------------------------------------------------------------
-- What the layout writes for a comment, and what is read back
------------------------------------------------------------------------

open import Once.Format.Comment using (isBlock; asLine; strip; dropBlanks; linesGo; linesOf; dropEmpty; trimLines;
  inside; atLeastOne; eolText; eolChars)

-- | The lines the layout writes for a comment line, at indentation `i`
-- (`Doc.paragraph`, `Doc.comment`).
renderK : ℕ → CLine → List (List Char)
renderK i (prose ws)   = map (λ l → lineComment (toList (fromList (dashed l)))) (fill i (i + 2) [] ws)
renderK i (verbatim v) = lineComment (toList v) ∷ []

renderLine : ℕ → String → List (List Char)
renderLine i c = renderK i (classify c)

-- | The lines of a run of comments.
rendered : ℕ → List String → List (List Char)
rendered i R = concatMap (renderLine i) (concatMap commentLines R)

-- | What the walker reads a written line as.
readBack : List Char → String
readBack L = trimEnd (fromList L)

-- | A line that, read back and formatted, is itself.
RL : ℕ → List Char → Set
RL i L = concatMap (renderLine i) (commentLines (readBack L)) ≡ L ∷ []

line-commentLines : ∀ s → LineC s → commentLines s ≡ s ∷ []
line-commentLines s (b , e , _ , _) = if-false (isBlock (toList s)) (cong isBlock e)

private
  lc-dd : LineC "--"
  lc-dd = [] , refl , [] , ('-' ∷ [] , '-' , refl , refl)

  line-id : ∀ s → LineC s → lineComment (toList s) ≡ toList s
  line-id s (b , e , nn , _) = trans (cong lineComment e) (trans (lineComment-id b nn) (sym e))

  readBack-line : ∀ v → LineC v → readBack (lineComment (toList v)) ≡ v
  readBack-line v lc@(b , e , nn , nt) =
    trans (cong (λ L → trimEnd (fromList L)) (line-id v lc))
      (trans (trimEnd-id (toList v) (subst NoTrail (sym e) nt)) (fromList∘toList v))

  rl-verb : ∀ i v → LineC v → classify v ≡ verbatim v → RL i (lineComment (toList v))
  rl-verb i v lc cv =
    trans (cong (λ s → concatMap (renderLine i) (commentLines s)) (readBack-line v lc))
      (trans (cong (concatMap (renderLine i)) (line-commentLines v lc))
        (trans (++-identityʳ _) (cong (renderK i) cv)))

  nt-spaced : ∀ w ws → All Word (w ∷ ws) → NoTrail (spaced (w ∷ ws))
  nt-spaced w [] ((x , xs , e , iw) ∷ []) =
    subst NoTrail (cong (λ cs → ' ' ∷ cs) (trans (sym (++-identityʳ (x ∷ xs))) (cong (_++ []) (sym e))))
      (notrail-++ (' ' ∷ []) (x ∷ xs) (notrail x xs iw))
  nt-spaced w (v ∷ vs) (_ ∷ aws) = notrail-++ (' ' ∷ toList w) (spaced (v ∷ vs)) (nt-spaced v vs aws)

  nt-dashed : ∀ l → All Word l → NoTrail (dashed l)
  nt-dashed []       []  = '-' ∷ [] , '-' , refl , refl
  nt-dashed (w ∷ ws) aws = notrail-++ ('-' ∷ '-' ∷ []) (spaced (w ∷ ws)) (nt-spaced w ws aws)

  lc-dashed : ∀ l → All Word l → LineC (fromList (dashed l))
  lc-dashed l aws = spaced l , toList∘fromList (dashed l) , spaced-nonl l aws , nt-dashed l aws

  -- a filled line, classified again: kept as written (a list item), or the same prose, filled as one line
  rl-kinds : ∀ i l → LineOK i l → All Word l
           → renderK i (classifyChars (fromList (dashed l)) (dashed l)) ≡ lineComment (toList (fromList (dashed l))) ∷ []
  rl-kinds i []       ok aws = refl
  rl-kinds i (w ∷ ws) ok aws@((x , xs , ew , ((nb , _) ∷ _)) ∷ _) =
    trans (cong (λ cs → renderK i (afterBlank s (cs ++ spaced ws))) ew)
      (trans (cong (renderK i) (if-false (is x ' ') (∨-false-l (is x ' ') (is x '\t' ∨ is x '\r') nb)))
        (li (listItem (x ∷ xs ++ spaced ws))))
    where
      s = fromList (dashed (w ∷ ws))
      wq : words (x ∷ xs ++ spaced ws) ≡ w ∷ ws
      wq = subst (λ cs → words (cs ++ spaced ws) ≡ w ∷ ws) ew (words-spaced w ws aws)
      li : ∀ b → renderK i (if b then verbatim s else prose (words (x ∷ xs ++ spaced ws))) ≡ lineComment (toList s) ∷ []
      li true  = refl
      li false = trans (cong (λ ws′ → renderK i (prose ws′)) wq)
                       (cong (map (λ l → lineComment (toList (fromList (dashed l))))) (fill-line i (w ∷ ws) ok))

  rl-prose : ∀ i l → LineOK i l → All Word l → RL i (lineComment (toList (fromList (dashed l))))
  rl-prose i l ok aws =
    trans (cong (λ s → concatMap (renderLine i) (commentLines s)) rb)
      (trans (cong (concatMap (renderLine i)) (line-commentLines s (lc-dashed l aws)))
        (trans (++-identityʳ _) (trans (cong (λ cs → renderK i (classifyChars s cs)) (toList∘fromList (dashed l)))
          (rl-kinds i l ok aws))))
    where
      s = fromList (dashed l)
      rb : readBack (lineComment (toList s)) ≡ s
      rb = readBack-line s (lc-dashed l aws)

  rl-lines : ∀ i ls → All (LineOK i) ls → All (All Word) ls → All (RL i) (map (λ l → lineComment (toList (fromList (dashed l)))) ls)
  rl-lines i []       []         []           = []
  rl-lines i (l ∷ ls) (ok ∷ oks) (aw ∷ aws) = rl-prose i l ok aw ∷ rl-lines i ls oks aws

  kind-rl : ∀ i s → LineC s → ∀ {k} → Kind s k → classify s ≡ k → All (RL i) (renderK i k)
  kind-rl i s lc k-kept          cv = rl-verb i s lc cv ∷ []
  kind-rl i s lc k-empty         cv = rl-verb i "--" lc-dd refl ∷ []
  kind-rl i s lc (k-prose {ws} aw) cv =
    rl-lines i (fill i (i + 2) [] ws) (fill-lines i ws) (fill-words i (i + 2) [] ws [] aw)

-- | The lines of a comment line, read back, are formatted as themselves.
renderLine-RL : ∀ i s → LineC s → All (RL i) (renderLine i s)
renderLine-RL i s lc = kind-rl i s lc (kind s lc) refl

------------------------------------------------------------------------
-- The comments the walker reads
------------------------------------------------------------------------

-- | A comment as the walker keeps it: a line comment, or a block comment.
data Src (s : String) : Set where
  src-line  : LineC s → Src s
  src-block : ∀ {b} → toList s ≡ '{' ∷ '-' ∷ b → Src s

private
  is-or : ∀ a b → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
  is-or true  b _ = inj₁ refl
  is-or false b e = inj₂ e

  db-all : ∀ {P : Char → Set} cs → All P cs → All P (dropBlanks cs)
  db-all []       []       = []
  db-all (c ∷ cs) (p ∷ ps) = pick (blankish c)
    where
      pick : ∀ b → All _ (if b then dropBlanks cs else c ∷ cs)
      pick true  = db-all cs ps
      pick false = p ∷ ps

  db-head : ∀ cs → dropBlanks cs ≡ [] ⊎ ∃₂ λ (z : Char) (zs : List Char) → dropBlanks cs ≡ z ∷ zs × blankish z ≡ false
  db-head []       = inj₁ refl
  db-head (c ∷ cs) = pick (blankish c) refl
    where
      pick : ∀ b → blankish c ≡ b → (if b then dropBlanks cs else c ∷ cs) ≡ [] ⊎
             ∃₂ λ (z : Char) (zs : List Char) → (if b then dropBlanks cs else c ∷ cs) ≡ z ∷ zs × blankish z ≡ false
      pick true  _ = db-head cs
      pick false e = inj₂ (c , cs , refl , e)

  strip-nonl : ∀ l → NoNl l → NoNl (strip l)
  strip-nonl l nn = all-rev (db-all _ (all-rev (db-all l nn)))

  strip-end : ∀ l → strip l ≡ [] ⊎ NoTrail (strip l)
  strip-end l with db-head (reverse (dropBlanks l))
  ... | inj₁ e = inj₁ (cong reverse e)
  ... | inj₂ (z , zs , e , nb) = inj₂ (reverse zs , z , trans (cong reverse e) (unfold-reverse z zs) , nb)

-- | What ends a line as a comment: `--`, then nothing, a blank or a dash.
Third : List Char → Set
Third []      = ⊤
Third (c ∷ _) = c ≡ ' ' ⊎ c ≡ '-'

EolC : String → Set
EolC s = ∃[ b ] (toList s ≡ '-' ∷ '-' ∷ b × NoNl b × NoTrail ('-' ∷ '-' ∷ b) × Third b)

private
  eol-line : ∀ s → EolC s → LineC s
  eol-line s (b , e , nn , nt , _) = b , e , nn , nt

  eol-dd : EolC "--"
  eol-dd = [] , refl , [] , ('-' ∷ [] , '-' , refl , refl) , tt

  -- `asLine` of a stripped line: a comment that ends a line, and a comment line
  asLine-eol : ∀ l → NoNl l → EolC (asLine (strip l))
  asLine-eol l nn = go (strip l) refl
    where
      go : ∀ r → strip l ≡ r → EolC (asLine r)
      go []       _ = eol-dd
      go (y ∷ ys) e with strip-end l
      ... | inj₁ e′ with trans (sym e) e′
      ...   | ()
      go (y ∷ ys) e | inj₂ nt =
        ' ' ∷ y ∷ ys , toList∘fromList _ , (λ ()) ∷ subst NoNl e (strip-nonl l nn) ,
        notrail-++ ('-' ∷ '-' ∷ ' ' ∷ []) (y ∷ ys) (subst NoTrail e nt) , inj₁ refl

  lines-nonl : ∀ cs l → NoNl l → All NoNl (linesGo cs l)
  lines-nonl []       l nl = all-rev nl ∷ []
  lines-nonl (c ∷ cs) l nl = pick (is c '\n') refl
    where
      pick : ∀ b → is c '\n' ≡ b → All NoNl (if b then reverse l ∷ linesGo cs [] else linesGo cs (c ∷ l))
      pick true  _ = all-rev nl ∷ lines-nonl cs [] []
      pick false e = lines-nonl cs (c ∷ l) (is-false c '\n' e ∷ nl)

  dropEmpty-all : ∀ {P : List Char → Set} ls → All P ls → All P (dropEmpty ls)
  dropEmpty-all []              []       = []
  dropEmpty-all ([] ∷ ls)       (_ ∷ ps) = dropEmpty-all ls ps
  dropEmpty-all ((c ∷ cs) ∷ ls) ps       = ps

  trimLines-all : ∀ {P : List Char → Set} ls → All P ls → All P (trimLines ls)
  trimLines-all ls ps = all-revA (dropEmpty-all _ (all-revA (dropEmpty-all ls ps)))

  map-asLine : ∀ ls → All NoNl ls → All LineC (map (λ l → asLine (strip l)) ls)
  map-asLine []       []         = []
  map-asLine (l ∷ ls) (nn ∷ nns) = eol-line (asLine (strip l)) (asLine-eol l nn) ∷ map-asLine ls nns

  atLeastOne-all : ∀ ls → All LineC ls → All LineC (atLeastOne ls)
  atLeastOne-all []       _  = eol-line "--" eol-dd ∷ []
  atLeastOne-all (l ∷ ls) ps = ps

-- | A comment's lines are comment lines.
commentLines-line : ∀ s → Src s → All LineC (commentLines s)
commentLines-line s (src-line lc) = subst (All LineC) (sym (line-commentLines s lc)) (lc ∷ [])
commentLines-line s (src-block e) =
  subst (All LineC) (sym (if-true (isBlock (toList s)) (subst (λ cs → T (isBlock cs)) (sym e) tt)))
    (atLeastOne-all _ (map-asLine _ (trimLines-all _ (lines-nonl (inside (toList s)) [] []))))

------------------------------------------------------------------------
-- A run of comments, formatted twice
------------------------------------------------------------------------

-- | A run's lines, read back and formatted, are themselves.
rendered-RL : ∀ i R → All Src R → All (RL i) (rendered i R)
rendered-RL i []       []         = []
rendered-RL i (c ∷ R)  (sc ∷ scs) =
  subst (All (RL i)) (sym (concatMap-++ (renderLine i) (commentLines c) (concatMap commentLines R)))
    (AllP.++⁺ (lines (commentLines c) (commentLines-line c sc)) (rendered-RL i R scs))
  where
    lines : ∀ ls → All LineC ls → All (RL i) (concatMap (renderLine i) ls)
    lines []       []         = []
    lines (l ∷ ls) (lc ∷ lcs) = AllP.++⁺ (renderLine-RL i l lc) (lines ls lcs)

-- | Formatting the lines a run is written as writes them again.
rendered-fix : ∀ i Ls → All (RL i) Ls → rendered i (map readBack Ls) ≡ Ls
rendered-fix i []       []         = refl
rendered-fix i (L ∷ Ls) (rl ∷ rls) =
  trans (concatMap-++ (renderLine i) (commentLines (readBack L)) (concatMap commentLines (map readBack Ls)))
    (cong₂ _++_ rl (rendered-fix i Ls rls))

------------------------------------------------------------------------
-- The comments that end a line
------------------------------------------------------------------------

private
  nl-sp : ∀ cs → NoNl (concatMap (λ c → if is c '\n' then ' ' ∷ [] else c ∷ []) cs)
  nl-sp []       = []
  nl-sp (c ∷ cs) = pick (is c '\n') refl
    where
      pick : ∀ b → is c '\n' ≡ b → NoNl ((if b then ' ' ∷ [] else c ∷ []) ++ concatMap (λ c → if is c '\n' then ' ' ∷ [] else c ∷ []) cs)
      pick true  _ = (λ ()) ∷ nl-sp cs
      pick false e = is-false c '\n' e ∷ nl-sp cs

  notrail-tail : ∀ a c cs → NoTrail (a ∷ c ∷ cs) → NoTrail (c ∷ cs)
  notrail-tail a c cs ([]     , z , () , _)
  notrail-tail a c cs (_ ∷ zs , z , e , nb) = zs , z , Data.List.Properties.∷-injectiveʳ e , nb

-- | A comment that ends a line, as written there.
eolText-eol : ∀ s → Src s → EolC (eolText s)
eolText-eol s (src-block e) =
  subst EolC (sym (if-true (isBlock (toList s)) (subst (λ cs → T (isBlock cs)) (sym e) tt))) (asLine-eol _ (nl-sp (inside (toList s))))
eolText-eol s (src-line (b , e , nn , nt)) =
  subst EolC (sym (trans (if-false (isBlock (toList s)) (cong isBlock e)) (cong (eolChars s) e))) (chars b e nn nt)
  where
    chars : ∀ b′ → toList s ≡ '-' ∷ '-' ∷ b′ → NoNl b′ → NoTrail ('-' ∷ '-' ∷ b′) → EolC (eolChars s ('-' ∷ '-' ∷ b′))
    chars []       e′ _  nt = [] , e′ , [] , nt , tt
    chars (c ∷ cs) e′ nn nt = pick (is c ' ' ∨ is c '-') refl
      where
        pick : ∀ b → (is c ' ' ∨ is c '-') ≡ b → EolC (if b then s else fromList ('-' ∷ '-' ∷ ' ' ∷ c ∷ cs))
        pick true  q = c ∷ cs , e′ , nn , nt , third (is-or _ _ q)
          where
            third : is c ' ' ≡ true ⊎ is c '-' ≡ true → c ≡ ' ' ⊎ c ≡ '-'
            third (inj₁ q′) = inj₁ (is-true c ' ' q′)
            third (inj₂ q′) = inj₂ (is-true c '-' q′)
        pick false _ = ' ' ∷ c ∷ cs , toList∘fromList _ , (λ ()) ∷ nn ,
                       notrail-++ ('-' ∷ '-' ∷ ' ' ∷ []) (c ∷ cs) (notrail-tail '-' c cs (notrail-tail '-' '-' (c ∷ cs) nt)) ,
                       inj₁ refl

private
  joined-eol : ∀ e es → All EolC (e ∷ es)
             → ∃[ b ] (joined (e ∷ es) ≡ '-' ∷ '-' ∷ b × NoNl b × NoTrail ('-' ∷ '-' ∷ b) × Third b)
  joined-eol e [] ((b , ee , nn , nt , th) ∷ []) = b , trans (cong lineComment ee) (lineComment-id b nn) , nn , nt , th
  joined-eol e (e′ ∷ es) ((b , ee , nn , nt , th) ∷ aes) with joined-eol e′ es aes
  ... | b′ , ej′ , nn′ , nt′ , th′ =
    b ++ ' ' ∷ '-' ∷ '-' ∷ b′ ,
    cong₂ (λ x y → x ++ ' ' ∷ y) (trans (cong lineComment ee) (lineComment-id b nn)) ej′ ,
    AllP.++⁺ nn ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ nn′) ,
    subst NoTrail (cong (λ cs → '-' ∷ '-' ∷ cs) (++-assoc b (' ' ∷ []) ('-' ∷ '-' ∷ b′)))
      (notrail-++ ('-' ∷ '-' ∷ b ++ ' ' ∷ []) ('-' ∷ '-' ∷ b′) nt′) ,
    third b th
    where
      third : ∀ b → Third b → Third (b ++ ' ' ∷ '-' ∷ '-' ∷ b′)
      third []      _  = inj₁ refl
      third (c ∷ _) th = th

  eolText-keep : ∀ b → Third b → eolText (fromList ('-' ∷ '-' ∷ b)) ≡ fromList ('-' ∷ '-' ∷ b)
  eolText-keep b th =
    trans (if-false (isBlock (toList s)) (cong isBlock (toList∘fromList ('-' ∷ '-' ∷ b))))
      (trans (cong (eolChars s) (toList∘fromList ('-' ∷ '-' ∷ b))) (keep b th))
    where
      s = fromList ('-' ∷ '-' ∷ b)
      keep : ∀ b′ → Third b′ → eolChars s ('-' ∷ '-' ∷ b′) ≡ s
      keep []               _           = refl
      keep (.' ' ∷ cs)  (inj₁ refl) = refl
      keep (.'-' ∷ cs)  (inj₂ refl) = refl

-- | The comments that end a line, written joined, are read back as one
-- comment, and that comment ends the line as they did.
eol-fix : ∀ e es → All EolC (e ∷ es) → lineComment (toList (eolText (readBack (joined (e ∷ es))))) ≡ joined (e ∷ es)
eol-fix e es aes with joined-eol e es aes
... | b , ej , nn , nt , th =
  trans (cong (λ J → lineComment (toList (eolText (readBack J)))) ej)
    (trans (cong (λ s → lineComment (toList (eolText s))) (trimEnd-id ('-' ∷ '-' ∷ b) nt))
      (trans (cong (λ s → lineComment (toList s)) (eolText-keep b th))
        (trans (cong lineComment (toList∘fromList ('-' ∷ '-' ∷ b))) (trans (lineComment-id b nn) (sym ej)))))

------------------------------------------------------------------------
-- A comment is written as some lines
------------------------------------------------------------------------

fill-ne : ∀ i c cur ws → ∃[ l ] ∃[ ls ] fill i c cur ws ≡ l ∷ ls
fill-ne i c []        []       = [] , [] , refl
fill-ne i c (x ∷ cur) []       = _ , [] , refl
fill-ne i c []        (w ∷ ws) = fill-ne i _ (w ∷ []) ws
fill-ne i c (x ∷ cur) (w ∷ ws) = pick ((c + 1 + Str.length w) Data.Nat.≤ᵇ width)
  where
    pick : ∀ b → ∃[ l ] ∃[ ls ] (if b then fill i (c + 1 + Str.length w) (w ∷ x ∷ cur) ws
                                else reverse (x ∷ cur) ∷ fill i (i + 3 + Str.length w) (w ∷ []) ws) ≡ l ∷ ls
    pick true  = fill-ne i _ (w ∷ x ∷ cur) ws
    pick false = _ , _ , refl

renderK-ne : ∀ i k → ∃[ L ] ∃[ Ls ] renderK i k ≡ L ∷ Ls
renderK-ne i (verbatim v) = _ , [] , refl
renderK-ne i (prose ws) with fill-ne i (i + 2) [] ws
... | l , ls , e = _ , _ , cong (map (λ l → lineComment (toList (fromList (dashed l))))) e

commentLines-ne : ∀ s → ∃[ l ] ∃[ ls ] commentLines s ≡ l ∷ ls
commentLines-ne s = pick (Once.Format.Comment.isBlock (toList s))
  where
    one : ∀ xs → ∃[ l ] ∃[ ls ] Once.Format.Comment.atLeastOne xs ≡ l ∷ ls
    one []       = _ , [] , refl
    one (x ∷ xs) = x , xs , refl
    pick : ∀ b → ∃[ l ] ∃[ ls ] (if b then Once.Format.Comment.atLeastOne
                                  (map (λ l → Once.Format.Comment.asLine (Once.Format.Comment.strip l))
                                    (Once.Format.Comment.trimLines (Once.Format.Comment.linesOf
                                      (Once.Format.Comment.inside (toList s))))) else s ∷ []) ≡ l ∷ ls
    pick true  = one _
    pick false = s , [] , refl

-- | A run of comments is written as some lines.
rendered-ne : ∀ i c cs → ∃[ L ] ∃[ Ls ] rendered i (c ∷ cs) ≡ L ∷ Ls
rendered-ne i c cs with commentLines-ne c
... | l , ls , e with renderK-ne i (classify l)
...   | L , Ls , e′ =
  L , _ , trans (cong (concatMap (renderLine i)) (cong (_++ concatMap commentLines cs) e))
            (cong (_++ concatMap (renderLine i) (ls ++ concatMap commentLines cs)) e′)
