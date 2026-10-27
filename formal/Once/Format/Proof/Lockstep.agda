-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Lockstep — the walker, read along the layout (plan
-- 0.124 step 4.5).
--
-- The second formatting pass reads the first pass's text. Its trivia is the
-- walker run over the first pass's lexemes (`Walk.formatted-trivia`), and the
-- layout writes those lexemes one step at a time, so the walker can be read
-- along the layout: `Φ` is the walker over what the layout has written so
-- far. A blank the layout takes back at a line's end (`Doc.trim`) was never
-- seen by the walker as anything (`trim-Φ`), so every step of the layout is a
-- step of the walker (`layout-reach`), and what the walk has settled is what
-- the second pass's trivia holds (`Walk.frozen-ti`, `Walk.frozen-after`).
------------------------------------------------------------------------

module Once.Format.Proof.Lockstep where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; reverse; foldl)
open import Data.List.Properties using (unfold-reverse; foldl-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Spec.Surface.Lexing using (Token)
open import Once.Format.Doc using (Doc; empty; tk; sp; cmt; para; line; newline; blank; eol; _<>_; nest; group;
  Lexeme; lt; lsp; lnl; lind; lcm; St; st; put; space; token; joined; trim; brk; comment; blankLine; fill;
  dashed; paragraph; fits; flatWidth; column; layout; apart)
open import Once.Format.Proof.Walk using (WL; stepL; walkL; w₀)

------------------------------------------------------------------------
-- The walker over what is written
------------------------------------------------------------------------

-- | The walker over the lexemes written so far (`out` holds them last first).
Φ : List Lexeme → WL
Φ o = walkL (w₀ , false) (reverse o)

Φ-cons : ∀ x o → Φ (x ∷ o) ≡ stepL (Φ o) x
Φ-cons x o = trans (cong (walkL (w₀ , false)) (unfold-reverse x o)) (foldl-++ stepL (w₀ , false) (reverse o) (x ∷ []))

-- Whether a line end waits.
waits : List Lexeme → Bool
waits o = proj₂ (Φ o)

-- | One walk state leads to another.
Reach : WL → WL → Set
Reach ω ω′ = ∃[ xs ] walkL ω xs ≡ ω′

reach-refl : ∀ {ω} → Reach ω ω
reach-refl = [] , refl

reach-trans : ∀ {ω ω′ ω″} → Reach ω ω′ → Reach ω′ ω″ → Reach ω ω″
reach-trans {ω} (xs , refl) (ys , refl) = xs ++ ys , foldl-++ stepL ω xs ys

reach-cons : ∀ x o → Reach (Φ o) (Φ (x ∷ o))
reach-cons x o = x ∷ [] , sym (Φ-cons x o)

------------------------------------------------------------------------
-- Blanks the layout takes back
------------------------------------------------------------------------

-- | Every blank in what is written was written where no line end waited.
data SpOK : List Lexeme → Set where
  sp-[]   : SpOK []
  sp-lsp  : ∀ {o} → SpOK o → waits o ≡ false → SpOK (lsp ∷ o)
  sp-lt   : ∀ {t o} → SpOK o → SpOK (lt t ∷ o)
  sp-lnl  : ∀ {o} → SpOK o → SpOK (lnl ∷ o)
  sp-lind : ∀ {i o} → SpOK o → SpOK (lind i ∷ o)
  sp-lcm  : ∀ {c o} → SpOK o → SpOK (lcm c ∷ o)

private
  lsp-id : ∀ ω → proj₂ ω ≡ false → stepL ω lsp ≡ ω
  lsp-id (w , false) refl = refl

-- | A blank taken back was nothing to the walker.
trim-Φ : ∀ o → SpOK o → Φ (trim o) ≡ Φ o
trim-Φ []          sp-[]          = refl
trim-Φ (lsp ∷ o)   (sp-lsp ok w)  = trans (trim-Φ o ok) (sym (trans (Φ-cons lsp o) (lsp-id (Φ o) w)))
trim-Φ (lt _ ∷ o)  (sp-lt ok)     = refl
trim-Φ (lnl ∷ o)   (sp-lnl ok)    = refl
trim-Φ (lind _ ∷ o) (sp-lind ok)  = refl
trim-Φ (lcm _ ∷ o) (sp-lcm ok)    = refl

trim-ok : ∀ o → SpOK o → SpOK (trim o)
trim-ok []           sp-[]         = sp-[]
trim-ok (lsp ∷ o)    (sp-lsp ok _) = trim-ok o ok
trim-ok (lt _ ∷ o)   ok            = ok
trim-ok (lnl ∷ o)    ok            = ok
trim-ok (lind _ ∷ o) ok            = ok
trim-ok (lcm _ ∷ o)  ok            = ok

-- | The layout state the walker can be read along: blanks as above, and a
-- line with text on it has no line end waiting.
record LI (σ : St) : Set where
  constructor li
  field
    sps   : SpOK (St.out σ)
    plain : St.pend σ ≡ nothing → waits (St.out σ) ≡ false

private
  waits-lt : ∀ t o → waits (lt t ∷ o) ≡ false
  waits-lt t o = cong proj₂ (Φ-cons (lt t) o)

  waits-lsp : ∀ o → waits (lsp ∷ o) ≡ false
  waits-lsp o = cong proj₂ (Φ-cons lsp o)

  -- a token's lexeme, after the pending indentation
  put-lt : ∀ t n σ → LI σ → LI (put (lt t) n σ) × Reach (Φ (St.out σ)) (Φ (St.out (put (lt t) n σ)))
  put-lt t n (st o c (just i) e) (li ok _) =
    li (sp-lt (sp-lind ok)) (λ _ → waits-lt t (lind i ∷ o)) ,
    reach-trans (reach-cons (lind i) o) (reach-cons (lt t) (lind i ∷ o))
  put-lt t n (st o c nothing e) (li ok _) = li (sp-lt ok) (λ _ → waits-lt t o) , reach-cons (lt t) o

  space-ok : ∀ σ → LI σ → LI (space σ) × Reach (Φ (St.out σ)) (Φ (St.out (space σ)))
  space-ok (st o c (just i) e) l = l , reach-refl
  space-ok (st o c nothing e) (li ok pl) = li (sp-lsp ok (pl refl)) (λ _ → waits-lsp o) , reach-cons lsp o

  token-ok : ∀ t σ → LI σ → LI (token t σ) × Reach (Φ (St.out σ)) (Φ (St.out (token t σ)))
  token-ok t (st [] c p e) l = put-lt t _ (st [] c p e) l
  token-ok t (st (lt u ∷ o) c (just i) e) l = put-lt t _ _ l
  token-ok t (st (lt u ∷ o) c nothing e) l = pick (apart u t)
    where
      σ = st (lt u ∷ o) c nothing e
      pick : ∀ b → LI (if b then put (lt t) _ (space σ) else put (lt t) _ σ) ×
                   Reach (Φ (lt u ∷ o)) (Φ (St.out (if b then put (lt t) _ (space σ) else put (lt t) _ σ)))
      pick true  with space-ok σ l
      ... | l′ , r′ with put-lt t _ (space σ) l′
      ...   | l″ , r″ = l″ , reach-trans r′ r″
      pick false = put-lt t _ σ l
  token-ok t (st (lsp ∷ o) c p e) l    = put-lt t _ _ l
  token-ok t (st (lnl ∷ o) c p e) l    = put-lt t _ _ l
  token-ok t (st (lind _ ∷ o) c p e) l = put-lt t _ _ l
  token-ok t (st (lcm _ ∷ o) c p e) l  = put-lt t _ _ l

-- | A line end, as the walker reads it.
brk-ok : ∀ i σ → LI σ → LI (brk i σ) × Reach (Φ (St.out σ)) (Φ (St.out (brk i σ)))
brk-ok i (st o c (just _) []) l = li (LI.sps l) (λ ()) , reach-refl
brk-ok i (st o c (just j) (x ∷ xs)) (li ok _) =
  li (sp-lnl (sp-lcm (sp-lind ok))) (λ ()) ,
  reach-trans (reach-cons (lind j) o)
    (reach-trans (reach-cons (lcm (joined (x ∷ xs))) (lind j ∷ o)) (reach-cons lnl (lcm (joined (x ∷ xs)) ∷ lind j ∷ o)))
brk-ok i (st o c nothing []) (li ok pl) =
  li (sp-lnl (trim-ok o ok)) (λ ()) ,
  subst-reach (sym (trim-Φ o ok)) (reach-cons lnl (trim o))
  where
    subst-reach : ∀ {ω ω′ ω″} → ω ≡ ω′ → Reach ω′ ω″ → Reach ω ω″
    subst-reach refl r = r
brk-ok i (st o c nothing (x ∷ xs)) (li ok pl) =
  li (sp-lnl (sp-lcm (sp-lsp (trim-ok o ok) (trans (cong proj₂ (trim-Φ o ok)) (pl refl))))) (λ ()) ,
  subst-reach (sym (trim-Φ o ok))
    (reach-trans (reach-cons lsp (trim o))
      (reach-trans (reach-cons (lcm (joined (x ∷ xs))) (lsp ∷ trim o)) (reach-cons lnl (lcm (joined (x ∷ xs)) ∷ lsp ∷ trim o))))
  where
    subst-reach : ∀ {ω ω′ ω″} → ω ≡ ω′ → Reach ω′ ω″ → Reach ω ω″
    subst-reach refl r = r

private
  comment-ok : ∀ i s σ → LI σ → LI (comment i s σ) × Reach (Φ (St.out σ)) (Φ (St.out (comment i s σ)))
  comment-ok i s (st o c p e) (li ok pl) = brk-ok i (st o c p (e ++ s ∷ [])) (li ok pl)

  blank-ok : ∀ i σ → LI σ → LI (blankLine i σ) × Reach (Φ (St.out σ)) (Φ (St.out (blankLine i σ)))
  blank-ok i σ l with brk i σ | brk-ok i σ l
  ... | st [] c p e      | li ok _ , r = li ok (λ ()) , r
  ... | st (x ∷ o) c p e | li ok _ , r = li (sp-lnl ok) (λ ()) , reach-trans r (reach-cons lnl (x ∷ o))

  para-ok : ∀ i ls σ → LI σ → LI (paragraph i ls σ) × Reach (Φ (St.out σ)) (Φ (St.out (paragraph i ls σ)))
  para-ok i []       σ l = l , reach-refl
  para-ok i (x ∷ ls) σ l with comment-ok i (Data.String.fromList (dashed x)) σ l
  ... | l′ , r′ with para-ok i ls _ l′
  ...   | l″ , r″ = l″ , reach-trans r′ r″

-- | Every step of the layout is a step of the walker.
layout-reach : ∀ i f d σ → LI σ → LI (layout i f d σ) × Reach (Φ (St.out σ)) (Φ (St.out (layout i f d σ)))
layout-reach i f empty σ l = l , reach-refl
layout-reach i f (tk t) σ l = token-ok t σ l
layout-reach i f sp σ l = space-ok σ l
layout-reach i f (cmt c) σ l = comment-ok i c σ l
layout-reach i f (para ws) σ l = para-ok i (fill i (column σ Data.Nat.+ 2) [] ws) σ l
layout-reach i true line σ l = space-ok σ l
layout-reach i false line σ l = brk-ok i σ l
layout-reach i f newline σ l = brk-ok i σ l
layout-reach zero f blank σ l = blank-ok zero σ l
layout-reach (suc i) f blank σ l = brk-ok (suc i) σ l
layout-reach i f (eol s) (st o c p e) l = li (LI.sps l) (LI.plain l) , reach-refl
layout-reach i f (a <> b) σ l with layout-reach i f a σ l
... | l′ , r′ with layout-reach i f b _ l′
...   | l″ , r″ = l″ , reach-trans r′ r″
layout-reach i f (nest n d) σ l = layout-reach (i Data.Nat.+ n) f d σ l
layout-reach i true (group d) σ l = layout-reach i true d σ l
layout-reach i false (group d) σ l = layout-reach i _ d σ l

------------------------------------------------------------------------
-- Comment lines on lines of their own
------------------------------------------------------------------------

open import Data.List using (map; concatMap)
open import Data.Product using (∃-syntax)
open import Data.Nat using (_+_)
open import Once.Format.Doc using (paragraph; dashed; fill)
open import Data.Char using (Char)
open import Data.String using (toList; fromList)
open import Once.Format.Comment using (commentLinesDoc; lineDoc; classify; CLine; prose; verbatim)
open import Once.Format.Proof.Rerender using (renderK; renderLine)
open import Once.Format.Doc using (lineComment)
open import Relation.Binary.PropositionalEquality using (cong₂)

-- | Lines written at indentation `i`, each on a line of its own.
linesOut : ℕ → List (List Char) → List Lexeme → List Lexeme
linesOut i []       o = o
linesOut i (L ∷ Ls) o = linesOut i Ls (lnl ∷ lcm L ∷ lind i ∷ o)

colOf : ∀ {A : Set} → List A → ℕ → ℕ
colOf []      c = c
colOf (_ ∷ _) c = 0

zero-col : ∀ {A : Set} (ls : List A) → colOf ls 0 ≡ 0
zero-col []      = refl
zero-col (_ ∷ _) = refl

linesOut-++ : ∀ i A B o → linesOut i (A ++ B) o ≡ linesOut i B (linesOut i A o)
linesOut-++ i []       B o = refl
linesOut-++ i (L ∷ A)  B o = linesOut-++ i A B _

para-lines : ∀ i ls o c → paragraph i ls (st o c (just i) [])
           ≡ st (linesOut i (map (λ l → lineComment (toList (fromList (dashed l)))) ls) o) (colOf ls c) (just i) []
para-lines i []       o c = refl
para-lines i (l ∷ ls) o c =
  trans (para-lines i ls (lnl ∷ lcm (lineComment (toList (fromList (dashed l)))) ∷ lind i ∷ o) 0)
    (cong (λ x → st (linesOut i (map (λ l → lineComment (toList (fromList (dashed l)))) ls)
                      (lnl ∷ lcm (lineComment (toList (fromList (dashed l)))) ∷ lind i ∷ o)) x (just i) []) (zero-col ls))

line-layout : ∀ i f k o c → ∃[ c′ ] layout i f (lineDoc k) (st o c (just i) []) ≡ st (linesOut i (renderK i k) o) c′ (just i) []
line-layout i f (prose ws)   o c = _ , para-lines i (fill i (i + 2) [] ws) o c
line-layout i f (verbatim v) o c = 0 , refl

-- | A run of comment lines, laid out from the start of a line: the lines,
-- each on a line of its own.
lines-layout : ∀ i f ls o c → layout i f (commentLinesDoc ls) (st o c (just i) [])
             ≡ st (linesOut i (concatMap (renderLine i) ls) o) (colOf ls c) (just i) []
lines-layout i f []       o c = refl
lines-layout i f (l ∷ ls) o c with line-layout i f (classify l) o c
... | c′ , e =
  trans (cong (λ σ → layout i f (commentLinesDoc ls) (brk i σ)) e)
    (trans (lines-layout i f ls (linesOut i (renderK i (classify l)) o) 0)
      (cong₂ (λ O x → st O x (just i) []) (sym (linesOut-++ i (renderK i (classify l)) (concatMap (renderLine i) ls) o))
             (zero-col ls)))

