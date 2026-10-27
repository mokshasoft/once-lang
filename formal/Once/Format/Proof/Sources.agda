-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Sources — the comments a text has (plan 0.124 step
-- 4.5).
--
-- The lexer's comments are `--` and what follows on the line, or `{-` and
-- what follows to the close (`items-raw`, by the lexer's own clauses). The
-- walker keeps each without its trailing blanks (`Rerender.Src`): a line
-- comment with no line end and no blank at its end, or a block comment
-- (`trivia-src`). That is what the formatter needs to write a comment so that
-- it reads back as itself.
------------------------------------------------------------------------

module Once.Format.Proof.Sources where

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Char using (Char; isDigit)
import Data.Char as Ch
open import Data.List using (List; []; _∷_; _++_; reverse; length; take; map)
open import Data.List.Properties using (++-assoc; unfold-reverse; reverse-++; length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _∸_; _+_)
open import Data.Nat.Properties using (+-∸-assoc; m+n∸n≡m)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (does)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Surface.Lexing using (LineRest; lr-end; lr-nl; lr-char)
open import Once.Parser.Token using (TLe; TLt; TGe; TGt; TEqEq; TEquals; TNeq; TBang)
open import Once.Parser.Lexer using (headK; hkWS; hkNL; hkCaret; hkDash; hkLBrace; hkLt; hkGt; hkEq; hkBang;
  hkLParen; hkRParen; hkRBrace; hkColon; hkLambda; hkComma; hkSemi; hkAt; hkPipe; hkPlus; hkStar; hkSlash; hkPct;
  hkAmp; hkDot; hkStr; hkGen; d-comment; d-arrow; d-minus; c-1; c-0; c-w; c-gen; nlIndent; isEqHead; isDashHead;
  dashClass; caretClass; drop1; adv; collectStringB; collectIdentB; collectDigitsB; collectFracB; skipLineB; skipBlockB;
  isIdentStart)
open import Once.Adequacy.SpecLexing using (line-sound)
open import Once.Format.Lex using (Item; tok; comment; cont; consumed; items-WF; it-head; it-str; it-gen; it-num;
  it-nl; it-op2; it-lbrace; it-minus; it-caret; lexItems)
open import Once.Format.Proof.Rerender using (NoNl; NoTrail; LineC; Src; src-line; src-block; is-true)

------------------------------------------------------------------------
-- The lexer's comments
------------------------------------------------------------------------

-- | A comment as the lexer reads it.
RawC : List Char → Set
RawC cs = (∃[ b ] cs ≡ '-' ∷ '-' ∷ b × NoNl b) ⊎ (∃[ b ] cs ≡ '{' ∷ '-' ∷ b)

ComOK : Item → Set
ComOK (tok _)     = ⊤
ComOK cont        = ⊤
ComOK (comment c) = RawC (toList c)

private
  lr-split : ∀ {cs r} → LineRest cs r → ∃[ pre ] cs ≡ pre ++ r × NoNl pre
  lr-split lr-end         = [] , refl , []
  lr-split lr-nl          = [] , refl , []
  lr-split (lr-char n lr) with lr-split lr
  ... | pre , e , nn = _ ∷ pre , cong (_ ∷_) e , n ∷ nn

  take-++ : ∀ (xs ys : List Char) → take (length xs) (xs ++ ys) ≡ xs
  take-++ []       ys = refl
  take-++ (x ∷ xs) ys = cong (x ∷_) (take-++ xs ys)

  consumed-++ : ∀ xs ys → consumed (xs ++ ys) ys ≡ xs
  consumed-++ xs ys rewrite length-++ xs {ys} | m+n∸n≡m (length xs) (length ys) = take-++ xs ys

  raw-line : ∀ c cs → c ≡ '-' → RawC ('-' ∷ consumed (c ∷ cs) (proj₁ (skipLineB cs)))
  raw-line .'-' cs refl with lr-split (line-sound cs)
  ... | pre , e , nn =
    inj₁ (pre , cong (λ x → '-' ∷ x) (trans (cong (λ y → consumed ('-' ∷ y) (proj₁ (skipLineB cs))) e)
                                             (consumed-++ ('-' ∷ pre) (proj₁ (skipLineB cs)))) , nn)

  raw-block : ∀ c cs → c ≡ '-' → RawC ('{' ∷ consumed (c ∷ cs) (proj₁ (skipBlockB 1 cs)))
  raw-block .'-' cs refl rewrite +-∸-assoc 1 (proj₂ (skipBlockB 1 cs)) = inj₂ (_ , refl)

-- | The lexer's comments are line and block comments.
items-raw : ∀ cs → All ComOK (lexItems cs)
ok-WF  : ∀ cs off a → All ComOK (items-WF cs off a)
ok-head : ∀ c cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) k → All ComOK (it-head c cs off rec k)
ok-str : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) m → All ComOK (it-str cs off rec m)
ok-gen : ∀ c cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) b₁ b₂ → All ComOK (it-gen c cs off rec b₁ b₂)
ok-num : ∀ c cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) ds rest bnd m → All ComOK (it-num c cs off rec ds rest bnd m)
ok-nl  : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) b → All ComOK (it-nl cs off rec b)
ok-op2 : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) t2 t1 b → All ComOK (it-op2 cs off rec t2 t1 b)
ok-dash  : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) → All ComOK (it-minus cs off rec (dashClass cs))
ok-brace : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) → All ComOK (it-lbrace cs off rec (isDashHead cs))
ok-caret : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) k → All ComOK (it-caret cs off rec k)

ok-WF [] off _ = tt ∷ []
ok-WF (c ∷ cs) off (acc rec) = ok-head c cs off rec (headK c)

ok-head c cs off rec hkWS     = ok-WF cs _ _
ok-head c cs off rec hkNL     = ok-nl cs off rec (nlIndent cs)
ok-head c cs off rec hkCaret  = ok-caret cs off rec (caretClass cs)
ok-head c cs off rec hkDash   = ok-dash cs off rec
ok-head c cs off rec hkLBrace = ok-brace cs off rec
ok-head c cs off rec hkLt     = ok-op2 cs off rec TLe TLt (isEqHead cs)
ok-head c cs off rec hkGt     = ok-op2 cs off rec TGe TGt (isEqHead cs)
ok-head c cs off rec hkEq     = ok-op2 cs off rec TEqEq TEquals (isEqHead cs)
ok-head c cs off rec hkBang   = ok-op2 cs off rec TNeq TBang (isEqHead cs)
ok-head c cs off rec hkLParen = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkRParen = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkRBrace = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkColon  = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkLambda = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkComma  = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkSemi   = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkAt     = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkPipe   = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkPlus   = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkStar   = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkSlash  = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkPct    = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkAmp    = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkDot    = tt ∷ (ok-WF cs _ _)
ok-head c cs off rec hkStr    = ok-str cs off rec (collectStringB cs)
ok-head c cs off rec hkGen    = ok-gen c cs off rec (isDigit c) (isIdentStart c)

ok-str cs off rec (just (s , rest , bnd)) = tt ∷ (ok-WF rest _ _)
ok-str cs off rec nothing = []
ok-gen c cs off rec true _ =
  ok-num c cs off rec (proj₁ (collectDigitsB cs)) (proj₁ (proj₂ (collectDigitsB cs)))
    (proj₂ (proj₂ (collectDigitsB cs))) (collectFracB (proj₁ (proj₂ (collectDigitsB cs))))
ok-gen c cs off rec false true =
  tt ∷ (ok-WF (proj₁ (proj₂ (collectIdentB cs))) _ _)
ok-gen c cs off rec false false = []

ok-num c cs off rec ds rest bnd (just (frac , rest' , fbnd)) = tt ∷ (ok-WF rest' _ _)
ok-num c cs off rec ds rest bnd nothing = tt ∷ (ok-WF rest _ _)

ok-nl cs off rec true  = tt ∷ ok-WF cs _ _
ok-nl cs off rec false = tt ∷ (ok-WF cs _ _)

ok-op2 cs off rec t2 t1 true  = tt ∷ (ok-WF (drop1 cs) _ _)
ok-op2 cs off rec t2 t1 false = tt ∷ (ok-WF cs _ _)

ok-brace []       off rec = tt ∷ tt ∷ []
ok-brace (c ∷ cs) off rec = pick (does (c Ch.≟ '-')) refl
  where
    pick : ∀ b → does (c Ch.≟ '-') ≡ b → All ComOK (it-lbrace (c ∷ cs) off rec b)
    pick true  e = subst RawC (sym (toList∘fromList ('{' ∷ consumed (c ∷ cs) (proj₁ (skipBlockB 1 cs))))) (raw-block c cs (is-true c '-' e)) ∷
                   ok-WF (proj₁ (skipBlockB 1 cs)) (adv (c ∷ cs) (proj₁ (skipBlockB 1 cs)) off) (rec _)
    pick false _ = tt ∷ ok-WF (c ∷ cs) (adv (c ∷ cs) (c ∷ cs) off) (rec _)

ok-dash []       off rec = tt ∷ tt ∷ []
ok-dash (c ∷ cs) off rec = pick (does (c Ch.≟ '-')) refl
  where
    pick : ∀ b → does (c Ch.≟ '-') ≡ b
         → All ComOK (it-minus (c ∷ cs) off rec (if b then d-comment else (if does (c Ch.≟ '>') then d-arrow else d-minus)))
    pick true  e = subst RawC (sym (toList∘fromList ('-' ∷ consumed (c ∷ cs) (proj₁ (skipLineB cs))))) (raw-line c cs (is-true c '-' e)) ∷
                   ok-WF (proj₁ (skipLineB cs)) (adv (c ∷ cs) (proj₁ (skipLineB cs)) off) (rec _)
    pick false _ = pick₂ (does (c Ch.≟ '>'))
      where
        pick₂ : ∀ b → All ComOK (it-minus (c ∷ cs) off rec (if b then d-arrow else d-minus))
        pick₂ true  = tt ∷ ok-WF cs (adv (c ∷ cs) cs off) (rec _)
        pick₂ false = tt ∷ ok-WF (c ∷ cs) (adv (c ∷ cs) (c ∷ cs) off) (rec _)

ok-caret cs off rec c-1   = tt ∷ (ok-WF (drop1 cs) _ _)
ok-caret cs off rec c-0   = tt ∷ (ok-WF (drop1 cs) _ _)
ok-caret cs off rec c-w   = tt ∷ (ok-WF (drop1 cs) _ _)
ok-caret cs off rec c-gen = []


items-raw cs = ok-WF cs 0 _

------------------------------------------------------------------------
-- The walker keeps them without their trailing blanks
------------------------------------------------------------------------

open import Once.Format.Comment using (blankish)
open import Once.Format.Print using (W; walker; Line; line-empty; line-code; line-text; Note; note-comment; note-blank;
  Notes; notes; noNotes; Trivia; lookupNotes; addTo; addTop; addInner; addAfter; Held; held-comment; held-blank;
  settleAt; settle; blankBefore; lineEnd; pending; stepTok; stepComment; afterCode; step;
  walkItems; finish; trivia; trimEnd; dropLead)
open import Once.Format.Proof.Rerender using (dropLead-keep; all-rev; all-revA; notrail-++)
import Once.Format.Proof.Walk

private
  dl-++ : ∀ xs y ys → blankish y ≡ false → dropLead (xs ++ y ∷ ys) ≡ dropLead xs ++ y ∷ ys
  dl-++ []       y ys nb = dropLead-keep y ys nb
  dl-++ (x ∷ xs) y ys nb = pick (blankish x)
    where
      pick : ∀ b → (if b then dropLead (xs ++ y ∷ ys) else x ∷ xs ++ y ∷ ys) ≡ (if b then dropLead xs else x ∷ xs) ++ y ∷ ys
      pick true  = dl-++ xs y ys nb
      pick false = refl

  dl-all : ∀ {P : Char → Set} cs → All P cs → All P (dropLead cs)
  dl-all []       []       = []
  dl-all (c ∷ cs) (p ∷ ps) = pick (blankish c)
    where
      pick : ∀ b → All _ (if b then dropLead cs else c ∷ cs)
      pick true  = dl-all cs ps
      pick false = p ∷ ps

  dl-head : ∀ cs → dropLead cs ≡ [] ⊎ ∃[ z ] ∃[ zs ] dropLead cs ≡ z ∷ zs × blankish z ≡ false
  dl-head []       = inj₁ refl
  dl-head (c ∷ cs) = pick (blankish c) refl
    where
      pick : ∀ b → blankish c ≡ b → (if b then dropLead cs else c ∷ cs) ≡ [] ⊎
             ∃[ z ] ∃[ zs ] (if b then dropLead cs else c ∷ cs) ≡ z ∷ zs × blankish z ≡ false
      pick true  _ = dl-head cs
      pick false e = inj₂ (c , cs , refl , e)

  -- the characters of a comment two non-blanks start, its trailing blanks dropped
  trim-chars : ∀ cs a d b → cs ≡ a ∷ d ∷ b → blankish d ≡ false
             → toList (fromList (reverse (dropLead (reverse cs)))) ≡ a ∷ d ∷ reverse (dropLead (reverse b))
  trim-chars cs a d b refl nb =
    trans (toList∘fromList _)
      (trans (cong (λ x → reverse (dropLead x)) (reverse-++ (a ∷ d ∷ []) b))
        (trans (cong reverse (dl-++ (reverse b) d (a ∷ []) nb)) (reverse-++ (dropLead (reverse b)) (d ∷ a ∷ []))))

  trim-tail : ∀ b → NoNl b → NoNl (reverse (dropLead (reverse b))) × NoTrail ('-' ∷ '-' ∷ reverse (dropLead (reverse b)))
  trim-tail b nn with dl-head (reverse b)
  ... | inj₁ e = all-rev (dl-all _ (all-rev nn)) , subst (λ r → NoTrail ('-' ∷ '-' ∷ reverse r)) (sym e) ('-' ∷ [] , '-' , refl , refl)
  ... | inj₂ (z , zs , e , nb) =
    all-rev (dl-all _ (all-rev nn)) ,
    subst (λ r → NoTrail ('-' ∷ '-' ∷ reverse r)) (sym e)
      (notrail-++ ('-' ∷ '-' ∷ []) (reverse (z ∷ zs)) (reverse zs , z , unfold-reverse z zs , nb))

-- | A comment the lexer read, without its trailing blanks, is one the
-- formatter writes so it reads back.
trimEnd-src : ∀ c → RawC (toList c) → Src (trimEnd c)
trimEnd-src c (inj₁ (b , e , nn)) = src-line (reverse (dropLead (reverse b)) , trim-chars (toList c) '-' '-' b e refl , trim-tail b nn)
trimEnd-src c (inj₂ (b , e))      = src-block (trim-chars (toList c) '{' '-' b e refl)

NoteSrc : Note → Set
NoteSrc (note-comment c) = Src c
NoteSrc note-blank       = ⊤

-- | Every comment in an anchor's notes is one the formatter writes back.
NotesSrc : Notes → Set
NotesSrc n = All NoteSrc (Notes.top n) × All Src (Notes.inner n) × All Src (Notes.after n)

TrivSrc : Trivia → Set
TrivSrc = All (λ e → NotesSrc (proj₂ e))

private
  HeldSrc : Held → Set
  HeldSrc (held-comment c) = Src c
  HeldSrc held-blank         = ⊤

  LineSrc : Line → Set
  LineSrc (line-text cs) = All Src cs
  LineSrc line-empty     = ⊤
  LineSrc line-code      = ⊤

  record WSrc (σ : W) : Set where
    constructor wsrc
    field
      lineS : LineSrc (W.ln σ)
      heldS : All HeldSrc (W.held σ)
      notes′ : TrivSrc (W.acc σ)

  noNotes-src : NotesSrc noNotes
  noNotes-src = [] , [] , []

  addTo-src : ∀ k f t → (∀ n → NotesSrc n → NotesSrc (f n)) → TrivSrc t → TrivSrc (addTo k f t)
  addTo-src k f []             ff []         = ff noNotes noNotes-src ∷ []
  addTo-src k f ((j , n) ∷ ts) ff (p ∷ ps)   = pick (k Data.Nat.≡ᵇ j)
    where
      pick : ∀ b → TrivSrc (if b then (j , f n) ∷ ts else (j , n) ∷ addTo k f ts)
      pick true  = ff n p ∷ ps
      pick false = p ∷ addTo-src k f ts ff ps

  top-src : ∀ x → NoteSrc x → ∀ n → NotesSrc n → NotesSrc (addTop x n)
  top-src x px (notes t i a) (pt , pi , pa) = AllP.++⁺ pt (px ∷ []) , pi , pa

  inner-src : ∀ x → Src x → ∀ n → NotesSrc n → NotesSrc (addInner x n)
  inner-src x px (notes t i a) (pt , pi , pa) = pt , AllP.++⁺ pi (px ∷ []) , pa

  after-src : ∀ x → Src x → ∀ n → NotesSrc n → NotesSrc (addAfter x n)
  after-src x px (notes t i a) (pt , pi , pa) = pt , pi , AllP.++⁺ pa (px ∷ [])

  settle-src : ∀ k f hs t → All HeldSrc hs → TrivSrc t → TrivSrc (settleAt k f hs t)
  settle-src k _     []                    t []       pt = pt
  settle-src k true  (held-comment h ∷ hs) t (p ∷ ps) pt =
    settle-src k true hs _ ps (addTo-src k _ t (top-src (note-comment h) p) pt)
  settle-src k false (held-comment h ∷ hs) t (p ∷ ps) pt =
    settle-src k false hs _ ps (addTo-src k _ t (inner-src h p) pt)
  settle-src k true  (held-blank ∷ hs)     t (p ∷ ps) pt =
    settle-src k true hs _ ps (addTo-src k _ t (top-src note-blank tt) pt)
  settle-src k false (held-blank ∷ hs)     t (p ∷ ps) pt = settle-src k false hs t ps pt

  blankBefore-src : ∀ b hs → All HeldSrc hs → All HeldSrc (blankBefore b hs)
  blankBefore-src b hs ps = pick (2 Data.Nat.<ᵇ suc b)
    where
      pick : ∀ c → All HeldSrc (if c then hs ++ (held-blank ∷ []) else hs)
      pick true  = AllP.++⁺ ps (tt ∷ [])
      pick false = ps

  map-held : ∀ cs → All Src cs → All HeldSrc (map held-comment cs)
  map-held []       []       = []
  map-held (c ∷ cs) (p ∷ ps) = p ∷ map-held cs ps

  pending-src : ∀ ln hs → LineSrc ln → All HeldSrc hs → All HeldSrc (pending ln hs)
  pending-src (line-text cs) hs pl ph = AllP.++⁺ ph (map-held cs pl)
  pending-src line-empty     hs _  ph = ph
  pending-src line-code      hs _  ph = ph

  lineEnd-src : ∀ top σ → WSrc σ → WSrc (lineEnd top σ)
  lineEnd-src top (walker k h (line-text cs) hs b fr t) (wsrc pl ph pa) = wsrc tt (AllP.++⁺ ph (map-held cs pl)) pa
  lineEnd-src top (walker k h line-empty hs b fr t)    (wsrc pl ph pa) = wsrc tt ph pa
  lineEnd-src top (walker k h line-code hs b fr t)     (wsrc pl ph pa) = wsrc tt ph pa

  nc-src : ∀ cs → All Src cs → All NoteSrc (map note-comment cs)
  nc-src []       []       = []
  nc-src (c ∷ cs) (p ∷ ps) = p ∷ nc-src cs ps

  hoist-trivsrc : ∀ k t → TrivSrc t → TrivSrc (Once.Format.Print.hoist k t)
  hoist-trivsrc k []             []       = []
  hoist-trivsrc k ((j , n) ∷ ts) (p ∷ ps) = pick (k Data.Nat.≡ᵇ j)
    where
      pick : ∀ b → TrivSrc (if b then (j , notes (Notes.top n ++ map note-comment (Notes.inner n)) [] (Notes.after n)) ∷ ts
                            else (j , n) ∷ Once.Format.Print.hoist k ts)
      pick true  = (AllP.++⁺ (proj₁ p) (nc-src _ (proj₁ (proj₂ p))) , [] , proj₂ (proj₂ p)) ∷ ps
      pick false = p ∷ hoist-trivsrc k ts ps

  hoistW-src : ∀ σ → WSrc σ → WSrc (Once.Format.Print.hoistW σ)
  hoistW-src (walker k h ln hs b fr t) (wsrc pl ph pa) =
    wsrc pl ph (Once.Format.Proof.Walk.hoistAt-cases k t TrivSrc pa (hoist-trivsrc k t pa))

  tok-src : ∀ σ a e → WSrc σ → WSrc (stepTok σ a e)
  tok-src σ a true w = hoistW-src (lineEnd true σ) (lineEnd-src true σ w)
  tok-src (walker k h ln hs b fr t) a false (wsrc pl ph pa) =
    wsrc tt [] (settle-src k fr _ t (pending-src ln _ pl (blankBefore-src b hs ph)) pa)

  com-src : ∀ σ c → Src c → WSrc σ → WSrc (stepComment σ c)
  com-src (walker k h line-empty hs b fr t) c pc (wsrc pl ph pa) = wsrc (pc ∷ []) (blankBefore-src b hs ph) pa
  com-src (walker k h (line-text cs) hs b fr t) c pc (wsrc pl ph pa) = wsrc (AllP.++⁺ pl (pc ∷ [])) ph pa
  com-src (walker k true line-code hs b fr t) c pc (wsrc pl ph pa) = wsrc tt ph (addTo-src (k Data.Nat.∸ 1) _ t (after-src c pc) pa)
  com-src (walker k false line-code hs b fr t) c pc (wsrc pl ph pa) = wsrc tt (AllP.++⁺ ph (pc ∷ [])) pa

  step-src : ∀ σ i → ComOK i → WSrc σ → WSrc (step σ i)
  step-src σ (tok x)     _  w = tok-src σ (Once.Format.Print.isAnchor x) (Once.Format.Print.isLineEnd x) w
  step-src σ cont        _  w = lineEnd-src false σ w
  step-src σ (comment c) rc w = com-src σ (trimEnd c) (trimEnd-src c rc) w

  walk-src : ∀ σ is → All ComOK is → WSrc σ → WSrc (walkItems σ is)
  walk-src σ []       []       w = w
  walk-src σ (i ∷ is) (p ∷ ps) w = walk-src (step σ i) is ps (step-src σ i p w)

  settle-W : ∀ σ → WSrc σ → TrivSrc (W.acc (settle σ))
  settle-W (walker k h ln hs b fr t) (wsrc _ ph pa) = settle-src k fr _ t ph pa

-- | The comments in a text's trivia are ones the formatter writes back.
trivia-src : ∀ cs → TrivSrc (trivia (lexItems cs))
trivia-src cs =
  settle-W (Once.Format.Print.hoistW (lineEnd true (walkItems _ (lexItems cs))))
    (hoistW-src _ (lineEnd-src true _ (walk-src _ (lexItems cs) (items-raw cs) (wsrc tt [] []))))

-- | So are an anchor's.
lookup-src : ∀ j t → TrivSrc t → NotesSrc (lookupNotes j t)
lookup-src j []             []       = noNotes-src
lookup-src j ((i , n) ∷ ts) (p ∷ ps) = pick (j Data.Nat.≡ᵇ i)
  where
    pick : ∀ b → NotesSrc (if b then n else lookupNotes j ts)
    pick true  = p
    pick false = lookup-src j ts ps
