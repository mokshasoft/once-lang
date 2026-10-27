-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Groups — the comments before a declaration and at the
-- end, formatted twice (plan 0.124 step 4.5).
--
-- What stands before a declaration is comments and blank lines; the printer
-- writes the comments in runs (`Print.runs`), a blank line between two runs
-- where the source had one, at the start of their lines. So the notes print
-- as their runs (`groups`, `runs-layout`). The walk over those lines holds
-- each, at the start of a line, before the declaration, a blank between two
-- runs (`run-walk`); the second pass prints those held comments as runs of
-- the written lines, which it writes again (`Rerender.rendered-fix`).
------------------------------------------------------------------------

module Once.Format.Proof.Groups where

open import Data.Bool using (Bool; true; false; not; if_then_else_; T)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; reverse)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Format.Doc using (Doc; empty; blank; _<>_; Lexeme; lt; lsp; lnl; lind; lcm; St; st; brk; layout;
  blankLine)
open import Once.Format.Comment using (commentRun; commentLines)
open import Once.Format.Print using (Note; note-comment; note-blank; runs)
open import Once.Format.Proof.Rerender using (rendered; rendered-ne; readBack; rendered-fix; rendered-RL; Src)
open import Once.Format.Proof.Lockstep using (linesOut; colOf; zero-col; lines-layout)

------------------------------------------------------------------------
-- Runs of comments
------------------------------------------------------------------------

-- | The runs of comments in notes, as `Print.runs` reads them: a blank line
-- between two comments ends a run.
groups : List Note → List String → Bool → List (List String)
groups []                    []          _     = []
groups []                    acc@(_ ∷ _) _     = acc ∷ []
groups (note-blank ∷ ns)     acc         _     = groups ns acc true
groups (note-comment c ∷ ns) []          _     = groups ns (c ∷ []) false
groups (note-comment c ∷ ns) acc@(_ ∷ _) false = groups ns (acc ++ (c ∷ [])) false
groups (note-comment c ∷ ns) acc@(_ ∷ _) true  = acc ∷ groups ns (c ∷ []) false

-- | Runs laid out, a blank line between two.
layoutG : ℕ → Bool → List (List String) → St → St
layoutG i f []            σ = σ
layoutG i f (R ∷ [])      σ = layout i f (commentRun R) σ
layoutG i f (R ∷ R′ ∷ Rs) σ = layoutG i f (R′ ∷ Rs) (layout i f blank (layout i f (commentRun R) σ))

groups-ne : ∀ ns c cs sd → ∃[ R ] ∃[ Rs ] groups ns (c ∷ cs) sd ≡ R ∷ Rs
groups-ne []                    c cs sd    = _ , [] , refl
groups-ne (note-blank ∷ ns)     c cs sd    = groups-ne ns c cs true
groups-ne (note-comment d ∷ ns) c cs false = groups-ne ns c (cs ++ d ∷ []) false
groups-ne (note-comment d ∷ ns) c cs true  = c ∷ cs , _ , refl

-- | Notes print as their runs.
runs-layout : ∀ i f ns acc sd σ → layout i f (runs ns acc sd) σ ≡ layoutG i f (groups ns acc sd) σ
runs-layout i f []                    []          sd    σ = refl
runs-layout i f []                    (a ∷ as)    sd    σ = refl
runs-layout i f (note-blank ∷ ns)     acc         sd    σ = runs-layout i f ns acc true σ
runs-layout i f (note-comment c ∷ ns) []          sd    σ = runs-layout i f ns (c ∷ []) false σ
runs-layout i f (note-comment c ∷ ns) (a ∷ as)    false σ = runs-layout i f ns (a ∷ as ++ c ∷ []) false σ
runs-layout i f (note-comment c ∷ ns) (a ∷ as)    true  σ with groups-ne ns c [] false
... | R , Rs , e rewrite e =
  trans (runs-layout i f ns (c ∷ []) false (layout i f blank (layout i f (commentRun (a ∷ as)) σ)))
        (cong (λ G → layoutG i f G (layout i f blank (layout i f (commentRun (a ∷ as)) σ))) e)

------------------------------------------------------------------------
-- What runs write, at the start of their lines
------------------------------------------------------------------------

open import Once.Format.Proof.Rerender using (commentLines-ne)

-- | Runs written at the start of lines, a blank line between two.
gOut : List (List String) → List Lexeme → List Lexeme
gOut []            o = o
gOut (R ∷ [])      o = linesOut 0 (rendered 0 R) o
gOut (R ∷ R′ ∷ Rs) o = gOut (R′ ∷ Rs) (lnl ∷ linesOut 0 (rendered 0 R) o)

NE : List String → Set
NE R = ∃[ c ] ∃[ cs ] R ≡ c ∷ cs

private
  linesOut-cons : ∀ i L Ls o → ∃[ Y ] linesOut i (L ∷ Ls) o ≡ lnl ∷ Y
  linesOut-cons i L []        o = _ , refl
  linesOut-cons i L (L′ ∷ Ls) o = linesOut-cons i L′ Ls _

  clines-ne : ∀ R → NE R → ∃[ l ] ∃[ ls ] concatMap commentLines R ≡ l ∷ ls
  clines-ne .(c ∷ cs) (c , cs , refl) with commentLines-ne c
  ... | l , ls , e = l , _ , cong (_++ concatMap commentLines cs) e

  run-out : ∀ f R o c → NE R → layout 0 f (commentRun R) (st o c (just 0) []) ≡ st (linesOut 0 (rendered 0 R) o) 0 (just 0) []
  run-out f R o c ne with clines-ne R ne
  ... | l , ls , e = trans (lines-layout 0 f (concatMap commentLines R) o c)
                           (cong (λ x → st (linesOut 0 (rendered 0 R) o) x (just 0) []) (cong (λ L → colOf L c) e))

-- | Runs of comments, laid out from the start of a line.
layoutG-out : ∀ f G o c → All NE G → layoutG 0 f G (st o c (just 0) []) ≡ st (gOut G o) (colOf G c) (just 0) []
layoutG-out f []            o c []           = refl
layoutG-out f (R ∷ [])      o c (ne ∷ [])    = run-out f R o c ne
layoutG-out f (R ∷ R′ ∷ Rs) o c (ne ∷ nes) with rendered-ne 0 (proj₁ ne) (proj₁ (proj₂ ne))
... | L , Ls , eL =
  trans (cong (λ σ → layoutG 0 f (R′ ∷ Rs) (layout 0 f blank σ)) (run-out f R o c ne))
    (trans (cong (λ σ → layoutG 0 f (R′ ∷ Rs) σ) (blank-after (linesOut 0 (rendered 0 R) o) (lo-cons)))
           (layoutG-out f (R′ ∷ Rs) (lnl ∷ linesOut 0 (rendered 0 R) o) 0 nes))
  where
    lo-cons : ∃[ Y ] linesOut 0 (rendered 0 R) o ≡ lnl ∷ Y
    lo-cons = subst (λ M → ∃[ Y ] linesOut 0 M o ≡ lnl ∷ Y) (sym (subst (λ x → rendered 0 x ≡ L ∷ Ls) (sym (proj₂ (proj₂ ne))) eL))
                (linesOut-cons 0 L Ls o)
    blank-after : ∀ O → (∃[ Y ] O ≡ lnl ∷ Y) → layout 0 f blank (st O 0 (just 0) []) ≡ st (lnl ∷ O) 0 (just 0) []
    blank-after .(lnl ∷ Y) (Y , refl) = refl

------------------------------------------------------------------------
-- The walk over them
------------------------------------------------------------------------

open import Once.Format.Print using (W; walker; Line; line-text; line-empty; line-code; Held; held-comment; held-blank;
  Trivia; stepComment; lineEnd; stepTok; settleAt; promote; promoteR; blankBefore; pending)
open import Once.Format.Proof.Walk using (WL; stepL; nlW)
open import Once.Format.Proof.Lockstep using (Φ; Φ-cons)

hcT : String → Held
hcT c = held-comment c true

-- | What the walk holds before a declaration for the runs: each written line
-- before it, a blank between two runs.
heldOf : List (List String) → List Held
heldOf []            = []
heldOf (R ∷ [])      = map hcT (map readBack (rendered 0 R))
heldOf (R ∷ R′ ∷ Rs) = map hcT (map readBack (rendered 0 R)) ++ held-blank ∷ heldOf (R′ ∷ Rs)

-- The walk after a comment line at the start of a line.
mid : ℕ → String → List Held → Trivia → WL
mid k r H T = walker k false (line-text (r ∷ [])) H 0 T , true

-- | A state the first comment line of the runs is read from, with what it
-- holds then.
Entry : List Lexeme → ℕ → List Held → Trivia → Set
Entry o k H₀ T = ∀ L → Φ (lnl ∷ lcm L ∷ lind 0 ∷ o) ≡ mid k (readBack L) H₀ T

private
  step3 : ∀ o L → Φ (lnl ∷ lcm L ∷ lind 0 ∷ o) ≡ stepL (stepL (stepL (Φ o) (lind 0)) (lcm L)) lnl
  step3 o L = trans (Φ-cons lnl (lcm L ∷ lind 0 ∷ o))
                (cong (λ ω → stepL ω lnl) (trans (Φ-cons (lcm L) (lind 0 ∷ o)) (cong (λ ω → stepL ω (lcm L)) (Φ-cons (lind 0) o))))

  top-next : ∀ o L r H k T → Φ o ≡ mid k r H T → Φ (lnl ∷ lcm L ∷ lind 0 ∷ o) ≡ mid k (readBack L) (H ++ hcT r ∷ []) T
  top-next o L r H k T e = trans (step3 o L) (cong (λ ω → stepL (stepL (stepL ω (lind 0)) (lcm L)) lnl) e)

  top-gap : ∀ o L r H k T → Φ o ≡ mid k r H T
          → Φ (lnl ∷ lcm L ∷ lind 0 ∷ lnl ∷ o) ≡ mid k (readBack L) ((H ++ hcT r ∷ []) ++ held-blank ∷ []) T
  top-gap o L r H k T e =
    trans (step3 (lnl ∷ o) L) (cong (λ ω → stepL (stepL (stepL ω (lind 0)) (lcm L)) lnl) (trans (Φ-cons lnl o) (cong (λ ω → stepL ω lnl) e)))

  lines-walk : ∀ Ls o r H k T → Φ o ≡ mid k r H T
             → ∃[ r′ ] ∃[ H′ ] Φ (linesOut 0 Ls o) ≡ mid k r′ H′ T × H′ ++ hcT r′ ∷ [] ≡ H ++ hcT r ∷ map hcT (map readBack Ls)
  lines-walk []       o r H k T e = r , H , e , refl
  lines-walk (L ∷ Ls) o r H k T e with lines-walk Ls (lnl ∷ lcm L ∷ lind 0 ∷ o) (readBack L) (H ++ hcT r ∷ []) k T (top-next o L r H k T e)
  ... | r′ , H′ , e′ , q = r′ , H′ , e′ , trans q (++-assoc H (hcT r ∷ []) _)

-- | The walk over runs of comment lines holds each, a blank between two runs.
runs-walk : ∀ G o k H₀ T → All NE G → Entry o k H₀ T → ∀ {R Rs} → G ≡ R ∷ Rs
          → ∃[ r ] ∃[ H ] Φ (gOut G o) ≡ mid k r H T × H ++ hcT r ∷ [] ≡ H₀ ++ heldOf G
runs-walk (R ∷ []) o k H₀ T (ne ∷ []) en refl with rendered-ne 0 (proj₁ ne) (proj₁ (proj₂ ne))
... | L , Ls , eL = go (rendered 0 R) (subst (λ x → rendered 0 x ≡ L ∷ Ls) (sym (proj₂ (proj₂ ne))) eL)
  where
    go : ∀ M → M ≡ L ∷ Ls → ∃[ r ] ∃[ H ] Φ (linesOut 0 M o) ≡ mid k r H T × H ++ hcT r ∷ [] ≡ H₀ ++ map hcT (map readBack M)
    go .(L ∷ Ls) refl with lines-walk Ls (lnl ∷ lcm L ∷ lind 0 ∷ o) (readBack L) H₀ k T (en L)
    ... | r′ , H′ , e′ , q = r′ , H′ , e′ , q
runs-walk (R ∷ R′ ∷ Rs) o k H₀ T (ne ∷ nes) en refl
  with runs-walk (R ∷ []) o k H₀ T (ne ∷ []) en refl
... | r , H , e , q
  with runs-walk (R′ ∷ Rs) (lnl ∷ linesOut 0 (rendered 0 R) o) k ((H ++ hcT r ∷ []) ++ held-blank ∷ []) T nes
         (λ L → top-gap (linesOut 0 (rendered 0 R) o) L r H k T e) refl
...   | r′ , H′ , e′ , q′ =
  r′ , H′ , e′ ,
  trans q′ (trans (cong (λ X → (X ++ held-blank ∷ []) ++ heldOf (R′ ∷ Rs)) q)
    (trans (++-assoc (H₀ ++ heldOf (R ∷ [])) (held-blank ∷ []) (heldOf (R′ ∷ Rs)))
           (++-assoc H₀ (heldOf (R ∷ [])) (held-blank ∷ heldOf (R′ ∷ Rs)))))

------------------------------------------------------------------------
-- What the walk settles before a declaration
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Once.Format.Print using (Notes; notes; lookupNotes; addTo; addTop)
open import Once.Format.Proof.Walk using (lookup-addTo-same)

-- What stands before a declaration: comments, and blank lines.
TopH : Held → Set
TopH (held-comment _ true)  = ⊤
TopH (held-comment _ false) = ⊥
TopH held-blank             = ⊤

-- | The notes held things settle as.
notesOf : List Held → List Note
notesOf []                      = []
notesOf (held-comment c _ ∷ hs) = note-comment c ∷ notesOf hs
notesOf (held-blank ∷ hs)       = note-blank ∷ notesOf hs

private
  map-top : ∀ rs → All TopH (map hcT rs)
  map-top []       = []
  map-top (r ∷ rs) = tt ∷ map-top rs

  all-++ : ∀ {A : Set} {P : A → Set} xs ys → All P xs → All P ys → All P (xs ++ ys)
  all-++ []       ys []       q = q
  all-++ (x ∷ xs) ys (p ∷ ps) q = p ∷ all-++ xs ys ps q

heldOf-top : ∀ G → All TopH (heldOf G)
heldOf-top []            = []
heldOf-top (R ∷ [])      = map-top _
heldOf-top (R ∷ R′ ∷ Rs) = all-++ _ _ (map-top _) (tt ∷ heldOf-top (R′ ∷ Rs))

private
  promoteR-top : ∀ hs b → All TopH hs → promoteR hs b ≡ hs
  promoteR-top []                         b     []       = refl
  promoteR-top (held-comment h true ∷ hs) false (_ ∷ ps) = cong (held-comment h true ∷_) (promoteR-top hs true ps)
  promoteR-top (held-comment h true ∷ hs) true  (_ ∷ ps) = cong (held-comment h true ∷_) (promoteR-top hs true ps)
  promoteR-top (held-blank ∷ hs)          b     (_ ∷ ps) = cong (held-blank ∷_) (promoteR-top hs true ps)

  all-revH : ∀ {P : Held → Set} {xs} → All P xs → All P (reverse xs)
  all-revH {P} {[]} [] = []
  all-revH {P} {x ∷ xs} (p ∷ ps) =
    subst (All P) (sym (Data.List.Properties.unfold-reverse x xs)) (all-++ (reverse xs) (x ∷ []) (all-revH ps) (p ∷ []))

-- | What stands before a declaration is not promoted further.
promote-top : ∀ hs → All TopH hs → promote hs ≡ hs
promote-top hs ps = trans (cong reverse (promoteR-top (reverse hs) false (all-revH ps))) (Data.List.Properties.reverse-involutive hs)

-- | Settling it adds it before the declaration's first anchor.
settle-tops : ∀ k hs T → All TopH hs → Notes.top (lookupNotes k (settleAt k hs T)) ≡ Notes.top (lookupNotes k T) ++ notesOf hs
settle-tops k []                         T []       = sym (++-identityʳ _)
settle-tops k (held-comment h true ∷ hs) T (_ ∷ ps) =
  trans (settle-tops k hs (addTo k (addTop (note-comment h)) T) ps)
    (trans (cong (λ n → Notes.top n ++ notesOf hs) (lookup-addTo-same k (addTop (note-comment h)) T))
      (trans (cong (_++ notesOf hs) (top-add (note-comment h) (lookupNotes k T))) (++-assoc _ (note-comment h ∷ []) _)))
  where
    top-add : ∀ x n → Notes.top (addTop x n) ≡ Notes.top n ++ x ∷ []
    top-add x (notes _ _ _) = refl
settle-tops k (held-blank ∷ hs) T (_ ∷ ps) =
  trans (settle-tops k hs (addTo k (addTop note-blank) T) ps)
    (trans (cong (λ n → Notes.top n ++ notesOf hs) (lookup-addTo-same k (addTop note-blank) T))
      (trans (cong (_++ notesOf hs) (top-add note-blank (lookupNotes k T))) (++-assoc _ (note-blank ∷ []) _)))
  where
    top-add : ∀ x n → Notes.top (addTop x n) ≡ Notes.top n ++ x ∷ []
    top-add x (notes _ _ _) = refl

settle-tops-inner : ∀ j k hs T → All TopH hs → Notes.inner (lookupNotes j (settleAt k hs T)) ≡ Notes.inner (lookupNotes j T)
settle-tops-inner j k []                         T []       = refl
settle-tops-inner j k (held-comment h true ∷ hs) T (_ ∷ ps) =
  trans (settle-tops-inner j k hs _ ps)
    (Once.Format.Proof.Walk.lookup-addTo-keeps Notes.inner j k (addTop (note-comment h)) T (λ { (notes _ _ _) → refl }))
settle-tops-inner j k (held-blank ∷ hs)          T (_ ∷ ps) =
  trans (settle-tops-inner j k hs _ ps)
    (Once.Format.Proof.Walk.lookup-addTo-keeps Notes.inner j k (addTop note-blank) T (λ { (notes _ _ _) → refl }))

------------------------------------------------------------------------
-- The second pass's runs
------------------------------------------------------------------------

open import Once.Format.Print using (hasComment; topDoc; lead; ending; gapEnd)
open import Once.Format.Proof.Sources using (NoteSrc)

-- | A run as the second pass reads it: the lines the first pass wrote.
rsOf : List String → List String
rsOf R = map readBack (rendered 0 R)

private
  notesOf-++ : ∀ xs ys → notesOf (xs ++ ys) ≡ notesOf xs ++ notesOf ys
  notesOf-++ []                      ys = refl
  notesOf-++ (held-comment c _ ∷ xs) ys = cong (note-comment c ∷_) (notesOf-++ xs ys)
  notesOf-++ (held-blank ∷ xs)       ys = cong (note-blank ∷_) (notesOf-++ xs ys)

  notesOf-map : ∀ rs → notesOf (map hcT rs) ≡ map note-comment rs
  notesOf-map []       = refl
  notesOf-map (r ∷ rs) = cong (note-comment r ∷_) (notesOf-map rs)

  flag-irr : ∀ ns sd sd′ → groups ns [] sd ≡ groups ns [] sd′
  flag-irr []                    sd sd′ = refl
  flag-irr (note-blank ∷ ns)     sd sd′ = refl
  flag-irr (note-comment c ∷ ns) sd sd′ = refl

  g-nc : ∀ rs acc rest → groups (map note-comment rs ++ rest) acc false ≡ groups rest (acc ++ rs) false
  g-nc []       acc      rest = cong (λ a → groups rest a false) (sym (++-identityʳ acc))
  g-nc (r ∷ rs) []       rest = g-nc rs (r ∷ []) rest
  g-nc (r ∷ rs) (a ∷ as) rest =
    trans (g-nc rs (a ∷ as ++ r ∷ []) rest) (cong (λ x → groups rest x false) (++-assoc (a ∷ as) (r ∷ []) rs))

  g-blanks : ∀ bs acc sd sd′ → All (_≡ held-blank) bs → groups (notesOf bs) acc sd ≡ groups [] acc sd′
  g-blanks []                 []       sd sd′ []          = refl
  g-blanks []                 (a ∷ as) sd sd′ []          = refl
  g-blanks (.held-blank ∷ bs) acc      sd sd′ (refl ∷ ps) = g-blanks bs acc true sd′ ps

  skip-blanks : ∀ B Y sd → All (_≡ note-blank) B → groups (B ++ Y) [] sd ≡ groups Y [] sd
  skip-blanks []                Y sd []          = refl
  skip-blanks (.note-blank ∷ B) Y sd (refl ∷ ps) = trans (skip-blanks B Y true ps) (flag-irr Y true sd)

  cons-rs : ∀ R → NE R → ∃[ c ] ∃[ cs ] rsOf R ≡ c ∷ cs
  cons-rs R (c , cs , e) with rendered-ne 0 c cs
  ... | L , Ls , eL = readBack L , map readBack Ls , cong (map readBack) (trans (cong (rendered 0) e) eL)

  emit-before : ∀ a c X → (∃[ x ] ∃[ xs ] a ≡ x ∷ xs) → groups (note-comment c ∷ X) a true ≡ a ∷ groups (note-comment c ∷ X) [] false
  emit-before .(x ∷ xs) c X (x , xs , refl) = refl

  heldOf-head : ∀ R′ Rs c′ cs′ → rsOf R′ ≡ c′ ∷ cs′ → ∃[ Y ] heldOf (R′ ∷ Rs) ≡ hcT c′ ∷ Y
  heldOf-head R′ []         c′ cs′ e = map hcT cs′ , cong (map hcT) e
  heldOf-head R′ (R″ ∷ Rs′) c′ cs′ e = _ , cong (λ rs → map hcT rs ++ held-blank ∷ heldOf (R″ ∷ Rs′)) e

  hg : ∀ R Rs → All NE (R ∷ Rs) → ∀ tb → All (_≡ held-blank) tb
     → groups (notesOf (heldOf (R ∷ Rs) ++ tb)) [] false ≡ rsOf R ∷ map rsOf Rs
  hg R [] (ne ∷ []) tb pb with cons-rs R ne
  ... | c , cs , e =
    trans (cong (λ x → groups x [] false) (trans (notesOf-++ (map hcT (rsOf R)) tb) (cong (_++ notesOf tb) (notesOf-map (rsOf R)))))
      (trans (g-nc (rsOf R) [] (notesOf tb))
        (trans (g-blanks tb (rsOf R) false false pb) (cong (λ x → groups [] x false) e |> λ q → trans q (cong (_∷ []) (sym e)))))
    where
      infixl 0 _|>_
      _|>_ : ∀ {A B : Set} → A → (A → B) → B
      x |> f = f x
  hg R (R′ ∷ Rs) (ne ∷ nes) tb pb with cons-rs R′ (Data.List.Relation.Unary.All.head nes)
  ... | c′ , cs′ , e′ with heldOf-head R′ Rs c′ cs′ e′
  ...   | Y , eY =
    trans (cong (λ x → groups x [] false)
             (trans (cong notesOf (++-assoc (map hcT (rsOf R)) (held-blank ∷ heldOf (R′ ∷ Rs)) tb))
               (trans (notesOf-++ (map hcT (rsOf R)) (held-blank ∷ (heldOf (R′ ∷ Rs) ++ tb)))
                      (cong (_++ note-blank ∷ notesOf (heldOf (R′ ∷ Rs) ++ tb)) (notesOf-map (rsOf R))))))
      (trans (g-nc (rsOf R) [] (note-blank ∷ notesOf (heldOf (R′ ∷ Rs) ++ tb)))
        (trans (cong (λ H → groups (notesOf (H ++ tb)) (rsOf R) true) eY)
          (trans (emit-before (rsOf R) c′ (notesOf (Y ++ tb)) (cons-rs R ne))
            (cong (rsOf R ∷_) (trans (cong (λ H → groups (notesOf (H ++ tb)) [] false) (sym eY)) (hg R′ Rs nes tb pb))))))

-- | The second pass's notes before a declaration: blank lines, then the runs
-- the walk held; their runs are the first pass's, as written.
groups-pass2 : ∀ G B tb → All NE G → All (_≡ note-blank) B → All (_≡ held-blank) tb
             → groups (B ++ notesOf (heldOf G ++ tb)) [] false ≡ map rsOf G
groups-pass2 []       B tb []         pB pb = trans (skip-blanks B _ false pB) (g-blanks tb [] false false pb)
groups-pass2 (R ∷ Rs) B tb nes        pB pb = trans (skip-blanks B _ false pB) (hg R Rs nes tb pb)

-- | Runs are not empty.
groups-ne-all : ∀ ns acc sd → All NE (groups ns acc sd)
groups-ne-all []                    []       sd    = []
groups-ne-all []                    (a ∷ as) sd    = (a , as , refl) ∷ []
groups-ne-all (note-blank ∷ ns)     acc      sd    = groups-ne-all ns acc true
groups-ne-all (note-comment c ∷ ns) []       sd    = groups-ne-all ns (c ∷ []) false
groups-ne-all (note-comment c ∷ ns) (a ∷ as) false = groups-ne-all ns (a ∷ as ++ c ∷ []) false
groups-ne-all (note-comment c ∷ ns) (a ∷ as) true  = (a , as , refl) ∷ groups-ne-all ns (c ∷ []) false

-- | Their comments are the notes'.
groups-src : ∀ ns acc sd → All NoteSrc ns → All Src acc → All (All Src) (groups ns acc sd)
groups-src []                    []       sd    []       pa = []
groups-src []                    (a ∷ as) sd    []       pa = pa ∷ []
groups-src (note-blank ∷ ns)     acc      sd    (_ ∷ ps) pa = groups-src ns acc true ps pa
groups-src (note-comment c ∷ ns) []       sd    (p ∷ ps) pa = groups-src ns (c ∷ []) false ps (p ∷ [])
groups-src (note-comment c ∷ ns) (a ∷ as) false (p ∷ ps) pa = groups-src ns (a ∷ as ++ c ∷ []) false ps (all-++ (a ∷ as) _ pa (p ∷ []))
groups-src (note-comment c ∷ ns) (a ∷ as) true  (p ∷ ps) pa = pa ∷ groups-src ns (c ∷ []) false ps (p ∷ [])

------------------------------------------------------------------------
-- The second pass prints them as the first
------------------------------------------------------------------------

notNull : ∀ {A : Set} → List A → Bool
notNull []      = false
notNull (_ ∷ _) = true

private

  ∨-true : ∀ b → b Data.Bool.∨ true ≡ true
  ∨-true true  = refl
  ∨-true false = refl

  ∨-false : ∀ b → b Data.Bool.∨ false ≡ b
  ∨-false true  = refl
  ∨-false false = refl

  has-groups : ∀ ns acc sd → notNull (groups ns acc sd) ≡ hasComment ns Data.Bool.∨ notNull acc
  has-groups []                    []       sd    = refl
  has-groups []                    (a ∷ as) sd    = refl
  has-groups (note-blank ∷ ns)     acc      sd    = has-groups ns acc true
  has-groups (note-comment c ∷ ns) []       sd    = trans (has-groups ns (c ∷ []) false) (∨-true (hasComment ns))
  has-groups (note-comment c ∷ ns) (a ∷ as) false = trans (has-groups ns (a ∷ as ++ c ∷ []) false) (∨-true (hasComment ns))
  has-groups (note-comment c ∷ ns) (a ∷ as) true  = refl


  notNull-map : ∀ {A B : Set} (f : A → B) xs → notNull (map f xs) ≡ notNull xs
  notNull-map f []      = refl
  notNull-map f (_ ∷ _) = refl

  colOf-map : ∀ {A B : Set} (f : A → B) xs c → colOf (map f xs) c ≡ colOf xs c
  colOf-map f []      c = refl
  colOf-map f (_ ∷ _) c = refl

  ne-map : ∀ G → All NE G → All NE (map rsOf G)
  ne-map []       []         = []
  ne-map (R ∷ Rs) (ne ∷ nes) = cons-rs R ne ∷ ne-map Rs nes

  rs-fix : ∀ R → All Src R → rendered 0 (rsOf R) ≡ rendered 0 R
  rs-fix R src = rendered-fix 0 (rendered 0 R) (rendered-RL 0 R src)

  gOut-rs : ∀ G o → All (All Src) G → gOut (map rsOf G) o ≡ gOut G o
  gOut-rs []            o []         = refl
  gOut-rs (R ∷ [])      o (p ∷ [])   = cong (λ M → linesOut 0 M o) (rs-fix R p)
  gOut-rs (R ∷ R′ ∷ Rs) o (p ∷ ps)   =
    trans (cong (λ M → gOut (map rsOf (R′ ∷ Rs)) (lnl ∷ linesOut 0 M o)) (rs-fix R p)) (gOut-rs (R′ ∷ Rs) _ ps)

-- | Notes have comments when they have runs.
has-of : ∀ ns → hasComment ns ≡ notNull (groups ns [] false)
has-of ns = sym (trans (has-groups ns [] false) (∨-false (hasComment ns)))

-- | Runs write a line end last.
gOut-lnl : ∀ R Rs o → All NE (R ∷ Rs) → ∃[ Y ] gOut (R ∷ Rs) o ≡ lnl ∷ Y
gOut-lnl R []        o (ne ∷ []) with rendered-ne 0 (proj₁ ne) (proj₁ (proj₂ ne))
... | L , Ls , eL = subst (λ M → ∃[ Y ] linesOut 0 M o ≡ lnl ∷ Y)
                      (sym (subst (λ x → rendered 0 x ≡ L ∷ Ls) (sym (proj₂ (proj₂ ne))) eL)) (lo L Ls o)
  where
    lo : ∀ L Ls o → ∃[ Y ] linesOut 0 (L ∷ Ls) o ≡ lnl ∷ Y
    lo L []        o = _ , refl
    lo L (L′ ∷ Ls) o = lo L′ Ls _
gOut-lnl R (R′ ∷ Rs) o (ne ∷ nes) = gOut-lnl R′ Rs _ nes

-- | The second pass's notes, whose runs are the first pass's as written,
-- print as the first pass's.
runs-eq : ∀ f ns₁ ns₂ o c → groups ns₂ [] false ≡ map rsOf (groups ns₁ [] false) → All NoteSrc ns₁
        → layout 0 f (runs ns₂ [] false) (st o c (just 0) []) ≡ layout 0 f (runs ns₁ [] false) (st o c (just 0) [])
runs-eq f ns₁ ns₂ o c eq src =
  trans (runs-layout 0 f ns₂ [] false _)
    (trans (cong (λ G → layoutG 0 f G (st o c (just 0) [])) eq)
      (trans (layoutG-out f (map rsOf G) o c (ne-map G (groups-ne-all ns₁ [] false)))
        (trans (cong₂ (λ O x → st O x (just 0) []) (gOut-rs G o (groups-src ns₁ [] false src [])) (colOf-map rsOf G c))
          (sym (trans (runs-layout 0 f ns₁ [] false _) (layoutG-out f G o c (groups-ne-all ns₁ [] false)))))))
  where G = groups ns₁ [] false

has-eq : ∀ ns₁ ns₂ → groups ns₂ [] false ≡ map rsOf (groups ns₁ [] false) → hasComment ns₂ ≡ hasComment ns₁
has-eq ns₁ ns₂ eq = trans (has-of ns₂) (trans (cong notNull eq) (trans (notNull-map rsOf _) (sym (has-of ns₁))))

-- | What stands before a declaration, printed again.
lead-eq : ∀ prev ns₁ ns₂ o c → groups ns₂ [] false ≡ map rsOf (groups ns₁ [] false) → All NoteSrc ns₁
        → layout 0 false (lead prev ns₂) (st o c (just 0) []) ≡ layout 0 false (lead prev ns₁) (st o c (just 0) [])
lead-eq (just _) ns₁ ns₂ o c eq src = runs-eq false ns₁ ns₂ o c eq src
lead-eq nothing  ns₁ ns₂ o c eq src rewrite has-eq ns₁ ns₂ eq = pick (hasComment ns₁)
  where
    pick : ∀ b → layout 0 false (if b then topDoc ns₂ <> blank else empty) (st o c (just 0) [])
               ≡ layout 0 false (if b then topDoc ns₁ <> blank else empty) (st o c (just 0) [])
    pick true  = cong (layout 0 false blank) (runs-eq false ns₁ ns₂ o c eq src)
    pick false = refl

private
  gap-fresh : ∀ prev o c → ∃[ o′ ] ∃[ c′ ] layout 0 false (gapEnd prev) (st o c (just 0) []) ≡ st o′ c′ (just 0) []
  gap-fresh nothing  o        c = o , c , refl
  gap-fresh (just _) []       c = [] , 0 , refl
  gap-fresh (just _) (x ∷ o)  c = _ , 0 , refl

-- | What stands after the last declaration, printed again.
ending-eq : ∀ prev ns₁ ns₂ o c → groups ns₂ [] false ≡ map rsOf (groups ns₁ [] false) → All NoteSrc ns₁
          → layout 0 false (ending prev ns₂) (st o c (just 0) []) ≡ layout 0 false (ending prev ns₁) (st o c (just 0) [])
ending-eq prev ns₁ ns₂ o c eq src rewrite has-eq ns₁ ns₂ eq = pick (hasComment ns₁)
  where
    pick : ∀ b → layout 0 false (if b then gapEnd prev <> topDoc ns₂ else empty) (st o c (just 0) [])
               ≡ layout 0 false (if b then gapEnd prev <> topDoc ns₁ else empty) (st o c (just 0) [])
    pick true with gap-fresh prev o c
    ... | o′ , c′ , e = trans (cong (layout 0 false (topDoc ns₂)) e)
                          (trans (runs-eq false ns₁ ns₂ o′ c′ eq src) (sym (cong (layout 0 false (topDoc ns₁)) e)))
    pick false = refl
