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
