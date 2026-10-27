-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Walk — the comment walker on the layout's lexemes
-- (plan 0.124 step 4.5).
--
-- The walker (`Print.trivia`) reads a text's items. On a formatted text those
-- are the items of the layout's lexemes (`ItemsLex.itemsL`), so the trivia of
-- a formatted text is the walker run over the lexemes themselves (`walkL`,
-- `formatted-trivia`), a line end waiting for what follows it as `itemsL`
-- does.
--
-- An anchor's notes stop changing once the walk is past them (`frozen-ti`,
-- `frozen-after`): what stands before an anchor is settled when the walk
-- reaches it, what ends its line when that line has ended or a later anchor
-- has come. So the second pass's trivia can be read off the walk as it goes.
------------------------------------------------------------------------

module Once.Format.Proof.Walk where

open import Data.Bool using (Bool; true; false; not; _∨_; if_then_else_; T)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; map; foldl; reverse)
open import Data.List.Properties using (foldl-++)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <-irrefl; ≤-refl; n<1+n; <-trans; m≤n⇒m≤1+n; ≤-trans; <⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; fromList; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.List.Properties using (reverse-++)

open import Once.Postulates using (toList∘fromList)
import Once.Parser.Token as P
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TString; TLParen; TRParen; TLBrace; TRBrace;
  TColon; TEquals; TArrow; TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon; TAt; TPipe; TDot; TPlus; TMinus;
  TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang; TNewline; TEOF)
open import Once.Adequacy.SpecLexing using (forget)
open import Once.Format.Doc using (Doc; Lexeme; lt; lsp; lnl; lind; lcm; chars; lexemes; render)
open import Once.Format.Lex using (Item; tok; comment; cont; lexItems)
open import Once.Format.Print using (W; walker; Line; line-empty; line-code; line-text; Notes; noNotes; Trivia;
  lookupNotes; addTo; settleAt; settle; lineEnd; stepTok; stepComment; afterCode; step; walkItems; finish; trivia;
  isAnchor; isLineEnd; trimEnd; promote; pending; blankBefore; addAfter)
open import Once.Format.Proof.Items using (EItem; etok; ecomment; econt; erase; items-complete)
open import Once.Format.Proof.ItemsLex using (itemsL; items-ws)
open import Once.Format.Proof.Lexing using (WS)
open import Once.Format.Proof.Skeleton using (anchorTok; lineEndTok)

------------------------------------------------------------------------
-- The walker on erased items
------------------------------------------------------------------------

stepE : W → EItem → W
stepE σ (etok x)     = stepTok σ (anchorTok x) (lineEndTok x)
stepE σ econt        = lineEnd false σ
stepE σ (ecomment c) = stepComment σ (trimEnd c)

walkE : W → List EItem → W
walkE = foldl stepE

private
  anchor-forget : ∀ t → isAnchor t ≡ anchorTok (forget t)
  anchor-forget (P.TWord s) = refl
  anchor-forget (P.TInt i _) = refl
  anchor-forget (P.TFloat a f n _) = refl
  anchor-forget (P.TString s) = refl
  anchor-forget P.TLParen = refl
  anchor-forget P.TRParen = refl
  anchor-forget P.TLBrace = refl
  anchor-forget P.TRBrace = refl
  anchor-forget P.TColon = refl
  anchor-forget P.TEquals = refl
  anchor-forget P.TArrow = refl
  anchor-forget P.TCaret1 = refl
  anchor-forget P.TCaret0 = refl
  anchor-forget P.TCaretW = refl
  anchor-forget P.TLambda = refl
  anchor-forget P.TComma = refl
  anchor-forget P.TSemicolon = refl
  anchor-forget P.TAt = refl
  anchor-forget P.TPipe = refl
  anchor-forget P.TDot = refl
  anchor-forget P.TPlus = refl
  anchor-forget P.TMinus = refl
  anchor-forget P.TStar = refl
  anchor-forget P.TSlash = refl
  anchor-forget P.TPercent = refl
  anchor-forget P.TAmpersand = refl
  anchor-forget P.TLt = refl
  anchor-forget P.TLe = refl
  anchor-forget P.TGt = refl
  anchor-forget P.TGe = refl
  anchor-forget P.TEqEq = refl
  anchor-forget P.TNeq = refl
  anchor-forget P.TBang = refl
  anchor-forget P.TNewline = refl
  anchor-forget P.TEOF = refl

  end-forget : ∀ t → isLineEnd t ≡ lineEndTok (forget t)
  end-forget (P.TWord s) = refl
  end-forget (P.TInt i _) = refl
  end-forget (P.TFloat a f n _) = refl
  end-forget (P.TString s) = refl
  end-forget P.TLParen = refl
  end-forget P.TRParen = refl
  end-forget P.TLBrace = refl
  end-forget P.TRBrace = refl
  end-forget P.TColon = refl
  end-forget P.TEquals = refl
  end-forget P.TArrow = refl
  end-forget P.TCaret1 = refl
  end-forget P.TCaret0 = refl
  end-forget P.TCaretW = refl
  end-forget P.TLambda = refl
  end-forget P.TComma = refl
  end-forget P.TSemicolon = refl
  end-forget P.TAt = refl
  end-forget P.TPipe = refl
  end-forget P.TDot = refl
  end-forget P.TPlus = refl
  end-forget P.TMinus = refl
  end-forget P.TStar = refl
  end-forget P.TSlash = refl
  end-forget P.TPercent = refl
  end-forget P.TAmpersand = refl
  end-forget P.TLt = refl
  end-forget P.TLe = refl
  end-forget P.TGt = refl
  end-forget P.TGe = refl
  end-forget P.TEqEq = refl
  end-forget P.TNeq = refl
  end-forget P.TBang = refl
  end-forget P.TNewline = refl
  end-forget P.TEOF = refl

  step-erase : ∀ σ i → step σ i ≡ stepE σ (erase i)
  step-erase σ (tok t)     = cong₂ (stepTok σ) (anchor-forget t) (end-forget t)
  step-erase σ (comment c) = refl
  step-erase σ cont        = refl

walk-erase : ∀ σ is → walkItems σ is ≡ walkE σ (map erase is)
walk-erase σ []       = refl
walk-erase σ (i ∷ is) rewrite step-erase σ i = walk-erase (stepE σ (erase i)) is

-- | The first walker state.
w₀ : W
w₀ = walker 0 false line-empty [] 0 []

------------------------------------------------------------------------
-- The walker on lexemes
------------------------------------------------------------------------

-- A walker state and whether a line end waits for what follows it.
WL : Set
WL = W × Bool

-- The waiting line end, read: before an unindented line it ends a line
-- (`TNewline`), before an indented one it is swallowed.
nlW : Bool → W → W
nlW true  w = stepTok w false true
nlW false w = w

contW : Bool → W → W
contW true  w = lineEnd false w
contW false w = w

stepL : WL → Lexeme → WL
stepL (w , p) (lt x)         = stepTok (nlW p w) (anchorTok x) (lineEndTok x) , false
stepL (w , p) lsp            = contW p w , false
stepL (w , p) lnl            = nlW p w , true
stepL (w , p) (lind zero)    = w , p
stepL (w , p) (lind (suc _)) = contW p w , false
stepL (w , p) (lcm c)        = stepComment (nlW p w) (trimEnd (fromList c)) , false

walkL : WL → List Lexeme → WL
walkL = foldl stepL

-- The end of the text: a waiting line end, then `TEOF`.
closeL : WL → W
closeL (w , p) = stepTok (nlW p w) false true

-- | The walker over a lexeme's items is the walker over the lexeme.
items-walk : ∀ w p xs → walkE w (itemsL p xs) ≡ closeL (walkL (w , p) xs)
items-walk w true  []                  = refl
items-walk w false []                  = refl
items-walk w true  (lt x ∷ xs)         = items-walk _ false xs
items-walk w false (lt x ∷ xs)         = items-walk _ false xs
items-walk w true  (lsp ∷ xs)          = items-walk _ false xs
items-walk w false (lsp ∷ xs)          = items-walk _ false xs
items-walk w true  (lnl ∷ xs)          = items-walk _ true xs
items-walk w false (lnl ∷ xs)          = items-walk _ true xs
items-walk w true  (lind zero ∷ xs)    = items-walk w true xs
items-walk w false (lind zero ∷ xs)    = items-walk w false xs
items-walk w true  (lind (suc _) ∷ xs) = items-walk _ false xs
items-walk w false (lind (suc _) ∷ xs) = items-walk _ false xs
items-walk w true  (lcm c ∷ xs)        = items-walk _ false xs
items-walk w false (lcm c ∷ xs)        = items-walk _ false xs

-- | The trivia of a formatted text: the walker over its lexemes.
formatted-trivia : ∀ d → WS (lexemes d) → trivia (lexItems (toList (render d))) ≡ finish (closeL (walkL (w₀ , false) (lexemes d)))
formatted-trivia d ws
  rewrite toList∘fromList (Data.List.concatMap chars (lexemes d))
        | walk-erase w₀ (lexItems (Data.List.concatMap chars (lexemes d)))
        | items-complete {off = 0} (<-wellFounded (length (Data.List.concatMap chars (lexemes d)))) (items-ws (lexemes d) ws)
  = cong finish (items-walk w₀ false (lexemes d))

------------------------------------------------------------------------
-- Where the walker writes
------------------------------------------------------------------------

open import Once.Format.Print using (Note; Held; held-comment; held-blank; notes; addTop; addInner)

-- What stands before an anchor: its top and inner notes.
ti : Notes → List Note × List String
ti n = Notes.top n , Notes.inner n

-- | What adding to one anchor's notes does to a view of any anchor's notes
-- that the addition keeps.
lookup-addTo-keeps : ∀ {A : Set} (V : Notes → A) j i f t → (∀ n → V (f n) ≡ V n)
                   → V (lookupNotes j (addTo i f t)) ≡ V (lookupNotes j t)
lookup-addTo-keeps V j i f [] e with j ≡ᵇ i
... | true  = e noNotes
... | false = refl
lookup-addTo-keeps V j i f ((i′ , n) ∷ ts) e with i ≡ᵇ i′
... | true with j ≡ᵇ i′
...   | true  = e n
...   | false = refl
lookup-addTo-keeps V j i f ((i′ , n) ∷ ts) e | false with j ≡ᵇ i′
...   | true  = refl
...   | false = lookup-addTo-keeps V j i f ts e

≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

-- | Adding to an anchor's notes adds to them.
lookup-addTo-same : ∀ k f t → lookupNotes k (addTo k f t) ≡ f (lookupNotes k t)
lookup-addTo-same k f [] rewrite ≡ᵇ-refl k = refl
lookup-addTo-same k f ((i , n) ∷ ts) with k ≡ᵇ i in e
... | true  rewrite e = refl
... | false rewrite e = lookup-addTo-same k f ts

private
  ≢-≡ᵇ : ∀ {m n} → m ≢ n → (m ≡ᵇ n) ≡ false
  ≢-≡ᵇ {m} {n} ne with m ≡ᵇ n in eq
  ... | true  = ⊥-elim (ne (≡ᵇ⇒≡ m n (subst T (sym eq) _)))
  ... | false = refl

-- | Adding to another anchor's notes leaves these.
lookup-addTo : ∀ j k f t → j ≢ k → lookupNotes j (addTo k f t) ≡ lookupNotes j t
lookup-addTo j k f []              ne rewrite ≢-≡ᵇ ne = refl
lookup-addTo j k f ((i , n) ∷ ts)  ne with k ≡ᵇ i in e
... | true  rewrite ≡ᵇ⇒≡ k i (subst T (sym e) _) | ≢-≡ᵇ ne = refl
... | false with j ≡ᵇ i
...   | true  = refl
...   | false = lookup-addTo j k f ts ne

lookup-settleAt : ∀ j k hs t → j ≢ k → lookupNotes j (settleAt k hs t) ≡ lookupNotes j t
lookup-settleAt j k []                         t ne = refl
lookup-settleAt j k (held-comment h true ∷ hs)  t ne = trans (lookup-settleAt j k hs _ ne) (lookup-addTo j k _ t ne)
lookup-settleAt j k (held-comment h false ∷ hs) t ne = trans (lookup-settleAt j k hs _ ne) (lookup-addTo j k _ t ne)
lookup-settleAt j k (held-blank ∷ hs)           t ne = trans (lookup-settleAt j k hs _ ne) (lookup-addTo j k _ t ne)

open import Once.Format.Print using (hoist; hoistAt; note-comment; notes)
open import Relation.Nullary using (yes; no)
open import Data.Unit using (tt)

-- | An anchor's notes as a declaration's first: what stood before it, in place,
-- stands before the declaration.
up : Notes → Notes
up n = notes (Notes.top n ++ map note-comment (Notes.inner n)) [] (Notes.after n)

hoist-at : ∀ k tv → lookupNotes k (hoist k tv) ≡ up (lookupNotes k tv)
hoist-at k []             = refl
hoist-at k ((j , n) ∷ ts) with k ≡ᵇ j in e
... | true  rewrite e = refl
... | false rewrite e = hoist-at k ts

hoist-other : ∀ j k tv → j ≢ k → lookupNotes j (hoist k tv) ≡ lookupNotes j tv
hoist-other j k []             ne = refl
hoist-other j k ((i , n) ∷ ts) ne with k ≡ᵇ i in e
... | true with j ≡ᵇ i in e′
...   | true  = ⊥-elim (ne (trans (≡ᵇ⇒≡ j i (subst T (sym e′) tt)) (sym (≡ᵇ⇒≡ k i (subst T (sym e) tt)))))
...   | false = refl
hoist-other j k ((i , n) ∷ ts) ne | false with j ≡ᵇ i
...   | true  = refl
...   | false = hoist-other j k ts ne

hoist-after : ∀ j k tv → Notes.after (lookupNotes j (hoist k tv)) ≡ Notes.after (lookupNotes j tv)
hoist-after j k tv with j Data.Nat.≟ k
... | yes refl = cong Notes.after (hoist-at j tv)
... | no ne    = cong Notes.after (hoist-other j k tv ne)


-- | A line that starts a declaration hoists what stood before the next
-- anchor, in place, when something did.
hoistAt-cases : ∀ k t (P : Trivia → Set) → P t → P (hoist k t) → P (hoistAt k t)
hoistAt-cases k t P pt ph with Data.List.null (Notes.inner (lookupNotes k t))
... | true  = pt
... | false = ph

hoistAt-id : ∀ k t → Notes.inner (lookupNotes k t) ≡ [] → hoistAt k t ≡ t
hoistAt-id k t e = cong (λ b → if b then t else hoist k t) (cong Data.List.null e)

hoistAt-other : ∀ j k t → j ≢ k → lookupNotes j (hoistAt k t) ≡ lookupNotes j t
hoistAt-other j k t ne = hoistAt-cases k t (λ t′ → lookupNotes j t′ ≡ lookupNotes j t) refl (hoist-other j k t ne)

hoistAt-after : ∀ j k t → Notes.after (lookupNotes j (hoistAt k t)) ≡ Notes.after (lookupNotes j t)
hoistAt-after j k t = hoistAt-cases k t (λ t′ → Notes.after (lookupNotes j t′) ≡ Notes.after (lookupNotes j t)) refl (hoist-after j k t)

-- | Settling adds nothing at the end of a line.
settleAt-after : ∀ j k hs t → Notes.after (lookupNotes j (settleAt k hs t)) ≡ Notes.after (lookupNotes j t)
settleAt-after j k []                         t = refl
settleAt-after j k (held-comment h true ∷ hs)  t =
  trans (settleAt-after j k hs _) (lookup-addTo-keeps Notes.after j k _ t (λ { (notes _ _ _) → refl }))
settleAt-after j k (held-comment h false ∷ hs) t =
  trans (settleAt-after j k hs _) (lookup-addTo-keeps Notes.after j k _ t (λ { (notes _ _ _) → refl }))
settleAt-after j k (held-blank ∷ hs)           t =
  trans (settleAt-after j k hs _) (lookup-addTo-keeps Notes.after j k _ t (λ { (notes _ _ _) → refl }))

------------------------------------------------------------------------
-- Frozen notes
------------------------------------------------------------------------

-- The notes of anchor `j` in a state.
Look : ℕ → W → Notes
Look j σ = lookupNotes j (W.acc σ)

-- | What ends anchor `j`'s line is settled once a later anchor has come, or
-- its line has ended (or a line end waits).
AFrozen : ℕ → WL → Set
AFrozen j (σ , p) = suc j < W.k σ ⊎ (W.k σ ≡ suc j × (W.onLine σ ≡ false ⊎ p ≡ true))

private
  <-≢ : ∀ {j k} → j < k → j ≢ k
  <-≢ {j} j<k refl = <-irrefl refl j<k

  -- The walker's moves, one function at a time.
  lineEnd-k : ∀ b σ → W.k (lineEnd b σ) ≡ W.k σ
  lineEnd-k b (walker k h (line-text _) hs b′ t) = refl
  lineEnd-k b (walker k h line-empty hs b′ t)   = refl
  lineEnd-k b (walker k h line-code hs b′ t)    = refl

  lineEnd-acc : ∀ b σ → W.acc (lineEnd b σ) ≡ W.acc σ
  lineEnd-acc b (walker k h (line-text _) hs b′ t) = refl
  lineEnd-acc b (walker k h line-empty hs b′ t)   = refl
  lineEnd-acc b (walker k h line-code hs b′ t)    = refl

  lineEnd-on : ∀ b σ → W.onLine (lineEnd b σ) ≡ false
  lineEnd-on b (walker k h (line-text _) hs b′ t) = refl
  lineEnd-on b (walker k h line-empty hs b′ t)   = refl
  lineEnd-on b (walker k h line-code hs b′ t)    = refl

  nlW-k : ∀ p σ → W.k (nlW p σ) ≡ W.k σ
  nlW-k true  σ = lineEnd-k true σ
  nlW-k false σ = refl

  -- a line that starts a declaration moves what stood before the next anchor, in place, before it
  endT-ti : ∀ j σ → j < W.k σ → ti (Look j (stepTok σ false true)) ≡ ti (Look j σ)
  endT-ti j (walker k h (line-text _) hs b t) j<k = cong ti (hoistAt-other j k t (<-≢ j<k))
  endT-ti j (walker k h line-empty hs b t)    j<k = cong ti (hoistAt-other j k t (<-≢ j<k))
  endT-ti j (walker k h line-code hs b t)     j<k = cong ti (hoistAt-other j k t (<-≢ j<k))

  endT-after : ∀ j σ → Notes.after (Look j (stepTok σ false true)) ≡ Notes.after (Look j σ)
  endT-after j (walker k h (line-text _) hs b t) = hoistAt-after j k t
  endT-after j (walker k h line-empty hs b t)    = hoistAt-after j k t
  endT-after j (walker k h line-code hs b t)     = hoistAt-after j k t

  nlW-ti : ∀ j p σ → j < W.k σ → ti (Look j (nlW p σ)) ≡ ti (Look j σ)
  nlW-ti j true  σ j<k = endT-ti j σ j<k
  nlW-ti j false σ j<k = refl

  nlW-after : ∀ j p σ → Notes.after (Look j (nlW p σ)) ≡ Notes.after (Look j σ)
  nlW-after j true  σ = endT-after j σ
  nlW-after j false σ = refl

  contW-k : ∀ p σ → W.k (contW p σ) ≡ W.k σ
  contW-k true  σ = lineEnd-k false σ
  contW-k false σ = refl

  contW-acc : ∀ p σ → W.acc (contW p σ) ≡ W.acc σ
  contW-acc true  σ = lineEnd-acc false σ
  contW-acc false σ = refl

  -- after `nlW p`, the line has an anchor only if it had one and no line end waited
  nlW-on : ∀ p σ → W.onLine σ ≡ false ⊎ p ≡ true → W.onLine (nlW p σ) ≡ false
  nlW-on true  σ _          = lineEnd-on true σ
  nlW-on false σ (inj₁ e)   = e
  nlW-on false σ (inj₂ ())

  contW-on : ∀ p σ → W.onLine σ ≡ false ⊎ p ≡ true → W.onLine (contW p σ) ≡ false
  contW-on true  σ _          = lineEnd-on false σ
  contW-on false σ (inj₁ e)   = e
  contW-on false σ (inj₂ ())

  -- a token: the index grows by one at an anchor; settling writes at the index
  tok-k : ∀ σ a b → W.k σ ≤ W.k (stepTok σ a b)
  tok-k σ a true = Data.Nat.Properties.≤-reflexive (sym (lineEnd-k true σ))
  tok-k (walker k h ln hs b t) true  false = m≤n⇒m≤1+n ≤-refl
  tok-k (walker k h ln hs b t) false false = ≤-refl

  tok-ti : ∀ j σ a b → j < W.k σ → ti (Look j (stepTok σ a b)) ≡ ti (Look j σ)
  tok-ti j σ a true j<k = endT-ti j σ j<k
  tok-ti j (walker k h ln hs b t) true  false j<k = cong ti (lookup-settleAt j k (promote (pending ln (blankBefore b hs))) t (<-≢ j<k))
  tok-ti j (walker k h ln hs b t) false false j<k = cong ti (lookup-settleAt j k (promote (pending ln (blankBefore b hs))) t (<-≢ j<k))

  tok-after : ∀ j σ a b → Notes.after (Look j (stepTok σ a b)) ≡ Notes.after (Look j σ)
  tok-after j σ a true = endT-after j σ
  tok-after j (walker k h ln hs b t) true  false = settleAt-after j k (promote (pending ln (blankBefore b hs))) t
  tok-after j (walker k h ln hs b t) false false = settleAt-after j k (promote (pending ln (blankBefore b hs))) t

  -- after a token not an anchor, the line has an anchor only if it had one (or the token ends it)
  tok-on : ∀ σ b → W.onLine σ ≡ false → W.onLine (stepTok σ false b) ≡ false
  tok-on σ true e = lineEnd-on true σ
  tok-on (walker k false ln hs b t) false refl = refl

  -- a comment writes only at the end of the last anchor's line, when that anchor is on it
  com-k : ∀ σ c → W.k (stepComment σ c) ≡ W.k σ
  com-k (walker k h line-empty hs b t) c    = refl
  com-k (walker k h (line-text _) hs b t) c = refl
  com-k (walker k true line-code hs b t) c  = refl
  com-k (walker k false line-code hs b t) c = refl

  com-on : ∀ σ c → W.onLine (stepComment σ c) ≡ W.onLine σ
  com-on (walker k h line-empty hs b t) c    = refl
  com-on (walker k h (line-text _) hs b t) c = refl
  com-on (walker k true line-code hs b t) c  = refl
  com-on (walker k false line-code hs b t) c = refl

  com-ti : ∀ j σ c → ti (Look j (stepComment σ c)) ≡ ti (Look j σ)
  com-ti j (walker k h line-empty hs b t) c    = refl
  com-ti j (walker k h (line-text _) hs b t) c = refl
  com-ti j (walker k true line-code hs b t) c  = lookup-addTo-keeps ti j (k ∸ 1) (addAfter c) t (λ { (notes _ _ _) → refl })
  com-ti j (walker k false line-code hs b t) c = refl

  com-after : ∀ j σ c → (W.onLine σ ≡ false ⊎ suc j < W.k σ) → Notes.after (Look j (stepComment σ c)) ≡ Notes.after (Look j σ)
  com-after j (walker k h line-empty hs b t) c _    = refl
  com-after j (walker k h (line-text _) hs b t) c _ = refl
  com-after j (walker k true line-code hs b t) c (inj₁ ())
  com-after j (walker (suc k) true line-code hs b t) c (inj₂ j<k) =
    cong Notes.after (lookup-addTo j k _ t (<-≢ (Data.Nat.Properties.<-pred j<k)))
  com-after j (walker k false line-code hs b t) c _ = refl

  ≡-k : ∀ {m n} → m ≡ n → m ≤ n
  ≡-k refl = ≤-refl

  -- | One lexeme keeps the frozen notes frozen.
  stepL-ti : ∀ j ω x → j < W.k (proj₁ ω) → ti (Look j (proj₁ (stepL ω x))) ≡ ti (Look j (proj₁ ω)) × j < W.k (proj₁ (stepL ω x))
  stepL-ti j (σ , p) (lt x) lt′ =
    trans (tok-ti j (nlW p σ) (anchorTok x) (lineEndTok x) (subst (j <_) (sym (nlW-k p σ)) lt′))
          (nlW-ti j p σ lt′) ,
    ≤-trans (subst (j <_) (sym (nlW-k p σ)) lt′) (tok-k (nlW p σ) (anchorTok x) (lineEndTok x))
  stepL-ti j (σ , p) lsp lt′ = cong (λ t → ti (lookupNotes j t)) (contW-acc p σ) , subst (j <_) (sym (contW-k p σ)) lt′
  stepL-ti j (σ , p) lnl lt′ = nlW-ti j p σ lt′ , subst (j <_) (sym (nlW-k p σ)) lt′
  stepL-ti j (σ , p) (lind zero) lt′ = refl , lt′
  stepL-ti j (σ , p) (lind (suc _)) lt′ = cong (λ t → ti (lookupNotes j t)) (contW-acc p σ) , subst (j <_) (sym (contW-k p σ)) lt′
  stepL-ti j (σ , p) (lcm c) lt′ =
    trans (com-ti j (nlW p σ) (trimEnd (fromList c))) (nlW-ti j p σ lt′) ,
    subst (j <_) (sym (trans (com-k (nlW p σ) (trimEnd (fromList c))) (nlW-k p σ))) lt′

  stepL-after : ∀ j ω x → AFrozen j ω → Notes.after (Look j (proj₁ (stepL ω x))) ≡ Notes.after (Look j (proj₁ ω)) × AFrozen j (stepL ω x)
  stepL-after j (σ , p) (lt x) fz with anchorTok x | lineEndTok x
  ... | a | true =
    trans (tok-after j (nlW p σ) a true) (nlW-after j p σ) ,
    frz fz
    where
      frz : AFrozen j (σ , p) → AFrozen j (stepTok (nlW p σ) a true , false)
      frz (inj₁ lt′) = inj₁ (subst (_ <_) (sym (trans (lineEnd-k true (nlW p σ)) (nlW-k p σ))) lt′)
      frz (inj₂ (e , _)) = inj₂ (trans (trans (lineEnd-k true (nlW p σ)) (nlW-k p σ)) e , inj₁ (lineEnd-on true (nlW p σ)))
  ... | true | false =
    trans (tok-after j (nlW p σ) true false) (nlW-after j p σ) ,
    inj₁ (frz fz)
    where
      grow : ∀ τ → W.k (stepTok τ true false) ≡ suc (W.k τ)
      grow (walker k h ln hs b t) = refl
      frz : AFrozen j (σ , p) → suc j < W.k (stepTok (nlW p σ) true false)
      frz (inj₁ lt′) = subst (suc j <_) (sym (grow (nlW p σ)))
                         (m≤n⇒m≤1+n (subst (suc j <_) (sym (nlW-k p σ)) lt′))
      frz (inj₂ (e , _)) = subst (suc j <_) (sym (grow (nlW p σ))) (s≤s (≡-k (sym (trans (nlW-k p σ) e))))
  ... | false | false =
    trans (tok-after j (nlW p σ) false false) (nlW-after j p σ) ,
    frz fz
    where
      same : ∀ τ → W.k (stepTok τ false false) ≡ W.k τ
      same (walker k h ln hs b t) = refl
      frz : AFrozen j (σ , p) → AFrozen j (stepTok (nlW p σ) false false , false)
      frz (inj₁ lt′) = inj₁ (subst (suc j <_) (sym (trans (same (nlW p σ)) (nlW-k p σ))) lt′)
      frz (inj₂ (e , o)) = inj₂ (trans (trans (same (nlW p σ)) (nlW-k p σ)) e , inj₁ (tok-on (nlW p σ) false (nlW-on p σ o)))
  stepL-after j (σ , p) lsp fz = cong (λ t → Notes.after (lookupNotes j t)) (contW-acc p σ) , frz fz
    where
      frz : AFrozen j (σ , p) → AFrozen j (contW p σ , false)
      frz (inj₁ lt′) = inj₁ (subst (suc j <_) (sym (contW-k p σ)) lt′)
      frz (inj₂ (e , o)) = inj₂ (trans (contW-k p σ) e , inj₁ (contW-on p σ o))
  stepL-after j (σ , p) lnl fz = nlW-after j p σ , frz fz
    where
      frz : AFrozen j (σ , p) → AFrozen j (nlW p σ , true)
      frz (inj₁ lt′) = inj₁ (subst (suc j <_) (sym (nlW-k p σ)) lt′)
      frz (inj₂ (e , o)) = inj₂ (trans (nlW-k p σ) e , inj₂ refl)
  stepL-after j (σ , p) (lind zero) fz = refl , fz
  stepL-after j (σ , p) (lind (suc _)) fz = cong (λ t → Notes.after (lookupNotes j t)) (contW-acc p σ) , frz fz
    where
      frz : AFrozen j (σ , p) → AFrozen j (contW p σ , false)
      frz (inj₁ lt′) = inj₁ (subst (suc j <_) (sym (contW-k p σ)) lt′)
      frz (inj₂ (e , o)) = inj₂ (trans (contW-k p σ) e , inj₁ (contW-on p σ o))
  stepL-after j (σ , p) (lcm c) fz =
    trans (com-after j (nlW p σ) _ (pre fz)) (nlW-after j p σ) , frz fz
    where
      pre : AFrozen j (σ , p) → W.onLine (nlW p σ) ≡ false ⊎ suc j < W.k (nlW p σ)
      pre (inj₁ lt′) = inj₂ (subst (suc j <_) (sym (nlW-k p σ)) lt′)
      pre (inj₂ (_ , o)) = inj₁ (nlW-on p σ o)
      frz : AFrozen j (σ , p) → AFrozen j (stepComment (nlW p σ) _ , false)
      frz (inj₁ lt′) = inj₁ (subst (suc j <_) (sym (trans (com-k (nlW p σ) _) (nlW-k p σ))) lt′)
      frz (inj₂ (e , o)) = inj₂ (trans (trans (com-k (nlW p σ) _) (nlW-k p σ)) e ,
                                 inj₁ (trans (com-on (nlW p σ) _) (nlW-on p σ o)))

-- | The trivia a walk ends with.
fin : WL → Trivia
fin ω = finish (closeL ω)

private
  settle-ti : ∀ j τ → j < W.k τ → ti (lookupNotes j (W.acc (settle τ))) ≡ ti (Look j τ)
  settle-ti j (walker k h ln hs b t) j<k = cong ti (lookup-settleAt j k (promote hs) t (<-≢ j<k))

  settle-after : ∀ j τ → Notes.after (lookupNotes j (W.acc (settle τ))) ≡ Notes.after (Look j τ)
  settle-after j (walker k h ln hs b t) = settleAt-after j k (promote hs) t

  endT-k : ∀ σ → W.k (stepTok σ false true) ≡ W.k σ
  endT-k (walker k h (line-text _) hs b t) = refl
  endT-k (walker k h line-empty hs b t)    = refl
  endT-k (walker k h line-code hs b t)     = refl

  close-k : ∀ ω → W.k (lineEnd true (closeL ω)) ≡ W.k (proj₁ ω)
  close-k (σ , p) = trans (lineEnd-k true (closeL (σ , p))) (trans (endT-k (nlW p σ)) (nlW-k p σ))

  close-ti : ∀ j ω → j < W.k (proj₁ ω) → ti (lookupNotes j (fin ω)) ≡ ti (Look j (proj₁ ω))
  close-ti j (σ , p) j<k =
    trans (settle-ti j (lineEnd true (closeL (σ , p))) (subst (j <_) (sym (close-k (σ , p))) j<k))
      (trans (cong (λ t → ti (lookupNotes j t)) (lineEnd-acc true (closeL (σ , p))))
        (trans (endT-ti j (nlW p σ) (subst (j <_) (sym (nlW-k p σ)) j<k)) (nlW-ti j p σ j<k)))

  close-after : ∀ j ω → Notes.after (lookupNotes j (fin ω)) ≡ Notes.after (Look j (proj₁ ω))
  close-after j (σ , p) =
    trans (settle-after j (lineEnd true (closeL (σ , p))))
      (trans (cong (λ t → Notes.after (lookupNotes j t)) (lineEnd-acc true (closeL (σ , p))))
        (trans (endT-after j (nlW p σ)) (nlW-after j p σ)))

-- | What stands before a passed anchor is what the walk ends with.
frozen-ti : ∀ j ω xs → j < W.k (proj₁ ω) → ti (lookupNotes j (fin (walkL ω xs))) ≡ ti (Look j (proj₁ ω))
frozen-ti j ω []       lt′ = close-ti j ω lt′
frozen-ti j ω (x ∷ xs) lt′ with stepL-ti j ω x lt′
... | e , lt″ = trans (frozen-ti j (stepL ω x) xs lt″) e

-- | So is what ends a line that has ended.
frozen-after : ∀ j ω xs → AFrozen j ω → Notes.after (lookupNotes j (fin (walkL ω xs))) ≡ Notes.after (Look j (proj₁ ω))
frozen-after j ω []       fz = close-after j ω
frozen-after j ω (x ∷ xs) fz with stepL-after j ω x fz
... | e , fz′ = trans (frozen-after j (stepL ω x) xs fz′) e
