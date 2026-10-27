-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Order — `once fmt` keeps the comments, in order (plan
-- 0.124 step 4.5).
--
-- The output's comment words are the input's, in order (`comments-kept`).
-- The walker numbers the input's anchors and keeps the words anchor by
-- anchor (`WalkWords.trivia-words`); the printer writes them declaration by
-- declaration (`Printed.pdecls-DocC`) and the layout writes what it reads
-- (`Written.render-words`). The two orders agree because a comment stands
-- before a declaration only at a line end (`WalkWords.trivia-tops`), and a
-- parsed text's line ends stand between its declarations, where the
-- printer's anchor count (`Counts`) and the grammar's (`GAnchors`) meet.
------------------------------------------------------------------------

module Once.Format.Proof.Order where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; concatMap; map; foldr)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injective)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm; m+n∸m≡n; ≤-refl; <-irrefl; ≤-trans; m≤m+n;
  n<1+n; <-≤-trans; ≤-<-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

open import Once.Spec.Surface.Lexing using (Token; TWord; TNewline; TEOF)
open import Once.Spec.Surface.Syntax using (Decl; Module; mkModule)
open import Once.Spec.Surface.Grammar using (Trailing; trail-end; trail-nl; trail-eof)
open import Once.Format.Doc using (toks)
open import Once.Format.Print using (pdecl)
open import Once.Format.Proof.Skeleton using (anchorTok; lineEndTok)
open import Once.Format.Proof.Counts using (Ind; ind-pdecl; anchors)
open import Once.Format.Proof.GAnchors using (Good; cD; Seg; NoNl; anchors-++; Nls; DeclSegs; decl-seg; decls-segs)
open import Once.Format.Proof.Lexing using (Printable; p-word; p-int; p-float; p-sym; Sym; s-lparen; s-rparen;
  s-lbrace; s-rbrace; s-colon; s-equals; s-arrow; s-caret1; s-caret0; s-caretw; s-lambda; s-comma; s-semicolon; s-at;
  s-pipe; s-dot; s-plus; s-minus; s-star; s-slash; s-percent; s-ampersand; s-lt; s-le; s-gt; s-ge; s-eqeq; s-neq; s-bang)
open import Once.Format.Proof.LexOK using (LexOK; Other; o-nl; o-eof; o-str)
open import Once.Format.Proof.ExprBase using (word-notOperator)

open import Once.Format.Proof.Printable using (PD; run; pr-gn; pr-body)
open import Once.Format.Proof.Decl using (WFD; decl-parses)
open import Once.Format.Proof.Layout using (toks-++)

------------------------------------------------------------------------
-- Words the lexer reads are no operator names
------------------------------------------------------------------------

good-pr : ∀ {t} → Printable t → Good t
good-pr (p-word {s} {c} {i} eq _ _ st _) = word-notOperator s c i eq st
good-pr p-int              = tt
good-pr (p-float _)        = tt
good-pr (p-sym s-lparen)   = tt
good-pr (p-sym s-rparen)   = tt
good-pr (p-sym s-lbrace)   = tt
good-pr (p-sym s-rbrace)   = tt
good-pr (p-sym s-colon)    = tt
good-pr (p-sym s-equals)   = tt
good-pr (p-sym s-arrow)    = tt
good-pr (p-sym s-caret1)   = tt
good-pr (p-sym s-caret0)   = tt
good-pr (p-sym s-caretw)   = tt
good-pr (p-sym s-lambda)   = tt
good-pr (p-sym s-comma)    = tt
good-pr (p-sym s-semicolon) = tt
good-pr (p-sym s-at)       = tt
good-pr (p-sym s-pipe)     = tt
good-pr (p-sym s-dot)      = tt
good-pr (p-sym s-plus)     = tt
good-pr (p-sym s-minus)    = tt
good-pr (p-sym s-star)     = tt
good-pr (p-sym s-slash)    = tt
good-pr (p-sym s-percent)  = tt
good-pr (p-sym s-ampersand) = tt
good-pr (p-sym s-lt)       = tt
good-pr (p-sym s-le)       = tt
good-pr (p-sym s-gt)       = tt
good-pr (p-sym s-ge)       = tt
good-pr (p-sym s-eqeq)     = tt
good-pr (p-sym s-neq)      = tt
good-pr (p-sym s-bang)     = tt

good-ok : ∀ {t} → LexOK t → Good t
good-ok (inj₁ p)     = good-pr p
good-ok (inj₂ o-nl)  = tt
good-ok (inj₂ o-eof) = tt
good-ok (inj₂ o-str) = tt

------------------------------------------------------------------------
-- The printer counts a declaration's anchors as the grammar does
------------------------------------------------------------------------

-- | The anchors the printer numbers in a declaration.
cP : Decl → ℕ
cP d = Ind.c (ind-pdecl d)

cP-cD : ∀ d → WFD d → PD d → cP d ≡ cD d
cP-cD d w p = trans (sym (+-identityʳ (cP d))) (trans (sym (Ind.tks (ind-pdecl d) [] 0 (TNewline ∷ []))) (trans as (+-identityʳ (cD d))))
  where
    D = proj₁ (pdecl d [] 0)
    good : All Good (toks D (TNewline ∷ []))
    good = subst (All Good) (sym (toks-++ D (TNewline ∷ [])))
             (AllP.++⁺ (Data.List.Relation.Unary.All.map good-pr (run (pr-gn (pr-body d p)) [] 0 [] [])) (tt ∷ []))
    sg : Seg (cD d) (toks D (TNewline ∷ [])) (TNewline ∷ [])
    sg = decl-seg good (decl-parses d [] 0 [] w)
    as : anchors (toks D (TNewline ∷ [])) ≡ cD d + 0
    as = trans (cong anchors (proj₁ (proj₂ sg))) (trans (anchors-++ (proj₁ sg) (TNewline ∷ [])) (cong (_+ 0) (proj₁ (proj₂ (proj₂ sg)))))

------------------------------------------------------------------------
-- Where the declarations start
------------------------------------------------------------------------

-- | The anchor index `j` is where one of the declarations `ds` starts, or
-- where they end, counting from `k` (each declaration holding `f d`).
data Start (f : Decl → ℕ) : List Decl → ℕ → ℕ → Set where
  here  : ∀ {ds k} → Start f ds k k
  there : ∀ {d ds k j} → Start f ds (k + f d) j → Start f (d ∷ ds) k j

Σc : (Decl → ℕ) → List Decl → ℕ
Σc f = foldr (λ d n → f d + n) 0

start-≥ : ∀ {f ds k j} → Start f ds k j → k ≤ j
start-≥ here      = ≤-refl
start-≥ (there s) = ≤-trans (m≤m+n _ _) (start-≥ s)

start-cong : ∀ {f g} ds → All (λ d → f d ≡ g d) ds → ∀ {k j} → Start f ds k j → Start g ds k j
start-cong ds        _        here      = here
start-cong {f} {g} (d ∷ ds) (e ∷ es) {k} {j} (there s) =
  there (subst (λ m → Start g ds m j) (cong (k +_) e) (start-cong {f} {g} ds es s))

-- | The end of the declarations.
start-end : ∀ f ds k → Start f ds k (k + Σc f ds)
start-end f []       k = subst (Start f [] k) (sym (+-identityʳ k)) here
start-end f (d ∷ ds) k = there (subst (Start f ds (k + f d)) (+-assoc k (f d) (Σc f ds)) (start-end f ds (k + f d)))

private
  -- tokens that hold no anchor
  NoA : List Token → Set
  NoA = All (λ t → anchorTok t ≡ false)

  noA-0 : ∀ ts → NoA ts → anchors ts ≡ 0
  noA-0 []       []       = refl
  noA-0 (t ∷ ts) (p ∷ ps) = trans (cong (λ b → (if b then 1 else 0) + anchors ts) p) (noA-0 ts ps)

  nls-noA : ∀ {ts} → Nls ts → NoA ts
  nls-noA []         = []
  nls-noA (refl ∷ ps) = refl ∷ nls-noA ps

  trail-noA : ∀ {ts} → Trailing ts → NoA ts
  trail-noA trail-end    = []
  trail-noA (trail-nl t)  = refl ∷ trail-noA t
  trail-noA (trail-eof t) = refl ∷ trail-noA t

  -- where an element stands in a concatenation
  split : ∀ {A : Set} (xs ys pre : List A) y rest → xs ++ ys ≡ pre ++ y ∷ rest
        → (∃[ q ] xs ≡ pre ++ y ∷ q) ⊎ (∃[ q ] (pre ≡ xs ++ q × ys ≡ q ++ y ∷ rest))
  split []       ys pre       y rest e = inj₂ (pre , refl , e)
  split (x ∷ xs) ys []        y rest e = inj₁ (xs , cong (_∷ xs) (proj₁ (∷-injective e)))
  split (x ∷ xs) ys (p ∷ pre) y rest e with split xs ys pre y rest (proj₂ (∷-injective e))
  ... | inj₁ (q , e′)      = inj₁ (q , cong₂ _∷_ (proj₁ (∷-injective e)) e′)
  ... | inj₂ (q , e′ , e″) = inj₂ (q , cong₂ _∷_ (sym (proj₁ (∷-injective e))) e′ , e″)

  noA-pre : ∀ pre y rest ts → ts ≡ pre ++ y ∷ rest → NoA ts → NoA pre
  noA-pre pre y rest ts refl a = AllP.++⁻ˡ pre a

  noNl-in : ∀ pre y q → NoNl (pre ++ y ∷ q) → lineEndTok y ≡ false
  noNl-in pre y q nn with AllP.++⁻ʳ pre nn
  ... | p ∷ _ = p

  clash : ∀ {b} → b ≡ true → b ≡ false → ⊥
  clash refl ()

-- | A line end among a parsed text's tokens stands where a declaration
-- starts, or at the end.
starts-segs : ∀ k ds ts r → DeclSegs ds ts r → NoA r → ∀ pre y rest → ts ≡ pre ++ y ∷ rest → lineEndTok y ≡ true
            → Start cD ds k (k + anchors pre)
starts-segs k [] ts r (nls , e , n) ar pre y rest et le =
  subst (Start cD [] k) (sym (trans (cong (k +_) (noA-0 pre (noA-pre pre y rest ts et (subst NoA (sym e) (AllP.++⁺ (nls-noA n) ar))))) (+-identityʳ k))) here
starts-segs k (d ∷ ds) ts r (nls , mid , e , n , rest′ , (seg , em , an , nn) , segs) ar pre y rest et le
  with split nls mid pre y rest (trans (sym e) et)
... | inj₁ (q , eq) =
  subst (Start cD (d ∷ ds) k) (sym (trans (cong (k +_) (noA-0 pre (noA-pre pre y q nls eq (nls-noA n)))) (+-identityʳ k))) here
... | inj₂ (q , ep , eq) with split seg rest′ q y rest (trans (sym em) eq)
...   | inj₁ (q′ , es) = ⊥-elim (clash le (noNl-in q y q′ (subst NoNl es nn)))
...   | inj₂ (q″ , eq′ , er) =
  there (subst (Start cD ds (k + cD d)) idx (starts-segs (k + cD d) ds rest′ r segs ar q″ y rest er le))
  where
    idx : k + cD d + anchors q″ ≡ k + anchors pre
    idx = trans (+-assoc k (cD d) (anchors q″))
            (cong (k +_) (sym (trans (cong anchors ep) (trans (anchors-++ nls q)
              (trans (cong₂ _+_ (noA-0 nls (nls-noA n)) (trans (cong anchors eq′) (anchors-++ seg q″)))
                     (cong (_+ anchors q″) an))))))

-- | A parsed text's anchors are its declarations'.
anchors-segs : ∀ ds ts r → DeclSegs ds ts r → NoA r → anchors ts ≡ Σc cD ds
anchors-segs [] ts r (nls , e , n) ar = trans (cong anchors e) (noA-0 _ (AllP.++⁺ (nls-noA n) ar))
anchors-segs (d ∷ ds) ts r (nls , mid , e , n , rest′ , (seg , em , an , nn) , segs) ar =
  trans (cong anchors e) (trans (anchors-++ nls mid) (trans (cong₂ _+_ (noA-0 nls (nls-noA n))
    (trans (cong anchors em) (trans (anchors-++ seg rest′) (cong₂ _+_ an (anchors-segs ds rest′ r segs ar))))) refl))

------------------------------------------------------------------------
-- The printer's order is the walker's
------------------------------------------------------------------------

open import Once.Format.Print using (Notes; lookupNotes; Trivia; hoist; topList; tops; note-comment)
open import Once.Format.Proof.Counts using (AnchC)
open import Once.Format.Proof.Printed using (MNote; MNotes; DC)
open import Once.Format.Proof.WalkWords using (slotW; ITs; slotW-hoist; slotW-up; MNotes-map-nc)
open import Once.Format.Proof.Walk using (up; hoist-at; hoist-other; hoist-after)
open import Once.Format.Proof.Words using (Mn; cm-++)

-- | The words of the anchors in [k, k + n), in order.
ITfrom : Trivia → ℕ → ℕ → List (List Char)
ITfrom t k zero    = []
ITfrom t k (suc n) = slotW (lookupNotes k t) ++ ITfrom t (suc k) n

ITfrom-+ : ∀ t k a b → ITfrom t k (a + b) ≡ ITfrom t k a ++ ITfrom t (k + a) b
ITfrom-+ t k zero    b = cong (λ m → ITfrom t m b) (sym (+-identityʳ k))
ITfrom-+ t k (suc a) b =
  trans (cong (slotW (lookupNotes k t) ++_)
          (trans (ITfrom-+ t (suc k) a b) (cong (λ m → ITfrom t (suc k) a ++ ITfrom t m b) (sym (+-suc k a)))))
    (sym (++-assoc (slotW (lookupNotes k t)) (ITfrom t (suc k) a) _))

ITs-from : ∀ t n → ITs t n ≡ ITfrom t 0 n
ITs-from t zero    = refl
ITs-from t (suc n) =
  trans (cong (_++ slotW (lookupNotes n t)) (ITs-from t n))
    (sym (trans (cong (ITfrom t 0) (+-comm 1 n)) (trans (ITfrom-+ t 0 n 1) (cong (ITfrom t 0 n ++_) (++-identityʳ _)))))

private
  ITfrom-hoist : ∀ t k j n → ITfrom (hoist k t) j n ≡ ITfrom t j n
  ITfrom-hoist t k j zero    = refl
  ITfrom-hoist t k j (suc n) = cong₂ _++_ (slotW-hoist j k t) (ITfrom-hoist t k (suc j) n)

  AnchC-cong : ∀ t t′ k n → (∀ j → k ≤ j → lookupNotes j t′ ≡ lookupNotes j t) → AnchC t′ k n ≡ AnchC t k n
  AnchC-cong t t′ k zero    h = refl
  AnchC-cong t t′ k (suc n) h =
    cong₂ (λ a b → concatMap Mn (Notes.inner a) ++ concatMap Mn (Notes.after a) ++ b) (h k ≤-refl)
      (AnchC-cong t t′ (suc k) n (λ j le → h j (≤-trans (n≤1+n k) le)))
    where open Data.Nat.Properties using (n≤1+n)

  -- anchors whose top notes hold no comment: their words are their notes' in place
  anch-it : ∀ t k n → (∀ j → k ≤ j → j < k + n → MNotes (Notes.top (lookupNotes j t)) ≡ []) → AnchC t k n ≡ ITfrom t k n
  anch-it t k zero    h = refl
  anch-it t k (suc n) h =
    trans (cong (λ z → concatMap Mn (Notes.inner nk) ++ concatMap Mn (Notes.after nk) ++ z)
                (anch-it t (suc k) n (λ j le lt → h j (≤-trans (n≤1+n k) le) (subst (j <_) (sym (+-suc k n)) lt))))
      (sym (trans (cong (λ z → (z ++ concatMap Mn (Notes.inner nk) ++ concatMap Mn (Notes.after nk)) ++ ITfrom t (suc k) n)
                        (h k ≤-refl (subst (k <_) (sym (+-suc k n)) (s≤s (m≤m+n k n)))))
                  (++-assoc (concatMap Mn (Notes.inner nk)) (concatMap Mn (Notes.after nk)) (ITfrom t (suc k) n))))
    where
      nk = lookupNotes k t
      open Data.Nat.Properties using (n≤1+n)

  tops-quiet : ∀ t j n → (∀ i → j ≤ i → i < j + n → MNotes (Notes.top (lookupNotes i t)) ≡ []) → MNotes (tops t j n) ≡ []
  tops-quiet t j zero    h = refl
  tops-quiet t j (suc n) h =
    trans (cm-++ MNote (Notes.top (lookupNotes j t)) (tops t (suc j) n))
      (cong₂ _++_ (h j ≤-refl (subst (j <_) (sym (+-suc j n)) (s≤s (m≤m+n j n))))
                  (tops-quiet t (suc j) n (λ i le lt → h i (≤-trans (n≤1+n j) le) (subst (i <_) (sym (+-suc j n)) lt))))
    where open Data.Nat.Properties using (n≤1+n)

  s∸ : ∀ k → suc k ∸ k ≡ 1
  s∸ zero    = refl
  s∸ (suc k) = s∸ k

  up-top : ∀ n → MNotes (Notes.top (up n)) ≡ MNotes (Notes.top n) ++ concatMap Mn (Notes.inner n)
  up-top n = trans (cm-++ MNote (Notes.top n) (map note-comment (Notes.inner n))) (cong (MNotes (Notes.top n) ++_) (MNotes-map-nc (Notes.inner n)))

  -- one declaration: the notes before it, then its anchors' in place
  decl-W : ∀ tv k c X → (∀ j → k < j → j < k + c → MNotes (Notes.top (lookupNotes j tv)) ≡ [])
         → MNotes (tops (hoist k tv) k c) ++ AnchC (hoist k tv) k c ++ X ≡ ITfrom tv k c ++ X
  decl-W tv k zero    X h = refl
  decl-W tv k (suc m) X h =
    trans (cong₂ (λ a b → a ++ b ++ X) mt an)
      (trans (cong (_++ (concatMap Mn (Notes.after nk) ++ ITfrom tv (suc k) m) ++ X) (++-identityʳ (MNotes (Notes.top nk) ++ concatMap Mn (Notes.inner nk))))
        (trans (++-assoc (MNotes (Notes.top nk)) (concatMap Mn (Notes.inner nk)) _)
          (sym (trans (++-assoc (slotW nk) (ITfrom tv (suc k) m) X)
            (trans (++-assoc (MNotes (Notes.top nk)) (concatMap Mn (Notes.inner nk) ++ concatMap Mn (Notes.after nk)) _)
              (cong (MNotes (Notes.top nk) ++_)
                (trans (++-assoc (concatMap Mn (Notes.inner nk)) (concatMap Mn (Notes.after nk)) _)
                  (cong (concatMap Mn (Notes.inner nk) ++_)
                    (sym (++-assoc (concatMap Mn (Notes.after nk)) (ITfrom tv (suc k) m) X))))))))))
    where
      tv′ = hoist k tv
      nk = lookupNotes k tv
      gt : ∀ {i} → k < i → i ≢ k
      gt le e = <-irrefl (sym e) le
      mt : MNotes (tops tv′ k (suc m)) ≡ (MNotes (Notes.top nk) ++ concatMap Mn (Notes.inner nk)) ++ []
      mt = trans (cm-++ MNote (Notes.top (lookupNotes k tv′)) (tops tv′ (suc k) m))
             (cong₂ _++_ (trans (cong (λ n → MNotes (Notes.top n)) (hoist-at k tv)) (up-top nk))
               (tops-quiet tv′ (suc k) m (λ i le lt → trans (cong (λ n → MNotes (Notes.top n)) (hoist-other i k tv (gt le)))
                                                           (h i le (subst (i <_) (sym (+-suc k m)) lt)))))
      an : AnchC tv′ k (suc m) ≡ concatMap Mn (Notes.after nk) ++ ITfrom tv (suc k) m
      an = trans (cong (λ n → concatMap Mn (Notes.inner n) ++ concatMap Mn (Notes.after n) ++ AnchC tv′ (suc k) m) (hoist-at k tv))
             (cong (concatMap Mn (Notes.after nk) ++_)
               (trans (AnchC-cong tv tv′ (suc k) m (λ j le → hoist-other j k tv (gt le)))
                      (anch-it tv (suc k) m (λ j le lt → h j le (subst (j <_) (sym (+-suc k m)) lt)))))

-- | The printer writes the trivia's words in the walker's order, when
-- comments stand before declarations only where they start.
pt-it : ∀ ds tv k → (∀ j → k ≤ j → MNotes (Notes.top (lookupNotes j tv)) ≡ [] ⊎ Start cP ds k j)
      → Notes.after (lookupNotes (k + Σc cP ds) tv) ≡ []
      → DC ds tv k ≡ ITfrom tv k (suc (Σc cP ds))
pt-it [] tv k ht ha =
  trans (cong (λ n → MNotes (tops (hoist k tv) k n)) (s∸ k))
    (trans (cong MNotes (++-identityʳ (Notes.top (lookupNotes k (hoist k tv)))))
      (trans (cong (λ n → MNotes (Notes.top n)) (hoist-at k tv))
        (trans (up-top nk)
          (sym (trans (++-identityʳ (slotW nk)) (trans (cong (λ z → MNotes (Notes.top nk) ++ concatMap Mn (Notes.inner nk) ++ concatMap Mn z) ha′)
                 (cong (MNotes (Notes.top nk) ++_) (++-identityʳ (concatMap Mn (Notes.inner nk))))))))))
  where
    nk = lookupNotes k tv
    ha′ : Notes.after nk ≡ []
    ha′ = subst (λ m → Notes.after (lookupNotes m tv) ≡ []) (+-identityʳ k) ha
pt-it (d ∷ ds) tv k ht ha =
  trans (cong (λ n → MNotes (tops tv′ k n) ++ AnchC tv′ k c ++ DC ds tv′ (k + c)) (m+n∸m≡n k c))
    (trans (cong (λ z → MNotes (tops tv′ k c) ++ AnchC tv′ k c ++ z)
                 (trans (pt-it ds tv′ (k + c) ht′ ha′) (ITfrom-hoist tv k (k + c) (suc (Σc cP ds)))))
      (trans (decl-W tv k c _ quiet)
        (sym (trans (cong (ITfrom tv k) (sym (+-suc c (Σc cP ds)))) (ITfrom-+ tv k c (suc (Σc cP ds)))))))
  where
    c = cP d
    tv′ = hoist k tv
    quiet : ∀ j → k < j → j < k + c → MNotes (Notes.top (lookupNotes j tv)) ≡ []
    quiet j kj jl with ht j (Data.Nat.Properties.<⇒≤ kj)
    ... | inj₁ e = e
    ... | inj₂ here = ⊥-elim (<-irrefl refl kj)
    ... | inj₂ (there s) = ⊥-elim (<-irrefl refl (<-≤-trans jl (start-≥ s)))
    ht′ : ∀ j → k + c ≤ j → MNotes (Notes.top (lookupNotes j tv′)) ≡ [] ⊎ Start cP ds (k + c) j
    ht′ j le with j Data.Nat.≟ k
    ... | yes refl = inj₂ (subst (Start cP ds (k + c)) (Data.Nat.Properties.≤-antisym le (m≤m+n j c)) here)
    ... | no ne with ht j (≤-trans (m≤m+n k c) le)
    ...   | inj₁ e = inj₁ (trans (cong (λ n → MNotes (Notes.top n)) (hoist-other j k tv ne)) e)
    ...   | inj₂ here = ⊥-elim (ne refl)
    ...   | inj₂ (there s) = inj₂ s
    ha′ : Notes.after (lookupNotes (k + c + Σc cP ds) tv′) ≡ []
    ha′ = trans (hoist-after _ k tv) (subst (λ m → Notes.after (lookupNotes m tv) ≡ []) (sym (+-assoc k c (Σc cP ds))) ha)

------------------------------------------------------------------------
-- The output's comments are the input's, in order
------------------------------------------------------------------------

open import Data.String using (String; toList)
open import Once.Parser using (parseStrict)
import Once.Adequacy.SpecGrammar.Decl
import Once.Adequacy.FrontEndBridge
open import Once.Adequacy.SpecLexing using (forget; spec-lexes-complete)
open import Once.Format.Lex using (lexItems; tokensOf; tokens-lexItems)
open import Once.Format.Print using (format; trivia; pmodule)
open import Once.Format.Proof.LexOK using (DigitBound; lexed-ok)
open import Once.Format.Proof.WF using (parsed-wf)
open import Once.Format.Proof.Module using (module-ws; DeclOK)
open import Once.Format.Proof.Decl using (decl-ok)
open import Once.Format.Proof.Written using (cwords; render-words)
open import Once.Format.Proof.Printed using (pmodule-DocC)
open import Once.Format.Proof.WalkWords using (trivia-words; trivia-end; trivia-tops; kEnd; kEnd-anchors; anchorsP)
open import Once.Format.Proof.Walk using (anchor-forget; end-forget)
import Once.Parser.Token as PT
open import Data.List.Properties using (map-++)

private
  anchorsP-forget : ∀ ts → anchorsP ts ≡ anchors (map forget ts)
  anchorsP-forget []       = refl
  anchorsP-forget (t ∷ ts) = cong₂ (λ b n → (if b then 1 else 0) + n) (anchor-forget t) (anchorsP-forget ts)

  oks : ∀ {ds} → All PD ds → All DeclOK ds
  oks []       = []
  oks (p ∷ ps) = decl-ok _ p ∷ oks ps

  counts : ∀ {ds} → All WFD ds → All PD ds → All (λ d → cD d ≡ cP d) ds
  counts []       []       = []
  counts (w ∷ ws) (p ∷ ps) = sym (cP-cD _ w p) ∷ counts ws ps

  Σc-cong : ∀ {f g} ds → All (λ d → f d ≡ g d) ds → Σc f ds ≡ Σc g ds
  Σc-cong []       []       = refl
  Σc-cong (d ∷ ds) (e ∷ es) = cong₂ _+_ e (Σc-cong ds es)

-- | Formatting keeps a text's comments, in order: the formatted text's
-- comment words are the text's (a comment's words: its text split at
-- blanks and line ends, each word without the dashes it starts with, a
-- block comment's without `{-` and `-}`).
comments-kept : DigitBound → ∀ text m → parseStrict text ≡ inj₂ m
              → cwords (lexItems (toList (format m (lexItems (toList text))))) ≡ cwords (lexItems (toList text))
comments-kept bound text (mkModule ds) eq =
  trans (render-words D (module-ws ds tv (oks pds)))
    (trans (pmodule-DocC ds tv)
      (trans (pt-it ds tv 0 ht ha)
        (trans (sym (ITs-from tv (suc (Σc cP ds))))
          (trans (cong (λ n → ITs tv (suc n)) ΣK) (sym (trivia-words is))))))
  where
    P = Once.Adequacy.SpecGrammar.Decl.parses→ {text} (Once.Adequacy.FrontEndBridge.parseStrict-sound text _ eq)
    ts = proj₁ P
    r  = proj₁ (proj₂ P)
    lx = proj₁ (proj₂ (proj₂ P))
    pd = proj₁ (proj₂ (proj₂ (proj₂ P)))
    tr = proj₂ (proj₂ (proj₂ (proj₂ P)))
    wfs = proj₁ (parsed-wf bound {text} {mkModule ds} P)
    pds = proj₂ (parsed-wf bound {text} {mkModule ds} P)
    is = lexItems (toList text)
    tv = trivia is
    D = proj₁ (pmodule (mkModule ds) tv 0)
    segs : DeclSegs ds ts r
    segs = decls-segs (Data.List.Relation.Unary.All.map good-ok (lexed-ok bound lx)) pd
    tf : map forget (tokensOf is) ≡ ts
    tf = trans (cong (map forget) (tokens-lexItems (toList text))) (spec-lexes-complete text ts lx)
    cc = counts wfs pds
    ΣK : Σc cP ds ≡ kEnd is
    ΣK = trans (sym (Σc-cong ds cc)) (trans (sym (anchors-segs ds ts r segs (trail-noA tr)))
           (trans (cong anchors (sym tf)) (trans (sym (anchorsP-forget (tokensOf is))) (sym (kEnd-anchors is)))))
    ht : ∀ j → 0 ≤ j → MNotes (Notes.top (lookupNotes j tv)) ≡ [] ⊎ Start cP ds 0 j
    ht j _ with trivia-tops is j
    ... | inj₁ e = inj₁ e
    ... | inj₂ (inj₁ (inj₁ e)) = inj₂ (subst (Start cP ds 0) (sym e) here)
    ... | inj₂ (inj₁ (inj₂ (pre , x , rest , e , le , a))) =
      inj₂ (start-cong ds cc (subst (Start cD ds 0) (trans (sym (anchorsP-forget pre)) a)
        (starts-segs 0 ds ts r segs (trail-noA tr) (map forget pre) (forget x) (map forget rest)
          (trans (sym tf) (trans (cong (map forget) e) (map-++ forget pre (x ∷ rest))))
          (trans (sym (end-forget x)) le))))
    ... | inj₂ (inj₂ e) = inj₂ (subst (Start cP ds 0) (trans ΣK (sym e)) (start-end cP ds 0))
    ha : Notes.after (lookupNotes (0 + Σc cP ds) tv) ≡ []
    ha = subst (λ n → Notes.after (lookupNotes n tv) ≡ []) (sym ΣK) (proj₁ (trivia-end is))
