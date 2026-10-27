-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Twice — formatting a formatted text gives it again
-- (plan 0.124 step 4.5).
--
-- The second pass reads the first pass's text as the same module
-- (`RoundTrip`) and its comments as the walk along the first pass's layout
-- finds them (`Walk.formatted-trivia`, `Lockstep`). Declaration by
-- declaration the two passes lay out alike: what stands before the
-- declaration (`Groups.lead-eq`, once the walk is past the declaration's
-- first anchor), the declaration itself (`Inside.start-sim`), its line end;
-- and at the end, what stands after the last declaration
-- (`Groups.ending-eq`).
------------------------------------------------------------------------

module Once.Format.Proof.Twice where

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _≡ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-irrefl; m≤m+n; ≡ᵇ⇒≡)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Format.Print using (Trivia; Notes; notes; noNotes; lookupNotes; hoist; tops; topList; Note;
  note-comment; note-blank)
open import Once.Format.Proof.Sources using (NotesSrc; NoteSrc)
open import Once.Format.Proof.Rerender using (Src)

------------------------------------------------------------------------
-- What `hoist` does
------------------------------------------------------------------------

-- | An anchor's notes as a declaration's first: what stood before it, in place,
-- stands before the declaration.
up : Notes → Notes
up n = notes (Notes.top n ++ map note-comment (Notes.inner n)) [] (Notes.after n)

private
  ≡ᵇ-sym-false : ∀ {j k} → j ≢ k → (k ≡ᵇ j) ≡ false
  ≡ᵇ-sym-false {j} {k} ne with k ≡ᵇ j in e
  ... | true  = ⊥-elim (ne (sym (≡ᵇ⇒≡ k j (subst T (sym e) tt))))
  ... | false = refl

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

hoist-src : ∀ k tv → (∀ j → NotesSrc (lookupNotes j tv)) → ∀ j → NotesSrc (lookupNotes j (hoist k tv))
hoist-src k tv src j with j Data.Nat.≟ k
... | yes refl = subst NotesSrc (sym (hoist-at j tv)) (up-src (src j))
  where
    nc-src : ∀ cs → All Src cs → All NoteSrc (map note-comment cs)
    nc-src []       []       = []
    nc-src (c ∷ cs) (p ∷ ps) = p ∷ nc-src cs ps
    all-++ : ∀ {A : Set} {P : A → Set} xs ys → All P xs → All P ys → All P (xs ++ ys)
    all-++ []       ys []       q = q
    all-++ (x ∷ xs) ys (p ∷ ps) q = p ∷ all-++ xs ys ps q
    up-src : NotesSrc (lookupNotes j tv) → NotesSrc (up (lookupNotes j tv))
    up-src (pt , pi , pa) = all-++ _ _ pt (nc-src _ pi) , [] , pa
... | no ne    = subst NotesSrc (sym (hoist-other j k tv ne)) (src j)

-- | The top notes of anchors, none of which has any, are none.
tops-nil : ∀ tv j n → (∀ i → j ≤ i → i < j + n → Notes.top (lookupNotes i tv) ≡ []) → tops tv j n ≡ []
tops-nil tv j zero    _ = refl
tops-nil tv j (suc n) e rewrite e j ≤-refl (subst (suc j ≤_) (sym (Data.Nat.Properties.+-suc j n)) (s≤s (m≤m+n j n))) =
  tops-nil tv (suc j) n (λ i ji lt → e i (≤-trans (Data.Nat.Properties.n≤1+n j) ji) (subst (i <_) (sym (Data.Nat.Properties.+-suc j n)) lt))

tops-src : ∀ tv j n → (∀ i → NotesSrc (lookupNotes i tv)) → All NoteSrc (tops tv j n)
tops-src tv j zero    src = []
tops-src tv j (suc n) src = all-++ _ _ (proj₁ (src j)) (tops-src tv (suc j) n src)
  where
    all-++ : ∀ {A : Set} {P : A → Set} xs ys → All P xs → All P ys → All P (xs ++ ys)
    all-++ []       ys []       q = q
    all-++ (x ∷ xs) ys (p ∷ ps) q = p ∷ all-++ xs ys ps q

------------------------------------------------------------------------
-- How a declaration starts
------------------------------------------------------------------------

open import Once.Format.Doc using (Doc; empty; blank; _<>_; Lexeme; lt; lsp; lnl; lind; lcm; St; st; brk; layout)
open import Once.Format.Print using (W; walker; line-code; line-empty; line-text; Held; held-blank; held-comment;
  stepTok; lineEnd; settleAt; promote; lead; runs; topDoc; hasComment)
open import Once.Format.Proof.Walk using (WL; stepL; w₀)
open import Once.Format.Proof.Lockstep using (Φ; Φ-cons; waits)
open import Once.Format.Proof.Skeleton using (anchorTok; lineEndTok)
open import Once.Format.Proof.Groups using (groups; gOut; mid; Entry; runs-walk; heldOf; heldOf-top; TopH; hcT;
  promote-top; runs-layout; layoutG-out; groups-ne-all; layoutG; notNull; has-of; gOut-lnl; NE)
open import Once.Spec.Surface.Lexing using (Token)

-- | Where the walk stands before the comments above a declaration, and
-- what the declaration's first token settles if there are none.
EntryT : List Lexeme → ℕ → List Held → Trivia → Set
EntryT o k H₀ T = Entry o k H₀ T
  × (∀ x → lineEndTok x ≡ false
       → proj₁ (Φ (lt x ∷ lind 0 ∷ o)) ≡ walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k H₀ T))

private
  Φ-tok0 : ∀ x o → Φ (lt x ∷ lind 0 ∷ o) ≡ stepL (Φ o) (lt x)
  Φ-tok0 x o = trans (Φ-cons (lt x) (lind 0 ∷ o)) (cong (λ ω → stepL ω (lt x)) (Φ-cons (lind 0) o))

  tok-end : ∀ x ω → lineEndTok x ≡ false
          → proj₁ (stepL ω (lt x)) ≡ stepTok (Once.Format.Proof.Walk.nlW (proj₂ ω) (proj₁ ω)) (anchorTok x) false
  tok-end x (w , p) e = cong (stepTok (Once.Format.Proof.Walk.nlW p w) (anchorTok x)) e

-- | At the start of the text.
entry-start : EntryT [] 0 [] []
entry-start = (λ L → refl) , λ x e → trans (cong proj₁ (Φ-tok0 x [])) (tok-end x (w₀ , false) e)

-- | After a declaration's line end.
entry-decl : ∀ o k h T → Φ o ≡ (walker k h line-code [] 0 T , true) → EntryT o k [] T
entry-decl o k h T e =
  (λ L → trans (Φ-cons lnl (lcm L ∷ lind 0 ∷ o)) (cong (λ ω → stepL ω lnl) (trans (Φ-cons (lcm L) (lind 0 ∷ o))
           (cong (λ ω → stepL ω (lcm L)) (trans (Φ-cons (lind 0) o) (cong (λ ω → stepL ω (lind 0)) e)))))) ,
  λ x ex → trans (cong proj₁ (Φ-tok0 x o)) (trans (tok-end x (Φ o) ex) (cong (λ ω → stepTok (Once.Format.Proof.Walk.nlW (proj₂ ω) (proj₁ ω)) (anchorTok x) false) e))

-- | After a blank line that follows a declaration.
entry-gap : ∀ o k h T → Φ o ≡ (walker k h line-code [] 0 T , true) → EntryT (lnl ∷ o) k (held-blank ∷ []) T
entry-gap o k h T e =
  (λ L → trans (Φ-cons lnl (lcm L ∷ lind 0 ∷ lnl ∷ o)) (cong (λ ω → stepL ω lnl) (trans (Φ-cons (lcm L) (lind 0 ∷ lnl ∷ o))
           (cong (λ ω → stepL ω (lcm L)) (trans (Φ-cons (lind 0) (lnl ∷ o)) (cong (λ ω → stepL ω (lind 0))
             (trans (Φ-cons lnl o) (cong (λ ω → stepL ω lnl) e)))))))) ,
  λ x ex → trans (cong proj₁ (Φ-tok0 x (lnl ∷ o)))
             (trans (tok-end x (Φ (lnl ∷ o)) ex)
               (cong (λ ω → stepTok (Once.Format.Proof.Walk.nlW (proj₂ ω) (proj₁ ω)) (anchorTok x) false)
                 (trans (Φ-cons lnl o) (cong (λ ω → stepL ω lnl) e))))

-- | What the layout and the walk are after the comments before a
-- declaration: at the start of a line, nothing waiting, and the
-- declaration's first token settles `H` before it.
LeadFacts : St → ℕ → List Held → Trivia → Set
LeadFacts σ k H T = St.pend σ ≡ just 0 × St.ends σ ≡ []
  × (∀ x → lineEndTok x ≡ false
       → proj₁ (Φ (lt x ∷ lind 0 ∷ St.out σ)) ≡ walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k H T))

private
  all-++ : ∀ {A : Set} {P : A → Set} xs ys → All P xs → All P ys → All P (xs ++ ys)
  all-++ []       ys []       q = q
  all-++ (x ∷ xs) ys (p ∷ ps) q = p ∷ all-++ xs ys ps q

  blanks-top : ∀ hs → All (_≡ held-blank) hs → All TopH hs
  blanks-top []                 []          = []
  blanks-top (.held-blank ∷ hs) (refl ∷ ps) = tt ∷ blanks-top hs ps


  -- the walk after the runs, at the declaration's first token
  runs-tok : ∀ x o k r H T → lineEndTok x ≡ false → Φ o ≡ mid k r H T → All TopH (H ++ hcT r ∷ [])
           → proj₁ (Φ (lt x ∷ lind 0 ∷ o)) ≡ walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k (H ++ hcT r ∷ []) T)
  runs-tok x o k r H T ex e tp =
    trans (cong proj₁ (Φ-tok0 x o))
      (trans (tok-end x (Φ o) ex)
        (trans (cong (λ ω → stepTok (Once.Format.Proof.Walk.nlW (proj₂ ω) (proj₁ ω)) (anchorTok x) false) e)
          (cong (λ hs → walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k hs T)) (promote-top _ tp))))

  -- …and after a blank line after them
  runs-blank-tok : ∀ x o k r H T → lineEndTok x ≡ false → Φ o ≡ mid k r H T → All TopH ((H ++ hcT r ∷ []) ++ held-blank ∷ [])
                 → proj₁ (Φ (lt x ∷ lind 0 ∷ lnl ∷ o))
                   ≡ walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k ((H ++ hcT r ∷ []) ++ held-blank ∷ []) T)
  runs-blank-tok x o k r H T ex e tp =
    trans (cong proj₁ (Φ-tok0 x (lnl ∷ o)))
      (trans (tok-end x (Φ (lnl ∷ o)) ex)
        (trans (cong (λ ω → stepTok (Once.Format.Proof.Walk.nlW (proj₂ ω) (proj₁ ω)) (anchorTok x) false)
                 (trans (Φ-cons lnl o) (cong (λ ω → stepL ω lnl) e)))
          (cong (λ hs → walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k hs T)) (promote-top _ tp))))

private
  heldG-top : ∀ H₀ G tb → All (_≡ held-blank) H₀ → All (_≡ held-blank) tb → All TopH (H₀ ++ heldOf G ++ tb)
  heldG-top H₀ G tb p₀ pb = all-++ H₀ _ (blanks-top H₀ p₀) (all-++ (heldOf G) tb (heldOf-top G) (blanks-top tb pb))

  lf-none : ∀ og c k H₀ T → EntryT og k H₀ T → LeadFacts (st og c (just 0) []) k (H₀ ++ heldOf [] ++ []) T
  lf-none og c k H₀ T en =
    refl , refl , λ x ex → trans (proj₂ en x ex)
      (cong (λ hs → walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k hs T)) (sym (++-identityʳ H₀)))

-- | The comments before a declaration, in the first pass: the declaration's
-- first token settles each line written, the blank lines between runs, and
-- the blank lines around them.
lead-facts : ∀ prev ns₁ og c k H₀ T → EntryT og k H₀ T → All (_≡ held-blank) H₀
           → ∃[ tb ] All (_≡ held-blank) tb
             × LeadFacts (layout 0 false (lead prev ns₁) (st og c (just 0) [])) k (H₀ ++ heldOf (groups ns₁ [] false) ++ tb) T
lead-facts (just p) ns₁ og c k H₀ T en p₀ =
  [] , [] , subst (λ σ → LeadFacts σ k (H₀ ++ heldOf (groups ns₁ [] false) ++ []) T) (sym (runs-layout 0 false ns₁ [] false _))
              (go (groups ns₁ [] false) (groups-ne-all ns₁ [] false))
  where
    go : ∀ G → All NE G → LeadFacts (layoutG 0 false G (st og c (just 0) [])) k (H₀ ++ heldOf G ++ []) T
    go []       []  = lf-none og c k H₀ T en
    go (R ∷ Rs) nes with runs-walk (R ∷ Rs) og k H₀ T nes (proj₁ en) refl
    ... | r , H , e , q =
      subst (λ σ → LeadFacts σ k (H₀ ++ heldOf (R ∷ Rs) ++ []) T) (sym (layoutG-out false (R ∷ Rs) og c nes))
        (refl , refl , λ x ex →
          trans (runs-tok x (gOut (R ∷ Rs) og) k r H T ex e (subst (All TopH) (sym q) (all-++ H₀ _ (blanks-top H₀ p₀) (heldOf-top (R ∷ Rs)))))
            (cong (λ hs → walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k hs T))
              (trans q (cong (H₀ ++_) (sym (++-identityʳ (heldOf (R ∷ Rs))))))))
lead-facts nothing ns₁ og c k H₀ T en p₀ = go (groups ns₁ [] false) refl (groups-ne-all ns₁ [] false)
  where
    go : ∀ G → groups ns₁ [] false ≡ G → All NE G
       → ∃[ tb ] All (_≡ held-blank) tb × LeadFacts (layout 0 false (lead nothing ns₁) (st og c (just 0) [])) k (H₀ ++ heldOf G ++ tb) T
    go [] eG _ rewrite trans (has-of ns₁) (cong notNull eG) = [] , [] , lf-none og c k H₀ T en
    go (R ∷ Rs) eG nes with runs-walk (R ∷ Rs) og k H₀ T nes (proj₁ en) refl | gOut-lnl R Rs og nes
    ... | r , H , e , q | Y , eY rewrite trans (has-of ns₁) (cong notNull eG) =
      held-blank ∷ [] , refl ∷ [] ,
      subst (λ σ → LeadFacts (layout 0 false blank σ) k (H₀ ++ heldOf (R ∷ Rs) ++ held-blank ∷ []) T)
        (sym (trans (runs-layout 0 false ns₁ [] false _) (trans (cong (λ G → layoutG 0 false G (st og c (just 0) [])) eG)
                                                                  (layoutG-out false (R ∷ Rs) og c nes))))
        (subst (λ O → LeadFacts (layout 0 false blank (st O (Once.Format.Proof.Lockstep.colOf (R ∷ Rs) c) (just 0) [])) k (H₀ ++ heldOf (R ∷ Rs) ++ held-blank ∷ []) T) (sym eY)
          (refl , refl , λ x ex →
            trans (cong (λ O → proj₁ (Φ (lt x ∷ lind 0 ∷ lnl ∷ O))) (sym eY))
              (trans (runs-blank-tok x (gOut (R ∷ Rs) og) k r H T ex e
                        (subst (λ hs → All TopH (hs ++ held-blank ∷ [])) (sym q)
                          (all-++ (H₀ ++ heldOf (R ∷ Rs)) _ (all-++ H₀ _ (blanks-top H₀ p₀) (heldOf-top (R ∷ Rs))) (tt ∷ []))))
                (cong (λ hs → walker (if anchorTok x then suc k else k) (anchorTok x) line-code [] 0 (settleAt k hs T))
                  (trans (cong (_++ held-blank ∷ []) q) (++-assoc H₀ (heldOf (R ∷ Rs)) (held-blank ∷ [])))))))
