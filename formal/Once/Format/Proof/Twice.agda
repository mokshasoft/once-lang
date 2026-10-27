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
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-irrefl; m≤m+n; ≡ᵇ⇒≡; +-identityʳ)
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

------------------------------------------------------------------------
-- Between two declarations
------------------------------------------------------------------------

open import Once.Spec.Surface.Syntax using (Decl)
open import Once.Format.Print using (pdecls; pdecl; pbody; ending; gap; gapEnd; together)
open import Once.Format.Proof.Walk using (fin; frozen-ti; ti; Look; settleAt-after; lookup-settleAt)
open import Once.Format.Proof.Lockstep using (LI; li; layout-reach; brk-ok; Reach; reach-trans; reach-refl)
open import Once.Format.Proof.Groups using (rsOf; groups-pass2; notesOf; notesOf-++; settle-tops; settle-tops-inner;
  lead-eq; ending-eq)

-- | The walk where a declaration ended (or at the text's start).
BW : St → ℕ → Trivia → Maybe Decl → Set
BW σ k T nothing  = St.out σ ≡ [] × k ≡ 0 × T ≡ []
BW σ k T (just _) = (∃[ h ] Φ (St.out σ) ≡ (walker k h line-code [] 0 T , true)) × (∃[ x ] ∃[ xs ] St.out σ ≡ x ∷ xs)

-- | Between two declarations: at the start of a line, nothing waiting; the
-- walk where the last declaration ended, nothing found yet at the next
-- anchors but blank lines before the next one.
record Bnd (σ : St) (k : ℕ) (T : Trivia) (prev : Maybe Decl) : Set where
  constructor bnd
  field
    b-pend  : St.pend σ ≡ just 0
    b-ends  : St.ends σ ≡ []
    b-walk  : BW σ k T prev
    b-after : ∀ j → k ≤ j → Notes.after (lookupNotes j T) ≡ []
    b-inner : ∀ j → k ≤ j → Notes.inner (lookupNotes j T) ≡ []
    b-top   : ∀ j → k < j → Notes.top (lookupNotes j T) ≡ []
    b-topk  : All (_≡ note-blank) (Notes.top (lookupNotes k T))
    b-li    : LI σ

-- | The trivia the two passes print the rest with: the first pass's, whose
-- comments are the formatter's; the second pass's, which is the final walk's
-- from `k` on (at `k`, what stands before the declaration).
record Hyps (F tvc₁ tvc₂ : Trivia) (k : ℕ) : Set where
  constructor hyps
  field
    h-src   : ∀ j → NotesSrc (lookupNotes j tvc₁)
    h-after : ∀ j → k ≤ j → Notes.after (lookupNotes j tvc₂) ≡ Notes.after (lookupNotes j F)
    h-inner : ∀ j → k < j → Notes.inner (lookupNotes j tvc₂) ≡ Notes.inner (lookupNotes j F)
    h-top   : ∀ j → k < j → Notes.top (lookupNotes j tvc₂) ≡ Notes.top (lookupNotes j F)
    h-k     : Notes.top (up (lookupNotes k tvc₂)) ≡ Notes.top (up (lookupNotes k F))

private
  fresh : ∀ σ → St.pend σ ≡ just 0 → St.ends σ ≡ [] → σ ≡ st (St.out σ) (St.col σ) (just 0) []
  fresh (st o c (just 0) []) refl refl = refl

  sk∸k : ∀ k → suc k ∸ k ≡ 1
  sk∸k k = Data.Nat.Properties.m+n∸n≡m 1 k

  ending-ns : ∀ k tv → topList k (suc k) (hoist k tv) ≡ Notes.top (up (lookupNotes k tv)) ++ []
  ending-ns k tv rewrite sk∸k k = cong (λ n → Notes.top n ++ []) (hoist-at k tv)

  blanks-groups : ∀ B → All (_≡ note-blank) B → groups B [] false ≡ []
  blanks-groups B pB = trans (cong (λ x → groups x [] false) (sym (++-identityʳ B))) (groups-pass2 [] B [] [] pB [])

  nc-nil : ∀ (n : Notes) → Notes.inner n ≡ [] → Notes.top (up n) ≡ Notes.top n
  nc-nil n e = trans (cong (λ i → Notes.top n ++ map note-comment i) e) (++-identityʳ _)

private
  -- nothing, or a blank line, before what follows a declaration
  pre-empty : ∀ σ k T prev → Bnd σ k T prev → EntryT (St.out σ) k [] T
  pre-empty σ .0 .[] nothing (bnd _ _ (eo , refl , refl) _ _ _ _ _) = subst (λ o → EntryT o 0 [] []) (sym eo) entry-start
  pre-empty σ k T (just p) (bnd _ _ ((h , e) , _) _ _ _ _ _) = entry-decl (St.out σ) k h T e

  pre-blank : ∀ σ k T p → Bnd σ k T (just p)
            → EntryT (lnl ∷ St.out σ) k (held-blank ∷ []) T × layout 0 false blank σ ≡ st (lnl ∷ St.out σ) 0 (just 0) []
  pre-blank σ k T p b@(bnd ep ee ((h , e) , (x , xs , eo)) _ _ _ _ _) =
    entry-gap (St.out σ) k h T e ,
    trans (cong (layout 0 false blank) (fresh σ ep ee)) (cong (λ o → Once.Format.Doc.blankLine 0 (st o (St.col σ) (just 0) [])) eo
      |> λ q → trans q (cong (λ o → st (lnl ∷ o) 0 (just 0) []) (sym eo)))
    where
      infixl 0 _|>_
      _|>_ : ∀ {A B : Set} → A → (A → B) → B
      a |> f = f a

  -- the final walk over the runs written from an entry
  runs-fin : ∀ G og k H₀ T → All NE G → EntryT og k H₀ T → ∀ {R Rs} → G ≡ R ∷ Rs → All (_≡ held-blank) H₀
           → fin (Φ (gOut G og)) ≡ settleAt k (H₀ ++ heldOf G) T
  runs-fin G og k H₀ T nes en eG p₀ with runs-walk G og k H₀ T nes (proj₁ en) eG
  ... | r , H , e , q =
    trans (cong fin e)
      (trans (cong (λ hs → settleAt k hs T) (promote-top _ (subst (All TopH) (sym q) (all-++ H₀ _ (blanks-top H₀ p₀) (heldOf-top G)))))
             (cong (λ hs → settleAt k hs T) q))

private
  notes-blank : ∀ hs → All (_≡ held-blank) hs → All (_≡ note-blank) (notesOf hs)
  notes-blank []                 []          = []
  notes-blank (.held-blank ∷ hs) (refl ∷ ps) = refl ∷ notes-blank hs ps

  -- the second pass's notes after the runs the walk held settled: the runs as written
  settled-groups : ∀ k T H₀ G → All NE G → All (_≡ note-blank) (Notes.top (lookupNotes k T)) → All (_≡ held-blank) H₀
                 → (∀ j → k ≤ j → Notes.inner (lookupNotes j T) ≡ [])
                 → groups (Notes.top (up (lookupNotes k (settleAt k (H₀ ++ heldOf G) T))) ++ []) [] false ≡ map rsOf G
  settled-groups k T H₀ G nes pT p₀ inn =
    trans (cong (λ x → groups x [] false)
             (trans (++-identityʳ _)
               (trans (nc-nil (lookupNotes k (settleAt k (H₀ ++ heldOf G) T)) (trans (settle-tops-inner k k (H₀ ++ heldOf G) T (all-++ H₀ _ (blanks-top H₀ p₀) (heldOf-top G))) (inn k ≤-refl)))
                 (trans (settle-tops k (H₀ ++ heldOf G) T (all-++ H₀ _ (blanks-top H₀ p₀) (heldOf-top G)))
                   (trans (cong (Notes.top (lookupNotes k T) ++_) (notesOf-++ H₀ (heldOf G)))
                     (trans (sym (++-assoc (Notes.top (lookupNotes k T)) (notesOf H₀) (notesOf (heldOf G))))
                            (cong (λ hs → (Notes.top (lookupNotes k T) ++ notesOf H₀) ++ notesOf hs) (sym (++-identityʳ (heldOf G))))))))))
      (groups-pass2 G (Notes.top (lookupNotes k T) ++ notesOf H₀) [] nes (all-++ _ _ pT (notes-blank H₀ p₀)) [])

  -- the final walk, when comments stand after the last declaration
  end-F : ∀ prev σ k T ns₁ R Rs → Bnd σ k T prev → groups ns₁ [] false ≡ R ∷ Rs → All NE (R ∷ Rs)
        → ∃[ H₀ ] All (_≡ held-blank) H₀
          × fin (Φ (St.out (brk 0 (layout 0 false (ending prev ns₁) σ)))) ≡ settleAt k (H₀ ++ heldOf (R ∷ Rs)) T
  lay-runs : ∀ ns₁ R Rs og c → groups ns₁ [] false ≡ R ∷ Rs → All NE (R ∷ Rs)
           → layout 0 false (runs ns₁ [] false) (st og c (just 0) []) ≡ st (gOut (R ∷ Rs) og) (Once.Format.Proof.Lockstep.colOf (R ∷ Rs) c) (just 0) []
  lay-runs ns₁ R Rs og c eG nes =
    trans (runs-layout 0 false ns₁ [] false _) (trans (cong (λ G → layoutG 0 false G (st og c (just 0) [])) eG) (layoutG-out false (R ∷ Rs) og c nes))

  end-F nothing σ k T ns₁ R Rs (bnd ep ee (eo , refl , refl) _ _ _ _ _) eG nes =
    [] , [] ,
    trans (cong (λ τ → fin (Φ (St.out (brk 0 τ))))
             (trans (cong (λ b → layout 0 false (if b then empty <> topDoc ns₁ else empty) σ) (trans (has-of ns₁) (cong notNull eG)))
               (trans (cong (layout 0 false (runs ns₁ [] false)) (trans (fresh σ ep ee) (cong (λ o → st o (St.col σ) (just 0) []) eo)))
                      (lay-runs ns₁ R Rs [] (St.col σ) eG nes))))
          (runs-fin (R ∷ Rs) [] 0 [] [] nes entry-start refl [])
  end-F (just p) σ k T ns₁ R Rs b eG nes =
    held-blank ∷ [] , refl ∷ [] ,
    trans (cong (λ τ → fin (Φ (St.out (brk 0 τ))))
             (trans (cong (λ b′ → layout 0 false (if b′ then blank <> topDoc ns₁ else empty) σ) (trans (has-of ns₁) (cong notNull eG)))
               (trans (cong (layout 0 false (runs ns₁ [] false)) (proj₂ (pre-blank σ k T p b)))
                      (lay-runs ns₁ R Rs (lnl ∷ St.out σ) 0 eG nes))))
          (runs-fin (R ∷ Rs) (lnl ∷ St.out σ) k (held-blank ∷ []) T nes (proj₁ (pre-blank σ k T p b)) refl (refl ∷ []))

-- | What stands after the last declaration, formatted twice.
ending-sim : ∀ ωF prev k tvc₁ tvc₂ σ T → Bnd σ k T prev → Hyps (fin ωF) tvc₁ tvc₂ k
           → ωF ≡ Φ (St.out (brk 0 (layout 0 false (ending prev (topList k (suc k) (hoist k tvc₁))) σ)))
           → layout 0 false (ending prev (topList k (suc k) (hoist k tvc₂))) σ ≡ layout 0 false (ending prev (topList k (suc k) (hoist k tvc₁))) σ
ending-sim ωF prev k tvc₁ tvc₂ σ T b hy fe =
  subst (λ τ → layout 0 false (ending prev ns₂) τ ≡ layout 0 false (ending prev ns₁) τ) (sym σ≡)
    (ending-eq prev ns₁ ns₂ (St.out σ) (St.col σ) eq src)
  where
    F = fin ωF
    ns₁ = topList k (suc k) (hoist k tvc₁)
    ns₂ = topList k (suc k) (hoist k tvc₂)
    σ≡ = fresh σ (Bnd.b-pend b) (Bnd.b-ends b)
    src : All NoteSrc ns₁
    src = tops-src (hoist k tvc₁) k (suc k ∸ k) (hoist-src k tvc₁ (Hyps.h-src hy))
    brk-same : ∀ τ → St.pend τ ≡ just 0 → St.ends τ ≡ [] → St.out (brk 0 τ) ≡ St.out τ
    brk-same (st o c (just 0) []) refl refl = refl
    fin-of : ∀ τ → layout 0 false (ending prev ns₁) σ ≡ τ → St.pend τ ≡ just 0 → St.ends τ ≡ [] → F ≡ fin (Φ (St.out τ))
    fin-of τ e ep ee = cong fin (trans fe (cong (λ o → Φ o) (trans (cong (λ v → St.out (brk 0 v)) e) (brk-same τ ep ee))))
    go : ∀ G → groups ns₁ [] false ≡ G → All NE G → groups (Notes.top (up (lookupNotes k F)) ++ []) [] false ≡ map rsOf G
    go [] eG _ = goN prev b refl
      where
        lay : layout 0 false (ending prev ns₁) σ ≡ σ
        lay rewrite trans (has-of ns₁) (cong notNull eG) = refl
        Fσ : F ≡ fin (Φ (St.out σ))
        Fσ = fin-of σ lay (Bnd.b-pend b) (Bnd.b-ends b)
        goN : ∀ p → Bnd σ k T p → prev ≡ p → groups (Notes.top (up (lookupNotes k F)) ++ []) [] false ≡ []
        goN nothing (bnd _ _ (eo , refl , refl) _ _ _ _ _) _ =
          trans (cong (λ x → groups (Notes.top (up (lookupNotes 0 x)) ++ []) [] false) (trans Fσ (cong (λ o → fin (Φ o)) eo))) refl
        goN (just p) (bnd _ _ ((h , e) , _) _ inn _ pT _) _ =
          trans (cong (λ x → groups (Notes.top (up (lookupNotes k x)) ++ []) [] false) (trans Fσ (cong fin e)))
            (blanks-groups _ (subst (All (_≡ note-blank)) (sym (trans (++-identityʳ _) (nc-nil (lookupNotes k T) (inn k ≤-refl)))) pT))
    go (R ∷ Rs) eG nes with end-F prev σ k T ns₁ R Rs b eG nes
    ... | H₀ , p₀ , eF =
      trans (cong (λ x → groups (Notes.top (up (lookupNotes k x)) ++ []) [] false) (trans (cong fin fe) eF))
            (settled-groups k T H₀ (R ∷ Rs) nes (Bnd.b-topk b) p₀ (Bnd.b-inner b))
    eq : groups ns₂ [] false ≡ map rsOf (groups ns₁ [] false)
    eq = trans (cong (λ x → groups x [] false) (trans (ending-ns k tvc₂) (cong (_++ []) (Hyps.h-k hy))))
               (go (groups ns₁ [] false) refl (groups-ne-all ns₁ [] false))

------------------------------------------------------------------------
-- A declaration, formatted twice
------------------------------------------------------------------------

private
  -- nothing, or a blank line, before a declaration
  gap-entry : ∀ prev d σ k T → Bnd σ k T prev
            → ∃[ og ] ∃[ c ] ∃[ H₀ ] layout 0 false (gap prev d) σ ≡ st og c (just 0) [] × EntryT og k H₀ T × All (_≡ held-blank) H₀
  gap-entry nothing d σ k T b =
    St.out σ , St.col σ , [] , fresh σ (Bnd.b-pend b) (Bnd.b-ends b) , pre-empty σ k T nothing b , []
  gap-entry (just p) d σ k T b = pick (together p d) refl
    where
      pick : ∀ t → together p d ≡ t → ∃[ og ] ∃[ c ] ∃[ H₀ ] layout 0 false (if t then empty else blank) σ ≡ st og c (just 0) []
                                              × EntryT og k H₀ T × All (_≡ held-blank) H₀
      pick true  _ = St.out σ , St.col σ , [] , fresh σ (Bnd.b-pend b) (Bnd.b-ends b) , pre-empty σ k T (just p) b , []
      pick false _ = lnl ∷ St.out σ , 0 , held-blank ∷ [] , proj₂ (pre-blank σ k T p b) , proj₁ (pre-blank σ k T p b) , refl ∷ []

  brk01 : ∀ σ → St.out (brk 0 σ) ≡ St.out (brk 1 σ)
  brk01 (st o c (just _) [])      = refl
  brk01 (st o c (just _) (_ ∷ _)) = refl
  brk01 (st o c nothing [])       = refl
  brk01 (st o c nothing (_ ∷ _))  = refl

  brk-st0 : ∀ σ → brk 0 σ ≡ st (St.out (brk 0 σ)) 0 (just 0) []
  brk-st0 (st o c (just _) [])      = refl
  brk-st0 (st o c (just _) (_ ∷ _)) = refl
  brk-st0 (st o c nothing [])       = refl
  brk-st0 (st o c nothing (_ ∷ _))  = refl

  li-brk0 : ∀ σ → LI σ → LI (brk 0 σ)
  li-brk0 σ l = proj₁ (brk-ok 0 σ l)

  reach-to : ∀ σ → LI σ → ∀ d → Reach (Φ (St.out σ)) (Φ (St.out (brk 0 (layout 0 false d σ))))
  reach-to σ l d = reach-trans (proj₂ (layout-reach 0 false d σ l)) (proj₂ (brk-ok 0 _ (proj₁ (layout-reach 0 false d σ l))))

  brk-pend : ∀ i σ → St.pend (brk i σ) ≡ just i
  brk-pend i (st o c (just _) [])      = refl
  brk-pend i (st o c (just _) (_ ∷ _)) = refl
  brk-pend i (st o c nothing [])       = refl
  brk-pend i (st o c nothing (_ ∷ _))  = refl

  ne-out : ∀ o → proj₂ (Φ o) ≡ true → ∃[ x ] ∃[ xs ] o ≡ x ∷ xs
  ne-out []       ()
  ne-out (x ∷ xs) _  = x , xs , refl

  n∸n : ∀ n → n ∸ n ≡ 0
  n∸n zero    = refl
  n∸n (suc n) = n∸n n

  ∸-suc : ∀ {k k′} → k < k′ → k′ ∸ k ≡ suc (k′ ∸ suc k)
  ∸-suc {zero}  {suc k′} _         = refl
  ∸-suc {suc k} {suc k′} (s≤s k<k′) = ∸-suc k<k′

  +∸ : ∀ {k k′} → k < k′ → suc k + (k′ ∸ suc k) ≡ k′
  +∸ {k} {k′} k<k′ = Data.Nat.Properties.m+[n∸m]≡n k<k′

import Once.Format.Proof.Inside as Inside
open import Once.Format.Proof.Skeleton using (module Same)

-- | The rest of the declarations, formatted twice, from where a declaration ends.
Rest : WL → Decl → List Decl → Set
Rest ωF d ds = ∀ k′ tv₁′ tv₂′ σ′ T′ → Bnd σ′ k′ T′ (just d) → Hyps (fin ωF) tv₁′ tv₂′ k′
             → ωF ≡ Φ (St.out (brk 0 (layout 0 false (proj₁ (pdecls (just d) ds tv₁′ k′)) σ′)))
             → layout 0 false (proj₁ (pdecls (just d) ds tv₂′ k′)) σ′ ≡ layout 0 false (proj₁ (pdecls (just d) ds tv₁′ k′)) σ′

-- | A declaration, formatted twice: what stands before it, it, its line end;
-- then the rest.
decl-step : ∀ ωF prev d ds k tvc₁ tvc₂ σ T → Bnd σ k T prev → Hyps (fin ωF) tvc₁ tvc₂ k
          → ωF ≡ Φ (St.out (brk 0 (layout 0 false (proj₁ (pdecls prev (d ∷ ds) tvc₁ k)) σ))) → Rest ωF d ds
          → layout 0 false (proj₁ (pdecls prev (d ∷ ds) tvc₂ k)) σ ≡ layout 0 false (proj₁ (pdecls prev (d ∷ ds) tvc₁ k)) σ
decl-step ωF prev d ds k tvc₁ tvc₂ σ T b hy fe IH = main
  where
    open import Once.Format.Doc using (group; nest; fits; flatWidth; column)
    F = fin ωF
    tv₁′ = hoist k tvc₁
    tv₂′ = hoist k tvc₂
    B₁ = proj₁ (pbody d tv₁′ k)
    B₂ = proj₁ (pbody d tv₂′ k)
    k′ = proj₂ (pbody d tv₁′ k)
    cnt : proj₂ (pbody d tv₂′ k) ≡ k′
    cnt = Same.Ind.cnt (Same.ind-body tv₁′ tv₂′ d) k
    ns₁ = topList k k′ tv₁′
    R₁ = proj₁ (pdecls (just d) ds tv₁′ k′)

    -- what stands before the declaration, in the first pass
    GE = gap-entry prev d σ k T b
    og = proj₁ GE
    c  = proj₁ (proj₂ GE)
    H₀ = proj₁ (proj₂ (proj₂ GE))
    eg = proj₁ (proj₂ (proj₂ (proj₂ GE)))
    en = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ GE))))
    p₀ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ GE))))
    σg = st og c (just 0) []
    lg : LI σg
    lg = subst LI eg (proj₁ (layout-reach 0 false (gap prev d) σ (Bnd.b-li b)))
    LF = lead-facts prev ns₁ og c k H₀ T en p₀
    tb  = proj₁ LF
    ptb = proj₁ (proj₂ LF)
    lfs = proj₂ (proj₂ LF)
    G = groups ns₁ [] false
    H′ = H₀ ++ heldOf G ++ tb
    T′ = settleAt k H′ T
    Tkd = Notes.top (lookupNotes k T′)
    topH′ : All TopH H′
    topH′ = heldG-top H₀ G tb p₀ ptb
    σl = layout 0 false (lead prev ns₁) σg
    ll = proj₁ (layout-reach 0 false (lead prev ns₁) σg lg)
    f′ = fits (column σl) (flatWidth B₁)
    σd = layout 2 f′ B₁ σl
    ld = proj₁ (layout-reach 2 f′ B₁ σl ll)
    σn = brk 0 σd

    whole₁ : layout 0 false (proj₁ (pdecls prev (d ∷ ds) tvc₁ k)) σ ≡ layout 0 false R₁ σn
    whole₁ = cong (λ τ → layout 0 false R₁ (brk 0 (layout 0 false (group (nest 2 B₁)) (layout 0 false (lead prev ns₁) τ)))) eg

    finR : ωF ≡ Φ (St.out (brk 0 (layout 0 false R₁ σn)))
    finR = trans fe (cong (λ τ → Φ (St.out (brk 0 τ))) whole₁)

    futn : Reach (Φ (St.out σn)) ωF
    futn = subst (Reach (Φ (St.out σn))) (sym finR) (reach-to σn (li-brk0 σd ld) R₁)

    futd : Reach (Φ (St.out σd)) ωF
    futd = reach-trans (proj₂ (brk-ok 0 σd ld)) futn

    fut1 : Reach (Φ (St.out (brk 1 σd))) ωF
    fut1 = subst (λ o → Reach (Φ o) ωF) (brk01 σd) futn

    -- the declaration, in step
    module I = Inside tv₁′ tv₂′ ωF k
      (λ j kd≤j → trans (hoist-after j k tvc₂) (Hyps.h-after hy j kd≤j))
      (λ j kd<j → trans (cong Notes.inner (hoist-other j k tvc₂ (λ e → <-irrefl (sym e) kd<j))) (Hyps.h-inner hy j kd<j))
      (cong Notes.inner (hoist-at k tvc₂)) (cong Notes.inner (hoist-at k tvc₁)) (hoist-src k tvc₁ (Hyps.h-src hy)) Tkd

    start : I.Start σl T′
    start = I.start (proj₁ lfs) (proj₁ (proj₂ lfs)) (proj₂ (proj₂ lfs))
      (λ j le → trans (settleAt-after j k H′ T) (Bnd.b-after b j le))
      (λ j le → trans (settle-tops-inner j k H′ T topH′) (Bnd.b-inner b j le))
      (λ j lt′ → trans (cong Notes.top (lookup-settleAt j k H′ T (λ e → <-irrefl (sym e) lt′))) (Bnd.b-top b j lt′))
      refl

    sB = Same.Ind.sk (Same.ind-body tv₁′ tv₂′ d) k
    A = I.start-sim sB (Same.starts-body tv₁′ tv₂′ d k) 2 f′ σl σl T′ (s≤s z≤n)
          (I.rel refl refl refl (proj₁ (proj₂ lfs)) (proj₁ (proj₂ lfs))) start ll futd
    σd₂ = layout 2 f′ B₂ σl

    -- its line end, in step
    kbA = I.After.kb A
    nA  = I.After.n A
    sumA : kbA + nA ≡ k′
    sumA = I.After.sum A
    NB = I.brk-sim 1 σd σd₂ kbA nA (s≤s z≤n) (I.After.kd≤ A) (I.After.rl A) (I.After.wk A) ld fut1
    r′ = proj₁ NB
    w′ = proj₂ NB
    Tend = I.WI.t w′
    h′   = I.WI.h w′
    k≤k′ : k ≤ k′
    k≤k′ = subst (k ≤_) sumA (≤-trans (I.After.kd≤ A) (m≤m+n kbA nA))

    σn≡ : brk 0 σd₂ ≡ σn
    σn≡ = trans (brk-st0 σd₂)
            (trans (cong (λ o → st o 0 (just 0) []) (trans (brk01 σd₂) (trans (sym (I.Rel.r-out r′)) (sym (brk01 σd)))))
                   (sym (brk-st0 σd)))

    Φn : Φ (St.out σn) ≡ (walker k′ h′ line-code [] 0 Tend , true)
    Φn = trans (cong Φ (brk01 σd))
           (cong₂ _,_ (trans (I.WI.w-φ w′) (cong (λ m → walker m h′ line-code [] 0 Tend) (trans (+-identityʳ (kbA + nA)) sumA)))
                      (proj₁ (I.WI.w-end w′ 1 (brk-pend 1 σd))))

    -- the final walk, where it has passed: what it found is what it has
    frz : ∀ j → j < k′ → ti (lookupNotes j F) ≡ ti (lookupNotes j Tend)
    frz j j<k′ =
      trans (cong (λ ω → ti (lookupNotes j (fin ω))) (sym (proj₂ futn)))
        (trans (frozen-ti j (Φ (St.out σn)) (proj₁ futn) (subst (λ v → j < Once.Format.Print.W.k (proj₁ v)) (sym Φn) j<k′))
               (cong (λ ω → ti (Look j (proj₁ ω))) Φn))

    k<of : ∀ {j} → k′ < j → k < j
    k<of k′<j = ≤-trans (s≤s k≤k′) k′<j

    ≢of : ∀ {j} → k′ < j → j ≢ k
    ≢of k′<j e = <-irrefl (sym e) (k<of k′<j)

    -- with no anchor, the declaration's notes before it are blank lines
    nsk : k′ ≡ k → ∀ tv → topList k k′ tv ≡ []
    nsk e tv = cong (λ x → tops tv k (x ∸ k)) e |> λ q → trans q (cong (tops tv k) (n∸n k))
      where
        infixl 0 _|>_
        _|>_ : ∀ {A B : Set} → A → (A → B) → B
        x |> f = f x

    topk′ : All (_≡ note-blank) (Notes.top (lookupNotes k′ Tend))
    topk′ with Data.Nat.Properties.m≤n⇒m<n∨m≡n k≤k′
    ... | inj₁ k<k′ = subst (All (_≡ note-blank)) (sym (I.WI.w-top w′ k′ k<k′)) []
    ... | inj₂ k≡k′ =
      subst (All (_≡ note-blank)) (sym (trans (cong (λ x → Notes.top (lookupNotes x Tend)) (sym k≡k′)) (I.WI.w-topk w′)))
        (subst (λ hs → All (_≡ note-blank) hs) (sym (settle-tops k H′ T topH′))
          (all-++ _ _ (Bnd.b-topk b)
            (notes-blank H′ (subst (λ G′ → All (_≡ held-blank) (H₀ ++ heldOf G′ ++ tb))
                              (sym (cong (λ ns → groups ns [] false) (nsk (sym k≡k′) tv₁′)))
                              (all-++ H₀ _ p₀ ptb)))))

    bnd′ : Bnd σn k′ Tend (just d)
    bnd′ = bnd (cong St.pend (brk-st0 σd)) (cong St.ends (brk-st0 σd)) ((h′ , Φn) , ne-out (St.out σn) (cong proj₂ Φn))
             (λ j le → I.WI.w-after w′ j (subst (_≤ j) (sym sumA) le))
             (λ j le → I.WI.w-inner w′ j (subst (_≤ j) (sym (trans (+-identityʳ _) sumA)) le))
             (λ j k′<j → I.WI.w-top w′ j (k<of k′<j)) topk′ (li-brk0 σd ld)

    hyps′ : Hyps F tv₁′ tv₂′ k′
    hyps′ = hyps (hoist-src k tvc₁ (Hyps.h-src hy))
      (λ j le → trans (hoist-after j k tvc₂) (Hyps.h-after hy j (≤-trans k≤k′ le)))
      (λ j k′<j → trans (cong Notes.inner (hoist-other j k tvc₂ (≢of k′<j))) (Hyps.h-inner hy j (k<of k′<j)))
      (λ j k′<j → trans (cong Notes.top (hoist-other j k tvc₂ (≢of k′<j))) (Hyps.h-top hy j (k<of k′<j)))
      hk′
      where
        hk′ : Notes.top (up (lookupNotes k′ tv₂′)) ≡ Notes.top (up (lookupNotes k′ F))
        hk′ with Data.Nat.Properties.m≤n⇒m<n∨m≡n k≤k′
        ... | inj₂ k≡k′ = subst (λ x → Notes.top (up (lookupNotes x tv₂′)) ≡ Notes.top (up (lookupNotes x F))) k≡k′
                            (trans (cong (λ n → Notes.top (up n)) (hoist-at k tvc₂)) (trans (++-identityʳ _) (Hyps.h-k hy)))
        ... | inj₁ k<k′ =
          trans (cong (λ n → Notes.top (up n)) (hoist-other k′ k tvc₂ (λ e → <-irrefl (sym e) k<k′)))
            (cong₂ (λ t i → t ++ map note-comment i) (Hyps.h-top hy k′ k<k′) (Hyps.h-inner hy k′ k<k′))

    -- what stands before it, in the second pass
    lead₂ : layout 0 false (lead prev (topList k k′ tv₂′)) σg ≡ σl
    lead₂ with Data.Nat.Properties.m≤n⇒m<n∨m≡n k≤k′
    ... | inj₂ k≡k′ = trans (cong (λ ns → layout 0 false (lead prev ns) σg) (nsk (sym k≡k′) tv₂′))
                            (sym (cong (λ ns → layout 0 false (lead prev ns) σg) (nsk (sym k≡k′) tv₁′)))
    ... | inj₁ k<k′ = lead-eq prev ns₁ (topList k k′ tv₂′) og c eqG (tops-src tv₁′ k (k′ ∸ k) (hoist-src k tvc₁ (Hyps.h-src hy)))
      where
        m = k′ ∸ suc k
        top₂k : Notes.top (lookupNotes k tv₂′) ≡ Tkd
        top₂k = trans (cong Notes.top (hoist-at k tvc₂))
                  (trans (Hyps.h-k hy)
                    (trans (cong₂ (λ t i → t ++ map note-comment i) (cong proj₁ (frz k k<k′)) (cong proj₂ (frz k k<k′)))
                      (trans (cong₂ (λ t i → t ++ map note-comment i) (I.WI.w-topk w′) (I.WI.w-innerk w′)) (++-identityʳ Tkd))))
        rest-nil : tops tv₂′ (suc k) m ≡ []
        rest-nil = tops-nil tv₂′ (suc k) m λ i ski i<e →
          trans (cong Notes.top (hoist-other i k tvc₂ (λ e → <-irrefl (sym e) ski)))
            (trans (Hyps.h-top hy i ski)
              (trans (cong proj₁ (frz i (subst (i <_) (+∸ k<k′) i<e))) (I.WI.w-top w′ i ski)))
        ns₂≡ : topList k k′ tv₂′ ≡ Tkd
        ns₂≡ = trans (cong (tops tv₂′ k) (∸-suc k<k′)) (trans (cong₂ _++_ top₂k rest-nil) (++-identityʳ Tkd))
        eqG : groups (topList k k′ tv₂′) [] false ≡ map rsOf G
        eqG = trans (cong (λ ns → groups ns [] false)
                      (trans ns₂≡ (trans (settle-tops k H′ T topH′)
                        (trans (cong (Notes.top (lookupNotes k T) ++_) (notesOf-++ H₀ (heldOf G ++ tb)))
                               (sym (++-assoc (Notes.top (lookupNotes k T)) (notesOf H₀) _))))))
                    (groups-pass2 G (Notes.top (lookupNotes k T) ++ notesOf H₀) tb (groups-ne-all ns₁ [] false)
                       (all-++ _ _ (Bnd.b-topk b) (notes-blank H₀ p₀)) ptb)

    main : layout 0 false (proj₁ (pdecls prev (d ∷ ds) tvc₂ k)) σ ≡ layout 0 false (proj₁ (pdecls prev (d ∷ ds) tvc₁ k)) σ
    main =
      trans (cong (λ τ → layout 0 false (proj₁ (pdecls (just d) ds tv₂′ (proj₂ (pbody d tv₂′ k))))
                           (brk 0 (layout 0 false (group (nest 2 B₂)) (layout 0 false (lead prev (topList k (proj₂ (pbody d tv₂′ k)) tv₂′)) τ)))) eg)
        (trans (cong (λ x → layout 0 false (proj₁ (pdecls (just d) ds tv₂′ x))
                             (brk 0 (layout 0 false (group (nest 2 B₂)) (layout 0 false (lead prev (topList k x tv₂′)) σg)))) cnt)
          (trans (cong (λ τ → layout 0 false (proj₁ (pdecls (just d) ds tv₂′ k′)) (brk 0 (layout 0 false (group (nest 2 B₂)) τ))) lead₂)
            (trans (cong (λ g → layout 0 false (proj₁ (pdecls (just d) ds tv₂′ k′)) (brk 0 (layout 2 (fits (column σl) g) B₂ σl)))
                         (sym (Once.Format.Proof.Skeleton.sk-width sB)))
              (trans (cong (layout 0 false (proj₁ (pdecls (just d) ds tv₂′ k′))) σn≡)
                (trans (IH k′ tv₁′ tv₂′ σn Tend bnd′ hyps′ finR) (sym whole₁))))))
