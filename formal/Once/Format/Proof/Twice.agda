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
