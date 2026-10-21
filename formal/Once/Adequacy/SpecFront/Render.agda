-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Render — `showCanonical` renders word names apart
-- (plan 0.121 R13, D329).
--
-- The compiler keys a generator by its rendered name, the Spec by its
-- canonical name. Rendering puts `.` between the parts, and a word has none,
-- so two word names that render alike are the same name. The String facts
-- are the tool hypotheses T1, T2 (`Once.Postulates`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Render where

open import Data.Bool using (true; T; _∧_)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (∷-injective)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; toList)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.String.Properties using (primStringToListInjective)

open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Internal.Name using (showCanonical; noDotB; wordCharsB; wordB; wordsB; WordName)
open import Once.Postulates using (toList-++)

private
  ∧-l : ∀ a b → T (a ∧ b) → T a
  ∧-l true _ t = tt

  ∧-r : ∀ a b → T (a ∧ b) → T b
  ∧-r true _ t = t

  -- the parts of a word name, and the characters of a word
  head-w : ∀ x xs → T (wordsB (x ∷ xs)) → T (wordB x)
  head-w x xs = ∧-l (wordB x) (wordsB xs)

  tail-w : ∀ x xs → T (wordsB (x ∷ xs)) → T (wordsB xs)
  tail-w x xs = ∧-r (wordB x) (wordsB xs)

  tail-nd : ∀ c cs → T (noDotB (c ∷ cs)) → T (noDotB cs)
  tail-nd c cs = ∧-r _ (noDotB cs)

  toList-inj : ∀ {s t : String} → toList s ≡ toList t → s ≡ t
  toList-inj {s} {t} = primStringToListInjective s t

  -- A list without `.` is no list with one.
  no-dot : ∀ (a b r : List Char) → T (noDotB a) → a ≡ b ++ '.' ∷ r → ⊥
  no-dot []      []      r nd ()
  no-dot []      (_ ∷ _) r nd ()
  no-dot (c ∷ a) []      r nd refl = nd
  no-dot (c ∷ a) (_ ∷ b) r nd refl = no-dot a b r (tail-nd c a nd) refl

  -- The first `.` splits both sides alike.
  split : ∀ (a b r s : List Char) → T (noDotB a) → T (noDotB b)
        → a ++ '.' ∷ r ≡ b ++ '.' ∷ s → a ≡ b × r ≡ s
  split []      []      r s _  _  refl = refl , refl
  split []      (c ∷ b) r s _  nb e    = ⊥-elim (subst (λ x → T (noDotB (x ∷ b))) (sym (proj₁ (∷-injective e))) nb)
  split (c ∷ a) []      r s na _  e    = ⊥-elim (subst (λ x → T (noDotB (x ∷ a))) (proj₁ (∷-injective e)) na)
  split (c ∷ a) (d ∷ b) r s na nb e    =
    let (h , t) = ∷-injective e
        (ab , rs) = split a b r s (tail-nd c a na) (tail-nd d b nb) t
    in cong₂′ h ab , rs
    where
      cong₂′ : ∀ {x y : Char} {xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
      cong₂′ refl refl = refl

  word-nodot : ∀ (x : String) → T (wordB x) → T (noDotB (toList x))
  word-nodot x w = go (toList x) w
    where
      go : ∀ cs → T (wordCharsB cs) → T (noDotB cs)
      go []       ()
      go (c ∷ cs) w = w

  word-nonempty : ∀ (x : String) → T (wordB x) → toList x ≡ [] → ⊥
  word-nonempty x w e = go (toList x) w e
    where
      go : ∀ cs → T (wordCharsB cs) → cs ≡ [] → ⊥
      go []       () _
      go (c ∷ cs) w  ()

  -- A name of two or more parts renders as its first part, `.`, the rest.
  render-cons : ∀ (x y : String) (ys : List String)
              → toList (showCanonical (canonical (x ∷ y ∷ ys)))
                ≡ toList x ++ '.' ∷ toList (showCanonical (canonical (y ∷ ys)))
  render-cons x y ys =
    trans (toList-++ x _) (cong (toList x ++_) (toList-++ "." (showCanonical (canonical (y ∷ ys)))))

  -- A nonempty word name renders nonempty.
  render-nonempty : ∀ (y : String) (ys : List String) → T (wordsB (y ∷ ys))
                  → toList (showCanonical (canonical (y ∷ ys))) ≡ [] → ⊥
  render-nonempty y []       w e = word-nonempty y (head-w y [] w) e
  render-nonempty y (z ∷ zs) w e = go (toList y) (trans (sym (render-cons y z zs)) e)
    where
      go : ∀ cs {r} → cs ++ '.' ∷ r ≡ [] → ⊥
      go []      ()
      go (_ ∷ _) ()

-- Two word names that render alike are the same name.
render-inj : ∀ (c d : CanonicalName) → WordName c → WordName d → showCanonical c ≡ showCanonical d → c ≡ d
render-inj (canonical [])            (canonical [])            _  _  _ = refl
render-inj (canonical [])            (canonical (y ∷ ys))      _  wd e = ⊥-elim (render-nonempty y ys wd (sym (cong toList e)))
render-inj (canonical (x ∷ xs))      (canonical [])            wc _  e = ⊥-elim (render-nonempty x xs wc (cong toList e))
render-inj (canonical (x ∷ []))      (canonical (y ∷ []))      _  _  e = cong (λ z → canonical (z ∷ [])) e
render-inj (canonical (x ∷ []))      (canonical (y ∷ z ∷ zs))  wc _  e =
  ⊥-elim (no-dot (toList x) (toList y) _ (word-nodot x (head-w x [] wc)) (trans (cong toList e) (render-cons y z zs)))
render-inj (canonical (x ∷ y ∷ ys))  (canonical (z ∷ []))      _  wd e =
  ⊥-elim (no-dot (toList z) (toList x) _ (word-nodot z (head-w z [] wd)) (trans (sym (cong toList e)) (render-cons x y ys)))
render-inj (canonical (x ∷ y ∷ ys))  (canonical (x′ ∷ y′ ∷ ys′)) wc wd e =
  let (hx , rest) = split (toList x) (toList x′) _ _ (word-nodot x (head-w x (y ∷ ys) wc)) (word-nodot x′ (head-w x′ (y′ ∷ ys′) wd))
                          (trans (sym (render-cons x y ys)) (trans (cong toList e) (render-cons x′ y′ ys′)))
      tl = render-inj (canonical (y ∷ ys)) (canonical (y′ ∷ ys′)) (tail-w x (y ∷ ys) wc) (tail-w x′ (y′ ∷ ys′) wd) (toList-inj rest)
  in cong₂ (toList-inj hx) tl
  where
    cong₂ : ∀ {a b : String} {as bs} → a ≡ b → canonical as ≡ canonical bs → canonical (a ∷ as) ≡ canonical (b ∷ bs)
    cong₂ refl refl = refl
