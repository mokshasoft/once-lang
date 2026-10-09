-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.LabelSymbols — plan 0.107 §8 step 4: WHAT A DEFINED LABEL'S
-- SYMBOL DETERMINES.
--
-- An image defines two kinds of label: COUNTER labels (`c-label`, closure-body
-- entries), minted from the label counter, and FUNCTION entries. A counter
-- label's symbol ends in `_<index>` — the decimal after the LAST `_`, which
-- digits never contain — so equal symbols mean equal indices, whatever the
-- owner and path. Counter symbols start with `.`, function symbols with `o`
-- (`once_`), so the kinds never meet. `key` is that reading: a counter label
-- by its index, a function entry by its symbol.
------------------------------------------------------------------------

module Once.Adequacy.LabelSymbols where

open import Data.Bool using (true)
open import Data.Char using (Char; isDigit)
open import Data.Char.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; reverse)
import Data.List
import Once.CanonicalName
open import Data.List.Properties using (++-assoc; reverse-++; unfold-reverse; reverse-involutive)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show.Properties using (charsInBase-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.String.Unsafe using (toList-++)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Label using (Label; once; callee; sigop; LabelId; e-thunk; e-fn; labelSym; showLabelId; showPath; module LabelId)
open LabelId using (idx; owner; path)
open import Once.Target.Symbol using (showNat; once-symbol-path; once-prefix; join-us; mangle-component)
open import Once.Target.SymbolInjective using (toList-showNat; charsInBase-all-digits)

------------------------------------------------------------------------
-- The key
------------------------------------------------------------------------

key : Label → ℕ ⊎ String
key (once n)             = inj₁ (idx n)
key (callee (e-thunk n)) = inj₁ (idx n)
key (callee (e-fn f))    = inj₂ (once-symbol-path f)
key (sigop s k)          = inj₂ (labelSym (sigop s k))

-- the labels an image DEFINES
data DefL : Label → Set where
  d-once   : ∀ {n} → DefL (once n)
  d-callee : ∀ {e} → DefL (callee e)

------------------------------------------------------------------------
-- The decimal after the last `_`
------------------------------------------------------------------------

-- the longest prefix free of `_`
tw     : List Char → List Char
tw-dec : (c : Char) → List Char → Dec (c ≡ '_') → List Char
tw []       = []
tw (c ∷ cs) = tw-dec c cs (c ≟ '_')
tw-dec c cs (yes _) = []
tw-dec c cs (no _)  = c ∷ tw cs

last-seg : List Char → List Char
last-seg cs = reverse (tw (reverse cs))

private
  reverse⁺ : ∀ {P : Char → Set} {xs : List Char} → All P xs → All P (reverse xs)
  reverse⁺ []                = []
  reverse⁺ {xs = x ∷ xs} (p ∷ ps) = subst (All _) (sym (unfold-reverse x xs)) (All-++⁺ (reverse⁺ ps) (p ∷ []))

  tw-split : ∀ (ys zs : List Char) → All (_≢ '_') ys → tw (ys ++ ('_' ∷ zs)) ≡ ys
  tw-split []       zs []       = refl
  tw-split (y ∷ ys) zs (p ∷ ps) = go (y ≟ '_')
    where
      go : (d : Dec (y ≡ '_')) → tw-dec y (ys ++ ('_' ∷ zs)) d ≡ y ∷ ys
      go (yes q) = ⊥-elim (p q)
      go (no _)  = cong (y ∷_) (tw-split ys zs ps)

last-seg-split : ∀ (xs ds : List Char) → All (_≢ '_') ds → last-seg (xs ++ ('_' ∷ ds)) ≡ ds
last-seg-split xs ds nd =
  trans (cong (λ z → reverse (tw z)) r≡)
        (trans (cong reverse (tw-split (reverse ds) (reverse xs) (reverse⁺ nd))) (reverse-involutive ds))
  where
    r≡ : reverse (xs ++ ('_' ∷ ds)) ≡ reverse ds ++ ('_' ∷ reverse xs)
    r≡ = trans (reverse-++ xs ('_' ∷ ds))
           (trans (cong (_++ reverse xs) (unfold-reverse '_' ds))
                  (++-assoc (reverse ds) ('_' ∷ []) (reverse xs)))

private
  digit≢_ : ∀ {c : Char} → isDigit c ≡ true → c ≢ '_'
  digit≢_ d refl = case d of λ ()
    where open import Function using (case_of_)

  digits-free : ∀ (n : ℕ) → All (_≢ '_') (toList (showNat n))
  digits-free n = subst (All (_≢ '_')) (sym (toList-showNat n)) (All-map digit≢_ (charsInBase-all-digits n))

-- a label id's rendering ends in `_<index>`
private
  lid-shape : ∀ (pre : String) (n : LabelId)
            → toList (pre ++ˢ showLabelId n)
              ≡ (toList pre ++ (toList (once-symbol-path (owner n)) ++ toList (showPath (path n)))) ++ ('_' ∷ toList (showNat (idx n)))
  lid-shape pre n =
    trans (toList-++ pre _)
      (trans (cong (toList pre ++_)
               (trans (toList-++ (once-symbol-path (owner n)) _)
                 (cong (toList (once-symbol-path (owner n)) ++_)
                   (trans (toList-++ (showPath (path n)) _) (cong (toList (showPath (path n)) ++_) (toList-++ "_" (showNat (idx n))))))))
        (trans (cong (toList pre ++_) (sym (++-assoc (toList (once-symbol-path (owner n))) (toList (showPath (path n))) _)))
               (sym (++-assoc (toList pre) _ _))))

idx-of-once : ∀ (n : LabelId) → last-seg (toList (labelSym (once n))) ≡ toList (showNat (idx n))
idx-of-once n = trans (cong last-seg (lid-shape ".Lonce_" n))
  (last-seg-split (toList ".Lonce_" ++ (toList (once-symbol-path (owner n)) ++ toList (showPath (path n)))) _ (digits-free (idx n)))

idx-of-thunk : ∀ (n : LabelId) → last-seg (toList (labelSym (callee (e-thunk n)))) ≡ toList (showNat (idx n))
idx-of-thunk n = trans (cong last-seg (lid-shape ".L_thunk_" n))
  (last-seg-split (toList ".L_thunk_" ++ (toList (once-symbol-path (owner n)) ++ toList (showPath (path n)))) _ (digits-free (idx n)))

private
  showNat-inj : ∀ {i j : ℕ} → toList (showNat i) ≡ toList (showNat j) → i ≡ j
  showNat-inj {i} {j} eq = charsInBase-injective 10 i j (trans (sym (toList-showNat i)) (trans eq (toList-showNat j)))

------------------------------------------------------------------------
-- First characters
------------------------------------------------------------------------

private
  head-of : List Char → Char
  head-of []      = ' '
  head-of (c ∷ _) = c

  once-head : ∀ (n : LabelId) → head-of (toList (labelSym (once n))) ≡ '.'
  once-head n = cong head-of (toList-++ ".Lonce_" (showLabelId n))

  thunk-head : ∀ (n : LabelId) → head-of (toList (labelSym (callee (e-thunk n)))) ≡ '.'
  thunk-head n = cong head-of (toList-++ ".L_thunk_" (showLabelId n))

  fn-head : ∀ (f : CanonicalName) → head-of (toList (once-symbol-path f)) ≡ 'o'
  fn-head f = cong head-of (toList-++ once-prefix (join-us (Data.List.map mangle-component (Once.CanonicalName.CanonicalName.parts f))))

  -- a counter symbol is no function symbol
  cnt≢fn : ∀ {s : String} (f : CanonicalName) → head-of (toList s) ≡ '.' → s ≢ once-symbol-path f
  cnt≢fn f h eq with trans (sym h) (trans (cong (λ z → head-of (toList z)) eq) (fn-head f))
  ... | ()

------------------------------------------------------------------------
-- THE READING: equal symbols, equal keys (for defined labels).
------------------------------------------------------------------------

sym-key : ∀ {x y : Label} → DefL x → DefL y → labelSym x ≡ labelSym y → key x ≡ key y
sym-key {once n} {once m} d-once d-once eq =
  cong inj₁ (showNat-inj (trans (sym (idx-of-once n)) (trans (cong (λ z → last-seg (toList z)) eq) (idx-of-once m))))
sym-key {once n} {callee (e-thunk m)} d-once d-callee eq =
  cong inj₁ (showNat-inj (trans (sym (idx-of-once n)) (trans (cong (λ z → last-seg (toList z)) eq) (idx-of-thunk m))))
sym-key {once n} {callee (e-fn f)} d-once d-callee eq = ⊥-elim (cnt≢fn f (once-head n) eq)
sym-key {callee (e-thunk n)} {once m} d-callee d-once eq =
  cong inj₁ (showNat-inj (trans (sym (idx-of-thunk n)) (trans (cong (λ z → last-seg (toList z)) eq) (idx-of-once m))))
sym-key {callee (e-thunk n)} {callee (e-thunk m)} d-callee d-callee eq =
  cong inj₁ (showNat-inj (trans (sym (idx-of-thunk n)) (trans (cong (λ z → last-seg (toList z)) eq) (idx-of-thunk m))))
sym-key {callee (e-thunk n)} {callee (e-fn f)} d-callee d-callee eq = ⊥-elim (cnt≢fn f (thunk-head n) eq)
sym-key {callee (e-fn f)} {once m} d-callee d-once eq = ⊥-elim (cnt≢fn f (once-head m) (sym eq))
sym-key {callee (e-fn f)} {callee (e-thunk m)} d-callee d-callee eq = ⊥-elim (cnt≢fn f (thunk-head m) (sym eq))
sym-key {callee (e-fn f)} {callee (e-fn g)} d-callee d-callee eq = cong inj₂ eq

-- …so distinct keys give distinct symbols.
keys→syms : ∀ {xs : List Label} → All DefL xs → AllPairs (λ x y → key x ≢ key y) xs
          → AllPairs (λ x y → labelSym x ≢ labelSym y) xs
keys→syms []       []         = []
keys→syms (d ∷ ds) (px ∷ pxs) = go d ds px ∷ keys→syms ds pxs
  where
    go : ∀ {x ys} → DefL x → All DefL ys → All (λ y → key x ≢ key y) ys → All (λ y → labelSym x ≢ labelSym y) ys
    go dx []         []         = []
    go dx (dy ∷ dys) (p ∷ ps) = (λ eq → p (sym-key dx dy eq)) ∷ go dx dys ps
