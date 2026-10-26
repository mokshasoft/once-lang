-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Tokens — the comments the printer adds are no tokens
-- (plan 0.124 step 4.2).
--
-- An anchor is its token, whatever comments stand around it; so is a word.
------------------------------------------------------------------------

module Once.Format.Proof.Tokens where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Data.String using (String; _==_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.Spec.Surface.Lexing using (Token; TWord)
open import Once.Format.Doc using (toks)
open import Once.Format.Comment using (commentLines; commentRun; commentLinesDoc; classify; prose; verbatim)
open import Once.Format.Print using (Trivia; Notes; lookupNotes; inners; eols; anchor; word)

private
  lines-toks : ∀ cs r → toks (commentLinesDoc cs) r ≡ r
  lines-toks []       r = refl
  lines-toks (c ∷ cs) r with classify c
  ... | prose ws   = lines-toks cs r
  ... | verbatim v = lines-toks cs r

  inners-toks : ∀ cs r → toks (inners cs) r ≡ r
  inners-toks []       r = refl
  inners-toks (c ∷ cs) r = lines-toks (concatMap commentLines (c ∷ cs)) r

  eols-toks : ∀ cs r → toks (eols cs) r ≡ r
  eols-toks []       r = refl
  eols-toks (c ∷ cs) r = eols-toks cs r

-- | An anchor is its token.
anchor-toks : ∀ x tv k r → toks (proj₁ (anchor x tv k)) r ≡ x ∷ r
anchor-toks x tv k r =
  trans (inners-toks (Notes.inner (lookupNotes k tv)) (x ∷ toks (eols (Notes.after (lookupNotes k tv))) r))
    (Relation.Binary.PropositionalEquality.cong (x ∷_) (eols-toks (Notes.after (lookupNotes k tv)) r))

-- | A word is its token.
word-toks : ∀ s tv k r → toks (proj₁ (word s tv k)) r ≡ TWord s ∷ r
word-toks s tv k r with s == "compose"
... | true  = refl
... | false = anchor-toks (TWord s) tv k r
