-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof — the theorems of `once fmt` (plan 0.124 step 4).
--
--   roundtrip         when the compiler's parser reads a text as a module,
--                     the formatted text is read as the same module
--                     (Proof.RoundTrip; through Lexing, Layout, Module, Types,
--                     Expr, Decl, Printable, WF, LexOK).
--   format-denotes    a source with its program text formatted denotes the
--                     same typed program (Spec.Source._⊢_): the apex's
--                     meaning is kept (Proof.Meaning).
--   format-canonical  two texts without comments that parse as the same
--                     module are formatted alike (Proof.Canon).
--   idempotent        formatting the output gives the output, whatever the
--                     comments (Proof.Twice; through Skeleton, Walk, Lockstep,
--                     Inside, Groups, Rerender, Sources, Items, ItemsLex).
--
-- `roundtrip`, `format-denotes` and `idempotent` take `DigitBound`: the primitive `isDigit`
-- accepts the decimal digits only (a fact about the tool that Agda's
-- conversion cannot see; a float's fraction is read back from it).
------------------------------------------------------------------------

module Once.Format.Proof where

open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; ∃-syntax)
open import Data.String using (String; toList)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Source using (Source; _⊢_)
open import Once.Parser using (parseStrict)
open import Once.Format using (formatSource)
open import Once.Format.Lex using (lexItems)
open import Once.Format.Print using (format)
open import Once.Format.Proof.LexOK using (DigitBound)
open import Once.Format.Proof.RoundTrip using (roundtrip)
open import Once.Format.Proof.Meaning using (format-denotes)
open import Once.Format.Proof.Canon using (NoComment; format-canonical)
import Once.Format.Proof.Twice as Twice

-- | What `once fmt` is proved to do (a field of the apex, `Once.Certified`).
record VerifiedFormatter : Set₁ where
  field
    keeps-module   : DigitBound → ∀ text m → parseStrict text ≡ inj₂ m
                   → ∃[ out ] (formatSource text ≡ inj₂ out × parseStrict out ≡ inj₂ m)
    keeps-meaning  : DigitBound → ∀ src tp → src ⊢ tp
                   → ∃[ out ] (formatSource (Source.text src) ≡ inj₂ out × record src { text = out } ⊢ tp)
    canonical      : ∀ t₁ t₂ m → parseStrict t₁ ≡ inj₂ m → parseStrict t₂ ≡ inj₂ m
                   → All NoComment (lexItems (toList t₁)) → All NoComment (lexItems (toList t₂))
                   → formatSource t₁ ≡ formatSource t₂
    idempotent     : DigitBound → ∀ text m → parseStrict text ≡ inj₂ m
                   → formatSource text ≡ inj₂ (format m (lexItems (toList text)))
                     × formatSource (format m (lexItems (toList text))) ≡ inj₂ (format m (lexItems (toList text)))

verifiedFormatter : VerifiedFormatter
verifiedFormatter = record
  { keeps-module    = roundtrip
  ; keeps-meaning   = format-denotes
  ; canonical       = format-canonical
  ; idempotent      = Twice.idempotent
  }
