-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Meaning — formatting keeps what a source means (plan
-- 0.124 step 4.4, at the apex's notion of meaning).
--
-- A source denotes a typed program (`Spec.Source._⊢_`) through its program
-- text's parse. Formatting that text gives a text with the same parse
-- (`RoundTrip.roundtrip`), so the formatted source denotes the same typed
-- program: the same module, signature and program, hence the same behaviour
-- and the same admissibility for every target. `once fmt` stays out of the
-- compiler's path; this is what it owes the apex.
------------------------------------------------------------------------

module Once.Format.Proof.Meaning where

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Source using (Source; Typed; _⊢_)
open import Once.Parser using (parseStrict)
open import Once.Adequacy.FrontEndBridge using (parseStrict-sound; parseStrict-complete)
open import Once.Adequacy.SpecGrammar.Decl using (parses→; parses←)
open import Once.Format using (formatSource)
open import Once.Format.Proof.LexOK using (DigitBound)
open import Once.Format.Proof.RoundTrip using (roundtrip)

-- | A source's program text, formatted, denotes what the source denotes.
format-denotes : DigitBound → ∀ src tp → src ⊢ tp
               → ∃[ out ] (formatSource (Source.text src) ≡ inj₂ out × record src { text = out } ⊢ tp)
format-denotes bound src tp (mm , p , pms , d) =
  rest (roundtrip bound (Source.text src) (Typed.module′ tp)
          (parseStrict-complete (Source.text src) (Typed.module′ tp) (parses← {Source.text src} p)))
  where
    rest : ∃[ out ] (formatSource (Source.text src) ≡ inj₂ out × parseStrict out ≡ inj₂ (Typed.module′ tp))
         → ∃[ out ] (formatSource (Source.text src) ≡ inj₂ out × record src { text = out } ⊢ tp)
    rest (out , eq , ps) = out , eq , (mm , parses→ {out} (parseStrict-sound out (Typed.module′ tp) ps) , pms , d)
