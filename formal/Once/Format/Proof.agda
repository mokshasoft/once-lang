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
--
-- `roundtrip` and `format-denotes` take `DigitBound`: the primitive `isDigit`
-- accepts the decimal digits only (a fact about the tool that Agda's
-- conversion cannot see; a float's fraction is read back from it).
------------------------------------------------------------------------

module Once.Format.Proof where

open import Once.Format.Proof.RoundTrip using (roundtrip; format-parses)
open import Once.Format.Proof.Meaning using (format-denotes)
open import Once.Format.Proof.Canon using (format-canonical)
