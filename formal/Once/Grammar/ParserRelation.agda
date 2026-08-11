-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.ParserRelation
--
-- Grammar-side wrapper around `Once.Parser.TypeRelation`: re-exports
-- the primitive parsing relations + shrinks lemmas + tail-stop
-- predicates (defined below the Grammar layer so the parser function
-- itself can reference them), and adds the `toType` function
-- converting a `Concrete g` GType to its internal `Type`.
--
-- Downstream (`RelRoundtrip`, `Roundtrip`) imports from here.
------------------------------------------------------------------------

module Once.Grammar.ParserRelation where

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Quantity; Zero; One; Many; mk-kind; pure; eff)

import Once.Grammar as G
open G using (GType)
open import Once.Grammar.Printer using (Concrete;
                                        c-unit; c-void; c-int; c-float;
                                        c-buffer; c-string; c-prod; c-sum;
                                        c-fun; c-eff)

-- Re-export the parser-layer relations, predicates, and shrinks.
open import Once.Parser.TypeRelation public

-- | Convert a concrete GType to its internal Type.
toType : ∀ {g : GType} → Concrete g → Type
toType c-unit   = Unit
toType c-void   = Void
toType c-int    = Int
toType c-float  = Float
toType c-buffer = Buffer
toType c-string = Str
toType (c-prod cA cB) = toType cA * toType cB
toType (c-sum  cA cB) = toType cA + toType cB
toType (c-fun {q = q} cA cB) = toType cA ⇒[ mk-kind q pure ] toType cB
toType (c-eff  cA cB) = toType cA ⇒[ mk-kind Many eff ] toType cB
