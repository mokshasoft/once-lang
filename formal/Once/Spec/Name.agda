{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Name — the resolved identity of a definition.
--
-- A `CanonicalName` is a definition's module path followed by its name:
-- `canonical (Cars ∷ All ∷ foo ∷ [])` is `foo` in module `Cars.All`, and a
-- definition of the program's own module is a single component (`own`).
--
-- A generator (`id`, `fst`, `inl`, …) is not a canonical name: it resolves to
-- the generator itself, so no name can be one. The words that name a
-- generator are reserved (`Spec.Surface.Generators.GenWord`); a definition
-- with one of these names is reached as `name@this`.
------------------------------------------------------------------------

module Once.Spec.Name where

open import Data.List using (List; []; _∷_)
open import Data.String using (String)

record CanonicalName : Set where
  constructor canonical
  field parts : List String

-- A one-component name.
bare : String → CanonicalName
bare s = canonical (s ∷ [])

-- A definition of the program's own module.
pattern own x = canonical (x ∷ [])
