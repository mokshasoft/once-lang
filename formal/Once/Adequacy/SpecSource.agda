-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecSource — the compiler's reading of a Spec source (plan
-- 0.119 D6): each module text parsed by the compiler's parser, at its path
-- (`parseModules`), and the source the compiler compiles (`toSource`).
------------------------------------------------------------------------

module Once.Adequacy.SpecSource where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)

open import Once.Parser using (parseStrict)
open import Once.Parser.Module.Resolve using (ModuleMap)
open import Once.Denotation.Behavior using (mkSource)
import Once.Denotation.Behavior as B
import Once.Spec.Source as SP

-- Each module text, parsed by the compiler's parser, at its path.
parseModules : List (List String × String) → Maybe ModuleMap
parseModules []                = just []
parseModules ((p , txt) ∷ ms) with parseStrict txt
... | inj₁ _ = nothing
... | inj₂ m = parseModules ms >>= λ mm → just ((p , m) ∷ mm)

toSource : SP.Source → Maybe B.Source
toSource src = parseModules (SP.Source.modules src) >>= λ mm → just (mkSource mm (SP.Source.text src))
