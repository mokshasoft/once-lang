-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CanonicalName — the resolved identity of a definition.
--
-- Plan 0.50. At the module level there is no SigOp/function distinction:
-- every definition is just a function, identified by its RESOLVED module
-- path. A `CanonicalName` is that identity as a component list `[path…,
-- name]` — `canonical (Cars ∷ All ∷ foo ∷ [])` for `foo` in module
-- `Cars.All`, `canonical (foo ∷ [])` for a bare/local/builtin name.
--
-- It is the ONE name carried end-to-end (parse-resolution → typing →
-- realize → SigOpInfo → trace → assembly symbol), so the spec/impl name
-- agreement holds BY CONSTRUCTION rather than by two String computations
-- coinciding. The only way to build one is via resolution (`canonical`
-- from a resolved path), so an unresolved alias can't masquerade as
-- canonical. Mangling to an assembly symbol lives in `Once.Target.Symbol`
-- (`once-symbol-path`); this module is the neutral type + equality, so the
-- typing judgment never depends on codegen.
------------------------------------------------------------------------

module Once.CanonicalName where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.String using (String) renaming (_≟_ to _≟ˢ_; _++_ to _++ˢ_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)

record CanonicalName : Set where
  constructor canonical
  field parts : List String

open CanonicalName public

-- A bare/single-component identity (local def, builtin, compiler-generated
-- block). Qualified refs build `canonical (path ++ [name])` at resolution.
bare : String → CanonicalName
bare s = canonical (s ∷ [])

-- Decidable equality — the trace's `ev-name` comparison needs it.
_≟ᶜ_ : DecidableEquality CanonicalName
canonical ps ≟ᶜ canonical qs with ≡-dec _≟ˢ_ ps qs
... | yes p = yes (cong canonical p)
... | no ¬p = no λ where refl → ¬p refl

-- Human-readable rendering (errors / debugging) — the dotted form. NOT the
-- assembly symbol (that is `once-symbol-path`, clash-free + asm-safe).
showCanonical : CanonicalName → String
showCanonical (canonical [])        = ""
showCanonical (canonical (x ∷ []))  = x
showCanonical (canonical (x ∷ xs))  = x ++ˢ "." ++ˢ showCanonical (canonical xs)
