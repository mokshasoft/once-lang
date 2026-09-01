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
open import Relation.Binary.PropositionalEquality using (_≢_)

record CanonicalName : Set where
  constructor canonical
  field parts : List String

open CanonicalName public

-- A bare/single-component identity (local def, builtin, compiler-generated
-- block). Qualified refs build `canonical (path ++ [name])` at resolution.
bare : String → CanonicalName
bare s = canonical (s ∷ [])

-- D136: THE GENERATOR NAMESPACE. The twelve categorical generators are
-- identified by a canonical name the COMPILER owns, not by a reserved bare
-- string — so a user's `fst` (`User.Module.fst`) and the generator
-- (`Generators.fst`) are different names and cannot collide. D001 reserved the
-- bare names instead; that was never enforced at the parser and produced a
-- collision in which the builtin silently won.
--
-- Here rather than in `Classify` because BOTH sides need it: the resolver
-- (`Once.Parser.Module.Resolve`, which emits it) and the elaborator
-- (`Once.TypeCheck.*`, which dispatches on it) — and this module is already
-- below both.
generatorNS : String
generatorNS = "Generators"

-- | The canonical name of generator `g`. A PATTERN SYNONYM, not a function,
-- because it has to work on BOTH sides: the judgment names it in rule indices
-- (types) and the elaborator matches on it in left-hand sides. A function
-- would be rejected in a pattern. The namespace is spelled literally here for
-- the same reason — `generatorNS` is a definition, and a pattern synonym may
-- only mention constructors and literals.
pattern gen g = canonical ("Generators" ∷ g ∷ [])

-- A user path can never BE a generator name: `bare x = canonical [x]` has one
-- component and `gen g` has two, so the two families are disjoint by length —
-- which is the property that replaces every "this name is not a builtin" side
-- condition once the migration lands.
gen≢bare : ∀ (g x : String) → gen g ≢ bare x
gen≢bare g x ()

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
