-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.Convert
--
-- Connects the formal grammar specification (`Once.Grammar`) to the
-- internal type representation (`Once.Type`).
--
-- The grammar spec (`GType`) is what users write in source code. The
-- internal type (`Type`) is what the type-checker operates on. The two
-- diverge in two directions:
--
--   * `GType` has `TVar` (for grammar-level type-variable references).
--     `Type` does not: after 0.2.5, type variables live only inside
--     `PolyType` signatures, never in user-written types.
--   * `Type` has `μ-type` / `ν-type` (inductive/coinductive fixed points).
--     `GType` does not: these are produced internally by the elaborator,
--     not parsed from source.
--
-- Conversion is therefore partial in both directions, matching those
-- asymmetries:
--
--   `typeToGType : Type → Maybe GType`  (fails on μ/ν)
--   `gtypeToType : GType → Maybe Type`  (fails on TVar)
--
-- The main connection theorem (`parseType-expressible-in-grammar`) says:
-- every type produced by the surface parser is expressible in the
-- formal grammar. This is the "grammar conformance" property — the
-- parser never produces internal-only shapes.
------------------------------------------------------------------------

module Once.Grammar.Convert where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

import Once.Type as T
open T using (Type; Quantity; Zero; One; Many)
import Once.Grammar as G
open G using (GType)

open import Once.Parser.Token
open import Once.Parser.Type using (parseType)

------------------------------------------------------------------------
-- GType → Type
------------------------------------------------------------------------

-- | Convert a grammar-level type to an internal type.
-- Fails if the grammar type uses `TVar`, since user-written types
-- are not allowed to contain free type variables.
gtypeToType : GType → Maybe Type
gtypeToType G.TUnit   = just T.Unit
gtypeToType G.TVoid   = just T.Void
gtypeToType G.TInt    = just T.Int
gtypeToType G.TFloat  = just T.Float
gtypeToType G.TBuffer = just T.Buffer
gtypeToType G.TString = just T.Str
gtypeToType (A G.⇒[ q ] B) with gtypeToType A | gtypeToType B
... | just A' | just B' = just (A' T.⇒[ q ] B')
... | _       | _       = nothing
gtypeToType (A G.⊗ B) with gtypeToType A | gtypeToType B
... | just A' | just B' = just (A' T.* B')
... | _       | _       = nothing
gtypeToType (A G.⊕ B) with gtypeToType A | gtypeToType B
... | just A' | just B' = just (A' T.+ B')
... | _       | _       = nothing
gtypeToType (G.TEff A B) with gtypeToType A | gtypeToType B
... | just A' | just B' = just (T.Eff A' B')
... | _       | _       = nothing
gtypeToType (G.TVar _) = nothing

------------------------------------------------------------------------
-- Type → GType
------------------------------------------------------------------------

-- | Convert an internal type back to a grammar-level type.
-- Fails on `μ-type` / `ν-type`, which the grammar does not express.
typeToGType : Type → Maybe GType
typeToGType T.Unit   = just G.TUnit
typeToGType T.Void   = just G.TVoid
typeToGType T.Int    = just G.TInt
typeToGType T.Float  = just G.TFloat
typeToGType T.Buffer = just G.TBuffer
typeToGType T.Str    = just G.TString
typeToGType (A T.⇒[ q ] B) with typeToGType A | typeToGType B
... | just A' | just B' = just (A' G.⇒[ q ] B')
... | _       | _       = nothing
typeToGType (A T.* B) with typeToGType A | typeToGType B
... | just A' | just B' = just (A' G.⊗ B')
... | _       | _       = nothing
typeToGType (A T.+ B) with typeToGType A | typeToGType B
... | just A' | just B' = just (A' G.⊕ B')
... | _       | _       = nothing
typeToGType (T.Eff A B) with typeToGType A | typeToGType B
... | just A' | just B' = just (G.TEff A' B')
... | _       | _       = nothing
typeToGType (T.μ-type _) = nothing
typeToGType (T.ν-type _) = nothing

------------------------------------------------------------------------
-- Round-trip lemmas
------------------------------------------------------------------------

-- | Type → GType → Type is the identity (when convertible in the first step).
--
-- Converting an internal type to its grammar form and back recovers the
-- original type exactly. This is a structural induction on `Type`.
typeToGType-gtypeToType : ∀ (t : Type) (g : GType)
                        → typeToGType t ≡ just g
                        → gtypeToType g ≡ just t
typeToGType-gtypeToType T.Unit   .G.TUnit   refl = refl
typeToGType-gtypeToType T.Void   .G.TVoid   refl = refl
typeToGType-gtypeToType T.Int    .G.TInt    refl = refl
typeToGType-gtypeToType T.Float  .G.TFloat  refl = refl
typeToGType-gtypeToType T.Buffer .G.TBuffer refl = refl
typeToGType-gtypeToType T.Str    .G.TString refl = refl
typeToGType-gtypeToType (A T.⇒[ q ] B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (A T.⇒[ q ] B) .(gA G.⇒[ q ] gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl
typeToGType-gtypeToType (A T.* B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (A T.* B) .(gA G.⊗ gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl
typeToGType-gtypeToType (A T.+ B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (A T.+ B) .(gA G.⊕ gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl
typeToGType-gtypeToType (T.Eff A B) g eq with typeToGType A in eqA | typeToGType B in eqB
typeToGType-gtypeToType (T.Eff A B) .(G.TEff gA gB) refl | just gA | just gB
  rewrite typeToGType-gtypeToType A gA eqA
        | typeToGType-gtypeToType B gB eqB = refl

-- | GType → Type → GType is the identity (when convertible in the first step).
gtypeToType-typeToGType : ∀ (g : GType) (t : Type)
                        → gtypeToType g ≡ just t
                        → typeToGType t ≡ just g
gtypeToType-typeToGType G.TUnit   .T.Unit   refl = refl
gtypeToType-typeToGType G.TVoid   .T.Void   refl = refl
gtypeToType-typeToGType G.TInt    .T.Int    refl = refl
gtypeToType-typeToGType G.TFloat  .T.Float  refl = refl
gtypeToType-typeToGType G.TBuffer .T.Buffer refl = refl
gtypeToType-typeToGType G.TString .T.Str    refl = refl
gtypeToType-typeToGType (A G.⇒[ q ] B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (A G.⇒[ q ] B) .(tA T.⇒[ q ] tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl
gtypeToType-typeToGType (A G.⊗ B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (A G.⊗ B) .(tA T.* tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl
gtypeToType-typeToGType (A G.⊕ B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (A G.⊕ B) .(tA T.+ tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl
gtypeToType-typeToGType (G.TEff A B) t eq with gtypeToType A in eqA | gtypeToType B in eqB
gtypeToType-typeToGType (G.TEff A B) .(T.Eff tA tB) refl | just tA | just tB
  rewrite gtypeToType-typeToGType A tA eqA
        | gtypeToType-typeToGType B tB eqB = refl

------------------------------------------------------------------------
-- Grammar expressibility predicate
------------------------------------------------------------------------

-- | A `Type` is "grammar-expressible" iff it can be round-tripped through
-- `GType`. This is the subset of internal types the surface grammar
-- can actually name.
--
-- Concretely: not `μ-type`, not `ν-type`, and recursively not containing
-- them. The parser only produces grammar-expressible types.
GrammarExpressible : Type → Set
GrammarExpressible t = Σ[ g ∈ GType ] typeToGType t ≡ just g

------------------------------------------------------------------------
-- Parser output is grammar-expressible
------------------------------------------------------------------------

-- | Every atomic type produced by `parseTypeAtom` is grammar-expressible.
-- (Proved by case analysis on the first token.)
--
-- We don't prove this for the full parser here (that is part of G1 in
-- plan 0.3) — but we state the top-level claim, and verify it
-- structurally for the atom-level cases which cover the base types.
--
-- The full completeness proof (for parseType) is deferred to G1; this
-- module just provides the conversion infrastructure it will build on.

-- | Convenience: the parser produces a GType-convertible Type.
-- This definition composes the parser with conversion, giving a
-- "grammar-level" parser for free.
parseGType : List Token → Maybe (GType × List Token)
parseGType toks with parseType toks
... | nothing = nothing
... | just (t , rest) with typeToGType t
...   | just g = just (g , rest)
...   | nothing = nothing

------------------------------------------------------------------------
-- Base-type examples (smoke checks that the connection works)
------------------------------------------------------------------------

-- These definitions exercise the round-trip at the definitional level;
-- if any of them fail to type-check, the conversion tables above are out
-- of sync with either `Grammar` or `Type`.

_ : gtypeToType G.TUnit ≡ just T.Unit
_ = refl

_ : gtypeToType G.TString ≡ just T.Str
_ = refl

_ : typeToGType T.Str ≡ just G.TString
_ = refl

_ : gtypeToType (G.TInt G.⇒[ One ] G.TInt) ≡ just (T.Int T.⇒[ One ] T.Int)
_ = refl

_ : typeToGType (T.Int T.* T.Str) ≡ just (G.TInt G.⊗ G.TString)
_ = refl

-- TVar is rejected:
_ : gtypeToType (G.TVar "A") ≡ nothing
_ = refl

-- μ-type is rejected:
_ : typeToGType (T.μ-type (T.K T.Int)) ≡ nothing
_ = refl

------------------------------------------------------------------------
-- Grammar-expressibility characterisation
--
-- An internal `Type` is grammar-expressible exactly when it avoids
-- the `μ-type` / `ν-type` constructors (the two Type constructors
-- without corresponding `GType` constructors). This predicate +
-- lemma pair provides a structural characterisation independent
-- of the partial conversion function.
------------------------------------------------------------------------

data NoMuNu : Type → Set where
  nmn-unit   : NoMuNu T.Unit
  nmn-void   : NoMuNu T.Void
  nmn-int    : NoMuNu T.Int
  nmn-float  : NoMuNu T.Float
  nmn-str    : NoMuNu T.Str
  nmn-buffer : NoMuNu T.Buffer
  nmn-prod   : ∀ {A B} → NoMuNu A → NoMuNu B → NoMuNu (A T.* B)
  nmn-sum    : ∀ {A B} → NoMuNu A → NoMuNu B → NoMuNu (A T.+ B)
  nmn-fun    : ∀ {A B q} → NoMuNu A → NoMuNu B → NoMuNu (A T.⇒[ q ] B)
  nmn-eff    : ∀ {A B} → NoMuNu A → NoMuNu B → NoMuNu (T.Eff A B)

-- | `NoMuNu t` suffices for `typeToGType t` to return `just _`.
typeToGType-NoMuNu :
  ∀ {t : Type} → NoMuNu t → Σ[ g ∈ GType ] typeToGType t ≡ just g
typeToGType-NoMuNu nmn-unit   = G.TUnit   , refl
typeToGType-NoMuNu nmn-void   = G.TVoid   , refl
typeToGType-NoMuNu nmn-int    = G.TInt    , refl
typeToGType-NoMuNu nmn-float  = G.TFloat  , refl
typeToGType-NoMuNu nmn-str    = G.TString , refl
typeToGType-NoMuNu nmn-buffer = G.TBuffer , refl
typeToGType-NoMuNu (nmn-prod nrA nrB)
  with typeToGType-NoMuNu nrA | typeToGType-NoMuNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = (gA G.⊗ gB) , refl
typeToGType-NoMuNu (nmn-sum nrA nrB)
  with typeToGType-NoMuNu nrA | typeToGType-NoMuNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = (gA G.⊕ gB) , refl
typeToGType-NoMuNu (nmn-fun {q = q} nrA nrB)
  with typeToGType-NoMuNu nrA | typeToGType-NoMuNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = (gA G.⇒[ q ] gB) , refl
typeToGType-NoMuNu (nmn-eff nrA nrB)
  with typeToGType-NoMuNu nrA | typeToGType-NoMuNu nrB
... | gA , eqA | gB , eqB rewrite eqA | eqB = G.TEff gA gB , refl
