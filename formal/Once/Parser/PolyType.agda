-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.PolyType
--
-- Parser for polymorphic types (`PolyType` with `PTVar`).
--
-- Separate from `Once.Parser.Type` (which parses ground `Type`)
-- because user-declared polymorphic signatures — `swap : a * b →
-- b * a` — need a type grammar that accepts type variables. Ground
-- `Type` stays TVar-free by design; see plan 0.2.5 for the rationale.
--
-- Grammar (lowercase-TVar convention, plan 0.6):
--   PolyType     ::= PolySum ArrowTail | PolySum
--   ArrowTail    ::= GradeAnn? '->' PolyType
--   GradeAnn     ::= '^1' | '^0' | '^w'
--   PolySum      ::= PolyProd ('+' PolyProd)*
--   PolyProd     ::= PolyAtom ('*' PolyAtom)*
--   PolyAtom     ::= 'Unit' | 'Void' | 'Int' | 'Float' | 'Buffer' | 'String'
--                  | 'Eff' PolyAtom PolyAtom | 'IO' PolyAtom
--                  | lower_ident                                -- type variable
--                  | 'Mu' PolyFuncSum | 'Nu' PolyFuncSum
--                  | lower_ident                                -- type variable
--                  | '(' PolyType ')'
--
-- D196: that grammar is no longer IMPLEMENTED here. This module is now just
-- the bounded wrapper `parsePolyTypeB`, which runs the generic parser
-- (`Once.Parser.Generic.PolyInst.parsePolyTypeP`) and attaches the
-- strict-decrease proof its WF callers need. The grammar above is the one
-- `ParsesPolyType` defines and the generic parser is proved sound and
-- complete against — so the header that used to promise "plan 0.7 Phase 2
-- will add a relational specification" is discharged: it exists, and it is
-- the only specification there is.
------------------------------------------------------------------------

module Once.Parser.PolyType where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Char using (isLower)
import Data.String as StrLib
open import Relation.Nullary using (yes; no)

open import Once.Type
open import Once.Parser.Token
open import Once.Parser.Core using (Parser)

------------------------------------------------------------------------
-- Lowercase-identifier test — the lexical distinction between a type
-- variable and a type keyword / alias.
------------------------------------------------------------------------

-- | True iff `s` starts with a lowercase letter (a-z).
-- (Definition relocated to Once.Parser.CharClass; re-exported here so existing
-- importers `Once.Parser.PolyType using (isLowerWord)` keep working.)
open import Once.Parser.CharClass public using (isLowerWord)

------------------------------------------------------------------------
-- D196: THE HAND-WRITTEN POLY PARSER IS GONE.
--
-- What stood here was a second, unverified implementation of the same
-- grammar: `parsePolyTypeImpl` and its ten mutually-recursive helpers, under
-- a termination-check-bypassing pragma, exported as `parsePolyType`. NOTHING
-- consumed it — the live signature path is `parsePolyTypeB` below, which runs
-- the GENERIC parser (`parsePolyTypeP`) and wraps it in `sound-polyType`, so
-- every accept is backed by a `ParsesPolyType` derivation.
--
-- It was not merely redundant, it was a HOLE IN THE GATE. D191 added `Nu` to
-- the ground-type parser and the first `ana` program still failed to parse;
-- adding `Nu` HERE produced zero proof obligations and still did not fix it,
-- because this parser is dead. Adding it to the generic algebra produced five
-- (relation constructor, shrink measure, parser clause, soundness,
-- completeness) and fixed it. A keyword could enter this file without anyone
-- having to prove the relation accepts it — exactly the island MERGE.md's
-- no-islands rule is about: dead code hides gaps instead of surfacing them as
-- type errors.
--
-- Coverage was checked before deleting, not assumed: both parsers accepted the
-- same keyword set (Unit/Void/Int/Float/Buffer/String/Eff/IO/Mu/Nu/K/Id), the
-- quantity arrows are handled generically by `arrowDir`, and this file's
-- `TLBrace` clause was a rejection, not a feature. Nothing to port.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Bounded variant: guarantees strict length decrease on success.
--
-- Needed by downstream WF parsers (`parseDeclB` / `parseDeclsWF`)
-- that derive their own termination proofs from the fact that
-- every successful type parse consumes at least one token.
--
-- Implementation: run the unbounded parser, then runtime-check the
-- length relation. On success the check is always true (every
-- `parsePolyType` success consumes ≥1 token); on the rare "parser
-- returned same-length residual" path (shouldn't happen
-- structurally) we return nothing rather than falsely asserting
-- the bound. Plan 0.7 Phase 2 replaces this runtime check with a
-- structural proof.
------------------------------------------------------------------------

open import Data.Nat using (_<_; _<?_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Parser.Generic.PolyInst
  using (parsePolyTypeP; sound-polyType; ParsesPolyType-shrink)

ParsePolyAtB : List Token → Set
ParsePolyAtB toks =
  Maybe (Σ[ t ∈ PolyType ] Σ[ rest ∈ List Token ] length rest < length toks)

-- Plan 0.7-2: the runtime `<?` check is replaced by a STRUCTURAL bound — the
-- generic bound-free parser `parsePolyTypeP` is now THE PolyType parser, and the
-- length decrease is the relation shrink applied to the soundness witness.
-- De-`with`'d through `ppB-go` (the result Maybe is a parameter) so the bridge
-- lemmas `parsePolyTypeB ↔ ParsesPolyType` can reason about it.
ppB-go : (toks : List Token) (r : Maybe (PolyType × List Token)) →
         parsePolyTypeP toks ≡ r → ParsePolyAtB toks
ppB-go toks nothing          pf = nothing
ppB-go toks (just (t , rest)) pf =
  just (t , rest , ParsesPolyType-shrink (sound-polyType toks (<-wellFounded (length toks)) pf))

parsePolyTypeB : (toks : List Token) → ParsePolyAtB toks
parsePolyTypeB toks = ppB-go toks (parsePolyTypeP toks) refl
