-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.EmittedWF   (D100)
--
-- WHAT THE ASSEMBLER NEEDS FROM US. `as` rejects text that defines the same
-- symbol twice, and `ld` rejects text that references a symbol nothing
-- defines. Neither fact was ever stated, so neither was ever proved — and the
-- 61-test regression of 2026-08-06 (`symbol .L_thunk_once_4main_10 is already
-- defined`) walked straight through the hole.
--
-- WHY NO PROOF CAUGHT IT. `find-label` is a FIRST-MATCH scan on every arch,
-- and the flat machine resolves labels by the same first-match scan. So for a
-- trace with a duplicated label the two machines still AGREE: the simulation
-- is true, and no theorem below the toolchain boundary can be false. The only
-- layer that rejects a duplicate is `as` — and that layer is
-- `<arch>-loader-faithful`, which was stated with no precondition at all. The
-- axiom was not weak, it was FALSE for every program the emitter duplicated.
--
-- This module states the missing precondition ONCE, on the ABSTRACT TRACE, so
-- that all three arches inherit it instead of each restating it. It is the
-- exact analogue of `DistinctSymbols` / `program-no-clash` (Plan 0.50) one
-- level down: that pair covers the `.globl` function symbols, this one covers
-- the local labels the codegen invents.
--
-- SCOPE, stated honestly: an arch's `compile-trace-cnt` allocates FURTHER
-- labels of its own (the case/loop expansions), starting from the counter this
-- trace hands out. Those are not covered here. That walk is LINEAR — it never
-- splices a sub-trace twice — so its freshness is a `LabelRange`-shaped
-- one-liner per arch; the non-linear walk (`ir-to-trace'`, whose `Cata` clause
-- splices its algebra twice) is the hard half and is the half stated here.
------------------------------------------------------------------------

module Once.CCC.Codegen.EmittedWF where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Once.CCC.Label using (Label; once; thunk; LabelId)
open import Once.CCC.Machine.SMCore using
  ( AbstractInstr; AbstractTrace
  ; instr-ctrl; instr-load-code-addr
  ; instr-case-on-tag; instr-loop
  ; FlatCtrl; c-label; c-jmp; c-thunk; c-ret
  ; c-branch-scratch-zero; c-branch-tag-zero )

------------------------------------------------------------------------
-- THE DEFINING OCCURRENCES — the symbols the emitted text DEFINES.
--
-- Two of them, in the two provenances: `c-label` renders as `.Lonce_…:` and
-- `c-thunk` as `.L_thunk_once_…:` (`compile-abstract`, all three arches).
-- `c-ret` carries a budget, not a label.
--
-- The two nested-trace constructors are traversed rather than swept into the
-- catch-all. Neither has a producer today (`IRToTrace`: "instr-case-on-tag now
-- has NO PRODUCER"), but a predicate that silently ignores a constructor is
-- how a retired-constructor catch-all becomes a lie later.
------------------------------------------------------------------------

labels-def   : AbstractTrace → List Label
labels-def-i : AbstractInstr → List Label

labels-def []       = []
labels-def (i ∷ is) = labels-def-i i ++ labels-def is

labels-def-i (instr-ctrl (c-label m))   = once  m ∷ []
labels-def-i (instr-ctrl (c-thunk m _)) = thunk m ∷ []
labels-def-i (instr-case-on-tag f g)    = labels-def f ++ labels-def g
labels-def-i (instr-loop b)             = labels-def b
{-# CATCHALL #-}
labels-def-i _                          = []

------------------------------------------------------------------------
-- THE REFERENCING OCCURRENCES — the symbols the emitted text MENTIONS.
--
-- The three `once`-provenance control transfers, plus the one `thunk`-
-- provenance code-address load (`lea .L_thunk_…(%rip)`, the closure record's
-- code cell). Cross-provenance confusion is impossible by `_≡ᵇᴸ_`'s catch-all
-- (D033/D082), which is why the two lists can share one `Label` type.
------------------------------------------------------------------------

labels-ref   : AbstractTrace → List Label
labels-ref-i : AbstractInstr → List Label

labels-ref []       = []
labels-ref (i ∷ is) = labels-ref-i i ++ labels-ref is

labels-ref-i (instr-ctrl (c-jmp m))                 = once  m ∷ []
labels-ref-i (instr-ctrl (c-branch-scratch-zero m)) = once  m ∷ []
labels-ref-i (instr-ctrl (c-branch-tag-zero m))     = once  m ∷ []
labels-ref-i (instr-load-code-addr m)               = thunk m ∷ []
labels-ref-i (instr-case-on-tag f g)                = labels-ref f ++ labels-ref g
labels-ref-i (instr-loop b)                         = labels-ref b
{-# CATCHALL #-}
labels-ref-i _                                      = []

------------------------------------------------------------------------
-- THE PREDICATE.
--
-- A RECORD rather than a pair: the two fields are owed by different proofs
-- (the first by the emitter's counter/path discipline, the second by the
-- `curry` clause emitting `c-thunk ℓ` in the same literal list as the
-- `instr-load-code-addr ℓ` that names it), and a record keeps the two obligations
-- separately nameable at every use site.
--
-- `labels-resolvable` IS the residual `emitted-code-addr-has-body` (ledger #10's
-- neighbour), stated where it belongs rather than as a free-floating apex
-- postulate — the same fact `code-map`'s `nothing`-filler comment appeals to.
------------------------------------------------------------------------

record EmittedWF (at : AbstractTrace) : Set where
  constructor mkEmittedWF
  field
    -- `as`: "symbol … is already defined". D099's defect, stated proof-side.
    labels-unique     : AllPairs _≢_ (labels-def at)
    -- `ld`: "undefined reference". Every jump/branch/code-address lands.
    labels-resolvable : All (_∈ labels-def at) (labels-ref at)

open EmittedWF public
