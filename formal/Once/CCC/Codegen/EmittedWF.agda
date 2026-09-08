-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
  ; c-branch-scratch-zero; c-branch-tag-zero
  -- D164: the rest of `AbstractInstr`, so both walks can be ENUMERATED
  -- instead of resting on a catch-all.
  ; mov-to-output; mov-to-input; load-indirect; load-indirect-suc
  ; store-indirect; store-indirect-suc; instr-pop-frame; instr-call-closure
  ; instr-save-closure-reg
  ; load-from-slot; store-at-slot; lea-slot; restore-input; instr-alloc-stack
  ; instr-dealloc-stack; instr-reclaim-to; instr-push-frame; worklist-init
  ; worklist-push; worklist-pop; worklist-check; instr-load-tag-lit
  ; instr-alloc-heap; instr-reg-op; lea-indexed
  ; instr-sigop; instr-load-const )

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

-- D164: ENUMERATED, not a catch-all. A new instruction must now be given a
-- verdict here rather than silently defining nothing.
labels-def-i (instr-ctrl (c-label m))                = once  m ∷ []
labels-def-i (instr-ctrl (c-thunk m _))              = thunk m ∷ []
labels-def-i (instr-ctrl (c-jmp _))                  = []
labels-def-i (instr-ctrl (c-branch-scratch-zero _))  = []
labels-def-i (instr-ctrl (c-branch-tag-zero _))      = []
labels-def-i (instr-ctrl (c-ret _))                  = []
labels-def-i (instr-case-on-tag f g)                 = labels-def f ++ labels-def g
labels-def-i (instr-loop b)                          = labels-def b
labels-def-i (instr-load-code-addr _)                = []
-- a SigOp INVOCATION defines nothing.
labels-def-i (instr-sigop _)                         = []
labels-def-i mov-to-output                            = []
labels-def-i mov-to-input                             = []
labels-def-i load-indirect                            = []
labels-def-i load-indirect-suc                        = []
labels-def-i store-indirect                           = []
labels-def-i store-indirect-suc                       = []
labels-def-i instr-pop-frame                          = []
labels-def-i instr-call-closure                       = []
labels-def-i instr-save-closure-reg                   = []
labels-def-i (load-from-slot _)                     = []
labels-def-i (store-at-slot _)                      = []
labels-def-i (lea-slot _)                           = []
labels-def-i (restore-input _)                      = []
labels-def-i (instr-alloc-stack _)                  = []
labels-def-i (instr-dealloc-stack _)                = []
labels-def-i (instr-reclaim-to _)                   = []
labels-def-i (instr-push-frame _)                   = []
labels-def-i (worklist-init _)                      = []
labels-def-i (worklist-push _)                      = []
labels-def-i (worklist-pop _)                       = []
labels-def-i (worklist-check _)                     = []
labels-def-i (instr-load-tag-lit _)                 = []
labels-def-i (instr-alloc-heap _)                   = []
labels-def-i (instr-reg-op _)                       = []
labels-def-i (lea-indexed _)                        = []
labels-def-i (instr-load-const _ _)                    = []

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

-- D164: ENUMERATED, not a catch-all — same reason, and here it also forced
-- the `instr-sigop` question to be answered in writing.
labels-ref-i (instr-ctrl (c-jmp m))                  = once  m ∷ []
labels-ref-i (instr-ctrl (c-branch-scratch-zero m))  = once  m ∷ []
labels-ref-i (instr-ctrl (c-branch-tag-zero m))      = once  m ∷ []
labels-ref-i (instr-ctrl (c-label _))                = []
labels-ref-i (instr-ctrl (c-thunk _ _))              = []
labels-ref-i (instr-ctrl (c-ret _))                  = []
labels-ref-i (instr-load-code-addr m)                = thunk m ∷ []
labels-ref-i (instr-case-on-tag f g)                 = labels-ref f ++ labels-ref g
labels-ref-i (instr-loop b)                          = labels-ref b
-- D164: A SIGOP INVOCATION REFERENCES A SYMBOL — AND IT IS NOT ONE OF THESE.
-- `instr-sigop si` lowers to `call <once-symbol-path (name si)>`, a `.globl`
-- symbol resolved by `ld` against this module's arith blocks or an external
-- interpretation. `labels-def` collects only `c-label` / `c-thunk`, so listing
-- it here would make `labels-resolvable` FALSE rather than useful. It belongs
-- in a SIBLING statement over `CanonicalName`s with its own resolution rule,
-- which does not exist yet — and its absence is what let D163's regression
-- ship a `call` to a symbol nothing defined. Recorded here rather than left
-- to a catch-all, so the gap is written down at the point it is skipped.
labels-ref-i (instr-sigop _)                         = []
labels-ref-i mov-to-output                            = []
labels-ref-i mov-to-input                             = []
labels-ref-i load-indirect                            = []
labels-ref-i load-indirect-suc                        = []
labels-ref-i store-indirect                           = []
labels-ref-i store-indirect-suc                       = []
labels-ref-i instr-pop-frame                          = []
labels-ref-i instr-call-closure                       = []
labels-ref-i instr-save-closure-reg                   = []
labels-ref-i (load-from-slot _)                     = []
labels-ref-i (store-at-slot _)                      = []
labels-ref-i (lea-slot _)                           = []
labels-ref-i (restore-input _)                      = []
labels-ref-i (instr-alloc-stack _)                  = []
labels-ref-i (instr-dealloc-stack _)                = []
labels-ref-i (instr-reclaim-to _)                   = []
labels-ref-i (instr-push-frame _)                   = []
labels-ref-i (worklist-init _)                      = []
labels-ref-i (worklist-push _)                      = []
labels-ref-i (worklist-pop _)                       = []
labels-ref-i (worklist-check _)                     = []
labels-ref-i (instr-load-tag-lit _)                 = []
labels-ref-i (instr-alloc-heap _)                   = []
labels-ref-i (instr-reg-op _)                       = []
labels-ref-i (lea-indexed _)                        = []
labels-ref-i (instr-load-const _ _)                    = []

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
