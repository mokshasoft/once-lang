-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SymbolClash   (D167)
--
-- THE `ld` HALF, WHICH DID NOT EXIST.
--
-- `as` rejects text that defines a symbol twice; `ld` rejects text that CALLS
-- a symbol nothing defines. The first half is stated twice — `DistinctSymbols`
-- (NameClash, the `.globl` function symbols) and `DistinctLabels` (LabelClash,
-- the `.L` locals, D100). The second half was stated NOWHERE, at either level.
--
-- D163 walked straight through that hole. QTT's operand wrappers stopped the
-- arith recogniser firing, so `rewrite-ir` lifted nothing and `arith.div.int`
-- reached the emitter unlifted; the text called `once_15arithzddivzdint` and
-- nothing defined it. 19 exit tests, 119 cabal tests — through a GREEN APEX,
-- because no theorem below the toolchain boundary was false. Exactly the shape
-- LabelClash records for the 2026-08-06 duplicate: the only layer that rejects
-- the text is the toolchain, i.e. `<arch>-loader-faithful`, and that axiom had
-- no such precondition.
--
-- WHAT IS ACTUALLY OWED (D061, and the framing to keep straight — D071).
-- A SigOp "escapes CCC structure but not soundness: it carries a contract
-- (`semM` + `EffectShape` + `impl ⊨ semM`) its producer must discharge", and
-- there are two producers:
--
--   * an INTERPRETATION discharges OFF-LINE, per (SigOp × target),
--     proof-or-postulate — all interpretations equal, none special. `ld`
--     resolves its symbol from the linked interpretation object, so this
--     module says nothing about it.
--   * the COMPILER, minting SigOps for optimisation (the arith path). Those
--     owe the same contract, and `impl ⊨ semM` is discharged by `rewrite-ir`
--     lifting the subtree into an `arith.block.<digest>` whose body
--     `emitArithBlocks` writes.
--
-- So this predicate is the CHECKABLE CONSEQUENCE of that discharge: every
-- compiler-minted SigOp the emitted text calls has its block emitted. It is
-- NOT the claim that "a SigOp owes a symbol" — a named definition is a context
-- projection with a direct-call ABI (D071), never a SigOp, and does not appear
-- in `syms-ref` at all.
--
-- SCOPE, honestly. Reading `sem` as "pureV ⇒ ours to emit" holds only because
-- an interpretation's contract is always `emitsV`/`haltsV`; a PURE EXTERNAL
-- would break it, and the discharge-owner would then have to be carried
-- explicitly (`Linkage`, D071, currently "never read"). Recorded at
-- `EmittedWF.sigop-owed` too.
------------------------------------------------------------------------

module Once.Adequacy.SymbolClash where

open import Data.Bool using (Bool; false)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)

open import Once.CanonicalName using (CanonicalName)
open import Once.Target.Arch using (Arch)
open import Once.Parser.Module.Core using (Module)
import Once.Compile as C

------------------------------------------------------------------------
-- The predicate. Both lists are read off the SAME `ir'` the backend compiles
-- (`directCallIR` then `rewrite-ir`), so neither can drift from the emitted
-- text — the property `moduleLabels` was given for the same reason.
------------------------------------------------------------------------

SymbolsResolvable : Arch → Module → Set
SymbolsResolvable arch m =
  All (_∈ C.moduleSymDefs C.Heap false m) (C.moduleSymRefs arch C.Heap false m)

postulate
  -- RESIDUAL (deferred proof / codegen). The obligation the apex owes so that
  -- `<arch>-loader-faithful` may assume the text it is handed LINKS, the exact
  -- sibling of `program-labels-distinct`.
  --
  -- It is TRUE for the emitter as it stands (D163 restored the lifting, and
  -- the exit tests link on all three targets), and the proof is the arith
  -- recogniser's completeness: every `pureV` SigOp the elaborator mints sits
  -- in a position `rewrite-ir` recognises. That is a real theorem about
  -- `recognise-body` and it is what would make a future recogniser regression
  -- a TYPE ERROR instead of a link error.
  program-symbols-resolvable : ∀ (arch : Arch) (m : Module) → SymbolsResolvable arch m
