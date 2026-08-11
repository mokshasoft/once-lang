-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.HeadView
--
-- THE PER-INSTRUCTION VIEW THE LABEL SCANS INDUCT OVER, arch-generic
-- (Plan 0.65 G1b-2, 2026-08-11).
--
-- `HeadView i` says how the two flat scans — `fl-go` (jump targets) and
-- `ft-go` (closure-body entries) — reduce on `i`, together with the shape of
-- the machine BLOCK `i` lowers to. Three shapes exhaust it: the block is a
-- single jump label, the block opens with a body-entry label, or the block
-- carries no label at all. Nothing here is about an instruction SET; the
-- constructors it names (`once` / `thunk`) are the compiler's own label
-- provenances (D082), which every arch shares.
--
-- WHY IT IS ITS OWN MODULE. `FlatComposition` takes `headView : ∀ i →
-- HeadView i` as a PARAMETER — the arch supplies it exactly as it supplies
-- `skip-law`, because its clauses are equations about that emitter. A module
-- parameter's type cannot mention that module's own body, so the datatype has
-- to be declared one module up. (Same reason `X86-64.ResourceBounds` exists.)
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr)
open import Once.CCC.Label using (Label; once; thunk; LabelId; _≡ᵇᴵ_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.FlatCore.HeadView
  (FS : FrameSemantics)
  (Instr : Set)
  (compile-abstract : AbstractInstr → List Instr)
  (is-label? : Instr → Bool)
  (mk-label : Label → Instr)
  where

open import Once.CCC.Machine.Flat
open FlatMachine {FS} using (fl-go; fl-label-match; ft-go; ft-match)

------------------------------------------------------------------------
-- Does a machine block define a label anywhere in it?
------------------------------------------------------------------------
has-label : List Instr → Bool
has-label []       = false
has-label (i ∷ is) with is-label? i
... | true  = true
... | false = has-label is

------------------------------------------------------------------------
-- HeadView: per-instruction evidence that confines the constructor
-- enumeration to the arch's `headView`, so the preservation proofs stay
-- structural. Either the head is `instr-ctrl (c-label m)` (a single jump
-- label), or `instr-ctrl (c-thunk m b)` (a body entry followed by a
-- label-free tail), or its block is label-free; in all three cases we record
-- how BOTH flat scans reduce on the head.
--
-- Plan 0.63: one enumeration serves both scans — the `once` scan (`fl-go`,
-- jumps) and the `thunk` scan (`ft-go`, calls). A parallel view would
-- duplicate 40 clauses to say the mirror-image thing.
------------------------------------------------------------------------
data HeadView (i : AbstractInstr) : Set where
  hv-clabel : (m : LabelId)
    → compile-abstract i ≡ mk-label (once m) ∷ []
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-label-match (m ≡ᵇᴵ tgt) rest tgt acc)
    -- a `once` label is INVISIBLE to the call scan: `thunk-of?` misses it, and
    -- concretely `once m ≡ᵇᴸ thunk tgt` is the catch-all `false` (D082).
    → (∀ rest tgt acc → ft-go (i ∷ rest) tgt acc ≡ ft-go rest tgt (suc acc))
    → HeadView i
  hv-plain : has-label (compile-abstract i) ≡ false
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-go rest tgt (suc acc))
    → (∀ rest tgt acc → ft-go (i ∷ rest) tgt acc ≡ ft-go rest tgt (suc acc))
    → HeadView i
  -- Plan 0.63 (D082): a block that OPENS WITH A FOREIGN-PROVENANCE LABEL.
  -- `c-thunk` fits neither case above — it IS a label instruction (so it
  -- occupies an index on both sides, which `hv-plain` would deny) but it is
  -- not a `once` label (so `hv-clabel`'s matching scan must not fire).
  -- Both scans therefore step over the whole block. The block is LONGER than
  -- one instruction (the label is followed by the body's frame reservation),
  -- so the tail is carried explicitly and only has to be label-free —
  -- `hv-clabel`'s single-instruction shape would not do.
  -- The provenance premise is `refl` at every producer precisely because
  -- provenances are definitionally disjoint — what D082 bought.
  -- …and it is the THUNK label specifically (the only producer is `c-thunk`),
  -- which is what lets the same view drive the call scan: there this head is
  -- the MATCH decision, exactly as `hv-clabel` is for the jump scan.
  hv-otherlabel : (m : LabelId) (tail : List Instr)
    → compile-abstract i ≡ mk-label (thunk m) ∷ tail
    → has-label tail ≡ false
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-go rest tgt (suc acc))
    → (∀ rest tgt acc → ft-go (i ∷ rest) tgt acc ≡ ft-match (m ≡ᵇᴵ tgt) rest tgt acc)
    → HeadView i
