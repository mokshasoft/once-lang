-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
--
-- `CompiledCorr` — the correspondence AT A COMPILED PROGRAM — stated once for
-- every arch (plan 0.65 G2, item 4's first slice).
--
-- WHY IT NEEDS ITS OWN MODULE. The record mentions BOTH layers: `FlatCorr` and
-- `RetAddrs` come from `FlatCorrespondence`, while `blk-off` and the compiled
-- program come from `FlatComposition`. Neither of those imports the other, so
-- the record has no home in either — it belongs one level above both, which is
-- also where the generic event engine will live when `ConcFlatSim` follows.
--
-- WHAT THE MEASUREMENT SHOWED. x86-64's and riscv64's copies were STRUCTURALLY
-- IDENTICAL — same four fields, same shapes, differing only in `X.State` versus
-- `R.State` and the corresponding projections. That is the evidence this layer
-- is generic in fact and not just in aspiration, and it is why the extraction
-- starts here rather than with the 1,661-line engine: a small piece that is
-- provably shared, moved first, so the engine's parameter surface is settled
-- before the engine moves.
--
-- The four fields, and why each lives HERE rather than in `FlatCorr`:
--
--   dataCorr  the data correspondence proper — that one IS `FlatCorr`.
--   pc-off    translating an abstract pc needs `prog`, which `FlatCorr` has no
--             access to. Same for the two below.
--   ret-eq    D093: every ghost `fret` entry is REALLY in the machine's memory,
--             at its frame's window end, under the same block-offset
--             translation the pc uses. This is what makes a return a
--             correspondence step rather than an assumption.
--   code-eq   D096: a `SV-Code ℓ` encodes to `caddr hv ℓ`, and that is the index
--             the compiled program's OWN label scan finds — the same scan the
--             concrete code-address load and jump use.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles using (RegRoles)
open import Data.Nat using (NonZero)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Once.CCC.Label using (Label)

module Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
  (FS : FrameSemantics)
  (slot-size : ℕ)
  ⦃ slot-size-nz : NonZero slot-size ⦄
  (word-eq : frame-word FS ≡ slot-size)
  (Reg : Set)
  (roles : RegRoles Reg)
  (State : Set)
  (rreg : State → Reg → ℕ)
  (memory : State → (ℕ → Maybe ℕ))
  (xhalted : State → Bool)
  -- …and the two things `FlatCorrespondence` does not see: where the machine's
  -- program counter is, and how a compiled program resolves a label. Both are
  -- about the COMPILED program, which is this layer's whole subject.
  (xpc : State → ℕ)
  (Program : Set)
  (compile-trace : AbstractTrace → Program)
  (find-label : Program → Label → Maybe ℕ)
  -- the block-offset translation, from `FlatComposition`
  (blk-off : AbstractTrace → ℕ → ℕ)
  where

open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fpc; fret; falloc)
open import Once.CCC.Label using (LabelId; thunk)

import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
-- PRIVATE: an instance re-opened publicly would clash with the `C` every arch
-- already binds for its own `FlatCorrespondence` instance. Only the record
-- below is exported.
private
  module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted

open CFC using (HeapView; FlatCorr; RetAddrs; frames-of; caddr)

------------------------------------------------------------------------
-- THE COMPILED CORRESPONDENCE.
------------------------------------------------------------------------
record CompiledCorr (hv : HeapView) (prog : AbstractTrace)
                    (fs : FlatState) (s : State) : Set where
  field
    dataCorr : FlatCorr hv fs s
    pc-off   : xpc s ≡ blk-off prog (fpc fs)
    ret-eq   : RetAddrs (blk-off prog) (memory s) (frames-of (falloc fs)) (fret fs)
    code-eq  : ∀ (ℓ : LabelId) (j : ℕ)
             → find-label (compile-trace prog) (thunk ℓ) ≡ just j
             → caddr hv ℓ ≡ j
open CompiledCorr public
