-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation
--
-- riscv64's compiled correspondence — the DATA correspondence (`FlatCorr`,
-- pc-free) ⊕ the block-offset pc relation, ⊕ the pending returns and the code
-- map. Mirror of x86-64's, and the same four fields for the same reasons:
-- `pc-off`, `ret-eq` and `code-eq` live HERE rather than in `FlatCorr` because
-- each needs `prog` to translate an abstract index or label.
--
-- SCOPE, stated so it is not mistaken for more than it is: this module holds
-- `CompiledCorr` and nothing else yet. The per-instruction BLOCK-STEPS are
-- G2's bulk and are not here.
--
-- It exists now for two reasons, both structural rather than opportunistic:
--
--   * `RiscV64/FlatComposition.agda` was an ISLAND — typechecked by the
--     `ccc-riscv64` target and imported by nothing. This is its first real
--     consumer (`blk-off`), so the second instance of the G1b core is now
--     wired rather than merely gated.
--   * `HeapRoom`/`StackRoom`/`CallRoom` are CONDITIONED on `CompiledCorr` —
--     unconditioned they are refutable (the 2026-07-30 vacuity lesson). So
--     riscv64 could not state its resource bounds, and therefore could not
--     thread them from the apex, until this record existed. That thread is
--     what stops G2's block-steps from inventing their own premises.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Once.CCC.Machine.Flat
open FlatMachine {FS} using (FlatState; fpc; fret; falloc)
open import Once.CCC.Label using (thunk; LabelId)

import Once.CCC.Target.RiscV64.Semantics as R
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FC
module C = FC FS word-eq
open C using (HeapView; haddr; HDom; hfront)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition FS
  using (blk-off)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace)

------------------------------------------------------------------------
-- The compiled correspondence.
------------------------------------------------------------------------
record CompiledCorr (hv : HeapView) (prog : AbstractTrace) (fs : FlatState) (s : R.State) : Set where
  field
    dataCorr : C.FlatCorr hv fs s
    -- CONTROL: the machine pc sits at the block offset of the flat pc.
    pc-off   : R.State.pc s ≡ blk-off prog (fpc fs)
    -- THE PENDING RETURNS (D093): every ghost `fret` entry is really in the
    -- machine's memory, at its frame's window end, under the same block-offset
    -- translation the pc uses.
    ret-eq   : C.RetAddrs (blk-off prog) (R.State.memory s)
                          (C.frames-of (falloc fs)) (fret fs)
    -- THE CODE MAP IS THE PROGRAM'S OWN RESOLUTION (D096): a `SV-Code ℓ`
    -- encodes to `caddr hv ℓ`, and that is the index the compiled program's
    -- own label scan finds.
    code-eq  : ∀ (ℓ : LabelId) (j : ℕ)
             → R.find-label (compile-trace prog) (thunk ℓ) ≡ just j
             → C.caddr hv ℓ ≡ j
open CompiledCorr public
