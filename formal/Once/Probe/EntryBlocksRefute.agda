-- PROBE (not part of the build): can `entry-blocks` be refuted the way D213
-- refuted `block-runs`?
--
-- D213's attack on `block-runs`: its premises mention only a STATE, so
-- fabricate a heap whose cells read `just (SV-Code ℓ)` for a label no program
-- ever minted, and the program-level conclusion collapses at `ir = id {Unit}`,
-- which emits no blocks at all.
--
-- The same move does not start here. `entry-blocks` takes ONLY the IR — there
-- is no state to fabricate, and its conclusion is about the list the emitter
-- itself produced. At D213's witness IR that list is EMPTY, so the residual's
-- content there is `All _ []`: inhabited, not absurd. This file records the
-- attempt and pins the fact the argument rests on, so a change to the
-- emitter's block channel breaks this file instead of silently invalidating it.
open import Once.CanonicalName using (CanonicalName)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Target.Arch using (arch-numerics)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Once.CCC.FrameSemantics

module Once.Probe.EntryBlocksRefute (o : CanonicalName)
  (arch : Arch) (FS : FrameSemantics)
  (fmt-agree : Once.CCC.FrameSemantics.fs-numerics FS ≡ arch-numerics arch)
  (entry-frame : FrameSemantics.Frame FS)
  (asem : ArchSemantics) where

open import Data.List using ([])
open import Once.IR using (IR; Unit; id)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.Adequacy.ArchCorrectness.FlatFromObs o arch FS fmt-agree entry-frame asem
  using (entry-blocks)

open IRObsCorrectFlatness {FS} using (BlocksAt; blocks)

id-has-no-blocks : blocks 0 0 (id {Unit}) ≡ []
id-has-no-blocks = refl
