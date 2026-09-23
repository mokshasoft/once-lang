-- PROBE (not part of the build): the apex axiom `block-runs`, at the very
-- telescope `FlatFromObs` is instantiated with, proves ⊥.
open import Data.Nat using (ℕ)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Target.Arch using (arch-numerics)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CanonicalName using (CanonicalName)
import Once.CCC.FrameSemantics

module Once.Probe.ApexInconsistent (o : CanonicalName)
  (arch : Arch) (FS : FrameSemantics)
  (fmt-agree : Once.CCC.FrameSemantics.fs-numerics FS ≡ arch-numerics arch)
  (entry-frame : FrameSemantics.Frame FS)
  (asem : ArchSemantics) where

open import Data.Empty using (⊥)
open import Once.IR using (IR; Unit; id)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.Adequacy.ArchCorrectness.FlatFromObs o arch FS fmt-agree entry-frame asem
  using (block-runs)
open import Once.Probe.BlockRunsRefute o using (module Refute)

open IRObsCorrectFlatness {FS} using (BlockRuns)
open Refute {FS} entry-frame using (refute)

boom : ⊥
boom = refute (BlockRuns.closures (block-runs (id {Unit})))

------------------------------------------------------------------------
-- The NEIGHBOURING postulate `entry-size` used to be refuted here too, by
-- `boom-size = 1+n≰n (≤-trans (entry-size (iter program-bound))
--                             (iter-big program-bound))`.
-- Plan 0.91 S1 / D214 DELETED `entry-size` and the whole `program-bound`
-- telescope, so that half of this probe no longer even typechecks — which is
-- the point. `boom` above is what still stands.
------------------------------------------------------------------------
