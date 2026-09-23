-- PROBE (not part of the build): is `block-runs` CONSISTENT as stated?
open import Once.CanonicalName using (CanonicalName)

module Once.Probe.BlockRunsRefute (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Interface o
open import Once.CCC.Machine.SMCore using (mkAllocState; mkLocState; mkRegs)
open import Data.Nat using (s≤s; z≤n)
import Once.CCC.FrameSemantics as FSem
import Once.IRTy

module Refute {FS : FrameSemantics}
              (fr : FSem.FrameSemantics.Frame FS) where
  open Core {FS}
  open FrontierInvariant {FS} using (heap-before)
  open ClosureWellFormedDef {FS} using (valid-unit-wf)

  lbl : LabelId
  lbl = ℓ o 0

  -- an allocator whose heap frontier is 1 (so ref 0 is BeforeFrontier)
  bad-alloc : AllocState {FS}
  bad-alloc = mkAllocState fr [] 0 0 1 (λ _ → 0)

  cloc : ValueLocation FS
  cloc = AtDynamic (heap-loc (mkHeapRef 0) 0)

  eloc : ValueLocation FS
  eloc = AtDynamic (heap-loc (mkHeapRef 0) 9)

  bad-heap : HeapLocation → Maybe (StoredValue FS)
  bad-heap (heap-loc r zero)    = just (SV-Ptr eloc)
  bad-heap (heap-loc r (suc n)) = just (SV-Code lbl)

  bad-st : LocState FS
  bad-st = mkLocState (mkRegs (SV-Tag 0) (SV-Tag 0) (SV-Tag 0) (SV-Tag 0))
                      (λ _ _ → nothing) bad-heap false

  bad-valid : ValidAtWF Heap bad-alloc
                {Unit Once.IRTy.⇛ Unit}
                (λ arg → evalᴰ (terminal {Unit Once.IRTy.* Unit}) (tt , arg))
                cloc bad-st
  bad-valid = valid-closure-wf {body = terminal} {env = tt}
                {alloc = bad-alloc} {closure-loc = cloc} {env-loc = eloc}
                {s = bad-st} {mEnv = Heap} {body-label = lbl}
                tt refl refl
                (heap-before (s≤s z≤n))
                (heap-before (s≤s z≤n))
                valid-unit-wf

  refute : CalleeRuns (ir-to-trace (id {Unit})) → ⊥
  refute cr with cr {Unit} {Unit} {Unit} terminal tt lbl bad-valid refl
  ... | (_ , () , _)
