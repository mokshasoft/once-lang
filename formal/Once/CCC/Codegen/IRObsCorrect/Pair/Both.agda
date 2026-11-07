-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair.Both
--
-- D211: `⟨ f , g ⟩` when BOTH halves returned — the pair is assembled (the
-- fifteen-field record `result`). Split from `Pair` (plan 0.144: together
-- they peaked at 3.0–3.4 GB); `Pair` keeps `g`'s other outcomes and the
-- dispatch. What keeps it fast is written in `Pair`'s header.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore
import Once.CCC.FrameSemantics as FrameSemantics′

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Both (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; restore-input; readReg; Output; module LocState; module AllocState)
open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)
open LocState using (halted; regs)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Chain    o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Place o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Proof o tbl
open import Data.List.Properties using (++-identityʳ)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IRTy as IRTy′
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.ValueDomain as ValueDomain
import Once.IR.Semantics.Trace as TM
open import Once.Res using (Res; stopped; returns; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft; done-value)

-- The pair's log, over plain lists (plan 0.144: the same chain written inline on
-- the machine states left the step states to unification, at seconds each).
log-assoc : ∀ {X : Set} {x E : List X} (h a b : List X) → x ≡ (h ++ a) ++ b → E ≡ a ++ b → x ≡ h ++ E
log-assoc h a b p q = trans p (trans (++-assoc h a b) (cong (h ++_) (sym q)))

module PairBothC {FS : FrameSemantics} where
  open Core  {FS}
  open Mach  {FS}
  open PairC {FS}
  open PairPlaceC {FS}

  open PairProofC {FS}
  module PairProofB {A B C} {f : IR A B} {g : IR A C}
    (ihf : IRObsCorrectF f) (ihg : IRObsCorrectF g) (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩)) (bl : BlocksAt prog (blocks n l ⟨ f , g ⟩))
    (la : LabelsAt prog base (emitted n l ⟨ f , g ⟩))
    (mIn : AllocMode) (x : ValueDomain.⟦ A ⟧ᴰᴵ) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (ns0 : next-slot alloc ≡ 0) (nh : halted s ≡ false) (inp : InputAt {prog = prog} {A} mIn alloc x s) (k : ℕ)
    where
      open PairProof ihf ihg n l prog base ss cr span bl la mIn x s alloc cl rs ns0 nh inp k

      module ReturnsB (vB : ⟦ B ⟧) (rB : ℕ) (rfeq : resultAt (floc PC.PR.p2) (⟪ evalᴰ f x ⟫ k) ≡ returns (done vB rB)) where
          open Returns vB rB rfeq

          progF : k ≤ rB + chain-ctrls (VR.run vrf)
          progF = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (VR.run vrf)) rfeq (VR.progress vrf)

          ctrlsG : chain-ctrls (VR.run vrg) ≡ chain-ctrls chainG₀
          ctrlsG = sym (chain-ctrls-subst-start (sym PCF.handG) (VR.run vrg))

          module ReturnsG (vC : ⟦ C ⟧) (rC : ℕ) (rgeq : resultAt (floc PCF.m2) (⟪ evalᴰ g x ⟫ rB) ≡ returns (done vC rC)) where
              -- `g` returned, so it was not cut.
              ncG : NotCut (resultAt (floc PCF.m2) (⟪ evalᴰ g x ⟫ rB))
              ncG = subst NotCut (sym rgeq) tt

              module PPresG = PPres ncG

              -- WHAT THE PAIR RUNS AND RETURNS: both calls' events, and `f`'s
              -- value with `g`'s, assembled by the inner `return∞`, with the
              -- budget `g` left.
              PR≡ : runAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ (esF ++ (esG ++ []) , returns (done (vB , vC) rC))
              PR≡ = inner-run (returns (done vC rC)) rgeq

              res-pair : resultAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ returns (done (vB , vC) rC)
              res-pair = cong proj₂ PR≡

              ev-pair : eventsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ esF ++ esG
              ev-pair = trans (cong proj₁ PR≡) (cong (esF ++_) (++-identityʳ esG))

              not-stopped : ∀ {X : Set} → stopsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ true → X
              not-stopped p = case trans (sym p) (cong is-stopped res-pair) of λ ()

              module PCG = PairChainG f g n l prog base s alloc cl rs n≤ nh span vrf rfeq vrg rgeq

              ----------------------------------------------------------------
              -- `PairPlace`'s five non-trivial parameters.
              ----------------------------------------------------------------
              runG≡ : exec-flat (VR.steps vrg) prog
                        (entry-flat PCF.bg (floc PCF.m2) (falloc PCF.m2)
                                    (fclosure PCF.m2) rs)
                      ≡ PCG.fsG
              runG≡ = trans (cong (λ m → exec-flat m prog
                                           (entry-flat PCF.bg (floc PCF.m2)
                                              (falloc PCF.m2) (fclosure PCF.m2) rs))
                                  (sym (+-identityʳ (VR.steps vrg))))
                            (exec-flat-steps (VR.run vrg) 0)

              ns-gs : next-slot (falloc PCG.fsG) ≡ next-slot alloc
              ns-gs = trans (trans (cong (λ st → next-slot (falloc st)) (sym runG≡))
                                   (flat-run-keeps-next-slot (VR.steps vrg) prog ss
                                      PCF.bg (floc PCF.m2) (falloc PCF.m2)
                                      (fclosure PCF.m2) rs))
                            ns-m2

              hr-gs : next-heap-ref (falloc PCF.fsF) ≤ next-heap-ref (falloc PCG.fsG)
              hr-gs = ≤-trans (≤-reflexive (sym hr-mid)) (vr-heap-mono vrg ncG)

              bf-fsF→g : ∀ (loc : ValueLocation FS)
                       → BeforeFrontier (falloc PCF.fsF) loc
                       → BeforeFrontier (record (falloc PCF.m2) { next-slot = PS.n1 }) loc
              bf-fsF→g = frontier-monotone (falloc PCF.fsF)
                           (record (falloc PCF.m2) { next-slot = PS.n1 })
                           (trans PCF.cf-fsF (sym PCF.cf-m2))
                           (≤-trans (≤-reflexive ns-fsF) (≤-trans n≤ n≤n1))
                           (≤-reflexive (sym hr-mid))

              mem-F→G : ∀ (loc : ValueLocation FS)
                      → BeforeFrontier (falloc PCF.fsF) loc
                      → SMCore.MemOps.readLoc (floc PCG.fsG) loc
                        ≡ SMCore.MemOps.readLoc (floc PCF.fsF) loc
              mem-F→G loc b =
                trans (vr-mem-pres vrg ncG loc (bf-fsF→g loc b))
                (trans (mem-untouched (restore-input n) (floc PCF.m1) (falloc PCF.m1) loc
                          Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
                       (store-slot-preserves-before (suc n) (floc PCF.fsF)
                          (falloc PCF.fsF) (falloc PCF.fsF) loc refl
                          (≤-trans (≤-reflexive ns-fsF) (≤-trans n≤ (n≤1+n n))) b))

              fst-cell-gs : SMCore.MemOps.readLoc (floc PCG.fsG)
                              (AtStack (current-frame alloc) (suc n))
                          ≡ just (readReg (regs (floc PCF.fsF)) Output)
              fst-cell-gs =
                trans (vr-mem-pres vrg ncG (AtStack (current-frame alloc) (suc n))
                        (BeforeFrontier.stack-before (sym PCF.cf-m2) PCG.fst<n1))
                (trans (mem-untouched (restore-input n) (floc PCF.m1) (falloc PCF.m1)
                          (AtStack (current-frame alloc) (suc n))
                          Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
                       PCF.read-fst-m1')

              module PPlace = PairPlace {prog} {B} {C} n alloc n≤ PCF.fsF (VR.settle vrg)
                                PCF.cf-fsF PCG.cf-fsG ns-fsF ns-gs hr-gs
                                vB vC
                                (VR.out-mode vrf) (VR.out-mode vrg)
                                (VR.cont-alloc vrf) (VR.cont-alloc vrg)
                                (VR.place vrf rfeq) (VR.place vrg rgeq)
                                mem-F→G fst-cell-gs

              module PPresF = PPresG.Fill PPlace.rdi-u6 PPlace.rdi-u8

              -- THE SETTLE STATE HAS THREE NAMES: `PCG.SETTLE` (the run's),
              -- `PPlace.u10` (the placement's) and `PPresG.NSP.u10` (the
              -- preservation facts'). Agda identifies any two of them directly
              -- only by evaluating all nine rows, ~100 s each (profile
              -- 2026-11-06, plan 0.144). So they are identified through the
              -- OPAQUE end state `NineSteps.u10ᵒ`, whose copies compare by their
              -- arguments (the `context-form-mismatch-opaque` pattern), and every
              -- field from `PairPlace`/`PairPres` is transported along that by
              -- `subst`, whose motive Agda checks by name.
              settle≡place : PCG.SETTLE ≡ PPlace.u10
              settle≡place = trans PCG.SETTLE≡ᵒ PPlace.NSP.u10ᵒ-def

              settle≡pres : PCG.SETTLE ≡ PPresG.NSP.u10
              settle≡pres = trans PCG.SETTLE≡ᵒ PPresG.NSP.u10ᵒ-def

              at-settle : ∀ {P : FlatState → Set} → P PPresG.NSP.u10 → P PCG.SETTLE
              at-settle {P} = subst P (sym settle≡pres)

              -- The record's fields, each NAMED AT ITS TYPE: the expected types
              -- mention `PCG.SETTLE`/`PCG.RUN`, the suppliers their own states,
              -- and stating each once keeps the conversion between them in
              -- one place (and lets a profile see which one costs).
              E : TM.T (Ap ⟦ B IRTy′.* C ⟧)
              E = ⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k

              field-log : SMCore.LocState.ev-log (floc PCG.SETTLE) ≡ SMCore.LocState.ev-log s ++ eventsAt s E
              field-log =
                log-assoc h esF esG (trans (log-silent PCG.tail-chain refl) log-fg) ev-pair

              -- plan 0.98: the premise binds `v`; `res-pair` says what the pair
              -- actually returned, and `done-value` identifies the two.
              field-place : ∀ {v r} → resultAt s E ≡ returns (done v r)
                          → ResultPlace {prog = prog} (B IRTy′.* C) PPlace.out-mode (falloc PCG.SETTLE)
                              PPlace.cont-alloc v (floc PCG.SETTLE)
              field-place {v} p =
                subst (λ st → ResultPlace {prog = prog} (B IRTy′.* C) PPlace.out-mode (falloc st) PPlace.cont-alloc v (floc st))
                      (sym settle≡place)
                      (subst (λ w → ResultPlace {prog = prog} (B IRTy′.* C) PPlace.out-mode (falloc PPlace.u10) PPlace.cont-alloc w (floc PPlace.u10))
                             (done-value (trans (sym res-pair) p))
                             PPlace.place)

              field-stack : ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                          → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                          → SMCore.MemOps.readLoc (floc PCG.SETTLE) (AtStack fr j) ≡ SMCore.MemOps.readLoc s (AtStack fr j)
              field-stack = at-settle {λ st → ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                                       → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                                       → SMCore.MemOps.readLoc (floc st) (AtStack fr j) ≡ SMCore.MemOps.readLoc s (AtStack fr j)}
                              PPresF.stack-pres-pair

              field-heap : ∀ (hl : HeapLocation)
                         → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                         → SMCore.MemOps.readLoc (floc PCG.SETTLE) (AtDynamic hl) ≡ SMCore.MemOps.readLoc s (AtDynamic hl)
              field-heap = at-settle {λ st → ∀ (hl : HeapLocation)
                                      → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                                      → SMCore.MemOps.readLoc (floc st) (AtDynamic hl) ≡ SMCore.MemOps.readLoc s (AtDynamic hl)}
                             PPresF.heap-pres-pair

              -- the SAME chain names `PCG.RUN` is built from (`PCF.chainF`,
              -- `PCG.chainG`), so the conclusion matches `RUN` after one
              -- unfolding instead of by normalising both runs' events
              -- (profile 2026-09-30: this call was 91% of the module).
              -- `RUN` split by its OWN pieces (`PCG.RUN-*`), not by `Proof`'s
              -- copies of them (plan 0.144, the `context-form-mismatch` pattern).
              ft-run : chain-events PCG.RUN ≡ chain-events PCG.RUN-F ++ chain-events PCG.chainG
              ft-run = PCG.RUN-events

              ft-calls : chain-events PCG.RUN-F ++ chain-events PCG.chainG ≡ esF ++ esG
              ft-calls = cong₂ _++_ tf tg

              field-traces : chain-events PCG.RUN ≡ eventsAt s E
              field-traces = trans ft-run (trans ft-calls (sym ev-pair))

              field-progress : k ≤ budgetLeft k (resultAt s E) + chain-ctrls PCG.RUN
              field-progress =
                subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls PCG.RUN) (sym res-pair)
                      (bind-arith rC progF
                         (subst (λ ρ → rB ≤ budgetLeft rB ρ + chain-ctrls (VR.run vrg)) rgeq (VR.progress vrg))
                         PCG.RUN-ctrls)

              field-frame : current-frame (falloc PCG.SETTLE) ≡ current-frame alloc
              field-frame = at-settle {λ st → current-frame (falloc st) ≡ current-frame alloc}
                              (PPresG.frame-pres-pair rgeq)

              field-frames : saved-frames (falloc PCG.SETTLE) ≡ saved-frames alloc
              field-frames = at-settle {λ st → saved-frames (falloc st) ≡ saved-frames alloc}
                               (PPresG.frames-pres-pair rgeq)

              field-bf : ∀ (m : ℕ) (loc : ValueLocation FS)
                       → BeforeFrontier (record alloc { next-slot = m }) loc
                       → BeforeFrontier (record (falloc PCG.SETTLE) { next-slot = m }) loc
              field-bf = at-settle {λ st → ∀ (m : ℕ) (loc : ValueLocation FS)
                                     → BeforeFrontier (record alloc { next-slot = m }) loc
                                     → BeforeFrontier (record (falloc st) { next-slot = m }) loc}
                           PPresG.bf-mono-pair

              result : MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl rs k
              result = record
                { value-realized =
                    realized PCG.STEPS PCG.SETTLE PPlace.out-mode PPlace.cont-alloc
                             PCG.RUN (λ _ → PCG.LIVE) (λ _ → PCG.ATEND)
                             not-stopped
                             (λ _ → PCG.NORET) (λ _ → PCG.NOLINK)
                             field-log field-place field-progress
                             (λ _ → field-stack) (λ _ → field-heap)
                             (λ _ → field-frame) (λ _ → field-bf) (λ _ → field-frames)
                ; traces-agree = field-traces
                }
