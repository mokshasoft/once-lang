-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair
--
-- D211: `⟨ f , g ⟩` — THE ASSEMBLY.
--
-- The clusters the clause is made of live under `Pair/`:
--   * `Pair.Chain` — the run's states: the prologue (`PairChain`), what
--     follows `f` (`PairChainF`) and what follows `g` (`PairChainG`);
--   * `Pair.Place` — the heap node and `ResultPlace`;
--   * `Pair.Pres`  — the D206/D208/D210 preservation quartet and the
--     five-segment event splice;
--   * `Pair.Proof` — the clause's binders and `f`'s half (`PairProof`).
-- This module is the rest of the WIRING: `g`'s half and the dispatch.
--
-- What is written here and in none of the clusters:
--
--   * `inpF-of` / `inpG-of` — the two `InputAt` transports. Without them
--     neither induction hypothesis can be applied at all, so nothing in any
--     cluster is reachable.
--   * `input1-m2` — the keystone's actual payoff: after `restore-input
--     backup`, `Input1` holds what it held at entry, so `g` receives the
--     input `f` received. `PairChain` builds `wf-restore` and stops one line
--     short of spending it.
--   * `ns-fsF`/`ns-m2`/`ns-gs` and `hr-mid`/`hr-gs` — the allocator
--     bookkeeping `PairPlace` takes as parameters. `next-slot` stability
--     needs `AllSlotStable prog`, which is a clause binder and therefore
--     available nowhere inside the `Pair/` clusters.
--   * `vr-heap-mono` — "a run only grows the heap frontier". Not a
--     `ValueRealized` field and nowhere in the tree; derivable from `bf-mono`
--     alone, at a synthetic reference one below the caller's frontier.
--
-- WHY SPLIT. Each file must check within the 30 s per-module cap, and one
-- pass over all the clusters plus the fifteen-field record does not; split,
-- each cluster is read back from its interface.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore
import Once.CCC.FrameSemantics as FrameSemantics′

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; restore-input; readReg; Output; module LocState; module AllocState)
open AllocState using (next-slot; next-heap-ref; current-frame)
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
import Once.Internal.Trace as TM
open import Once.Internal.Res using (Res; stopped; returns; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft; done-value)

module PairAsm {FS : FrameSemantics} where
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
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false) (inp : InputAt {A} mIn alloc x s) (k : ℕ)
    where
      open PairProof ihf ihg n l prog base ss cr span bl la mIn x s alloc cl rs n≤ nh inp k

      -- `f`'s control steps, as its chain inside the pair's runs.
      ctrlsF : chain-ctrls (VR.run vrf) ≡ chain-ctrls chainF₀
      ctrlsF = sym (chain-ctrls-subst-start (sym PC.handF) (VR.run vrf))

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

              module PPlace = PairPlace {B} {C} n alloc n≤ PCF.fsF (VR.settle vrg)
                                PCF.cf-fsF PCG.cf-fsG ns-fsF ns-gs hr-gs
                                vB vC
                                (VR.out-mode vrf) (VR.out-mode vrg)
                                (VR.cont-alloc vrf) (VR.cont-alloc vrg)
                                (VR.place vrf rfeq) (VR.place vrg rgeq)
                                mem-F→G fst-cell-gs

              module PPresF = PPresG.Fill PPlace.rdi-u6 PPlace.rdi-u8

              -- The record's fields, each NAMED AT ITS TYPE: the expected types
              -- mention `PCG.SETTLE`/`PCG.RUN`, the suppliers their own states,
              -- and stating each once keeps the conversion between them in
              -- one place (and lets a profile see which one costs).
              E : TM.T (Ap ⟦ B IRTy′.* C ⟧)
              E = ⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k

              field-log : SMCore.LocState.ev-log (floc PCG.SETTLE) ≡ SMCore.LocState.ev-log s ++ eventsAt s E
              field-log =
                trans (log-silent PCG.tail-chain _ refl)
                (trans log-fg
                (trans (++-assoc h esF esG) (cong (h ++_) (sym ev-pair))))

              -- plan 0.98: the premise binds `v`; `res-pair` says what the pair
              -- actually returned, and `done-value` identifies the two.
              field-place : ∀ {v r} → resultAt s E ≡ returns (done v r)
                          → ResultPlace (B IRTy′.* C) PPlace.out-mode (falloc PCG.SETTLE)
                              PPlace.cont-alloc v (floc PCG.SETTLE)
              field-place p = subst (λ w → ResultPlace _ _ _ _ w _)
                                    (done-value (trans (sym res-pair) p))
                                    PPlace.place

              field-stack : ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                          → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                          → SMCore.MemOps.readLoc (floc PCG.SETTLE) (AtStack fr j) ≡ SMCore.MemOps.readLoc s (AtStack fr j)
              field-stack = PPresF.stack-pres-pair

              field-heap : ∀ (hl : HeapLocation)
                         → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                         → SMCore.MemOps.readLoc (floc PCG.SETTLE) (AtDynamic hl) ≡ SMCore.MemOps.readLoc s (AtDynamic hl)
              field-heap = PPresF.heap-pres-pair

              -- the SAME chain names `PCG.RUN` is built from (`PCF.chainF`,
              -- `PCG.chainG`), so the conclusion matches `RUN` after one
              -- unfolding instead of by normalising both runs' events
              -- (profile 2026-09-30: this call was 91% of the module).
              field-traces : chain-events PCG.RUN ≡ eventsAt s E
              field-traces =
                trans (PT.pair-chain-events PC.pre-chain PCF.chainF PCF.mid-chain
                               PCG.chainG PCG.tail-chain refl refl refl)
                      (trans (cong₂ _++_ tf tg) (sym ev-pair))

              field-progress : k ≤ budgetLeft k (resultAt s E) + chain-ctrls PCG.RUN
              field-progress =
                subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls PCG.RUN) (sym res-pair)
                      (bind-arith rC progF
                         (subst (λ ρ → rB ≤ budgetLeft rB ρ + chain-ctrls (VR.run vrg)) rgeq (VR.progress vrg))
                         PCG.RUN-ctrls)

              result : MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl rs k
              result = record
                { value-realized =
                    realized PCG.STEPS PCG.SETTLE PPlace.out-mode PPlace.cont-alloc
                             PCG.RUN (λ _ → PCG.LIVE) (λ _ → PCG.ATEND)
                             not-stopped
                             (λ _ → PCG.NORET) (λ _ → PCG.NOLINK)
                             field-log field-place field-progress
                             (λ _ → field-stack) (λ _ → field-heap)
                             (λ _ → PPresG.frame-pres-pair rgeq) (λ _ → PPresG.bf-mono-pair)
                ; traces-agree = field-traces
                }

          -- `g`'s chain and the run up to its settle state, shared by the
          -- branches where `g` does not reach the tail.
          chain-to-g : FlatSteps prog (2 + (VR.steps vrf + (2 + VR.steps vrg))) (entry-flat base s alloc cl rs) (VR.settle vrg)
          chain-to-g = FlatSteps-++ PC.pre-chain (FlatSteps-++ chainF₀ (FlatSteps-++ PCF.mid-chain chainG₀))

          dispatch-g : (ρ : Res (Ap ⟦ C ⟧)) → resultAt (floc PCF.m2) (⟪ evalᴰ g x ⟫ rB) ≡ ρ
                     → MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl rs k

          -- ── `g` ENDED THE PROGRAM ───────────────────────────────────
          -- Four segments run, not five: the nine-row tail that builds the
          -- pair node never executes, so there is no pair value to place —
          -- and the observable is still `dEvF ++ dEvG`, because a stopped
          -- `g` contributes everything it emitted before stopping.
          dispatch-g stopped rgeq = record
            { value-realized =
                realized (2 + (VR.steps vrf + (2 + VR.steps vrg)))
                         (VR.settle vrg) (VR.out-mode vrg) (VR.cont-alloc vrg)
                         chain-to-g
                         absurd-g (λ p → case trans (sym res-g) p of λ ())
                         (λ _ → proj₁ (VR.stops vrg sgeq)
                              , trans (proj₂ (VR.stops vrg sgeq))
                                      (chain-left (FlatSteps-++ PC.pre-chain (FlatSteps-++ chainF₀ PCF.mid-chain)) PCF.nhM2))
                         (λ p → case trans (sym res-g) p of λ ()) (λ _ → VR.no-link vrg ncG)
                         (trans log-fg (trans (++-assoc h esF esG) (cong (h ++_) (sym ev-pair-g))))
                         (λ p → case trans (sym res-g) p of λ ())
                         (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chain-to-g) (sym res-g) (m≤m+n k _))
                         (λ _ fr j b → PPresG.mem-pres-to-gs (AtStack fr j) b)
                         (λ _ hl b → PPresG.mem-pres-to-gs (AtDynamic hl) b)
                         (λ p → case trans (sym res-g) p of λ ())
                         (λ _ → PPresG.bf-to-gs)
            ; traces-agree =
                trans (PT.pair-chain-events-g PC.pre-chain chainF₀ PCF.mid-chain chainG₀ refl refl)
                      (trans (cong₂ _++_ tf tg) (sym ev-pair-g))
            }
            where
              ncG : NotCut (resultAt (floc PCF.m2) (⟪ evalᴰ g x ⟫ rB))
              ncG = subst NotCut (sym rgeq) tt

              module PPresG = PPres ncG

              sgeq : stopsAt (floc PCF.m2) (⟪ evalᴰ g x ⟫ rB) ≡ true
              sgeq = cong is-stopped rgeq

              PR≡ : runAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ (esF ++ esG , stopped)
              PR≡ = inner-run stopped rgeq

              res-g : resultAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ stopped
              res-g = cong proj₂ PR≡

              ev-pair-g : eventsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ esF ++ esG
              ev-pair-g = cong proj₁ PR≡

              absurd-g : ∀ {X : Set} → stopsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ false → X
              absurd-g p = case trans (sym (cong is-stopped res-g)) p of λ ()

          -- ── `g` WAS CUT: as a stopped `g`, but the machine is still running.
          dispatch-g (returns cut) rgeq = record
            { value-realized =
                realized (2 + (VR.steps vrf + (2 + VR.steps vrg)))
                         (VR.settle vrg) (VR.out-mode vrg) (VR.cont-alloc vrg)
                         chain-to-g
                         (λ _ → VR.live vrg (cong is-stopped rgeq))
                         (λ p → case trans (sym res-g) p of λ ())
                         (λ p → case trans (sym (cong is-stopped res-g)) p of λ ())
                         (λ p → case trans (sym res-g) p of λ ()) (cut-absurd res-g)
                         (trans log-fg (trans (++-assoc h esF esG) (cong (h ++_) (sym ev-pair-g))))
                         (λ p → case trans (sym res-g) p of λ ())
                         (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chain-to-g) (sym res-g)
                                (bind-arith 0 progF
                                   (subst (λ ρ → rB ≤ budgetLeft rB ρ + chain-ctrls (VR.run vrg)) rgeq (VR.progress vrg))
                                   (subst₂ (λ a b → a + b ≤ chain-ctrls chain-to-g) (sym ctrlsF) (sym ctrlsG)
                                           (ctrls-4 PC.pre-chain chainF₀ PCF.mid-chain chainG₀))))
                         (cut-absurd res-g) (cut-absurd res-g) (λ p → case trans (sym res-g) p of λ ()) (cut-absurd res-g)
            ; traces-agree =
                trans (PT.pair-chain-events-g PC.pre-chain chainF₀ PCF.mid-chain chainG₀ refl refl)
                      (trans (cong₂ _++_ tf tg) (sym ev-pair-g))
            }
            where
              PR≡ : runAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ (esF ++ esG , returns cut)
              PR≡ = inner-run (returns cut) rgeq

              res-g : resultAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ returns cut
              res-g = cong proj₂ PR≡

              ev-pair-g : eventsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ esF ++ esG
              ev-pair-g = cong proj₁ PR≡

          -- ── BOTH REACHED THEIR END — the pair is assembled. ──────────
          dispatch-g (returns (done vC rC)) rgeq = ReturnsG.result vC rC rgeq

      dispatch : (ρ : Res (Ap ⟦ B ⟧)) → resultAt (floc PC.PR.p2) (⟪ evalᴰ f x ⟫ k) ≡ ρ
               → MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl rs k

      -- ── `f` ENDED THE PROGRAM ───────────────────────────────────────
      -- The pair's run is the prologue and `f`; the two mid rows, `g` and the
      -- nine-row tail never execute, and the pair's observable is `f`'s.
      dispatch stopped rfeq = record
        { value-realized =
            realized (2 + VR.steps vrf) (VR.settle vrf)
                     (VR.out-mode vrf) (VR.cont-alloc vrf)
                     (FlatSteps-++ PC.pre-chain chainF₀)
                     absurd-f (λ p → case trans (sym res-f) p of λ ())
                     (λ _ → proj₁ (VR.stops vrf sfeq) , trans (proj₂ (VR.stops vrf sfeq)) (chain-left PC.pre-chain PC.nh2))
                     (λ p → case trans (sym res-f) p of λ ()) (λ _ → VR.no-link vrf ncF)
                     (trans (VR.log vrf) (trans (cong (_++ esF) logP2) (cong (h ++_) (sym ev-pair-f))))
                     (λ p → case trans (sym res-f) p of λ ())
                     (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (FlatSteps-++ PC.pre-chain chainF₀)) (sym res-f) (m≤m+n k _))
                     (λ _ fr j b → mem-to-fsF (AtStack fr j) b)
                     (λ _ hl b → mem-to-fsF (AtDynamic hl) b)
                     (λ p → case trans (sym res-f) p of λ ())
                     (λ _ m loc b → VR.bf-mono vrf ncF m loc b)
        ; traces-agree =
            trans (PT.pair-chain-events-f PC.pre-chain chainF₀ refl) (trans tf (sym ev-pair-f))
        }
        where
          ncF : NotCut (resultAt (floc PC.PR.p2) (⟪ evalᴰ f x ⟫ k))
          ncF = subst NotCut (sym rfeq) tt

          mem-to-fsF : ∀ (loc : ValueLocation FS)
                     → BeforeFrontier (record alloc { next-slot = n }) loc
                     → SMCore.MemOps.readLoc (floc (VR.settle vrf)) loc ≡ SMCore.MemOps.readLoc s loc
          mem-to-fsF loc b = trans (vr-mem-pres vrf ncF loc (bf-f loc b)) (mem-to-p2 loc b)

          sfeq : stopsAt (floc PC.PR.p2) (⟪ evalᴰ f x ⟫ k) ≡ true
          sfeq = cong is-stopped rfeq

          PR≡ : runAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ (esF , stopped)
          PR≡ = pair-run stopped rfeq

          res-f : resultAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ stopped
          res-f = cong proj₂ PR≡

          ev-pair-f : eventsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ esF
          ev-pair-f = cong proj₁ PR≡

          absurd-f : ∀ {X : Set} → stopsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ false → X
          absurd-f p = case trans (sym (cong is-stopped res-f)) p of λ ()

      -- ── `f` WAS CUT: the budget ran out inside `f`. ─────────────────
      dispatch (returns cut) rfeq = record
        { value-realized =
            realized (2 + VR.steps vrf) (VR.settle vrf)
                     (VR.out-mode vrf) (VR.cont-alloc vrf)
                     (FlatSteps-++ PC.pre-chain chainF₀)
                     (λ _ → VR.live vrf (cong is-stopped rfeq))
                     (λ p → case trans (sym res-f) p of λ ())
                     (λ p → case trans (sym (cong is-stopped res-f)) p of λ ())
                     (λ p → case trans (sym res-f) p of λ ()) (cut-absurd res-f)
                     (trans (VR.log vrf) (trans (cong (_++ esF) logP2) (cong (h ++_) (sym ev-pair-f))))
                     (λ p → case trans (sym res-f) p of λ ())
                     (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (FlatSteps-++ PC.pre-chain chainF₀)) (sym res-f)
                            (progress-≤ {b = 0} (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (VR.run vrf)) rfeq (VR.progress vrf))
                                        (≤-trans (≤-reflexive ctrlsF) (ctrls-≤ʳ PC.pre-chain chainF₀))))
                     (cut-absurd res-f) (cut-absurd res-f) (λ p → case trans (sym res-f) p of λ ()) (cut-absurd res-f)
        ; traces-agree =
            trans (PT.pair-chain-events-f PC.pre-chain chainF₀ refl) (trans tf (sym ev-pair-f))
        }
        where
          PR≡ : runAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ (esF , returns cut)
          PR≡ = pair-run (returns cut) rfeq

          res-f : resultAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ returns cut
          res-f = cong proj₂ PR≡

          ev-pair-f : eventsAt s (⟪ evalᴰ ⟨ f , g ⟩ x ⟫ k) ≡ esF
          ev-pair-f = cong proj₁ PR≡

      -- ── `f` REACHED ITS END ─────────────────────────────────────────
      dispatch (returns (done vB rB)) rfeq = ReturnsB.dispatch-g vB rB rfeq (resultAt (floc PCF.m2) (⟪ evalᴰ g x ⟫ rB)) refl
        where module PCF = PairChainF f g n l prog base s alloc cl rs n≤ nh span vrf rfeq

  obs-correct-pair-proof :
    ∀ {A B C} {f : IR A B} {g : IR A C}
    → IRObsCorrectF f → IRObsCorrectF g → IRObsCorrectF ⟨ f , g ⟩
  obs-correct-pair-proof {A} {B} {C} {f} {g} ihf ihg n l prog base
                         ss cr span bl la mIn x s alloc cl n≤ nh inp k rs =
    PairProofB.dispatch ihf ihg n l prog base ss cr span bl la mIn x s alloc cl rs n≤ nh inp k
      (resultAt (floc (PairChain.PR.p2 f g n l prog base s alloc cl rs n≤ nh span)) (⟪ evalᴰ f x ⟫ k)) refl
