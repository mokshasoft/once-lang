-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair
--
-- D211: `⟨ f , g ⟩` — THE ASSEMBLY.
--
-- The clusters the clause is made of live under `Pair/`:
--   * `Pair.Chain` — the run's states: the prologue (`PairChain`), what
--     follows `f` (`PairChainF`) and what follows `g` (`PairChainG`), and
--     the five-segment event splice (`PairTrace`, `PairChainG.RUN-events`);
--   * `Pair.Place` — the heap node and `ResultPlace`;
--   * `Pair.Pres`  — the D206/D208/D210 preservation quartet;
--   * `Pair.Proof` — the clause's binders and `f`'s half (`PairProof`);
--   * `Pair.Both`  — both halves returned: the pair's fifteen-field record.
-- This module is the rest of the WIRING: `g`'s other outcomes and the dispatch.
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
-- WHY SPLIT. Each file must check within the per-module limit (plan 0.144:
-- 50 s and 3 GB), and one pass over all the clusters plus the fifteen-field
-- record does not; split, each cluster is read back from its interface.
--
-- WHAT KEEPS IT FAST (plan 0.144, 739 s → 48 s; profile per definition):
--   * the settle state is met through the OPAQUE `NineSteps.u10ᵒ`
--     (`settle≡place`, `settle≡pres`) and the clusters' facts are moved along
--     those two equalities by `subst`; met directly, the three families'
--     spellings of it are identified by evaluating the nine rows (~100 s each);
--   * every implicit that would be solved against a computed term is pinned
--     (`field-place`'s `{prog = prog}`: >20 min unpinned);
--   * facts about `PCG.RUN` are stated in `Pair.Chain`, where `RUN`'s pieces
--     are its own names (`RUN-events`; the straight segments' `[]`s).
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
open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)
open LocState using (halted; regs)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Chain    o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Place o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Proof o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Both o tbl
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

module PairAsm {FS : FrameSemantics} where
  open Core  {FS}
  open Mach  {FS}
  open PairC {FS}
  open PairPlaceC {FS}

  open PairProofC {FS}
  open PairBothC {FS} using () renaming (module PairProofB to Both)

  module PairProofB {A B C} {f : IR A B} {g : IR A C}
    (ihf : IRObsCorrectF f) (ihg : IRObsCorrectF g) (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩)) (bl : BlocksAt prog (blocks n l ⟨ f , g ⟩))
    (la : LabelsAt prog base (emitted n l ⟨ f , g ⟩))
    (mIn : AllocMode) (x : ValueDomain.⟦ A ⟧ᴰᴵ) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (ns0 : next-slot alloc ≡ 0) (nh : halted s ≡ false) (inp : InputAt {prog = prog} {A} mIn alloc x s) (k : ℕ)
    where
      open PairProof ihf ihg n l prog base ss cr span bl la mIn x s alloc cl rs ns0 nh inp k

      -- `f`'s control steps, as its chain inside the pair's runs.
      ctrlsF : chain-ctrls (VR.run vrf) ≡ chain-ctrls chainF₀
      ctrlsF = sym (chain-ctrls-subst-start (sym PC.handF) (VR.run vrf))

      module ReturnsB (vB : ⟦ B ⟧) (rB : ℕ) (rfeq : resultAt (floc PC.PR.p2) (⟪ evalᴰ f x ⟫ k) ≡ returns (done vB rB)) where
          open Returns vB rB rfeq

          progF : k ≤ rB + chain-ctrls (VR.run vrf)
          progF = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (VR.run vrf)) rfeq (VR.progress vrf)

          ctrlsG : chain-ctrls (VR.run vrg) ≡ chain-ctrls chainG₀
          ctrlsG = sym (chain-ctrls-subst-start (sym PCF.handG) (VR.run vrg))

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
                         (log-assoc h esF esG log-fg ev-pair-g)
                         (λ p → case trans (sym res-g) p of λ ())
                         (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chain-to-g) (sym res-g) (m≤m+n k _))
                         (λ _ fr j b → PPresG.mem-pres-to-gs (AtStack fr j) b)
                         (λ _ hl b → PPresG.mem-pres-to-gs (AtDynamic hl) b)
                         (λ p → case trans (sym res-g) p of λ ())
                         (λ _ → PPresG.bf-to-gs)
                         (λ p → case trans (sym res-g) p of λ ())
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
                         (log-assoc h esF esG log-fg ev-pair-g)
                         (λ p → case trans (sym res-g) p of λ ())
                         (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls chain-to-g) (sym res-g)
                                (bind-arith 0 progF
                                   (subst (λ ρ → rB ≤ budgetLeft rB ρ + chain-ctrls (VR.run vrg)) rgeq (VR.progress vrg))
                                   (subst₂ (λ a b → a + b ≤ chain-ctrls chain-to-g) (sym ctrlsF) (sym ctrlsG)
                                           (ctrls-4 PC.pre-chain chainF₀ PCF.mid-chain chainG₀))))
                         (cut-absurd res-g) (cut-absurd res-g) (λ p → case trans (sym res-g) p of λ ()) (cut-absurd res-g) (λ p → case trans (sym res-g) p of λ ())
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
          dispatch-g (returns (done vC rC)) rgeq =
            Both.ReturnsB.ReturnsG.result ihf ihg n l prog base ss cr span bl la mIn x s alloc cl rs ns0 nh inp k vB rB rfeq vC rC rgeq

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
                     (λ _ m loc b → VR.bf-mono vrf ncF m loc b) (λ p → case trans (sym res-f) p of λ ())
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
                     (cut-absurd res-f) (cut-absurd res-f) (λ p → case trans (sym res-f) p of λ ()) (cut-absurd res-f) (λ p → case trans (sym res-f) p of λ ())
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
      (resultAt (floc (PairChain.PR.p2 f g n l prog base s alloc cl rs (ns≤ {alloc} n n≤) nh span)) (⟪ evalᴰ f x ⟫ k)) refl
