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

open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Chain    o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Place o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Proof o tbl
open import Data.List.Properties using (++-identityʳ)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM
open import Once.Res using (Res; stopped; returns; is-stopped; returns-inj)

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
    (mIn : AllocMode) (x : DT.⟦ A ⟧ᴰᴵ) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false) (inp : InputAt {A} mIn alloc x s) (k : ℕ)
    where
      open PairProof ihf ihg n l prog base ss cr span bl la mIn x s alloc cl n≤ nh inp k

      module ReturnsB (vB : ⟦ B ⟧) (rfeq : resultAt (floc PC.PR.p2) (evalᴰ f x) ≡ returns vB) where
          open Returns vB rfeq

          module ReturnsG (vC : ⟦ C ⟧) (rgeq : resultAt (floc PCF.m2) (evalᴰ g x) ≡ returns vC) where
              sgeq : stopsAt (floc PCF.m2) (evalᴰ g x) ≡ false
              sgeq = cong is-stopped rgeq

              -- WHAT THE PAIR RUNS AND RETURNS: both calls' events, and `f`'s
              -- value with `g`'s, assembled by the inner `returnT`.
              PR≡ : runAt s (evalᴰ ⟨ f , g ⟩ x) ≡ (esF ++ (esG ++ []) , returns (vB , vC))
              PR≡ = inner-run (returns vC) rgeq

              res-pair : resultAt s (evalᴰ ⟨ f , g ⟩ x) ≡ returns (vB , vC)
              res-pair = cong proj₂ PR≡

              ev-pair : eventsAt s (evalᴰ ⟨ f , g ⟩ x) ≡ esF ++ esG
              ev-pair = trans (cong proj₁ PR≡) (cong (esF ++_) (++-identityʳ esG))

              not-stopped : ∀ {X : Set} → stopsAt s (evalᴰ ⟨ f , g ⟩ x) ≡ true → X
              not-stopped p = case trans (sym p) (cong is-stopped res-pair) of λ ()

              module PCG = PairChainG f g n l prog base s alloc cl n≤ nh span vrf sfeq vrg sgeq

              ----------------------------------------------------------------
              -- `PairPlace`'s five non-trivial parameters.
              ----------------------------------------------------------------
              runG≡ : exec-flat (VR.steps vrg) prog
                        (entry-flat PCF.bg (floc PCF.m2) (falloc PCF.m2)
                                    (fclosure PCF.m2))
                      ≡ PCG.fsG
              runG≡ = trans (cong (λ m → exec-flat m prog
                                           (entry-flat PCF.bg (floc PCF.m2)
                                              (falloc PCF.m2) (fclosure PCF.m2)))
                                  (sym (+-identityʳ (VR.steps vrg))))
                            (exec-flat-steps (VR.run vrg) 0)

              ns-gs : next-slot (falloc PCG.fsG) ≡ next-slot alloc
              ns-gs = trans (trans (cong (λ st → next-slot (falloc st)) (sym runG≡))
                                   (flat-run-keeps-next-slot (VR.steps vrg) prog ss
                                      PCF.bg (floc PCF.m2) (falloc PCF.m2)
                                      (fclosure PCF.m2)))
                            ns-m2

              hr-gs : next-heap-ref (falloc PCF.fsF) ≤ next-heap-ref (falloc PCG.fsG)
              hr-gs = ≤-trans (≤-reflexive (sym hr-mid)) (vr-heap-mono vrg)

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
                      → MemOps.readLoc (floc PCG.fsG) loc
                        ≡ MemOps.readLoc (floc PCF.fsF) loc
              mem-F→G loc b =
                trans (vr-mem-pres vrg loc (bf-fsF→g loc b))
                (trans (mem-untouched (restore-input n) (floc PCF.m1) (falloc PCF.m1) loc
                          Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
                       (store-slot-preserves-before (suc n) (floc PCF.fsF)
                          (falloc PCF.fsF) (falloc PCF.fsF) loc refl
                          (≤-trans (≤-reflexive ns-fsF) (≤-trans n≤ (n≤1+n n))) b))

              fst-cell-gs : MemOps.readLoc (floc PCG.fsG)
                              (AtStack (current-frame alloc) (suc n))
                          ≡ just (readReg (regs (floc PCF.fsF)) Output)
              fst-cell-gs =
                trans (vr-mem-pres vrg (AtStack (current-frame alloc) (suc n))
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

              module PPresF = PPres.Fill PPlace.rdi-u6 PPlace.rdi-u8

              -- The record's fields, each NAMED AT ITS TYPE: the expected types
              -- mention `PCG.SETTLE`/`PCG.RUN`, the suppliers their own states,
              -- and stating each once keeps the conversion between them in
              -- one place (and lets a profile see which one costs).
              E : TM.T ⟦ B IRTy.* C ⟧
              E = evalᴰ ⟨ f , g ⟩ x

              field-log : LocState.ev-log (floc PCG.SETTLE) ≡ LocState.ev-log s ++ eventsAt s E
              field-log =
                trans (log-silent PCG.tail-chain _ refl)
                (trans log-fg
                (trans (++-assoc h esF esG) (cong (h ++_) (sym ev-pair))))

              -- plan 0.98: the premise binds `v`; `res-pair` says what the pair
              -- actually returned, and `returns-inj` identifies the two.
              field-place : ∀ {v} → resultAt s E ≡ returns v
                          → ResultPlace (B IRTy.* C) PPlace.out-mode (falloc PCG.SETTLE)
                              PPlace.cont-alloc v (floc PCG.SETTLE)
              field-place p = subst (λ w → ResultPlace _ _ _ _ w _)
                                    (returns-inj (trans (sym res-pair) p))
                                    PPlace.place

              field-stack : ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                          → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                          → MemOps.readLoc (floc PCG.SETTLE) (AtStack fr j) ≡ MemOps.readLoc s (AtStack fr j)
              field-stack = PPresF.stack-pres-pair

              field-heap : ∀ (hl : HeapLocation)
                         → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                         → MemOps.readLoc (floc PCG.SETTLE) (AtDynamic hl) ≡ MemOps.readLoc s (AtDynamic hl)
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

              result : MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl k
              result = record
                { value-realized =
                    realized PCG.STEPS PCG.SETTLE PPlace.out-mode PPlace.cont-alloc
                             PCG.RUN (λ _ → PCG.LIVE) (λ _ → PCG.ATEND)
                             not-stopped
                             PCG.NORET PCG.NOLINK
                             field-log field-place field-stack field-heap
                             PPres.frame-pres-pair PPres.bf-mono-pair
                ; traces-agree = field-traces
                }

          dispatch-g : (r : Res ⟦ C ⟧) → resultAt (floc PCF.m2) (evalᴰ g x) ≡ r
                     → MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl k

          -- ── `g` ENDED THE PROGRAM ───────────────────────────────────
          -- Four segments run, not five: the nine-row tail that builds the
          -- pair node never executes, so there is no pair value to place —
          -- and the observable is still `dEvF ++ dEvG`, because a stopped
          -- `g` contributes everything it emitted before stopping.
          dispatch-g stopped rgeq = record
            { value-realized =
                realized (2 + (VR.steps vrf + (2 + VR.steps vrg)))
                         (VR.settle vrg) (VR.out-mode vrg) (VR.cont-alloc vrg)
                         (FlatSteps-++ PC.pre-chain
                           (FlatSteps-++ chainF₀ (FlatSteps-++ PCF.mid-chain chainG₀)))
                         absurd-g absurd-g (λ _ → VR.stops vrg sgeq)
                         (VR.no-ret vrg) (VR.no-link vrg)
                         (trans log-fg (trans (++-assoc h esF esG) (cong (h ++_) (sym ev-pair-g))))
                         absurd-g-res
                         (λ fr j b → PPres.mem-pres-to-gs (AtStack fr j) b)
                         (λ hl b → PPres.mem-pres-to-gs (AtDynamic hl) b)
                         PPres.frame-pres-to-gs
                         PPres.bf-to-gs
            ; traces-agree =
                trans (PT.pair-chain-events-g PC.pre-chain chainF₀ PCF.mid-chain chainG₀ refl refl)
                      (trans (cong₂ _++_ tf tg) (sym ev-pair-g))
            }
            where
              sgeq : stopsAt (floc PCF.m2) (evalᴰ g x) ≡ true
              sgeq = cong is-stopped rgeq

              PR≡ : runAt s (evalᴰ ⟨ f , g ⟩ x) ≡ (esF ++ esG , stopped)
              PR≡ = inner-run stopped rgeq

              ev-pair-g : eventsAt s (evalᴰ ⟨ f , g ⟩ x) ≡ esF ++ esG
              ev-pair-g = cong proj₁ PR≡

              absurd-g : ∀ {X : Set} → stopsAt s (evalᴰ ⟨ f , g ⟩ x) ≡ false → X
              absurd-g p = case trans (sym (cong (λ r → is-stopped (proj₂ r)) PR≡)) p of λ ()

              absurd-g-res : ∀ {X : Set} {v}
                           → resultAt s (evalᴰ ⟨ f , g ⟩ x) ≡ returns v → X
              absurd-g-res p = case trans (sym (cong proj₂ PR≡)) p of λ ()

          -- ── BOTH REACHED THEIR END — the pair is assembled. ──────────
          dispatch-g (returns vC) rgeq = ReturnsG.result vC rgeq

      dispatch : (r : Res ⟦ B ⟧) → resultAt (floc PC.PR.p2) (evalᴰ f x) ≡ r
               → MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl k

      -- ── `f` ENDED THE PROGRAM ───────────────────────────────────────
      -- The pair's run is the prologue and `f`; the two mid rows, `g` and the
      -- nine-row tail never execute, and the pair's observable is `f`'s.
      dispatch stopped rfeq = record
        { value-realized =
            realized (2 + VR.steps vrf) (VR.settle vrf)
                     (VR.out-mode vrf) (VR.cont-alloc vrf)
                     (FlatSteps-++ PC.pre-chain chainF₀)
                     absurd-f absurd-f (λ _ → VR.stops vrf sfeq)
                     (VR.no-ret vrf) (VR.no-link vrf)
                     (trans (VR.log vrf) (trans (cong (_++ esF) logP2) (cong (h ++_) (sym ev-pair-f))))
                     absurd-f-res
                     (λ fr j b → mem-to-fsF (AtStack fr j) b)
                     (λ hl b → mem-to-fsF (AtDynamic hl) b)
                     (VR.frame-pres vrf)
                     (λ m loc b → VR.bf-mono vrf m loc b)
        ; traces-agree =
            trans (PT.pair-chain-events-f PC.pre-chain chainF₀ refl) (trans tf (sym ev-pair-f))
        }
        where
          mem-to-fsF : ∀ (loc : ValueLocation FS)
                     → BeforeFrontier (record alloc { next-slot = n }) loc
                     → MemOps.readLoc (floc (VR.settle vrf)) loc ≡ MemOps.readLoc s loc
          mem-to-fsF loc b = trans (vr-mem-pres vrf loc (bf-f loc b)) (mem-to-p2 loc b)

          sfeq : stopsAt (floc PC.PR.p2) (evalᴰ f x) ≡ true
          sfeq = cong is-stopped rfeq

          PR≡ : runAt s (evalᴰ ⟨ f , g ⟩ x) ≡ (esF , stopped)
          PR≡ = pair-run stopped rfeq

          ev-pair-f : eventsAt s (evalᴰ ⟨ f , g ⟩ x) ≡ esF
          ev-pair-f = cong proj₁ PR≡

          absurd-f : ∀ {X : Set} → stopsAt s (evalᴰ ⟨ f , g ⟩ x) ≡ false → X
          absurd-f p = case trans (sym (cong (λ r → is-stopped (proj₂ r)) PR≡)) p of λ ()

          -- …and the pair has NO result, so `place`'s premise refutes itself.
          absurd-f-res : ∀ {X : Set} {v}
                       → resultAt s (evalᴰ ⟨ f , g ⟩ x) ≡ returns v → X
          absurd-f-res p = case trans (sym (cong proj₂ PR≡)) p of λ ()

      -- ── `f` REACHED ITS END ─────────────────────────────────────────
      dispatch (returns vB) rfeq = ReturnsB.dispatch-g vB rfeq (resultAt (floc PCF.m2) (evalᴰ g x)) refl
        where module PCF = PairChainF f g n l prog base s alloc cl n≤ nh span vrf (cong is-stopped rfeq)

  obs-correct-pair-proof :
    ∀ {A B C} {f : IR A B} {g : IR A C}
    → IRObsCorrectF f → IRObsCorrectF g → IRObsCorrectF ⟨ f , g ⟩
  obs-correct-pair-proof {A} {B} {C} {f} {g} ihf ihg n l prog base
                         ss cr span bl la mIn x s alloc cl n≤ nh inp k =
    PairProofB.dispatch ihf ihg n l prog base ss cr span bl la mIn x s alloc cl n≤ nh inp k
      (resultAt (floc (PairChain.PR.p2 f g n l prog base s alloc cl n≤ nh span)) (evalᴰ f x)) refl
