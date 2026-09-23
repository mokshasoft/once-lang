-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.PairAssemble
--
-- D211: `⟨ f , g ⟩` — THE ASSEMBLY.
--
-- `Pair.agda` proves the four clusters the clause is made of — `PairChain`
-- (the five-segment run and the seven control fields), `PairPlace` (the heap
-- node and `ResultPlace`), `PairPres` (the D206/D208/D210 preservation
-- quartet) and `PairTrace` (the two-bind trace split). This module is the
-- fifteenth thing: the WIRING between them.
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
--     available nowhere inside `Pair.agda`'s clusters.
--   * `vr-heap-mono` — "a run only grows the heap frontier". Not a
--     `ValueRealized` field and nowhere in the tree; derivable from `bf-mono`
--     alone, at a synthetic reference one below the caller's frontier.
--
-- WHY ITS OWN FILE. `Pair.agda` is 1835 lines of four independent clusters;
-- assembling them in the same module means holding all four plus the
-- fifteen-field record in one type-checking pass, which does not fit the
-- 5.5 GiB cap the build runs under. Split, `Pair.agda`'s clusters are read
-- back from its interface and only the wiring is elaborated. (Same reason
-- `Pair` itself is not inside `Simple`.)
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.PairAssemble (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o
open import Once.CCC.Codegen.IRObsCorrect.Pair    o
open import Data.Nat using (z≤n)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module PairAsm {FS : FrameSemantics} where

  open Core  {FS}
  open Mach  {FS}
  open PairC {FS}

  ----------------------------------------------------------------------
  -- THE GLUE. Three facts the four clusters consume and none of them
  -- exports, because none of them is about `⟨ f , g ⟩` in particular.
  ----------------------------------------------------------------------

  -- `BeforeFrontier`'s heap constructor, read back. (`stack-before` and
  -- `stack-ancestor` index at `AtStack`, so they do not unify.)
  bf-heap-out : ∀ {a : AllocState {FS}} {hl : HeapLocation}
              → BeforeFrontier a (AtDynamic hl)
              → ref-id (heap-ref hl) < next-heap-ref a
  bf-heap-out (BeforeFrontier.heap-before p) = p

  -- `a ≤ b` from "every predecessor of `a` is below `b`" — the shape the
  -- synthetic-reference argument below produces.
  ≤-from-pred : ∀ {a b : ℕ} → (∀ c → a ≡ suc c → c < b) → a ≤ b
  ≤-from-pred {zero}  fp = z≤n
  ≤-from-pred {suc c} fp = fp c refl

  -- A RUN ONLY GROWS THE HEAP FRONTIER.
  --
  -- Not a `ValueRealized` field and nowhere in the tree, but derivable from
  -- `bf-mono` alone: a reference one below the caller's frontier is live
  -- before the run, hence live after it — which IS the inequality.
  vr-heap-mono : ∀ {prog base A B n l} {ir : IR A B} {x s alloc cl k}
               → (vr : ValueRealized prog base n l ir x s alloc cl k)
               → next-heap-ref alloc
                 ≤ next-heap-ref (falloc (ValueRealized.settle vr))
  vr-heap-mono vr = ≤-from-pred (λ c eq →
    bf-heap-out (ValueRealized.bf-mono vr 0 (AtDynamic (heap-loc (mkHeapRef c) 0))
                   (BeforeFrontier.heap-before (≤-reflexive (sym eq)))))

  ----------------------------------------------------------------------
  -- THE CLAUSE. Every field is one of the four clusters'; what is written
  -- here is only the WIRING — the two induction hypotheses' preconditions
  -- (chiefly the two `InputAt` transports, which is where `restore-input`'s
  -- keystone is actually spent) and the allocator bookkeeping `PairPlace`
  -- asks for.
  ----------------------------------------------------------------------
  obs-correct-pair-proof :
    ∀ {A B C} {f : IR A B} {g : IR A C}
    → IRObsCorrectF f → IRObsCorrectF g → IRObsCorrectF ⟨ f , g ⟩
  obs-correct-pair-proof {A} {B} {C} {f} {g} ihf ihg n l prog base
                         ss cr span bl la mIn x s alloc cl n≤ nh inp k =
    dispatch (TM.stoppedT (evalᴰ f x) k) refl
    where
      module PS = PairShape f g n l
      module PC = PairChain f g n l prog base s alloc cl n≤ nh span
      module PT = PairTrace f g x k
      module VR = ValueRealized

      -- plan 0.91 S2: `ir-to-trace' n l ⟨ f , g ⟩` ends `… , (fb ++ gb)`
      -- (IRToTrace:817), and `PairShape` already names the sites the two
      -- halves are emitted at — `f` at `f-start`/`l`, `g` at `n1`/`l1` — so
      -- the block premise splits on the same `++` the emitter built.
      blocks-f : BlocksAt prog (blocks PS.f-start l f)
      blocks-f = proj₁ (++⁻ (blocks PS.f-start l f) bl)

      blocks-g : BlocksAt prog (blocks PS.n1 PS.l1 g)
      blocks-g = proj₂ (++⁻ (blocks PS.f-start l f) bl)

      -- the caller's window, raised to the fragment's own bound and then to
      -- `f`'s emission frontier.
      bf-n : ∀ (loc : ValueLocation FS) → BeforeFrontier alloc loc
           → BeforeFrontier (record alloc { next-slot = n }) loc
      bf-n = frontier-monotone alloc (record alloc { next-slot = n })
                               refl n≤ ≤-refl

      bf-f : ∀ (loc : ValueLocation FS)
           → BeforeFrontier (record alloc { next-slot = n }) loc
           → BeforeFrontier (record alloc { next-slot = PS.f-start }) loc
      bf-f = frontier-monotone (record alloc { next-slot = n })
                               (record alloc { next-slot = PS.f-start })
                               refl PC.n≤f-start ≤-refl

      ----------------------------------------------------------------
      -- `f`'s INPUT. The two prologue rows write `Output` and slot
      -- `backup = n`, neither of which is inside the caller's window.
      ----------------------------------------------------------------
      memP : ∀ (loc : ValueLocation FS) → BeforeFrontier alloc loc
           → MemOps.readLoc (floc PC.PR.p2) loc ≡ MemOps.readLoc s loc
      memP loc b =
        trans (store-slot-preserves-before n (floc PC.PR.p1) alloc
                 (falloc PC.PR.p1) loc
                 (exec-abstract-preserves-frame mov-to-output s alloc) n≤ b)
              (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl)

      inpF-of : InputAt mIn alloc x s → InputAt mIn alloc x (floc PC.PR.p2)
      inpF-of (in-loc loc vd bf rd) =
        in-loc loc (validityWF-mem-preserved x loc s (floc PC.PR.p2) bf
                      (λ loc' b' → memP loc' b') vd)
               bf (trans PC.PR.input1-p2 rd)
      inpF-of (in-reg fit rd) = in-reg fit (trans PC.PR.input1-p2 rd)
      inpF-of (in-unit e)     = in-unit e

      mrf : MachineRefinesObsF prog (suc (suc base)) PS.f-start l f x
              (floc PC.PR.p2) (falloc PC.PR.p2) (fclosure PC.PR.p2) k
      mrf = ihf PS.f-start l prog (suc (suc base)) ss cr
                (PS.span-f prog base span) blocks-f
                (PS.labels-f prog base la) mIn x
                (floc PC.PR.p2) (falloc PC.PR.p2) (fclosure PC.PR.p2)
                PC.ns-p2 PC.nh2 (inpF-of inp) k

      vrf : ValueRealized prog (suc (suc base)) PS.f-start l f x
              (floc PC.PR.p2) (falloc PC.PR.p2) (fclosure PC.PR.p2) k
      vrf = MachineRefinesObsF.value-realized mrf

      ----------------------------------------------------------------
      -- plan 0.97: `f`'s CHAIN AND ITS TRACE, hoisted out of `PC.WithF`.
      -- `WithF` now takes "`f` reached its end" as a parameter — everything
      -- in it is about what happens AFTER `f` — but these two are about `f`
      -- itself and are needed on the stopped branch too.
      ----------------------------------------------------------------
      chainF₀ : FlatSteps prog (VR.steps vrf) PC.PR.p2 (VR.settle vrf)
      chainF₀ = subst (λ st → FlatSteps prog (VR.steps vrf) st (VR.settle vrf))
                      (sym PC.handF) (VR.run vrf)

      tf : take k (chain-events chainF₀) ≡ take k PT.dEvF
      tf = trans (cong (take k)
                   (chain-events-subst-start (sym PC.handF) (VR.run vrf)))
                 (MachineRefinesObsF.traces-agree mrf)

      -- The two prologue rows, at the window's own bound. (`memP` states the
      -- same thing at `alloc`; the record's field is at `alloc { next-slot = n }`.)
      mem-to-p2 : ∀ (loc : ValueLocation FS)
                → BeforeFrontier (record alloc { next-slot = n }) loc
                → MemOps.readLoc (floc PC.PR.p2) loc ≡ MemOps.readLoc s loc
      mem-to-p2 loc b =
        trans (store-slot-preserves-before n (floc PC.PR.p1)
                 (record alloc { next-slot = n }) (falloc PC.PR.p1) loc
                 (exec-abstract-preserves-frame mov-to-output s alloc) ≤-refl b)
              (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl)

      -- The pair's stoppedness, spelled at the shape `join-st` gives it.
      -- `evalᴰ ⟨ f , g ⟩ x` is `evalᴰ f x >>=T λ b → innerT`, so the outer
      -- flag is `join-st` of `f`'s and the inner bind's.
      st-pair-of : ∀ (sf : TM.Stopped) → TM.stoppedT (evalᴰ f x) k ≡ sf
                 → TM.stoppedT (evalᴰ ⟨ f , g ⟩ x) k
                   ≡ TM.join-st sf (TM.stoppedT PT.innerT PT.kg)
      st-pair-of sf q = cong (λ z → TM.join-st z (TM.stoppedT PT.innerT PT.kg)) q

      ----------------------------------------------------------------
      -- THE SPLIT. Three outcomes, not one: `f` stops, `g` stops, or the
      -- pair is assembled. The first two are plan 0.97's — until it, the
      -- obligation asserted the machine was live and at the end of the
      -- pair's text no matter what the Spec said, which a program that
      -- exits inside `f` cannot satisfy.
      ----------------------------------------------------------------
      dispatch : (sf : TM.Stopped) → TM.stoppedT (evalᴰ f x) k ≡ sf
               → MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl k

      -- ── `f` ENDED THE PROGRAM ───────────────────────────────────────
      -- The pair's run is the prologue and `f`; the two mid rows, `g` and the
      -- nine-row tail never execute, and the pair's observable is `f`'s.
      dispatch true sfeq = record
        { value-realized =
            realized (2 + VR.steps vrf) (VR.settle vrf)
                     (VR.out-mode vrf) (VR.cont-alloc vrf)
                     (FlatSteps-++ PC.pre-chain chainF₀)
                     absurd-f absurd-f (λ _ → VR.stops vrf sfeq)
                     (VR.no-ret vrf) (VR.no-link vrf) absurd-f
                     (λ fr j b → mem-to-fsF (AtStack fr j) b)
                     (λ hl b → mem-to-fsF (AtDynamic hl) b)
                     (VR.frame-pres vrf)
                     (λ m loc b → VR.bf-mono vrf m loc b)
        ; traces-agree =
            PT.pair-traces-stopped PC.pre-chain chainF₀ refl sfeq tf
        }
        where
          mem-to-fsF : ∀ (loc : ValueLocation FS)
                     → BeforeFrontier (record alloc { next-slot = n }) loc
                     → MemOps.readLoc (floc (VR.settle vrf)) loc ≡ MemOps.readLoc s loc
          mem-to-fsF loc b = trans (vr-mem-pres vrf loc (bf-f loc b)) (mem-to-p2 loc b)

          absurd-f : ∀ {X : Set} → TM.stoppedT (evalᴰ ⟨ f , g ⟩ x) k ≡ false → X
          absurd-f p with trans (sym (st-pair-of true sfeq)) p
          ... | ()

      -- ── `f` REACHED ITS END ─────────────────────────────────────────
      dispatch false sfeq = dispatch-g (TM.stoppedT (evalᴰ g x) PT.kg) refl
        where
          module PCF = PC.WithF vrf sfeq

          ----------------------------------------------------------------
          -- The allocator across `f` and the two mid rows. `next-slot` never
          -- moves at run time (`AllSlotStable prog` — a clause binder), and
          -- neither mid row allocates.
          ----------------------------------------------------------------
          runF≡ : exec-flat (VR.steps vrf) prog
                    (entry-flat (suc (suc base)) (floc PC.PR.p2) (falloc PC.PR.p2)
                                (fclosure PC.PR.p2))
                  ≡ PCF.fsF
          runF≡ = trans (cong (λ m → exec-flat m prog
                                       (entry-flat (suc (suc base)) (floc PC.PR.p2)
                                          (falloc PC.PR.p2) (fclosure PC.PR.p2)))
                              (sym (+-identityʳ (VR.steps vrf))))
                        (exec-flat-steps (VR.run vrf) 0)

          ns-fsF : next-slot (falloc PCF.fsF) ≡ next-slot alloc
          ns-fsF = trans (cong (λ st → next-slot (falloc st)) (sym runF≡))
                         (flat-run-keeps-next-slot (VR.steps vrf) prog ss
                            (suc (suc base)) (floc PC.PR.p2) (falloc PC.PR.p2)
                            (fclosure PC.PR.p2))

          ns-m2 : next-slot (falloc PCF.m2) ≡ next-slot alloc
          ns-m2 =
            trans (exec-abstract-preserves-next-slot (restore-input n)
                     (floc PCF.m1) (falloc PCF.m1) tt)
            (trans (exec-abstract-preserves-next-slot (store-at-slot (suc n))
                     (floc PCF.fsF) (falloc PCF.fsF) tt) ns-fsF)

          hr-mid : next-heap-ref (falloc PCF.m2) ≡ next-heap-ref (falloc PCF.fsF)
          hr-mid =
            trans (exec-abstract-preserves-heap-ref (restore-input n)
                     (floc PCF.m1) (falloc PCF.m1) tt)
                  (exec-abstract-preserves-heap-ref (store-at-slot (suc n))
                     (floc PCF.fsF) (falloc PCF.fsF) tt)

          n≤n1 : n ≤ PS.n1
          n≤n1 = ≤-trans PC.n≤f-start (frontier-mono f PS.f-start l)

          nsG : next-slot (falloc PCF.m2) ≤ PS.n1
          nsG = ≤-trans (≤-reflexive ns-m2) (≤-trans n≤ n≤n1)

          ----------------------------------------------------------------
          -- THE KEYSTONE'S PAYOFF: after `restore-input backup`, `Input1`
          -- holds what it held at entry — so `g` receives `f`'s input.
          ----------------------------------------------------------------
          input1-m2 : readReg (regs (floc PCF.m2)) Input1 ≡ readReg (regs s) Input1
          input1-m2 =
            trans (RecSchemeSemantics.exec-abstract-restore-input-sets-input
                     n (floc PCF.m1) (falloc PCF.m1)
                     (readReg (regs (floc PC.PR.p1)) Output) (proj₂ PCF.wf-restore))
                  (writeReg-same (regs s) Output (readReg (regs s) Input1))

          mem-to-m2 : ∀ (loc : ValueLocation FS)
                    → BeforeFrontier (record alloc { next-slot = n }) loc
                    → MemOps.readLoc (floc PCF.m2) loc ≡ MemOps.readLoc s loc
          mem-to-m2 loc b =
            trans (mem-untouched (restore-input n) (floc PCF.m1) (falloc PCF.m1) loc
                     Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
            (trans (store-slot-preserves-before (suc n) (floc PCF.fsF)
                     (record alloc { next-slot = n }) (falloc PCF.fsF) loc
                     (VR.frame-pres vrf) (n≤1+n n) b)
            (trans (vr-mem-pres vrf loc (bf-f loc b))
            (trans (store-slot-preserves-before n (floc PC.PR.p1)
                     (record alloc { next-slot = n }) (falloc PC.PR.p1) loc
                     (exec-abstract-preserves-frame mov-to-output s alloc) ≤-refl b)
                   (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl))))

          bfG : ∀ (loc : ValueLocation FS) → BeforeFrontier alloc loc
              → BeforeFrontier (falloc PCF.m2) loc
          bfG loc b =
            frontier-monotone
              (record (falloc PCF.fsF) { next-slot = next-slot alloc })
              (falloc PCF.m2)
              (trans PCF.cf-fsF (sym PCF.cf-m2))
              (≤-reflexive (sym ns-m2)) (≤-reflexive (sym hr-mid))
              loc (VR.bf-mono vrf (next-slot alloc) loc b)

          inpG-of : InputAt mIn alloc x s → InputAt mIn (falloc PCF.m2) x (floc PCF.m2)
          inpG-of (in-loc loc vd bf rd) =
            in-loc loc
              (validityWF-frontier-advance x loc (floc PCF.m2)
                 PCF.cf-m2 (≤-reflexive (sym ns-m2))
                 (≤-trans (vr-heap-mono vrf) (≤-reflexive (sym hr-mid)))
                 (validityWF-mem-preserved x loc s (floc PCF.m2) bf
                    (λ loc' b' → mem-to-m2 loc' (bf-n loc' b')) vd))
              (bfG loc bf) (trans input1-m2 rd)
          inpG-of (in-reg fit rd) = in-reg fit (trans input1-m2 rd)
          inpG-of (in-unit e)     = in-unit e

          mrg : MachineRefinesObsF prog PCF.bg PS.n1 PS.l1 g x
                  (floc PCF.m2) (falloc PCF.m2) (fclosure PCF.m2) PT.kg
          mrg = ihg PS.n1 PS.l1 prog PCF.bg ss cr (PS.span-g prog base span)
                    blocks-g (PS.labels-g prog base la) mIn x (floc PCF.m2) (falloc PCF.m2) (fclosure PCF.m2)
                    nsG PCF.nhM2 (inpG-of inp) PT.kg

          vrg : ValueRealized prog PCF.bg PS.n1 PS.l1 g x
                  (floc PCF.m2) (falloc PCF.m2) (fclosure PCF.m2) PT.kg
          vrg = MachineRefinesObsF.value-realized mrg

          -- The pair's stoppedness is now the INNER bind's, which is `g`'s.
          st-inner : TM.stoppedT (evalᴰ ⟨ f , g ⟩ x) k
                   ≡ TM.stoppedT PT.innerT PT.kg
          st-inner = st-pair-of false sfeq

          chainG₀ : FlatSteps prog (VR.steps vrg) PCF.m2 (VR.settle vrg)
          chainG₀ = subst (λ st → FlatSteps prog (VR.steps vrg) st (VR.settle vrg))
                          (sym PCF.handG) (VR.run vrg)

          tg : take PT.kg (chain-events chainG₀) ≡ take PT.kg PT.dEvG
          tg = trans (cong (take PT.kg)
                       (chain-events-subst-start (sym PCF.handG) (VR.run vrg)))
                     (MachineRefinesObsF.traces-agree mrg)

          module PPres = PairPres f g n l prog base s alloc cl vrf
                           PS.n1 PS.l1 n≤n1 vrg

          dispatch-g : (sg : TM.Stopped) → TM.stoppedT (evalᴰ g x) PT.kg ≡ sg
                     → MachineRefinesObsF prog base n l ⟨ f , g ⟩ x s alloc cl k

          -- ── `g` ENDED THE PROGRAM ───────────────────────────────────
          -- Four segments run, not five: the nine-row tail that builds the
          -- pair node never executes, so there is no pair value to place —
          -- and the observable is still `dEvF ++ dEvG`, because a stopped
          -- `g` contributes everything it emitted before stopping.
          dispatch-g true sgeq = record
            { value-realized =
                realized (2 + (VR.steps vrf + (2 + VR.steps vrg)))
                         (VR.settle vrg) (VR.out-mode vrg) (VR.cont-alloc vrg)
                         (FlatSteps-++ PC.pre-chain
                           (FlatSteps-++ chainF₀ (FlatSteps-++ PCF.mid-chain chainG₀)))
                         absurd-g absurd-g (λ _ → VR.stops vrg sgeq)
                         (VR.no-ret vrg) (VR.no-link vrg) absurd-g
                         (λ fr j b → PPres.mem-pres-to-gs (AtStack fr j) b)
                         (λ hl b → PPres.mem-pres-to-gs (AtDynamic hl) b)
                         PPres.frame-pres-to-gs
                         PPres.bf-to-gs
            ; traces-agree =
                PT.pair-traces-stopped-g PC.pre-chain chainF₀ PCF.mid-chain chainG₀
                                         refl refl sfeq tf tg
            }
            where
              absurd-g : ∀ {X : Set} → TM.stoppedT (evalᴰ ⟨ f , g ⟩ x) k ≡ false → X
              absurd-g p
                with trans (sym (trans st-inner (cong (λ z → TM.join-st z false) sgeq))) p
              ... | ()

          -- ── BOTH REACHED THEIR END — the pair is assembled. ──────────
          dispatch-g false sgeq = record
            { value-realized =
                realized PCG.STEPS PCG.SETTLE PPlace.out-mode PPlace.cont-alloc
                         PCG.RUN (λ _ → PCG.LIVE) (λ _ → PCG.ATEND)
                         not-stopped
                         PCG.NORET PCG.NOLINK
                         (λ _ → PPlace.place)
                         PPresF.stack-pres-pair PPresF.heap-pres-pair
                         PPres.frame-pres-pair PPres.bf-mono-pair
            ; traces-agree =
                PT.pair-traces PC.pre-chain chainF₀ PCF.mid-chain
                               chainG₀ PCG.tail-chain refl refl refl sfeq tf tg
            }
            where
              not-stopped : ∀ {X : Set} → TM.stoppedT (evalᴰ ⟨ f , g ⟩ x) k ≡ true → X
              not-stopped p
                with trans (sym p) (trans st-inner (cong (λ z → TM.join-st z false) sgeq))
              ... | ()

              module PCG = PCF.WithG vrg sgeq

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

              module PPlace = PairPlace {B} {C} n alloc n≤ PCF.fsF PCG.fsG
                                PCF.cf-fsF PCG.cf-fsG ns-fsF ns-gs hr-gs
                                (TM.valueT (evalᴰ f x) k) (TM.valueT (evalᴰ g x) PT.kg)
                                (VR.out-mode vrf) (VR.out-mode vrg)
                                (VR.cont-alloc vrf) (VR.cont-alloc vrg)
                                (VR.place vrf sfeq) (VR.place vrg sgeq)
                                mem-F→G fst-cell-gs

              module PPresF = PPres.Fill PPlace.rdi-u6 PPlace.rdi-u8
