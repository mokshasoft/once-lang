-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair.Proof
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
import Once.CCC.Machine.SMCore as SMCore
import Once.CCC.Machine.SMPrimitives as SMPrimitives

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Proof (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.CCC.Machine.Locations using (AtDynamic; ValueLocation)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; mov-to-output; restore-input; store-at-slot; readReg; Input1; Output; writeReg-same; module LocState; module AllocState)
open AllocState using (next-heap-ref; next-slot)
open LocState using (halted; regs)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Chain    o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Pres o tbl
open import Data.Nat using (z≤n)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IRTy as IRTy′
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.ValueDomain as ValueDomain
import Once.Denotation.TraceMonad as TM
import Once.Denotation.TraceMonadLaws as TML
open import Once.Res using (Res; returns; is-stopped)

module PairProofC {FS : FrameSemantics} where

  open Core  {FS}
  open Mach  {FS}
  open PairC {FS}
  open PairPresC {FS}

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
  -- The proof's body, as a MODULE over the clause's binders rather than its
  -- `where`: a `where` block is one mutual block, and the positivity checker
  -- closes that block's whole occurrence graph — every definition's every
  -- argument, including the module applications' generated copies — at cubic
  -- cost (profile 2026-09-30: 323 members, 17 495 nodes, 38 s). Here each
  -- definition is its own block.
  module PairProof {A B C} {f : IR A B} {g : IR A C}
    (ihf : IRObsCorrectF f) (ihg : IRObsCorrectF g) (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩)) (bl : BlocksAt prog (blocks n l ⟨ f , g ⟩))
    (la : LabelsAt prog base (emitted n l ⟨ f , g ⟩))
    (mIn : AllocMode) (x : ValueDomain.⟦ A ⟧ᴰᴵ) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false) (inp : InputAt {A} mIn alloc x s) (k : ℕ)
    where
      module PS = PairShape f g n l
      module PC = PairChain f g n l prog base s alloc cl n≤ nh span
      module PT = PairTrace
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
           → SMCore.MemOps.readLoc (floc PC.PR.p2) loc ≡ SMCore.MemOps.readLoc s loc
      memP loc b =
        trans (store-slot-preserves-before n (floc PC.PR.p1) alloc
                 (falloc PC.PR.p1) loc
                 (exec-abstract-preserves-frame mov-to-output s alloc) n≤ b)
              (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl)

      inpF-of : InputAt {A} mIn alloc x s → InputAt {A} mIn alloc x (floc PC.PR.p2)
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

      ----------------------------------------------------------------
      -- plan 0.105: THE PAIR'S RUN. `⟨ f , g ⟩` is two binds, so its run is
      -- `f`'s calls, then `g`'s from the log `f` left, then the `returnT`
      -- (`run-bind`, twice). The prologue rows make no call, so `f` runs
      -- from the caller's log.
      ----------------------------------------------------------------
      h : List SigOpEvent
      h = SMCore.LocState.ev-log s

      logP2 : SMCore.LocState.ev-log (floc PC.PR.p2) ≡ h
      logP2 = log-silent PC.pre-chain _ refl

      esF : List SigOpEvent
      esF = eventsAt (floc PC.PR.p2) (evalᴰ f x)

      innerT : ⟦ B ⟧ → TM.T ⟦ B IRTy′.* C ⟧
      innerT vb = evalᴰ g x TM.>>=T λ c → TM.returnT (vb , c)

      RF : runAt (floc PC.PR.p2) (evalᴰ f x) ≡ TM.run ιᶠ h (evalᴰ f x)
      RF = cong (λ hh → TM.run ιᶠ hh (evalᴰ f x)) logP2

      pair-run : ∀ (r : Res ⟦ B ⟧) → resultAt (floc PC.PR.p2) (evalᴰ f x) ≡ r
               → runAt s (evalᴰ ⟨ f , g ⟩ x) ≡ TM.thenRes ιᶠ h esF r innerT
      pair-run r q =
        trans (TML.run-bind ιᶠ h (evalᴰ f x) innerT)
              (cong₂ (λ es r′ → TM.thenRes ιᶠ h es r′ innerT)
                     (sym (cong proj₁ RF)) (trans (sym (cong proj₂ RF)) q))

      tf : chain-events chainF₀ ≡ esF
      tf = trans (chain-events-subst-start (sym PC.handF) (VR.run vrf))
                 (MachineRefinesObsF.traces-agree mrf)

      -- The two prologue rows, at the window's own bound. (`memP` states the
      -- same thing at `alloc`; the record's field is at `alloc { next-slot = n }`.)
      mem-to-p2 : ∀ (loc : ValueLocation FS)
                → BeforeFrontier (record alloc { next-slot = n }) loc
                → SMCore.MemOps.readLoc (floc PC.PR.p2) loc ≡ SMCore.MemOps.readLoc s loc
      mem-to-p2 loc b =
        trans (store-slot-preserves-before n (floc PC.PR.p1)
                 (record alloc { next-slot = n }) (falloc PC.PR.p1) loc
                 (exec-abstract-preserves-frame mov-to-output s alloc) ≤-refl b)
              (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl)

      -- The pair's stoppedness, read off `f`'s RESULT (plan 0.98).
      -- `evalᴰ ⟨ f , g ⟩ x` is `PT.pairOf (T.resT (evalᴰ f x))`, so one `cong`
      -- on `f`'s result gives the pair's flag at whichever shape the branch
      -- has. `join-st` used to be this `cong`'s function.

      ----------------------------------------------------------------
      -- THE SPLIT. Three outcomes, not one: `f` stops, `g` stops, or the
      -- pair is assembled. The first two are plan 0.97's — until it, the
      -- obligation asserted the machine was live and at the end of the
      -- pair's text no matter what the Spec said, which a program that
      -- exits inside `f` cannot satisfy.
      ----------------------------------------------------------------
      -- plan 0.98: the split is on `f`'s RESULT. `returns vB` binds the value
      -- `PairPlace` has to place, so it is no longer fetched out of a total
      -- field on a branch that may not have one.
      module Returns (vB : ⟦ B ⟧) (rfeq : resultAt (floc PC.PR.p2) (evalᴰ f x) ≡ returns vB) where
          sfeq : stopsAt (floc PC.PR.p2) (evalᴰ f x) ≡ false
          sfeq = cong is-stopped rfeq

          module PCF = PairChainF f g n l prog base s alloc cl n≤ nh span vrf sfeq

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
            trans (SMPrimitives.RecSchemeSemantics.exec-abstract-restore-input-sets-input
                     n (floc PCF.m1) (falloc PCF.m1)
                     (readReg (regs (floc PC.PR.p1)) Output) (proj₂ PCF.wf-restore))
                  (writeReg-same (regs s) Output (readReg (regs s) Input1))

          mem-to-m2 : ∀ (loc : ValueLocation FS)
                    → BeforeFrontier (record alloc { next-slot = n }) loc
                    → SMCore.MemOps.readLoc (floc PCF.m2) loc ≡ SMCore.MemOps.readLoc s loc
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

          inpG-of : InputAt {A} mIn alloc x s → InputAt {A} mIn (falloc PCF.m2) x (floc PCF.m2)
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
                  (floc PCF.m2) (falloc PCF.m2) (fclosure PCF.m2) k
          mrg = ihg PS.n1 PS.l1 prog PCF.bg ss cr (PS.span-g prog base span)
                    blocks-g (PS.labels-g prog base la) mIn x (floc PCF.m2) (falloc PCF.m2) (fclosure PCF.m2)
                    nsG PCF.nhM2 (inpG-of inp) k

          vrg : ValueRealized prog PCF.bg PS.n1 PS.l1 g x
                  (floc PCF.m2) (falloc PCF.m2) (fclosure PCF.m2) k
          vrg = MachineRefinesObsF.value-realized mrg

          -- `g` runs from the log `f` left: the two mid rows make no call.
          logM2 : SMCore.LocState.ev-log (floc PCF.m2) ≡ h ++ esF
          logM2 = trans (log-silent PCF.mid-chain _ refl)
                        (trans (VR.log vrf) (cong (_++ esF) logP2))

          esG : List SigOpEvent
          esG = eventsAt (floc PCF.m2) (evalᴰ g x)

          RG : runAt (floc PCF.m2) (evalᴰ g x) ≡ TM.run ιᶠ (h ++ esF) (evalᴰ g x)
          RG = cong (λ hh → TM.run ιᶠ hh (evalᴰ g x)) logM2

          inner-run : ∀ (r : Res ⟦ C ⟧) → resultAt (floc PCF.m2) (evalᴰ g x) ≡ r
                    → runAt s (evalᴰ ⟨ f , g ⟩ x)
                      ≡ TM.appE esF (TM.thenRes ιᶠ (h ++ esF) esG r (λ c → TM.returnT (vB , c)))
          inner-run r q =
            trans (pair-run (returns vB) rfeq)
                  (cong (TM.appE esF)
                    (trans (TML.run-bind ιᶠ (h ++ esF) (evalᴰ g x) (λ c → TM.returnT (vB , c)))
                           (cong₂ (λ es r′ → TM.thenRes ιᶠ (h ++ esF) es r′ (λ c → TM.returnT (vB , c)))
                                  (sym (cong proj₁ RG)) (trans (sym (cong proj₂ RG)) q))))

          -- …and the log after `g` is the caller's followed by both.
          log-fg : SMCore.LocState.ev-log (floc (VR.settle vrg)) ≡ (h ++ esF) ++ esG
          log-fg = trans (VR.log vrg) (cong (_++ esG) logM2)

          chainG₀ : FlatSteps prog (VR.steps vrg) PCF.m2 (VR.settle vrg)
          chainG₀ = subst (λ st → FlatSteps prog (VR.steps vrg) st (VR.settle vrg))
                          (sym PCF.handG) (VR.run vrg)

          tg : chain-events chainG₀ ≡ esG
          tg = trans (chain-events-subst-start (sym PCF.handG) (VR.run vrg))
                     (MachineRefinesObsF.traces-agree mrg)

          module PPres = PairPres f g n l prog base s alloc cl vrf
                           PS.n1 PS.l1 n≤n1 vrg
