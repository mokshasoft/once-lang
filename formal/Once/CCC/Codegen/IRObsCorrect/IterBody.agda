-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterBody
--
-- plan 0.119 D5: ONE ROUND'S BODY RUN. At a round entry the body's own
-- witness (the induction hypothesis, emitted at `3 + base`) runs the round;
-- this module states what that run leaves, relative to the round entry and to
-- the loop's anchor — the facts the exit and the continue paths consume.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterBody (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack)
open import Once.CCC.Machine.SMCore
  using (AllocState; AbstractTrace; LocState; StoredValue; module LocState; module AllocState)
open AllocState using (next-slot; current-frame; saved-frames; next-heap-ref)
open LocState using (halted; regs)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (s≤s)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT
open import Once.Internal.Res using (Res; stopped; returns; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)

open import Once.CCC.Codegen.IRObsCorrect.IterShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterRun o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterInv o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Proof o tbl using (module PairProofC)

module IterBodyC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open IterShapeC {FS}
  open IterRunC {FS}
  open IterInvC {FS}
  open PairProofC {FS} using (vr-heap-mono)

  module Body {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A))
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (Iter body)))
    (ihb : IRObsCorrectF body)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (bl : BlocksAt prog (blocks n l (Iter body)))
    (la : LabelsAt prog base (emitted n l (Iter body)))
    (Z : Loop.Anchor body n l base)
    (σ : FlatState) (a : ⟦ A ⟧) (inv : Loop.RoundInv body n l base Z σ a) (r : ℕ)
    where

    open IterShape body n l
    open IterRun body n l prog base span
    open Loop body n l base
    open Anchor Z
    module I = RoundInv inv
    module VR = ValueRealized

    n≤n4 : n ≤ suc (suc (suc (suc n)))
    n≤n4 = ≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n))))))

    nsB : next-slot (falloc σ) ≤ suc (suc (suc (suc n)))
    nsB = ≤-trans (≤-reflexive I.ns) (≤-trans n≤₀ n≤n4)

    mrb : MachineRefinesObsF prog (3 + base) (suc (suc (suc (suc n)))) (suc (suc l)) body (e , a)
            (floc σ) (falloc σ) (fclosure σ) rs₀ r
    mrb = ihb (suc (suc (suc (suc n)))) (suc (suc l)) prog (3 + base) ss cr
              (span-b prog base span) (blocks-b prog bl) (labels-b prog base la)
              I.mode (e , a) (floc σ) (falloc σ) (fclosure σ) nsB I.nh I.inp r rs₀

    vb : ValueRealized prog (3 + base) (suc (suc (suc (suc n)))) (suc (suc l)) body (e , a)
           (floc σ) (falloc σ) (fclosure σ) rs₀ r
    vb = MachineRefinesObsF.value-realized mrb

    S0 : FlatState
    S0 = VR.settle vb

    handB : σ ≡ entry-flat (3 + base) (floc σ) (falloc σ) (fclosure σ) rs₀
    handB = handover-eq (3 + base) σ rs₀ I.pc I.ret I.lnk

    chainB : FlatSteps prog (VR.steps vb) σ S0
    chainB = subst (λ st → FlatSteps prog (VR.steps vb) st S0) (sym handB) (VR.run vb)

    ev-chainB : chain-events chainB ≡ eventsAt (floc σ) (⟪ round e a ⟫ r)
    ev-chainB = trans (chain-events-subst-start (sym handB) (VR.run vb)) (MachineRefinesObsF.traces-agree mrb)

    ctrls-chainB : chain-ctrls chainB ≡ chain-ctrls (VR.run vb)
    ctrls-chainB = chain-ctrls-subst-start (sym handB) (VR.run vb)

    -- the round's result, at the budget the loop was given
    ρ₁ : Res (Ap ⟦ B IRT.+ A ⟧)
    ρ₁ = resultAt (floc σ) (⟪ round e a ⟫ r)

    pc0-of : ∀ {v r′} → ρ₁ ≡ returns (done v r′) → fpc S0 ≡ (3 + length bt + 0) + base
    pc0-of q = trans (VR.at-end vb q) rend-eq

    -- `next-slot` never moves at run time.
    ns0 : next-slot (falloc S0) ≡ next-slot alloc₀
    ns0 = trans (trans (cong (λ st → next-slot (falloc st)) (sym runB≡))
                       (flat-run-keeps-next-slot (VR.steps vb) prog ss (3 + base) (floc σ) (falloc σ) (fclosure σ) rs₀))
                I.ns
      where
        runB≡ : exec-flat (VR.steps vb) prog (entry-flat (3 + base) (floc σ) (falloc σ) (fclosure σ) rs₀) ≡ S0
        runB≡ = trans (cong (λ m → exec-flat m prog (entry-flat (3 + base) (floc σ) (falloc σ) (fclosure σ) rs₀))
                            (sym (+-identityʳ (VR.steps vb))))
                      (exec-flat-steps (VR.run vb) 0)

    -- the frontiers the body's preservation is stated against
    bfσ : ∀ (lc : ValueLocation FS) → BeforeFrontier (falloc fsF) lc
        → BeforeFrontier (record (falloc σ) { next-slot = suc (suc (suc (suc n))) }) lc
    bfσ = frontier-monotone (falloc fsF) (record (falloc σ) { next-slot = suc (suc (suc (suc n))) })
            (trans cf-F (sym I.cf)) (≤-trans (≤-reflexive ns-F) (≤-trans n≤₀ n≤n4)) I.hr

    bf0σ : ∀ (lc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = n }) lc
         → BeforeFrontier (record (falloc σ) { next-slot = suc (suc (suc (suc n))) }) lc
    bf0σ = frontier-monotone (record alloc₀ { next-slot = n }) (record (falloc σ) { next-slot = suc (suc (suc (suc n))) })
             (sym I.cf) n≤n4 (≤-trans hr-F I.hr)

    -- D337: the frame and the return stack are restored when the round
    -- RETURNED, so these two take its equation rather than `NotCut`.
    cf0-of : ∀ {v r′} → ρ₁ ≡ returns (done v r′) → current-frame (falloc S0) ≡ FR Z
    cf0-of q = trans (VR.frame-pres vb q) I.cf

    ret0-of : ∀ {v r′} → ρ₁ ≡ returns (done v r′) → fret S0 ≡ rs₀
    ret0-of q = VR.no-ret vb q

    -- D338: …and so is the frame stack.
    sf0-of : ∀ {v r′} → ρ₁ ≡ returns (done v r′) → saved-frames (falloc S0) ≡ SF Z
    sf0-of q = trans (VR.frames-pres vb q) I.sf

    module NC (nc : NotCut ρ₁) where

      hr0 : next-heap-ref (falloc fsF) ≤ next-heap-ref (falloc S0)
      hr0 = ≤-trans I.hr (vr-heap-mono vb nc)

      memF0 : ∀ (lc : ValueLocation FS) → BeforeFrontier (falloc fsF) lc
            → SMCore.MemOps.readLoc (floc S0) lc ≡ SMCore.MemOps.readLoc (floc fsF) lc
      memF0 lc bf = trans (vr-mem-pres vb nc lc (bfσ lc bf)) (I.memF lc bf)

      env0 : SMCore.MemOps.readLoc (floc S0) (AtStack (FR Z) (suc n)) ≡ just (fv Z)
      env0 = trans (VR.stack-pres vb nc (FR Z) (suc n)
                      (BeforeFrontier.stack-before (sym I.cf)
                        (s≤s (≤-trans (n≤1+n (suc n)) (n≤1+n (suc (suc n)))))))
                   I.env

      mem00 : ∀ (lc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = n }) lc
            → SMCore.MemOps.readLoc (floc S0) lc ≡ SMCore.MemOps.readLoc s₀ lc
      mem00 lc bf = trans (vr-mem-pres vb nc lc (bf0σ lc bf)) (I.mem0 lc bf)

      bf00 : ∀ (m : ℕ) (lc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = m }) lc
           → BeforeFrontier (record (falloc S0) { next-slot = m }) lc
      bf00 m lc bf = VR.bf-mono vb nc m lc (I.bf0 m lc bf)

      lnk0 : flink S0 ≡ nothing
      lnk0 = VR.no-link vb nc

    module Live (ns : stopsAt (floc σ) (⟪ round e a ⟫ r) ≡ false) where
      nh0 : halted (floc S0) ≡ false
      nh0 = VR.live vb ns

      left0 : LocState.left (floc S0) ≡ LocState.left s₀
      left0 = trans (chain-left chainB nh0) I.left
