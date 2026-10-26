-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CaseArmR
--
-- plan 0.88: `case f g` — THE ONE CONSTRUCTOR WITH CONTROL FLOW.
--
--   c-branch-tag-zero (ℓ o l) ∷ load-indirect-suc ∷ mov-to-input ∷
--   gt ++
--   c-jmp (ℓ o (suc l)) ∷ c-label (ℓ o l) ∷ load-indirect-suc ∷ mov-to-input ∷
--   ft ++
--   c-label (ℓ o (suc l)) ∷ []
--
-- Note the INVERSION: the trace runs `g` first, because the branch tests for
-- the `inl` tag and jumps FORWARD over `g`'s arm to reach `f`'s. The emitter
-- nonetheless generates `f` first (`ir-to-trace' n (suc (suc l)) f`, then `g`
-- at its outputs), so labels and blocks are ordered `f`-then-`g` while the
-- text is ordered `g`-then-`f`. Every split below has to keep those two
-- orders straight; `Pair` never had to, because there the two agree.
--
-- The two arms CONVERGE. `inl` jumps to `c-label (ℓ o l)`, runs the two
-- unpack rows and `ft`, and falls through the final `c-label`; `inr` falls
-- through the branch, runs the unpack rows and `gt`, and `c-jmp` carries it to
-- that same final label. Both leave the pc at `base + length (emitted …)`,
-- which is what `ValueRealized.at-end` asks for regardless of the tag.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CaseArmR (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; readReg; Input1; SV-Ptr; mov-to-input; module LocState; module AllocState)
open AllocState using (next-slot)
open LocState using (halted; regs)
open import Data.Sum using (inj₂)
open import Data.List.Properties using () renaming (++-identityʳ to ++-idʳ)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM
open import Once.Res using (Res; stopped; returns; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)
open import Data.Bool using (Bool)

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.CaseRun o tbl

------------------------------------------------------------------------
-- ONE ARM. Split from its twin purely for typechecking cost.
------------------------------------------------------------------------
module ArmRC {FS : FrameSemantics} where


  open Core {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-jmp)
  -- The first half of this same clause: the shape, the four premise splits,
  -- the two jump targets, and the residence lemmas.
  open ShapeC {FS}
  open RunC {FS}
  ----------------------------------------------------------------------
  module ArmR {A B C : IRTy} (f : IR A C) (g : IR B C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (case f g)))
                (ihg : IRObsCorrectF g)
                (ss : AllSlotStable prog) (cr : BlockRuns prog)
                (bl : BlocksAt prog (blocks n l (case f g)))
                (la : LabelsAt prog base (emitted n l (case f g)))
                (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
                (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
                {Bv : ⟦ B ⟧} {mIn : AllocMode} {loc : ValueLocation FS}
                (vd : ValidAtWF mIn alloc {A IRT.+ B} (inj₂ Bv) loc s)
                (rd : readReg (regs s) Input1 ≡ SV-Ptr loc)
                (k : ℕ)
                where

      open CaseShape f g n l
      open CaseRun f g n l prog base span

      -- Derived, not taken: the unpack row's well-formedness, the branch
      -- condition and the arm's input all come from the SAME residence, so
      -- asking for them separately would instantiate `Prologue` at the call
      -- site as well as here. (Plan 0.18's lesson: nested module telescopes
      -- are what OOMs, and every extra instantiation pays the whole one.)
      module P = Prologue s alloc cl nh (unpack-wf vd rd) la
      module VR = ValueRealized

      mB : AllocMode
      mB = proj₁ (arm-input-r (floc P.r3) vd rd P.mv-eq P.mem-eq)

      inpB : InputAt mB alloc Bv (floc P.r3)
      inpB = proj₂ (arm-input-r (floc P.r3) vd rd P.mv-eq P.mem-eq)

      cond : tag-zf (flat-read-tag s) ≡ false
      cond = tag-inr vd rd

      handG : P.r3 ≡ entry-flat (3 + base) (floc P.r3) (falloc P.r3) (fclosure P.r3)
      handG = handover-eq (3 + base) P.r3 refl refl refl

      nsG : next-slot (falloc P.r3) ≤ n1
      nsG = ≤-trans n≤ (frontier-mono f n (suc (suc l)))

      nh-r3 : halted (floc P.r3) ≡ false
      nh-r3 = exec-abstract-preserves-halted-WF mov-to-input (floc P.r2) (falloc P.r2) P.nh-r2 tt

      mrg : MachineRefinesObsF prog (3 + base) n1 l1 g Bv
              (floc P.r3) (falloc P.r3) (fclosure P.r3) k
      mrg = ihg n1 l1 prog (3 + base) ss cr (span-g prog base span) (blocks-g prog bl)
                (labels-g prog base la) mB Bv
                (floc P.r3) (falloc P.r3) (fclosure P.r3) nsG nh-r3 inpB k

      vg : ValueRealized prog (3 + base) n1 l1 g Bv
             (floc P.r3) (falloc P.r3) (fclosure P.r3) k
      vg = MachineRefinesObsF.value-realized mrg

      chainG : FlatSteps prog (VR.steps vg) P.r3 (VR.settle vg)
      chainG = subst (λ st → FlatSteps prog (VR.steps vg) st (VR.settle vg))
                     (sym handG) (VR.run vg)

      -- the `c-jmp`, then the join label — both arms' last step.
      t1 t2 : FlatState
      t1 = record (VR.settle vg) { fpc = join-at + base }
      t2 = record t1 { fpc = suc (join-at + base) }

      -- plan 0.97: the two trailing control rows happen only when the arm
      -- REACHED ITS END. `evalᴰ (case f g) (inj₂ Bv)` IS `evalᴰ g Bv`, so the
      -- arm's stoppedness is the clause's, and a stopped arm never jumps.
      pc-at-jmp : ∀ {v r} → resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ returns (done v r)
                → fpc (VR.settle vg) ≡ (3 + length gt) + base
      pc-at-jmp q = trans (VR.at-end vg q) (shuffle-jmp (length gt) base)

      jmpStep : ∀ {v r} (q : resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ returns (done v r)) → FlatSteps prog 1 (VR.settle vg) t1
      jmpStep q = flat-step1 {prog} {VR.settle vg} (VR.live vg (cong is-stopped q))
                  (trans (cong (fetch prog) (pc-at-jmp q)) at-jmp)
                  (trans (flat-jmp prog (VR.settle vg) (ℓ o (suc l)))
                         (cong (λ mj → do-jump mj (VR.settle vg)) (join-target prog base la)))

      labelStep : ∀ {v r} (q : resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ returns (done v r)) → FlatSteps prog 1 t1 t2
      labelStep q = flat-step1 {prog} {t1} (VR.live vg (cong is-stopped q)) at-join-label refl

      chain : ∀ {v r} (q : resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ returns (done v r))
            → FlatSteps prog (3 + (VR.steps vg + (1 + 1))) P.fs0 t2
      chain q = FlatSteps-++ (P.run-r cond)
                (FlatSteps-++ chainG (FlatSteps-++ (jmpStep q) (labelStep q)))

      chain-stopped : FlatSteps prog (3 + VR.steps vg) P.fs0 (VR.settle vg)
      chain-stopped = FlatSteps-++ (P.run-r cond) chainG

      at-end-t2 : fpc t2 ≡ length (emitted n l (case f g)) + base
      at-end-t2 = sym (cong (_+ base) len-eq)

      ------------------------------------------------------------
      -- WHAT THE PROLOGUE LEAVES ALONE. The branch row only moves the pc;
      -- `load-indirect-suc` READS memory and `mov-to-input` moves a
      -- register, so neither writes — and neither allocates, so the
      -- allocator arrives at `g` unchanged.
      ------------------------------------------------------------
      alloc-P : falloc P.r3 ≡ alloc
      alloc-P = refl

      -- the caller's window, raised to `g`'s emission frontier.
      bf-up : ∀ (loc : ValueLocation FS)
            → BeforeFrontier (record alloc { next-slot = n }) loc
            → BeforeFrontier (record (falloc P.r3) { next-slot = n1 }) loc
      bf-up = frontier-monotone (record alloc { next-slot = n })
                                (record (falloc P.r3) { next-slot = n1 })
                                refl (frontier-mono f n (suc (suc l))) ≤-refl

      mem-pres : NotCut (resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k))
               → ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → SMCore.MemOps.readLoc (floc t2) loc ≡ SMCore.MemOps.readLoc s loc
      mem-pres nc loc bf = trans (vr-mem-pres vg nc loc (bf-up loc bf)) (P.mem-eq loc)

      bf-mono-c : NotCut (resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k))
                → ∀ (m : ℕ) (loc : ValueLocation FS)
                → BeforeFrontier (record alloc { next-slot = m }) loc
                → BeforeFrontier (record (falloc t2) { next-slot = m }) loc
      bf-mono-c nc m loc bf = VR.bf-mono vg nc m loc bf

      ------------------------------------------------------------
      -- THE EVENTS. Five control/straight rows surround `g`'s run and none
      -- of them is a SigOp, so the composite emits exactly what `g` does.
      ------------------------------------------------------------
      ev-chain : ∀ {v r} (q : resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ returns (done v r))
               → chain-events (chain q) ≡ chain-events (VR.run vg)
      ev-chain q =
        trans (chain-events-++ (P.run-r cond) (FlatSteps-++ chainG (FlatSteps-++ (jmpStep q) (labelStep q))))
          (trans (cong (_++ chain-events (FlatSteps-++ chainG (FlatSteps-++ (jmpStep q) (labelStep q))))
                       (P.ev-run-r cond))
            (trans (chain-events-++ chainG (FlatSteps-++ (jmpStep q) (labelStep q)))
              (trans (cong₂ _++_ (chain-events-subst-start (sym handG) (VR.run vg))
                                 (trans (chain-events-++ (jmpStep q) (labelStep q))
                                        (cong₂ _++_
                                           (ev-step1 (VR.settle vg) (VR.live vg (cong is-stopped q))
                                              (trans (cong (fetch prog) (pc-at-jmp q)) at-jmp)
                                              (trans (flat-jmp prog (VR.settle vg) (ℓ o (suc l)))
                                                     (cong (λ mj → do-jump mj (VR.settle vg))
                                                           (join-target prog base la)))
                                              refl)
                                           (ev-step1 t1 (VR.live vg (cong is-stopped q)) at-join-label refl refl))))
                     (++-idʳ (chain-events (VR.run vg))))))

      ev-chain-stopped : chain-events chain-stopped ≡ chain-events (VR.run vg)
      ev-chain-stopped =
        trans (chain-events-++ (P.run-r cond) chainG)
          (trans (cong (_++ chain-events chainG) (P.ev-run-r cond))
                 (chain-events-subst-start (sym handG) (VR.run vg)))

      -- plan 0.105: the arm runs from the caller's log — the three prologue
      -- rows make no call — so its run IS the clause's.
      h-eq : SMCore.LocState.ev-log (floc P.r3) ≡ SMCore.LocState.ev-log s
      h-eq = P.log-r3

      RE : runAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ runAt s (⟪ evalᴰ (case f g) (inj₂ Bv) ⟫ k)
      RE = runAt-≡ {st = floc P.r3} {st′ = s} {m = ⟪ evalᴰ g Bv ⟫ k} {m′ = ⟪ evalᴰ (case f g) (inj₂ Bv) ⟫ k} h-eq refl

      res-eq : resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ resultAt s (⟪ evalᴰ (case f g) (inj₂ Bv) ⟫ k)
      res-eq = cong proj₂ RE

      nc-g : NotCut (resultAt s (⟪ evalᴰ (case f g) (inj₂ Bv) ⟫ k)) → NotCut (resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k))
      nc-g = subst NotCut (sym res-eq)

      prog-g : ∀ {m} → chain-ctrls (VR.run vg) ≤ m → k ≤ budgetLeft k (resultAt s (⟪ evalᴰ (case f g) (inj₂ Bv) ⟫ k)) + m
      prog-g = progress-≤ (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (VR.run vg)) res-eq (VR.progress vg))

      -- The arm's control steps, inside the clause's chain.
      ctrlsG : chain-ctrls (VR.run vg) ≡ chain-ctrls chainG
      ctrlsG = sym (chain-ctrls-subst-start (sym handG) (VR.run vg))

      log-c : SMCore.LocState.ev-log (floc (VR.settle vg)) ≡ SMCore.LocState.ev-log s ++ eventsAt s (⟪ evalᴰ (case f g) (inj₂ Bv) ⟫ k)
      log-c = trans (VR.log vg) (cong₂ _++_ h-eq (cong proj₁ RE))

      -- plan 0.119 D5: the arm's budgeted run returned (the clause jumps to the
      -- join), stopped, or was cut (the machine is inside the arm).
      witness : MachineRefinesObsF prog base n l (case f g) (inj₂ Bv) s alloc cl k
      witness = wit (resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k)) refl
        where
          wit : (ρ : Res (Ap ⟦ C ⟧)) → resultAt (floc P.r3) (⟪ evalᴰ g Bv ⟫ k) ≡ ρ
              → MachineRefinesObsF prog base n l (case f g) (inj₂ Bv) s alloc cl k
          wit (returns (done v r)) q = record
            { value-realized =
                realized (3 + (VR.steps vg + (1 + 1))) t2 (VR.out-mode vg) (VR.cont-alloc vg)
                         (chain q) (λ _ → VR.live vg (cong is-stopped q)) (λ _ → at-end-t2)
                         (λ p → case trans (sym (cong is-stopped (trans (sym res-eq) q))) p of λ ())
                         (λ nc → VR.no-ret vg (nc-g nc)) (λ nc → VR.no-link vg (nc-g nc))
                         log-c
                         (λ p → VR.place vg (trans res-eq p))
                         (prog-g (≤-trans (≤-reflexive ctrlsG) (≤-trans (ctrls-≤ˡ chainG (FlatSteps-++ (jmpStep q) (labelStep q))) (ctrls-≤ʳ (P.run-r cond) _))))
                         (λ nc fr j bf → mem-pres (nc-g nc) (AtStack fr j) bf)
                         (λ nc hl bf → mem-pres (nc-g nc) (AtDynamic hl) bf)
                         (λ nc → VR.frame-pres vg (nc-g nc))
                         (λ nc → bf-mono-c (nc-g nc))
            ; traces-agree =
                trans (ev-chain q) (trans (MachineRefinesObsF.traces-agree mrg) (cong proj₁ RE))
            }
          wit stopped q = record
            { value-realized =
                realized (3 + VR.steps vg) (VR.settle vg) (VR.out-mode vg) (VR.cont-alloc vg)
                         chain-stopped
                         (λ p → case trans (sym (cong is-stopped (trans (sym res-eq) q))) p of λ ())
                         (λ p → case trans (sym (trans (sym res-eq) q)) p of λ ())
                         (λ _ → proj₁ (VR.stops vg (cong is-stopped q)) , trans (proj₂ (VR.stops vg (cong is-stopped q))) (chain-left (P.run-r cond) nh-r3))
                         (λ nc → VR.no-ret vg (nc-g nc)) (λ nc → VR.no-link vg (nc-g nc))
                         log-c
                         -- plan 0.98: the arm stopped, so it has NO result —
                         -- `place`'s premise says otherwise and refutes itself.
                         (λ p → case trans (sym (trans (sym res-eq) q)) p of λ ())
                         (prog-g (≤-trans (≤-reflexive ctrlsG) (ctrls-≤ʳ (P.run-r cond) chainG)))
                         (λ nc fr j bf → mem-pres (nc-g nc) (AtStack fr j) bf)
                         (λ nc hl bf → mem-pres (nc-g nc) (AtDynamic hl) bf)
                         (λ nc → VR.frame-pres vg (nc-g nc))
                         (λ nc → bf-mono-c (nc-g nc))
            ; traces-agree =
                trans ev-chain-stopped (trans (MachineRefinesObsF.traces-agree mrg) (cong proj₁ RE))
            }
          wit (returns cut) q = record
            { value-realized =
                realized (3 + VR.steps vg) (VR.settle vg) (VR.out-mode vg) (VR.cont-alloc vg)
                         chain-stopped (λ _ → VR.live vg (cong is-stopped q))
                         (λ p → case trans (sym cM) p of λ ())
                         (λ p → case trans (sym (cong is-stopped cM)) p of λ ())
                         (cut-absurd cM) (cut-absurd cM)
                         log-c
                         (λ p → case trans (sym cM) p of λ ())
                         (prog-g (≤-trans (≤-reflexive ctrlsG) (ctrls-≤ʳ (P.run-r cond) chainG)))
                         (cut-absurd cM) (cut-absurd cM) (cut-absurd cM) (cut-absurd cM)
            ; traces-agree =
                trans ev-chain-stopped (trans (MachineRefinesObsF.traces-agree mrg) (cong proj₁ RE))
            }
            where
              cM : resultAt s (⟪ evalᴰ (case f g) (inj₂ Bv) ⟫ k) ≡ returns cut
              cM = trans (sym res-eq) q

    ------------------------------------------------------------------
    -- THE `inl` ARM. The branch JUMPS here, so the prologue is one step
    -- longer; and `ft` is followed directly by the join label, so the tail is
    -- one step SHORTER. The two arms therefore reach the same pc.
    ------------------------------------------------------------------

