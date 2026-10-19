-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CaseArmL
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
module Once.CCC.Codegen.IRObsCorrect.CaseArmL (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; readReg; Input1; SV-Ptr; mov-to-input; module LocState; module AllocState)
open AllocState using (next-slot)
open LocState using (halted; regs)
open import Data.Sum using (inj₁)
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
import Once.Lang.Trace as TM
open import Data.Bool using (Bool)
open import Once.Lang.Res using (Res; stopped; returns; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.CaseRun o tbl

------------------------------------------------------------------------
-- ONE ARM. Split from its twin purely for typechecking cost.
------------------------------------------------------------------------
module ArmLC {FS : FrameSemantics} where


  open Core {FS}
  open FlatStepsAPI {FS} using (flat-step1)
  -- The first half of this same clause: the shape, the four premise splits,
  -- the two jump targets, and the residence lemmas.
  open ShapeC {FS}
  open RunC {FS}
  ----------------------------------------------------------------------
  module ArmL {A B C : IRTy} (f : IR A C) (g : IR B C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (case f g)))
                (ihf : IRObsCorrectF f)
                (ss : AllSlotStable prog) (cr : BlockRuns prog)
                (bl : BlocksAt prog (blocks n l (case f g)))
                (la : LabelsAt prog base (emitted n l (case f g)))
                (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
                (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
                {Av : ⟦ A ⟧} {mIn : AllocMode} {loc : ValueLocation FS}
                (vd : ValidAtWF mIn alloc {A IRT.+ B} (inj₁ Av) loc s)
                (rd : readReg (regs s) Input1 ≡ SV-Ptr loc)
                (k : ℕ)
                where

      open CaseShape f g n l
      open CaseRun f g n l prog base span

      module P = Prologue s alloc cl nh (unpack-wf vd rd) la
      module VR = ValueRealized

      mA : AllocMode
      mA = proj₁ (arm-input-l (floc P.r3) vd rd P.mv-eq P.mem-eq)

      inpA : InputAt mA alloc Av (floc P.i4)
      inpA = proj₂ (arm-input-l (floc P.r3) vd rd P.mv-eq P.mem-eq)

      cond : tag-zf (flat-read-tag s) ≡ true
      cond = tag-inl vd rd

      -- `fpc i4` is `3 + (inl-at + base)`; `ft` is emitted at `fbase base`.
      pc-i4 : fpc P.i4 ≡ fbase base
      pc-i4 = shuffle-i4 (length gt) base

      handF : P.i4 ≡ entry-flat (fbase base) (floc P.i4) (falloc P.i4) (fclosure P.i4)
      handF = handover-eq (fbase base) P.i4 pc-i4 refl refl

      nh-i4 : halted (floc P.i4) ≡ false
      nh-i4 = exec-abstract-preserves-halted-WF mov-to-input (floc P.i3) (falloc P.i3) P.nh-i3 tt

      mrf : MachineRefinesObsF prog (fbase base) n (suc (suc l)) f Av
              (floc P.i4) (falloc P.i4) (fclosure P.i4) k
      mrf = ihf n (suc (suc l)) prog (fbase base) ss cr (span-f prog base span)
                (blocks-f prog bl) (labels-f prog base la) mA Av
                (floc P.i4) (falloc P.i4) (fclosure P.i4) n≤ nh-i4 inpA k

      vf : ValueRealized prog (fbase base) n (suc (suc l)) f Av
             (floc P.i4) (falloc P.i4) (fclosure P.i4) k
      vf = MachineRefinesObsF.value-realized mrf

      chainF : FlatSteps prog (VR.steps vf) P.i4 (VR.settle vf)
      chainF = subst (λ st → FlatSteps prog (VR.steps vf) st (VR.settle vf))
                     (sym handF) (VR.run vf)

      -- …and `ft` runs straight into the join label, no jump.
      u1 : FlatState
      u1 = record (VR.settle vf) { fpc = suc (join-at + base) }

      -- plan 0.97: everything from here to the join label is what the arm
      -- does WHEN IT REACHES ITS END. `evalᴰ (case f g) (inj₁ Av)` IS
      -- `evalᴰ f Av`, so the arm's stoppedness is the whole clause's, and the
      -- trailing row to the join label happens only on the live branch — an
      -- arm that ends in a halting SigOp never gets there.
      pc-at-join : ∀ {v r} → resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k) ≡ returns (done v r) → fpc (VR.settle vf) ≡ join-at + base
      pc-at-join q = trans (VR.at-end vf q) (shuffle-end (length gt) (length ft) base)

      joinStep : ∀ {v r} (q : resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k) ≡ returns (done v r)) → FlatSteps prog 1 (VR.settle vf) u1
      joinStep q = flat-step1 {prog} {VR.settle vf} (VR.live vf (cong is-stopped q))
                   (trans (cong (fetch prog) (pc-at-join q)) at-join-label)
                   (cong (λ z → record (VR.settle vf) { fpc = suc z }) (pc-at-join q))

      chain : ∀ {v r} (q : resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k) ≡ returns (done v r))
            → FlatSteps prog (4 + (VR.steps vf + 1)) P.fs0 u1
      chain q = FlatSteps-++ (P.run-i cond) (FlatSteps-++ chainF (joinStep q))

      -- …and the run that STOPS: the same setup rows and the same arm, full
      -- stop, no join row.
      chain-stopped : FlatSteps prog (4 + VR.steps vf) P.fs0 (VR.settle vf)
      chain-stopped = FlatSteps-++ (P.run-i cond) chainF

      at-end-u1 : fpc u1 ≡ length (emitted n l (case f g)) + base
      at-end-u1 = sym (cong (_+ base) len-eq)


      ------------------------------------------------------------
      -- …and the same preservation argument, one row longer.
      ------------------------------------------------------------
      mem-pres : NotCut (resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k))
               → ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → SMCore.MemOps.readLoc (floc u1) loc ≡ SMCore.MemOps.readLoc s loc
      mem-pres nc loc bf = trans (vr-mem-pres vf nc loc bf) (P.mem-eq loc)

      bf-mono-c : NotCut (resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k))
                → ∀ (m : ℕ) (loc : ValueLocation FS)
                → BeforeFrontier (record alloc { next-slot = m }) loc
                → BeforeFrontier (record (falloc u1) { next-slot = m }) loc
      bf-mono-c nc m loc bf = VR.bf-mono vf nc m loc bf

      ev-chain : ∀ {v r} (q : resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k) ≡ returns (done v r))
               → chain-events (chain q) ≡ chain-events (VR.run vf)
      ev-chain q =
        trans (chain-events-++ (P.run-i cond) (FlatSteps-++ chainF (joinStep q)))
          (trans (cong (_++ chain-events (FlatSteps-++ chainF (joinStep q))) (P.ev-run-i cond))
            (trans (chain-events-++ chainF (joinStep q))
              (trans (cong₂ _++_ (chain-events-subst-start (sym handF) (VR.run vf))
                                 (ev-step1 (VR.settle vf) (VR.live vf (cong is-stopped q))
                                    (trans (cong (fetch prog) (pc-at-join q)) at-join-label)
                                    (cong (λ z → record (VR.settle vf) { fpc = suc z }) (pc-at-join q))
                                    refl))
                     (++-idʳ (chain-events (VR.run vf))))))

      ev-chain-stopped : chain-events chain-stopped ≡ chain-events (VR.run vf)
      ev-chain-stopped =
        trans (chain-events-++ (P.run-i cond) chainF)
          (trans (cong (_++ chain-events chainF) (P.ev-run-i cond))
                 (chain-events-subst-start (sym handF) (VR.run vf)))

      -- `false ≡ true` from the two directions of the same boolean.
      -- plan 0.105: the arm runs from the caller's log — the four prologue
      -- rows make no call — so its run IS the clause's.
      h-eq : SMCore.LocState.ev-log (floc P.i4) ≡ SMCore.LocState.ev-log s
      h-eq = P.log-i4

      RE : runAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k) ≡ runAt s (⟪ evalᴰ (case f g) (inj₁ Av) ⟫ k)
      RE = runAt-≡ {st = floc P.i4} {st′ = s} {m = ⟪ evalᴰ f Av ⟫ k} {m′ = ⟪ evalᴰ (case f g) (inj₁ Av) ⟫ k} h-eq refl

      res-eq : resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k) ≡ resultAt s (⟪ evalᴰ (case f g) (inj₁ Av) ⟫ k)
      res-eq = cong proj₂ RE

      nc-f : NotCut (resultAt s (⟪ evalᴰ (case f g) (inj₁ Av) ⟫ k)) → NotCut (resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k))
      nc-f = subst NotCut (sym res-eq)

      prog-f : ∀ {m} → chain-ctrls (VR.run vf) ≤ m → k ≤ budgetLeft k (resultAt s (⟪ evalᴰ (case f g) (inj₁ Av) ⟫ k)) + m
      prog-f = progress-≤ (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (VR.run vf)) res-eq (VR.progress vf))

      -- The arm's control steps, inside the clause's chain.
      ctrlsF : chain-ctrls (VR.run vf) ≡ chain-ctrls chainF
      ctrlsF = sym (chain-ctrls-subst-start (sym handF) (VR.run vf))

      log-c : SMCore.LocState.ev-log (floc (VR.settle vf)) ≡ SMCore.LocState.ev-log s ++ eventsAt s (⟪ evalᴰ (case f g) (inj₁ Av) ⟫ k)
      log-c = trans (VR.log vf) (cong₂ _++_ h-eq (cong proj₁ RE))

      -- plan 0.119 D5: the arm's budgeted run returned (the clause runs on to
      -- the join label), stopped, or was cut (the machine is inside the arm).
      witness : MachineRefinesObsF prog base n l (case f g) (inj₁ Av) s alloc cl k
      witness = wit (resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k)) refl
        where
          wit : (ρ : Res (Ap ⟦ C ⟧)) → resultAt (floc P.i4) (⟪ evalᴰ f Av ⟫ k) ≡ ρ
              → MachineRefinesObsF prog base n l (case f g) (inj₁ Av) s alloc cl k
          wit (returns (done v r)) q = record
            { value-realized =
                realized (4 + (VR.steps vf + 1)) u1 (VR.out-mode vf) (VR.cont-alloc vf)
                         (chain q) (λ _ → VR.live vf (cong is-stopped q)) (λ _ → at-end-u1)
                         (λ p → case trans (sym (cong is-stopped (trans (sym res-eq) q))) p of λ ())
                         (λ nc → VR.no-ret vf (nc-f nc)) (λ nc → VR.no-link vf (nc-f nc))
                         log-c
                         (λ p → VR.place vf (trans res-eq p))
                         (prog-f (≤-trans (≤-reflexive ctrlsF) (≤-trans (ctrls-≤ˡ chainF (joinStep q)) (ctrls-≤ʳ (P.run-i cond) _))))
                         (λ nc fr j bf → mem-pres (nc-f nc) (AtStack fr j) bf)
                         (λ nc hl bf → mem-pres (nc-f nc) (AtDynamic hl) bf)
                         (λ nc → VR.frame-pres vf (nc-f nc))
                         (λ nc → bf-mono-c (nc-f nc))
            ; traces-agree =
                trans (ev-chain q) (trans (MachineRefinesObsF.traces-agree mrf) (cong proj₁ RE))
            }
          -- THE ARM STOPPED. The clause's settle state is the arm's own — the
          -- machine is sitting at the halting instruction inside `ft`, which
          -- is why `at-end` had to become conditional: the pc is NOT at the
          -- end of `case f g`'s text.
          wit stopped q = record
            { value-realized =
                realized (4 + VR.steps vf) (VR.settle vf) (VR.out-mode vf) (VR.cont-alloc vf)
                         chain-stopped
                         (λ p → case trans (sym (cong is-stopped (trans (sym res-eq) q))) p of λ ())
                         (λ p → case trans (sym (trans (sym res-eq) q)) p of λ ())
                         (λ _ → proj₁ (VR.stops vf (cong is-stopped q)) , trans (proj₂ (VR.stops vf (cong is-stopped q))) (chain-left (P.run-i cond) nh-i4))
                         (λ nc → VR.no-ret vf (nc-f nc)) (λ nc → VR.no-link vf (nc-f nc))
                         log-c
                         -- plan 0.98: the arm stopped, so it has NO result —
                         -- `place`'s premise says otherwise and refutes itself.
                         (λ p → case trans (sym (trans (sym res-eq) q)) p of λ ())
                         (prog-f (≤-trans (≤-reflexive ctrlsF) (ctrls-≤ʳ (P.run-i cond) chainF)))
                         (λ nc fr j bf → mem-pres (nc-f nc) (AtStack fr j) bf)
                         (λ nc hl bf → mem-pres (nc-f nc) (AtDynamic hl) bf)
                         (λ nc → VR.frame-pres vf (nc-f nc))
                         (λ nc → bf-mono-c (nc-f nc))
            ; traces-agree =
                trans ev-chain-stopped (trans (MachineRefinesObsF.traces-agree mrf) (cong proj₁ RE))
            }
          -- THE ARM WAS CUT: as a stopped arm, but the machine is still running.
          wit (returns cut) q = record
            { value-realized =
                realized (4 + VR.steps vf) (VR.settle vf) (VR.out-mode vf) (VR.cont-alloc vf)
                         chain-stopped (λ _ → VR.live vf (cong is-stopped q))
                         (λ p → case trans (sym cM) p of λ ())
                         (λ p → case trans (sym (cong is-stopped cM)) p of λ ())
                         (cut-absurd cM) (cut-absurd cM)
                         log-c
                         (λ p → case trans (sym cM) p of λ ())
                         (prog-f (≤-trans (≤-reflexive ctrlsF) (ctrls-≤ʳ (P.run-i cond) chainF)))
                         (cut-absurd cM) (cut-absurd cM) (cut-absurd cM) (cut-absurd cM)
            ; traces-agree =
                trans ev-chain-stopped (trans (MachineRefinesObsF.traces-agree mrf) (cong proj₁ RE))
            }
            where
              cM : resultAt s (⟪ evalᴰ (case f g) (inj₁ Av) ⟫ k) ≡ returns cut
              cM = trans (sym res-eq) q


  ----------------------------------------------------------------------
  -- THE DISPATCH, and the whole clause.
  --
  -- The input's RESIDENCE decides which arm's witness applies, and the sum's
  -- own tag is what makes that decision agree with the machine's — `tag-inl` /
  -- `tag-inr` feed the very condition the branch step consumes. A sum cannot
  -- live in a register (`FitsInRegI` has only the two primitives) and is not
  -- `Unit`, so the pointer residence is the only one.
  ----------------------------------------------------------------------

