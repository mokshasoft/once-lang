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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.CaseArmL (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in; LabelsIn; LabelIn; li-none; li-lab; in-range)
open import Once.CCC.Codegen.LabelRange o using (label-mono)
open import Once.CCC.Label using (idx)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label)
open import Data.Nat.Properties using (1+n≰n)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ)
open import Data.List.Properties using () renaming (++-identityʳ to ++-idʳ)
open import Once.IRTy using () renaming (_+_ to _+ᵀ_)
open import Data.Nat using (s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM
open import Once.Res using (Res; stopped; returns; is-stopped; res-returns; res-stopped)

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o
open import Once.CCC.Codegen.IRObsCorrect.CaseRun o

------------------------------------------------------------------------
-- ONE ARM. Split from its twin purely for typechecking cost.
------------------------------------------------------------------------
module ArmLC {FS : FrameSemantics} where


  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes; flat-tag-branch-not;
                                flat-jmp; flat-label)
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
                (vd : ValidAtWF mIn alloc {A +ᵀ B} (inj₁ Av) loc s)
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
      pc-at-join : TM.stoppedT (evalᴰ f Av) k ≡ false → fpc (VR.settle vf) ≡ join-at + base
      pc-at-join q = trans (VR.at-end vf q) (shuffle-end (length gt) (length ft) base)

      joinStep : (q : TM.stoppedT (evalᴰ f Av) k ≡ false) → FlatSteps prog 1 (VR.settle vf) u1
      joinStep q = flat-step1 {prog} {VR.settle vf} (VR.live vf q)
                   (trans (cong (fetch prog) (pc-at-join q)) at-join-label)
                   (cong (λ z → record (VR.settle vf) { fpc = suc z }) (pc-at-join q))

      chain : (q : TM.stoppedT (evalᴰ f Av) k ≡ false)
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
      mem-pres : ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → MemOps.readLoc (floc u1) loc ≡ MemOps.readLoc s loc
      mem-pres loc bf = trans (vr-mem-pres vf loc bf) (P.mem-eq loc)

      bf-mono-c : ∀ (m : ℕ) (loc : ValueLocation FS)
                → BeforeFrontier (record alloc { next-slot = m }) loc
                → BeforeFrontier (record (falloc u1) { next-slot = m }) loc
      bf-mono-c m loc bf = VR.bf-mono vf m loc bf

      ev-chain : (q : TM.stoppedT (evalᴰ f Av) k ≡ false)
               → chain-events (chain q) ≡ chain-events (VR.run vf)
      ev-chain q =
        trans (chain-events-++ (P.run-i cond) (FlatSteps-++ chainF (joinStep q)))
          (trans (cong (_++ chain-events (FlatSteps-++ chainF (joinStep q))) (P.ev-run-i cond))
            (trans (chain-events-++ chainF (joinStep q))
              (trans (cong₂ _++_ (chain-events-subst-start (sym handF) (VR.run vf))
                                 (ev-step1 (VR.settle vf) (VR.live vf q)
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
      arm-not-stopped : ∀ {X : Set} → TM.stoppedT (evalᴰ f Av) k ≡ false
                      → TM.stoppedT (evalᴰ f Av) k ≡ true → X
      arm-not-stopped q₀ q₁ with trans (sym q₀) q₁
      ... | ()

      witness : MachineRefinesObsF prog base n l (case f g) (inj₁ Av) s alloc cl k
      witness = wit (TM.stoppedT (evalᴰ f Av) k) refl
        where
          -- The boolean with its own equation, not `with`: the block above is
          -- stated against it and a `with` cannot abstract that far.
          wit : (sf : TM.Stopped) → TM.stoppedT (evalᴰ f Av) k ≡ sf
              → MachineRefinesObsF prog base n l (case f g) (inj₁ Av) s alloc cl k
          wit false q = record
            { value-realized =
                realized (4 + (VR.steps vf + 1)) u1 (VR.out-mode vf) (VR.cont-alloc vf)
                         (chain q) (λ _ → VR.live vf q) (λ _ → at-end-u1)
                         (λ p → arm-not-stopped q p)
                         (VR.no-ret vf) (VR.no-link vf)
                         (VR.place vf)
                         (λ fr j bf → mem-pres (AtStack fr j) bf)
                         (λ hl bf → mem-pres (AtDynamic hl) bf)
                         (VR.frame-pres vf)
                         bf-mono-c
            ; traces-agree =
                trans (cong (take k) (ev-chain q)) (MachineRefinesObsF.traces-agree mrf)
            }
          -- THE ARM STOPPED. The clause's settle state is the arm's own — the
          -- machine is sitting at the halting instruction inside `ft`, which
          -- is why `at-end` had to become conditional: the pc is NOT at the
          -- end of `case f g`'s text.
          wit true q = record
            { value-realized =
                realized (4 + VR.steps vf) (VR.settle vf) (VR.out-mode vf) (VR.cont-alloc vf)
                         chain-stopped (λ p → arm-not-stopped p q) (λ p → arm-not-stopped p q)
                         (λ _ → VR.stops vf q)
                         (VR.no-ret vf) (VR.no-link vf)
                         -- plan 0.98: the arm stopped, so it has NO result —
                         -- `place`'s premise says otherwise and refutes itself.
                         (λ p → arm-not-stopped (cong is-stopped p) q)
                         (λ fr j bf → mem-pres (AtStack fr j) bf)
                         (λ hl bf → mem-pres (AtDynamic hl) bf)
                         (VR.frame-pres vf)
                         bf-mono-c
            ; traces-agree =
                trans (cong (take k) ev-chain-stopped) (MachineRefinesObsF.traces-agree mrf)
            }


  ----------------------------------------------------------------------
  -- THE DISPATCH, and the whole clause.
  --
  -- The input's RESIDENCE decides which arm's witness applies, and the sum's
  -- own tag is what makes that decision agree with the machine's — `tag-inl` /
  -- `tag-inr` feed the very condition the branch step consumes. A sum cannot
  -- live in a register (`FitsInRegI` has only the two primitives) and is not
  -- `Unit`, so the pointer residence is the only one.
  ----------------------------------------------------------------------

