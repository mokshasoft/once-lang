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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.CaseArmR (o : CanonicalName) where

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
module ArmRC {FS : FrameSemantics} where


  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes; flat-tag-branch-not;
                                flat-jmp; flat-label)
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
                (vd : ValidAtWF mIn alloc {A +ᵀ B} (inj₂ Bv) loc s)
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
      pc-at-jmp : TM.stoppedT (evalᴰ g Bv) k ≡ false
                → fpc (VR.settle vg) ≡ (3 + length gt) + base
      pc-at-jmp q = trans (VR.at-end vg q) (shuffle-jmp (length gt) base)

      jmpStep : (q : TM.stoppedT (evalᴰ g Bv) k ≡ false) → FlatSteps prog 1 (VR.settle vg) t1
      jmpStep q = flat-step1 {prog} {VR.settle vg} (VR.live vg q)
                  (trans (cong (fetch prog) (pc-at-jmp q)) at-jmp)
                  (trans (flat-jmp prog (VR.settle vg) (ℓ o (suc l)))
                         (cong (λ mj → do-jump mj (VR.settle vg)) (join-target prog base la)))

      labelStep : (q : TM.stoppedT (evalᴰ g Bv) k ≡ false) → FlatSteps prog 1 t1 t2
      labelStep q = flat-step1 {prog} {t1} (VR.live vg q) at-join-label refl

      chain : (q : TM.stoppedT (evalᴰ g Bv) k ≡ false)
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

      mem-pres : ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → MemOps.readLoc (floc t2) loc ≡ MemOps.readLoc s loc
      mem-pres loc bf = trans (vr-mem-pres vg loc (bf-up loc bf)) (P.mem-eq loc)

      bf-mono-c : ∀ (m : ℕ) (loc : ValueLocation FS)
                → BeforeFrontier (record alloc { next-slot = m }) loc
                → BeforeFrontier (record (falloc t2) { next-slot = m }) loc
      bf-mono-c m loc bf = VR.bf-mono vg m loc bf

      ------------------------------------------------------------
      -- THE EVENTS. Five control/straight rows surround `g`'s run and none
      -- of them is a SigOp, so the composite emits exactly what `g` does.
      ------------------------------------------------------------
      ev-chain : (q : TM.stoppedT (evalᴰ g Bv) k ≡ false)
               → chain-events (chain q) ≡ chain-events (VR.run vg)
      ev-chain q =
        trans (chain-events-++ (P.run-r cond) (FlatSteps-++ chainG (FlatSteps-++ (jmpStep q) (labelStep q))))
          (trans (cong (_++ chain-events (FlatSteps-++ chainG (FlatSteps-++ (jmpStep q) (labelStep q))))
                       (P.ev-run-r cond))
            (trans (chain-events-++ chainG (FlatSteps-++ (jmpStep q) (labelStep q)))
              (trans (cong₂ _++_ (chain-events-subst-start (sym handG) (VR.run vg))
                                 (trans (chain-events-++ (jmpStep q) (labelStep q))
                                        (cong₂ _++_
                                           (ev-step1 (VR.settle vg) (VR.live vg q)
                                              (trans (cong (fetch prog) (pc-at-jmp q)) at-jmp)
                                              (trans (flat-jmp prog (VR.settle vg) (ℓ o (suc l)))
                                                     (cong (λ mj → do-jump mj (VR.settle vg))
                                                           (join-target prog base la)))
                                              refl)
                                           (ev-step1 t1 (VR.live vg q) at-join-label refl refl))))
                     (++-idʳ (chain-events (VR.run vg))))))

      ev-chain-stopped : chain-events chain-stopped ≡ chain-events (VR.run vg)
      ev-chain-stopped =
        trans (chain-events-++ (P.run-r cond) chainG)
          (trans (cong (_++ chain-events chainG) (P.ev-run-r cond))
                 (chain-events-subst-start (sym handG) (VR.run vg)))

      arm-not-stopped : ∀ {X : Set} → TM.stoppedT (evalᴰ g Bv) k ≡ false
                      → TM.stoppedT (evalᴰ g Bv) k ≡ true → X
      arm-not-stopped q₀ q₁ with trans (sym q₀) q₁
      ... | ()

      witness : MachineRefinesObsF prog base n l (case f g) (inj₂ Bv) s alloc cl k
      witness = wit (TM.stoppedT (evalᴰ g Bv) k) refl
        where
          wit : (sg : TM.Stopped) → TM.stoppedT (evalᴰ g Bv) k ≡ sg
              → MachineRefinesObsF prog base n l (case f g) (inj₂ Bv) s alloc cl k
          wit false q = record
            { value-realized =
                realized (3 + (VR.steps vg + (1 + 1))) t2 (VR.out-mode vg) (VR.cont-alloc vg)
                         (chain q) (λ _ → VR.live vg q) (λ _ → at-end-t2)
                         (λ p → arm-not-stopped q p)
                         (VR.no-ret vg) (VR.no-link vg)
                         (VR.place vg)
                         (λ fr j bf → mem-pres (AtStack fr j) bf)
                         (λ hl bf → mem-pres (AtDynamic hl) bf)
                         (VR.frame-pres vg)
                         bf-mono-c
            ; traces-agree =
                trans (cong (take k) (ev-chain q)) (MachineRefinesObsF.traces-agree mrg)
            }
          wit true q = record
            { value-realized =
                realized (3 + VR.steps vg) (VR.settle vg) (VR.out-mode vg) (VR.cont-alloc vg)
                         chain-stopped (λ p → arm-not-stopped p q) (λ p → arm-not-stopped p q)
                         (λ _ → VR.stops vg q)
                         (VR.no-ret vg) (VR.no-link vg)
                         -- plan 0.98: the arm stopped, so it has NO result —
                         -- `place`'s premise says otherwise and refutes itself.
                         (λ p → arm-not-stopped (cong is-stopped p) q)
                         (λ fr j bf → mem-pres (AtStack fr j) bf)
                         (λ hl bf → mem-pres (AtDynamic hl) bf)
                         (VR.frame-pres vg)
                         bf-mono-c
            ; traces-agree =
                trans (cong (take k) ev-chain-stopped) (MachineRefinesObsF.traces-agree mrg)
            }

    ------------------------------------------------------------------
    -- THE `inl` ARM. The branch JUMPS here, so the prologue is one step
    -- longer; and `ft` is followed directly by the join label, so the tail is
    -- one step SHORTER. The two arms therefore reach the same pc.
    ------------------------------------------------------------------

