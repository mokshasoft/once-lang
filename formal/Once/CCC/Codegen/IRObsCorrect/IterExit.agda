-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterExit
--
-- plan 0.119 D5: THE LOOP'S EXIT. A round returned `inl b`: from the
-- round's end the machine runs four rows —
--
--   mov-to-input ∷ c-branch-tag-zero (ℓ o (suc l)) ∷ … ∷ c-label (ℓ o (suc l)) ∷ load-indirect-suc
--
-- — the branch reads the `inl` tag and jumps to the exit label, and the
-- unpack row puts the payload `b` in `Output`. None of the four writes
-- memory, allocates, or makes a call. Also here: the payload's `ResultPlace`
-- after an unpack row, for both tags (the continue path needs the `inr` one).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterExit (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.CCC.Machine.SMCore
  using (instr-ctrl; c-branch-tag-zero; c-label; AllocState; AbstractTrace; AbstractInstr;
         load-indirect-suc; mov-to-input; LocState; StoredValue; readReg; Input1; Output; SV-Ptr;
         sv-as-loc; sucLoc; writeReg-same; module LocState)
open LocState using (halted; regs)
open import Data.Product using (Σ)
open import Data.Sum using (inj₁; inj₂)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterRun o tbl
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)

module IterExitC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes)
  open ShapeC {FS} using (tag-inl; payload-l)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem)
  open IterShapeC {FS}
  open IterRunC {FS}

  -- A one-step chain built by `flat-step1` emits what its instruction emits.
  ev-step1 : ∀ {prog : AbstractTrace} (fs : FlatState) {fs′ : FlatState} {i : AbstractInstr}
               (h : halted (floc fs) ≡ false) (ft : fetch prog (fpc fs) ≡ just i)
               (eq : flat-exec-instr i prog fs ≡ fs′)
             → event-of i fs ≡ []
             → chain-events (flat-step1 {prog} {fs} h ft eq) ≡ []
  ev-step1 fs h ft refl e = cong (_++ []) e

  ----------------------------------------------------------------------
  -- THE EXIT RUN.
  ----------------------------------------------------------------------
  module Exit {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A))
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (Iter body)))
    (la : LabelsAt prog base (emitted n l (Iter body)))
    (S0 : FlatState) (b : ⟦ B ⟧) {m : AllocMode}
    (nh0 : halted (floc S0) ≡ false)
    (pc0 : fpc S0 ≡ (3 + length (IterShape.bt body n l) + 0) + base)
    where

    open IterShape body n l
    open IterRun body n l prog base span

    s1 s2 s3 : FlatState
    s1 = flat-exec-instr mov-to-input prog S0
    s2 = record s1 { fpc = done-at + base }
    s3 = record s2 { fpc = suc (done-at + base) }

    -- The round's result: a sum in memory (a sum fits no register and is no unit).
    module P (loc : ValueLocation FS) (vS : ValidAtWF {prog = prog} m (falloc S0) {B IRT.+ A} (inj₁ b) loc (floc S0))
             (bef : Live (falloc S0) loc)
             (rax : readReg (regs (floc S0)) Output ≡ SV-Ptr loc) where

      rd1 : readReg (regs (floc s1)) Input1 ≡ SV-Ptr loc
      rd1 = trans (writeReg-same (regs (floc S0)) Input1 (readReg (regs (floc S0)) Output)) rax

      mem1 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc s1) lc ≡ SMCore.MemOps.readLoc (floc S0) lc
      mem1 lc = mem-untouched mov-to-input (floc S0) (falloc S0) lc nhw-mov-to-input refl

      v1 : ValidAtWF {prog = prog} m (falloc s1) {B IRT.+ A} (inj₁ b) loc (floc s1)
      v1 = validityWF-mem-preserved (inj₁ b) loc (floc S0) (floc s1) (live→bf bef) (λ lc _ → mem1 lc) vS

      nh1 : halted (floc s1) ≡ false
      nh1 = exec-abstract-preserves-halted-WF mov-to-input (floc S0) (falloc S0) nh0 tt

      cond : tag-test (flat-read-tag (floc s1)) ≡ just true
      cond = tag-inl v1 rd1

      -- the result, read at word 1 of the sum (`Get.get-run`)
      g : GetOut {prog = prog} B b s3
      g = get-run B 1 s3 loc nh1 at-out rd1 bef (payload-l v1)

      s4 : FlatState
      s4 = setOut s3 (GetOut.out g)

      nh4 : halted (floc s4) ≡ false
      nh4 = nh1

      pc1 : fpc s1 ≡ (rend + 1) + base
      pc1 = trans (cong suc pc0) (sym (cong (_+ base) (+-suc rend 0)))

      br : FlatSteps prog 1 s1 s2
      br = flat-step1 nh1 (trans (cong (fetch prog) pc1) at-branch)
             (trans (flat-tag-branch-yes prog s1 (ℓ o (suc l)) cond)
                    (cong (λ mj → do-jump mj s1) (done-target prog base la)))

      lab : FlatSteps prog 1 s2 s3
      lab = flat-step1 nh1 at-done refl

      chain : FlatSteps prog 4 S0 s4
      chain = (nh0 , trans (cong (fetch prog) pc0) at-movin1)
            ∷ FlatSteps-++ br (FlatSteps-++ lab (GetOut.step g))

      placeB : Σ AllocMode (λ mB → ResultPlace {prog = prog} B mB (falloc s4) (falloc s4) b (floc s4))
      placeB = GetOut.mode g , GetOut.place g

      pc-end : fpc s4 ≡ length (emitted n l (Iter body)) + base
      pc-end = sym (trans end-eq (trans (cong (λ z → (rend + z) + base) (length-++ post14 {post2}))
                                        (arith rend (length post14) base)))
        where
          open import Data.Nat.Solver using (module +-*-Solver)
          open +-*-Solver using (solve; _:+_; con; _:=_)
          arith : ∀ a p b → (a + (p + 2)) + b ≡ suc (suc ((a + p) + b))
          arith = solve 3 (λ a p b → (a :+ (p :+ con 2)) :+ b := con 2 :+ ((a :+ p) :+ b)) refl

      ev-chain : chain-events chain ≡ []
      ev-chain =
        trans (chain-events-++ br (FlatSteps-++ lab (GetOut.step g)))
          (cong₂ _++_
            (ev-step1 {prog} s1 nh1 (trans (cong (fetch prog) pc1) at-branch)
               (trans (flat-tag-branch-yes prog s1 (ℓ o (suc l)) cond)
                      (cong (λ mj → do-jump mj s1) (done-target prog base la))) refl)
            (trans (chain-events-++ lab (GetOut.step g))
                   (cong₂ _++_ (ev-step1 {prog} s2 nh1 at-done refl refl) (GetOut.silent g))))

      log4 : SMCore.LocState.ev-log (floc s4) ≡ SMCore.LocState.ev-log (floc S0)
      log4 = log-abstract mov-to-input tt (floc S0) (falloc S0)

      mem4 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc s4) lc ≡ SMCore.MemOps.readLoc (floc S0) lc
      mem4 lc = trans (out-mem s3 (GetOut.out g) lc) (mem1 lc)

      alloc4 : falloc s4 ≡ falloc S0
      alloc4 = refl

      ret4 : fret s4 ≡ fret S0
      ret4 = refl

      lnk4 : flink s4 ≡ flink S0
      lnk4 = refl

      left4 : ending (floc s4) ≡ ending (floc S0)
      left4 = chain-left chain nh4
