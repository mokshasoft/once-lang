-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CaseRun
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
module Once.CCC.Codegen.IRObsCorrect.CaseRun (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.IRTy using (IRTy)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label; AllocState; AbstractTrace; AbstractInstr; load-indirect-suc; mov-to-input; LocState; StoredValue; readReg; Input1; Output; writeReg-same; module LocState)
open LocState using (halted; regs)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.FlatLayout using (get; get-one)

------------------------------------------------------------------------
-- THE SHARED RUN SCAFFOLDING: where every instruction sits, how long the
-- emitted text is, and the three-row prologue both arms share. The two arms
-- live in their own modules — each ends in a full `MachineRefinesObsF`, and
-- checking both in one module cost more memory than this machine has.
------------------------------------------------------------------------
module RunC {FS : FrameSemantics} where


  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes; flat-tag-branch-not)
  -- The first half of this same clause: the shape, the four premise splits,
  -- the two jump targets, and the residence lemmas.
  open ShapeC {FS}
  open GetC {FS} using (GetOut; module GetOut; setOut; out-mem)
  ----------------------------------------------------------------------
  module CaseRun {A B C : IRTy} (f : IR A C) (g : IR B C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (CaseShape.E′ f g n l))
    where

    open CaseShape f g n l

    -- The emitted length, in the form the two arms' end-pcs take.
    len-eq : length (emitted n l (case f g)) ≡ suc join-at
    len-eq = trans (cong length shape) (trans step (shuffle-len (length gt) (length ft)))
      where
        step : length E′
             ≡ 3 + (length gt + (4 + (length ft + 1)))
        step = trans (length-++ pre {gt ++ mid ++ ft ++ post})
                 (cong (3 +_)
                   (trans (length-++ gt {mid ++ ft ++ post})
                     (cong (length gt +_)
                       (trans (length-++ mid {ft ++ post})
                              (cong (4 +_) (length-++ ft {post}))))))

    ------------------------------------------------------------------
    -- THE FETCHES. The three straight rows of each arm, the `c-jmp`, and the
    -- two `c-label`s — each read out of `span` at its own offset. Everything
    -- past `gt` goes through one helper, because `fetch-++-right` indexes as
    -- `length gt + j` while the offsets read `j + length gt`.
    ------------------------------------------------------------------
    gt-at : ∀ (j : ℕ) (i : AbstractInstr)
          → fetch (mid ++ ft ++ post) j ≡ just i
          → fetch prog ((3 + (j + length gt)) + base) ≡ just i
    gt-at j i e =
      span (3 + (j + length gt)) i
        (subst (λ z → fetch (gt ++ mid ++ ft ++ post) z ≡ just i)
               (+-comm (length gt) j)
               (trans (fetch-++-right gt (mid ++ ft ++ post) j) e))

    at-branch : fetch prog (0 + base) ≡ just (instr-ctrl (c-branch-tag-zero (ℓ o l)))
    at-branch = span 0 _ refl

    -- the payload reads: `get`'s one instruction, at each arm's offset
    at-unpack-r : ∀ i → fetch (get B 1) 0 ≡ just i → fetch prog (1 + base) ≡ just i
    at-unpack-r i e = span 1 i (trans (sym (cong (λ t → fetch t 0) (get-one B 1))) e)

    at-movin-r : fetch prog (2 + base) ≡ just mov-to-input
    at-movin-r = span 2 _ refl

    at-jmp : fetch prog ((3 + length gt) + base) ≡ just (instr-ctrl (c-jmp (ℓ o (suc l))))
    at-jmp = gt-at 0 _ refl

    at-inl-label : fetch prog (inl-at + base) ≡ just (instr-ctrl (c-label (ℓ o l)))
    at-inl-label = gt-at 1 _ refl

    at-unpack-l : ∀ i → fetch (get A 1) 0 ≡ just i → fetch prog ((5 + length gt) + base) ≡ just i
    at-unpack-l i e = gt-at 2 i (trans (sym (cong (λ t → fetch t 0) (get-one A 1))) e)

    at-movin-l : fetch prog ((6 + length gt) + base) ≡ just mov-to-input
    at-movin-l = gt-at 3 _ refl

    at-join-label : fetch prog (join-at + base) ≡ just (instr-ctrl (c-label (ℓ o (suc l))))
    at-join-label =
      subst (λ z → fetch prog (z + base) ≡ just (instr-ctrl (c-label (ℓ o (suc l)))))
            (shuffle-join (length gt) (length ft))
            (gt-at (4 + length ft) _
              (trans (fetch-++-right mid (ft ++ post) (length ft))
                     (subst (λ z → fetch (ft ++ post) z ≡ just (instr-ctrl (c-label (ℓ o (suc l)))))
                            (+-identityʳ (length ft))
                            (fetch-++-right ft post 0))))

    ------------------------------------------------------------------
    -- `chain-events` does not look at the END state, so the `subst`
    -- `flat-step1` wraps a named branch/jump result in is invisible to it.
    ------------------------------------------------------------------
    chain-events-subst-end : ∀ {k fs fs' fs''} (eq : fs' ≡ fs'') (c : FlatSteps prog k fs fs')
                           → chain-events (subst (FlatSteps prog k fs) eq c) ≡ chain-events c
    chain-events-subst-end refl c = refl

    -- …and a ONE-step chain built by `flat-step1` emits what its instruction
    -- emits. The start state is EXPLICIT: `chain-events c` does not mention
    -- it, so with it implicit the metas were left for whoever used the lemma
    -- to solve — which the arms happened to do while they lived in this same
    -- module, and nothing does now that they do not.
    ev-step1 : ∀ (fs : FlatState) {fs' : FlatState} {i : AbstractInstr}
                 (h : halted (floc fs) ≡ false) (ft : fetch prog (fpc fs) ≡ just i)
                 (eq : flat-exec-instr i prog fs ≡ fs')
               → event-of i fs ≡ []
               → chain-events (flat-step1 {prog} {fs} h ft eq) ≡ []
    ev-step1 fs h ft refl e = cong (_++ []) e

    ------------------------------------------------------------------
    -- THE TWO PROLOGUES: the branch row, then the arm's payload read
    -- (`get`, one step — `Get.get-run`) and `mov-to-input` (hand it to the
    -- arm). They differ in whether the branch falls through or jumps, which
    -- the input's own tag decides (`tag-inr` / `tag-inl`), and in the payload
    -- type the read is at.
    ------------------------------------------------------------------
    module Prologue (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
                    (nh : halted s ≡ false)
                    (la : LabelsAt prog base E′)
                    where

      fs0 : FlatState
      fs0 = entry-flat base s alloc cl rs

      r1 i1 i2 : FlatState
      r1 = record fs0 { fpc = suc base }
      i1 = record fs0 { fpc = inl-at + base }
      i2 = record i1  { fpc = suc (inl-at + base) }

      -- ── the `inr` arm: the branch falls through.
      module R {b : ⟦ B ⟧} {KG} (gr : GetOut {prog = prog} B b r1 KG) where
        r2 r3 : FlatState
        r2 = setOut r1 (GetOut.out gr)
        r3 = flat-exec-instr mov-to-input prog r2

        nh-r2 : halted (floc r2) ≡ false
        nh-r2 = nh

        run-r : tag-test (flat-read-tag (floc fs0)) ≡ just false → FlatSteps prog 3 fs0 r3
        run-r cond =
          FlatSteps-++ (flat-step1 nh at-branch (flat-tag-branch-not prog fs0 (ℓ o l) cond))
                       (FlatSteps-++ (GetOut.step gr) ((nh-r2 , at-movin-r) ∷ []))

        mv-eq : readReg (regs (floc r3)) Input1 ≡ readReg (regs (floc r2)) Output
        mv-eq = writeReg-same (regs (floc r2)) Input1 (readReg (regs (floc r2)) Output)

        mem-mv : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc r3) lc ≡ SMCore.MemOps.readLoc (floc r2) lc
        mem-mv lc = mem-untouched mov-to-input (floc r2) (falloc r2) lc nhw-mov-to-input refl

        mem-eq : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc r3) lc ≡ SMCore.MemOps.readLoc s lc
        mem-eq lc = trans (mem-mv lc) (out-mem r1 (GetOut.out gr) lc)

        log-r3 : SMCore.LocState.ev-log (floc r3) ≡ SMCore.LocState.ev-log s
        log-r3 = refl

        inp : InputAt {prog = prog} (GetOut.mode gr) alloc b (floc r3)
        inp = place→input (GetOut.place gr) mv-eq mem-mv

        ev-run-r : ∀ (cond : tag-test (flat-read-tag (floc fs0)) ≡ just false)
                 → chain-events (run-r cond) ≡ []
        ev-run-r cond =
          trans (chain-events-++
                   (flat-step1 {prog} {fs0} nh at-branch (flat-tag-branch-not prog fs0 (ℓ o l) cond))
                   (FlatSteps-++ (GetOut.step gr) ((nh-r2 , at-movin-r) ∷ [])))
                (cong₂ _++_
                  (ev-step1 fs0 nh at-branch (flat-tag-branch-not prog fs0 (ℓ o l) cond) refl)
                  (trans (chain-events-++ (GetOut.step gr) ((nh-r2 , at-movin-r) ∷ []))
                         (cong (_++ _) (GetOut.silent gr))))

      -- ── the `inl` arm: the branch jumps to `ℓ o l`, the mid row's own
      -- `c-label`; executing that label is the second step.
      module L {a : ⟦ A ⟧} (gl : GetOut {prog = prog} A a i2) where
        i3 i4 : FlatState
        i3 = setOut i2 (GetOut.out gl)
        i4 = flat-exec-instr mov-to-input prog i3

        nh-i3 : halted (floc i3) ≡ false
        nh-i3 = nh

        br : flat-exec-instr (instr-ctrl (c-branch-tag-zero (ℓ o l))) prog fs0 ≡ i1
           → FlatSteps prog 1 fs0 i1
        br e = flat-step1 nh at-branch e

        jump : tag-test (flat-read-tag (floc fs0)) ≡ just true
             → flat-exec-instr (instr-ctrl (c-branch-tag-zero (ℓ o l))) prog fs0 ≡ i1
        jump cond = trans (flat-tag-branch-yes prog fs0 (ℓ o l) cond)
                          (cong (λ mj → do-jump mj fs0) (inl-target prog base la))

        tail : FlatSteps prog 3 i1 i4
        tail = FlatSteps-++ (flat-step1 nh at-inl-label refl)
                            (FlatSteps-++ (GetOut.step gl) ((nh-i3 , at-movin-l) ∷ []))

        run-i : tag-test (flat-read-tag (floc fs0)) ≡ just true → FlatSteps prog 4 fs0 i4
        run-i cond = FlatSteps-++ (br (jump cond)) tail

        mv-eq : readReg (regs (floc i4)) Input1 ≡ readReg (regs (floc i3)) Output
        mv-eq = writeReg-same (regs (floc i3)) Input1 (readReg (regs (floc i3)) Output)

        mem-mv : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc i4) lc ≡ SMCore.MemOps.readLoc (floc i3) lc
        mem-mv lc = mem-untouched mov-to-input (floc i3) (falloc i3) lc nhw-mov-to-input refl

        mem-eq : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc i4) lc ≡ SMCore.MemOps.readLoc s lc
        mem-eq lc = trans (mem-mv lc) (out-mem i2 (GetOut.out gl) lc)

        log-i4 : SMCore.LocState.ev-log (floc i4) ≡ SMCore.LocState.ev-log s
        log-i4 = refl

        inp : InputAt {prog = prog} (GetOut.mode gl) alloc a (floc i4)
        inp = place→input (GetOut.place gl) mv-eq mem-mv

        ev-run-i : ∀ (cond : tag-test (flat-read-tag (floc fs0)) ≡ just true)
                 → chain-events (run-i cond) ≡ []
        ev-run-i cond =
          trans (chain-events-++ (br (jump cond)) tail)
                (cong₂ _++_ (ev-step1 fs0 nh at-branch (jump cond) refl)
                  (trans (chain-events-++ (flat-step1 {prog} {i1} nh at-inl-label refl)
                                          (FlatSteps-++ (GetOut.step gl) ((nh-i3 , at-movin-l) ∷ [])))
                         (cong₂ _++_ (ev-step1 i1 nh at-inl-label refl refl)
                           (trans (chain-events-++ (GetOut.step gl) ((nh-i3 , at-movin-l) ∷ []))
                                  (cong (_++ _) (GetOut.silent gl))))))

    ------------------------------------------------------------------
    -- D158's hand-over, restated locally (it lives inside `CompC`).
    ------------------------------------------------------------------
    handover-eq : ∀ (b : ℕ) (fs : FlatState) (rs : List ℕ)
                → fpc fs ≡ b → fret fs ≡ rs → flink fs ≡ nothing
                → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs) rs
    handover-eq b (mkFlatFull lo al pc rt cls lk) _ refl refl refl = refl

    ------------------------------------------------------------------
    -- THE `inr` ARM, END TO END. Fall through the branch, unpack, run `g`,
    -- and `c-jmp` to the join — which is where the `inl` arm arrives too.
    ------------------------------------------------------------------
