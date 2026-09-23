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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.CaseRun (o : CanonicalName) where

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

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o

------------------------------------------------------------------------
-- THE SHARED RUN SCAFFOLDING: where every instruction sits, how long the
-- emitted text is, and the three-row prologue both arms share. The two arms
-- live in their own modules — each ends in a full `MachineRefinesObsF`, and
-- checking both in one module cost more memory than this machine has.
------------------------------------------------------------------------
module RunC {FS : FrameSemantics} where


  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes; flat-tag-branch-not;
                                flat-jmp; flat-label)
  -- The first half of this same clause: the shape, the four premise splits,
  -- the two jump targets, and the residence lemmas.
  open ShapeC {FS}
  ----------------------------------------------------------------------
  module CaseRun {A B C : IRTy} (f : IR A C) (g : IR B C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (case f g)))
    where

    open CaseShape f g n l

    -- The emitted length, in the form the two arms' end-pcs take.
    len-eq : length (emitted n l (case f g)) ≡ suc join-at
    len-eq = trans step (shuffle-len (length gt) (length ft))
      where
        step : length (emitted n l (case f g))
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

    at-unpack-r : fetch prog (1 + base) ≡ just load-indirect-suc
    at-unpack-r = span 1 _ refl

    at-movin-r : fetch prog (2 + base) ≡ just mov-to-input
    at-movin-r = span 2 _ refl

    at-jmp : fetch prog ((3 + length gt) + base) ≡ just (instr-ctrl (c-jmp (ℓ o (suc l))))
    at-jmp = gt-at 0 _ refl

    at-inl-label : fetch prog (inl-at + base) ≡ just (instr-ctrl (c-label (ℓ o l)))
    at-inl-label = gt-at 1 _ refl

    at-unpack-l : fetch prog ((5 + length gt) + base) ≡ just load-indirect-suc
    at-unpack-l = gt-at 2 _ refl

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
    -- THE TWO PROLOGUES. Both are three steps: the branch row, then the
    -- arm's `load-indirect-suc` (Output := the sum's payload cell) and
    -- `mov-to-input` (hand it to the arm). They differ ONLY in whether the
    -- branch falls through or jumps, and that is decided by the input's own
    -- tag — `tag-inr` / `tag-inl`.
    ------------------------------------------------------------------
    module Prologue (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
                    (nh : halted s ≡ false)
                    (iwf : InstrWF s alloc load-indirect-suc)
                    (la : LabelsAt prog base (emitted n l (case f g)))
                    where

      fs0 : FlatState
      fs0 = entry-flat base s alloc cl

      -- ── the `inr` arm: the branch falls through.
      r1 r2 r3 : FlatState
      r1 = record fs0 { fpc = suc base }
      r2 = flat-exec-instr load-indirect-suc prog r1
      r3 = flat-exec-instr mov-to-input      prog r2

      nh-r1 : halted (floc r1) ≡ false
      nh-r1 = nh
      nh-r2 : halted (floc r2) ≡ false
      nh-r2 = exec-abstract-preserves-halted-WF load-indirect-suc (floc r1) (falloc r1) nh-r1 iwf

      run-r : tag-zf (flat-read-tag (floc fs0)) ≡ false → FlatSteps prog 3 fs0 r3
      run-r cond =
        FlatSteps-++ (flat-step1 nh at-branch (flat-tag-branch-not prog fs0 (ℓ o l) cond))
                     ((nh-r1 , at-unpack-r) ∷ (nh-r2 , at-movin-r) ∷ [])

      -- ── the `inl` arm: the branch jumps to `ℓ o l`, which is the mid row's
      -- own `c-label`; executing that label is the second step.
      i1 i2 i3 i4 : FlatState
      i1 = record fs0 { fpc = inl-at + base }
      i2 = record i1  { fpc = suc (inl-at + base) }
      i3 = flat-exec-instr load-indirect-suc prog i2
      i4 = flat-exec-instr mov-to-input      prog i3

      nh-i2 : halted (floc i2) ≡ false
      nh-i2 = nh
      nh-i3 : halted (floc i3) ≡ false
      nh-i3 = exec-abstract-preserves-halted-WF load-indirect-suc (floc i2) (falloc i2) nh-i2 iwf

      run-i : tag-zf (flat-read-tag (floc fs0)) ≡ true → FlatSteps prog 4 fs0 i4
      run-i cond =
        FlatSteps-++
          (flat-step1 nh at-branch
            (trans (flat-tag-branch-yes prog fs0 (ℓ o l) cond)
                   (cong (λ mj → do-jump mj fs0) (inl-target prog base la))))
          (FlatSteps-++ (flat-step1 nh at-inl-label refl)
                        ((nh-i2 , at-unpack-l) ∷ (nh-i3 , at-movin-l) ∷ []))

      ------------------------------------------------------------
      -- BOTH ARMS REACH THE SAME `LocState`. `r3` and `i4` differ only in
      -- the pc — the memory and registers are the same two rows applied to
      -- the same start — so the facts about what the prologue did are
      -- shared, and stated once here rather than twice below.
      ------------------------------------------------------------
      mv-eq : readReg (regs (floc r3)) Input1
            ≡ readReg (regs (proj₁ (exec-abstract load-indirect-suc s alloc))) Output
      mv-eq = writeReg-same (regs (floc r2)) Input1
                (readReg (regs (floc r2)) Output)

      mem-eq : ∀ (lc : ValueLocation FS) → MemOps.readLoc (floc r3) lc ≡ MemOps.readLoc s lc
      mem-eq lc = trans (mem-untouched mov-to-input (floc r2) (falloc r2) lc
                           nhw-mov-to-input refl)
                        (mem-untouched load-indirect-suc s alloc lc
                           nhw-load-indirect-suc refl)

      -- NONE of the five rows is a SigOp, so a prologue emits nothing. The
      -- `subst` inside `flat-step1` is what stops that from being `refl`.
      ev-run-r : ∀ (cond : tag-zf (flat-read-tag (floc fs0)) ≡ false)
               → chain-events (run-r cond) ≡ []
      ev-run-r cond =
        trans (chain-events-++
                 (flat-step1 {prog} {fs0} nh at-branch (flat-tag-branch-not prog fs0 (ℓ o l) cond))
                 ((nh-r1 , at-unpack-r) ∷ (nh-r2 , at-movin-r) ∷ []))
              (cong (_++ [])
                (ev-step1 fs0 nh at-branch
                   (flat-tag-branch-not prog fs0 (ℓ o l) cond) refl))

      ev-run-i : ∀ (cond : tag-zf (flat-read-tag (floc fs0)) ≡ true)
               → chain-events (run-i cond) ≡ []
      ev-run-i cond =
        trans (chain-events-++
                 (flat-step1 {prog} {fs0} nh at-branch
                   (trans (flat-tag-branch-yes prog fs0 (ℓ o l) cond)
                          (cong (λ mj → do-jump mj fs0) (inl-target prog base la))))
                 (FlatSteps-++ (flat-step1 {prog} {i1} nh at-inl-label refl)
                               ((nh-i2 , at-unpack-l) ∷ (nh-i3 , at-movin-l) ∷ [])))
          (trans (cong (_++ chain-events (FlatSteps-++ (flat-step1 {prog} {i1} nh at-inl-label refl)
                                            ((nh-i2 , at-unpack-l) ∷ (nh-i3 , at-movin-l) ∷ [])))
                       (ev-step1 fs0 nh at-branch
                          (trans (flat-tag-branch-yes prog fs0 (ℓ o l) cond)
                                 (cong (λ mj → do-jump mj fs0) (inl-target prog base la)))
                          refl))
                 (trans (chain-events-++ (flat-step1 {prog} {i1} nh at-inl-label refl)
                                         ((nh-i2 , at-unpack-l) ∷ (nh-i3 , at-movin-l) ∷ []))
                        (cong (_++ []) (ev-step1 i1 nh at-inl-label refl refl))))

    ------------------------------------------------------------------
    -- D158's hand-over, restated locally (it lives inside `CompC`).
    ------------------------------------------------------------------
    handover-eq : ∀ (b : ℕ) (fs : FlatState)
                → fpc fs ≡ b → fret fs ≡ [] → flink fs ≡ nothing
                → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs)
    handover-eq b (mkFlatFull lo al pc rt cls lk) refl refl refl = refl

    ------------------------------------------------------------------
    -- THE `inr` ARM, END TO END. Fall through the branch, unpack, run `g`,
    -- and `c-jmp` to the join — which is where the `inl` arm arrives too.
    ------------------------------------------------------------------
