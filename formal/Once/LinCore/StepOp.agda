-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepOp — plan 0.146 B1.4b (D426): AN OP STEP AGREES WITH THE
-- MACHINE. The image's op takes the world's answer as given; the flat
-- machine answers by its effect class and interpretation. The step theorem
-- is relative to the machine's world: at an op step, the machine's sigop
-- (Input1 and Output at the argument's words, as the lowering leaves them)
-- does not halt and the answer's words are none or its Output word; at a
-- halting op it halts. Every other step: nothing. The split on the step
-- lives here, in a module of its own.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; Σ)
open import Data.Bool using (false; true)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.StepOp
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV)
open import Once.LinCore.Machine fmt ans bw using (Sh)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; StepI; i-prim; i-opend)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Words fmt ans bw using (module Rel)

module Agree {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf using (W; VW; SlotsAt)
  open FlatMachine {FS} using (FlatState; floc; falloc)
  open AbstractExec {FS} using (exec-sigop-output; exec-sigop-halts)
  open import Once.LinCore.Moves {FS} using (slot)

  -- the sigop's state: Input1 and Output the argument's address (`lea-slot d`, `mov-to-input`)
  at-arg : FlatState → ℕ → LocState FS
  at-arg fs d = record (floc fs) { regs = writeReg (writeReg (LocState.regs (floc fs)) Output p) Input1 p }
    where p = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)

  -- an op's answer: the machine does not halt, the answer's words are none or its Output word
  OpVal : (s : Sig) → MV ⌜ sdom s ⌝ → MV ⌜ scod s ⌝ → FlatState → Set
  OpVal s x y fs = ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                 → (exec-sigop-halts (info s) (at-arg fs d) ≡ false)
                   × Σ (List W) λ wy → VW (LocState.heapMem (floc fs)) y wy
                       × ((wy ≡ []) ⊎ (wy ≡ exec-sigop-output (info s) (at-arg fs d) ∷ []))

  -- a halting op: the machine halts
  OpHalt : (s : Sig) → MV ⌜ sdom s ⌝ → FlatState → Set
  OpHalt s x fs = ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                → exec-sigop-halts (info s) (at-arg fs d) ≡ true

  module _ {T : Sh} where
    Agrees : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
           → StepI c r m n t c′ r′ m′ n′ → FlatState → Set
    Agrees (i-prim {g = lop s} {v = x} {w = y} _) fs = OpVal s x y fs
    Agrees (i-opend {s = s} {x = x} _) fs = OpHalt s x fs
    {-# CATCHALL #-}
    Agrees _ fs = ⊤
