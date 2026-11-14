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
open import Data.List using (List; []; _∷_; map)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; Σ)
open import Data.Bool using (false; true)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Type using (fits-int)
open import Once.Arith.SigOp.Compare using (cmp-block-info)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (module SigOpInfo)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.StepOp
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; Trace; Io; io-call; io-halt; ios)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.IR.Semantics.Trace using (callEvent; haltEvent)
open import Once.LinCore.Machine fmt ans bw using (Sh)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; StepI; i-prim; i-opend)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Lower fmt ans bw using (cmpOf; opSig)
open import Once.LinCore.Words fmt ans bw using (module Rel)

-- ★ D427: what a trace shows the machine's log: its calls and halts, each the
-- sigop event of the op, its argument (the answer is the world's)
ioEvent : Io → SigOpEvent
ioEvent (io-call o a _) = callEvent o a
ioEvent (io-halt o a)   = haltEvent o a

evsOf : Trace → List SigOpEvent
evsOf t = map ioEvent (ios t)

-- the head word, or a default
hdOr : ∀ {X : Set} → List X → X → X
hdOr (w ∷ _) _ = w
hdOr []      p = p

module Agree {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf using (W; VW; SlotsAt)
  open FlatMachine {FS} using (FlatState; floc; falloc)
  open AbstractExec {FS} using (exec-sigop-output; exec-sigop-halts; sigop-events)
  open import Once.LinCore.Moves {FS} using (slot)

  -- the sigop's state: Input1 and Output the argument's word (`argIn`, `mov-to-input`)
  at-arg : FlatState → StoredValue FS → LocState FS
  at-arg fs v = record (floc fs) { regs = writeReg (writeReg (LocState.regs (floc fs)) Output v) Input1 v }

  -- ★ D428: the argument's word, by its base (D398): a scalar its one word, any other its address
  argV : ∀ {A} → ST.Base ST.∅ₖ A → FlatState → ℕ → List W → StoredValue FS
  argV (ST.b-var {i = ()} _) fs d wx
  argV ST.b-Unit    fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)
  argV ST.b-Void    fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)
  argV ST.b-Int     fs d wx = hdOr wx (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d))
  argV ST.b-Float   fs d wx = hdOr wx (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d))
  argV (ST.b-* _ _) fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)
  argV (ST.b-+ _ _) fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)

  -- the sigop's state at an argument at slot `d` of words `wx`
  arg : Sig → FlatState → ℕ → List W → LocState FS
  arg s fs d wx = at-arg fs (argV (SigOpInfo.baseA (info s)) fs d wx)

  -- an op's answer, by the sigop its code runs (D428): the machine does not halt; the answer's
  -- words are none or its Output word, or (a compare) its Output's truth as a tag
  OpValM : (s : Sig) → Maybe CmpOp → MV ⌜ sdom s ⌝ → MV ⌜ scod s ⌝ → List SigOpEvent → FlatState → Set
  OpValM s nothing x y E fs = ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                 → (exec-sigop-halts (info s) (arg s fs d wx) ≡ false)
                   × (sigop-events (info s) (arg s fs d wx) ≡ E)
                   × Σ (List W) λ wy → VW (LocState.heapMem (floc fs)) y wy
                       × ((wy ≡ []) ⊎ (wy ≡ exec-sigop-output (info s) (arg s fs d wx) ∷ []))
  OpValM s (just o) x y E fs = ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                 → (exec-sigop-halts (cmp-block-info o) (arg s fs d wx) ≡ false)
                   × (sigop-events (cmp-block-info o) (arg s fs d wx) ≡ E)
                   × Σ _ λ k → (exec-sigop-output (cmp-block-info o) (arg s fs d wx) ≡ SV-Lit fits-int k)
                       × VW (LocState.heapMem (floc fs)) y (sv-nz (SV-Lit {FS} fits-int k) ∷ [])

  OpVal : (s : Sig) → MV ⌜ sdom s ⌝ → MV ⌜ scod s ⌝ → List SigOpEvent → FlatState → Set
  OpVal s = OpValM s (cmpOf s)

  -- a halting op: the machine halts
  OpHalt : (s : Sig) → MV ⌜ sdom s ⌝ → List SigOpEvent → FlatState → Set
  OpHalt s x E fs = ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                → (exec-sigop-halts (info (opSig s (cmpOf s))) (arg s fs d wx) ≡ true)
                  × (sigop-events (info (opSig s (cmpOf s))) (arg s fs d wx) ≡ E)

  module _ {T : Sh} where
    Agrees : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
           → StepI c r m n t c′ r′ m′ n′ → FlatState → Set
    Agrees (i-prim {g = lop s} {v = x} {w = y} {t = t} _) fs = OpVal s x y (evsOf t) fs
    Agrees (i-opend {s = s} {x = x} {t = t} _) fs = OpHalt s x (evsOf t) fs
    {-# CATCHALL #-}
    Agrees _ fs = ⊤
