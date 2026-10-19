-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterInv
--
-- plan 0.119 D5: THE LOOP'S INVARIANT. The loop is entered once (the
-- three-row prologue) and then runs ROUNDS, each starting at the round's
-- first row `3 + base` with the current pair `(e , a)` in `Input1`. What
-- every round entry has in common is fixed by the entry (`Anchor`): the
-- environment `e`, where the prologue put it (`fsF`, the state after
-- `load-indirect`, whose `Output` is `e`'s cell and whose `ResultPlace` is
-- `placeF`), and the caller's frame and frontier. `RoundInv` is what holds at
-- each round entry; `RoundsRun` is what the rounds from there realize — the
-- fields of `ValueRealized`, stated from a round entry rather than from the
-- fragment's own entry, over the loop's meaning from there,
-- `iterRun f (f a)` at the remaining budget.
--
-- `Anchor` is a RECORD, not a module telescope: the rounds are proved by
-- induction across several modules, and a telescope this size instantiated
-- at each would be re-elaborated per use (the project's OOM lesson).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterInv (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack)
open import Once.CCC.Machine.SMCore
  using (AllocState; AbstractTrace; LocState; StoredValue; readReg; Output; module LocState; module AllocState)
open AllocState using (next-slot; current-frame; next-heap-ref)
open LocState using (halted; regs)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT
open import Once.Lang.Iterative using (T∞; iterRun)
open import Once.Lang.Res using (Res; stopped; returns)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)

module IterInvC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  module Loop {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A)) (n l : ℕ) (base : ℕ) where

    -- the round, as a function of the state (the environment is fixed)
    round : ⟦ E ⟧ → ⟦ A ⟧ → T∞ ⟦ B IRT.+ A ⟧
    round e a = evalᴰ body (e , a)

    -- the loop from a round entry: the round at `a`, then the iteration
    loopFrom : ⟦ E ⟧ → ⟦ A ⟧ → T∞ ⟦ B ⟧
    loopFrom e a = iterRun (round e) (round e a)

    record Anchor : Set where
      field
        s₀     : LocState FS
        alloc₀ : AllocState {FS}
        n≤₀    : next-slot alloc₀ ≤ n
        e      : ⟦ E ⟧
        -- the state after the prologue's `load-indirect`: `Output` is `e`'s cell
        fsF    : FlatState
        mf     : AllocMode
        caf    : AllocState {FS}
        placeF : ResultPlace E mf (falloc fsF) caf e (floc fsF)
        cf-F   : current-frame (falloc fsF) ≡ current-frame alloc₀
        ns-F   : next-slot (falloc fsF) ≡ next-slot alloc₀
        hr-F   : next-heap-ref alloc₀ ≤ next-heap-ref (falloc fsF)
        -- what the caller has live is untouched at `fsF` (a register write)
        mem0-F : ∀ (loc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = n }) loc
               → SMCore.MemOps.readLoc (floc fsF) loc ≡ SMCore.MemOps.readLoc s₀ loc
        bf0-F  : ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = m }) loc
               → BeforeFrontier (record (falloc fsF) { next-slot = m }) loc
        left-F : LocState.left (floc fsF) ≡ LocState.left s₀

    module _ (Z : Anchor) where
      open Anchor Z

      FR : Once.CCC.FrameSemantics.FrameSemantics.Frame FS
      FR = current-frame alloc₀

      -- `e`'s cell, as the prologue stashed it at `suc n`
      fv : StoredValue FS
      fv = readReg (regs (floc fsF)) Output

      record RoundInv (σ : FlatState) (a : ⟦ A ⟧) : Set where
        field
          pc   : fpc σ ≡ 3 + base
          ret  : fret σ ≡ []
          lnk  : flink σ ≡ nothing
          nh   : halted (floc σ) ≡ false
          mode : AllocMode
          inp  : InputAt {E IRT.* A} mode (falloc σ) (e , a) (floc σ)
          cf   : current-frame (falloc σ) ≡ FR
          ns   : next-slot (falloc σ) ≡ next-slot alloc₀
          hr   : next-heap-ref (falloc fsF) ≤ next-heap-ref (falloc σ)
          memF : ∀ (loc : ValueLocation FS) → BeforeFrontier (falloc fsF) loc
               → SMCore.MemOps.readLoc (floc σ) loc ≡ SMCore.MemOps.readLoc (floc fsF) loc
          env  : SMCore.MemOps.readLoc (floc σ) (AtStack FR (suc n)) ≡ just fv
          mem0 : ∀ (loc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = n }) loc
               → SMCore.MemOps.readLoc (floc σ) loc ≡ SMCore.MemOps.readLoc s₀ loc
          bf0  : ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = m }) loc
               → BeforeFrontier (record (falloc σ) { next-slot = m }) loc
          left : LocState.left (floc σ) ≡ LocState.left s₀

      -- What the rounds from a round entry realize (`ValueRealized`'s fields).
      record RoundsRun (prog : AbstractTrace) (σ : FlatState) (a : ⟦ A ⟧) (r : ℕ) : Set where
        field
          steps      : ℕ
          settle     : FlatState
          out-mode   : AllocMode
          cont-alloc : AllocState {FS}
          run        : FlatSteps prog steps σ settle
          live       : stopsAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ false → halted (floc settle) ≡ false
          at-end     : ∀ {v r′} → resultAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ returns (done v r′)
                     → fpc settle ≡ length (emitted n l (Iter body)) + base
          stops      : stopsAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ true
                     → halted (floc settle) ≡ true × LocState.left (floc settle) ≡ LocState.left s₀
          no-ret     : NotCut (resultAt (floc σ) (⟪ loopFrom e a ⟫ r)) → fret settle ≡ []
          no-link    : NotCut (resultAt (floc σ) (⟪ loopFrom e a ⟫ r)) → flink settle ≡ nothing
          place      : ∀ {v r′} → resultAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ returns (done v r′)
                     → ResultPlace B out-mode (falloc settle) cont-alloc v (floc settle)
          events     : chain-events run ≡ eventsAt (floc σ) (⟪ loopFrom e a ⟫ r)
          log        : SMCore.LocState.ev-log (floc settle)
                     ≡ SMCore.LocState.ev-log (floc σ) DL.++ eventsAt (floc σ) (⟪ loopFrom e a ⟫ r)
          progress   : r ≤ budgetLeft r (resultAt (floc σ) (⟪ loopFrom e a ⟫ r)) + chain-ctrls run
          mem0       : NotCut (resultAt (floc σ) (⟪ loopFrom e a ⟫ r))
                     → ∀ (loc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = n }) loc
                     → SMCore.MemOps.readLoc (floc settle) loc ≡ SMCore.MemOps.readLoc s₀ loc
          frame      : NotCut (resultAt (floc σ) (⟪ loopFrom e a ⟫ r)) → current-frame (falloc settle) ≡ FR
          bf0        : NotCut (resultAt (floc σ) (⟪ loopFrom e a ⟫ r))
                     → ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = m }) loc
                     → BeforeFrontier (record (falloc settle) { next-slot = m }) loc
