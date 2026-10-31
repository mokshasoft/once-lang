-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv   (plan 0.135 S3, cata M4 stage D1b)
--
-- THE FOLD LOOP'S INVARIANT AND ITS ROUND'S SHAPE.
--
--   * `Inv.HeadAt σ ns vs`: the machine is at the fold head `X` (live,
--     stack frontier 0), the eval stack (slot `suc n`) holds the nodes
--     `ns`, the value stack (slot `n+2`) the results `vs` (each a valid word
--     of `C`), slot `c` the algebra's closure record `hc` (its code cell the
--     body's label, below the heap frontier), slot `c+2` the environment's
--     word, itself a valid word of `E` for `e`. Both stacks share the
--     sentinel `sn`.
--
--   * `RoundRun prog n σ comp k Post`: a run from `σ` that does what the
--     budgeted computation `comp` does at depth `k` — its events, its log,
--     its control steps against the budget, stopping when it stops — leaves
--     everything below the frontier `n` alone (when not cut), and, when
--     `comp` RETURNED `v`, ends in a state satisfying `Post v` with the
--     return stack, frame and saved frames it started with. It is what one
--     round of the fold hands D2's induction, with `comp` the algebra on the
--     round's layer and `Post v` = `HeadAt` one node on, `v` pushed.
--
-- Both are plain records over abstract states, so a consumer never unfolds
-- the run that produced them.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; SV-Ptr; SV-Code)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy; IRFunctor; μ-type)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.Res using (Res; returns)
open import Once.Denotation.Approx using (Ap; done; NotCut; budgetLeft)

module CataFoldInvC {FS : FrameSemantics} where

  open Core {FS}
  open CataStackC {FS} using (StackAt; NodeE; ValE; WordAt)
  open LocState using (halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  module Inv (prog : AbstractTrace) (F : IRFunctor) (E C : IRTy) (n c bodyL X : ℕ) (sn hc : HeapLocation)
             (e : ⟦ E ⟧) (env-sv : StoredValue FS) where

    record HeadAt (σ : FlatState) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧) : Set where
      field
        nh    : halted (floc σ) ≡ false
        pc    : fpc σ ≡ X
        ns0   : next-slot (falloc σ) ≡ 0
        eval  : StackAt (NodeE prog F) (falloc σ) (floc σ) (suc n) sn ns
        val   : StackAt (ValE prog C) (falloc σ) (floc σ) (n + 2) sn vs
        cl    : readLoc (floc σ) (AtStack (current-frame (falloc σ)) c) ≡ just (SV-Ptr (AtDynamic hc))
        ev    : readLoc (floc σ) (AtStack (current-frame (falloc σ)) (c + 2)) ≡ just env-sv
        code  : readLoc (floc σ) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o bodyL))
        hc-lt : suc (ref-id (heap-ref hc)) ≤ next-heap-ref (falloc σ)
        env   : WordAt prog (falloc σ) E e env-sv (floc σ)

  -- what a run that ended in a RETURN kept of its start
  record Same (σ τ : FlatState) : Set where
    field
      ret : fret τ ≡ fret σ
      cf  : current-frame (falloc τ) ≡ current-frame (falloc σ)
      sf  : saved-frames (falloc τ) ≡ saved-frames (falloc σ)

  record RoundRun (prog : AbstractTrace) (n : ℕ) (σ : FlatState) {V : Set} (comp : T∞ V) (k : ℕ)
                  (Post : V → FlatState → Set) : Set where
    field
      τ        : FlatState
      steps    : ℕ
      run      : FlatSteps prog steps σ τ
      events   : chain-events run ≡ eventsAt (floc σ) (⟪ comp ⟫ k)
      log      : LocState.ev-log (floc τ) ≡ LocState.ev-log (floc σ) ++ eventsAt (floc σ) (⟪ comp ⟫ k)
      progress : k ≤ budgetLeft k (resultAt (floc σ) (⟪ comp ⟫ k)) + chain-ctrls run
      live     : stopsAt (floc σ) (⟪ comp ⟫ k) ≡ false → halted (floc τ) ≡ false
      stops    : stopsAt (floc σ) (⟪ comp ⟫ k) ≡ true
               → halted (floc τ) ≡ true × LocState.left (floc τ) ≡ LocState.left (floc σ)
      no-link  : NotCut (resultAt (floc σ) (⟪ comp ⟫ k)) → flink τ ≡ nothing
      mem      : NotCut (resultAt (floc σ) (⟪ comp ⟫ k)) → ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record (falloc σ) { next-slot = n }) loc → readLoc (floc τ) loc ≡ readLoc (floc σ) loc
      bf       : NotCut (resultAt (floc σ) (⟪ comp ⟫ k)) → ∀ (m : ℕ) (loc : ValueLocation FS)
               → BeforeFrontier (record (falloc σ) { next-slot = m }) loc
               → BeforeFrontier (record (falloc τ) { next-slot = m }) loc
      same     : ∀ {v r} → resultAt (floc σ) (⟪ comp ⟫ k) ≡ returns (done v r) → Same σ τ
      post     : ∀ {v r} → resultAt (floc σ) (⟪ comp ⟫ k) ≡ returns (done v r) → Post v τ
