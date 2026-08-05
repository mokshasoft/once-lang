-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.FlatSemanticLift
--
-- Plan 0.32 choice (a), migration step 2 — the capstone: lift a
-- semantic-side `ValidAtWF` result stated over `exec-trace` onto the flat
-- machine's `exec-flat` final state, on a jump-free trace.
--
-- This is what makes `exec-flat` THE abstract semantics while the WF
-- proofs keep reasoning over `exec-trace`: the surviving theorem
-- `exec-trace-is-flat` (bridge) + `validAtWF-set-halted` (halted-
-- invariance) transport the conclusion across. The trace's straightness
-- comes from `straight-ir-to-trace` for any Cata-free IR.
--
-- Combines (all postulate-free):
--   * Flat.exec-trace-is-flat   — flat final ≡ exec-trace final (up to forced)
--   * ValidAtWFHalted.validAtWF-set-halted — ValidAtWF ignores `halted`
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.FlatSemanticLift (o : CanonicalName) where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (true)
open import Data.List using (length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace; LocState; AllocState; module AbstractExec)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.Type using (Type)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
open import Once.CCC.Machine.ValidAtWFHalted o using (validAtWF-set-halted)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module _ {FS : FrameSemantics} (program-bound : ℕ) where
  open FlatMachine {FS}
  open AbstractExec {FS} using (exec-trace)
  open ClosureWellFormedDef {FS} program-bound

  -- The semantic-side conclusion (over exec-trace) transports to the
  -- flat final state. The alloc swaps via `falloc ≡ proj₂ exec-trace`;
  -- the state via `forced (floc …) ≡ forced (proj₁ exec-trace)`, having
  -- first forced the exec-trace state's `halted` (validAtWF-set-halted).
  lift-validAtWF-flat : ∀ {mOut A} {v : ⟦ A ⟧} {loc}
    (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS})
    → Straight trace
    → ValidAtWF mOut (proj₂ (exec-trace trace s alloc)) v loc
                     (proj₁ (exec-trace trace s alloc))
    → ValidAtWF mOut (falloc (exec-flat (suc (length trace)) trace (mkFlat s alloc 0))) v loc
                     (forced (floc (exec-flat (suc (length trace)) trace (mkFlat s alloc 0))))
  lift-validAtWF-flat {mOut} {A} {v} {loc} trace s alloc straight valid =
    subst (λ st → ValidAtWF mOut (falloc EF) v loc st) (sym (proj₁ br))
      (subst (λ a → ValidAtWF mOut a v loc (forced (proj₁ ET))) (sym (proj₂ br))
        (validAtWF-set-halted program-bound true valid))
    where
      ET = exec-trace trace s alloc
      EF = exec-flat (suc (length trace)) trace (mkFlat s alloc 0)
      br = exec-trace-is-flat trace s alloc straight
