-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.RelaxedContract
--
-- The CCC-layer relaxed contract for SigOp implementations.
--
-- ## Why
--
-- Plan 0.10 Phase A added per-arch `sigop-codegen-faithful` postulates
-- so that SigOp codegen↔abstract correspondence has a named audit
-- handle. Those postulates assume `exec-abstract (instr-sigop si) s
-- alloc = s , alloc` (a no-op). That assumption makes the postulate
-- *vacuously* satisfied by any codegen that doesn't change observable
-- state — and *trivially false* for any codegen that does. Either way
-- the postulate paper-cuts the verification: it can't catch a wrong
-- codegen because the abstract semantics is empty.
--
-- This module replaces the unconditional postulate with a derivable
-- obligation: *the trace satisfies the CCC-discipline contract*. The
-- contract is intentionally minimal — it only enforces "stack
-- discipline + register discipline + cleanup". It does NOT (yet) tie
-- the output value to `semM si` of the input.
--
-- The most relaxed CCC contract:
--   1. doesn't mess with prior-frontier stack/heap memory,
--   2. doesn't change the current frame,
--   3. doesn't grow the stack frontier,
--   4. doesn't touch any register other than Output,
--   5. either stays not-halted (pure) or halts (terminating effect).
--
-- ## What this contract does NOT enforce (yet)
--
-- This contract has NO value-flow obligation tying Output to `semM
-- si`. That means a copy-trace `mov-to-output ∷ []` (which sets
-- Output := Input1) satisfies the contract for *any* SigOp, including
-- `arith.add.int` whose `semM` is "add the components of the input
-- pair" — clearly not a copy.
--
-- This is on purpose for the POC: it exposes the gap. The next
-- iteration adds an `output-represents-semM` field (or an external
-- per-arch obligation) and re-attempts the proof; the proof should
-- then *fail* for the copy-trace, which is the property we want.
--
-- ## Layering
--
-- This record lives at the CCC layer and knows nothing about Int,
-- syscalls, or any specific SigOp. Per-name discharge happens in the
-- domain layer (Arith for `arith.*`, Strata/Linux for `linux.*`).
--
-- ## Plan
--
-- Plan 0.10 Phase A — SigOp gap closure, contract design POC.
------------------------------------------------------------------------

module Once.CCC.SigOp.RelaxedContract where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Once.Type using (Type)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.SigOp.Info using (SigOpInfo; name; semM)
open import Once.CCC.Machine.SMCore
  using (LocState; AbstractInstr; AbstractTrace;
         AbstractReg; Input1; Output;
         halted; regs; readReg;
         module AbstractExec; module MemOps)
open import Once.CCC.Machine.Allocation
  using (AllocState; current-frame; next-slot; next-heap-ref;
         module FrontierInvariant)

------------------------------------------------------------------------
-- The relaxed CCC-discipline contract
------------------------------------------------------------------------

module RelaxedDef {FS : FrameSemantics} where
  open AbstractExec {FS} using (exec-trace)
  open MemOps {FS} using (readLoc)
  open FrontierInvariant {FS} using (BeforeFrontier)

  ----------------------------------------------------------------------
  -- The contract record.
  --
  -- Each field is an obligation on the trace. Per-name discharge in
  -- the domain layer (Arith/Linux) constructs this record.
  --
  -- Note: every field assumes `halted s ≡ false` as its precondition.
  -- A trace that runs from a halted state has no obligations (the
  -- machine is already halted; further instructions are no-ops).
  ----------------------------------------------------------------------

  record RelaxedContract {A B} (si : SigOpInfo A B) (trace : AbstractTrace) : Set where
    field
      ------------------------------------------------------------------
      -- (1) Frame discipline
      ------------------------------------------------------------------
      preserves-frame : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
        halted s ≡ false →
        current-frame (proj₂ (exec-trace trace s alloc))
          ≡ current-frame alloc

      ------------------------------------------------------------------
      -- (2) Stack/heap discipline: pre-frontier memory is preserved
      ------------------------------------------------------------------
      preserves-prior-mem : ∀ (s : LocState FS) (alloc : AllocState {FS}) loc →
        halted s ≡ false →
        BeforeFrontier alloc loc →
        readLoc (proj₁ (exec-trace trace s alloc)) loc
          ≡ readLoc s loc

      ------------------------------------------------------------------
      -- (3) Cleanup: stack frontier unchanged, heap may grow
      ------------------------------------------------------------------
      slot-stable : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
        halted s ≡ false →
        next-slot (proj₂ (exec-trace trace s alloc))
          ≡ next-slot alloc

      ------------------------------------------------------------------
      -- (4) Register discipline: only Output may change.
      --
      -- Input1 is preserved too. (For SigOps that need to read input
      -- multiple times — e.g. binary arithmetic on a pair — this is
      -- naturally satisfied since they only consume from Input1.)
      ------------------------------------------------------------------
      regs-only-output : ∀ (s : LocState FS) (alloc : AllocState {FS})
        (r : AbstractReg) →
        ¬ (r ≡ Output) →
        halted s ≡ false →
        readReg (regs (proj₁ (exec-trace trace s alloc))) r
          ≡ readReg (regs s) r

      ------------------------------------------------------------------
      -- (5) Halting: stays false (pure SigOp) OR becomes true
      -- (terminating effect like exit). Both branches are allowed at
      -- the contract level; per-name discharge picks one.
      ------------------------------------------------------------------
      halted-after : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
        halted s ≡ false →
        halted (proj₁ (exec-trace trace s alloc)) ≡ false
        ⊎ halted (proj₁ (exec-trace trace s alloc)) ≡ true

  open RelaxedContract public
