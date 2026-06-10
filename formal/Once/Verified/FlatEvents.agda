-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.FlatEvents — the machine SigOp-event trace.
--
-- Plan 0.36 (machine side): `flat-events` is the machine counterpart of
-- the source observable `obs` (Once.Verified.TraceDenote). It mirrors
-- `exec-flat`'s three mutual fuel functions (Once.CCC.Machine.Flat) and
-- emits a `SigOpEvent` at each `instr-sigop` it executes — leaving
-- `exec-flat`/`FlatState` untouched (a parallel observation, not an
-- accumulator threaded through the machine).
--
-- It runs over `exec-flat` (pc + jump + fuel), NOT the straight-line
-- `exec-trace`, because the recursion schemes compile to LOOPS
-- (`instr-ctrl` jumps) which only the flat machine can execute. The
-- machine is architecture-GENERIC (`FrameSemantics`-parameterised), so
-- `flat-events` — and the `traces-agree` theorem over it — is one
-- definition for all targets; the per-target bridge is the IR-agnostic
-- `flat-sim`.
--
-- FAITHFUL arguments: the Layer-0 observable IS the `linux.exit`
-- argument, so the trace must carry it. `SigOpEvent` coarsens the
-- argument to `ev-argℕ : Maybe ℕ`; `flat-events` decodes the machine's
-- `Input1` (`SV-Lit {Int}` → the ℕ) — a function. `traces-agree` (next)
-- proves this ℕ equals `obs`'s via the per-SigOp value-correspondence.
------------------------------------------------------------------------

module Once.Verified.FlatEvents where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Int)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SigOp.Info using (SigOpInfo; name)
open import Once.CCC.Machine.SMCore
  using (LocState; halted; regs; readReg; Input1;
         StoredValue; SV-Lit;
         AbstractTrace; AbstractInstr; instr-sigop)
open import Once.CCC.Machine.Flat
open import Once.Verified.Trace using (SigOpEvent; mk-event; isInt?)

module FlatEventTrace {FS : FrameSemantics} where
  open FlatMachine {FS}

  -- Decode a register cell to a ℕ argument (only `Int` literals decode).
  decode-ℕ : StoredValue FS → Maybe ℕ
  decode-ℕ (SV-Lit {Int} _ v) = just v
  decode-ℕ _                  = nothing

  -- The event a `SigOp` invocation emits, read off the machine: name
  -- from the descriptor, ℕ argument decoded from `Input1` when the
  -- input type is `Int` (matching `mkEvent`'s `isInt?` gate on the
  -- source side, so the two sides can be proven equal).
  machine-event : ∀ {A B} → SigOpInfo A B → StoredValue FS → SigOpEvent
  machine-event {A} si sv with isInt? A
  ... | just _  = mk-event (name si) (decode-ℕ sv)
  ... | nothing = mk-event (name si) nothing

  -- Events emitted by executing one instruction from state `fs`.
  event-of : AbstractInstr → FlatState → List SigOpEvent
  event-of (instr-sigop si) fs = machine-event si (readReg (regs (floc fs)) Input1) ∷ []
  event-of _                _  = []

  -- The SigOp-event trace, mirroring `exec-flat`'s fuel/fetch dispatch.
  flat-events       : ℕ → AbstractTrace → FlatState → List SigOpEvent
  flat-events-step  : Bool → ℕ → AbstractTrace → FlatState → List SigOpEvent
  flat-events-fetch : Maybe AbstractInstr → ℕ → AbstractTrace → FlatState → List SigOpEvent

  flat-events zero    _    fs = []
  flat-events (suc n) prog fs = flat-events-step (halted (floc fs)) n prog fs

  flat-events-step true  _ _    fs = []
  flat-events-step false n prog fs = flat-events-fetch (fetch prog (fpc fs)) n prog fs

  flat-events-fetch nothing  _ _    fs = []
  flat-events-fetch (just i) n prog fs =
    event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs)

  ----------------------------------------------------------------------
  -- Machine-side "no SigOp ⇒ empty trace": if every instruction the run
  -- can fetch emits nothing (`event-of … ≡ []` — i.e. no `instr-sigop`),
  -- the whole `flat-events` trace is `[]`. By fuel induction, mirroring
  -- `flat-events`'s dispatch. This discharges `traces-agree` for a PURE
  -- cata (with `pure-cata-emits-[]`: both sides `[]`) and is what
  -- `pure-refines` consumes for straight-line IRs.
  ----------------------------------------------------------------------

  flat-events-[] : ∀ (prog : AbstractTrace)
                 → (∀ pc i → fetch prog pc ≡ just i → ∀ fs → event-of i fs ≡ [])
                 → ∀ (fuel : ℕ) (fs : FlatState) → flat-events fuel prog fs ≡ []
  flat-events-[] prog H zero    fs = refl
  flat-events-[] prog H (suc n) fs with halted (floc fs)
  ... | true  = refl
  ... | false with fetch prog (fpc fs) in eq
  ...   | nothing = refl
  ...   | just i  rewrite H (fpc fs) i eq fs =
            flat-events-[] prog H n (flat-exec-instr i prog fs)
