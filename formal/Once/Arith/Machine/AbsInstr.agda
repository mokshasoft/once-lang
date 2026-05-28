-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Machine.AbsInstr
--
-- Plan 0.20 — the abstract instruction set for arith blocks and the
-- denotational `run-abstract : [AbstractInstr] → State → State`.
--
-- Per I-arith-3, registers and scratch slots are plain `ℕ` indices.
-- The store model (`AbsState.Store`) gives `nothing` for indices
-- that haven't been written; `step` propagates that through arith
-- ops. Compile-abs's structural lemma in Phase C will show "all reg
-- reads return just" — that's the only place where index discipline
-- comes back as a proof obligation.
------------------------------------------------------------------------

module Once.Arith.Machine.AbsInstr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Arith.Machine.AbsState
open import Once.Word using (module Word64)
open Word64 using (Word; fromℤ; _⊕_; _⊖_; _⊗_; ⊝_)

------------------------------------------------------------------------
-- Abstract instruction set
------------------------------------------------------------------------

data AbstractInstr : Set where
  -- | `load-input p r` : reg r := project sh p input.
  load-input  : InputPath → ℕ → AbstractInstr

  -- | `load-imm z r` : reg r := just z.
  load-imm    : ℤ → ℕ → AbstractInstr

  -- | `add-rrr dst a b` : reg dst := reg a + reg b (Maybe-lifted).
  add-rrr     : ℕ → ℕ → ℕ → AbstractInstr

  -- | `sub-rrr dst a b` : reg dst := reg a - reg b.
  sub-rrr     : ℕ → ℕ → ℕ → AbstractInstr

  -- | `mul-rrr dst a b` : reg dst := reg a * reg b.
  mul-rrr     : ℕ → ℕ → ℕ → AbstractInstr

  -- | `neg-rr dst a` : reg dst := - reg a.
  neg-rr      : ℕ → ℕ → AbstractInstr

  -- | `spill src s` : scratch s := reg src.
  spill       : ℕ → ℕ → AbstractInstr

  -- | `reload s dst` : reg dst := scratch s.
  reload      : ℕ → ℕ → AbstractInstr

  -- | `move-to-out src` : output := reg src.
  move-to-out : ℕ → AbstractInstr

------------------------------------------------------------------------
-- Single-step interpreter
------------------------------------------------------------------------

-- | Lift a binary operation over `Maybe Word`, propagating `nothing`.
bin-op : (Word → Word → Word) → Maybe Word → Maybe Word → Maybe Word
bin-op f (just x) (just y) = just (f x y)
bin-op _ (just _) nothing  = nothing
bin-op _ nothing  (just _) = nothing
bin-op _ nothing  nothing  = nothing

-- | Lift a unary operation over `Maybe Word`.
un-op : (Word → Word) → Maybe Word → Maybe Word
un-op f (just x) = just (f x)
un-op _ nothing  = nothing

-- | Default-zero helper for `load-input` — keeps the abstract machine
-- aligned with `eval-arith`'s "+0 on malformed path" rule (see
-- `Once.Arith.Machine.IR.eval-arith`). A well-formed IR (paths
-- match the input shape) never sees this default; the recognition
-- pass produces well-formed IRs by construction. The projected value
-- is the ℤ spec input; `load-input` applies `fromℤ` to land it in a
-- (modular `Word`) register.
maybe-zero : Maybe ℤ → ℤ
maybe-zero (just z) = z
maybe-zero nothing  = + 0

-- | One abstract step.
step : ∀ {sh} → AbstractInstr → ArithAbsState sh → ArithAbsState sh
step {sh} (load-input p r) s = record s
  { regs = ArithAbsState.regs s [ r ↦
      just (fromℤ (maybe-zero (project sh p (ArithAbsState.input s)))) ] }
step (load-imm z r) s = record s
  { regs = ArithAbsState.regs s [ r ↦ just (fromℤ z) ] }
step (add-rrr dst a b) s = record s
  { regs = ArithAbsState.regs s [ dst ↦
      bin-op _⊕_ (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
step (sub-rrr dst a b) s = record s
  { regs = ArithAbsState.regs s [ dst ↦
      bin-op _⊖_ (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
step (mul-rrr dst a b) s = record s
  { regs = ArithAbsState.regs s [ dst ↦
      bin-op _⊗_ (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
step (neg-rr dst a) s = record s
  { regs = ArithAbsState.regs s [ dst ↦
      un-op ⊝_ (ArithAbsState.regs s [ a ]) ] }
step (spill src slot) s = record s
  { scratch = ArithAbsState.scratch s [ slot ↦
      ArithAbsState.regs s [ src ] ] }
step (reload slot dst) s = record s
  { regs = ArithAbsState.regs s [ dst ↦
      ArithAbsState.scratch s [ slot ] ] }
step (move-to-out src) s = record s
  { output = ArithAbsState.regs s [ src ] }

------------------------------------------------------------------------
-- Trace interpreter
------------------------------------------------------------------------

run-abstract : ∀ {sh} → List AbstractInstr → ArithAbsState sh → ArithAbsState sh
run-abstract []       s = s
run-abstract (i ∷ is) s = run-abstract is (step i s)
