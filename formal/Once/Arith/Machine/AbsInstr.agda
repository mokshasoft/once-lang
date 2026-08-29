-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
--
-- clean-semantics L1 (D054): the instruction set and the Maybe-lifters
-- are width-AGNOSTIC (the register carrier is `ℕ` at every width); only
-- the executor `step`/`run-abstract`, which applies the modular ops,
-- is parameterised by the word width `bits` (module `Exec`). The
-- architecture supplies `bits`; nothing here hard-codes 64.
------------------------------------------------------------------------

module Once.Arith.Machine.AbsInstr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Arith.Machine.AbsState
open import Once.Word using (module Width)
open import Once.Arith.Machine.Shape using (projectF)
open import Once.Float.Dyadic using (FloatFormat)
open import Once.Float.Decimal using (Decimal; round)
import Once.Float.Arith as FA

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

  -- | `div-rrr dst a b` : reg dst := reg a /ˢ reg b (D055 total signed div).
  div-rrr     : ℕ → ℕ → ℕ → AbstractInstr

  -- | `rem-rrr dst a b` : reg dst := reg a %ˢ reg b (D055 total signed rem).
  rem-rrr     : ℕ → ℕ → ℕ → AbstractInstr

  -- | `div-safe-rrr dst a b` / `rem-safe-rrr dst a b` : SEMANTICALLY IDENTICAL
  -- to `div-rrr`/`rem-rrr` (both denote `_/ˢ_`/`_%ˢ_`). The `-safe` marker is
  -- a codegen HINT that the divisor is a compile-time-safe literal (nonzero,
  -- not −1), so the per-arch Emit may drop the D055 idiv guard. The abstract
  -- MEANING is unchanged — see the `step` cases below (identical writes).
  div-safe-rrr : ℕ → ℕ → ℕ → AbstractInstr
  rem-safe-rrr : ℕ → ℕ → ℕ → AbstractInstr

  -- | `shl-rri dst src imm` : reg dst := reg src `shlᵂ` imm — the modular
  -- value of a left shift by `imm` (`= reg src ⊗ 2^imm`). Emitted for a
  -- multiply by a positive power-of-two literal (strength reduction).
  shl-rri     : ℕ → ℕ → ℕ → AbstractInstr

  -- | `sdiv-pow2-rri dst src imm` : reg dst := reg src `sdiv2ᵏ` imm — the
  -- truncated signed division of reg src by `2^imm` (`= reg src /ˢ 2^imm`).
  -- Emitted for a divide by a positive power-of-two literal.
  sdiv-pow2-rri : ℕ → ℕ → ℕ → AbstractInstr

  -- | `neg-rr dst a` : reg dst := - reg a.
  neg-rr      : ℕ → ℕ → AbstractInstr

  -- | `spill src s` : scratch s := reg src.
  spill       : ℕ → ℕ → AbstractInstr

  -- | `reload s dst` : reg dst := scratch s.
  reload      : ℕ → ℕ → AbstractInstr

  -- | `move-to-out src` : output := reg src.
  move-to-out : ℕ → AbstractInstr

  ----------------------------------------------------------------------
  -- PLAN 0.75 F4: the FLOAT instructions.
  --
  -- NO SECOND REGISTER FILE, and that is a considered choice rather than a
  -- shortcut. A register here holds a `Maybe ℕ`, and a float VALUE is a bit
  -- pattern — also `ℕ` (D113). So the two kinds already share a carrier, and
  -- what distinguishes them is the OPERATION, which is what these
  -- constructors are. Splitting the file would ripple through every proof in
  -- `CompileCorrect` that reasons about `regs s [ r ]`, and would buy nothing:
  -- the abstract "registers" are stack slots at the emitter, and a slot does
  -- not care which kind it holds.
  --
  -- The concrete machines DO have separate files, and that is the emitter's
  -- business: it loads a slot into `%xmm0`/`ft0` for a float op exactly as it
  -- loads one into `%r8` for an integer op.
  ----------------------------------------------------------------------

  -- | `load-finput p r` : reg r := the FLOAT leaf at `p` (no `fromℤ` — a
  -- float leaf is already a pattern).
  load-finput : InputPath → ℕ → AbstractInstr

  -- | `load-fimm d r` : reg r := `round F d`. The payload is the `Decimal`
  -- (D117), so the ONE rounding happens here, at the target's format.
  load-fimm   : Decimal → ℕ → AbstractInstr

  fadd-rrr    : ℕ → ℕ → ℕ → AbstractInstr
  fsub-rrr    : ℕ → ℕ → ℕ → AbstractInstr
  fmul-rrr    : ℕ → ℕ → ℕ → AbstractInstr
  -- | Correctly-rounded division (`FA.fdiv`), admitted now that the sticky bit
  -- exists. `%` has no float form — IEEE's `fmod` is a different function.
  fdiv-rrr    : ℕ → ℕ → ℕ → AbstractInstr

  -- | `fneg-rr dst a` : a SIGN-BIT FLIP, not `0 − x` — the latter turns `−0`
  -- into `+0` and canonicalises a NaN, neither of which negation may do.
  fneg-rr     : ℕ → ℕ → AbstractInstr

  -- | `i2f-rr dst a` : D125's widening, correctly rounded. The only
  -- instruction that crosses the kinds, which is why it is the only place the
  -- emitter has to move a value between register files.
  i2f-rr      : ℕ → ℕ → AbstractInstr

------------------------------------------------------------------------
-- Maybe-lifters (width-agnostic: register carrier is ℕ at every width)
------------------------------------------------------------------------

-- | Lift a binary operation over `Maybe` register values, propagating
-- `nothing`. `Exec` supplies the modular op (`_⊕_` etc.).
bin-op : (ℕ → ℕ → ℕ) → Maybe ℕ → Maybe ℕ → Maybe ℕ
bin-op f (just x) (just y) = just (f x y)
bin-op _ (just _) nothing  = nothing
bin-op _ nothing  (just _) = nothing
bin-op _ nothing  nothing  = nothing

-- | Lift a unary operation over `Maybe` register values.
un-op : (ℕ → ℕ) → Maybe ℕ → Maybe ℕ
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

-- | …and the FLOAT leaf's default (plan 0.75 F4). A separate function because
-- the carriers differ: a float leaf is already a pattern (`ℕ`), so there is no
-- `fromℤ` after it and the default is `0` — which is `+0.0`, the same value
-- the integer default denotes.
maybe-zero-f : Maybe ℕ → ℕ
maybe-zero-f (just w) = w
maybe-zero-f nothing  = 0

------------------------------------------------------------------------
-- Single-step + trace interpreter — WIDTH-PARAMETERISED (D054).
-- The architecture supplies `bits`; the carrier stays ℕ, only the
-- modular ops vary.
------------------------------------------------------------------------

-- PLAN 0.75 F4: the FORMAT joins the width. Both are target facts, neither is
-- baked, and the float instructions read `F` exactly as the integer ones read
-- `bits`.
module Exec (bits : ℕ) (F : FloatFormat) where
  open Width bits using (fromℤ; toℤ; _⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_; shlᵂ; sdiv2ᵏ)

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
  step (div-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op _/ˢ_ (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  step (rem-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op _%ˢ_ (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  -- `-safe` variants: step is IDENTICAL to the guarded div-rrr/rem-rrr.
  step (div-safe-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op _/ˢ_ (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  step (rem-safe-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op _%ˢ_ (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  -- strength-reduced multiply / divide by a power-of-two literal.
  step (shl-rri dst src imm) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        un-op (λ x → shlᵂ x imm) (ArithAbsState.regs s [ src ]) ] }
  step (sdiv-pow2-rri dst src imm) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        un-op (λ x → sdiv2ᵏ x imm) (ArithAbsState.regs s [ src ]) ] }
  step (neg-rr dst a) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        un-op ⊝_ (ArithAbsState.regs s [ a ]) ] }
  step (spill src slot) s = record s
    { scratch = ArithAbsState.scratch s [ slot ↦
        ArithAbsState.regs s [ src ] ] }
  step (reload slot dst) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        ArithAbsState.scratch s [ slot ] ] }
  -- The float steps. Each reads `Once.Float.Arith` at `F` — the SAME
  -- functions `block-semM` and `eval-arith-W` call, so the abstract machine
  -- and the denotation cannot drift.
  step {sh} (load-finput p r) s = record s
    { regs = ArithAbsState.regs s [ r ↦
        just (maybe-zero-f (projectF sh p (ArithAbsState.input s))) ] }
  step (load-fimm d r) s = record s
    { regs = ArithAbsState.regs s [ r ↦ just (round F d) ] }
  step (fadd-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op (FA.fadd F) (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  step (fsub-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op (FA.fsub F) (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  step (fmul-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op (FA.fmul F) (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  step (fdiv-rrr dst a b) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        bin-op (FA.fdiv F) (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
  step (fneg-rr dst a) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        un-op (FA.fneg F) (ArithAbsState.regs s [ a ]) ] }
  step (i2f-rr dst a) s = record s
    { regs = ArithAbsState.regs s [ dst ↦
        un-op (λ w → FA.i2f F (toℤ w)) (ArithAbsState.regs s [ a ]) ] }
  step (move-to-out src) s = record s
    { output = ArithAbsState.regs s [ src ] }

  run-abstract : ∀ {sh} → List AbstractInstr → ArithAbsState sh → ArithAbsState sh
  run-abstract []       s = s
  run-abstract (i ∷ is) s = run-abstract is (step i s)
