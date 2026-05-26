-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86.CodeGen
--
-- Plan 0.20 Phase D — `emit : AbstractInstr → XProgram`.
--
-- Per I-arith-3, AbstractInstr uses unbounded `ℕ` indices. `abs-reg`
-- maps `0..3` to r12-r15; `≥ 4` returns `nothing` and the emit case
-- emits no instruction (the naive Phase C compile is dimensioned at 2
-- abstract regs, so this never fires in the current pipeline).
------------------------------------------------------------------------

module Once.Arith.Backend.X86.CodeGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Arith.Machine.AbsState using (InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         neg-rr; spill; reload; move-to-out)
open import Once.Arith.Backend.X86.Syntax

------------------------------------------------------------------------
-- Register allocation
------------------------------------------------------------------------

-- | Map an abstract reg index to its concrete x86 register.
abs-reg : ℕ → Maybe XReg
abs-reg zero                              = just XR12
abs-reg (suc zero)                        = just XR13
abs-reg (suc (suc zero))                  = just XR14
abs-reg (suc (suc (suc zero)))            = just XR15
abs-reg (suc (suc (suc (suc _))))         = nothing

------------------------------------------------------------------------
-- Input-path → byte-offset
------------------------------------------------------------------------

path-offset : InputPath → ℕ
path-offset []          = 0
path-offset (Fst ∷ p)   = path-offset p
path-offset (Snd ∷ p)   = 8 Data.Nat.+ path-offset p
  where import Data.Nat

------------------------------------------------------------------------
-- Per-AbstractInstr translation
------------------------------------------------------------------------

emit : AbstractInstr → XProgram
emit (load-imm z r) with abs-reg r
... | just xr = Xmov-imm xr z ∷ []
... | nothing = []
emit (load-input p r) with abs-reg r
... | just xr = Xmov-arg xr (path-offset p) ∷ []
... | nothing = []
emit (add-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb = Xmov-rr xd xa ∷ Xadd-rr xd xb ∷ []
... | _       | _       | _       = []
emit (sub-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb = Xmov-rr xd xa ∷ Xsub-rr xd xb ∷ []
... | _       | _       | _       = []
emit (mul-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb = Xmov-rr xd xa ∷ Ximul-rr xd xb ∷ []
... | _       | _       | _       = []
emit (neg-rr dst a) with abs-reg dst | abs-reg a
... | just xd | just xa = Xmov-rr xd xa ∷ Xneg-r xd ∷ []
... | _       | _       = []
emit (spill src slot) with abs-reg src
... | just xs = Xmov-r-m (mk-scratch slot) xs ∷ []
... | nothing = []
emit (reload slot dst) with abs-reg dst
... | just xd = Xmov-m-r xd (mk-scratch slot) ∷ []
... | nothing = []
emit (move-to-out src) with abs-reg src
... | just xs = Xmov-out xs ∷ []
... | nothing = []

emit-program : List AbstractInstr → XProgram
emit-program []       = []
emit-program (i ∷ is) = emit i ++ emit-program is
