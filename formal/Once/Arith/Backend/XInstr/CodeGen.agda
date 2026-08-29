-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.XInstr.CodeGen
--
-- Plan 0.20 Phase D — `emit : AbstractInstr → XProgram`.
--
-- Per I-arith-3, AbstractInstr uses unbounded `ℕ` indices. `abs-reg`
-- maps `0..3` to r12-r15; `≥ 4` returns `nothing` and the emit case
-- emits no instruction (the naive Phase C compile is dimensioned at 2
-- abstract regs, so this never fires in the current pipeline).
------------------------------------------------------------------------

module Once.Arith.Backend.XInstr.CodeGen where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Arith.Machine.AbsState using (InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.AbsInstr
  using (load-finput; load-fimm; fadd-rrr; fsub-rrr; fmul-rrr; fdiv-rrr; fneg-rr; i2f-rr; AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         div-rrr; rem-rrr; div-safe-rrr; rem-safe-rrr; shl-rri; sdiv-pow2-rri;
         neg-rr; spill; reload; move-to-out)
open import Once.Arith.Backend.XInstr.Syntax

------------------------------------------------------------------------
-- Decidable equality on XReg (needed by the binary-op emit cases to
-- avoid the dst==b aliasing bug — `mov a → dst; add b → dst` loses
-- `b` when dst==b).
------------------------------------------------------------------------

_≟x_ : (a b : XReg) → Dec (a ≡ b)
XR0 ≟x XR0 = yes refl
XR1 ≟x XR1 = yes refl
XR0 ≟x XR1 = no λ ()
XR1 ≟x XR0 = no λ ()

------------------------------------------------------------------------
-- Register allocation
------------------------------------------------------------------------

-- | Map an abstract reg index to its concrete register (XR0/XR1). `compile-go`
-- only ever emits reg 0/1 (2-register + stack-spill discipline), so indices ≥ 2
-- are unreachable and map to `nothing`.
abs-reg : ℕ → Maybe XReg
abs-reg zero              = just XR0
abs-reg (suc zero)        = just XR1
abs-reg (suc (suc _))     = nothing

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
... | just xr = Xmov-arg xr p ∷ []
... | nothing = []
-- | `add-rrr dst a b` = `dst := a + b`. Addition is commutative, so
-- when `dst ≡ a` or `dst ≡ b` the move is unnecessary; in both
-- aliasing cases we collapse to a single in-place `add`.
emit (add-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb        with xd ≟x xa
...   | yes _                              = Xadd-rr xd xb ∷ []
...   | no _                               with xd ≟x xb
...     | yes _                            = Xadd-rr xd xa ∷ []
...     | no _                             = Xmov-rr xd xa ∷ Xadd-rr xd xb ∷ []
emit (add-rrr _ _ _) | _ | _ | _           = []

-- | `sub-rrr dst a b` = `dst := a - b`. Subtraction is NOT
-- commutative. When `dst ≡ b` we'd otherwise lose `b` to the leading
-- move; emit `neg dst; add a → dst` (= a - b) instead.
emit (sub-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb        with xd ≟x xa
...   | yes _                              = Xsub-rr xd xb ∷ []
...   | no _                               with xd ≟x xb
...     | yes _                            = Xneg-r xd ∷ Xadd-rr xd xa ∷ []
...     | no _                             = Xmov-rr xd xa ∷ Xsub-rr xd xb ∷ []
emit (sub-rrr _ _ _) | _ | _ | _           = []

-- | `mul-rrr dst a b` = `dst := a * b`. Commutative; same aliasing
-- treatment as `add-rrr`.
emit (mul-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb        with xd ≟x xa
...   | yes _                              = Ximul-rr xd xb ∷ []
...   | no _                               with xd ≟x xb
...     | yes _                            = Ximul-rr xd xa ∷ []
...     | no _                             = Xmov-rr xd xa ∷ Ximul-rr xd xb ∷ []
emit (mul-rrr _ _ _) | _ | _ | _           = []
-- | `div-rrr dst a b` / `rem-rrr dst a b`. THREE-address: emit a single
-- neutral `Xdiv-rrr`/`Xrem-rrr` with explicit dividend/divisor. No aliasing
-- dispatch is needed — the per-arch Emit reads both operands before writing
-- `dst` (x86 idiv consumes rax/rdx internally; RV64 div/rem is 3-address).
emit (div-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb          = Xdiv-rrr xd xa xb ∷ []
... | _       | _       | _                = []
emit (rem-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb          = Xrem-rrr xd xa xb ∷ []
... | _       | _       | _                = []
-- `-safe` variants: same 3-address shape, guard-elided Emit downstream.
emit (div-safe-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb          = Xdiv-safe-rrr xd xa xb ∷ []
... | _       | _       | _                = []
emit (rem-safe-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb          = Xrem-safe-rrr xd xa xb ∷ []
... | _       | _       | _                = []
-- Strength-reduced multiply / divide by a power-of-two literal. Single-write
-- (`dst := f src`); the neutral XInstr carries both regs plus the immediate
-- shift count. No aliasing dispatch — the per-arch Emit reads `src` before
-- writing `dst`.
emit (shl-rri dst src imm) with abs-reg dst | abs-reg src
... | just xd | just xs                    = Xshl-rri xd xs imm ∷ []
... | _       | _                          = []
emit (sdiv-pow2-rri dst src imm) with abs-reg dst | abs-reg src
... | just xd | just xs                    = Xsdiv-pow2-rri xd xs imm ∷ []
... | _       | _                          = []
emit (neg-rr dst a) with abs-reg dst | abs-reg a
... | just xd | just xa = Xmov-rr xd xa ∷ Xneg-r xd ∷ []
... | _       | _       = []

----------------------------------------------------------------------
-- PLAN 0.75 F4: the float instructions.
--
-- The ALIASING treatment is the integer one verbatim, and it has to be:
-- `compile-go` emits `fadd-rrr 0 1 0`, i.e. `dst ≡ b`, for every binary float
-- node. For the commutative ops that is the `add-rrr` case; for `fsub` it is
-- `Xfsubr-rr`, the REVERSE subtract — which is the operation the aliasing
-- actually calls for, and avoids needing `a − b ≡ a + (−b)` as a lemma.
----------------------------------------------------------------------
emit (load-fimm d r) with abs-reg r
... | just xr = Xmov-fimm xr d ∷ []
... | nothing = []
emit (load-finput p r) with abs-reg r
... | just xr = Xmov-farg xr p ∷ []
... | nothing = []
emit (fadd-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb        with xd ≟x xa
...   | yes _                              = Xfadd-rr xd xb ∷ []
...   | no _                               with xd ≟x xb
...     | yes _                            = Xfadd-rr xd xa ∷ []
...     | no _                             = Xmov-rr xd xa ∷ Xfadd-rr xd xb ∷ []
emit (fadd-rrr _ _ _) | _ | _ | _          = []
emit (fsub-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb        with xd ≟x xa
...   | yes _                              = Xfsub-rr xd xb ∷ []
...   | no _                               with xd ≟x xb
...     | yes _                            = Xfsubr-rr xd xa ∷ []
...     | no _                             = Xmov-rr xd xa ∷ Xfsub-rr xd xb ∷ []
emit (fsub-rrr _ _ _) | _ | _ | _          = []
emit (fmul-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb        with xd ≟x xa
...   | yes _                              = Xfmul-rr xd xb ∷ []
...   | no _                               with xd ≟x xb
...     | yes _                            = Xfmul-rr xd xa ∷ []
...     | no _                             = Xmov-rr xd xa ∷ Xfmul-rr xd xb ∷ []
emit (fmul-rrr _ _ _) | _ | _ | _          = []
-- Three-address: the sources are read before the destination is written, so
-- the `dst ≡ b` aliasing that forces `fmul`'s swap analysis cannot bite.
emit (fdiv-rrr dst a b) with abs-reg dst | abs-reg a | abs-reg b
... | just xd | just xa | just xb          = Xfdiv-rrr xd xa xb ∷ []
... | _       | _       | _                = []
emit (fneg-rr dst a) with abs-reg dst | abs-reg a
... | just xd | just xa = Xmov-rr xd xa ∷ Xfneg-r xd ∷ []
... | _       | _       = []
emit (i2f-rr dst a) with abs-reg dst | abs-reg a
... | just xd | just xa = Xi2f-r xd xa ∷ []
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
