-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.ExecArith  (Plan 0.54 rung B / B2.3)
--
-- The x86-32 concrete block fold for the arith VALUE simulation. Unlike
-- x86-64/riscv64, x86-32 cannot instantiate `ExecArithCore`: its arith
-- registers (edx = XR0, edi = XR1) are CCC-BORROWED, so the per-instruction
-- step does NOT preserve CCC state — the whole block does, via the emit's
-- push/pop save-restore framing (a separate, asm-level concern, orthogonal to
-- the value fold here). So this module is self-contained: it defines only the
-- register footprint (`writes`), the write-fold (`step-of`), the memory effect
-- (`mem-effect` — spill's `4·slot(%esp)` scratch write), and the fold
-- `exec1`/`exec-arith-block`, exactly the surface `ArithSimX86-32` consumes.
--
-- DIV/REM MODEL: x86-32 `idivl` clobbers %edx (= XR0, an arith register — not a
-- spare like x86-64's %rdx) and returns via %eax. `compile-go` only ever emits
-- div/rem with `dst = XR0`, so the %edx clobber IS the destination write; the
-- footprint is modeled as {arith-reg dst, eax} (peel eax, like the arg/sdiv
-- io-scratch). The residual real-asm faithfulness (executing `instr-text` writes
-- exactly this footprint, given the dst=XR0 discipline) is the ISA axiom.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.ExecArith where

open import Data.Nat using (ℕ; suc; _*_; _+_)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.X86-32.Emit using (arith-reg)
open import Once.CCC.Target.X86-32.Semantics
  using (State; mkstate; RegFile; Memory; readReg; writeReg; readMem; writeMem; Word)
open import Once.Target.X86-32.PhysReg using (Reg; eax; esp)
open State

------------------------------------------------------------------------
-- Register footprint (over-approximation of `instr-text`'s clobber set). io =
-- eax (Output / div-result / path-walk scratch). Div/rem are DOUBLE-write
-- {arith-reg dst, eax} (see the DIV/REM MODEL note above).
------------------------------------------------------------------------

writes : XInstr → List Reg
writes (Xmov-imm dst _)         = arith-reg dst ∷ []
writes (Xmov-rr dst _)          = arith-reg dst ∷ []
writes (Xmov-r-m _ _)           = []
writes (Xmov-m-r dst _)         = arith-reg dst ∷ []
writes (Xmov-arg dst _)         = arith-reg dst ∷ eax ∷ []
writes (Xadd-rr dst _)          = arith-reg dst ∷ []
writes (Xsub-rr dst _)          = arith-reg dst ∷ []
writes (Ximul-rr dst _)         = arith-reg dst ∷ []
writes (Xneg-r dst)             = arith-reg dst ∷ []
writes (Xdiv-rrr dst _ _)       = arith-reg dst ∷ eax ∷ []
writes (Xrem-rrr dst _ _)       = arith-reg dst ∷ eax ∷ []
writes (Xdiv-safe-rrr dst _ _)  = arith-reg dst ∷ eax ∷ []
writes (Xrem-safe-rrr dst _ _)  = arith-reg dst ∷ eax ∷ []
writes (Xshl-rri dst _ _)       = arith-reg dst ∷ []
writes (Xsdiv-pow2-rri dst _ _) = arith-reg dst ∷ eax ∷ []
writes (Xmov-out _)             = eax ∷ []

module _ (val : XInstr → State → Reg → Word) where

  -- Scratch slot at `4·slot(%esp)` — ADDITIVE (like riscv `sp+8·slot`), so
  -- injective in the slot unconditionally.
  scratch-addr : State → XScratch → Word
  scratch-addr s sc = readReg (regs s) esp + (4 * XScratch.slot sc)

  write-regs : List (Reg × Word) → RegFile → RegFile
  write-regs []             rf = rf
  write-regs ((r , v) ∷ ps) rf = write-regs ps (writeReg rf r v)

  step-of : XInstr → State → RegFile
  step-of i s = write-regs (map (λ r → (r , val i s r)) (writes i)) (regs s)

  mem-effect : XInstr → State → Memory
  mem-effect (Xmov-r-m sc src) s = writeMem (memory s) (scratch-addr s sc) (readReg (regs s) (arith-reg src))
  mem-effect _                 s = memory s

  exec1 : XInstr → State → State
  exec1 i s = mkstate (step-of i s) (mem-effect i s) (flags s) (suc (pc s)) (halted s)

  exec-arith-block : List XInstr → State → State
  exec-arith-block []       s = s
  exec-arith-block (i ∷ is) s = exec-arith-block is (exec1 i s)
