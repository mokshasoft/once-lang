-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.Emit
--
-- Plan 0.53 — x86-32 arith-block emitter. Mirrors
-- `Once.Arith.Backend.X86-64.Emit` (x86-64) with i386 conventions.
--
-- Calling convention (matching the rest of Once's x86-32 codegen):
--   - `%ecx` holds the block input value pointer (Input1). A primitive Int
--     lives at `0(%ecx)`; a nested pair's `Fst`/`Snd` map to byte offsets
--     `0` / `4` (4-byte i386 words).
--   - The Int result is returned in `%eax` (Output); `%eax` also doubles as
--     the path-walk scratch.
--   - The 4 abstract arith registers (`AbsReg 0..3`) map to `%edx`, `%edi`,
--     `%ebx`, `%esi`. `%ebx` (closure) and `%esi` (heap) are GLOBAL in the
--     wider codegen, so the block saves/restores them (push/pop). `%edx` and
--     `%edi` are free (Scratch / Input2, dead across a SigOp call).
--   - Scratch stack slots live at `4*slot(%esp)` within a reserved frame.
--     The block is a leaf (no calls), so it needs no return-address save
--     beyond what `ret` already handles.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.Emit where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ; suc; _*_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.AbsState using (InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.Compile using (compile-abs; required-scratch)
open import Once.Arith.Machine.IR using (MArithIR; ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-shape; block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Target.Symbol using (once-symbol-own)

------------------------------------------------------------------------
-- Register / scratch text
------------------------------------------------------------------------

reg-text : XReg → String
reg-text XR0 = "%edx"
reg-text XR1 = "%edi"
reg-text XR2 = "%ebx"
reg-text XR3 = "%esi"

-- | A scratch slot lives at `4*slot(%esp)` within the reserved frame.
scratch-text : XScratch → String
scratch-text record { slot = s } =
  showℕ (4 * s) ++ "(%esp)"

------------------------------------------------------------------------
-- Per-instruction text
------------------------------------------------------------------------

instr-text : XInstr → String
instr-text (Xmov-imm dst z)   = "    movl $" ++ showℤ z ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-rr dst src)  = "    movl " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-r-m s src)   = "    movl " ++ reg-text src ++ ", " ++ scratch-text s ++ "\n"
instr-text (Xmov-m-r dst s)   = "    movl " ++ scratch-text s ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-arg dst path) = path-load-text dst path
  where
    side-offset : Side → String
    side-offset Fst = "0"
    side-offset Snd = "4"

    walk-eax-rest : XReg → InputPath → String
    walk-eax-rest dst (s ∷ []) =
      "    movl " ++ side-offset s ++ "(%eax), " ++ reg-text dst ++ "\n"
    walk-eax-rest dst (s ∷ ss) =
      "    movl " ++ side-offset s ++ "(%eax), %eax\n" ++ walk-eax-rest dst ss
    walk-eax-rest dst []       = ""

    path-load-text : XReg → InputPath → String
    path-load-text dst []         =
      "    movl %ecx, " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ [])   =
      "    movl " ++ side-offset s ++ "(%ecx), " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ rest) =
      "    movl " ++ side-offset s ++ "(%ecx), %eax\n" ++
      walk-eax-rest dst rest
instr-text (Xadd-rr dst src)  = "    addl " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xsub-rr dst src)  = "    subl " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Ximul-rr dst src) = "    imull " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xneg-r dst)       = "    negl " ++ reg-text dst ++ "\n"
instr-text (Xmov-out src)     = "    movl " ++ reg-text src ++ ", %eax\n"

program-text : XProgram → String
program-text []       = ""
program-text (i ∷ is) = instr-text i ++ program-text is

------------------------------------------------------------------------
-- Block subroutine emission
------------------------------------------------------------------------

-- | A complete arith-block subroutine. Saves/restores the two borrowed
-- global registers (%ebx = closure, %esi = heap) around the body, and
-- reserves `4 * required-scratch` bytes of scratch below them.
--
--   <sym>:
--       pushl %ebx ; pushl %esi        ; save borrowed abstract regs
--       subl $N, %esp                  ; reserve scratch
--       <emitted instructions>
--       addl $N, %esp
--       popl %esi ; popl %ebx
--       ret
emit-arith-block : (sym : String) → ArithBlock → String
emit-arith-block sym blk =
  let n     = required-scratch (block-body blk)
      pad   = showℕ (4 * n)
      instr = emit-program (compile-abs (block-body blk))
  in sym ++ ":\n" ++
     -- Save ALL four borrowed abstract-reg registers: %ebx (closure) and
     -- %esi (heap) are global; %edx (Scratch) and %edi (Input2) are the
     -- CCC reg-op registers, live across a cata loop whose algebra calls
     -- this block. Clobbering %edx would corrupt the loop counter.
     "    pushl %ebx\n" ++
     "    pushl %esi\n" ++
     "    pushl %edx\n" ++
     "    pushl %edi\n" ++
     "    subl $" ++ pad ++ ", %esp\n" ++
     program-text instr ++
     "    addl $" ++ pad ++ ", %esp\n" ++
     "    popl %edi\n" ++
     "    popl %edx\n" ++
     "    popl %esi\n" ++
     "    popl %ebx\n" ++
     "    ret\n\n"

------------------------------------------------------------------------
-- Block-list emission
------------------------------------------------------------------------

arith-block-symbol : ArithBlock → String
arith-block-symbol blk = once-symbol-own (block-name (block-body blk))

emit-arith-blocks : List ArithBlock → String
emit-arith-blocks []       = ""
emit-arith-blocks (b ∷ bs) =
  ".globl " ++ arith-block-symbol b ++ "\n" ++
  emit-arith-block (arith-block-symbol b) b ++
  emit-arith-blocks bs
